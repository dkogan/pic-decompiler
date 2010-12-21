#!/usr/bin/perl
use strict;
use warnings;
use feature qw(say);
use List::MoreUtils qw(indexes first_index);
use Data::Dumper;
use Text::Tabs;
use Storable qw(dclone);
use Set::IntSpan;

my (%regaddrs, %regmaps, %bitmaps);
parseIncludeFile();
addExtraRegisterMappings();

my @lines = expand <>; # slurp all lines, convert tabs to spaces

my @instructions;
my %functions;

# I parse all my lines into a list of instructions
foreach my $line (@lines)
{
  chomp $line;
  next if $line =~/^#/;

  my ($addrhex, $opcode, $mnemonic, $arg1, $arg2) =
    $line =~
      /([0-9a-z]+):\s+               # address
       ([0-9a-z]{4})\s+              # opcode
       ([a-z]+)                      # mnemonic
       (?:\s+([0-9a-zx]+)            # arg1
         (?:,\s+([0-9a-zxw]+))?)?/x; # arg2

  next unless defined $addrhex;

  my $addr = hex $addrhex;
  $arg1 = oct $arg1 if defined $arg1 && $arg1 =~ /^0x/;
  $arg2 = oct $arg2 if defined $arg2 && $arg2 =~ /^0x/;

  if( defined $instructions[$addr]) { die("duplicate instruction defined at 0x$addrhex"); }

  $instructions[$addr] = {line      => $line,
                          addr      => $addr,
                          opcode    => $opcode,
                          mnemonic  => $mnemonic,
                          arg1      => $arg1,
                          arg2      => $arg2,

                          # execution paths
                          from      => {},
                          to        => {},

                          # different possibilities for the call stack when we get here
                          callstack => [],

                          #indents
                          indent_start => 0,
                          indent_end   => 0
                         };

  $instructions[$addr]{writes_w} =
    ( defined $arg2 && $arg2 eq 'w') || $mnemonic =~ /w$/;
  $instructions[$addr]{writes_f} =
    ( defined $arg2 && $arg2 eq 'f') || ($mnemonic =~ /f$/ && (!defined $arg2 || $arg2 ne 'w'));
  $instructions[$addr]{accesses_f}   = $mnemonic =~ /f$|btfs|cfsz/;
  $instructions[$addr]{jmps}         = $mnemonic =~ /goto|call/;
  $instructions[$addr]{returns}      = $mnemonic =~ /return|retlw|retfie/;
  $instructions[$addr]{accesses_bit} = $mnemonic =~ /^(?:btfs[cs]|b[cs]f)$/;

  if(defined $arg1 && $arg1 == $regaddrs{PCL} && $instructions[$addr]{writes_f})
  {
    say sprintf 'WARNING: Manipulating PCL in 0x%x. Not supported yet', $addr;
  }
}

traceProgramFlow();

my @instructions_undefined   = indexes {!defined $_ || !defined $_->{addr} } @instructions;
my @instructions_unreachable = grep { defined $_ && !%{$_->{from}}         } @instructions;

if(0)
{
  foreach(@instructions_undefined  ) { say sprintf 'Undefined   instruction at 0x%x', $_; }
  foreach(@instructions_unreachable) { say sprintf 'Unreachable instruction at 0x%x', $_->{addr}; }
}

markUninteresting();
my $functionbounds = markFunctionBounds();
expandConditionals($functionbounds);
printAnnotated($functionbounds);




sub traceProgramFlow
{
  # pclath is upper 5 bits of the program counter, stored at a bit vector if I'm
  # manipulating PCL, all 5 are used. A call or goto uses only the top 2
  # bits
  my $state0 = {PCLATH => 0,
                STATUS => 0,
                w      => 0};

  # trace all execution paths from the start of the program
  traceFunctionCall(0, '', [], $state0);

  # trace all execution paths from the start of the ISR
  traceFunctionCall(4, 'isr', [], $state0);

  sub traceFunctionCall
  {
    my ($addr, $isisr, $callstack, $state0) = @_;

    # by default, set the state to state0
    $instructions[$addr]->{state} //= $state0;

    # start keeping track of the contents of this function
    my %functionContext;
    if(exists $functions{$addr})
    {
      if( !findStateConflicts( $functions{$addr}{state0}, $instructions[$addr]->{state} ) )
      {
        say STDERR
          sprintf 'WARNING: inconsistent state at start of different calls to a function at 0x%x', $addr;
      }

      # At this point I should be able to skip tracing this function, since I've already done
      # it. Unfortunately, the return-from-call tracing is implemented by lookintg at the local call
      # stack, so I MUST retrace it. I should reimplement the return handling so that I can be more
      # efficient about this
    }

    %functionContext = (state0 => $instructions[$addr]->{state}, memberInstructions => new Set::IntSpan);
    $functions{$addr} = \%functionContext;;

    if( @$callstack > 25)
    {
      say sprintf 'WARNING: call stack too deep at 0x%x', $addr;
      return;
    }

    my @totrace = ($addr);

    while(defined (my $addr = shift @totrace) )
    {
      my $instruction = $instructions[$addr];
      if(!defined $instruction || !defined $instruction->{addr})
      {
        say STDERR sprintf 'WARNING: ended up at 0x%x, which isn\'t defined. Where am I?', $addr;
        next;
      }

      # skip if I've already traced this instruction. Otherwise, mark it as traced and move on
      next if( $functionContext{memberInstructions}->member($addr) );
      $functionContext{memberInstructions}->insert($addr);

      # first, handle anything that needs to happen in the instruction itself
      push @{$instruction->{callstack}}, $callstack;
      expandArguments($instruction);
      my $newstate = updateState($addr);

      # now handle the program flow
      my $addrto;

      if ($instruction->{mnemonic} eq 'goto')
      {
        $addrto = $instruction->{arg1_expanded_num};
      }
      elsif ($instruction->{mnemonic} =~ /btfs.|..cfsz/)
      {
        # handle the next instruction normally
        $addrto = $addr + 1;

        # handle the skipped instruction case later
        addExecutionPath($addr, $addr + 2, $newstate, \@totrace);
      }
      elsif ($instruction->{mnemonic} eq 'call')
      {
        $addrto = $instruction->{arg1_expanded_num};

        # I add the call execution link, but do NOT add it to @totrace, since
        # I'll recursively trace it
        addExecutionPath($addr, $addrto, $newstate);
        traceFunctionCall($addrto, $isisr, [@$callstack, $addr + 1]);

        # continue tracing from the call return. Note that the state has changed
        # at this point, but I'm adding the old one to the list. This is WRONG
        $addrto = $addr + 1;
        push @totrace, $addrto;
        next;

      }
      elsif ($instruction->{mnemonic} =~ /return|retlw/)
      {
        if(!@$callstack)
        {
          say STDERR sprintf('WARNING: 0x%x: returning, but call stack empty!', $addr);
          next;
        }

        $addrto = $callstack->[$#$callstack];
        addExecutionPath($addr, $addrto, $newstate);
        next;
      }
      elsif ($instruction->{mnemonic} =~ /retfie/)
      {
        if(!$isisr)
        {
          say STDERR sprintf('WARNING: 0x%x: retfie, but not in an isr!', $addr);
        }

        if(@$callstack)
        {
          say STDERR sprintf('WARNING: 0x%x: retfie, but nonempty call stack!', $addr);
        }

        next;
      }
      else
      {
        # simple linear execution. I can go only to the immediately next instruction
        $addrto = $addr + 1;
      }

      addExecutionPath($addr, $addrto, $newstate, \@totrace);
    }
  }

  sub updateState
  {
    my ($addr) = @_;

    my $instruction = $instructions[$addr];
    my $newstate    = dclone( $instruction->{state} );

    if ($instruction->{writes_f})
    {
      handleWriteF_bankless($addr, $newstate, 'PCLATH');
      handleWriteF_bankless($addr, $newstate, 'STATUS');
    }

    if ( $instruction->{writes_w} )
    {
      if ( $instruction->{mnemonic} eq 'movlw' )
      { $newstate->{w} = $instruction->{arg1}; }
      else
      {
        # there will be way to many of these
        #        say STDERR sprintf 'WARNING: manipulating W with $instruction->{mnemonic} in 0x%x not yet supported', $addr;
      }
    }

    return $newstate;
  }

  sub handleWriteF_bankless
  {
    my ($addr, $newstate, $reg) = @_;
    my $regaddr = $regaddrs{$reg};

    my $instruction = $instructions[$addr];

    if (defined $instruction->{arg1} && $instruction->{arg1} == $regaddr)
    {
      if ($instruction->{mnemonic} eq 'bsf')
      { $newstate->{$reg} |=  (1 << $instruction->{arg2}); }
      elsif ($instruction->{mnemonic} eq 'bcf')
      { $newstate->{$reg} &= ~(1 << $instruction->{arg2}); }
      elsif ($instruction->{mnemonic} eq 'movwf')
      { $newstate->{$reg} = $newstate->{w}; }
      else
      {
        say STDERR sprintf 'WARNING: manipulating $reg with $instruction->{mnemonic} in 0x%x not yet supported', $addr;
      }
    }
  }

  sub findStateConflicts
  {
    my ($state0, $state1) = @_;

    if( $state0->{PCLATH} != $state1->{PCLATH} )
    {
      my $xor = $state0->{PCLATH} ^ $state1->{PCLATH};
      say STDERR sprintf 'WARNING: PCLATH off bits: 0x%x', $xor;
      return undef;
    }

    # should check for w conflicts here, but there will be many
    return 1;
  }

  sub addExecutionPath
  {
    my ($addrfrom, $addrto, $newstate, $totrace) = @_;
    $instructions[$addrfrom]->{to  }{$addrto  } = 1;
    $instructions[$addrto  ]->{from}{$addrfrom} = 1;

    # before I store the new CPU state, I check for conflicts
    if(defined $instructions[$addrto  ]->{state} &&
       !findStateConflicts($instructions[$addrto  ]->{state}, $newstate))
    {
      say STDERR sprintf 'WARNING: state conflict in 0x%x', $addrto;
    }

    $instructions[$addrto  ]->{state} = $newstate;

    push( @$totrace, $addrto ) if defined $totrace;
  }
}

sub parseIncludeFile
{
  open INC, '<', '/usr/share/gputils/header/p16f876a.inc' or die "Couldn't open include";

  my ($mode, $reg);
  while(<INC>)
  {
    if(/^;-+[^-].*(files|bits)/i)
    {
      $mode = lc $1;

      if ($mode eq 'bits')
      {
        ($reg) = /([a-z0-9_]+)\s+Bits/i;
        if (!defined $reg)
        {
          say STDERR "Couldn't parse line $_";
          $mode = undef;
        }
      }

      next;
    }
    elsif( defined $mode )
    {
      next if /^;/;
      next unless my ($var, $val) = /^(\S+)\s+equ\s+h'([0-9a-z]+)'/i;
      $val = hex $val;

      if ($mode eq 'files')
      {
        $regaddrs{$var} = $val;
        $regmaps {$val} = $var;
      }
      else
      {
        $bitmaps{$reg}{$val}        = $var;
        $bitmaps{$reg}{addrs}{$var} = $val;
      }
    }
  }

  close INC;
}

# The PIC include files do not include the redundant register mappings so I add them here manually
sub addExtraRegisterMappings
{
  $regmaps{0x180} = $regmaps{0x100} = $regmaps{0x80} = $regmaps{0x0};
  $regmaps{0x101} = $regmaps{0x001};
  $regmaps{0x181} = $regmaps{0x081};
  $regmaps{0x182} = $regmaps{0x102} = $regmaps{0x82} = $regmaps{0x2};
  $regmaps{0x183} = $regmaps{0x103} = $regmaps{0x83} = $regmaps{0x3};
  $regmaps{0x184} = $regmaps{0x104} = $regmaps{0x84} = $regmaps{0x4};
  $regmaps{0x106} = $regmaps{0x006};
  $regmaps{0x186} = $regmaps{0x086};
  $regmaps{0x18a} = $regmaps{0x10a} = $regmaps{0x8a} = $regmaps{0xa};
  $regmaps{0x18b} = $regmaps{0x10b} = $regmaps{0x8b} = $regmaps{0xb};
}

sub expandArguments
{
  my ($instruction) = @_;

  my $arg1          = \$instruction->{arg1};
  my $arg2          = \$instruction->{arg2};
  $instruction->{arg1_expanded_num}   = $$arg1;
  $instruction->{arg2_expanded_num}   = $$arg2;
  $instruction->{arg1_expanded_print} = $$arg1;
  $instruction->{arg2_expanded_print} = $$arg2;
  my $arg1_expanded_num   = \$instruction->{arg1_expanded_num};
  my $arg2_expanded_num   = \$instruction->{arg2_expanded_num};
  my $arg1_expanded_print = \$instruction->{arg1_expanded_print};
  my $arg2_expanded_print = \$instruction->{arg2_expanded_print};

  if ($instruction->{accesses_f} && defined $instruction->{arg1})
  {
    if (defined $instruction->{state} && defined $instruction->{state}{STATUS})
    {
      # grab the full register address, taking into account banking
      $$arg1_expanded_num |= 0x80  if $instruction->{state}{STATUS} & (1 << $bitmaps{STATUS}{addrs}{RP0});
      $$arg1_expanded_num |= 0x100 if $instruction->{state}{STATUS} & (1 << $bitmaps{STATUS}{addrs}{RP1});
      $$arg1_expanded_print = $$arg1_expanded_num;

      # convert register address to its name
      $$arg1_expanded_print = $regmaps{$$arg1_expanded_num} if defined $regmaps{$$arg1_expanded_num};

      # If arg2 is a bit access instruction, convert arg2 to the name of the bit
      if ($instruction->{accesses_bit} && defined $bitmaps{$$arg1_expanded_print}{$$arg2})
      {
        $$arg2_expanded_print = $bitmaps{$$arg1_expanded_print}{$$arg2};
      }
    }
  }

  if ( $instruction->{jmps} )
  {
    # The PIC16 architecture has 13-bit program instruction pointers. PCL is an
    # 8-bit register, so the upper 5 bits must come from elsewhere.
    #
    # direct PCL manipulations use the lower 5 bits of PCLATH.

    # call/goto instruction contain 11 bits in the opcode, with the rest coming
    # from the upper 2 bits of the lower 5 bits of PCLATH. This masks to 0x18
    # and I hardcode it since it's fundamental to the PIC16
    $$arg1_expanded_num  += ($instruction->{state}{PCLATH} & 0x18) << 8;
    $$arg1_expanded_print = $$arg1_expanded_num;
  }


  foreach($$arg1_expanded_print, $$arg2_expanded_print)
  {
    $_ = sprintf('0x%x', $_) if defined $_ && /^[0-9]*$/;
  }
}

sub markUninteresting
{
  foreach my $instruction (@instructions)
  {
    next unless defined($instruction->{addr});
    next unless $instruction->{writes_f};
    if($instruction->{arg1_expanded_print} =~ /PCLATH/)
    {
      $instruction->{uninteresting} = 1;
      next
    }

    if($instruction->{arg1_expanded_print} =~ /STATUS/ &&
       $instruction->{mnemonic} =~ /^b[cs]f$/ &&
       $instruction->{arg2_expanded_print} =~ /^RP[01]$/)
    {
      $instruction->{uninteresting} = 1;
      next
    }
  }
}

sub markFunctionBounds
{
  my @functionbounds;

 FUNCTIONLOOP:
  foreach my $funcaddr (sort {$a <=> $b} keys %functions)
  {
    my $context = $functions{$funcaddr};

    if($context->{memberInstructions}->min != $funcaddr)
    {
      say STDERR sprintf('WARNING: Function at 0x%x has addrmin at 0x%x. Should be the same',
                         $funcaddr, $context->{memberInstructions}->min);
      next;
    }

    if($context->{memberInstructions}->holes)
    {
      say STDERR sprintf('WARNING: Function at 0x%x has holes', $funcaddr);
      next;
    }

    foreach my $addr ($context->{memberInstructions}->elements)
    {
      next if $addr == $funcaddr;

      foreach my $addrfrom (keys %{$instructions[$addr]{from}})
      {
        if( ! $context->{memberInstructions}->member($addrfrom) &&
            !$instructions[$addrfrom]->{returns})
        {
          say STDERR
            sprintf('WARNING: Function at 0x%x has instruction at 0x%x coming from 0x%x. NOT in function',
                    $funcaddr, $addr, $addrfrom);
          next FUNCTIONLOOP;
        }
      }
    }

    push @functionbounds, $context->{memberInstructions};
  }

  return \@functionbounds;
}

sub expandConditionals
{
  my ($functionbounds) = @_;

  # look through each verified-selfcontained function
  foreach my $bound (@$functionbounds)
  {
    my $addr    = $bound->min;
    # I'm looking for beginnings of chunks of instructions (at least 2-instructions long). I thus
    # don't need to search the extreme tail
    my $addrmax = $bound->max - 1;

    # look for a branch
    while(1)
    {
      my $conditionalStartIndex = first_index {$instructions[$_]->{mnemonic} =~ /^btfs/} $addr..$addrmax;
      last if $conditionalStartIndex < 0; # keep going as long as we're finding branches

      # move addr to the start of the conditional
      $addr += $conditionalStartIndex;

      # I now look and process the conditional templates I know about

      if($instructions[$addr + 1]->{mnemonic} eq 'goto')
      {
        # skipping over a goto

        if($addr+3 <= $bound->max && $instructions[$addr + 2]->{mnemonic} eq 'goto' &&
           $instructions[$addr + 1]->{arg1_expanded_num} == $addr + 3)
            {
          }

        # skipping a goto. Expand it and move on if successful. If not successful, fall through and
        # expand less fully
        handleSkipOverGoto($addr, $addr+1) and next;
      }

      # skipping over something that's not a goto. This is a 1-instruction-block if
      my $action = $instructions[$addr]->{mnemonic} eq 'btfsc' ? 'set' : 'clear';

      $instructions[$addr]->{annotated} =
        "if ($action $instructions[$addr]->{arg1_expanded_print}.$instructions[$addr]->{arg2_expanded_print})";
      addIndent($addr + 1);
    }
    continue
    {
      # go to next instruction. don't search for the branch in the same place, since we handle it as
      # soon as we find it
      $addr++;
    }
  }
}

sub handleSkipOverGoto
{
  my ($addr_branch, $addr_goto, $reversed_action) = @_;
  my $goto_target = $instructions[$addr_goto]->{arg1_expanded_num};

  my @actions = qw(clear set);

  my $action = ($instructions[$addr_branch]->{mnemonic} eq 'btfsc') ? 1 : 0;
  if($reversed_action) { $action ^= 1; };

  # skipping over a single goto
  # are we going forwards or backwards?
  if ($goto_target > $addr_goto)
  {
    # the skipped goto goes forward

    # If I can successfully indent the section, I do that and proceed. Otherwise
    # treat this branch as a single-instruction if
    if ( addIndent( $addr_branch + 1, $goto_target - 1) )
    {
      $instructions[$addr_branch]->{annotated} =
        "if ($actions[$action ^ 1] $instructions[$addr_branch]->{arg1_expanded_print}.$instructions[$addr_branch]->{arg2_expanded_print})";
      $instructions[$addr_goto]->{uninteresting} = 1;

      return 1;
    }
  }
  else
  {
    # the skipped goto goes backward

    # If I can successfully indent the section, I do that and proceed. Otherwise
    # treat this branch as a single-instruction if
    if ( addIndent( $goto_target, $addr_branch - 1 ))
    {
      $instructions[$addr_branch]->{annotated} =
        "while ($actions[$action] $instructions[$addr_branch]->{arg1_expanded_print}.$instructions[$addr_branch]->{arg2_expanded_print})";
      $instructions[$addr_goto]->{uninteresting} = 1;

      return 1;
    }
  }

  return undef;
}

sub addIndent
{
  # This function tries to add an indentation block for the given instruction bounds. If it's
  # possible it returns true, and marks the indentation. If not, it does NOT mark it and returns
  # false
  my $start = $_[0];
  my $end   = $_[$#_] // $start;

  if($start > $end)
  {
    $instructions[$start]->{indent_startend} = 1;
    return 1;
  }

  my $count = 0;
  foreach my $addr ($start..$end)
  {
    $count += $instructions[$addr]->{indent_start} unless $addr == $start;
    $count -= $instructions[$addr]->{indent_end}   unless $addr == $end;
  }

  if($count != 0)
  { return undef; }

  # All seems good so I go ahead and indent the section
  $instructions[$start]->{indent_start}++;
  $instructions[$end  ]->{indent_end}  ++;

  return 1;
}

sub indented
{
  return ('  ' x $_[1]) . $_[0];
}

sub printAnnotated
{
  my ($functionbounds) = @_;
  my $nextFunc = shift @$functionbounds if @$functionbounds;

  my $indent = 0;

  foreach my $instruction (@instructions)
  {
    next if !defined  $instruction->{line};

    if(defined $nextFunc)
    {
      if($instruction->{addr} > $nextFunc->max)
      {
        say "}}}}}}}}}}}}}}}} function\n";
        $nextFunc = shift @$functionbounds if @$functionbounds;
      }
      if ($instruction->{addr} == $nextFunc->min)
      {
        say 'function {{{{{{{{{{{{{{{{';
      }
    }

    # handle the bookeeping of the indentation starts
    if($instruction->{indent_startend})
    { say indented('{}', $indent); }
    foreach(1..$instruction->{indent_start})
    { say indented('{', $indent++); }

    my $annotated = $instruction->{annotated} // '';
    if(!$annotated && !$instruction->{uninteresting})
    {
      $annotated .= sprintf '%-10s', $instruction->{mnemonic};
      if(defined $instruction->{arg1_expanded_print})
      {
        $annotated .= $instruction->{arg1_expanded_print};
        if (defined $instruction->{arg2_expanded_print})
        {
          $annotated .= ', ' . $instruction->{arg2_expanded_print};
        }
      }
    }

    $annotated = indented($annotated, $indent);

    printf "%-40s; %s\n", $annotated, $instruction->{line};

    # handle the bookeeping of the indentation ends
    foreach(1..$instruction->{indent_end})
    { say indented('}', --$indent); }
  }
}
