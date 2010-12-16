#!/usr/bin/perl
use strict;
use warnings;
use feature qw(say);
use List::MoreUtils qw(indexes);
use Data::Dumper;
use Text::Tabs;

my (%regaddrs, %regmaps, %bitmaps);
parseIncludeFile();
addExtraRegisterMappings();

my @lines = expand <>; # slurp all lines, convert tabs to spaces

my @instructions;

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

                          # persistent state at the beginning of this instruction
                          state     => {},

                          # different possibilities for the call stack when we get here
                          callstack => []};

  $instructions[$addr]{writes_w} =
    ( defined $arg2 && $arg2 eq 'w') || $mnemonic =~ /w$/;

  $instructions[$addr]{writes_f} =
    ( defined $arg2 && $arg2 eq 'f') || ($mnemonic =~ /f$/ && (!defined $arg2 || $arg2 ne 'w'));

  $instructions[$addr]{accesses_f} = $mnemonic =~ /f$|btfs|cfsz/;

  $instructions[$addr]{returns} = $mnemonic =~ /return|retlw|retfie/;

  if(defined $arg1 && $arg1 == $regaddrs{PCL} && $instructions[$addr]{writes_f})
  {
    say sprintf "WARNING: Manipulating PCL in 0x%x. Not supported yet", $addr;
  }
}

traceProgramFlow();

my @instructions_undefined   = indexes {!defined $_ || !defined $_->{addr} } @instructions;
my @instructions_unreachable = grep { defined $_ && !%{$_->{from}}         } @instructions;

if(0)
{
  foreach(@instructions_undefined  ) { say sprintf "Undefined   instruction at 0x%x", $_; }
  foreach(@instructions_unreachable) { say sprintf "Unreachable instruction at 0x%x", $_->{addr}; }
}

mapRegisters();
printAnnotated();

sub traceProgramFlow
{
  # pclath is upper 5 bits of the program counter, stored at a bit vector if I'm
  # manipulating PCL, all 5 are used. A call or goto uses only the top 2
  # bits. 'x' means unknown/inconsistent value
  my $originalstate = {pclath => 0,
                       status => 0,
                       w      => 0};

  # trace all execution paths from the start of the program
  traceCall(0, [], $originalstate);

  # trace all execution paths from the start of the ISR
  traceCall(4, [], $originalstate, 'isr');

  sub traceCall
  {
    my ($addr, $callstack, $state, $isisr) = @_;

    if( @$callstack > 25)
    {
      say "WARNING: call stack too deep";
      return;
    }

    my %traced  = ();
    my @totrace = ([$addr, $state]);

    while(defined (my $traceElement = shift @totrace) )
    {
      ($addr, $state) = @$traceElement;

      my $instruction = $instructions[$addr];
      if(!defined $instruction || !defined $instruction->{addr})
      {
        say STDERR sprintf "WARNING: ended up at 0x%x, which isn't defined. Where am I?", $addr;
        next;
      }

      if( $traced{$addr} )
      {
        findStateConflicts($state, $instruction->{state}) or
          say STDERR sprintf "WARNING: state conflict in 0x%x", $addr;
        next;
      }

      # first, handle anything that needs to happen in the instruction itself
      push @{$instruction->{callstack}}, $callstack;
      %{$instruction->{state}} = %$state;
      updateState($instruction, $state, $addr);

      # now handle the program flow
      my $addrto;

      if ($instruction->{mnemonic} eq 'goto')
      {
        $addrto = $instruction->{arg1};
        $addrto +=
          ($state->{pclath} & 0x18) << 8;
      }
      elsif ($instruction->{mnemonic} =~ /btfs.|..cfsz/)
      {
        # handle the next instruction normally
        $addrto = $addr + 1;

        # handle the skipped instruction case later
        addExecutionPath($addr, $addr + 2, $state, \%traced, \@totrace);
      }
      elsif ($instruction->{mnemonic} eq 'call')
      {
        $addrto = $instruction->{arg1};
        $addrto +=
          ($state->{pclath} & 0x18) << 8;

        # I add the call execution link, but do NOT add it to @totrace, since
        # I'll recursively trace it
        addExecutionPath($addr, $addrto, $state, \%traced);

        traceCall($addrto, [@$callstack, $addr + 1], $state, $isisr);

        # continue tracing from the call return. Note that the state has changed
        # at this point, but I'm adding the old one to the list. This is WRONG
        $addrto = $addr + 1;
        push @totrace, [$addrto, $state];
        next;

      }
      elsif ($instruction->{mnemonic} =~ /return|retlw/)
      {
        if(!@$callstack)
        {
          say STDERR sprintf("WARNING: 0x%x: returning, but call stack empty!", $addr);
          next;
        }

        $addrto = $callstack->[$#$callstack];
        addExecutionPath($addr, $addrto, $state, \%traced);
        next;
      }
      elsif ($instruction->{mnemonic} =~ /retfie/)
      {
        if(!$isisr)
        {
          say STDERR sprintf("WARNING: 0x%x: retfie, but not in an isr!", $addr);
        }

        if(@$callstack)
        {
          say STDERR sprintf("WARNING: 0x%x: retfie, but nonempty call stack!", $addr);
        }

        next;
      }
      else
      {
        # simple linear execution. I can go only to the immediately next instruction
        $addrto = $addr + 1;
      }

      addExecutionPath($addr, $addrto, $state, \%traced, \@totrace);
    }


  }

  sub updateState
  {
    my ($instruction, $state, $addr) = @_;

    if ($instruction->{writes_f})
    {
      handleWriteF_bankless($instruction, $state, $addr, $regaddrs{PCLATH}, 'pclath');
      handleWriteF_bankless($instruction, $state, $addr, $regaddrs{STATUS}, 'status');
    }

    if ( $instruction->{writes_w} )
    {
      if ( $instruction->{mnemonic} eq 'movlw' )
      { $state->{w} = $instruction->{arg1}; }
      else
      {
        # there will be way to many of these
        #        say STDERR sprintf "WARNING: manipulating W with $instruction->{mnemonic} in 0x%x not yet supported", $addr;
      }
    }
  }

  sub handleWriteF_bankless
  {
    my ($instruction, $state, $addr, $REG, $reg) = @_;

    if (defined $instruction->{arg1} && $instruction->{arg1} == $REG)
    {
      if ($instruction->{mnemonic} eq 'bsf')
      { $state->{$reg} |=  (1 << $instruction->{arg2}); }
      elsif ($instruction->{mnemonic} eq 'bcf')
      { $state->{$reg} &= ~(1 << $instruction->{arg2}); }
      elsif ($instruction->{mnemonic} eq 'movwf')
      { $state->{$reg} = $state->{w}; }
      else
      {
        say STDERR sprintf "WARNING: manipulating $reg with $instruction->{mnemonic} in 0x%x not yet supported", $addr;
      }
    }
  }

  sub findStateConflicts
  {
    my ($state0, $state1) = @_;

    return undef if $state0->{pclath} != $state0->{pclath};

    # should check for w conflicts here, but there will be many
    return 1;
  }

  sub addExecutionPath
  {
    my ($addrfrom, $addrto, $state, $traced, $totrace) = @_;
    $instructions[$addrto  ]->{from}{$addrfrom} = 1;
    $instructions[$addrfrom]->{to  }{$addrto  } = 1;
    $traced->{$addrfrom} = 1;
    push( @$totrace, [$addrto, $state] ) if defined $totrace;
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

sub mapRegisters
{
  foreach my $instruction (@instructions)
  {
    next unless defined $instruction && defined $instruction->{mnemonic};

    if(!%{$instruction->{from}})
    {
      $instruction->{annotated} = 'unreachable';
      next;
    }

    my $annotated = "$instruction->{mnemonic}	";
    my $arg1 = $instruction->{arg1};
    my $arg2 = $instruction->{arg2};
    if($instruction->{accesses_f} && defined $arg1)
    {
      my $state = $instruction->{state};
      if(defined $state->{status})
      {
        $arg1 |= 0x80  if $state->{status} & (1 << $bitmaps{STATUS}{addrs}{RP0});
        $arg1 |= 0x100 if $state->{status} & (1 << $bitmaps{STATUS}{addrs}{RP1});

        $arg1 = $regmaps{$arg1} if defined $regmaps{$arg1};
        if (defined $arg2 && defined $bitmaps{$arg1}{$arg2})
        {
          $arg2 = $bitmaps{$arg1}{$arg2};
        }
      }
    }

    if(defined $arg1)
    {
      $annotated .= $arg1;
      if(defined $arg2)
      {
        $annotated .= ", $arg2";
      }
    }

    $instruction->{annotated} = $annotated;
  }
}

sub printAnnotated
{
  foreach my $instruction (@instructions)
  {
    next if !defined $instruction->{line};
    printf "%-40s", $instruction->{line};

    next if !defined $instruction->{annotated};

    print "; $instruction->{annotated}";

    # extra newline if we're returning. This increases visibility of functions
    if($instruction->{returns}) { print "\n"; }
  }
  continue
  {
    print "\n";
  }
}
