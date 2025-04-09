#! /usr/local/bin/perl -w

# Test the formula parser.  Inputs a formula in a fairly liberal
# format and prints it back in a standardized form.

use utf8;
use strict;
use warnings;

use constant {
    VARIABLE => 0,
    LOGICAL_TRUE => 1,
    LOGICAL_FALSE => 2,
    LOGICAL_AND => 3,
    LOGICAL_OR => 4,
    LOGICAL_IMP => 5,
    LOGICAL_NOT => 6
};

use Regexp::Grammars;
use Data::Dump qw(dump);

binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";

my $nbvariables = 0;
my @variable_names;
my %variable_nums;

my $formula_parser = qr{
   ^<Expr>$
   <rule: Expr>		<OrExpr> ( (?:⇒|\=\>|→|\-\>) <ImpExpr=Expr> )?
   <rule: OrExpr>	<[AndExpr]>+ % (?:∨|\\\/|\|)
   <rule: AndExpr>	<[NotExpr]>+ % (?:∧|\/\\|\&)
   <rule: NotExpr>	<Atom> | (?:¬|\~) <NotExpr>
   <rule: Atom>		<Variable> | <TrueExpr> | <FalseExpr> | \( <ParenExpr=Expr> \)
   <rule: TrueExpr>	(?:⊤|\_True|1)
   <rule: FalseExpr>	(?:⊥|\_False|0)
   <token: Variable>	[a-zA-Z][a-zA-Z0-9\_]*
}xms;

sub parsetree_to_formula {
    # Convert a parse tree to a formula.  Takes a rule name and a hash
    # as returned by $formula_parser and returns the array
    # representation of this formula.  Calls itself recursively.  Call
    # this with "Expr" as first argument for the overall grammar.
    # Variables are allocated as they are encountered.
    my $u = shift;  # The grammar rule matched at the top level
    my $r = shift;  # Parsing result for this grammar rule
    if ( $u eq "Expr" ) {
	if ( defined($r->{Expr}) ) {
	    # Be liberal: allow for calling on $r or $r->{Expr} indifferently.
	    return parsetree_to_formula("Expr", $r->{Expr});
	}
	die "this is impossible" unless defined($r->{OrExpr});
	if ( defined($r->{ImpExpr}) ) {
	    return [ LOGICAL_IMP, parsetree_to_formula("OrExpr", $r->{OrExpr}),
		     parsetree_to_formula("Expr", $r->{ImpExpr}) ];
	} else {
	    return parsetree_to_formula("OrExpr", $r->{OrExpr});
	}
    } elsif ( $u eq "OrExpr" ) {
	die "this is impossible"
	    unless defined($r->{AndExpr}) && ref($r->{AndExpr}) eq "ARRAY";
	if ( scalar(@{$r->{AndExpr}}) == 1 ) {
	    return parsetree_to_formula("AndExpr", $r->{AndExpr}->[0]);
	} else {
	    my @f = ( LOGICAL_OR );
	    foreach my $rr ( @{$r->{AndExpr}} ) {
		push @f, parsetree_to_formula("AndExpr", $rr);
	    }
	    return \@f;
	}
    } elsif ( $u eq "AndExpr" ) {
	die "this is impossible"
	    unless defined($r->{NotExpr}) && ref($r->{NotExpr}) eq "ARRAY";
	if ( scalar(@{$r->{NotExpr}}) == 1 ) {
	    return parsetree_to_formula("NotExpr", $r->{NotExpr}->[0]);
	} else {
	    my @f = ( LOGICAL_AND );
	    foreach my $rr ( @{$r->{NotExpr}} ) {
		push @f, parsetree_to_formula("NotExpr", $rr);
	    }
	    return \@f;
	}
    } elsif ( $u eq "NotExpr" ) {
	die "this is impossible" unless defined($r->{Atom}) || defined($r->{NotExpr});
	die "this is impossible" if defined($r->{Atom}) && defined($r->{NotExpr});
	if ( defined($r->{NotExpr}) ) {
	    return [ LOGICAL_NOT, parsetree_to_formula("NotExpr", $r->{NotExpr}) ];
	} else {
	    return parsetree_to_formula("Atom", $r->{Atom});
	}
    } elsif ( $u eq "Atom" ) {
	die "this is impossible" unless defined($r->{Variable}) + defined($r->{TrueExpr}) + defined($r->{FalseExpr}) + defined($r->{ParenExpr}) == 1;
	if ( defined($r->{ParenExpr}) ) {
	    return parsetree_to_formula("Expr", $r->{ParenExpr});
	} elsif ( defined($r->{TrueExpr}) ) {
	    return [ LOGICAL_TRUE ];
	} elsif ( defined($r->{FalseExpr}) ) {
	    return [ LOGICAL_FALSE ];
	} else {
	    return parsetree_to_formula("Variable", $r->{Variable});
	}
    } elsif ( $u eq "Variable" ) {
	my $varname = $r;
	die "this is impossible" unless scalar(@variable_names) == $nbvariables;
	if ( defined($variable_nums{$varname}) ) {
	    return [ VARIABLE, $variable_nums{$varname} ];
	} else {
	    push @variable_names, $varname;
	    $variable_nums{$varname} = $nbvariables;
	    $nbvariables++;
	    return [ VARIABLE, $variable_nums{$varname} ];
	}
    } else {
	die "this is impossible";
    }
}

sub formula_text {
    # Convert a formula to (Unicode!) text.  Note that this is not
    # just used for display/documentation purposes, but also
    # internally to avoid useless reduplication of SAT problem
    # variables.
    my $formula = shift;
    my $priority = shift // 0;  # At which priority to parenthesize.
    my $fullparen = shift;
    die "not a formula" unless ref($formula) eq "ARRAY";
    if ( $formula->[0] == VARIABLE ) {
	die "not a formula" unless scalar(@{$formula}) == 2;
	my $r = $formula->[1];  # Variable number
	die "variable out of bounds" unless $r>=0 && $r<$nbvariables;
	return $variable_names[$r];
    } elsif ( $formula->[0] == LOGICAL_TRUE ) {
	return "⊤";
    } elsif ( $formula->[0] == LOGICAL_FALSE ) {
	return "⊥";
    } elsif ( $formula->[0] == LOGICAL_AND ) {
	my $s = "";
	my $fence = ($priority>=3) || $fullparen;
	$s .= "(" if $fence;
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    $s .= "∧" if $i>=2;
	    $s .= formula_text($formula->[$i], 3, $fullparen);
	}
	$s .= ")" if $fence;
	return $s;
    } elsif ( $formula->[0] == LOGICAL_OR ) {
	my $s = "";
	my $fence = ($priority>=2) || $fullparen;
	$s .= "(" if $fence;
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    $s .= "∨" if $i>=2;
	    $s .= formula_text($formula->[$i], 2, $fullparen);
	}
	$s .= ")" if $fence;
	return $s;
    } elsif ( $formula->[0] == LOGICAL_IMP ) {
	die "not a formula" unless scalar(@{$formula}) == 3;
	my $s = "";
	my $fence = ($priority>=1) || $fullparen;
	$s .= "(" if $fence;
	$s .= formula_text($formula->[1], 1, $fullparen);
	$s .= "⇒";
	$s .= formula_text($formula->[2], 0, $fullparen);
	$s .= ")" if $fence;
	return $s;
    } elsif ( $formula->[0] == LOGICAL_NOT ) {
	die "not a formula" unless scalar(@{$formula}) == 2;
	my $s = "";
	my $fence = ($priority>=4) || $fullparen;
	$s .= "(" if $fence;
	$s .= "¬";
	$s .= formula_text($formula->[1], 3, $fullparen);
	$s .= ")" if $fence;
	return $s;
    }
}

while (<>) {
    if ( $_ =~ $formula_parser) {
	# dump(\%/);
	my $f = parsetree_to_formula("Expr", \%/);
	# dump($f);
	print formula_text($f), "\n";
	print "Fully parenthesized:\n", formula_text($f, undef, 1), "\n";
    } else {
	print "Parse failure\n";
    }
}
