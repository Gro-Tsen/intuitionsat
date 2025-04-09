#! /usr/local/bin/perl -w

# Use a SAT-solver to decide whether an intuitionistic formula holds
# in a given Kripke frame.  (Work in progress.)

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

binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";

## THIS IS THE FRAME:

my $nbnodes = 5;
my @node_names = ( "u0", "u1", "u2", "u3", "u4" );
my @frame_edges = (
    [0,1], [0,2], [2,3], [2,4]
);

# my $nbnodes = 4;
# my @node_names = ( "u0", "u1", "u2", "u3" );
# my @frame_edges = (
#     [0,1], [0,2], [0,3], [2,4]
# );

## THIS IS THE FORMULA:

my $nbvariables = 3;
my @variable_names = ( "p1", "p2", "p3" );
my $formula = [
    LOGICAL_IMP,
    [ LOGICAL_AND,
      [ LOGICAL_NOT, [ LOGICAL_AND, [VARIABLE, 1], [VARIABLE, 2] ] ],
      [ LOGICAL_NOT, [ LOGICAL_AND, [VARIABLE, 0], [VARIABLE, 2] ] ],
      [ LOGICAL_NOT, [ LOGICAL_AND, [VARIABLE, 0], [VARIABLE, 1] ] ],
      [ LOGICAL_IMP, [ LOGICAL_NOT, [ VARIABLE, 0 ] ],
	[ LOGICAL_OR, [VARIABLE, 1], [VARIABLE, 2] ] ],
      [ LOGICAL_IMP, [ LOGICAL_NOT, [ VARIABLE, 1 ] ],
	[ LOGICAL_OR, [VARIABLE, 0], [VARIABLE, 2] ] ],
      [ LOGICAL_IMP, [ LOGICAL_NOT, [ VARIABLE, 2 ] ],
	[ LOGICAL_OR, [VARIABLE, 0], [VARIABLE, 1] ] ] ],
    [ LOGICAL_OR, [VARIABLE, 0], [VARIABLE, 1], [VARIABLE, 2] ]
];

# my $nbvariables = 4;
# my @variable_names = ( "p1", "p2", "p3", "q" );
# my $formula = [
#     LOGICAL_IMP,
#     [ LOGICAL_AND,
#       [ LOGICAL_NOT, [ LOGICAL_AND, [VARIABLE, 1], [VARIABLE, 2] ] ],
#       [ LOGICAL_NOT, [ LOGICAL_AND, [VARIABLE, 0], [VARIABLE, 2] ] ],
#       [ LOGICAL_NOT, [ LOGICAL_AND, [VARIABLE, 0], [VARIABLE, 1] ] ],
#       [ LOGICAL_IMP, [ LOGICAL_NOT, [ VARIABLE, 0 ] ],
# 	[ LOGICAL_OR, [ LOGICAL_NOT, [ VARIABLE, 3 ] ],
# 	  [ LOGICAL_NOT, [ LOGICAL_NOT, [ VARIABLE, 3 ] ] ] ] ],
#       [ LOGICAL_IMP, [ LOGICAL_NOT, [ VARIABLE, 1 ] ],
# 	[ LOGICAL_OR, [ LOGICAL_NOT, [ VARIABLE, 3 ] ],
# 	  [ LOGICAL_NOT, [ LOGICAL_NOT, [ VARIABLE, 3 ] ] ] ] ],
#       [ LOGICAL_IMP, [ LOGICAL_NOT, [ VARIABLE, 2 ] ],
# 	[ LOGICAL_OR, [ LOGICAL_NOT, [ VARIABLE, 3 ] ],
# 	  [ LOGICAL_NOT, [ LOGICAL_NOT, [ VARIABLE, 3 ] ] ] ] ] ],
#     [ LOGICAL_OR, [ LOGICAL_NOT, [ VARIABLE, 3 ] ],
#       [ LOGICAL_NOT, [ LOGICAL_NOT, [ VARIABLE, 3 ] ] ] ]
# ];

sub formula_text {
    # Convert a formula to (Unicode!) text.  Note that this is not
    # just used for display/documentation purposes, but also
    # internally to avoid useless reduplication of SAT problem
    # variables.
    my $formula = shift;
    my $priority = shift // 0;  # At which priority to parenthesize.
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
	my $fence = ($priority>=3);
	$s .= "(" if $fence;
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    $s .= "∧" if $i>=2;
	    $s .= formula_text($formula->[$i], 3);
	}
	$s .= ")" if $fence;
	return $s;
    } elsif ( $formula->[0] == LOGICAL_OR ) {
	my $s = "";
	my $fence = ($priority>=2);
	$s .= "(" if $fence;
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    $s .= "∨" if $i>=2;
	    $s .= formula_text($formula->[$i], 2);
	}
	$s .= ")" if $fence;
	return $s;
    } elsif ( $formula->[0] == LOGICAL_IMP ) {
	die "not a formula" unless scalar(@{$formula}) == 3;
	my $s = "";
	my $fence = ($priority>=1);
	$s .= "(" if $fence;
	$s .= formula_text($formula->[1], 1);
	$s .= "⇒";
	$s .= formula_text($formula->[2], 0);
	$s .= ")" if $fence;
	return $s;
    } elsif ( $formula->[0] == LOGICAL_NOT ) {
	die "not a formula" unless scalar(@{$formula}) == 2;
	my $s = "";
	my $fence = ($priority>=4);
	$s .= "(" if $fence;
	$s .= "¬";
	$s .= formula_text($formula->[1], 3);
	$s .= ")" if $fence;
	return $s;
    }
}

# List of SAT problem variables: each one is a ref to an array of 3 items:
# ->[0] is the index back in the @satvars array itself.
# ->[1] is the textual formula whose validity is asserted.
# ->[2] is the number of the node where it is asserted.
# (Variable 0 is a dummy variable because SAT-solvers number from 1.)
my @satvars = ( [0, "INVALID", 0 ] );

# The SAT problem variables corresponding to the main formula
# variables: each one is a ref to an array of indexes in @satvar for
# the SAT variables asserting the validity of the formula variable in
# question at a given node.
my @variable_satvars;

# The SAT variables corresponding to the subformulas (indexed by the
# _textual_ formula): each one is a ref to an array of indexes in
# @satvar for the SAT variables asserting the validity of the
# subformula in question at a given node.
my %subformula_satvars;

sub allocate_formula_variables {
    # Allocate (and number) SAT variables for each variable and
    # subformula in the given formula.  Calls itself recursively: call
    # this just once on the main formula.
    my $formula = shift;
    die "not a formula" unless ref($formula) eq "ARRAY";
    my $formula_text = formula_text($formula);
    if ( $formula->[0] == VARIABLE ) {
	die "not a formula" unless scalar(@{$formula}) == 2;
	my $r = $formula->[1];
	die "variable out of bounds" unless $r>=0 && $r<$nbvariables;
	if ( defined($variable_satvars[$r]) != defined($subformula_satvars{$formula_text}) ) {
	    die "internal inconsistency";
	} elsif ( ! defined($subformula_satvars{$formula_text}) ) {
	    for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
		my $k = scalar(@satvars);
		$variable_satvars[$r][$nd] = $k;
		$subformula_satvars{$formula_text}[$nd] = $k;
		push @satvars, [ $k, $formula_text, $nd ];
	    }
	}
    } else {
	if ( ! defined($subformula_satvars{$formula_text}) ) {
	    for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
		my $k = scalar(@satvars);
		$subformula_satvars{$formula_text}[$nd] = $k;
		push @satvars, [ $k, $formula_text, $nd ];
	    }
	}
    }
    if ( $formula->[0] == LOGICAL_AND || $formula->[0] == LOGICAL_OR ) {
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    allocate_formula_variables($formula->[$i]);
	}
    } elsif ( $formula->[0] == LOGICAL_IMP ) {
	die "not a formula" unless scalar(@{$formula}) == 3;
	allocate_formula_variables($formula->[1]);
	allocate_formula_variables($formula->[2]);
    } elsif ( $formula->[0] == LOGICAL_NOT ) {
	die "not a formula" unless scalar(@{$formula}) == 2;
	allocate_formula_variables($formula->[1]);
    }
}

allocate_formula_variables($formula);

my $global_formula_text = formula_text($formula);
die "this is impossible" unless defined($subformula_satvars{$global_formula_text});

# List of SAT problem clauses: each one is a ref to an array of
# integers indicating which disjunction of variables (for >0 values)
# or negations of variables (for <0 values) is required to be
# satisfied.  The @clauses_comments array is indexed in the same way
# and contains an optional (one-line) comment for each clause.
my @clauses;
my @clauses_comments;

sub add_clause {
    # Add a clause to the list.
    my $cl = shift;
    my $cmt = shift;
    my $c = scalar(@clauses);
    $clauses_comments[$c] = $cmt if defined($cmt);
    push @clauses, $cl;
}

sub allocate_global_clause {
    # Add the clause expressing failure of the global formula at some
    # node.  Call this once.
    my @cl = ();
    for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	die "this is impossible" unless defined($subformula_satvars{$global_formula_text}[$nd]);
	push @cl, - $subformula_satvars{$global_formula_text}[$nd];
    }
    add_clause \@cl, "global failure of $global_formula_text";
}

sub allocate_formula_clauses {
    # Add a clause expressing validity constraints for a subformula.
    # Calls itself recursively: call this just once on the main
    # formula.
    my $formula = shift;
    die "not a formula" unless ref($formula) eq "ARRAY";
    my $formula_text = formula_text($formula);
    die "this is impossible" unless defined($subformula_satvars{$formula_text});
    if ( $formula->[0] == VARIABLE ) {
	# For a variable, we emit clauses expressing permanence of the
	# variable for every edge.
	die "not a formula" unless scalar(@{$formula}) == 2;
	my $r = $formula->[1];  # Variable number
	die "this is impossible" unless defined($variable_satvars[$r]);
	foreach my $edge ( @frame_edges ) {
	    die "this is impossible" unless defined($variable_names[$r]);
	    my $nd = $edge->[0];
	    my $tnd = $edge->[1];
	    my @cl = ( - $variable_satvars[$r][$nd], $variable_satvars[$r][$tnd] );
	    add_clause \@cl, sprintf("permanence of variable %s on %s->%s", $variable_names[$r], $node_names[$nd], $node_names[$tnd]);
	}
    } elsif ( $formula->[0] == LOGICAL_TRUE ) {
	# For a tautologically true formula, we emit a clause
	# expressing its validity at every node.
	for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	    my @cl = ( $subformula_satvars{$formula_text}[$nd] );
	    add_clause \@cl, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	}
    } elsif ( $formula->[0] == LOGICAL_FALSE ) {
	# For a tautologically false formula, we emit a clause
	# expressing its failure at every node.
	for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	    my @cl = ( - $subformula_satvars{$formula_text}[$nd] );
	    add_clause \@cl, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	}
    } elsif ( $formula->[0] == LOGICAL_AND ) {
	# For a logical conjunction and for each node, we emit single
	# clause (@cl1) expressing the fact that if it fails then one
	# of the conjuncts must fail at the node, as well as one
	# clause per conjunct (@cl) expressing the fact that if the
	# conjunction holds then the conjunct does too.
	for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	    my @cl1 = ( $subformula_satvars{$formula_text}[$nd] );
	    for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
		my $sf_text = formula_text($formula->[$i]);
		die "this is impossible" unless defined($subformula_satvars{$sf_text});
		my @cl = ( - $subformula_satvars{$formula_text}[$nd], $subformula_satvars{$sf_text}[$nd] );
		add_clause \@cl, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
		push @cl1, - $subformula_satvars{$sf_text}[$nd];
	    }
	    add_clause \@cl1, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	}
	# Recurse!
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    allocate_formula_clauses($formula->[$i]);
	}
    } elsif ( $formula->[0] == LOGICAL_OR ) {
	# For a logical disjunct and for each node, we emit single
	# clause (@cl1) expressing the fact that if it holds then one
	# of the disjuncts must hold at the node, as well as one
	# clause per disjunct (@cl) expressing the fact that if the
	# disjunction fails then the disjunct does too.
	for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	    my @cl1 = ( - $subformula_satvars{$formula_text}[$nd] );
	    for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
		my $sf_text = formula_text($formula->[$i]);
		die "this is impossible" unless defined($subformula_satvars{$sf_text});
		my @cl = ( $subformula_satvars{$formula_text}[$nd], - $subformula_satvars{$sf_text}[$nd] );
		add_clause \@cl, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
		push @cl1, $subformula_satvars{$sf_text}[$nd];
	    }
	    add_clause \@cl1, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	}
	# Recurse!
	for ( my $i=1 ; $i<scalar(@{$formula}) ; $i++ ) {
	    allocate_formula_clauses($formula->[$i]);
	}
    } elsif ( $formula->[0] == LOGICAL_IMP ) {
	# For a logical implication and for each node, we emit four
	# kinds of clauses: one (@cl0) expressing the fact that if the
	# implication holds at the node and the protasis does, then
	# the apodosis does too; one for each edge from this node
	# (@cl) expressing permanence of the implication along this
	# edge; one (@cl1p) expressing the fact that if the
	# implication fails at the node then either the protasis holds
	# or the implication fails at one of the nodes reachable from
	# an edge from this node; and one (@cl1a) expressing the fact
	# that if the implication fails at the node then either the
	# protasis fails or the implication fails at one of the nodes
	# reachable from an edge from this node.
	die "not a formula" unless scalar(@{$formula}) == 3;
	my $protasis_text = formula_text($formula->[1]);
	my $apodosis_text = formula_text($formula->[2]);
	die "this is impossible" unless defined($subformula_satvars{$protasis_text});
	die "this is impossible" unless defined($subformula_satvars{$apodosis_text});
	for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	    my @cl0 = ( - $subformula_satvars{$formula_text}[$nd], - $subformula_satvars{$protasis_text}[$nd], $subformula_satvars{$apodosis_text}[$nd] );
	    add_clause \@cl0, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	    my @cl1p = ( $subformula_satvars{$formula_text}[$nd], $subformula_satvars{$protasis_text}[$nd] );
	    my @cl1a = ( $subformula_satvars{$formula_text}[$nd], - $subformula_satvars{$apodosis_text}[$nd] );
	    foreach my $edge ( @frame_edges ) {
		next unless $edge->[0] == $nd;
		my $tnd = $edge->[1];
		my @cl = ( - $subformula_satvars{$formula_text}[$nd], $subformula_satvars{$formula_text}[$tnd] );
		add_clause \@cl, sprintf("permanence of %s on %s->%s", $formula_text, $node_names[$nd], $node_names[$tnd]);
		push @cl1p, - $subformula_satvars{$formula_text}[$tnd];
		push @cl1a, - $subformula_satvars{$formula_text}[$tnd];
	    }
	    add_clause \@cl1p, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	    add_clause \@cl1a, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	}
	# Recurse!
	allocate_formula_clauses($formula->[1]);
	allocate_formula_clauses($formula->[2]);
    } elsif ( $formula->[0] == LOGICAL_NOT ) {
	# For a logical negation and for each node, we emit three
	# kinds of clauses: one (@cl0) expressing the fact that if the
	# negation holds at the node then the refuted formula fails;
	# one for each edge from this node (@cl) expressing permanence
	# of the negation along this edge; one (@cl1) expressing the
	# fact that if the negation fails at the node then either the
	# refuted formula holds or the negation fails at one of the
	# nodes reachable from an edge from this node.
	die "not a formula" unless scalar(@{$formula}) == 2;
	my $refuted_text = formula_text($formula->[1]);
	die "this is impossible" unless defined($subformula_satvars{$refuted_text});
	for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	    my @cl0 = ( - $subformula_satvars{$formula_text}[$nd], - $subformula_satvars{$refuted_text}[$nd] );
	    add_clause \@cl0, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	    my @cl1 = ( $subformula_satvars{$formula_text}[$nd], $subformula_satvars{$refuted_text}[$nd] );
	    foreach my $edge ( @frame_edges ) {
		next unless $edge->[0] == $nd;
		my $tnd = $edge->[1];
		my @cl = ( - $subformula_satvars{$formula_text}[$nd], $subformula_satvars{$formula_text}[$tnd] );
		add_clause \@cl, sprintf("permanence of %s on %s->%s", $formula_text, $node_names[$nd], $node_names[$tnd]);
		push @cl1, - $subformula_satvars{$formula_text}[$tnd];
	    }
	    add_clause \@cl1, sprintf("validity of %s on %s", $formula_text, $node_names[$nd]);
	}
	# Recurse!
	allocate_formula_clauses($formula->[1]);
    }
}

allocate_global_clause;
allocate_formula_clauses($formula);

## We now emit the SAT problem:

printf "p cnf %d %d\n", scalar(@satvars), scalar(@clauses);

for ( my $j=1 ; $j<scalar(@satvars) ; $j++) {
    die "this is impossible" unless $satvars[$j]->[0] == $j;
    printf "c variable %d expresses %s at node %s\n", $j, $satvars[$j]->[1], $node_names[$satvars[$j]->[2]];
}

for ( my $c=0 ; $c<scalar(@clauses) ; $c++ ) {
    printf "c %s\n", $clauses_comments[$c] if defined($clauses_comments[$c]);
    print join(" ", @{$clauses[$c]}), " 0\n";
}
