#! /usr/local/bin/perl -w

# Use a SAT-solver to decide whether an intuitionistic formula holds
# in a given Kripke frame.  (Work in progress.)

# Command line arguments are:
# -k <frame file>: the frame to use
# -K <frame description>: enter frame directly on command line
# -f <formula>: the formula to test
# -v: verbose
# -q: quiet (suppress all output)
# -S <filename>: write the SAT problem to this file (rather than a temp file)

use utf8;
use strict;
use warnings;
use Encode qw(decode_utf8);
use File::Temp;

use Getopt::Std;

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

binmode STDIN, ":utf8";
binmode STDOUT, ":utf8";
binmode STDERR, ":utf8";

@ARGV = map { decode_utf8($_, 1) } @ARGV;
my %opts;
getopts("k:K:f:vqS:", \%opts);

my $verbose = $opts{v};
my $quiet = $opts{q};
my $outsatfilename = $opts{S};

## READING AND PARSING THE FRAME:

my $nbnodes = 0;
my @node_names;
my %node_nums;
my @frame_edges;

my $frame_parser = qr{
   ^<Frame>$
   <rule: Frame>	digraph [a-zA-Z][a-zA-Z0-9\_]* \{ <Edgelist> \} | <Edgelist>
   <rule: Edgelist>	( <[Edge]> \; )+
   <rule: Edge>		<[Nodename]>+ % (?:\-\>)
   <token: Nodename>	[a-zA-Z][a-zA-Z0-9\_]*
}xms;

my $frame_textcontent = $opts{K};
my $frame_filename = $opts{k};

if ( ! defined($frame_filename) && ! defined($frame_textcontent) ) {
    die "expecting -k <frame file> or -K <frame description> option";
}
if ( defined($frame_filename) && defined($frame_textcontent) ) {
    die "-k and -K options are incompatible";
}

my $frame_file;
if ( defined($frame_filename) && $frame_filename eq "-" ) {
    # Open STDIN
    open $frame_file, "<-";
} elsif ( defined($frame_filename) ) {
    open $frame_file, "<", $frame_filename
	or die "failed to open $frame_filename for reading: $!";
}

unless ( defined($frame_textcontent) ) {
    $frame_textcontent = do { local $/ = undef; <$frame_file>; };
}

unless ( $frame_textcontent =~ $frame_parser ) {
    die "frame failed to parse";
}

do {
    # Convert parse tree to frame.
    die "this is impossible"
	unless defined($/{Frame}->{Edgelist}->{Edge}) && ref($/{Frame}->{Edgelist}->{Edge}) eq "ARRAY";
    foreach my $e ( @{$/{Frame}->{Edgelist}->{Edge}} ) {
	die "this is impossible"
	    unless defined($e->{Nodename}) && ref($e->{Nodename}) eq "ARRAY";
	my $pn;
	foreach my $n ( @{$e->{Nodename}} ) {
	    my $nodename = $n;
	    die "this is impossible" unless scalar(@node_names) == $nbnodes;
	    if ( ! defined($node_nums{$nodename}) ) {
		# Allocate a new node:
		push @node_names, $nodename;
		$node_nums{$nodename} = $nbnodes;
		$nbnodes++;
	    }
	    if ( defined($pn) ) {
		# Add an edge:
		die "this is impossible" unless defined($node_nums{$pn});
		push @frame_edges, [ $node_nums{$pn}, $node_nums{$n} ];
	    }
	    $pn = $n;
	}
    }
};

die "frame should have at least one node" unless $nbnodes>=1;

## PARSING THE FORMULA:

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
	    # Allocate a new variable:
	    push @variable_names, $varname;
	    $variable_nums{$varname} = $nbvariables;
	    $nbvariables++;
	    return [ VARIABLE, $variable_nums{$varname} ];
	}
    } else {
	die "this is impossible";
    }
}

my $input_formula = $opts{f};
if ( ! defined($input_formula) ) {
    die "expecting -f <formula> option";
}

unless ( $input_formula =~ $formula_parser ) {
    die "formula failed to parse";
}

my $global_formula = parsetree_to_formula("Expr", \%/);

## CONVERTING A FORMULA TO TEXT:

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

printf STDERR "Input formula parsed as: %s\n", formula_text($global_formula)
    if $verbose;

## CREATING THE SAT PROBLEM:

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

allocate_formula_variables($global_formula);

my $global_formula_text = formula_text($global_formula);
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
allocate_formula_clauses($global_formula);

## RUN THE SAT-SOLVER:

my $outsatfile;

if ( defined($outsatfilename) ) {
    open $outsatfile, ">", $outsatfilename
	or die "failed to open $outsatfilename for writing: $!";
} else {
    $outsatfile = File::Temp->new(SUFFIX=>".cnf")
	or die "failed to create temp file";
    $outsatfilename = $outsatfile->filename;
}

printf STDERR "Writing SAT problem to %s\n", $outsatfilename
    if $verbose;

binmode $outsatfile, ":utf8";
printf $outsatfile "p cnf %d %d\n", scalar(@satvars)-1, scalar(@clauses);

for ( my $j=1 ; $j<scalar(@satvars) ; $j++) {
    die "this is impossible" unless $satvars[$j]->[0] == $j;
    printf $outsatfile "c variable %d expresses %s at node %s\n", $j, $satvars[$j]->[1], $node_names[$satvars[$j]->[2]];
}

for ( my $c=0 ; $c<scalar(@clauses) ; $c++ ) {
    printf $outsatfile "c %s\n", $clauses_comments[$c] if defined($clauses_comments[$c]);
    print $outsatfile join(" ", @{$clauses[$c]}), " 0\n";
}

close $outsatfile;

printf STDERR "Running SAT-solver on %s\n", $outsatfilename
    if $verbose;

open my $satsolver, "-|", "cryptominisat", "--verb", "0", $outsatfilename
    or die "failed to run cryptominisat";

my $answerline = <$satsolver>;

if ( $answerline =~ /^s UNSATISFIABLE/ ) {
    print "formula holds\n" unless $quiet;
    exit 0;
} elsif ( $answerline =~ /^s SATISFIABLE/ ) {
    print "formula fails\n" unless $quiet;
    exit 1 if $quiet;
    my @solution_values;
  SAT_ANSWER_LINE:
    while ( <$satsolver> ) {
	if ( $_ =~ /^v\s+(.*)/ ) {
	    my @lst = split " ", $1;
	    foreach my $k ( @lst ) {
		die "strange output from SAT-solver"
		    unless $k =~ m/\-?[0-9]+/;
		last SAT_ANSWER_LINE if $k==0;
		my $b = $k>=0;
		$k = -$k unless $b;
		die "strange value $k from SAT-solver"
		    if $k>=scalar(@satvars);
		$solution_values[$k] = $b;
	    }
	}
    }
    for ( my $r=0 ; $r<scalar(@variable_satvars) ; $r++ ) {
	if ( defined($variable_satvars[$r]) ) {
	    printf "%s:", $variable_names[$r];
	    for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
		my $k = $variable_satvars[$r][$nd];
		die "missing variable $k value from SAT-solver"
		    unless defined($solution_values[$k]);
		printf " %s%s", ($solution_values[$k]?"":"!"), $node_names[$nd];
	    }
	    print "\n";
	}
    }
    printf "%s:", $global_formula_text;
    for ( my $nd=0 ; $nd<$nbnodes ; $nd++ ) {
	my $k = $subformula_satvars{$global_formula_text}[$nd];
	die "missing variable $k value from SAT-solver"
	    unless defined($solution_values[$k]);
	printf " %s%s", ($solution_values[$k]?"":"!"), $node_names[$nd];
    }
    print "\n";
    exit 1;
} else {
    die "unexpected output from SAT-solver";
}
