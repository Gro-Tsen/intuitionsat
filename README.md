# intuitionsat.pl

**Use a SAT solver to decide whether an intuitionistic propositional formula holds in a given Kripke frame.**

**Author:** [David A. Madore](http://www.madore.org/~david/)  
**License:** [CC0 1.0 Universal](./LICENSE)

---

## Overview

`intuitionsat.pl` is a single-file Perl program that determines
whether a given intuitionistic propositional logic formula is valid in
a specified Kripke frame.  It does this by converting the problem into
a SAT instance and running a SAT solver (currently, CryptoMiniSat) to
check satisfiability.

---

## Requirements

- **Perl**

- The `Regexp::Grammars` Perl module  
  (Packaged as `libregexp-grammars-perl` on Debian/Ubuntu)  
  *Used to parse formula syntax*

- **CryptoMiniSat**  
  (Packaged as `cryptominisat` on Debian/Ubuntu)  
  *The SAT solver used to solve the generated SAT problem*  
  (But another SAT solver can be used instead through the `-e` option.)

---

## Usage

This program is just a single Perl script: simply run it as follows:

```
./intuitionsat.pl [options]
```

You may need to adjust the shebang line (`#!/usr/local/bin/perl -w`)
at the top of the script to match the location of Perl on your system.
You may also need to make sure that it is executable (`chmod +x
intuitionsat.pl`).

Alternatively:

```
perl intuitionsat.pl [options]
```

---

## Terminal & Encoding Notes

- This program assumes a **Unicode-capable terminal**.
- **Formula input and output is UTF-8** encoded.
- Formulas can be input using ASCII characters but are displayed using Unicode.

---

## Command-Line Options

| Option           | Description |
|------------------|-------------|
| `-k <file>`      | Load Kripke frame from a file |
| `-K <string>`    | Provide Kripke frame directly as a string |
| `-f <formula>`   | The formula to check |
| `-v`             | Verbose output |
| `-q`             | Quiet mode (suppress all output) |
| `-S <filename>`  | Save SAT problem to this file (instead of a temporary file) |
| `-e <command line>`  | Call this SAT solver (instead of `cryptominisat --verb 0`) |

These options also have long equivalents: `--framefile`, `--frame`,
`--formula`, `--verbose`, `--quiet`, `--satfile` and `--satcmd`
respectively.  The `--help` option (or `-h`) displays a summary of
known options.

The SAT solver command line can also be passed as the `SATCMD`
environment variable (it is run through `sh -c` so be aware that it
can interpret arbitrary shell commands).  Any SAT solver program
supporting the DIMACS format should be fine, but I didn't check.

---

## Return Values

- `0` (success): The formula **holds** in the given frame
- `1`: The formula **fails**
- Any other value: An **error** occurred

---

## Example use

```
./intuitionsat.pl -K 'u->v;' -f 'p\/~p'
```

This should return:

```
formula fails
p: !u v
p∨¬p: !u v
```

This indicates a counterexample: variable `p` holds at node `v` but
not at node `u`.

---

## Frame syntax

Frame descriptions use a **simplified Graphviz dot syntax**. For example:

```
u->v0->w0; u->v1->w1;
```

This defines five nodes (`u`, `v0`, `w0`, `v1`, `w1`) with a relation
taken as the **transitive closure** of the directed edges provided.

Loops and bidirectional edges are allowed but not useful (and might
slow down the SAT solving).

The description can be wrapped in a Graphviz `digraph` block, for
example:

```
digraph test {
  u->v0->w0; u->v1->w1;
}
```

A frame consisting of a **single node** can be created by the syntax
`u;` (no arrow).  This is useful for testing the validity of a
**classical** propositional formula.

---

## Formula syntax

Formulas follow **standard intuitionistic propositional logic** with
Unicode symbols for display.  Input can use either **Unicode** or
**ASCII** versions of logical operators.

### Accepted symbols

| Logical Operator | Unicode Symbol | ASCII Alternatives |
|------------------|----------------|--------------------|
| Conjunction      | `∧` (U+2227)     | `/\` or `&`        |
| Disjunction      | `∨` (U+2228)     | `\/` or `\|`       |
| Implication      | `⇒` (U+21D2) or `→` (U+2192)  | `=>` or `->`       |
| Negation         | `¬` (U+00AC)     | `~`                |
| Truth            | `⊤` (U+22A4)     | `1` or `_True`     |
| Falsehood        | `⊥` (U+22A5)     | `0` or `_False`    |

**Operator precedence** is: negation (highest priority) > conjunction >
disjunction > implication.  For example, `p∨q∧r` is interpreted as
`p∨(q∧r)`, and `p∨q⇒r` is interpreted as `(p∨q)⇒r`.  The implication
operator associates rightwards, that is, `p⇒q⇒r` is read as `p⇒(q⇒r)`.
