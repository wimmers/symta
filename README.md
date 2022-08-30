# Simple Symbolic Model Checking of Timed Automata

This repository contains a translation of timed automata specified with
[JANI](https://jani-spec.org/) to SMT formulae.
Based on this translation, it provides rudimentary capabilities for bounded
model checking of timed automata.
The implementation language is [OCaml](https://ocaml.org/),
using the [Z3 SMT solver](https://github.com/Z3Prover/z3) as a backend.

## Installation

1. Install [opam](https://opam.ocaml.org/)
2. Clone this repository
3. Open it: `cd symta`
4. Install dependencies: `opam install --deps-only .`

## Building

This project uses [dune](https://dune.build/) as a build system,
so you can simply run:

```dune build```

## Usage

The command format for the bounded model checker is:

```_build/default/bin/main.exe -bound BOUND MODEL FORMULA_NAME```

Example:

```_build/default/bin/main.exe -bound 5 models/HDDI_02.jani 'Muntax Formula'```

## Install as opam module

To use this project's library in other projects, you can install at as an opam
module:

```opam install .```

If the exported OCaml code changes, you can run `opam upgrade munta`
from anywhere to recompile and update.

## Warning

This implementation has not been tested intensively, and the translation is
not complete, so use with care.
The translation should fail with an error for unsupported features.

## Additional Features

For rapid testing, this repository provides a translation of `.muntax` files
for the [Munta](https://github.com/wimmers/munta) model checker to JANI.
You can use it like this:

```_build/default/bin/muntax_to_jani.exe INPUT.muntax > OUTPUT.jani```

## Additional Testing

Additional testing is configured through dune. Run `dune test`.
