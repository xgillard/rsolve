# Rsolve 

[![license-badge][]][license] 
[![travis-badge][]][travis-ci] [![appveyor-badge][]][appveyor-ci]
[![codecov-badge][]][codecov]

`rsolve` is a SAT solver written in Rust. Its purpose is to implement state of the
art SAT solving techniques while keeping a codebase which is clean, robust, 
thoroughly documented and tested. Once compiled, the resulting binary **should**
be competitive with the best SAT solvers out there.

## Usage
```
c ******************************************************************************
c This is the `rsolve` SAT solver version 0.1.0
c ------------------------------------------------------------------------------
c Copyright 2017 Xavier Gillard, LVL -- Université Catholique de Louvain (BE)
c This software is licensed to you under the terms of the MIT license
c ==============================================================================
Usage:
    ./target/debug/rsolve [OPTIONS] [INPUT_FILE]

rsolve, a simple yet performant propositional SAT solver

positional arguments:
  input_file            The input file. This should be a dimacs cnf file which
                        may be compressed with bz2 (bzip2) , gz (gzip) or xz
                        (lzma)

optional arguments:
  -h,--help             show this help message and exit
  -p,--print-model      Prints a model when the instance is proven satisfiable.
  -d,--drat             Prints a proof of unsatisfiability in DRAT format (aka
                        UNSAT certificate).
```

## Installation
`rsolve` was not yet released on crates.io. Hence you **have to** compile the 
solver for yourself if you intend to use it.

## Build
`rsolve` is built with `cargo` like any other Rust project. If you haven't 
yet installed the rust toolchain (which comprises cargo), check the installation
instructions on the rust-lang project page: 
   https://www.rust-lang.org/en-US/install.html 

Once you are sure to have a stable Rust toolchain properly installed, issue the
following command: 

```
cargo build --release
```

The resulting binary program will be located in _rsolve/target/release/rsolve_.

## Legal
Rsolve is distributed to you under the terms of the _MIT_  license (see 
https://opensource.org/licenses/MIT for the full details). 

## Credits 
Rsolve is developed by Xavier Gillard, PhD student at Université Catholique de
Louvain and member of the Louvain Verification Lab (http://lvl.info.ucl.ac.be). 

[license-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[license]: https://opensource.org/licenses/MIT
[travis-badge]: https://travis-ci.org/xgillard/rsolve.svg?branch=master
[travis-ci]: https://travis-ci.org/xgillard/rsolve
[appveyor-badge]: https://ci.appveyor.com/api/projects/status/quie3y6aoumtf88b?svg=true
[appveyor-ci]: https://ci.appveyor.com/project/xgillard/rsolve
[codecov-badge]: https://codecov.io/gh/xgillard/rsolve/branch/master/graph/badge.svg
[codecov]: https://codecov.io/gh/xgillard/rsolve
