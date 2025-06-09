# Motto

My fork for [mit-pdos/perennial](https://github.com/mit-pdos/perennial/commit/8548a371b20bbb764a51db4ee97cfc1bb3ab0e5c)

## Quick Start

```
$ git submodule update --init --recursive
$ eval `opam env`
$ make -j4 -k
```
## COQC

```
The Coq Proof Assistant, version 8.20.0
compiled with OCaml 5.2.1
```

## Notable Changes

### 2025-06-09

- added the file `Motto.md` in the directory `.` : It explains our repository.
- added the files `server.go` and `client.go` in the directory `external/Goose/session/goFiles/` : the Go files to be verified.
- added the files `server.v` and `client.v` in the directory `external/Goose/session/` : which are the translations of the Go files.
- added the files `session_definitions.v` and `session_prelude.v` in the directory `src/program_proof/session/` : They include the basic definitions, which will be used to verify the Go files.
- modified `src/ShouldBuild.v` : Now, it requires only `src/LiteBuild.v` and all `src/program_proof/session/*.v`.
- modified `Makefile` : to fix an error raised when running `make`.
