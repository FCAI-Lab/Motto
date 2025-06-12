# Motto

Our fork of [mit-pdos/perennial](https://github.com/mit-pdos/perennial/commit/8548a371b20bbb764a51db4ee97cfc1bb3ab0e5c)

## Quick Start

```shell
git submodule update --init --recursive
eval `opam env`
make -j4 -k
```

## `coqc -v`

```
The Coq Proof Assistant, version 8.20.0
compiled with OCaml 5.2.1
```

## Progress

- [x] `session_prelude.v` (1336 lines)
- [x] `session_definitions.v` (1134 lines)
- [x] `versionVector.v` (751 lines)
- [x] `gossip.v` (841 lines)
- [x] `processRequest.v` (1069 lines)
- [ ] `u64ToNat.v`

## Notable Changes

### 2025-06-09

- Added the file `Motto.md` in the directory `.`. It explains our repository.
- Added the files `server.go` and `client.go` in the directory `external/Goose/session/goFiles/`, which are the Go files to be verified.
- Added the files `server.v` and `client.v` in the directory `external/Goose/session/`, which are the translations of the Go files.
- Added the files `session_definitions.v` and `session_prelude.v` in the directory `src/program_proof/session/`. They include the basic definitions and lemmas, which will be used to verify the Go files, and export `std_proof` and `grove_prelude`.
- Modified `src/ShouldBuild.v`. Now, it requires only `src/LiteBuild.v` and all `src/program_proof/session/*.v`.
- Modified `Makefile`, to fix an error raised when running `make`.

### 2025-06-10

- Removed the Go function `equalOperations()` from `server.go`.
- Added the nat-version Coq counterpart functions `session_definitions`.
- Added the file `versionVector.v` in the directory `src/program_proof/session/`. It includes the wp_lemmas relavant to `VersionVector`.

### 2025-06-10

- Added the file `gossip.v`, `processRequest`, and `u64ToNat` in the directory `src/program_proof/session/`.
- Completed `session_prelude.v`, `session_definitions.v`, and `versionVector.v`.

### 2025-06-12

- Porting done. It remains to show `Coq_nat -> Coq_u64`.
