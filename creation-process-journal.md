# Documenting the creation process of this repo

## Initializing the repo

I've figured out how to initialize a Lean project that utilizes Mathlib. I
needed access to Lean-QuantumInfo, however, and to guarantee compatibility, I
would better rely on that project's own choices of lean4 and mathlib4 versions.

The creation of a mathlib project involves the `lake` command to get
pre-compiled packages and to build mathlib.

To manage the lean4 and mathlib4 versions the files `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json` are used and must have compatible
requirements.

In order to get rid of the most-to-date versions of lean and mathlib that were
used to create this repo, I had to clean up the builds and those configuration
files, and update them by declaring a requirement in `lake-manifest.json` of the
Lean-QuantumInfo repository.

I have now started this journal and some other documentation about the project.
Next, I should keep updating these and start working on the actual files that I
want to use in the minicourse.
