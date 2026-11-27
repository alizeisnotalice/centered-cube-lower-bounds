# Exact √n lower bound for the centered cube weak (1,1) constant

The Lean kernel verified the original manuscript's two lower-bound statements:

1. `CenteredCube.sqrt_manuscript_main`: the liminf of the actual weak constant
   divided by √n, taken along all positive integer dimensions, is at least
   **87 / (220√(58π))**.
2. `CenteredCube.sqrt_manuscript_rational`: for all sufficiently large integer
   dimensions, the actual weak constant is at least √n/35.

The first statement enumerates the positive integer dimensions as `m + 1`;
it does not restrict to a subsequence. The second is a consequence, not a
replacement. Neither asserts that the rational coefficient holds for every
small dimension. `ExactManuscriptAudit.lean` restates both formulas explicitly
and checks them against the top-level declarations.

## Reproduce

Use Lean **4.36.0** and Mathlib commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` with the dependencies pinned by its
Lake manifest. In the pinned Mathlib checkout, run `lake exe cache get` or
build Mathlib, then use the `LEAN_PATH` from `lake env printenv LEAN_PATH` there:

```sh
LEAN_BIN=/path/to/lean \
MATHLIB_LEAN_PATH=/paths/from/the/pinned/mathlib/checkout \
./replay.sh
```

The script uses a new empty folder for project oleans and rebuilds all 402
project modules in dependency order, followed by the separate literal
statement audit. Precompiled project oleans are not included. The archive
contains the complete transitive project-source closure and SHA-256 manifest.
The companion verification log lists the source replay and four final
`#print axioms` results. Each final statement uses only `propext`,
`Classical.choice`, and `Quot.sound`.

## Third-party source

The vendored `ProbabilityApproximation/` modules derive from Polarnova/ProbabilityApproximation v0.9.6 (commit c89fba908a33ba741836407f43c67609e2d05279), ported to Lean 4.36.0. The original source notices are retained; see [the Apache 2.0 license](ProbabilityApproximation/LICENSE).
