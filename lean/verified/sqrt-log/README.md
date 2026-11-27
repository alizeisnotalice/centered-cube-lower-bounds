# Centered-cube lower bound of order sqrt(n)/log(n)

The exact top-level theorem is `CenteredCube.RudinDensity.sqrtLogLowerBound_paper`.
`geometry/FinalAudit.lean` re-states the full conclusion with no problem-specific
assumptions, and prints its transitive axiomatic dependencies.

Lean is pinned to 4.36.0, Mathlib to commit
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`; the base source is snapshot
`dba55aea565020771595493c27ec33f20d4f624e`. Before `./verify-clean.sh`, put the
pinned Lean distribution (the directory containing bin/lean and bin/lake) at
`toolchain/lean-4.36.0-linux` or symlink it there, then from
`centered-cube/lean` run `lake exe cache get` with that bin directory on PATH.
The package contains no precompiled Lean objects or third-party binary caches.

The accompanying verification uses a slightly more conservative explicit
dimension threshold in the Berry–Esseen moderate-deviation lemma and a stronger
Hoeffding estimate in the good-event step. The theorem still concerns the
original centered cube weak constant, for every sufficiently large integer
dimension. The subsequent sqrt(n) lower bound is a different theorem and is
not claimed in this package.

The separately namespaced ProbabilityApproximation source portions used by
the Berry–Esseen proof retain the upstream Apache-2.0 license in
`sqrt-log-track/BE-port/LICENSE`. They were ported from Polarnova/ProbabilityApproximation
v0.9.6 (c89fba908a33ba741836407f43c67609e2d05279) to the pinned Lean/Mathlib toolchain.
