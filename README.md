# Sharp Frobenius error for Matérn covariance approximation on moving Fourier grids

Yoolkyu Park

The Lean theorem `MaternAudit.Manuscript.sharp_matern_rows` proves both full-error limits in Theorem 1.1. Write $F_n = \|\widetilde K_n-K_n\|_F/N_n$, where $\widetilde K_n$ is the finite real cosine matrix and $K_n$ is the unit-variance Matérn covariance matrix in Bessel form. [Theorem source](MaternAudit/ManuscriptTheorem.lean)

Fix $d\geq 1$ and $\nu>0$. Within each row, the $N_n$ locations are iid from a fixed bounded density on $[0,1]^d$. Each row may use its own probability space. The deterministic grid has spacing $0<h_n\leq 1$, cutoff $R_n=h_nm_n$, and length scale $\ell_n>0$, with $N_n$, $R_n$, and $\ell_nR_n$ tending to infinity. Assume that the infinite-grid alias on $[-1,1]^d$ is bounded uniformly by $\eta_n=o\big((\ell_nR_n)^{-2\nu}\sqrt{N_n^{-1}+R_n^{-d}}\big)$. Then

$$
\frac{\mathbb{E}[F_n^2]}{L_n^2}\longrightarrow 1,
\qquad
\frac{F_n}{L_n}\xrightarrow{\mathbb{P}}1.
$$

The deterministic $L_n^2$, defined by `MovingMatern.leadingSq`, includes the diagonal contribution and the independent-pair contribution. For the omitted Fourier tail, `TriangularRows.movingMatern_sharp_rows` proves the same limits under the grid and sampling assumptions alone. The Section 4 grid-selection rules and the numerical simulations are outside the scope of this formalization. [Leading term](MaternAudit/MovingMatern.lean) · [Row-wise tail theorem](MaternAudit/TriangularRows.lean)

## Build

With `elan` and Git installed, run the following from the repository root. The toolchain is Lean 4.19.0. The manifest pins mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` and records the exact revisions of its eight dependencies.

```sh
lake build Cache.Main
awk '$1 == "import" && $2 ~ /^Mathlib[.]/ {print $2}' MaternAudit/*.lean |
  LC_ALL=C sort -u |
  xargs lake env lean --run .lake/packages/mathlib/Cache/Main.lean get
lake build
```

The first command prepares mathlib’s cache tool. The pipeline requests compiled files for the directly imported mathlib modules and their dependencies. The final `lake build` compiles the default `MaternAudit` library, including the manuscript theorem, with `--trust=0 -DwarningAsError=true`.

## Check the proofs and axioms

```sh
lake env lean --trust=0 -DwarningAsError=true MaternAudit/ManuscriptTheorem.lean
lake env lean --trust=0 -DwarningAsError=true CheckAxioms.lean
```

The first command checks the manuscript proof directly. The second prints the axiom dependencies of selected results and checks every theorem declaration in the project modules, including private lemmas. It exits with an error if any project theorem uses an axiom outside the three below or if the manuscript theorem’s axiom set differs from the displayed set. [Axiom checker](CheckAxioms.lean)

The manuscript proof printed this line under Lean 4.19.0.

```text
'MaternAudit.Manuscript.sharp_matern_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
```
