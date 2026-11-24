import MaternAudit.PaperTheorem
import MaternAudit.TriangularRows

/-! # Matérn covariance error for row-wise iid locations

In row `n`, the error is the Frobenius norm of the finite real cosine matrix
minus the unit-variance Bessel Matérn matrix, divided by the row size.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace MaternAudit.Manuscript

open MaternParameters MaternProfile PaperTheorem TriangularRows

variable {d : ℕ}

private theorem rowFullRMS_eq_matern (g : Grid) {ν : ℝ} (hν : 0 < ν)
    (n : ℕ) (x : Fin (g.N n) → E d) :
    rowFullRMS g ν n x =
      covarianceRMS ν (g.len n) (g.h n) (g.m n) (maternCov ν (g.len n)) x := by
  unfold rowFullRMS AliasTransfer.sampleRMS
  rw [RealCovariance.frobeniusNorm_error_eq_real]
  simp only [covarianceRMS, finiteGrid_re, kernel_re_eq_maternCov hν (g.len_pos n)]

/-- The expected squared RMS divided by `leadingSq` tends to one, and the
RMS divided by its square root tends to one in row-wise probability.
Each row has the same design density `D` and may use its own probability
space. The norm in `halias` is the maximum norm on coordinates, so the
alias envelope covers the entire closed lag cube `[-1,1]^d`. -/
theorem sharp_matern_rows {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) {P : (n : ℕ) → Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin (g.N n) → Ω n → E d}
    (hx : ∀ n, IIDVariance.SampleLaw (P n) D.μ (X n))
    (η : ℕ → ℝ)
    (halias : ∀ n (z : E d), ‖z‖ ≤ 1 → ‖lagAlias ν (g.len n) (g.h n) z‖ ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / FullCovariance.baseRate d ν g n) atTop (𝓝 0)) :
    let F (n : ℕ) (ω : Ω n) := covarianceRMS ν (g.len n) (g.h n) (g.m n)
      (maternCov ν (g.len n)) (fun i ↦ X n i ω)
    Tendsto (fun n ↦ (∫ ω, F n ω ^ 2 ∂P n) / MovingMatern.leadingSq g ν D n) atTop (𝓝 1) ∧
      ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (P n).real {ω |
        ε ≤ |F n ω / Real.sqrt (MovingMatern.leadingSq g ν D n) - 1|}) atTop (𝓝 0) := by
  dsimp only
  simpa only [rowFullRMS_eq_matern g hν] using
    (movingMatern_full_sharp_rows hd hν g D hx η (fun n ↦ aliasBound_of_lags (halias n)) hsmall)

end MaternAudit.Manuscript

#print axioms MaternAudit.Manuscript.sharp_matern_rows
