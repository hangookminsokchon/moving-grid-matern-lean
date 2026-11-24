import MaternAudit.FourierBound
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FieldSimp

/-! A fixed-torus version of the spectral step behind the leading pair constant.
The analytic input is an explicit small-translation condition on the tail arrays. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace MaternAudit

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- When every fixed spectral shift changes the coefficients by little in relative
ℓ² norm, the normalized population series tends to the squared L² norm of the
design density. The density and the normalized Haar torus are fixed. -/
theorem spectral_density_limit {d : Type*} [Fintype d]
    (ρ : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (c : ℕ → (d → ℤ) → ℝ)
    (hc : ∀ n j, 0 ≤ c n j) (hs : ∀ n, Summable (fun j ↦ c n j ^ 2))
    (he : ∀ n, 0 < ∑' j, c n j ^ 2)
    (hshift : ∀ l, Tendsto (fun n ↦ (∑' j, (c n j - c n (j + l)) ^ 2) /
      (∑' j, c n j ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (∑' l, ‖UnitAddTorus.mFourierCoeff ρ l‖ ^ 2 *
      ∑' j, c n j * c n (j + l)) / (∑' j, c n j ^ 2)) atTop (𝓝 (∫ x, ‖ρ x‖ ^ 2)) := by
  let w (l : d → ℤ) := ‖UnitAddTorus.mFourierCoeff ρ l‖ ^ 2
  let E (n : ℕ) := ∑' j, c n j ^ 2
  let C (n : ℕ) (l : d → ℤ) := ∑' j, c n j * c n (j + l)
  have hp := UnitAddTorus.hasSum_sq_mFourierCoeff ρ
  have hw (l) : 0 ≤ w l := sq_nonneg _
  have hlow (n l) : 0 ≤ C n l / E n :=
    div_nonneg (tsum_nonneg fun j ↦ mul_nonneg (hc n j) (hc n _)) (he n).le
  have hupp (n l) : C n l / E n ≤ 1 := by
    rw [div_le_one (he n)]
    exact spectral_autocorrelation_le (c n) (hc n) (hs n) l
  have hlim (l) : Tendsto (fun n ↦ C n l / E n) atTop (𝓝 1) := by
    have hl := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub ((hshift l).div_const 2)
    simp only [zero_div, sub_zero] at hl
    refine hl.congr (fun n ↦ ?_)
    rw [spectral_autocorrelation_deficit (c n) (hc n) (hs n) l]
    change 1 - 2 * (E n - C n l) / E n / 2 = C n l / E n
    have hz : E n ≠ 0 := ne_of_gt (he n)
    calc
      _ = 1 - (E n / E n - C n l / E n) := by ring
      _ = _ := by rw [div_self hz]; ring
  have htotal : Tendsto (fun n ↦ ∑' l, w l * (C n l / E n)) atTop (𝓝 (∑' l, w l)) := by
    apply tendsto_tsum_of_dominated_convergence hp.summable
    · intro l
      simpa only [mul_one] using (hlim l).const_mul (w l)
    · filter_upwards with n l
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw l) (hlow n l))]
      exact mul_le_of_le_one_right (hw l) (hupp n l)
  rw [← hp.tsum_eq]
  refine htotal.congr fun n ↦ ?_
  change (∑' l, w l * (C n l / E n)) = (∑' l, w l * C n l) / E n
  simp only [div_eq_mul_inv, ← mul_assoc, tsum_mul_right]

end MaternAudit
