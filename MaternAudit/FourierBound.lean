import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linarith

/-! Two independent bounds on the fixed-grid population error. The first treats the
regrouped lattice expression in BGR (42). The second works directly with two points
on a group with invariant measure. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace MaternAudit

/-- The shortfall of a translated autocorrelation is half the squared translation
difference. This also identifies the remainder in the population upper bound. -/
theorem spectral_autocorrelation_deficit {G : Type*} [AddGroup G] (c : G → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hs : Summable (fun j ↦ c j ^ 2)) (l : G) :
    (∑' j, (c j - c (j + l)) ^ 2) =
      2 * ((∑' j, c j ^ 2) - ∑' j, c j * c (j + l)) := by
  let e : G ≃ G := Equiv.addRight l
  have ht : HasSum (fun j ↦ c (j + l) ^ 2) (∑' j, c j ^ 2) :=
    (e.hasSum_iff (f := fun j : G ↦ c j ^ 2)).mpr hs.hasSum
  have hm := (hs.hasSum.add ht).div_const (2 : ℝ)
  have hb (j : G) : c j * c (j + l) ≤ (c j ^ 2 + c (j + l) ^ 2) / 2 := by
    nlinarith [sq_nonneg (c j - c (j + l))]
  have hprod : Summable (fun j ↦ c j * c (j + l)) :=
    .of_nonneg_of_le (fun j ↦ mul_nonneg (hc j) (hc _)) hb hm.summable
  have hr := (hs.hasSum.add ht).sub (hprod.hasSum.mul_left 2)
  have hh := hr.congr_fun (g := fun j ↦ (c j - c (j + l)) ^ 2) (fun j ↦ by dsimp; ring)
  rw [hh.tsum_eq]
  ring

/-- Translating a nonnegative square-summable sequence does not increase its
cross-correlation beyond its energy. The lattice can be `Fin d → ℤ`. -/
theorem spectral_autocorrelation_le {G : Type*} [AddGroup G] (c : G → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hs : Summable (fun j ↦ c j ^ 2)) (l : G) :
    (∑' j, c j * c (j + l)) ≤ ∑' j, c j ^ 2 := by
  have h := tsum_nonneg (fun j ↦ sq_nonneg (c j - c (j + l)))
  rw [spectral_autocorrelation_deficit c hc hs l] at h
  linarith

/-- An ℓ¹ weight on spectral lags costs exactly its total mass in the bound. -/
theorem weighted_spectral_bound {G : Type*} [AddGroup G] (c w : G → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hs : Summable (fun j ↦ c j ^ 2))
    (hw : ∀ l, 0 ≤ w l) (hwSum : Summable w) :
    (∑' l, w l * ∑' j, c j * c (j + l)) ≤ (∑' l, w l) * ∑' j, c j ^ 2 := by
  have hb (l : G) := mul_le_mul_of_nonneg_left (spectral_autocorrelation_le c hc hs l) (hw l)
  have hm := hwSum.mul_right (∑' j, c j ^ 2)
  have he : Summable (fun l ↦ w l * ∑' j, c j * c (j + l)) :=
    .of_nonneg_of_le (fun l ↦ mul_nonneg (hw l) (tsum_nonneg fun j ↦ mul_nonneg (hc j) (hc _))) hb hm
  exact (he.tsum_le_tsum hb hm).trans_eq (hwSum.tsum_mul_right _)

section Torus
attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- With normalized Haar measure, Parseval evaluates the entire design weight.
This is the inequality for the regrouped population series in equation (42). -/
theorem eq42_torus_bound {d : Type*} [Fintype d]
    (ρ : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (c : (d → ℤ) → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable (fun j ↦ c j ^ 2)) :
    (∑' l, ‖UnitAddTorus.mFourierCoeff ρ l‖ ^ 2 * ∑' j, c j * c (j + l)) ≤
      (∫ x, ‖ρ x‖ ^ 2) * ∑' j, c j ^ 2 := by
  have hp := UnitAddTorus.hasSum_sq_mFourierCoeff ρ
  simpa only [hp.tsum_eq] using
    weighted_spectral_bound c (fun l ↦ ‖UnitAddTorus.mFourierCoeff ρ l‖ ^ 2)
      hc hs (fun l ↦ sq_nonneg _) hp.summable
end Torus

/-- If a density is bounded by L on a group with Haar measure, an independent
pair integrates any nonnegative lag energy against at most L times Haar measure.
This gives the fixed-grid physical-space proof with g = |T|². -/
theorem pair_energy_le {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (μ : Measure G) [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (ρ g : G → ℝ) (L : ℝ) (hρ : Integrable ρ μ) (hprob : ∫ x, ρ x ∂μ = 1)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ L) (hg : Integrable g μ) (hp : ∀ x, 0 ≤ g x) :
    (∫ x, ρ x * (∫ y, ρ y * g (x - y) ∂μ) ∂μ) ≤ L * ∫ z, g z ∂μ := by
  have innerBound (x : G) : (∫ y, ρ y * g (x - y) ∂μ) ≤ L * ∫ z, g z ∂μ := by
    calc
      _ ≤ ∫ y, L * g (x - y) ∂μ := integral_mono_of_nonneg
        (ae_of_all _ fun y ↦ mul_nonneg (hn y) (hp _)) ((hg.comp_sub_left x).const_mul L)
        (ae_of_all _ fun y ↦ mul_le_mul_of_nonneg_right (hb y) (hp _))
      _ = _ := by rw [integral_const_mul, integral_sub_left_eq_self g μ x]
  calc
    _ ≤ ∫ x, ρ x * (L * ∫ z, g z ∂μ) ∂μ := integral_mono_of_nonneg
      (ae_of_all _ fun x ↦ mul_nonneg (hn x) (integral_nonneg fun y ↦ mul_nonneg (hn y) (hp _)))
      (hρ.mul_const _) (ae_of_all _ fun x ↦ mul_le_mul_of_nonneg_left (innerBound x) (hn x))
    _ = _ := by rw [integral_mul_const, hprob, one_mul]

section HaarTorus
attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- For an actual L² tail on the multidimensional unit torus, the independent-pair
RMS squared is at most the density bound times the sum of squared Fourier coefficients. -/
theorem iid_torus_pair_le_spectral_energy {d : Type*} [Fintype d]
    (T : Lp ℂ 2 (volume : Measure (UnitAddTorus d)))
    (ρ : UnitAddTorus d → ℝ) (L : ℝ) (hρ : Integrable ρ) (hprob : ∫ x, ρ x = 1)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ L) :
    (∫ x, ρ x * (∫ y, ρ y * ‖T (x - y)‖ ^ 2)) ≤ L * ∑' j, ‖UnitAddTorus.mFourierCoeff T j‖ ^ 2 := by
  letI : (volume : Measure UnitAddCircle).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  letI : (volume : Measure (UnitAddTorus d)).IsNegInvariant :=
    Measure.pi.isNegInvariant (fun _ : d ↦ (volume : Measure UnitAddCircle))
  rw [(UnitAddTorus.hasSum_sq_mFourierCoeff T).tsum_eq]
  exact pair_energy_le volume ρ (fun z ↦ ‖T z‖ ^ 2) L hρ hprob hn hb
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable T)).mp (Lp.memLp T))
    (fun z ↦ sq_nonneg _)
end HaarTorus

end MaternAudit
