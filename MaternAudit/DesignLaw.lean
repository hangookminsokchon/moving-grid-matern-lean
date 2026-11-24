import MaternAudit.DesignParseval
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A bounded probability density on the unit cube

All almost-everywhere hypotheses refer to ordinary product Lebesgue measure.
The design law uses the same cube and Fourier character as `DesignParseval`.
-/

noncomputable section

namespace MaternAudit.DesignLaw

open MeasureTheory
open scoped ENNReal NNReal
open MaternAudit.DesignParseval (E unitCube spatialLaw char FT)

/-- A normalized real density supported almost everywhere on the unit cube.
The integral normalization also supplies the default proof of integrability. -/
structure Density (d : ℕ) where
  ρ : E d → ℝ
  L : ℝ≥0
  nonneg : ∀ᵐ x ∂volume, 0 ≤ ρ x
  normalized : (∫ x, ρ x) = 1
  integrable : Integrable ρ volume := integrable_of_integral_eq_one normalized
  support : ∀ᵐ x ∂volume, x ∉ unitCube d → ρ x = 0
  bounded : ∀ᵐ x ∂volume, ρ x ≤ (L : ℝ)

/-- The half-open and closed unit cubes agree almost everywhere for product Lebesgue measure. -/
theorem unitCube_ae_eq_Icc (d : ℕ) : unitCube d =ᵐ[volume] Set.Icc (0 : E d) 1 :=
  Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin d => (volume : Measure ℝ))
    (f := (0 : E d)) (g := (1 : E d))

/-- The union of the upper faces removed from the closed cube has Lebesgue measure zero. -/
theorem volume_Icc_diff_unitCube (d : ℕ) : volume (Set.Icc (0 : E d) 1 \ unitCube d) = 0 :=
  (ae_eq_set.mp (unitCube_ae_eq_Icc d)).2

namespace Density

variable {d : ℕ} (D : Density d)

/-- Construct a cube-supported density using support on the ordinary closed cube. -/
def ofIcc (ρ : E d → ℝ) (L : ℝ≥0) (h₀ : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    (h₁ : (∫ x, ρ x) = 1) (hs : ∀ᵐ x ∂volume, x ∉ Set.Icc (0 : E d) 1 → ρ x = 0)
    (hb : ∀ᵐ x ∂volume, ρ x ≤ (L : ℝ)) : Density d where
  ρ := ρ
  L := L
  nonneg := h₀
  normalized := h₁
  support := by
    filter_upwards [hs, (unitCube_ae_eq_Icc d).mem_iff] with x hx hc
    exact fun h => hx (fun hclosed => h (hc.mpr hclosed))
  bounded := hb

/-- The sampling law with Radon–Nikodym density `D.ρ` against Lebesgue measure. -/
def μ : Measure (E d) := spatialLaw D.ρ

instance probability : IsProbabilityMeasure D.μ where
  measure_univ := by
    rw [μ, spatialLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal D.integrable D.nonneg, D.normalized, ENNReal.ofReal_one]

theorem sq_le : ∀ᵐ x ∂volume, D.ρ x ^ 2 ≤ (D.L : ℝ) * D.ρ x := by
  filter_upwards [D.nonneg, D.bounded] with x h₀ hL
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hL h₀

theorem integrable_sq : Integrable (fun x => D.ρ x ^ 2) volume := by
  refine (D.integrable.const_mul (D.L : ℝ)).mono' (D.integrable.aestronglyMeasurable.pow 2) ?_
  filter_upwards [D.sq_le] with x hx
  rwa [Real.norm_of_nonneg (sq_nonneg _)]

theorem memLp_two : MemLp D.ρ 2 volume :=
  (memLp_two_iff_integrable_sq D.integrable.aestronglyMeasurable).2 D.integrable_sq

/-- The squared density mass appearing in the leading independent-pair term. -/
def designMass : ℝ := ∫ x, D.ρ x ^ 2

theorem designMass_pos : 0 < D.designMass := by
  change 0 < ∫ x, D.ρ x ^ 2
  refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg (D.ρ x)) ?_
  intro h
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (D.ρ x)) D.integrable_sq).1 h.symm
  have hρ : D.ρ =ᵐ[volume] 0 := hz.mono fun x hx => sq_eq_zero_iff.mp hx
  have h10 : (1 : ℝ) = 0 := D.normalized.symm.trans ((integral_congr_ae hρ).trans (by simp))
  exact one_ne_zero h10

theorem designMass_le_L : D.designMass ≤ (D.L : ℝ) := by
  simpa only [designMass, integral_const_mul, D.normalized, mul_one] using
    integral_mono_ae D.integrable_sq (D.integrable.const_mul (D.L : ℝ)) D.sq_le

theorem L_pos : 0 < D.L := D.designMass_pos.trans_le D.designMass_le_L

/-- Fourier transform of the density as the expectation of the negative-exponent
character under its sampling law. -/
theorem integral_char (ξ : E d) : (∫ x, char ξ x ∂D.μ) = FT D.ρ ξ := by
  unfold μ spatialLaw FT
  calc
    _ = ∫ x, (ENNReal.ofReal (D.ρ x)).toReal • char ξ x :=
      integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (D.ρ x))
        (ENNReal.measurable_ofReal.comp_aemeasurable D.integrable.aestronglyMeasurable.aemeasurable)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (char ξ)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [D.nonneg] with x hx
      rw [ENNReal.toReal_ofReal hx, Complex.real_smul, mul_comm]

/-- Domination by `L` times Lebesgue measure restricted to the project's half-open cube. -/
theorem μ_le_restrict : D.μ ≤ D.L • volume.restrict (unitCube d) :=
  DesignParseval.spatialLaw_le_restrict D.bounded D.support

/-- A single draw from the design law belongs to the half-open unit cube almost surely. -/
theorem ae_mem_unitCube : ∀ᵐ x ∂D.μ, x ∈ unitCube d :=
  ae_mono D.μ_le_restrict
    (Measure.ae_smul_measure (ae_restrict_mem DesignParseval.measurableSet_unitCube) D.L)

/-- All locations in a finite iid sample belong to the cube simultaneously almost surely. -/
theorem ae_sample_mem_unitCube (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => D.μ), ∀ i, x i ∈ unitCube d :=
  ae_all_iff.2 fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => D.μ) (i := i)).eventually D.ae_mem_unitCube

end Density
end MaternAudit.DesignLaw
