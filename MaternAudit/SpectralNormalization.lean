import MaternAudit.PhysicalKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Normalization of the physical Matérn spectrum

Frequencies use product Lebesgue measure in cycles per unit length. A Gamma
integral represents the negative power, and the Gaussian integral factors in
the Cartesian coordinates. This gives the total spectral mass, including all
scale and dimension constants, and evaluates the inverse transform at zero.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace MaternAudit.SpectralNormalization

open MaternParameters
open MaternProfile (E radiusSq radiusSq_nonneg continuous_radiusSq)

variable {d : ℕ}

private theorem gaussian_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : E d, Real.exp (-(radiusSq x * t))) =
      Real.pi ^ ((d : ℝ) / 2) * t ^ (-((d : ℝ) / 2)) := by
  have hprod (x : E d) : Real.exp (-(radiusSq x * t)) =
      ∏ i, Real.exp (-t * x i ^ 2) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    congr 1
    unfold radiusSq
    ring
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_pow (Fin d) (fun u : ℝ ↦ Real.exp (-t * u ^ 2)),
    Fintype.card_fin, integral_gaussian, Real.sqrt_eq_rpow,
    ← Real.rpow_mul_natCast (div_nonneg Real.pi_pos.le ht.le),
    show (1 / 2 : ℝ) * d = (d : ℝ) / 2 by ring,
    Real.div_rpow Real.pi_pos.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]

/-- Integrating the Gamma–Gaussian mixture removes half the dimension from the
shape parameter and leaves exactly the stated powers of π and the scale `b`. -/
private theorem integral_radiusSq_add_rpow {ν b : ℝ} (hν : 0 < ν) (hb : 0 < b) :
    (∫ x : E d, (radiusSq x + b) ^ (-(ν + (d : ℝ) / 2))) =
      Real.pi ^ ((d : ℝ) / 2) * ((1 / b) ^ ν * Real.Gamma ν) / Real.Gamma (ν + (d : ℝ) / 2) := by
  let p := ν + (d : ℝ) / 2
  have hp : 0 < p := add_pos_of_pos_of_nonneg hν (by positivity)
  let F (t : ℝ) (x : E d) := t ^ (p - 1) * Real.exp (-((radiusSq x + b) * t))
  have hx (x : E d) : (∫ t in Ioi 0, F t x) = (radiusSq x + b) ^ (-p) * Real.Gamma p := by
    have hr := add_pos_of_nonneg_of_pos (radiusSq_nonneg x) hb
    simpa only [F, one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi hp hr
  have ht (t : ℝ) (ht : 0 < t) : (∫ x, F t x) =
      Real.pi ^ ((d : ℝ) / 2) * (t ^ (ν - 1) * Real.exp (-(b * t))) := by
    have hfactor (x : E d) : F t x =
        (t ^ (p - 1) * Real.exp (-(b * t))) * Real.exp (-(radiusSq x * t)) := by
      dsimp only [F]
      rw [show -((radiusSq x + b) * t) = -(b * t) + -(radiusSq x * t) by ring, Real.exp_add]
      ring
    simp_rw [hfactor]
    rw [integral_const_mul, gaussian_integral ht]
    have hpow : t ^ (p - 1) * t ^ (-((d : ℝ) / 2)) = t ^ (ν - 1) := by
      rw [← Real.rpow_add ht]
      congr 1
      dsimp [p]
      ring
    rw [← hpow]
    ring
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi hν hb
  have hg : IntegrableOn (fun t : ℝ ↦ t ^ (ν - 1) * Real.exp (-(b * t))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hgamma]
    positivity
  have hm : Measurable (Function.uncurry F) :=
    (measurable_fst.pow_const (p - 1)).mul <| Real.continuous_exp.measurable.comp
      ((((continuous_radiusSq.measurable.comp measurable_snd).add measurable_const).mul measurable_fst).neg)
  have hF : Integrable (Function.uncurry F) ((volume.restrict (Ioi 0)).prod volume) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht0
      change 0 < t at ht0
      apply Integrable.of_integral_ne_zero
      change (∫ x, F t x) ≠ 0
      rw [ht t ht0]
      positivity
    · apply (hg.const_mul (Real.pi ^ ((d : ℝ) / 2))).congr
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht0
      change 0 < t at ht0
      have hn (x : E d) : ‖F t x‖ = F t x := Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)
      change _ = ∫ x, ‖F t x‖
      simp only [hn, ht t ht0]
  apply (eq_div_iff (Real.Gamma_pos_of_pos hp).ne').2
  calc
    _ = ∫ x : E d, (radiusSq x + b) ^ (-p) * Real.Gamma p := (integral_mul_const _ _).symm
    _ = ∫ x : E d, ∫ t in Ioi 0, F t x := by simp only [hx]
    _ = ∫ t in Ioi 0, ∫ x : E d, F t x := (integral_integral_swap (f := F) hF).symm
    _ = ∫ t in Ioi 0, Real.pi ^ ((d : ℝ) / 2) * (t ^ (ν - 1) * Real.exp (-(b * t))) :=
      setIntegral_congr_fun measurableSet_Ioi ht
    _ = _ := by rw [integral_const_mul, hgamma]

private theorem frequencyScale_pos {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) :
    0 < frequencyScale ν ℓ := by unfold frequencyScale; positivity

private theorem prefactor {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) :
    cInfinity d ν * ℓ ^ (-2 * ν) = (frequencyScale ν ℓ ^ 2) ^ ν * Real.Gamma (ν + (d : ℝ) / 2) /
      (Real.pi ^ ((d : ℝ) / 2) * Real.Gamma ν) := by
  have hscale : frequencyScale ν ℓ ^ 2 = (ν / 2) / (Real.pi ^ 2 * ℓ ^ 2) := by
    rw [frequencyScale, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * ν)]
    field_simp
    ring
  rw [hscale, Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (sq_nonneg Real.pi) (sq_nonneg ℓ),
    ← Real.rpow_natCast_mul Real.pi_pos.le 2 ν, ← Real.rpow_natCast_mul hℓ.le 2 ν,
    cInfinity, Real.rpow_add Real.pi_pos, show -2 * ν = -(2 * ν) by ring, Real.rpow_neg hℓ.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- The physical density is strictly positive at every frequency. -/
theorem spectralDensity_pos {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (ξ : E d) :
    0 < spectralDensity ν ℓ ξ := by
  exact mul_pos (mul_pos (cInfinity_pos hν) (Real.rpow_pos_of_pos hℓ _))
    (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (radiusSq_nonneg ξ)
      (sq_pos_of_pos (frequencyScale_pos hν hℓ))) _)

/-- The cycles-per-unit-length Matérn spectral density has total Lebesgue mass one. -/
theorem integral_spectralDensity {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) :
    (∫ ξ : E d, spectralDensity ν ℓ ξ) = 1 := by
  have hb := sq_pos_of_pos (frequencyScale_pos hν hℓ)
  have hp : 0 < ν + (d : ℝ) / 2 := add_pos_of_pos_of_nonneg hν (by positivity)
  have he : -beta d ν / 2 = -(ν + (d : ℝ) / 2) := by unfold beta; ring
  simp only [spectralDensity, he, integral_const_mul]
  rw [integral_radiusSq_add_rpow hν hb, prefactor hν hℓ, one_div, Real.inv_rpow hb.le]
  field_simp [(Real.Gamma_pos_of_pos hν).ne', (Real.Gamma_pos_of_pos hp).ne',
    (Real.rpow_pos_of_pos Real.pi_pos ((d : ℝ) / 2)).ne', (Real.rpow_pos_of_pos hb ν).ne']

theorem integrable_spectralDensity {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) :
    Integrable (spectralDensity (d := d) ν ℓ) :=
  integrable_of_integral_eq_one (integral_spectralDensity hν hℓ)

/-- Absolute Bochner integrability of the defining inverse Fourier integral at every lag. -/
theorem integrable_inverseFourier {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (z : E d) :
    Integrable fun ξ ↦ (spectralDensity ν ℓ ξ : ℂ) * conj (DesignParseval.char ξ z) := by
  have hi := integrable_spectralDensity (d := d) hν hℓ
  apply hi.mono' (hi.ofReal.aestronglyMeasurable.mul
    (Complex.continuous_conj.comp (DesignParseval.continuous_char_left z)).aestronglyMeasurable)
  exact ae_of_all _ fun ξ ↦ by
    change ‖(spectralDensity ν ℓ ξ : ℂ) * conj (DesignParseval.char ξ z)‖ ≤ spectralDensity ν ℓ ξ
    simp only [norm_mul, Complex.norm_conj, DesignParseval.norm_char, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (spectralDensity_pos hν hℓ ξ).le, le_refl]

/-- Unit variance for the physical kernel itself. -/
theorem kernel_zero {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) :
    PhysicalKernel.kernel (d := d) ν ℓ 0 = 1 := by
  have hchar (ξ : E d) : DesignParseval.char ξ 0 = 1 := by simp [DesignParseval.char_eq_exp]
  simp only [PhysicalKernel.kernel, hchar, map_one, mul_one, integral_complex_ofReal,
    integral_spectralDensity hν hℓ, Complex.ofReal_one]

end MaternAudit.SpectralNormalization
