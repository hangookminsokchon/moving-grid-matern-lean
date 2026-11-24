import MaternAudit.SpectralNormalization
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The real-space Matérn covariance

The inverse Fourier integral uses the positive phase over all real frequencies.
We evaluate it by Gaussian integration and complex Fubini. On the positive real axis the modified Bessel function of the
second kind is defined here by Schläfli's integral in DLMF 10.32.10. The change of
variables `t = z² / (4u)` gives the equivalent positive-order moment.
-/

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace MaternAudit.MaternBessel

open MaternParameters
open MaternProfile (E radiusSq radiusSq_nonneg continuous_radiusSq norm_sq_le_radiusSq)

variable {d : ℕ}

/-- Fourier transform of the Cartesian Gaussian in the physical character convention. -/
private theorem gaussian_inverse {a : ℝ} (ha : 0 < a) (x : E d) :
    (∫ ξ : E d, (Real.exp (-(a * radiusSq ξ)) : ℂ) * conj (DesignParseval.char ξ x)) =
      (((Real.pi / a) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 * radiusSq x / a)) : ℝ) : ℂ) := by
  let c (i : Fin d) : ℂ := Complex.I * ((2 * Real.pi * x i : ℝ) : ℂ)
  have hlinear (ξ : E d) : (∑ i, c i * (ξ i : ℂ)) =
      ((2 * Real.pi * ∑ i, ξ i * x i : ℝ) : ℂ) * Complex.I := by
    simp only [c, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hconj (ξ : E d) : conj (DesignParseval.char ξ x) =
      Complex.exp (((2 * Real.pi * ∑ i, ξ i * x i : ℝ) : ℂ) * Complex.I) := by
    rw [DesignParseval.char_eq_exp, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  have hquad : (∑ i, c i ^ 2) = -4 * (Real.pi : ℂ) ^ 2 * (radiusSq x : ℂ) := by
    simp only [c, mul_pow, Complex.I_sq, radiusSq, Complex.ofReal_sum, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  calc
    _ = ∫ ξ : E d, Complex.exp (-(a : ℂ) * (∑ i, (ξ i : ℂ) ^ 2) + ∑ i, c i * (ξ i : ℂ)) := by
      refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
      dsimp only
      rw [hconj, hlinear, Complex.exp_add, Complex.ofReal_exp]
      simp only [radiusSq, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sum,
        Complex.ofReal_pow, neg_mul]
    _ = _ := by
      rw [GaussianFourier.integral_cexp_neg_mul_sum_add (b := (a : ℂ)) ha c, hquad,
        Fintype.card_fin, Complex.ofReal_mul, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le ha.le),
        Complex.ofReal_exp]
      push_cast
      congr 2
      ring

/-- The real Gamma-type moment on the positive half-line. -/
def moment (ν q : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - q / t)

/-- Schläfli's integral for real order and positive argument, in the convention
of [DLMF 10.32.10](https://dlmf.nist.gov/10.32.E10). Its integrand has power `-ν-1`. -/
def besselK (ν z : ℝ) : ℝ := (1 / 2) * (z / 2) ^ ν * moment (-ν) (z ^ 2 / 4)

private theorem integral_reciprocal_scale {q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) :
    (∫ t in Ioi (0 : ℝ), f t) = ∫ u in Ioi (0 : ℝ), q / u ^ 2 * f (q / u) := by
  calc
    _ = ∫ t in Ioi (0 : ℝ), q * f (q * t) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi f 0 hq, mul_zero, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    _ = ∫ u in Ioi (0 : ℝ), (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) •
        (q * f (q * u ^ (-1 : ℝ))) :=
      (integral_comp_rpow_Ioi (fun t ↦ q * f (q * t)) (by norm_num : (-1 : ℝ) ≠ 0)).symm
    _ = _ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
      change 0 < u at hu
      rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num, Real.rpow_neg hu.le, Real.rpow_two,
        Real.rpow_neg_one, abs_neg, abs_one, one_mul, smul_eq_mul]
      simp only [div_eq_mul_inv]
      ring

/-- The substitution `t = q/u` exchanges the two real orders in Schläfli's integral. -/
theorem moment_reflection (ν : ℝ) {q : ℝ} (hq : 0 < q) :
    moment ν q = q ^ ν * moment (-ν) q := by
  rw [moment, integral_reciprocal_scale hq, moment, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  change 0 < u at hu
  change q / u ^ 2 * ((q / u) ^ (ν - 1) * Real.exp (-(q / u) - q / (q / u))) = _
  have hex : -(q / u) - q / (q / u) = -u - q / u := by field_simp; ring
  have hqpow : q ^ ν = q ^ (ν - 1) * q := by
    rw [← Real.rpow_add_one hq.ne', sub_add_cancel]
  have hupow : u ^ (-ν - 1) = (u ^ 2 * u ^ (ν - 1))⁻¹ := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu, ← Real.rpow_neg hu.le]
    congr 1
    push_cast
    ring
  rw [hex, Real.div_rpow hq.le hu.le, hqpow, hupow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Equivalent Schläfli form with integrand `t^(ν-1)`, proved from the reciprocal substitution. -/
theorem besselK_eq_positive_moment (ν : ℝ) {z : ℝ} (hz : 0 < z) :
    besselK ν z = (1 / 2) * (z / 2) ^ (-ν) * moment ν (z ^ 2 / 4) := by
  have h : 0 < z / 2 := by positivity
  rw [moment_reflection ν (by positivity : 0 < z ^ 2 / 4), besselK,
    show z ^ 2 / 4 = (z / 2) ^ 2 by ring, ← Real.rpow_natCast_mul h.le 2 ν,
    show ((2 : ℕ) : ℝ) * ν = ν + ν by push_cast; ring, Real.rpow_add h, Real.rpow_neg h.le]
  field_simp [(Real.rpow_pos_of_pos h ν).ne']
  ring

/-- For positive order the positive-order moment is absolutely convergent even at `q = 0`. -/
theorem integrableOn_moment {ν q : ℝ} (hν : 0 < ν) (hq : 0 ≤ q) :
    IntegrableOn (fun t : ℝ ↦ t ^ (ν - 1) * Real.exp (-t - q / t)) (Ioi 0) := by
  have hm : Measurable (fun t : ℝ ↦ t ^ (ν - 1) * Real.exp (-t - q / t)) :=
    (measurable_id.pow_const _).mul <| Real.continuous_exp.measurable.comp
      (measurable_id.neg.sub (measurable_const.div measurable_id))
  apply (Real.GammaIntegral_convergent hν).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_self _ (div_nonneg hq ht.le)))
    (Real.rpow_nonneg ht.le _)).trans_eq (mul_comm _ _)

private theorem moment_pos {ν q : ℝ} (hν : 0 < ν) (hq : 0 ≤ q) : 0 < moment ν q := by
  have hp (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : 0 < t ^ (ν - 1) * Real.exp (-t - q / t) :=
    mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have hs : Function.support (fun t : ℝ ↦ t ^ (ν - 1) * Real.exp (-t - q / t)) ∩ Ioi 0 = Ioi 0 :=
    inter_eq_right.mpr fun t ht ↦ (hp t ht).ne'
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi).mono fun t ht ↦ (hp t ht).le)
    (integrableOn_moment hν hq)).2
  rw [hs, Real.volume_Ioi]
  exact bot_lt_top

/-- Absolute convergence of the DLMF integral used for the Matérn range of orders and arguments. -/
theorem integrableOn_besselK {ν z : ℝ} (hν : 0 < ν) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-ν - 1) * Real.exp (-t - z ^ 2 / (4 * t))) (Ioi 0) := by
  have hq : 0 < z ^ 2 / 4 := by positivity
  have hm : moment (-ν) (z ^ 2 / 4) ≠ 0 := by
    intro hzero
    have h := moment_reflection ν hq
    rw [hzero, mul_zero] at h
    exact (moment_pos hν hq.le).ne' h
  apply Integrable.of_integral_ne_zero
  simpa only [moment, div_div] using hm

private def mixingWeight (p b : ℝ) (ξ : E d) (t : ℝ) : ℝ :=
  t ^ (p - 1) * Real.exp (-((1 + radiusSq ξ / b) * t))

private theorem gaussian_section (A ν : ℝ) {b t : ℝ} (hb : 0 < b) (ht : 0 < t) (x : E d) :
    (∫ ξ : E d, ((A * mixingWeight (ν + (d : ℝ) / 2) b ξ t : ℝ) : ℂ) *
        conj (DesignParseval.char ξ x)) =
      (((A * (Real.pi * b) ^ ((d : ℝ) / 2)) *
        (t ^ (ν - 1) * Real.exp (-t - (Real.pi ^ 2 * b * radiusSq x) / t)) : ℝ) : ℂ) := by
  let p := ν + (d : ℝ) / 2
  have hfactor (ξ : E d) :
      ((A * mixingWeight p b ξ t : ℝ) : ℂ) * conj (DesignParseval.char ξ x) =
      ((A * t ^ (p - 1) * Real.exp (-t) : ℝ) : ℂ) *
        ((Real.exp (-((t / b) * radiusSq ξ)) : ℂ) * conj (DesignParseval.char ξ x)) := by
    rw [mixingWeight, show -((1 + radiusSq ξ / b) * t) = -t + -((t / b) * radiusSq ξ) by ring,
      Real.exp_add]
    push_cast
    ring
  change (∫ ξ : E d, ((A * mixingWeight p b ξ t : ℝ) : ℂ) * conj (DesignParseval.char ξ x)) = _
  simp_rw [hfactor]
  rw [integral_const_mul, gaussian_inverse (div_pos ht hb), ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hscale : Real.pi / (t / b) = Real.pi * b / t := by field_simp
  have hex : -(Real.pi ^ 2 * radiusSq x / (t / b)) = -(Real.pi ^ 2 * b * radiusSq x / t) := by
    field_simp [ht.ne', hb.ne']
    ring
  have hpow : t ^ (p - 1) / t ^ ((d : ℝ) / 2) = t ^ (ν - 1) := by
    rw [← Real.rpow_sub ht]
    congr 1
    dsimp [p]
    ring
  rw [hscale, Real.div_rpow (mul_nonneg Real.pi_pos.le hb.le) ht.le, hex, ← hpow,
    show Real.exp (-t - Real.pi ^ 2 * b * radiusSq x / t) =
      Real.exp (-t) * Real.exp (-(Real.pi ^ 2 * b * radiusSq x / t)) by rw [sub_eq_add_neg, Real.exp_add]]
  ring

/-- Complex Fubini for the physical character. The norm of its integrand, integrated over
the positive mixing variable, is the already normalized spectral density. -/
private theorem transform_mixture {ν ℓ b A : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (hb : 0 < b)
    (hA : 0 ≤ A) (hW : ∀ ξ : E d, (∫ t in Ioi 0, A * mixingWeight (ν + (d : ℝ) / 2) b ξ t) =
      spectralDensity ν ℓ ξ) (x : E d) :
    PhysicalKernel.kernel ν ℓ x =
      (((A * (Real.pi * b) ^ ((d : ℝ) / 2)) * moment ν (Real.pi ^ 2 * b * radiusSq x) : ℝ) : ℂ) := by
  let p := ν + (d : ℝ) / 2
  let F (ξ : E d) (t : ℝ) := ((A * mixingWeight p b ξ t : ℝ) : ℂ) * conj (DesignParseval.char ξ x)
  have hm : Measurable (Function.uncurry F) := by
    have hw : Measurable (fun y : E d × ℝ ↦ A * mixingWeight p b y.1 y.2) :=
      measurable_const.mul <| (measurable_snd.pow_const (p - 1)).mul <| Real.continuous_exp.measurable.comp
        (((measurable_const.add ((continuous_radiusSq.measurable.comp measurable_fst).div_const b)).mul
          measurable_snd).neg)
    exact (Complex.continuous_ofReal.measurable.comp hw).mul
      ((Complex.continuous_conj.comp (DesignParseval.continuous_char_left x)).measurable.comp measurable_fst)
  have hξ (ξ : E d) : (∫ t in Ioi 0, F ξ t) = (spectralDensity ν ℓ ξ : ℂ) * conj (DesignParseval.char ξ x) := by
    simp only [F, p, integral_mul_const, integral_complex_ofReal, hW]
  have hF : Integrable (Function.uncurry F) ((volume : Measure (E d)).prod (volume.restrict (Ioi 0))) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · refine ae_of_all _ fun ξ ↦ Integrable.of_integral_ne_zero ?_
      change (∫ t in Ioi 0, F ξ t) ≠ 0
      rw [hξ]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (SpectralNormalization.spectralDensity_pos hν hℓ ξ).ne')
        (norm_ne_zero_iff.mp (by rw [Complex.norm_conj, DesignParseval.norm_char]; exact one_ne_zero))
    · apply (SpectralNormalization.integrable_spectralDensity (d := d) hν hℓ).congr
      refine ae_of_all _ fun ξ ↦ ?_
      change spectralDensity ν ℓ ξ = ∫ t in Ioi 0, ‖F ξ t‖
      rw [← hW ξ]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have hw : 0 ≤ A * mixingWeight p b ξ t :=
        mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
      simp only [F, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, Complex.norm_conj,
        DesignParseval.norm_char, mul_one, p]
  calc
    _ = ∫ ξ : E d, ∫ t in Ioi 0, F ξ t := integral_congr_ae (ae_of_all _ fun ξ ↦ (hξ ξ).symm)
    _ = ∫ t in Ioi 0, ∫ ξ : E d, F ξ t := integral_integral_swap hF
    _ = ∫ t in Ioi 0, (((A * (Real.pi * b) ^ ((d : ℝ) / 2)) *
        (t ^ (ν - 1) * Real.exp (-t - (Real.pi ^ 2 * b * radiusSq x) / t)) : ℝ) : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ gaussian_section A ν hb ht x
    _ = _ := by rw [integral_complex_ofReal, integral_const_mul]; rfl

private theorem moment_zero {ν : ℝ} (hν : 0 < ν) : moment ν 0 = Real.Gamma ν := by
  rw [moment, Real.Gamma_eq_integral hν]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by simp [mul_comm]

private theorem kernel_eq_moment {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (x : E d) :
    PhysicalKernel.kernel ν ℓ x =
      (((1 / Real.Gamma ν) * moment ν (ν * radiusSq x / (2 * ℓ ^ 2)) : ℝ) : ℂ) := by
  let b := frequencyScale ν ℓ ^ 2
  have hb : 0 < b := by dsimp [b, frequencyScale]; positivity
  let p := ν + (d : ℝ) / 2
  have hp : 0 < p := add_pos_of_pos_of_nonneg hν (by positivity)
  let A := cInfinity d ν * ℓ ^ (-2 * ν) * b ^ (-p) / Real.Gamma p
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hci := cInfinity_pos (d := d) hν
    positivity
  have hW (ξ : E d) : (∫ t in Ioi 0, A * mixingWeight p b ξ t) = spectralDensity ν ℓ ξ := by
    have hr : 0 < 1 + radiusSq ξ / b := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (radiusSq_nonneg ξ) hb.le)
    have hscale : b * (1 + radiusSq ξ / b) = radiusSq ξ + b := by field_simp; ring
    have he : -beta d ν / 2 = -p := by dsimp [beta, p]; ring
    rw [integral_const_mul]
    change A * (∫ t in Ioi 0, t ^ (p - 1) * Real.exp (-((1 + radiusSq ξ / b) * t))) = _
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hp hr, one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le,
      spectralDensity, he]
    change _ = cInfinity d ν * ℓ ^ (-2 * ν) * (radiusSq ξ + b) ^ (-p)
    rw [← hscale, Real.mul_rpow hb.le hr.le]
    dsimp only [A]
    field_simp [(Real.Gamma_pos_of_pos hp).ne']
    ac_rfl
  have hrep := transform_mixture hν hℓ hb hA hW
  have hconst : A * (Real.pi * b) ^ ((d : ℝ) / 2) = 1 / Real.Gamma ν := by
    apply (eq_div_iff (Real.Gamma_pos_of_pos hν).ne').2
    apply Complex.ofReal_injective
    have h0 : radiusSq (0 : E d) = 0 := by simp [radiusSq]
    simpa only [h0, mul_zero, moment_zero hν, SpectralNormalization.kernel_zero hν hℓ,
      Complex.ofReal_one] using (hrep (0 : E d)).symm
  have hscale : Real.pi ^ 2 * b = ν / (2 * ℓ ^ 2) := by
    dsimp only [b, frequencyScale]
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * ν)]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hrep, hconst, hscale,
    show ν / (2 * ℓ ^ 2) * radiusSq x = ν * radiusSq x / (2 * ℓ ^ 2) by ring]

/-- The inverse Fourier integral of the actual spectrum at every lag, including zero. -/
theorem kernel_eq_gammaIntegral {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (x : E d) :
    PhysicalKernel.kernel ν ℓ x = (((1 / Real.Gamma ν) *
      ∫ t in Ioi (0 : ℝ), t ^ (ν - 1) * Real.exp (-t - ν * radiusSq x / (2 * ℓ ^ 2 * t)) : ℝ) : ℂ) := by
  simpa only [moment, div_div] using kernel_eq_moment hν hℓ x

/-- The dimensionless Matérn argument formed from the Euclidean length of the lag. -/
def scaledRadius (ν ℓ : ℝ) (x : E d) : ℝ := Real.sqrt (2 * ν) * Real.sqrt (radiusSq x) / ℓ

/-- The classical real-space Matérn covariance at nonzero lag, for every positive smoothness.
See [Barnett, Greengard and Rachh, Eq. (19)](https://arxiv.org/pdf/2305.11065#page=6). -/
theorem kernel_eq_besselK {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) {x : E d} (hx : x ≠ 0) :
    PhysicalKernel.kernel ν ℓ x =
      (((2 : ℝ) ^ (1 - ν) * (scaledRadius ν ℓ x) ^ ν * besselK ν (scaledRadius ν ℓ x) /
        Real.Gamma ν : ℝ) : ℂ) := by
  let z := scaledRadius ν ℓ x
  have hr : 0 < radiusSq x := (sq_pos_of_pos (norm_pos_iff.mpr hx)).trans_le (norm_sq_le_radiusSq x)
  have hz : 0 < z := by dsimp [z, scaledRadius]; positivity
  have hzsq : z ^ 2 / 4 = ν * radiusSq x / (2 * ℓ ^ 2) := by
    dsimp only [z, scaledRadius]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * ν), Real.sq_sqrt hr.le]
    ring
  rw [kernel_eq_moment hν hℓ]
  apply congrArg Complex.ofReal
  change _ = (2 : ℝ) ^ (1 - ν) * z ^ ν * besselK ν z / Real.Gamma ν
  rw [besselK_eq_positive_moment ν hz, hzsq, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one, Real.rpow_neg (by positivity : 0 ≤ z / 2),
    Real.div_rpow hz.le (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [(Real.rpow_pos_of_pos hz ν).ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ν).ne']
  ring

end MaternAudit.MaternBessel
