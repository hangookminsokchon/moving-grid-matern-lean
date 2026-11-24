import MaternAudit.DesignLaw
import MaternAudit.IIDVariance

/-!
# Independent-pair Fourier energy on a physical grid

The Gram feature at integer frequency `j` is the positive character evaluated at
`H x` modulo one. Pairing frequencies `j` and `j + l` leaves the negative
character at lag `l`. The coefficients may be signed and absolutely summable.
-/

noncomputable section

open MeasureTheory UnitAddTorus
open scoped ComplexConjugate NNReal

namespace MaternAudit.PairSpectrum

open DesignParseval

variable {d : ℕ}

/-- Positive Fourier character at physical frequency `H j`. -/
def physicalFeature (H : ℝ) (j : Fin d → ℤ) (x : Fin d → ℝ) : ℂ :=
  mFourier j (torusPoint H x)

/-- Squared modulus of the physical Fourier Gram entry. -/
def physicalLoss (H : ℝ) (c : (Fin d → ℤ) → ℝ) (x y : E d) : ℝ :=
  ‖FixedGridLaw.gramKernel c (physicalFeature H) x y‖ ^ 2

theorem continuous_torusPoint (H : ℝ) : Continuous (torusPoint (d := d) H) :=
  continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_const.mul (continuous_apply i))

theorem continuous_physicalFeature (H : ℝ) (j : Fin d → ℤ) : Continuous (physicalFeature H j) :=
  (mFourier j).continuous.comp (continuous_torusPoint H)

theorem norm_physicalFeature (H : ℝ) (j : Fin d → ℤ) (x : Fin d → ℝ) :
    ‖physicalFeature H j x‖ = 1 := by
  simp only [physicalFeature, mFourier, ContinuousMap.coe_mk, fourier_apply, norm_prod,
    Circle.norm_coe, Finset.prod_const_one]

private theorem torusPoint_sub (H : ℝ) (x y : E d) :
    torusPoint H (x - y) = torusPoint H x - torusPoint H y := by
  funext i
  change ((H * (x i - y i) : ℝ) : UnitAddCircle) = _
  rw [mul_sub]
  rfl

private theorem physicalFeature_mul_conj (H : ℝ) (j : Fin d → ℤ) (x y : E d) :
    physicalFeature H j x * conj (physicalFeature H j y) = physicalFeature H j (x - y) := by
  simp only [physicalFeature, torusPoint_sub, FixedFourier.mFourier_apply_sub]

/-- The sign and angular normalization of the physical feature. -/
theorem physicalFeature_eq_exp (H : ℝ) (j : Fin d → ℤ) (x : E d) :
    physicalFeature H j x =
      Complex.exp ((2 * Real.pi * (∑ i, H * (j i : ℝ) * x i) : ℝ) * Complex.I) := by
  simpa only [physicalFeature, neg_neg, char_eq_exp, sampleFreq, Pi.zero_apply, add_zero,
    Pi.neg_apply, Int.cast_neg, mul_neg, neg_mul, Finset.sum_neg_distrib] using
      mFourier_neg_torusPoint H (-j) x

private theorem norm_gramTerm (H : ℝ) (c : (Fin d → ℤ) → ℝ) (j : Fin d → ℤ) (x y : E d) :
    ‖(c j : ℂ) * (physicalFeature H j x * conj (physicalFeature H j y))‖ = |c j| := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
    norm_physicalFeature, mul_one]

/-- The actual Gram entry is the sum of the positive-exponent Fourier series at physical lag
`x - y`. Absolute summability gives convergence even at a repeated location. -/
theorem hasSum_positive_phase (H : ℝ) {c : (Fin d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|)
    (x y : E d) :
    HasSum (fun j ↦ (c j : ℂ) *
      Complex.exp ((2 * Real.pi * (∑ i, H * (j i : ℝ) * (x i - y i)) : ℝ) * Complex.I))
      (FixedGridLaw.gramKernel c (physicalFeature H) x y) := by
  have hs : Summable (fun j ↦ ‖(c j : ℂ) *
      (physicalFeature H j x * conj (physicalFeature H j y))‖) := by
    simpa only [norm_gramTerm] using hc
  exact hs.of_norm.hasSum.congr_fun fun j ↦ by
    rw [physicalFeature_mul_conj, physicalFeature_eq_exp]
    rfl

/-- Multiplying every coefficient by a real amplitude scales the loss by its square. -/
theorem physicalLoss_mul (H a : ℝ) (c : (Fin d → ℤ) → ℝ) (x y : E d) :
    physicalLoss H (fun j ↦ a * c j) x y = a ^ 2 * physicalLoss H c x y := by
  simp only [physicalLoss, FixedGridLaw.gramKernel, Complex.ofReal_mul, mul_assoc,
    tsum_mul_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- With nonnegative summable coefficients, the diagonal loss equals the global envelope. -/
theorem kernelBounds (H : ℝ) {c : (Fin d → ℤ) → ℝ} (hn : ∀ j, 0 ≤ c j) (hc : Summable c) :
    IIDVariance.KernelBounds (physicalLoss H c) ((∑' j, c j) ^ 2) ((∑' j, c j) ^ 2) := by
  have hgram (x y : E d) : FixedGridLaw.gramKernel c (physicalFeature H) x y =
      FixedFourier.fourierSeries c (torusPoint H x - torusPoint H y) :=
    (FixedFourier.fourierSeries_sub_eq_gramKernel hc.abs _ _).symm
  constructor
  · change Measurable (fun p : E d × E d ↦ ‖FixedGridLaw.gramKernel c (physicalFeature H) p.1 p.2‖ ^ 2)
    simp_rw [hgram]
    exact (((FixedFourier.fourierSeries c).continuous.comp
      (((continuous_torusPoint H).comp continuous_fst).sub
        ((continuous_torusPoint H).comp continuous_snd))).norm.pow 2).measurable
  · intro x y
    have hconj : conj (FixedGridLaw.gramKernel c (physicalFeature H) x y) =
        FixedGridLaw.gramKernel c (physicalFeature H) y x := by
      simp only [FixedGridLaw.gramKernel, Complex.conj_tsum, map_mul, Complex.conj_ofReal,
        starRingEnd_self_apply]
      exact tsum_congr fun j ↦ by rw [mul_comm (conj _) _]
    simp only [physicalLoss, ← hconj, Complex.norm_conj]
  · intro x
    have hdiag : FixedGridLaw.gramKernel c (physicalFeature H) x x = ((∑' j, c j : ℝ) : ℂ) := by
      simp only [FixedGridLaw.gramKernel, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        norm_physicalFeature, one_pow, Complex.ofReal_one, mul_one, Complex.ofReal_tsum]
    simp only [physicalLoss, hdiag, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · exact fun _ _ ↦ sq_nonneg _
  · intro x y
    have hs : Summable (fun j ↦ ‖(c j : ℂ) *
        (physicalFeature H j x * conj (physicalFeature H j y))‖) := by
      simpa only [norm_gramTerm, abs_of_nonneg (hn _)] using hc
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [FixedGridLaw.gramKernel, norm_gramTerm, abs_of_nonneg (hn _)] using
      norm_tsum_le_tsum_norm hs

private theorem pairFeature_eq (H : ℝ) (p : (Fin d → ℤ) × (Fin d → ℤ)) (x : Fin d → ℝ) :
    FixedGridLaw.pairFeature (physicalFeature H) p x = physicalFeature H (p.1 - p.2) x := by
  simp only [FixedGridLaw.pairFeature, physicalFeature, sub_eq_add_neg, mFourier_add, mFourier_neg]

/-- `(lag, base)` parametrizes the ordered frequency pairs `(base, base + lag)`. -/
private def lagEquiv (G : Type*) [AddCommGroup G] : G × G ≃ G × G where
  toFun q := (q.2, q.2 + q.1)
  invFun p := (p.2 - p.1, p.1)
  left_inv := by rintro ⟨l, j⟩; simp
  right_inv := by rintro ⟨j, k⟩; simp

/-- For any physical probability law, the independent-pair Gram energy is the lag sum
of the design character powers times the autocorrelation of the Fourier coefficients. -/
theorem independentPair_eq_characterSpectrum (H : ℝ) (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] {c : (Fin d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) :
    (∫ p, ‖FixedGridLaw.gramKernel c (physicalFeature H) p.1 p.2‖ ^ 2 ∂μ.prod μ) =
      ∑' l, ‖∫ x, physicalFeature H (-l) x ∂μ‖ ^ 2 * ∑' j, c j * c (j + l) := by
  let F (p : (Fin d → ℤ) × (Fin d → ℤ)) :=
    c p.1 * c p.2 * ‖∫ x, physicalFeature H (p.1 - p.2) x ∂μ‖ ^ 2
  have hcc : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) ↦ |c p.1| * |c p.2| :=
    hc.mul_of_nonneg hc (fun _ ↦ abs_nonneg _) (fun _ ↦ abs_nonneg _)
  have hb (j : Fin d → ℤ) (x : Fin d → ℝ) : ‖physicalFeature H j x‖ ≤ 1 :=
    (norm_physicalFeature H j x).le
  have hi (j : Fin d → ℤ) : ‖∫ x, physicalFeature H j x ∂μ‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (ae_of_all μ (hb j))
  have hF : Summable F := by
    apply hcc.of_norm_bounded
    intro p
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (by simpa using pow_le_pow_left₀ (norm_nonneg _) (hi (p.1 - p.2)) 2)
  have hm (p : (Fin d → ℤ) × (Fin d → ℤ)) :
      Measurable (FixedGridLaw.pairFeature (physicalFeature H) p) := by
    simpa only [funext (pairFeature_eq H p)] using (continuous_physicalFeature H (p.1 - p.2)).measurable
  have hbp (p : (Fin d → ℤ) × (Fin d → ℤ)) (x : Fin d → ℝ) :
      ‖FixedGridLaw.pairFeature (physicalFeature H) p x‖ ≤ 1 := by
    rw [pairFeature_eq]; exact hb _ _
  have hs : Summable fun j ↦ |c j| * (1 : ℝ) ^ 2 := by simpa using hc
  have hsp : Summable fun p : (Fin d → ℤ) × (Fin d → ℤ) ↦ |c p.1 * c p.2| * (1 : ℝ) ^ 2 :=
    by simpa only [one_pow, mul_one, abs_mul] using hcc
  calc
    _ = (∫ p, FixedGridLaw.productKernel (fun q ↦ c q.1 * c q.2)
          (FixedGridLaw.pairFeature (physicalFeature H)) p.1 p.2 ∂μ.prod μ) := by
      exact integral_congr_ae (ae_of_all _ fun p ↦
        FixedGridLaw.sq_norm_gramKernel_eq_productKernel hb hs p.1 p.2)
    _ = ∑' p, F p := by
      rw [FixedGridLaw.integral_productKernel μ hm hbp hsp]
      simp only [F, pairFeature_eq]
    _ = ∑' q, F (lagEquiv (Fin d → ℤ) q) := ((lagEquiv _).tsum_eq F).symm
    _ = ∑' l, ∑' j, F (lagEquiv (Fin d → ℤ) (l, j)) :=
      (((lagEquiv (Fin d → ℤ)).summable_iff (f := F)).2 hF).tsum_prod
    _ = _ := by
      refine tsum_congr fun l ↦ ?_
      rw [← tsum_mul_left]
      refine tsum_congr fun j ↦ ?_
      change c j * c (j + l) * ‖∫ x, physicalFeature H (j - (j + l)) x ∂μ‖ ^ 2 = _
      rw [show j - (j + l) = -l by abel, mul_comm]

section Haar

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : (volume : Measure UnitAddCircle).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
local instance : (FixedFourier.normalizedHaar (Fin d)).IsNegInvariant :=
  Measure.pi.isNegInvariant (fun _ : Fin d ↦ (volume : Measure UnitAddCircle))

private theorem haar_fourierSeries_energy {c : (Fin d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) :
    (∫ z, ‖FixedFourier.fourierSeries c z‖ ^ 2 ∂FixedFourier.normalizedHaar (Fin d)) =
      ∑' j, c j ^ 2 := by
  let T := FixedFourier.fourierSeries c
  let f := ContinuousMap.toLp 2 (FixedFourier.normalizedHaar (Fin d)) ℂ T
  have hrep : ∀ᵐ z ∂FixedFourier.normalizedHaar (Fin d), f z = T z :=
    T.coeFn_toLp _
  have hcoeff (j : Fin d → ℤ) : mFourierCoeff f j = (c j : ℂ) :=
    (mFourierCoeff_toLp T j).trans (FixedFourier.mFourierCoeff_fourierSeries hc j)
  calc
    _ = ∫ z, ‖f z‖ ^ 2 ∂FixedFourier.normalizedHaar (Fin d) := by
      exact integral_congr_ae (hrep.mono fun _ hz ↦ congrArg (fun w : ℂ ↦ ‖w‖ ^ 2) hz.symm)
    _ = ∑' j, ‖mFourierCoeff f j‖ ^ 2 := (hasSum_sq_mFourierCoeff f).tsum_eq.symm
    _ = _ := by
      refine tsum_congr fun j ↦ ?_
      rw [hcoeff, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A physical design whose torus image is dominated by `L` times normalized Haar has
row energy at most `L` times the squared coefficient norm, at every physical point. -/
theorem conditionalRow_le_of_map_le (H : ℝ) (μ : Measure (Fin d → ℝ)) (L : ℝ≥0)
    (hdom : μ.map (torusPoint H) ≤ L • FixedFourier.normalizedHaar (Fin d))
    {c : (Fin d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) (x : Fin d → ℝ) :
    (∫ y, ‖FixedGridLaw.gramKernel c (physicalFeature H) x y‖ ^ 2 ∂μ) ≤
      (L : ℝ) * ∑' j, c j ^ 2 := by
  let g (z : UnitAddTorus (Fin d)) := ‖FixedFourier.fourierSeries c z‖ ^ 2
  have hg : Continuous g := (FixedFourier.fourierSeries c).continuous.norm.pow 2
  have hi : Integrable g (FixedFourier.normalizedHaar (Fin d)) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let t := torusPoint H x
  calc
    _ = ∫ y, g (t - torusPoint H y) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
        (FixedFourier.fourierSeries_sub_eq_gramKernel hc t (torusPoint H y)).symm
    _ = ∫ u, g (t - u) ∂μ.map (torusPoint H) :=
      (integral_map (continuous_torusPoint H).aemeasurable
        (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).symm
    _ ≤ ∫ u, g (t - u) ∂(L • FixedFourier.normalizedHaar (Fin d)) :=
      integral_mono_measure hdom (ae_of_all _ fun _ ↦ sq_nonneg _)
        ((hi.comp_sub_left t).smul_measure_nnreal)
    _ = (L : ℝ) * ∫ z, g z ∂FixedFourier.normalizedHaar (Fin d) := by
      rw [integral_smul_nnreal_measure, integral_sub_left_eq_self, NNReal.smul_def, smul_eq_mul]
    _ = _ := congrArg (fun s : ℝ ↦ (L : ℝ) * s) (haar_fourierSeries_energy hc)

end Haar

/-- For the actual spatial density, the independent-pair integral of the physical squared
Gram loss equals the sampled Fourier power weighted by the coefficient autocorrelation. -/
theorem independentPair_eq_spectrum (H : ℝ) (D : DesignLaw.Density d)
    {c : (Fin d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) :
    (∫ p : E d × E d, physicalLoss H c p.1 p.2 ∂D.μ.prod D.μ) =
      ∑' l, ‖FT D.ρ (sampleFreq H 0 l)‖ ^ 2 * ∑' j, c j * c (j + l) := by
  unfold physicalLoss
  rw [independentPair_eq_characterSpectrum H D.μ hc]
  simp only [physicalFeature, mFourier_neg_torusPoint, D.integral_char]

/-- For every physical row, the bounded cube-supported design contributes the factor
`D.L / H^d` to its squared coefficient energy. -/
theorem conditionalRow_le (D : DesignLaw.Density d) {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1)
    {c : (Fin d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) (x : E d) :
    (∫ y, physicalLoss H c x y ∂D.μ) ≤ (D.L : ℝ) / H ^ d * ∑' j, c j ^ 2 := by
  have hdom := torusLaw_le D.bounded D.support hH hH1
  simpa only [physicalLoss, NNReal.coe_mul, div_eq_mul_inv,
    Real.coe_toNNReal _ (inv_nonneg.mpr (pow_nonneg hH.le d))] using
      conditionalRow_le_of_map_le H D.μ _ hdom hc x

end MaternAudit.PairSpectrum
