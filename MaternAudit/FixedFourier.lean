import MaternAudit.FixedGridLaw
import MaternAudit.FourierBound

/-!
# Fixed stationary Fourier series on the unit torus

The Fourier series is constructed in the uniform norm from its real coefficients.
The kernel at a pair of locations is evaluated at their difference, including at zero
for repeated locations. All Haar measures below have total mass one.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory UnitAddTorus
open scoped Topology NNReal ComplexConjugate

namespace MaternAudit.FixedFourier

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : (volume : Measure UnitAddCircle).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular _

/-- Product of the normalized Haar probability measures on the coordinate circles. -/
abbrev normalizedHaar (d : Type*) [Fintype d] : Measure (UnitAddTorus d) :=
  Measure.pi (fun _ : d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))

variable {d : Type*} [Fintype d]

local instance : (normalizedHaar d).IsNegInvariant :=
  Measure.pi.isNegInvariant (fun _ : d ↦ (volume : Measure UnitAddCircle))

/-- The continuous stationary profile with prescribed absolutely summable real coefficients. -/
def fourierSeries (c : (d → ℤ) → ℝ) : C(UnitAddTorus d, ℂ) :=
  ∑' j, (c j : ℂ) • mFourier j

theorem hasSum_fourierSeries {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) :
    HasSum (fun j ↦ (c j : ℂ) • mFourier j) (fourierSeries c) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [norm_smul, mFourier_norm, mul_one, Complex.norm_real, Real.norm_eq_abs] using hc

/-- The actual torus characters take differences to products with complex conjugates. -/
theorem mFourier_apply_sub (j : d → ℤ) (x y : UnitAddTorus d) :
    mFourier j (x - y) = mFourier j x * conj (mFourier j y) := by
  have h (n : ℤ) (u v : UnitAddCircle) :
      fourier n (u - v) = fourier n u * conj (fourier n v) := by
    rw [sub_eq_add_neg, fourier_apply, smul_add, smul_neg, AddCircle.toCircle_add, Circle.coe_mul,
      fourier_neg']
    rfl
  simp only [mFourier, ContinuousMap.coe_mk, Pi.sub_apply, h, Finset.prod_mul_distrib, map_prod]

theorem fourierSeries_sub_eq_gramKernel {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|)
    (x y : UnitAddTorus d) :
    fourierSeries c (x - y) = FixedGridLaw.gramKernel c (fun j z ↦ mFourier j z) x y := by
  have he := ((ContinuousMap.evalCLM ℂ (x - y)).hasSum (hasSum_fourierSeries hc)).tsum_eq.symm
  simpa only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul, mFourier_apply_sub,
    FixedGridLaw.gramKernel] using he

/-- The normalized Haar Fourier coefficients of the constructed series are the prescribed
coefficients. This uses the orthonormality of the multidimensional characters in `L²`. -/
theorem mFourierCoeff_fourierSeries {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|)
    (k : d → ℤ) : mFourierCoeff (fourierSeries c) k = (c k : ℂ) := by
  classical
  let T := ContinuousMap.toLp 2 (normalizedHaar d) ℂ (fourierSeries c)
  have hsum : HasSum (fun j ↦ (c j : ℂ) • mFourierLp 2 j) T := by
    simpa only [map_smul] using
      (ContinuousMap.toLp 2 (normalizedHaar d) ℂ).hasSum (hasSum_fourierSeries hc)
  have hinner := ((innerSL ℂ (mFourierLp 2 k)).hasSum hsum).tsum_eq.symm
  rw [← mFourierCoeff_toLp (fourierSeries c), ← mFourierBasis_repr,
    HilbertBasis.repr_apply_apply, coe_mFourierBasis]
  have hdelta : (∑' j : d → ℤ, if k = j then (c j : ℂ) else 0) = (c k : ℂ) := by
    rw [tsum_eq_single k (fun j hj ↦ if_neg hj.symm), if_pos rfl]
  simpa only [innerSL_apply, inner_smul_right, orthonormal_iff_ite.mp orthonormal_mFourier,
    mul_ite, mul_one, mul_zero, hdelta] using hinner

/-- Squared Frobenius norm divided by `n²` for the lag kernel with profile `T`. -/
def sampleEnergy (T : C(UnitAddTorus d, ℂ)) (x : ℕ → UnitAddTorus d) (n : ℕ) : ℝ :=
  FixedGridLaw.pairMean (fun u v ↦ ‖T (u - v)‖ ^ 2) x n

/-- Squared lag energy of an independent pair from the design law `ν`. -/
def populationEnergy (T : C(UnitAddTorus d, ℂ)) (ν : Measure (UnitAddTorus d)) : ℝ :=
  ∫ p : UnitAddTorus d × UnitAddTorus d, ‖T (p.1 - p.2)‖ ^ 2 ∂ν.prod ν

/-- The sample energy converges almost surely to the actual independent-pair integral
for every common law. Pairwise independence suffices. -/
theorem sampleEnergy_tendsto_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure (UnitAddTorus d)} {X : ℕ → Ω → UnitAddTorus d}
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hlaw : ∀ i, IdentDistrib (X i) id μ ν)
    {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|) :
    ∀ᵐ ω ∂μ, Tendsto (sampleEnergy (fourierSeries c) (fun i ↦ X i ω)) atTop
      (𝓝 (populationEnergy (fourierSeries c) ν)) := by
  have hmap : μ.map (X 0) = ν := by simpa using (hlaw 0).map_eq
  have hm (j : d → ℤ) : Measurable (mFourier j) := (mFourier j).continuous.measurable
  have hb (j : d → ℤ) (x : UnitAddTorus d) : ‖mFourier j x‖ ≤ 1 := by
    simpa only [mFourier_norm] using (mFourier j).norm_coe_le_norm x
  have hs : Summable fun j ↦ |c j| * (1 : ℝ) ^ 2 := by simpa using hc
  have he := FixedGridLaw.pairMean_sq_norm_gramKernel_tendsto_ae hind
    (fun i ↦ (hlaw i).trans (hlaw 0).symm) hm hb hs
  unfold sampleEnergy populationEnergy
  simp_rw [fourierSeries_sub_eq_gramKernel hc]
  simpa only [hmap] using he

/-- Measure domination in only the second coordinate suffices. Haar invariance makes its
lag integral independent of the first point. -/
theorem populationEnergy_le_haar (T : C(UnitAddTorus d, ℂ))
    (ν : Measure (UnitAddTorus d)) [IsProbabilityMeasure ν] (L : ℝ≥0)
    (hdom : ν ≤ L • normalizedHaar d) :
    populationEnergy T ν ≤ (L : ℝ) * ∫ z, ‖T z‖ ^ 2 ∂normalizedHaar d := by
  let g (z : UnitAddTorus d) := ‖T z‖ ^ 2
  have hcont : Continuous g := T.continuous.norm.pow 2
  have hi : Integrable g (normalizedHaar d) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpair : Integrable (fun p : UnitAddTorus d × UnitAddTorus d ↦ g (p.1 - p.2)) (ν.prod ν) :=
    (hcont.comp (continuous_fst.sub continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hinner (x : UnitAddTorus d) :
      (∫ y, g (x - y) ∂ν) ≤ (L : ℝ) * ∫ z, g z ∂normalizedHaar d := by
    calc
      _ ≤ ∫ y, g (x - y) ∂(L • normalizedHaar d) :=
        integral_mono_measure hdom (ae_of_all _ fun _ ↦ sq_nonneg _)
          ((hi.comp_sub_left x).smul_measure_nnreal)
      _ = _ := by
        rw [integral_smul_nnreal_measure, integral_sub_left_eq_self, NNReal.smul_def, smul_eq_mul]
  change (∫ p, g (p.1 - p.2) ∂ν.prod ν) ≤ _
  rw [integral_prod _ hpair]
  calc
    _ ≤ ∫ _x : UnitAddTorus d, (L : ℝ) * (∫ z, g z ∂normalizedHaar d) ∂ν :=
      integral_mono_of_nonneg (ae_of_all _ fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)
        (integrable_const _) (ae_of_all _ hinner)
    _ = _ := by simp [g]

/-- The density form of the torus pair bound, evaluated on the continuous Fourier
series itself. Translation preserves the almost-everywhere agreement with its
`L²` representative in each inner integral. -/
theorem density_pair_le_spectral {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|)
    (ρ : UnitAddTorus d → ℝ) (L : ℝ) (hρ : Integrable ρ (normalizedHaar d))
    (hprob : ∫ x, ρ x ∂normalizedHaar d = 1) (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ L) :
    (∫ x, ρ x * (∫ y, ρ y * ‖fourierSeries c (x - y)‖ ^ 2 ∂normalizedHaar d)
      ∂normalizedHaar d) ≤ L * ∑' j, c j ^ 2 := by
  let T := ContinuousMap.toLp 2 (normalizedHaar d) ℂ (fourierSeries c)
  have hrep : ∀ᵐ z ∂normalizedHaar d, T z = fourierSeries c z :=
    (fourierSeries c).coeFn_toLp (normalizedHaar d)
  have hinter (x : UnitAddTorus d) : (∫ y, ρ y * ‖T (x - y)‖ ^ 2 ∂normalizedHaar d) =
      ∫ y, ρ y * ‖fourierSeries c (x - y)‖ ^ 2 ∂normalizedHaar d := by
    apply integral_congr_ae
    filter_upwards [(quasiMeasurePreserving_sub_left (normalizedHaar d) x).ae hrep] with y hy
    rw [hy]
  have hcoeff (j : d → ℤ) : mFourierCoeff T j = (c j : ℂ) :=
    (mFourierCoeff_toLp (fourierSeries c) j).trans (mFourierCoeff_fourierSeries hc j)
  have hpair : (∫ x, ρ x * (∫ y, ρ y * ‖T (x - y)‖ ^ 2 ∂normalizedHaar d)
      ∂normalizedHaar d) ≤ L * ∑' j, ‖mFourierCoeff T j‖ ^ 2 :=
    MaternAudit.iid_torus_pair_le_spectral_energy T ρ L hρ hprob hn hb
  simpa only [hinter, hcoeff, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hpair

/-- If the design law is at most `L` times normalized Haar, the population limit
is bounded by `L` times the sum of the squares of the prescribed coefficients. -/
theorem populationEnergy_le_spectral {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|)
    (ν : Measure (UnitAddTorus d)) [IsProbabilityMeasure ν] (L : ℝ≥0)
    (hdom : ν ≤ L • normalizedHaar d) :
    populationEnergy (fourierSeries c) ν ≤ (L : ℝ) * ∑' j, c j ^ 2 := by
  have htranslate (x : UnitAddTorus d) :
      (∫ y, ‖fourierSeries c (x - y)‖ ^ 2 ∂normalizedHaar d) =
      ∫ z, ‖fourierSeries c z‖ ^ 2 ∂normalizedHaar d :=
    integral_sub_left_eq_self (fun z ↦ ‖fourierSeries c z‖ ^ 2) (normalizedHaar d) x
  have hHaar : (∫ z, ‖fourierSeries c z‖ ^ 2 ∂normalizedHaar d) ≤ ∑' j, c j ^ 2 := by
    simpa only [one_mul, htranslate, integral_const, measureReal_univ_eq_one, one_smul] using
      density_pair_le_spectral hc (fun _ ↦ 1) 1 (integrable_const 1) (by simp)
        (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl)
  exact (populationEnergy_le_haar _ ν L hdom).trans (mul_le_mul_of_nonneg_left hHaar L.coe_nonneg)

/-- On one probability-one event the normalized squared Frobenius norm eventually
satisfies the spectral bound with each strictly positive additive slack. -/
theorem sampleEnergy_eventually_lt_spectral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure (UnitAddTorus d)} {X : ℕ → Ω → UnitAddTorus d}
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) μ)
    (hlaw : ∀ i, IdentDistrib (X i) id μ ν)
    {c : (d → ℤ) → ℝ} (hc : Summable fun j ↦ |c j|)
    (L : ℝ≥0) (hdom : ν ≤ L • normalizedHaar d) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      sampleEnergy (fourierSeries c) (fun i ↦ X i ω) n < (L : ℝ) * (∑' j, c j ^ 2) + ε := by
  have hmap : μ.map (X 0) = ν := by simpa using (hlaw 0).map_eq
  haveI : IsProbabilityMeasure ν := hmap ▸ isProbabilityMeasure_map (hlaw 0).aemeasurable_fst
  have hb := populationEnergy_le_spectral hc ν L hdom
  filter_upwards [sampleEnergy_tendsto_ae hind hlaw hc] with ω hω
  intro ε hε
  exact hω.eventually_lt_const (hb.trans_lt (lt_add_of_pos_right _ hε))

end MaternAudit.FixedFourier
