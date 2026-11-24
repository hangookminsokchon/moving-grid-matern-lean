import MaternAudit.MaternParameters
import MaternAudit.MaternProfile
import MaternAudit.DesignParseval
import MaternAudit.SampleTightness
import MaternAudit.MovingLimit
import MaternAudit.PairSpectrum

/-!
# Population Fourier energy on a growing Matérn grid

The design weights live at physical frequencies `h r` and have fixed total
mass by sampled Parseval. On a bounded physical frequency window the shift in
the Matérn profile is `r / m = (h r) / R`, which vanishes as the cutoff grows.
-/

noncomputable section

namespace MaternAudit.PopulationLimit

open Filter MeasureTheory MaternParameters MaternProfile
open scoped Topology

variable {d : ℕ}

/-- The omitted Fourier coefficients after removing the common spectral amplitude. -/
def coeff (g : Grid) (ν : ℝ) (n : ℕ) (j : Z d) : ℝ :=
  ((g.m n : ℝ) ^ d)⁻¹ * b (beta d ν) (g.t ν n) (g.m n) j

theorem omitted_eq_amplitude_mul_coeff (g : Grid) (ν : ℝ) (n : ℕ) (j : Z d) :
    omitted ν (g.len n) (g.h n) (g.m n) j =
      amplitude d ν (g.len n) (g.R n) * coeff g ν n j := by
  rw [omitted_eq_rescaled (g.len_pos n) (g.h_pos n) (g.m_pos n)]
  exact mul_assoc _ _ _

private theorem lt_beta {ν : ℝ} (hν : 0 < ν) : (d : ℝ) < beta d ν := by
  unfold beta
  linarith

theorem coeff_nonneg (g : Grid) (ν : ℝ) (n : ℕ) (j : Z d) : 0 ≤ coeff g ν n j :=
  mul_nonneg (by positivity) (b_nonneg _ _ _ _)

theorem summable_coeff (g : Grid) {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    Summable (coeff (d := d) g ν n) :=
  (summable_b (lt_beta hν) (g.t ν n) (g.m n)).mul_left _

theorem summable_abs_coeff (g : Grid) {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    Summable (fun j : Z d => |coeff g ν n j|) := by
  simpa only [abs_of_nonneg (coeff_nonneg g ν n _)] using summable_coeff (d := d) g hν n

theorem tsum_coeff (g : Grid) (ν : ℝ) (n : ℕ) :
    (∑' j : Z d, coeff g ν n j) =
      (∑' j : Z d, b (beta d ν) (g.t ν n) (g.m n) j) / (g.m n : ℝ) ^ d := by
  simp only [coeff, tsum_mul_left, div_eq_inv_mul]

theorem tendsto_coeff_mass (g : Grid) {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun n => ∑' j : Z d, coeff g ν n j) atTop (𝓝 (I1 d (beta d ν))) := by
  simpa only [tsum_coeff] using (tendsto_mass (lt_beta hν) g.m_grows (g.t_zero ν))

/-- Parseval's `h⁻ᵈ` times the squared coefficient sum, on the relative scale `v = R⁻ᵈ`. -/
theorem tendsto_coeff_energy (g : Grid) {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun n => ((g.h n) ^ d)⁻¹ * (∑' j : Z d, coeff g ν n j ^ 2) / g.v d n)
      atTop (𝓝 (I2 d (beta d ν))) := by
  refine (tendsto_energy (lt_beta hν) g.m_grows (g.t_zero ν)).congr fun n => ?_
  simp only [coeff, mul_pow, tsum_mul_left, Grid.v, Grid.R, mul_pow]
  field_simp [Nat.cast_ne_zero.mpr (g.m_pos n).ne', (g.h_pos n).ne']
  ring

/-- Normalized coefficient autocorrelation in the rescaled profile coordinates. -/
def profileAutocorrelation (g : Grid) (ν : ℝ) (n : ℕ) (r : Z d) : ℝ :=
  (∑' j : Z d, b (beta d ν) (g.t ν n) (g.m n) j *
    b (beta d ν) (g.t ν n) (g.m n) (j + r)) / (g.m n : ℝ) ^ d

/-- Physical design frequency of the lattice lag `r`. -/
def frequency (g : Grid) (n : ℕ) (r : Z d) : E d := fun i => g.h n * (r i : ℝ)

@[simp] theorem frequency_zero (g : Grid) (n : ℕ) : frequency g n (0 : Z d) = 0 := by
  funext i
  simp [frequency]

/-- `Rᵈ` times the independent-pair spectrum of the amplitude-normalized tail. -/
def normalizedPairSpectrum (g : Grid) (ν : ℝ) (ρ : E d → ℝ) (n : ℕ) : ℝ :=
  (g.R n) ^ d * ∑' r : Z d, ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2 *
    ∑' j : Z d, coeff g ν n j * coeff g ν n (j + r)

private theorem autocorrelation_nonneg (g : Grid) (ν : ℝ) (n : ℕ) (r : Z d) :
    0 ≤ profileAutocorrelation g ν n r :=
  div_nonneg (tsum_nonneg fun j => mul_nonneg (b_nonneg _ _ _ j) (b_nonneg _ _ _ (j + r))) (by positivity)

private theorem autocorrelation_le_mass (g : Grid) {ν : ℝ} (hν : 0 < ν) (n : ℕ) (r : Z d) :
    profileAutocorrelation g ν n r ≤ ∑' j : Z d, coeff g ν n j := by
  have hβ := lt_beta (d := d) hν
  rw [tsum_coeff, profileAutocorrelation]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (summable_b_mul_shift hβ _ _ r).tsum_le_tsum (fun j =>
    mul_le_of_le_one_right (b_nonneg _ _ _ j) (b_le_one ((Nat.cast_nonneg d).trans hβ.le) _ _ _))
    (summable_b hβ _ _)

private theorem frequency_eq_smul (g : Grid) (n : ℕ) (r : Z d) :
    frequency g n r = g.R n • MovingCells.gridPoint (g.m n) r := by
  funext i
  change g.h n * (r i : ℝ) = (g.h n * (g.m n : ℝ)) * ((r i : ℝ) / (g.m n : ℝ))
  field_simp [Nat.cast_ne_zero.mpr (g.m_pos n).ne']
  ring

private theorem window_shift_tendsto (g : Grid) {K : ℝ} (r : ℕ → Z d)
    (hr : ∀ n, ‖frequency g n (r n)‖ ≤ K) :
    Tendsto (fun n => MovingCells.gridPoint (g.m n) (r n)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (g.radius_grows.const_div_atTop K)
  apply (le_div_iff₀ (g.R_pos n)).mpr
  simpa only [frequency_eq_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (g.R_pos n), mul_comm] using hr n

private theorem uniform_window (g : Grid) {ν : ℝ} (hν : 0 < ν) {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ r : Z d, ‖frequency g n r‖ ≤ K →
      |profileAutocorrelation g ν n r - I2 d (beta d ν)| ≤ δ := by
  apply MovingLimit.uniform_of_selections (fun n => {r : Z d | ‖frequency g n r‖ ≤ K}) 0
    (fun n => by
      change ‖frequency g n (0 : Z d)‖ ≤ K
      simpa only [frequency_zero, norm_zero] using hK)
    (profileAutocorrelation g ν) (I2 d (beta d ν)) _ hδ
  intro r hr
  exact tendsto_shifted_energy (lt_beta hν) g.m_grows (g.t_zero ν) (window_shift_tendsto g r hr)

/-- Splitting `Rᵈ = hᵈ mᵈ` puts `hᵈ` in the sampled Parseval weights. -/
theorem normalizedPairSpectrum_eq (g : Grid) (ν : ℝ) (ρ : E d → ℝ) (n : ℕ) :
    normalizedPairSpectrum g ν ρ n = ∑' r : Z d,
      ((g.h n) ^ d * ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2) * profileAutocorrelation g ν n r := by
  unfold normalizedPairSpectrum
  rw [← tsum_mul_left]
  refine tsum_congr fun r => ?_
  let a : Z d → ℝ := b (beta d ν) (g.t ν n) (g.m n)
  have hp (j : Z d) : coeff g ν n j * coeff g ν n (j + r) =
      (((g.m n : ℝ) ^ d)⁻¹) ^ 2 * (a j * a (j + r)) := by unfold coeff a; ring
  simp_rw [hp]
  rw [tsum_mul_left, profileAutocorrelation, Grid.R, mul_pow]
  change _ = _ * ((∑' j : Z d, a j * a (j + r)) / (g.m n : ℝ) ^ d)
  field_simp [Nat.cast_ne_zero.mpr (g.m_pos n).ne']
  ring

private theorem designWeights_hasSum (g : Grid) (n : ℕ) {ρ : E d → ℝ} (h₂ : MemLp ρ 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ DesignParseval.unitCube d → ρ x = 0) :
    HasSum (fun r : Z d => (g.h n) ^ d * ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2)
      (∫ x, ρ x ^ 2) := by
  obtain ⟨hu, he⟩ := DesignParseval.sampled_parseval h₂ hs (g.h_pos n) (g.h_le_one n) 0
  have hpoint : DesignParseval.sampleFreq (g.h n) (0 : E d) = frequency g n := by
    funext r i
    exact add_zero _
  rw [hpoint] at hu he
  exact he ▸ hu.hasSum.mul_left ((g.h n) ^ d)

private theorem designWeights_tight (g : Grid) {ρ : E d → ℝ} (h₁ : Integrable ρ)
    (h₂ : MemLp ρ 2 volume) (hs : ∀ᵐ x ∂volume, x ∉ DesignParseval.unitCube d → ρ x = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K ≥ (0 : ℝ), ∀ᶠ n in atTop, (∑' r : Z d, if K < ‖frequency g n r‖ then
      (g.h n) ^ d * ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2 else 0) ≤ δ := by
  have hp (H : ℝ) (hH : H ∈ Set.Icc (1/2 : ℝ) 1) (α : E d) :=
    DesignParseval.sampled_parseval h₂ hs (lt_of_lt_of_le (by norm_num) hH.1) hH.2 α
  obtain ⟨K, hK, ht⟩ := SampleTightness.uniform_sampled_energy_tight (DesignParseval.FT ρ)
    (DesignParseval.continuous_FT h₁) (∫ x, ρ x ^ 2)
    (fun H hH α _ => (hp H hH α).1) (fun H hH α _ => (hp H hH α).2) δ hδ
  refine ⟨K, hK, Eventually.of_forall fun n => ?_⟩
  apply le_trans _ (ht (g.h n) (g.h_pos n) (g.h_le_one n))
  rw [← tsum_mul_left]
  apply le_of_eq
  apply tsum_congr
  intro r
  change (if K < ‖frequency g n r‖ then (g.h n) ^ d * ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2 else 0) =
    (g.h n) ^ d * (if K < ‖frequency g n r‖ then ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2 else 0)
  by_cases hk : K < ‖frequency g n r‖ <;> simp only [hk, if_true, if_false, mul_zero]

/-- Population leading constant for an arbitrary growing grid and a cube-supported
real design function in `L¹ ∩ L²`. -/
theorem tendsto_normalizedPairSpectrum (g : Grid) {ν : ℝ} (hν : 0 < ν) {ρ : E d → ℝ}
    (h₁ : Integrable ρ) (h₂ : MemLp ρ 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ DesignParseval.unitCube d → ρ x = 0) :
    Tendsto (normalizedPairSpectrum g ν ρ) atTop (𝓝 ((∫ x, ρ x ^ 2) * I2 d (beta d ν))) := by
  let M := |I1 d (beta d ν)| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hlarge : I1 d (beta d ν) < M := lt_of_le_of_lt (le_abs_self _) (lt_add_one _)
  have hb : ∀ᶠ n in atTop, ∀ r : Z d, |profileAutocorrelation g ν n r| ≤ M := by
    filter_upwards [(tendsto_coeff_mass g hν).eventually (gt_mem_nhds hlarge)] with n hn r
    rw [abs_of_nonneg (autocorrelation_nonneg g ν n r)]
    exact (autocorrelation_le_mass g hν n r).trans hn.le
  have h := MovingLimit.weighted_limit_of_tight
    (fun n (r : Z d) => (g.h n) ^ d * ‖DesignParseval.FT ρ (frequency g n r)‖ ^ 2)
    (profileAutocorrelation g ν) (fun n r => ‖frequency g n r‖)
    (∫ x, ρ x ^ 2) (I2 d (beta d ν)) M
    (fun n _ => mul_nonneg (pow_nonneg (g.h_pos n).le _) (sq_nonneg _))
    (fun n => designWeights_hasSum g n h₂ hs) hM hb (designWeights_tight g h₁ h₂ hs)
    (fun _ hK _ hδ => uniform_window g hν hK hδ)
  exact h.congr fun n => (normalizedPairSpectrum_eq g ν ρ n).symm

/-- The negative physical character integrated under a nonnegative density is its
ordinary Fourier transform at the physical grid frequency. -/
theorem integral_physicalFeature_neg_eq_FT (H : ℝ) {ρ : E d → ℝ} (h₁ : Integrable ρ)
    (h₀ : ∀ᵐ x ∂volume, 0 ≤ ρ x) (r : Z d) :
    (∫ x, PairSpectrum.physicalFeature H (-r) x ∂DesignParseval.spatialLaw ρ) =
      DesignParseval.FT ρ (fun i => H * (r i : ℝ)) := by
  unfold DesignParseval.spatialLaw DesignParseval.FT
  rw [integral_withDensity_eq_integral_toReal_smul₀ h₁.aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _]
  apply integral_congr_ae
  filter_upwards [h₀] with x hx
  have hfreq : DesignParseval.sampleFreq H (0 : E d) r = fun i => H * (r i : ℝ) :=
    funext fun _ => add_zero _
  have hchar : PairSpectrum.physicalFeature H (-r) x =
      DesignParseval.char (fun i => H * (r i : ℝ)) x := by
    simpa only [hfreq] using DesignParseval.mFourier_neg_torusPoint H r x
  rw [hchar, ENNReal.toReal_ofReal hx, Complex.real_smul, mul_comm]

/-- Exact finite-row link to the independent-pair integral in `PairSpectrum`. -/
theorem independentPair_eq_normalizedPairSpectrum (g : Grid) {ν : ℝ} (hν : 0 < ν)
    {ρ : E d → ℝ} (h₁ : Integrable ρ) (h₀ : ∀ᵐ x ∂volume, 0 ≤ ρ x)
    [IsProbabilityMeasure (DesignParseval.spatialLaw ρ)] (n : ℕ) :
    (g.R n) ^ d * (∫ p, ‖FixedGridLaw.gramKernel (coeff g ν n) (PairSpectrum.physicalFeature (g.h n))
      p.1 p.2‖ ^ 2 ∂(DesignParseval.spatialLaw ρ).prod (DesignParseval.spatialLaw ρ)) =
        normalizedPairSpectrum g ν ρ n := by
  rw [normalizedPairSpectrum, PairSpectrum.independentPair_eq_characterSpectrum (g.h n)
    (DesignParseval.spatialLaw ρ) (summable_abs_coeff (d := d) g hν n)]
  apply congrArg (fun s : ℝ => (g.R n) ^ d * s)
  exact tsum_congr fun r => congrArg (fun z : ℂ => ‖z‖ ^ 2 * ∑' j : Z d, coeff g ν n j * coeff g ν n (j + r))
    (integral_physicalFeature_neg_eq_FT (g.h n) h₁ h₀ r)

/-- For an ordinary probability density the population spectral limit is the
normalized squared Gram-kernel energy of an independent pair of locations. -/
theorem tendsto_independentPair (g : Grid) {ν : ℝ} (hν : 0 < ν) {ρ : E d → ℝ}
    (h₁ : Integrable ρ) (h₂ : MemLp ρ 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ DesignParseval.unitCube d → ρ x = 0)
    (h₀ : ∀ᵐ x ∂volume, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) :
    Tendsto (fun n => (g.R n) ^ d * (∫ p, ‖FixedGridLaw.gramKernel (coeff g ν n)
      (PairSpectrum.physicalFeature (g.h n)) p.1 p.2‖ ^ 2
      ∂(DesignParseval.spatialLaw ρ).prod (DesignParseval.spatialLaw ρ))) atTop
        (𝓝 ((∫ x, ρ x ^ 2) * I2 d (beta d ν))) := by
  letI : IsProbabilityMeasure (DesignParseval.spatialLaw ρ) := ⟨by
    rw [DesignParseval.spatialLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal h₁ h₀, hmass, ENNReal.ofReal_one]⟩
  exact (tendsto_normalizedPairSpectrum g hν h₁ h₂ hs).congr fun n =>
    (independentPair_eq_normalizedPairSpectrum g hν h₁ h₀ n).symm

end MaternAudit.PopulationLimit
