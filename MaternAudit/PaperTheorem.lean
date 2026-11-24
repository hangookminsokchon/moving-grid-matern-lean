import MaternAudit.FullCovariance
import MaternAudit.RealCovariance
import MaternAudit.MaternBessel

/-! Real finite cosine-grid formulation and ordinary convergence in probability. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace MaternAudit.PaperTheorem
open MaternParameters MaternProfile PhysicalKernel FullCovariance MovingMatern
variable {d : ℕ}

/-- Real finite Fourier sum as a function of the lag. -/
def cosineGrid (ν ℓ h : ℝ) (m : ℕ) (z : E d) : ℝ :=
  ∑ j ∈ indexBox d m, coefficient ν ℓ h j *
    Real.cos (2 * Real.pi * ∑ i, (h * (j i : ℝ)) * z i)

theorem finiteGrid_re (ν ℓ h : ℝ) (m : ℕ) (x y : E d) :
    (finiteGrid ν ℓ h m x y).re = cosineGrid ν ℓ h m (x-y) := by
  unfold finiteGrid cosineGrid
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [feature_product_eq_char, Complex.re_ofReal_mul, Complex.conj_re,
    DesignParseval.char_eq_exp, Complex.exp_ofReal_mul_I_re, neg_mul, Real.cos_neg]
  rfl

/-- Classical Matérn covariance, with unit marginal variance and the positive-real
Schläfli integral for the modified Bessel function of the second kind. -/
def maternCov (ν ℓ : ℝ) (z : E d) : ℝ :=
  if z = 0 then 1 else (2 : ℝ) ^ (1-ν) * (MaternBessel.scaledRadius ν ℓ z)^ν *
    MaternBessel.besselK ν (MaternBessel.scaledRadius ν ℓ z) / Real.Gamma ν

theorem kernel_re_eq_maternCov {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (z : E d) :
    (kernel ν ℓ z).re = maternCov ν ℓ z := by
  by_cases hz : z = 0
  · subst z
    simp [maternCov, SpectralNormalization.kernel_zero hν hℓ]
  · rw [maternCov, if_neg hz, MaternBessel.kernel_eq_besselK hν hℓ hz, Complex.ofReal_re]

/-- Entrywise real RMS against an exact lag covariance, divided by the number of observations. -/
def covarianceRMS {N : ℕ} (ν ℓ h : ℝ) (m : ℕ) (k : E d → ℝ) (x : Fin N → E d) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (cosineGrid ν ℓ h m (x i-x j) - k (x i-x j))^2) / (N : ℝ)

/-- Alias at a single physical lag, before applying the cutoff. -/
def lagAlias (ν ℓ h : ℝ) (z : E d) := infiniteGrid ν ℓ h z 0 - kernel ν ℓ z

theorem alias_eq_lag (ν ℓ h : ℝ) (x y : E d) :
    PhysicalKernel.alias ν ℓ h x y = lagAlias ν ℓ h (x-y) := by
  simp only [PhysicalKernel.alias, lagAlias, infiniteGrid, FixedGridLaw.gramKernel,
    feature_product_eq_char, sub_zero]

theorem aliasBound_of_lags {ν ℓ h η : ℝ}
    (ha : ∀ z : E d, ‖z‖ ≤ 1 → ‖lagAlias ν ℓ h z‖ ≤ η) : AliasBound d ν ℓ h η := by
  intro x hx y hy
  rw [alias_eq_lag]
  apply ha
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  obtain ⟨hx₀, hx₁⟩ := hx i (Set.mem_univ i)
  obtain ⟨hy₀, hy₁⟩ := hy i (Set.mem_univ i)
  change |x i - y i| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem fullRMS_eq_cosine (g : Grid) (ν : ℝ) (X : ℕ → Ω → E d) (n : ℕ) (ω : Ω) :
    fullRMS g ν X n ω = covarianceRMS ν (g.len n) (g.h n) (g.m n)
      (fun z ↦ (kernel ν (g.len n) z).re) (fun i : Fin (g.N n) ↦ X i ω) := by
  change AliasTransfer.frobeniusNorm _ / (g.N n : ℝ) = _
  have h := RealCovariance.frobeniusNorm_error_eq_real ν (g.len n) (g.h n) (g.m n)
    (fun i : Fin (g.N n) ↦ X i ω)
  change AliasTransfer.frobeniusNorm (fun i j : Fin (g.N n) ↦
    finiteGrid ν (g.len n) (g.h n) (g.m n) (X i ω) (X j ω) -
      kernel ν (g.len n) (X i ω - X j ω)) / (g.N n : ℝ) = _
  rw [h]
  simp only [covarianceRMS, finiteGrid_re]

omit [MeasurableSpace Ω] in
theorem fullRMS_eq_matern (g : Grid) {ν : ℝ} (hν : 0 < ν) (X : ℕ → Ω → E d) (n : ℕ) (ω : Ω) :
    fullRMS g ν X n ω = covarianceRMS ν (g.len n) (g.h n) (g.m n)
      (maternCov ν (g.len n)) (fun i : Fin (g.N n) ↦ X i ω) := by
  simpa only [kernel_re_eq_maternCov hν (g.len_pos n)] using fullRMS_eq_cosine g ν X n ω

/-- Both sharp limits for the finite real cosine approximation to the original
Bessel Matérn covariance, with aliasing controlled on the closed lag cube. -/
theorem sharp_covariance_rms (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E d} (hx : IIDVariance.SampleLaw P D.μ X)
    (η : ℕ → ℝ) (halias : ∀ n (z : E d), ‖z‖ ≤ 1 → ‖lagAlias ν (g.len n) (g.h n) z‖ ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / baseRate d ν g n) atTop (𝓝 0)) :
    let F (n : ℕ) (ω : Ω) := covarianceRMS ν (g.len n) (g.h n) (g.m n)
      (maternCov ν (g.len n)) (fun i : Fin (g.N n) ↦ X i ω)
    Tendsto (fun n ↦ (∫ ω, F n ω ^ 2 ∂P) / leadingSq g ν D n) atTop (𝓝 1) ∧
    TendstoInMeasure P (fun n ω ↦ F n ω / Real.sqrt (leadingSq g ν D n)) atTop (fun _ ↦ 1) := by
  dsimp only
  obtain ⟨he, hp⟩ := movingMatern_full_sharp hd hν g D hx η (fun n ↦ aliasBound_of_lags (halias n)) hsmall
  simp_rw [← fullRMS_eq_matern g hν X]
  exact ⟨he, (AliasTransfer.tendstoInMeasure_iff_real_tail P).mpr hp⟩

end MaternAudit.PaperTheorem
