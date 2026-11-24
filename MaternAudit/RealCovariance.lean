import MaternAudit.SpectralNormalization
import MaternAudit.AliasTransfer

/-!
# Reality of the physical Matérn covariance entries

Frequency negation conjugates the Fourier character and preserves the Matérn
density. The finite index box and product Lebesgue measure are both invariant
under this negation.
-/

noncomputable section

namespace MaternAudit.RealCovariance

open MeasureTheory MovingCells MaternParameters PhysicalKernel PairSpectrum
open scoped ComplexConjugate

variable {d : ℕ}

theorem spectralDensity_neg (ν ℓ : ℝ) (ξ : E d) :
    spectralDensity ν ℓ (-ξ) = spectralDensity ν ℓ ξ := by
  simp [spectralDensity, MaternProfile.radiusSq]

private theorem lattice_neg (j : Z d) : lattice (-j) = -lattice j := by
  funext i
  simp [lattice]

theorem coefficient_neg (ν ℓ h : ℝ) (j : Z d) :
    coefficient ν ℓ h (-j) = coefficient ν ℓ h j := by
  simp only [coefficient, lattice_neg, smul_neg, spectralDensity_neg]

theorem neg_mem_indexBox (m : ℕ) (j : Z d) :
    -j ∈ indexBox d m ↔ j ∈ indexBox d m := by
  rw [mem_indexBox, mem_indexBox, lattice_neg, norm_neg]

private theorem char_neg_freq (ξ z : E d) :
    DesignParseval.char (-ξ) z = conj (DesignParseval.char ξ z) := by
  have hdot : (∑ i, (-ξ) i * z i) = -(∑ i, ξ i * z i) := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [DesignParseval.char_eq_exp (-ξ) z, DesignParseval.char_eq_exp ξ z, hdot,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- Negation permutes the frequency box and conjugates its summands, including
the fixed zero frequency. -/
theorem conj_finiteGrid (ν ℓ h : ℝ) (m : ℕ) (x y : E d) :
    conj (finiteGrid ν ℓ h m x y) = finiteGrid ν ℓ h m x y := by
  unfold finiteGrid
  rw [map_sum]
  apply Finset.sum_equiv (Equiv.neg (Z d)) (fun j => (neg_mem_indexBox m j).symm)
  intro j _
  simp only [Equiv.neg_apply, coefficient_neg, physicalFeature, UnitAddTorus.mFourier_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_conj]

/-- The Bochner integral is fixed by conjugation after the substitution `ξ ↦ -ξ`. -/
theorem conj_kernel (ν ℓ : ℝ) (z : E d) : conj (kernel ν ℓ z) = kernel ν ℓ z := by
  let F (ξ : E d) := (spectralDensity ν ℓ ξ : ℂ) * conj (DesignParseval.char ξ z)
  have href (ξ : E d) : conj (F ξ) = F (-ξ) := by
    simp only [F, spectralDensity_neg, char_neg_freq, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]
  change conj (∫ ξ, F ξ) = ∫ ξ, F ξ
  rw [← integral_conj]
  calc
    _ = ∫ ξ, F (-ξ) := integral_congr_ae (ae_of_all _ href)
    _ = _ := integral_neg_eq_self F volume

theorem finiteGrid_im (ν ℓ h : ℝ) (m : ℕ) (x y : E d) : (finiteGrid ν ℓ h m x y).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_finiteGrid ν ℓ h m x y)

theorem kernel_im (ν ℓ : ℝ) (z : E d) : (kernel ν ℓ z).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_kernel ν ℓ z)

/-- For positive smoothness and length scale, the real kernel entry is the
ordinary cosine integral with frequencies in cycles per unit length. -/
theorem kernel_re_eq_cosineIntegral {ν ℓ : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (z : E d) :
    (kernel ν ℓ z).re =
      ∫ ξ : E d, spectralDensity ν ℓ ξ * Real.cos (2 * Real.pi * ∑ i, ξ i * z i) := by
  refine (integral_re (SpectralNormalization.integrable_inverseFourier hν hℓ z)).symm.trans ?_
  apply integral_congr_ae
  refine ae_of_all _ fun ξ => ?_
  change ((spectralDensity ν ℓ ξ : ℂ) * conj (DesignParseval.char ξ z)).re = _
  rw [Complex.re_ofReal_mul, Complex.conj_re, DesignParseval.char_eq_exp, Complex.exp_ofReal_mul_I_re,
    neg_mul, Real.cos_neg]

theorem error_im (ν ℓ h : ℝ) (m : ℕ) (x y : E d) :
    (finiteGrid ν ℓ h m x y - kernel ν ℓ (x - y)).im = 0 := by
  rw [Complex.sub_im, finiteGrid_im, kernel_im, sub_self]

theorem error_eq_ofReal (ν ℓ h : ℝ) (m : ℕ) (x y : E d) :
    finiteGrid ν ℓ h m x y - kernel ν ℓ (x - y) =
      (((finiteGrid ν ℓ h m x y).re - (kernel ν ℓ (x - y)).re : ℝ) : ℂ) := by
  rw [Complex.ofReal_sub, Complex.conj_eq_iff_re.mp (conj_finiteGrid ν ℓ h m x y),
    Complex.conj_eq_iff_re.mp (conj_kernel ν ℓ (x - y))]

theorem norm_error_eq_abs_re_sub_re (ν ℓ h : ℝ) (m : ℕ) (x y : E d) :
    ‖finiteGrid ν ℓ h m x y - kernel ν ℓ (x - y)‖ =
      |(finiteGrid ν ℓ h m x y).re - (kernel ν ℓ (x - y)).re| := by
  rw [error_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]

/-- The project's complex Frobenius norm equals the usual real Frobenius
formula for every finite configuration of sample locations. -/
theorem frobeniusNorm_error_eq_real {N : ℕ} (ν ℓ h : ℝ) (m : ℕ) (X : Fin N → E d) :
    AliasTransfer.frobeniusNorm (fun i j =>
      finiteGrid ν ℓ h m (X i) (X j) - kernel ν ℓ (X i - X j)) =
      Real.sqrt (∑ i, ∑ j, ((finiteGrid ν ℓ h m (X i) (X j)).re -
        (kernel ν ℓ (X i - X j)).re) ^ 2) := by
  rw [AliasTransfer.frobeniusNorm_eq_sqrt]
  simp only [norm_error_eq_abs_re_sub_re, sq_abs]

end MaternAudit.RealCovariance
