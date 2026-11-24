import MaternAudit.MaternParameters
import MaternAudit.MaternProfile
import MaternAudit.DesignParseval
import MaternAudit.PairSpectrum

/-!
# Physical Matérn covariance and its equispaced Fourier grids

Frequencies are in cycles per unit length. The inverse transform uses the
conjugate of the negative-exponent character used for design densities.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace MaternAudit.PhysicalKernel

open MaternParameters MaternProfile MovingCells PairSpectrum
variable {d : ℕ}

/-- Inverse Fourier integral of the unit-variance Matérn spectral density. -/
def kernel (ν ℓ : ℝ) (z : Fin d → ℝ) : ℂ :=
  ∫ ξ, (spectralDensity ν ℓ ξ : ℂ) * conj (DesignParseval.char ξ z)

/-- Full cubical set of retained integer frequencies, including both endpoints. -/
def indexBox (d m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(m : ℤ)) (m : ℤ)

theorem mem_indexBox (m : ℕ) (j : Fin d → ℤ) :
    j ∈ indexBox d m ↔ ‖lattice j‖ ≤ (m : ℝ) := by
  rw [indexBox, Fintype.mem_piFinset, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg m)]
  apply forall_congr' fun i => ?_
  rw [Finset.mem_Icc]
  change _ ↔ ‖(j i : ℝ)‖ ≤ (m : ℝ)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor
  all_goals first | exact_mod_cast hl | exact_mod_cast hu

/-- The trapezoidal weight of a single physical lattice frequency. -/
def coefficient (ν ℓ h : ℝ) (j : Fin d → ℤ) : ℝ :=
  h ^ d * spectralDensity ν ℓ (h • lattice j)

/-- The literal finite Fourier approximation at two sample locations. -/
def finiteGrid (ν ℓ h : ℝ) (m : ℕ) (x y : Fin d → ℝ) : ℂ :=
  ∑ j ∈ indexBox d m, (coefficient ν ℓ h j : ℂ) *
    (physicalFeature h j x * conj (physicalFeature h j y))

/-- The full equispaced Fourier series before truncation. -/
def infiniteGrid (ν ℓ h : ℝ) (x y : Fin d → ℝ) : ℂ :=
  FixedGridLaw.gramKernel (coefficient ν ℓ h) (physicalFeature h) x y

/-- Difference between the complete Fourier grid and the original continuous kernel. -/
def «alias» (ν ℓ h : ℝ) (x y : Fin d → ℝ) : ℂ :=
  infiniteGrid ν ℓ h x y - kernel ν ℓ (x - y)

/-- Measurability of the inverse transform as a function of its lag. The
parameter-integral theorem only requires joint measurability here. -/
theorem measurable_kernel (ν ℓ : ℝ) : Measurable (kernel (d := d) ν ℓ) := by
  have hs : Measurable (spectralDensity (d := d) ν ℓ) :=
    measurable_const.mul ((continuous_radiusSq.measurable.add measurable_const).pow measurable_const)
  have hc : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => DesignParseval.char p.2 p.1) := by
    simp_rw [DesignParseval.char_eq_exp]
    fun_prop
  have hm : StronglyMeasurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (spectralDensity ν ℓ p.2 : ℂ) * conj (DesignParseval.char p.2 p.1)) :=
    ((Complex.continuous_ofReal.measurable.comp (hs.comp measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp hc)).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem measurable_finiteGrid (ν ℓ h : ℝ) (m : ℕ) :
    Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => finiteGrid ν ℓ h m p.1 p.2 := by
  unfold finiteGrid
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (((continuous_physicalFeature h j).measurable.comp measurable_fst).mul
    (Complex.continuous_conj.measurable.comp ((continuous_physicalFeature h j).measurable.comp measurable_snd)))

/-- Joint measurability of the literal finite-grid error on pairs of locations. -/
theorem measurable_error (ν ℓ h : ℝ) (m : ℕ) :
    Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) =>
      finiteGrid ν ℓ h m z.1 z.2 - kernel ν ℓ (z.1 - z.2) :=
  (measurable_finiteGrid ν ℓ h m).sub ((measurable_kernel ν ℓ).comp (measurable_fst.sub measurable_snd))

/-- The omitted real coefficients equal the full weights on the complement of the finite box. -/
theorem omitted_eq_ite (ν ℓ h : ℝ) (m : ℕ) (j : Fin d → ℤ) :
    omitted ν ℓ h m j = if j ∈ indexBox d m then 0 else coefficient ν ℓ h j := by
  by_cases hj : j ∈ indexBox d m
  · simp [omitted, hj, not_lt.mpr ((mem_indexBox m j).mp hj)]
  · have hlt : (m : ℝ) < ‖lattice j‖ := lt_of_not_ge (fun hle => hj ((mem_indexBox m j).mpr hle))
    simp [omitted, coefficient, hj, hlt]

/-- Absolute summability of all grid weights. Applying the rescaling at cutoff
one suffices because the remaining central frequencies form a finite set. -/
theorem summable_coefficient {ν ℓ h : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (hh : 0 < h) :
    Summable (fun j : Fin d → ℤ => |coefficient ν ℓ h j|) := by
  have hβ : (d : ℝ) < beta d ν := by unfold beta; linarith
  have ho : Summable (omitted (d := d) ν ℓ h 1) := by
    refine ((summable_b hβ (frequencyScale ν ℓ / (h * (1 : ℕ))) 1).mul_left
      (amplitude d ν ℓ (h * (1 : ℕ)) * (((1 : ℕ) : ℝ)^d)⁻¹)).congr fun j => ?_
    exact (omitted_eq_rescaled hℓ hh (by decide : 0 < 1) j).symm
  let J := indexBox d 1
  have hf : Summable (fun j => if j ∈ J then coefficient ν ℓ h j else 0) :=
    summable_of_ne_finset_zero (s := J) fun j hj => if_neg hj
  apply Summable.abs
  refine (hf.add ho).congr fun j => ?_
  rw [omitted_eq_ite]
  by_cases hj : j ∈ J <;> simp [J] at hj ⊢ <;> simp [hj]

/-- The two sampled characters are exactly the positive phase at lag `x - y`. -/
theorem feature_product_eq_char (h : ℝ) (j : Fin d → ℤ) (x y : Fin d → ℝ) :
    physicalFeature h j x * conj (physicalFeature h j y) =
      conj (DesignParseval.char (h • lattice j) (x - y)) := by
  have hp : DesignParseval.torusPoint h x - DesignParseval.torusPoint h y =
      DesignParseval.torusPoint h (x-y) := by
    funext i
    change ((h*x i : ℝ) : UnitAddCircle) - ((h*y i : ℝ) : UnitAddCircle) =
      ((h*(x i - y i) : ℝ) : UnitAddCircle)
    rw [mul_sub, AddCircle.coe_sub]
  have hf : DesignParseval.sampleFreq h (0 : Fin d → ℝ) j = h • lattice j := by
    funext i
    simp [DesignParseval.sampleFreq, lattice]
  change UnitAddTorus.mFourier j (DesignParseval.torusPoint h x) *
    conj (UnitAddTorus.mFourier j (DesignParseval.torusPoint h y)) = _
  rw [← FixedFourier.mFourier_apply_sub, hp,
    ← hf, ← DesignParseval.mFourier_neg_torusPoint, UnitAddTorus.mFourier_neg, Complex.conj_conj]

/-- Absolute convergence of the complex grid at any pair of physical locations. -/
theorem summable_grid_terms {ν ℓ h : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (hh : 0 < h)
    (x y : Fin d → ℝ) : Summable fun j => (coefficient ν ℓ h j : ℂ) *
      (physicalFeature h j x * conj (physicalFeature h j y)) := by
  apply (summable_coefficient hν hℓ hh).of_norm_bounded
  intro j
  simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_physicalFeature]

/-- Exact deterministic split of the infinite grid into the finite grid and the
omitted Gram kernel. The identity holds for every cutoff, including zero. -/
theorem infiniteGrid_eq_finiteGrid_add_tail {ν ℓ h : ℝ} (hν : 0 < ν)
    (hℓ : 0 < ℓ) (hh : 0 < h) (m : ℕ) (x y : Fin d → ℝ) :
    infiniteGrid ν ℓ h x y = finiteGrid ν ℓ h m x y +
      FixedGridLaw.gramKernel (omitted ν ℓ h m) (physicalFeature h) x y := by
  let J := indexBox d m
  let f (j : Fin d → ℤ) := (coefficient ν ℓ h j : ℂ) *
    (physicalFeature h j x * conj (physicalFeature h j y))
  have hs : Summable f := summable_grid_terms hν hℓ hh x y
  calc
    _ = (∑ j ∈ J, f j) + ∑' j : ↑((J : Set (Fin d → ℤ))ᶜ), f j :=
      (hs.sum_add_tsum_compl (s := J)).symm
    _ = _ := by
      rw [tsum_subtype, FixedGridLaw.gramKernel]
      apply congrArg ((∑ j ∈ J, f j) + ·)
      apply tsum_congr
      intro j
      rw [omitted_eq_ite]
      by_cases hj : j ∈ J
      · simp [Set.indicator, J, f] at hj ⊢; simp [hj]
      · simp [Set.indicator, J, f] at hj ⊢; simp [hj]

/-- Signed full error in the orientation `finite − exact = alias − truncation`. -/
theorem finiteGrid_sub_kernel {ν ℓ h : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (hh : 0 < h)
    (m : ℕ) (x y : Fin d → ℝ) :
    finiteGrid ν ℓ h m x y - kernel ν ℓ (x-y) = «alias» ν ℓ h x y -
      FixedGridLaw.gramKernel (omitted ν ℓ h m) (physicalFeature h) x y := by
  rw [«alias», infiniteGrid_eq_finiteGrid_add_tail hν hℓ hh]
  abel

/-- Explicit uniform aliasing hypothesis on pairs of points in the design cube. -/
def AliasBound (d : ℕ) (ν ℓ h η : ℝ) : Prop :=
  ∀ x ∈ DesignParseval.unitCube d, ∀ y ∈ DesignParseval.unitCube d, ‖«alias» ν ℓ h x y‖ ≤ η

theorem abs_entry_norm_sub_tail_le {ν ℓ h η : ℝ} (hν : 0 < ν) (hℓ : 0 < ℓ) (hh : 0 < h)
    (hη : AliasBound d ν ℓ h η) (m : ℕ) {x y : Fin d → ℝ}
    (hx : x ∈ DesignParseval.unitCube d) (hy : y ∈ DesignParseval.unitCube d) :
    |‖finiteGrid ν ℓ h m x y - kernel ν ℓ (x-y)‖ -
      ‖FixedGridLaw.gramKernel (omitted ν ℓ h m) (physicalFeature h) x y‖| ≤ η := by
  let T := FixedGridLaw.gramKernel (omitted ν ℓ h m) (physicalFeature h) x y
  rw [finiteGrid_sub_kernel hν hℓ hh]
  exact (by simpa only [norm_neg, sub_neg_eq_add, sub_add_cancel] using
    abs_norm_sub_norm_le («alias» ν ℓ h x y - T) (-T) :
      |‖«alias» ν ℓ h x y - T‖ - ‖T‖| ≤ ‖«alias» ν ℓ h x y‖).trans (hη x hx y hy)

end MaternAudit.PhysicalKernel
