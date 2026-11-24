import MaternAudit.FixedFourier
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Modulated lattice Parseval for a spatial density on the unit cube -/

noncomputable section

open Filter MeasureTheory Set UnitAddTorus
open scoped Topology ENNReal NNReal

namespace MaternAudit.DesignParseval

abbrev E (d : ℕ) := Fin d → ℝ

def unitCube (d : ℕ) : Set (E d) := univ.pi fun _ ↦ Ico 0 1

variable {d : ℕ}

private def phase (s : ℝ) : ℂ := Complex.exp ((-(2 * Real.pi) * s : ℝ) * Complex.I)

/-- Negative-exponent Fourier character in cycles per unit length. -/
def char (ξ x : E d) : ℂ := phase (∑ i, ξ i * x i)

def FT (ρ : E d → ℝ) (ξ : E d) : ℂ := ∫ x, char ξ x * (ρ x : ℂ)

def sampleFreq (H : ℝ) (α : E d) (j : Fin d → ℤ) : E d := fun i ↦ H * (j i : ℝ) + α i

theorem char_eq_exp (ξ x : E d) :
    char ξ x = Complex.exp ((-(2 * Real.pi) * (∑ i, ξ i * x i) : ℝ) * Complex.I) := rfl

@[simp] theorem norm_char (ξ x : E d) : ‖char ξ x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem continuous_char_right (ξ : E d) : Continuous (char ξ) := by
  unfold char phase
  fun_prop

theorem continuous_char_left (x : E d) : Continuous fun ξ ↦ char ξ x := by
  unfold char phase
  fun_prop

theorem continuous_FT {ρ : E d → ℝ} (hρ : Integrable ρ) : Continuous (FT ρ) := by
  apply continuous_of_dominated (bound := fun x ↦ ‖ρ x‖)
  · exact fun ξ ↦ (continuous_char_right ξ).aestronglyMeasurable.mul hρ.ofReal.aestronglyMeasurable
  · exact fun ξ ↦ ae_of_all _ fun x ↦ by simp only [norm_mul, norm_char, one_mul, Complex.norm_real, le_refl]
  · exact hρ.norm
  · exact ae_of_all _ fun x ↦ (continuous_char_left x).mul continuous_const

private theorem phase_add (s t : ℝ) : phase (s+t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    phase (∑ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | insert i s hi ih => simp [hi, phase_add, ih]

attribute [local instance] Real.fact_zero_lt_one

abbrev torusHaar (d : ℕ) := FixedFourier.normalizedHaar (Fin d)

/-- Spatial design mapped to the torus of unit periods, coordinate by coordinate. -/
def wrap (x : E d) : UnitAddTorus (Fin d) := fun i ↦ (x i : UnitAddCircle)

def torusPoint (H : ℝ) (x : E d) : UnitAddTorus (Fin d) := wrap (H • x)

private def reprPoint (t : UnitAddTorus (Fin d)) : E d :=
  fun i ↦ ((AddCircle.measurableEquivIco 1 0 (t i)).val : ℝ)

theorem measurableSet_unitCube : MeasurableSet (unitCube d) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

theorem measurable_wrap : Measurable (wrap (d := d)) :=
  measurable_pi_lambda _ fun i ↦ AddCircle.measurable_mk'.comp (measurable_pi_apply i)

private theorem measurable_reprPoint : Measurable (reprPoint (d := d)) :=
  measurable_pi_lambda _ fun i ↦ measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco 1 0).measurable.comp (measurable_pi_apply i))

private theorem reprPoint_wrap {x : E d} (hx : x ∈ unitCube d) : reprPoint (wrap x) = x := by
  funext i
  exact congrArg Subtype.val ((AddCircle.measurableEquivIco 1 0).apply_symm_apply
    ⟨x i, by simpa only [zero_add] using hx i (mem_univ i)⟩)

private theorem wrap_reprPoint (t : UnitAddTorus (Fin d)) : wrap (reprPoint t) = t := by
  funext i
  exact (AddCircle.measurableEquivIco 1 0).symm_apply_apply (t i)

theorem measurePreserving_wrap :
    MeasurePreserving (wrap (d := d)) (volume.restrict (unitCube d)) (torusHaar d) := by
  have h1 : MeasurePreserving ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ico 0 1))
      AddCircle.haarAddCircle := by
    have h := UnitAddCircle.measurePreserving_mk 0
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul, zero_add] at h
    rwa [restrict_Ico_eq_restrict_Ioc]
  change MeasurePreserving _ ((Measure.pi (fun _ : Fin d ↦ (volume : Measure ℝ))).restrict
    (univ.pi (fun _ ↦ Ico 0 1))) _
  rw [Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ (fun _ ↦ h1)

private theorem measurePreserving_reprPoint :
    MeasurePreserving (reprPoint (d := d)) (torusHaar d) (volume.restrict (unitCube d)) := by
  refine ⟨measurable_reprPoint, ?_⟩
  rw [← measurePreserving_wrap.map_eq, Measure.map_map measurable_reprPoint measurable_wrap]
  have he : reprPoint ∘ wrap =ᵐ[volume.restrict (unitCube d)] id :=
    (ae_restrict_mem measurableSet_unitCube).mono fun _ hx ↦ reprPoint_wrap hx
  rw [Measure.map_congr he, Measure.map_id]

private theorem measurableEmbedding_reprPoint : MeasurableEmbedding (reprPoint (d := d)) := by
  refine MeasurableEmbedding.of_measurable_inverse measurable_reprPoint ?_ measurable_wrap wrap_reprPoint
  have hr : range (reprPoint (d := d)) = unitCube d := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩ i _
      simpa only [zero_add] using (AddCircle.measurableEquivIco 1 0 (t i)).property
    · exact fun hx ↦ ⟨wrap x, reprPoint_wrap hx⟩
  rw [hr]
  exact measurableSet_unitCube

theorem mFourier_neg_wrap (j : Fin d → ℤ) (x : E d) :
    mFourier (-j) (wrap x) = char (fun i ↦ (j i : ℝ)) x := by
  rw [char, phase_sum]
  change (∏ i, fourier (-(j i)) (x i : UnitAddCircle)) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [fourier_coe_apply]
  unfold phase
  congr 1
  push_cast
  ring

private theorem mode_modulation (H : ℝ) (α x : E d) (j : Fin d → ℤ) :
    mFourier (-j) (torusPoint H x) * char α x = char (sampleFreq H α j) x := by
  rw [torusPoint, mFourier_neg_wrap]
  unfold char sampleFreq
  rw [← phase_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (j i : ℝ) * (H * x i) + α i * x i = (H * (j i : ℝ) + α i) * x i
  ring

@[simp] theorem char_zero_left (x : E d) : char 0 x = 1 := by simp [char, phase]

theorem mFourier_neg_torusPoint (H : ℝ) (j : Fin d → ℤ) (x : E d) :
    mFourier (-j) (torusPoint H x) = char (sampleFreq H 0 j) x := by
  simpa only [char_zero_left, mul_one] using mode_modulation H 0 x j

theorem measurable_torusPoint (H : ℝ) : Measurable (torusPoint (d := d) H) :=
  measurable_wrap.comp (measurable_const_smul H)

def spatialLaw (ρ : E d → ℝ) : Measure (E d) :=
  volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)

def torusLaw (H : ℝ) (ρ : E d → ℝ) : Measure (UnitAddTorus (Fin d)) :=
  (spatialLaw ρ).map (torusPoint H)

private theorem dilate_mem_cube {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) {x : E d}
    (hx : x ∈ unitCube d) : H • x ∈ unitCube d := by
  intro i _
  obtain ⟨h0, h1⟩ := hx i (mem_univ i)
  exact ⟨mul_nonneg hH.le h0, (mul_le_mul_of_nonneg_right hH1 h0).trans_lt (by simpa using h1)⟩

private theorem map_dilate {H : ℝ} (hH : 0 < H) :
    (volume : Measure (E d)).map (fun x ↦ H • x) = ENNReal.ofReal (H ^ d)⁻¹ • volume := by
  simpa only [E, Module.finrank_fin_fun, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hH.le d))] using
    Measure.map_addHaar_smul (volume : Measure (E d)) hH.ne'

private theorem map_inv_dilate {H : ℝ} (hH : 0 < H) :
    (volume : Measure (E d)).map (fun x ↦ H⁻¹ • x) = ENNReal.ofReal (H ^ d) • volume := by
  simpa only [inv_pow, inv_inv] using map_dilate (d := d) (inv_pos.mpr hH)

theorem spatialLaw_le_restrict {ρ : E d → ℝ} {L : ℝ≥0}
    (hb : ∀ᵐ x ∂volume, ρ x ≤ (L : ℝ))
    (hs : ∀ᵐ x ∂volume, x ∉ unitCube d → ρ x = 0) :
    spatialLaw ρ ≤ L • volume.restrict (unitCube d) := by
  have h : (fun x ↦ ENNReal.ofReal (ρ x)) ≤ᵐ[volume]
      (unitCube d).indicator (fun _ ↦ (L : ℝ≥0∞)) := by
    filter_upwards [hb, hs] with x hx hxs
    by_cases hxc : x ∈ unitCube d
    · simpa [hxc] using ENNReal.ofReal_le_ofReal hx
    · simp [hxc, hxs hxc]
  simpa only [spatialLaw, withDensity_indicator measurableSet_unitCube, withDensity_const] using
    withDensity_mono h

/-- The image of a cube-supported density bounded by `L` is dominated by
`L / H^d` times normalized torus Haar measure. -/
theorem torusLaw_le {ρ : E d → ℝ} {L : ℝ≥0}
    (hb : ∀ᵐ x ∂volume, ρ x ≤ (L : ℝ))
    (hs : ∀ᵐ x ∂volume, x ∉ unitCube d → ρ x = 0) {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) :
    torusLaw H ρ ≤ (L * Real.toNNReal (H ^ d)⁻¹) • torusHaar d := by
  let C := unitCube d
  let μ : Measure (E d) := (volume.restrict C).map (fun x ↦ H • x)
  have hcon : ∀ᵐ x ∂μ, x ∈ C := (ae_map_iff (measurable_const_smul H).aemeasurable
    measurableSet_unitCube).2 ((ae_restrict_mem measurableSet_unitCube).mono
      fun _ hx ↦ dilate_mem_cube hH hH1 hx)
  have hm : μ ≤ ENNReal.ofReal (H ^ d)⁻¹ • volume := by
    rw [← map_dilate hH]
    exact Measure.map_mono Measure.restrict_le_self (measurable_const_smul H)
  have hmC : μ ≤ ENNReal.ofReal (H ^ d)⁻¹ • volume.restrict C := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hcon, Measure.restrict_smul] using
      Measure.restrict_mono_measure hm C
  have hq : (volume.restrict C).map (torusPoint H) ≤ ENNReal.ofReal (H ^ d)⁻¹ • torusHaar d := by
    change (volume.restrict C).map (wrap ∘ fun x ↦ H • x) ≤ _
    rw [← Measure.map_map measurable_wrap (measurable_const_smul H)]
    exact (Measure.map_mono hmC measurable_wrap).trans_eq (by
      rw [Measure.map_smul, measurePreserving_wrap.map_eq])
  calc
    torusLaw H ρ ≤ (L • volume.restrict C).map (torusPoint H) :=
      Measure.map_mono (spatialLaw_le_restrict hb hs) (measurable_torusPoint H)
    _ = L • (volume.restrict C).map (torusPoint H) := Measure.map_smul _ _ _
    _ ≤ L • (ENNReal.ofReal (H ^ d)⁻¹ • torusHaar d) := by
      intro s
      exact mul_le_mul_left' (hq s) (L : ℝ≥0∞)
    _ = _ := by
      change L • (Real.toNNReal (H ^ d)⁻¹ • torusHaar d) = _
      rw [smul_smul]

/-- Spatial representative of a torus point on the cube of side `1/H`. -/
private def unscale (H : ℝ) (t : UnitAddTorus (Fin d)) : E d := H⁻¹ • reprPoint t

private theorem measurable_unscale (H : ℝ) : Measurable (unscale (d := d) H) :=
  (measurable_const_smul H⁻¹).comp measurable_reprPoint

private theorem torusPoint_unscale {H : ℝ} (hH : 0 < H) (t : UnitAddTorus (Fin d)) :
    torusPoint H (unscale H t) = t := by
  rw [torusPoint, unscale, smul_inv_smul₀ hH.ne', wrap_reprPoint]

/-- The Jacobian and the support restriction for both the Fourier-coefficient integral
and the squared norm integral. The half-open cube avoids choices at the faces. -/
private theorem integral_unscale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E d → V) (hs : ∀ᵐ x ∂volume, x ∉ unitCube d → f x = 0)
    {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) :
    (∫ t, f (unscale H t) ∂torusHaar d) = H ^ d • ∫ x, f x := by
  have hzero : ∀ᵐ u ∂volume, u ∉ unitCube d → f (H⁻¹ • u) = 0 := by
    filter_upwards [(Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hH.ne')).ae hs] with u hu
    intro hou
    apply hu
    intro hin
    exact hou (by simpa only [smul_inv_smul₀ hH.ne'] using dilate_mem_cube hH hH1 hin)
  calc
    _ = ∫ u in unitCube d, f (H⁻¹ • u) :=
      measurePreserving_reprPoint.integral_comp measurableEmbedding_reprPoint (fun u ↦ f (H⁻¹ • u))
    _ = ∫ u, f (H⁻¹ • u) := setIntegral_eq_integral_of_ae_compl_eq_zero hzero
    _ = ∫ x, f x ∂(volume.map (fun u : E d ↦ H⁻¹ • u)) :=
      (integral_map_equiv (Homeomorph.smul (Units.mk0 H⁻¹ (inv_ne_zero hH.ne'))).toMeasurableEquiv f).symm
    _ = _ := by rw [map_inv_dilate hH, integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg hH.le d)]

private theorem memLp_unscale {ρ : E d → ℝ} (h₂ : MemLp ρ 2 volume) {H : ℝ} (hH : 0 < H) :
    MemLp (fun t ↦ ρ (unscale H t)) 2 (torusHaar d) := by
  have hmap : MemLp ρ 2 (volume.map (fun u : E d ↦ H⁻¹ • u)) := by
    rw [map_inv_dilate hH]
    exact h₂.smul_measure ENNReal.ofReal_ne_top
  have hreal : MemLp (fun u : E d ↦ ρ (H⁻¹ • u)) 2 volume :=
    hmap.comp_of_map (measurable_const_smul H⁻¹).aemeasurable
  exact (hreal.mono_measure Measure.restrict_le_self).comp_measurePreserving measurePreserving_reprPoint

/-- Parseval for every translate of the lattice of spacing `H`. The Fourier transform
and the right-hand energy use ordinary Lebesgue measure on real space. -/
theorem sampled_parseval {ρ : E d → ℝ} (h₂ : MemLp ρ 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ unitCube d → ρ x = 0) {H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1)
    (α : E d) :
    Summable (fun j : Fin d → ℤ ↦ ‖FT ρ (sampleFreq H α j)‖ ^ 2) ∧
      H ^ d * (∑' j : Fin d → ℤ, ‖FT ρ (sampleFreq H α j)‖ ^ 2) = ∫ x, ρ x ^ 2 := by
  let g (t : UnitAddTorus (Fin d)) : ℂ := char α (unscale H t) * (ρ (unscale H t) : ℂ)
  have hρt := memLp_unscale h₂ hH
  have hg : MemLp g 2 (torusHaar d) := by
    apply hρt.congr_norm
    · exact ((continuous_char_right α).measurable.comp (measurable_unscale H)).aestronglyMeasurable.mul
        hρt.ofReal.aestronglyMeasurable
    · exact ae_of_all _ fun t ↦ by simp only [g, norm_mul, norm_char, one_mul, Complex.norm_real]
  let F := hg.toLp g
  have hrep : ∀ᵐ t ∂torusHaar d, F t = g t := hg.coeFn_toLp
  have hcoef (j : Fin d → ℤ) :
      mFourierCoeff F j = H ^ d • FT ρ (sampleFreq H α j) := by
    calc
      _ = ∫ t, char (sampleFreq H α j) (unscale H t) * (ρ (unscale H t) : ℂ) ∂torusHaar d := by
        apply integral_congr_ae
        filter_upwards [hrep] with t ht
        have hm := mode_modulation H α (unscale H t) j
        rw [torusPoint_unscale hH] at hm
        change mFourier (-j) t * F t = _
        rw [ht]
        dsimp only [g]
        rw [← mul_assoc, hm]
      _ = _ := integral_unscale (fun x ↦ char (sampleFreq H α j) x * (ρ x : ℂ))
        (hs.mono fun x hx hxc ↦ by simp [hx hxc]) hH hH1
  have henergy : (∫ t, ‖F t‖ ^ 2 ∂torusHaar d) = H ^ d * ∫ x, ρ x ^ 2 := by
    calc
      _ = ∫ t, ρ (unscale H t) ^ 2 ∂torusHaar d := by
        apply integral_congr_ae
        filter_upwards [hrep] with t ht
        simp only [ht, g, norm_mul, norm_char, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = _ := integral_unscale (fun x ↦ ρ x ^ 2) (hs.mono fun x hx hxc ↦ by simp [hx hxc]) hH hH1
  have hP : HasSum (fun j ↦ ‖mFourierCoeff F j‖ ^ 2) (∫ t, ‖F t‖ ^ 2 ∂torusHaar d) :=
    hasSum_sq_mFourierCoeff F
  have hscaled : HasSum (fun j ↦ (H ^ d) ^ 2 * ‖FT ρ (sampleFreq H α j)‖ ^ 2)
      (H ^ d * ∫ x, ρ x ^ 2) := by
    simpa only [hcoef, norm_smul, Real.norm_of_nonneg (pow_nonneg hH.le d), mul_pow, henergy] using hP
  have hne : H ^ d ≠ 0 := pow_ne_zero _ hH.ne'
  have hsum : HasSum (fun j ↦ ‖FT ρ (sampleFreq H α j)‖ ^ 2) ((∫ x, ρ x ^ 2) / H ^ d) := by
    convert hscaled.div_const ((H ^ d) ^ 2) using 1
    · funext j
      field_simp
    · field_simp
      ring
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq]
  field_simp

end MaternAudit.DesignParseval
