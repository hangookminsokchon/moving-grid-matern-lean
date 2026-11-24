import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounds and almost-everywhere continuity for the rescaled Matérn spectral tail. -/

noncomputable section

namespace MaternAudit.MaternProfile

open Filter MeasureTheory
open scoped Topology

abbrev E (d : ℕ) := Fin d → ℝ
abbrev Z (d : ℕ) := Fin d → ℤ

variable {d : ℕ}

/-- Squared Euclidean norm, with coordinates in the ambient sup-norm space. -/
def radiusSq (x : E d) : ℝ := ∑ i, x i ^ 2

/-- The max-norm cutoff is the exterior of the closed unit cube. -/
def profile (β t : ℝ) (x : E d) : ℝ :=
  if 1 < ‖x‖ then (radiusSq x + t ^ 2) ^ (-β / 2 : ℝ) else 0

def I1 (d : ℕ) (β : ℝ) : ℝ := ∫ x : E d, profile β 0 x

def I2 (d : ℕ) (β : ℝ) : ℝ := ∫ x : E d, profile β 0 x ^ 2

theorem radiusSq_nonneg (x : E d) : 0 ≤ radiusSq x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_le_radiusSq (x : E d) : ‖x‖ ^ 2 ≤ radiusSq x := by
  have hn : ‖x‖ ≤ Real.sqrt (radiusSq x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => x k ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i))
  simpa only [Real.sq_sqrt (radiusSq_nonneg x)] using pow_le_pow_left₀ (norm_nonneg _) hn 2

theorem continuous_radiusSq : Continuous (radiusSq (d := d)) := by unfold radiusSq; fun_prop

theorem measurable_profile (β t : ℝ) : Measurable (profile (d := d) β t) := by
  unfold profile
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    ((continuous_radiusSq.measurable.add measurable_const).pow measurable_const) measurable_const

theorem profile_nonneg (β t : ℝ) (x : E d) : 0 ≤ profile β t x := by
  unfold profile
  split
  · exact Real.rpow_nonneg (add_nonneg (radiusSq_nonneg _) (sq_nonneg _)) _
  · exact le_rfl

theorem profile_pos {β t : ℝ} {x : E d} (hx : 1 < ‖x‖) : 0 < profile β t x := by
  rw [profile, if_pos hx]
  apply Real.rpow_pos_of_pos
  exact add_pos_of_pos_of_nonneg
    ((sq_pos_of_pos (zero_lt_one.trans hx)).trans_le (norm_sq_le_radiusSq x)) (sq_nonneg _)

theorem profile_le_one {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) (x : E d) : profile β t x ≤ 1 := by
  unfold profile
  split
  next hx =>
    apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
    exact ((one_le_pow₀ hx.le).trans (norm_sq_le_radiusSq x)).trans (le_add_of_nonneg_right (sq_nonneg _))
  next => exact zero_le_one

/-- A common integrable bound for profile samples within one sup-norm unit of `x`. -/
def majorant (β : ℝ) (x : E d) : ℝ := (1 + ‖x‖) ^ (-β) / (3 : ℝ) ^ (-β)

theorem integrable_majorant {β : ℝ} (hβ : (d : ℝ) < β) : Integrable (majorant (d := d) β) := by
  have hr : (Module.finrank ℝ (E d) : ℝ) < β := by simpa [E] using hβ
  exact (integrable_one_add_norm (μ := volume) hr).div_const _

theorem profile_le_majorant {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) {x y : E d}
    (hxy : ‖x - y‖ ≤ 1) : profile β t y ≤ majorant β x := by
  by_cases hy : 1 < ‖y‖
  · have ht : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      calc
        ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have hbase : 0 < (1 + ‖x‖) / 3 := by positivity
    have hcomp : (1 + ‖x‖) / 3 ≤ ‖y‖ := by linarith only [ht, hxy, hy]
    have hsq := (pow_le_pow_left₀ hbase.le hcomp 2).trans (norm_sq_le_radiusSq y)
    rw [profile, if_pos hy]
    calc
      _ ≤ (((1 + ‖x‖) / 3) ^ 2) ^ (-β / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hbase)
          (hsq.trans (le_add_of_nonneg_right (sq_nonneg t))) (by linarith)
      _ = ((1 + ‖x‖) / 3) ^ (-β) := by
        rw [← Real.rpow_natCast_mul hbase.le]
        congr 1
        norm_num
        ring
      _ = majorant β x := Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 3) _
  · rw [profile, if_neg hy, majorant]
    positivity

theorem integrable_profile {β : ℝ} (hβ : (d : ℝ) < β) (t : ℝ) :
    Integrable (profile (d := d) β t) := by
  apply (integrable_majorant hβ).mono' (measurable_profile β t).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (profile_nonneg _ _ _)]
  exact profile_le_majorant ((Nat.cast_nonneg _).trans hβ.le) t (by simp)

theorem integrable_profile_sq {β : ℝ} (hβ : (d : ℝ) < β) (t : ℝ) :
    Integrable (fun x : E d => profile β t x ^ 2) := by
  apply (integrable_profile hβ t).mono' ((measurable_profile β t).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_of_le_one_right (profile_nonneg _ _ _) (profile_le_one ((Nat.cast_nonneg _).trans hβ.le) _ _)

/-- Sequences may approach through either side of the cutoff. Off the unit sphere the
cutoff is eventually constant. -/
theorem tendsto_profile {ι : Type*} {l : Filter ι} {u : ι → E d} {t : ι → ℝ} {x : E d}
    (β : ℝ) (hu : Tendsto u l (𝓝 x)) (ht : Tendsto t l (𝓝 0)) (hx : ‖x‖ ≠ 1) :
    Tendsto (fun n => profile β (t n) (u n)) l (𝓝 (profile β 0 x)) := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [profile, if_neg h.asymm]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hu.norm.eventually (gt_mem_nhds h)] with n hn
    simp [profile, not_lt_of_ge hn.le]
  · have ha : 0 < radiusSq x := (sq_pos_of_pos (zero_lt_one.trans h)).trans_le (norm_sq_le_radiusSq x)
    have hb := (continuous_radiusSq.tendsto x).comp hu
    have hs : Tendsto (fun n => radiusSq (u n) + t n ^ 2) l (𝓝 (radiusSq x + 0 ^ 2)) :=
      hb.add (ht.pow 2)
    rw [profile, if_pos h]
    refine (hs.rpow_const (Or.inl (by simpa using ha.ne'))).congr' ?_
    filter_upwards [hu.norm.eventually (lt_mem_nhds h)] with n hn
    simp [profile, hn]

theorem ae_norm_ne_one : ∀ᵐ x : E d, ‖x‖ ≠ 1 := by
  rw [ae_iff]
  simpa [Metric.sphere, dist_zero_right] using
    (Measure.addHaar_sphere_of_ne_zero (volume : Measure (E d)) 0 (one_ne_zero : (1 : ℝ) ≠ 0))

private theorem exterior_positive_volume (hd : 0 < d) :
    0 < volume {x : E d | 1 < ‖x‖} := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply (isOpen_lt continuous_const continuous_norm).measure_pos volume
  refine ⟨fun _ => 2, ?_⟩
  change 1 < ‖fun _ : Fin d => (2 : ℝ)‖
  rw [pi_norm_const, Real.norm_eq_abs]
  norm_num

theorem I1_pos {β : ℝ} (hd : 0 < d) (hβ : (d : ℝ) < β) : 0 < I1 d β := by
  apply (integral_pos_iff_support_of_nonneg (fun x => profile_nonneg β 0 x) (integrable_profile hβ 0)).mpr
  exact (exterior_positive_volume hd).trans_le (measure_mono fun x hx => (profile_pos hx).ne')

theorem I2_pos {β : ℝ} (hd : 0 < d) (hβ : (d : ℝ) < β) : 0 < I2 d β := by
  apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (profile β 0 x)) (integrable_profile_sq hβ 0)).mpr
  exact (exterior_positive_volume hd).trans_le (measure_mono fun x hx => (sq_pos_of_pos (profile_pos hx)).ne')

end MaternAudit.MaternProfile
