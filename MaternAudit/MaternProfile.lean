import MaternAudit.MaternProfileBounds
import MaternAudit.MovingCells

/-!
# Growing-grid Matérn spectral mass and autocorrelation

The coefficients are sampled at `j / m` in Euclidean frequency coordinates
outside the sup-norm unit cube. A lattice shift may vary with the row.
When its displacement `r / m` tends to zero, the two sampled profiles converge
to the same value almost everywhere. Their product is dominated by the same
integrable majorant as the unshifted profile.
-/

noncomputable section

namespace MaternAudit.MaternProfile

open Filter MeasureTheory
open scoped Topology

variable {d : ℕ}

/-- The rescaled Matérn coefficient at the actual grid point `j / m`. -/
def b (β t : ℝ) (m : ℕ) (j : Z d) : ℝ := profile β t (MovingCells.gridPoint m j)

theorem b_nonneg (β t : ℝ) (m : ℕ) (j : Z d) : 0 ≤ b β t m j := profile_nonneg _ _ _

theorem b_le_one {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) (m : ℕ) (j : Z d) : b β t m j ≤ 1 :=
  profile_le_one hβ t _

@[simp] theorem b_zero_mesh (β t : ℝ) (j : Z d) : b β t 0 j = 0 := by
  have hz : MovingCells.gridPoint 0 j = (0 : E d) := by
    funext i
    simp [MovingCells.gridPoint]
  simp [b, hz, profile]

private theorem measurable_step (m : ℕ) (f : Z d → ℝ) :
    Measurable (fun x : E d => f (MovingCells.cellIndex m x)) :=
  (measurable_of_countable f).comp (MovingCells.measurable_cellIndex m)

private theorem b_step_le {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) {m : ℕ} (hm : 0 < m) (x : E d) :
    b β t m (MovingCells.cellIndex m x) ≤ majorant β x := by
  apply profile_le_majorant hβ
  rw [norm_sub_rev]
  apply (MovingCells.norm_gridPoint_cellIndex_sub_le hm x).trans
  exact (div_le_one (Nat.cast_pos.mpr hm : 0 < (m : ℝ))).mpr (by exact_mod_cast hm)

private theorem integrable_step_of_bound {β : ℝ} (hβ : (d : ℝ) < β) (m : ℕ) (f : Z d → ℝ)
    (hf : ∀ x : E d, ‖f (MovingCells.cellIndex m x)‖ ≤ majorant β x) :
    Integrable (fun x : E d => f (MovingCells.cellIndex m x)) :=
  (integrable_majorant hβ).mono' (measurable_step m f).aestronglyMeasurable (ae_of_all _ hf)

theorem summable_b {β : ℝ} (hβ : (d : ℝ) < β) (t : ℝ) (m : ℕ) :
    Summable (b (d := d) β t m) := by
  cases m with
  | zero => simpa only [show b (d := d) β t 0 = fun _ => 0 from funext (b_zero_mesh β t)]
              using (summable_zero : Summable (fun _ : Z d => (0 : ℝ)))
  | succ k =>
    apply MovingCells.summable_of_integrable_cellIndex (Nat.succ_pos k)
    apply integrable_step_of_bound hβ
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (b_nonneg _ _ _ _)]
    exact b_step_le ((Nat.cast_nonneg _).trans hβ.le) _ (Nat.succ_pos k) x

theorem summable_b_mul_shift {β : ℝ} (hβ : (d : ℝ) < β) (t : ℝ) (m : ℕ) (r : Z d) :
    Summable (fun j : Z d => b β t m j * b β t m (j + r)) :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (b_nonneg β t m j) (b_nonneg β t m (j + r)))
    (fun j => mul_le_of_le_one_right (b_nonneg _ _ _ _)
      (b_le_one ((Nat.cast_nonneg _).trans hβ.le) t m (j + r))) (summable_b hβ t m)

theorem summable_b_sq {β : ℝ} (hβ : (d : ℝ) < β) (t : ℝ) (m : ℕ) :
    Summable (fun j : Z d => b β t m j ^ 2) := by
  simpa only [add_zero, sq] using summable_b_mul_shift hβ t m (0 : Z d)

private theorem tendsto_cell_point {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) (x : E d) :
    Tendsto (fun n => MovingCells.gridPoint (m n) (MovingCells.cellIndex (m n) x)) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    ((hm.eventually_gt_atTop 0).mono fun n hn => MovingCells.norm_gridPoint_cellIndex_sub_le hn x)
    (tendsto_one_div_atTop_nhds_zero_nat.comp hm)

/-- Dominated convergence on the actual lattice cells, followed by the exact cell integral identity. -/
private theorem tendsto_cell_sums {β : ℝ} (hβ : (d : ℝ) < β) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (f : ℕ → Z d → ℝ) {g : E d → ℝ}
    (hb : ∀ n, 0 < m n → ∀ x : E d, ‖f n (MovingCells.cellIndex (m n) x)‖ ≤ majorant β x)
    (hg : ∀ᵐ x : E d, Tendsto (fun n => f n (MovingCells.cellIndex (m n) x)) atTop (𝓝 (g x))) :
    Tendsto (fun n => (∑' j, f n j) / (m n : ℝ) ^ d) atTop (𝓝 (∫ x, g x)) := by
  have hp := hm.eventually_gt_atTop 0
  have h := tendsto_integral_filter_of_dominated_convergence (majorant β)
    (Eventually.of_forall fun n => (measurable_step (m n) (f n)).aestronglyMeasurable)
    (hp.mono fun n hn => ae_of_all _ (hb n hn)) (integrable_majorant hβ) hg
  refine h.congr' (hp.mono fun n hn => ?_)
  rw [MovingCells.integral_cellIndex hn (integrable_step_of_bound hβ (m n) (f n) (hb n hn))]
  ring

/-- The normalized lattice mass converges to the first profile integral. -/
theorem tendsto_mass {β : ℝ} (hβ : (d : ℝ) < β) {m : ℕ → ℕ} {t : ℕ → ℝ}
    (hm : Tendsto m atTop atTop) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (∑' j : Z d, b β (t n) (m n) j) / (m n : ℝ) ^ d)
      atTop (𝓝 (I1 d β)) := by
  apply tendsto_cell_sums hβ hm (fun n => b β (t n) (m n))
  · intro n hn x
    rw [Real.norm_eq_abs, abs_of_nonneg (b_nonneg _ _ _ _)]
    exact b_step_le ((Nat.cast_nonneg _).trans hβ.le) _ hn x
  · filter_upwards [ae_norm_ne_one (d := d)] with x hx
    exact tendsto_profile β (tendsto_cell_point hm x) ht hx

/-- Autocorrelation at any lattice shifts whose physical displacements tend to zero. -/
theorem tendsto_shifted_energy {β : ℝ} (hβ : (d : ℝ) < β) {m : ℕ → ℕ} {t : ℕ → ℝ}
    {r : ℕ → Z d} (hm : Tendsto m atTop atTop) (ht : Tendsto t atTop (𝓝 0))
    (hr : Tendsto (fun n => MovingCells.gridPoint (m n) (r n)) atTop (𝓝 0)) :
    Tendsto (fun n => (∑' j : Z d, b β (t n) (m n) j * b β (t n) (m n) (j + r n)) /
      (m n : ℝ) ^ d) atTop (𝓝 (I2 d β)) := by
  have hβ' : 0 ≤ β := (Nat.cast_nonneg d).trans hβ.le
  apply tendsto_cell_sums hβ hm (fun n j => b β (t n) (m n) j * b β (t n) (m n) (j + r n))
  · intro n hn x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (b_nonneg _ _ _ _) (b_nonneg _ _ _ _))]
    exact (mul_le_of_le_one_right (b_nonneg _ _ _ _) (b_le_one hβ' _ _ _)).trans (b_step_le hβ' _ hn x)
  · filter_upwards [ae_norm_ne_one (d := d)] with x hx
    have hu := tendsto_cell_point hm x
    have hv : Tendsto (fun n => MovingCells.gridPoint (m n) (MovingCells.cellIndex (m n) x + r n))
        atTop (𝓝 x) := by
      simpa only [MovingCells.gridPoint_add, add_zero] using hu.add hr
    simpa only [b, sq] using (tendsto_profile β hu ht hx).mul (tendsto_profile β hv ht hx)

/-- The zero-shift case is the unshifted energy limit. -/
theorem tendsto_energy {β : ℝ} (hβ : (d : ℝ) < β) {m : ℕ → ℕ} {t : ℕ → ℝ}
    (hm : Tendsto m atTop atTop) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (∑' j : Z d, b β (t n) (m n) j ^ 2) / (m n : ℝ) ^ d)
      atTop (𝓝 (I2 d β)) := by
  have hz (k : ℕ) : MovingCells.gridPoint k (0 : Z d) = 0 := by
    funext i
    simp [MovingCells.gridPoint]
  have hr : Tendsto (fun n => MovingCells.gridPoint (m n) (0 : Z d)) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds (x := (0 : E d)) (f := (atTop : Filter ℕ)))
  simpa only [add_zero, sq] using (tendsto_shifted_energy (r := fun _ => 0) hβ hm ht hr)

end MaternAudit.MaternProfile
