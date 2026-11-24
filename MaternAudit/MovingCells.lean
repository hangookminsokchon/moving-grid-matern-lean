import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Integrating a function constant on lattice cells

For a positive integer mesh parameter `m`, the fibers of `cellIndex m` are
half-open cubes of side `1/m`. Integrating a real-valued function lifted from
the lattice gives its unconditional sum times the common cube volume.
-/

namespace MaternAudit.MovingCells

open MeasureTheory Set

abbrev E (d : ℕ) := Fin d → ℝ
abbrev Z (d : ℕ) := Fin d → ℤ

variable {d m : ℕ}

def lattice (j : Z d) : E d := fun i => (j i : ℝ)

noncomputable def cellIndex (m : ℕ) (x : E d) : Z d := fun i => ⌊(m : ℝ) * x i⌋

noncomputable def gridPoint (m : ℕ) (j : Z d) : E d := fun i => (j i : ℝ) / m

theorem gridPoint_eq_smul_lattice (m : ℕ) (j : Z d) :
    gridPoint m j = (1 / (m : ℝ)) • lattice j := by
  funext i
  change (j i : ℝ) / m = (1 / (m : ℝ)) * (j i : ℝ)
  rw [div_eq_mul_inv, one_div, mul_comm]

theorem gridPoint_add (m : ℕ) (j r : Z d) :
    gridPoint m (j + r) = gridPoint m j + gridPoint m r := by
  funext i
  simp [gridPoint, add_div]

theorem cellIndex_add_gridPoint (hm : 0 < m) (x : E d) (r : Z d) :
    cellIndex m (x + gridPoint m r) = cellIndex m x + r := by
  funext i
  change ⌊(m : ℝ) * (x i + (r i : ℝ) / m)⌋ = ⌊(m : ℝ) * x i⌋ + r i
  rw [mul_add, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm.ne'), Int.floor_add_intCast]

theorem gridPoint_cellIndex_shift (hm : 0 < m) (x : E d) (r : Z d) :
    gridPoint m (cellIndex m (x + gridPoint m r)) =
      gridPoint m (cellIndex m x) + gridPoint m r := by
  rw [cellIndex_add_gridPoint hm, gridPoint_add]

theorem measurable_cellIndex (m : ℕ) : Measurable (cellIndex (d := d) m) := by
  have hf : Measurable (Int.floor : ℝ → ℤ) :=
    measurable_to_countable fun k => by
      rw [Int.preimage_floor_singleton]
      exact measurableSet_Ico
  exact measurable_pi_lambda _ fun i => hf.comp (measurable_const.mul (measurable_pi_apply i))

/-- The fiber contains the lower face of the cube and excludes the upper face in each coordinate. -/
def cell (m : ℕ) (j : Z d) : Set (E d) := cellIndex m ⁻¹' {j}

theorem cell_eq_box (hm : 0 < m) (j : Z d) :
    cell m j = univ.pi (fun i => Ico ((j i : ℝ) / m) (((j i : ℝ) + 1) / m)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  ext x
  change cellIndex m x = j ↔ _
  rw [funext_iff, mem_univ_pi]
  refine forall_congr' fun i => ?_
  change ⌊(m : ℝ) * x i⌋ = j i ↔ (j i : ℝ) / m ≤ x i ∧ x i < ((j i : ℝ) + 1) / m
  rw [Int.floor_eq_iff, div_le_iff₀ hm', lt_div_iff₀ hm', mul_comm (m : ℝ)]

/-- The ambient Pi norm is the sup norm. The estimate includes dimension zero. -/
theorem norm_gridPoint_cellIndex_sub_le (hm : 0 < m) (x : E d) :
    ‖gridPoint m (cellIndex m x) - x‖ ≤ 1 / (m : ℝ) := by
  have hx : x ∈ cell m (cellIndex m x) := rfl
  rw [cell_eq_box hm, mem_univ_pi] at hx
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))).2
  intro i
  change |gridPoint m (cellIndex m x) i - x i| ≤ _
  have hlo : gridPoint m (cellIndex m x) i ≤ x i := (hx i).1
  have hhi : x i < gridPoint m (cellIndex m x) i + 1 / (m : ℝ) := by
    simpa only [gridPoint, add_div] using (hx i).2
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

theorem measurableSet_cell (m : ℕ) (j : Z d) : MeasurableSet (cell m j) :=
  (measurableSet_singleton j).preimage (measurable_cellIndex m)

theorem iUnion_cell (m : ℕ) : (⋃ j : Z d, cell m j) = univ :=
  iUnion_eq_univ_iff.mpr fun x => ⟨cellIndex m x, rfl⟩

theorem volume_cell (hm : 0 < m) (j : Z d) :
    volume (cell m j) = ENNReal.ofReal (1 / (m : ℝ) ^ d) := by
  have width (i : Fin d) : ((j i : ℝ) + 1) / m - (j i : ℝ) / m = 1 / (m : ℝ) := by
    rw [add_div, add_sub_cancel_left]
  rw [cell_eq_box hm, volume_pi_pi]
  simp only [Real.volume_Ico, width, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity), one_div_pow]

theorem integral_on_cell (hm : 0 < m) (f : Z d → ℝ) (j : Z d) :
    (∫ x in cell m j, f (cellIndex m x)) = (1 / (m : ℝ) ^ d) * f j := by
  calc
    _ = ∫ _ : E d in cell m j, f j :=
      setIntegral_congr_fun (measurableSet_cell m j) fun _ hx => congrArg f hx
    _ = _ := by
      rw [setIntegral_const, measureReal_def, volume_cell hm, ENNReal.toReal_ofReal (by positivity),
        smul_eq_mul]

/-- Countable additivity of the integral over the disjoint fibers. -/
theorem hasSum_cellIndex (hm : 0 < m) {f : Z d → ℝ}
    (hf : Integrable (fun x : E d => f (cellIndex m x))) :
    HasSum (fun j => (1 / (m : ℝ) ^ d) * f j) (∫ x : E d, f (cellIndex m x)) := by
  have h := hasSum_integral_iUnion (measurableSet_cell (d := d) m)
    (pairwise_disjoint_fiber (cellIndex (d := d) m)) hf.integrableOn
  simpa only [integral_on_cell hm, iUnion_cell, setIntegral_univ] using h

theorem summable_of_integrable_cellIndex (hm : 0 < m) {f : Z d → ℝ}
    (hf : Integrable (fun x : E d => f (cellIndex m x))) : Summable f :=
  (summable_mul_left_iff (by positivity : (1 / (m : ℝ) ^ d) ≠ 0)).mp
    (hasSum_cellIndex hm hf).summable

theorem integral_cellIndex (hm : 0 < m) {f : Z d → ℝ}
    (hf : Integrable (fun x : E d => f (cellIndex m x))) :
    (∫ x : E d, f (cellIndex m x)) = (1 / (m : ℝ) ^ d) * ∑' j, f j := by
  simpa only [tsum_mul_left] using (hasSum_cellIndex hm hf).tsum_eq.symm

theorem integrable_cellIndex_iff (hm : 0 < m) (f : Z d → ℝ) :
    Integrable (fun x : E d => f (cellIndex m x)) ↔ Summable f := by
  refine ⟨summable_of_integrable_cellIndex hm, fun hf => ?_⟩
  have hi (j : Z d) : IntegrableOn (fun x => f (cellIndex m x)) (cell m j) := by
    have hc : IntegrableOn (fun _ : E d => f j) (cell m j) :=
      integrableOn_const.mpr (Or.inr (by rw [volume_cell hm]; exact ENNReal.ofReal_lt_top))
    exact hc.congr_fun (fun _ hx => (congrArg f hx).symm) (measurableSet_cell m j)
  have hs : Summable (fun j : Z d => ∫ x in cell m j, ‖f (cellIndex m x)‖) :=
    (hf.abs.mul_left (1 / (m : ℝ) ^ d)).congr fun j =>
      (integral_on_cell hm (fun k => |f k|) j).symm
  simpa only [iUnion_cell, integrableOn_univ] using integrableOn_iUnion_of_summable_integral_norm hi hs

end MaternAudit.MovingCells
