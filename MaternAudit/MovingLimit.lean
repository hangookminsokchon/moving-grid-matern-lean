import MaternAudit.FourierBound
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Integration against a moving discrete measure. The support of a fixed compact
frequency window can contain more and more lattice points as the mesh decreases. -/

noncomputable section
open Filter
open scoped Topology

namespace MaternAudit.MovingLimit

/-- Uniform convergence on row-dependent sets follows by testing all selections.
An element of every row is supplied to handle rows without counterexamples. -/
theorem uniform_of_selections {α : Type*} (S : ℕ → Set α) (z : α)
    (hz : ∀ n, z ∈ S n) (B : ℕ → α → ℝ) (b : ℝ)
    (h : ∀ r : ℕ → α, (∀ n, r n ∈ S n) →
      Tendsto (fun n ↦ B n (r n)) atTop (𝓝 b)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ r ∈ S n, |B n r - b| ≤ ε := by
  classical
  let bad (n : ℕ) := ∃ r ∈ S n, ε < |B n r - b|
  let r (n : ℕ) := if hn : bad n then hn.choose else z
  have hr (n) : r n ∈ S n := by
    by_cases hn : bad n
    · simpa [r, hn] using hn.choose_spec.1
    · simpa [r, hn] using hz n
  have hc := (Metric.tendsto_nhds.mp (h r hr)) ε hε
  filter_upwards [hc] with n hn r' hr'
  rw [Real.dist_eq] at hn
  by_contra! hb
  have hex : bad n := ⟨r', hr', hb⟩
  have hc' := hex.choose_spec.2
  simp only [r, dif_pos hex] at hn
  exact (lt_asymm hn hc')

/-- A moving Fourier mass with fixed total mass and uniformly tight physical
tails may be tested against autocorrelations converging on all physical windows. -/
theorem weighted_limit_of_tight {α : Type*} (w B rad : ℕ → α → ℝ) (mass b M : ℝ)
    (hw : ∀ n r, 0 ≤ w n r) (hs : ∀ n, HasSum (w n) mass)
    (hM : 0 ≤ M) (hbounded : ∀ᶠ n in atTop, ∀ r, |B n r| ≤ M)
    (htail : ∀ δ > (0 : ℝ), ∃ K ≥ (0 : ℝ), ∀ᶠ n in atTop,
      (∑' r, if K < rad n r then w n r else 0) ≤ δ)
    (hwindow : ∀ K ≥ (0 : ℝ), ∀ δ > (0 : ℝ), ∀ᶠ n in atTop,
      ∀ r, rad n r ≤ K → |B n r - b| ≤ δ) :
    Tendsto (fun n ↦ ∑' r, w n r * B n r) atTop (𝓝 (mass * b)) := by
  classical
  have hm : 0 ≤ mass := (hs 0).tsum_eq ▸ tsum_nonneg (hw 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C := M + |b|
  have hC : 0 ≤ C := add_nonneg hM (abs_nonneg _)
  let δ := ε / (mass + C + 1)
  have hd : 0 < δ := div_pos hε (by positivity)
  obtain ⟨K, hK, hKtail⟩ := htail δ hd
  filter_upwards [hbounded, hKtail, hwindow K hK δ hd] with n hBn ht hwn
  let v (r : α) := if K < rad n r then w n r else 0
  have hvn (r : α) : 0 ≤ v r := by dsimp [v]; split_ifs <;> simp [hw n r]
  have hvs : Summable v := .of_nonneg_of_le hvn
    (fun r ↦ by dsimp [v]; split_ifs <;> simp [hw n r]) (hs n).summable
  have hmaj := ((hs n).summable.mul_right δ).add (hvs.mul_right C)
  have hbabs (r : α) : |B n r - b| ≤ C :=
    (abs_sub _ _).trans (add_le_add_right (hBn r) _)
  have hper (r : α) : ‖w n r * (B n r - b)‖ ≤ w n r * δ + v r * C := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n r)]
    by_cases hr : K < rad n r
    · simp only [v, if_pos hr]
      exact (mul_le_mul_of_nonneg_left (hbabs r) (hw n r)).trans
        (le_add_of_nonneg_left (mul_nonneg (hw n r) hd.le))
    · simp only [v, if_neg hr, zero_mul, add_zero]
      exact mul_le_mul_of_nonneg_left (hwn r (le_of_not_gt hr)) (hw n r)
  have hnorm : Summable (fun r ↦ ‖w n r * (B n r - b)‖) :=
    .of_nonneg_of_le (fun r ↦ norm_nonneg _) hper hmaj
  have hdev := hnorm.of_norm
  have hcombine := hdev.hasSum.add ((hs n).mul_right b)
  have hsum : HasSum (fun r ↦ w n r * B n r)
      ((∑' r, w n r * (B n r - b)) + mass * b) :=
    hcombine.congr_fun fun r ↦ by ring
  rw [Real.dist_eq, hsum.tsum_eq, add_sub_cancel_right, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' r, ‖w n r * (B n r - b)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r, (w n r * δ + v r * C) := hnorm.tsum_le_tsum hper hmaj
    _ = mass * δ + (∑' r, v r) * C := by
      rw [Summable.tsum_add ((hs n).summable.mul_right δ) (hvs.mul_right C),
        tsum_mul_right, tsum_mul_right, (hs n).tsum_eq]
    _ ≤ mass * δ + δ * C := add_le_add_left (mul_le_mul_of_nonneg_right ht hC) _
    _ < ε := by
      have he : δ * (mass + C + 1) = ε := by
        apply div_mul_cancel₀
        positivity
      linarith [show mass * δ + δ * C + δ = ε by linear_combination he]

end MaternAudit.MovingLimit
