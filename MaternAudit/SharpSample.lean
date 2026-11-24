import MaternAudit.OverlapVariance
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Relative limits with two competing scales; no limit of their ratio is needed. -/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace MaternAudit.SharpSample

theorem mixed_ratio {a b u v : ℕ → ℝ} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : ∀ n, 0 < u n) (hv : ∀ n, 0 ≤ v n)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun n ↦ (a n * u n + b n * v n) / (A * u n + B * v n)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp ha (ε / 2 * A) (by positivity),
    Metric.tendsto_nhds.mp hb (ε / 2 * B) (by positivity)] with n hna hnb
  simp only [Real.dist_eq] at hna hnb ⊢
  have hs : 0 < A * u n + B * v n :=
    add_pos_of_pos_of_nonneg (mul_pos hA (hu n)) (mul_nonneg hB.le (hv n))
  rw [div_sub_one hs.ne', abs_div, abs_of_pos hs, div_lt_iff₀ hs]
  have hid : a n * u n + b n * v n - (A * u n + B * v n) =
    (a n - A) * u n + (b n - B) * v n := by ring
  rw [hid]
  calc
    _ ≤ |(a n - A) * u n| + |(b n - B) * v n| := abs_add_le _ _
    _ = |a n - A| * u n + |b n - B| * v n := by
      simp only [abs_mul, abs_of_nonneg (hu n).le, abs_of_nonneg (hv n)]
    _ ≤ (ε / 2 * A) * u n + (ε / 2 * B) * v n :=
      add_le_add (mul_le_mul_of_nonneg_right hna.le (hu n).le)
        (mul_le_mul_of_nonneg_right hnb.le (hv n))
    _ < _ := by nlinarith [mul_pos hε hs]

/-- Any uniform variance bound of the indicated order is negligible for the two-term mean. -/
theorem relative_variance {V u v : ℕ → ℝ} {A B K : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hK : 0 ≤ K) (hu : ∀ n, 0 < u n) (hv : ∀ n, 0 ≤ v n)
    (hu0 : Tendsto u atTop (𝓝 0)) (hV : ∀ n, 0 ≤ V n)
    (hb : ∀ᶠ n in atTop, V n ≤ K * u n * (u n + v n) ^ 2) :
    Tendsto (fun n ↦ V n / (A * u n + B * v n)^2) atTop (𝓝 0) := by
  let D := min A B
  have hD : 0 < D := lt_min hA hB
  have ht : Tendsto (fun n ↦ (K / D^2) * u n) atTop (𝓝 0) := by
    simpa using hu0.const_mul (K / D^2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun n ↦ div_nonneg (hV n) (sq_nonneg _)
  filter_upwards [hb] with n hn
  have hsum : 0 < u n + v n := add_pos_of_pos_of_nonneg (hu n) (hv n)
  have hden : D * (u n + v n) ≤ A * u n + B * v n := by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left A B) (hu n).le)
      (mul_le_mul_of_nonneg_right (min_le_right A B) (hv n))
  have hnon : 0 ≤ K * u n * (u n + v n)^2 :=
    mul_nonneg (mul_nonneg hK (hu n).le) (sq_nonneg _)
  calc
    V n / (A * u n + B * v n)^2 ≤ (K * u n * (u n + v n)^2) /
        (D * (u n + v n))^2 := by
      exact div_le_div₀ hnon hn (sq_pos_of_pos (mul_pos hD hsum))
        (pow_le_pow_left₀ (mul_pos hD hsum).le hden 2)
    _ = _ := by field_simp [hD.ne', hsum.ne']; ring

/-- Concentration of the observed RMS around its deterministic two-term equivalent. -/
theorem relative_rms {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (s : ℕ → ℝ) (hs : ∀ n, 0 < s n)
    (hz : ∀ n ω, 0 ≤ Z n ω) (hm : ∀ n, MemLp (Z n) 2 P)
    (hmean : Tendsto (fun n ↦ (∫ ω, Z n ω ∂P) / s n) atTop (𝓝 1))
    (hvar : Tendsto (fun n ↦ variance (Z n) P / (s n)^2) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ P.real
      {ω | ε ≤ |Real.sqrt (Z n ω) / Real.sqrt (s n) - 1|}) atTop (𝓝 0) := by
  intro ε hε
  let t := ε / 2
  have ht : 0 < t := half_pos hε
  have hupper : Tendsto (fun n ↦ (variance (Z n) P / s n ^ 2) / t ^ 2) atTop (𝓝 0) := by
    simpa using hvar.div_const (t^2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg
  filter_upwards [Metric.tendsto_nhds.mp hmean t ht] with n he
  have hsn := hs n
  rw [Real.dist_eq, div_sub_one hsn.ne', abs_div, abs_of_pos hsn, div_lt_iff₀ hsn] at he
  have hsub : {ω | ε ≤ |Real.sqrt (Z n ω) / Real.sqrt (s n) - 1|} ⊆
      {ω | t * s n ≤ |Z n ω - ∫ w, Z n w ∂P|} := by
    intro ω hω
    change ε ≤ |Real.sqrt (Z n ω) / Real.sqrt (s n) - 1| at hω
    change t * s n ≤ _
    rw [← Real.sqrt_div (hz n ω)] at hω
    have hx : 0 ≤ Z n ω / s n := div_nonneg (hz n ω) hsn.le
    have hroot : |Real.sqrt (Z n ω / s n) - 1| ≤ |Z n ω / s n - 1| := by
      let r := Real.sqrt (Z n ω / s n)
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have hid : Z n ω / s n - 1 = (r - 1) * (r + 1) := by nlinarith [Real.sq_sqrt hx]
      rw [hid, abs_mul, abs_of_nonneg (by linarith : 0 ≤ r + 1)]
      exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    have hzω := hω.trans hroot
    rw [div_sub_one hsn.ne', abs_div, abs_of_pos hsn, le_div_iff₀ hsn] at hzω
    have htri := abs_sub_le (Z n ω) (∫ w, Z n w ∂P) (s n)
    dsimp [t] at he ⊢
    linarith
  calc
    _ ≤ _ := measureReal_mono hsub
    _ ≤ variance (Z n) P / (t * s n)^2 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (meas_ge_le_variance_div_sq (hm n) (mul_pos ht hsn))
      rwa [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at h
    _ = _ := by ring

end MaternAudit.SharpSample
