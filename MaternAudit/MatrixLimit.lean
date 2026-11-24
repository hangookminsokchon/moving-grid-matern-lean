import MaternAudit.MaternParameters
import MaternAudit.IIDVariance
import MaternAudit.SharpSample

/-! From the two population energies to the iid matrix RMS with no aspect-ratio restriction. -/

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace MaternAudit.MatrixLimit
open MaternParameters IIDVariance
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

def observed (g : Grid) (H : ℕ → S → S → ℝ) (X : ℕ → Ω → S) (n : ℕ) : Ω → ℝ :=
  statistic (H n) (fun i : Fin (g.N n) ↦ X i)

omit [MeasurableSpace S] [MeasurableSpace Ω] in
theorem observed_nonneg (g : Grid) (H : ℕ → S → S → ℝ) (X : ℕ → Ω → S)
    (hn : ∀ n x y, 0 ≤ H n x y) (n : ℕ) (ω : Ω) : 0 ≤ observed g H X n ω := by
  unfold observed statistic OverlapVariance.pairAverage
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ hn _ _ _)

theorem two_term_matrix {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure S}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → S} (hx : SampleLaw P μ X)
    (g : Grid) (d : ℕ) (H : ℕ → S → S → ℝ) (δ : ℕ → ℝ) (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hH : ∀ n, KernelBounds (H n) (δ n) (δ n))
    (hdiag : Tendsto δ atTop (𝓝 A))
    (hpair : Tendsto (fun n ↦ (∫ z, Function.uncurry (H n) z ∂μ.prod μ) / g.v d n)
      atTop (𝓝 B))
    (hproj : ∃ C ≥ (0 : ℝ), ∀ᶠ n in atTop, ∀ᵐ x ∂μ, projection μ (H n) x ≤ C * g.v d n) :
    let s (n : ℕ) := A * g.u n + B * g.v d n
    Tendsto (fun n ↦ (∫ ω, observed g H X n ω ∂P) / s n) atTop (𝓝 1) ∧
      ∀ ε > (0 : ℝ), Tendsto (fun n ↦ P.real {ω |
        ε ≤ |Real.sqrt (observed g H X n ω) / Real.sqrt (s n) - 1|}) atTop (𝓝 0) := by
  dsimp only
  let s (n : ℕ) := A * g.u n + B * g.v d n
  have hs (n : ℕ) : 0 < s n := add_pos (mul_pos hA (g.u_pos n)) (mul_pos hB (g.v_pos d n))
  let mean (n : ℕ) := ∫ z, Function.uncurry (H n) z ∂μ.prod μ
  have hfactor : Tendsto (fun n ↦ (1 : ℝ) - g.u n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub g.u_zero
  have hp : Tendsto (fun n ↦ (1 - g.u n) * (mean n / g.v d n)) atTop (𝓝 B) := by
    simpa using hfactor.mul hpair
  have he := SharpSample.mixed_ratio hA hB g.u_pos (fun n ↦ (g.v_pos d n).le) hdiag hp
  have hmean : Tendsto (fun n ↦ (∫ ω, observed g H X n ω ∂P) / s n) atTop (𝓝 1) := by
    refine he.congr fun n ↦ ?_
    rw [show (∫ ω, observed g H X n ω ∂P) = rowMean μ (H n) (δ n) (g.N n) from
      expectation_statistic (g.N_pos n) (hx.first _) (hH n)]
    dsimp only [rowMean, s, mean, Grid.u]
    rw [one_div, mul_assoc, div_mul_cancel₀ _ (g.v_pos d n).ne', div_eq_mul_inv (δ n)]
  refine ⟨hmean, ?_⟩
  obtain ⟨C, hC, hproj'⟩ := hproj
  let D := A + 1
  have hD : 0 < D := by dsimp [D]; linarith
  have hdelt : ∀ᶠ n in atTop, δ n ≤ D := hdiag.eventually_le_const (by dsimp [D]; linarith)
  let K := 2 * D * C + 4 * C ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply SharpSample.relative_rms P (observed g H X) s hs
    (observed_nonneg g H X fun n ↦ (hH n).nonneg)
    (fun n ↦ statistic_memLp (hx.first _) (hH n)) hmean
  apply SharpSample.relative_variance hA hB hK g.u_pos (fun n ↦ (g.v_pos d n).le)
    g.u_zero (fun n ↦ variance_nonneg _ _)
  filter_upwards [g.sample_grows.eventually_ge_atTop 2, hproj', hdelt] with n hn hqp hdp
  have hv := (g.v_pos d n).le
  have hu := (g.u_pos n).le
  have hb := variance_le_envelopes hn (hx.first (g.N n)) (hH n) hqp
  refine hb.trans ?_
  have hid : 2 * δ n * (C * g.v d n) / (g.N n : ℝ)^2 + 4 * (C * g.v d n)^2 / g.N n =
      (2 * δ n * C) * (g.v d n * (g.u n)^2) + (4 * C^2) * (g.u n * (g.v d n)^2) := by
    dsimp only [Grid.u]
    ring
  rw [hid]
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdp (by norm_num : (0:ℝ) ≤ 2)) hC)
    (mul_nonneg hv (sq_nonneg (g.u n)))
  have hs1 : g.v d n * (g.u n)^2 ≤ g.u n * (g.u n + g.v d n)^2 := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hs2 : g.u n * (g.v d n)^2 ≤ g.u n * (g.u n + g.v d n)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv (le_add_of_nonneg_left hu) 2) hu
  calc
    _ ≤ (2 * D * C) * (g.v d n * (g.u n)^2) + (4 * C^2) * (g.u n * (g.v d n)^2) :=
      add_le_add_right h1 _
    _ ≤ (2 * D * C) * (g.u n * (g.u n + g.v d n)^2) +
        (4 * C^2) * (g.u n * (g.u n + g.v d n)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hs1 (by positivity)) (mul_le_mul_of_nonneg_left hs2 (by positivity))
    _ = _ := by dsimp [K]; ring

omit [MeasurableSpace S] [MeasurableSpace Ω] in
theorem observed_scale (g : Grid) {H H' : ℕ → S → S → ℝ} (X : ℕ → Ω → S) (a : ℕ → ℝ)
    (he : ∀ n x y, H' n x y = (a n)^2 * H n x y) (n : ℕ) (ω : Ω) :
    observed g H' X n ω = (a n)^2 * observed g H X n ω := by
  unfold observed statistic OverlapVariance.pairAverage
  simp_rw [he]
  simp only [← Finset.mul_sum]
  ring

/-- Restores a row-dependent spectral amplitude in both the statistic and its scale. -/
theorem restore_amplitude {P : Measure Ω} (Z Z' : ℕ → Ω → ℝ) (a s : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hs : ∀ n, 0 < s n)
    (hz : ∀ n ω, Z' n ω = (a n)^2 * Z n ω)
    (hmean : Tendsto (fun n ↦ (∫ ω, Z n ω ∂P) / s n) atTop (𝓝 1))
    (hrms : ∀ ε > (0 : ℝ), Tendsto (fun n ↦ P.real {ω |
      ε ≤ |Real.sqrt (Z n ω) / Real.sqrt (s n) - 1|}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (∫ ω, Z' n ω ∂P) / ((a n)^2 * s n)) atTop (𝓝 1) ∧
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ P.real {ω |
      ε ≤ |Real.sqrt (Z' n ω) / Real.sqrt ((a n)^2 * s n) - 1|}) atTop (𝓝 0) := by
  constructor
  · apply hmean.congr
    intro n
    simp_rw [hz n, integral_const_mul]
    field_simp [(ha n).ne', (hs n).ne']
    ring
  intro ε hε
  apply (hrms ε hε).congr
  intro n
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, hz, Real.sqrt_mul (sq_nonneg (a n)), Real.sqrt_sq (ha n).le]
  rw [mul_div_mul_left _ _ (ha n).ne']

end MaternAudit.MatrixLimit
