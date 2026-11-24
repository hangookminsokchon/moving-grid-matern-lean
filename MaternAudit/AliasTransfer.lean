import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Transfer an entrywise aliasing bound to the empirical Frobenius RMS,
convergence in probability, and convergence of relative second moments. -/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace MaternAudit.AliasTransfer

private def entries {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  (WithLp.equiv 2 _).symm fun p ↦ A p.1 p.2

/-- The unnormalized complex Frobenius norm on a square sample matrix. -/
def frobeniusNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ℝ := ‖entries A‖

theorem frobeniusNorm_eq_sqrt {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    frobeniusNorm A = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) := by
  rw [frobeniusNorm, EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  rfl

/-- The reverse triangle inequality bounds the absolute norm difference by
`N * η` when each of the `N²` entries changes in magnitude by at most `η`. -/
theorem frobenius_residual_bound {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hentry : ∀ i j, ‖A i j - B i j‖ ≤ η) :
    |frobeniusNorm A - frobeniusNorm B| ≤ (N : ℝ) * η := by
  apply (abs_norm_sub_norm_le (entries A) (entries B)).trans
  change frobeniusNorm (A - B) ≤ (N : ℝ) * η
  rw [frobeniusNorm_eq_sqrt, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Nat.cast_nonneg N) hη, ?_⟩
  calc
    (∑ i, ∑ j, ‖(A - B) i j‖ ^ 2) ≤ ∑ _i : Fin N, ∑ _j : Fin N, η ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- Root mean square over all ordered entries, including the diagonal. -/
def sampleRMS {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ℝ := frobeniusNorm A / N

theorem sampleRMS_eq_sqrt_mean_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    sampleRMS A = Real.sqrt ((∑ i, ∑ j, ‖A i j‖ ^ 2) / (N : ℝ) ^ 2) := by
  rw [sampleRMS, frobeniusNorm_eq_sqrt, Real.sqrt_div (by positivity),
    Real.sqrt_sq (Nat.cast_nonneg N)]

@[simp] theorem sampleRMS_neg {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    sampleRMS (-A) = sampleRMS A := by
  simp [sampleRMS, frobeniusNorm_eq_sqrt, Matrix.neg_apply]

/-- Dividing the Frobenius norm by the sample size leaves exactly the
entrywise residual bound. This includes the empty matrix under Lean's division convention. -/
theorem sampleRMS_residual_bound {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hentry : ∀ i j, ‖A i j - B i j‖ ≤ η) :
    |sampleRMS A - sampleRMS B| ≤ η := by
  by_cases hN : N = 0
  · simp [sampleRMS, hN, hη]
  have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [sampleRMS, sampleRMS, ← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  simpa only [mul_comm η] using frobenius_residual_bound A B hη hentry

/-- The full kernel error in the note is `alias - trunc`, and the comparison
RMS is that of `trunc`. -/
theorem sampleRMS_alias_sub {N : ℕ} (aliasMatrix trunc : Matrix (Fin N) (Fin N) ℂ) {η : ℝ}
    (hη : 0 ≤ η) (ha : ∀ i j, ‖aliasMatrix i j‖ ≤ η) :
    |sampleRMS (aliasMatrix - trunc) - sampleRMS trunc| ≤ η := by
  have h := sampleRMS_residual_bound (aliasMatrix - trunc) (-trunc) hη fun i j ↦ by
    simpa only [Matrix.sub_apply, Matrix.neg_apply, sub_neg_eq_add, sub_add_cancel] using ha i j
  simpa only [sampleRMS_neg] using h


section Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A deterministic bound on the residual, valid almost surely at each index,
transfers convergence in measure of normalized RMS to any target. -/
theorem tendstoInMeasure_ratio (P : Measure Ω) {full trunc : ℕ → Ω → ℝ}
    {L η : ℕ → ℝ} {limit : Ω → ℝ} (hL : ∀ n, 0 < L n)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |full n ω - trunc n ω| ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / L n) atTop (𝓝 0))
    (htrunc : TendstoInMeasure P (fun n ω ↦ trunc n ω / L n) atTop limit) :
    TendstoInMeasure P (fun n ω ↦ full n ω / L n) atTop limit := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (htrunc (ε/2) (half_pos hε))
  · exact Eventually.of_forall fun _ ↦ zero_le _
  filter_upwards [hsmall.eventually (eventually_lt_nhds (half_pos hε))] with n hn
  apply measure_mono_ae
  filter_upwards [hbound n] with ω hω
  intro hfull
  change ε ≤ dist (full n ω / L n) (limit ω) at hfull
  change ε / 2 ≤ dist (trunc n ω / L n) (limit ω)
  have hd : dist (full n ω / L n) (trunc n ω / L n) ≤ η n / L n := by
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hL n)]
    exact div_le_div_of_nonneg_right hω (hL n).le
  have htri := dist_triangle (full n ω / L n) (trunc n ω / L n) (limit ω)
  linarith

/-- The real-valued tail probability formulation used in the sample RMS theorem. -/
theorem tendstoInMeasure_iff_real_tail (P : Measure Ω) [IsFiniteMeasure P]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} :
    TendstoInMeasure P X atTop Y ↔ ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ P.real {ω | ε ≤ |X n ω - Y ω|}) atTop (𝓝 0) := by
  unfold TendstoInMeasure
  simp only [Real.dist_eq]
  have hiff (ε : ℝ) := ENNReal.tendsto_toReal_iff (fi := atTop)
    (f := fun n ↦ P {ω | ε ≤ |X n ω - Y ω|}) (fun n ↦ measure_ne_top _ _) ENNReal.zero_ne_top
  constructor <;> intro h ε hε
  · simpa only [Measure.real, ENNReal.toReal_zero] using (hiff ε).mpr (h ε hε)
  · apply (hiff ε).mp
    simpa only [Measure.real, ENNReal.toReal_zero] using h ε hε

/-- Convergence transfer stated directly with real tail probabilities. -/
theorem probability_ratio (P : Measure Ω) [IsFiniteMeasure P] {full trunc : ℕ → Ω → ℝ}
    {L η : ℕ → ℝ} {limit : Ω → ℝ} (hL : ∀ n, 0 < L n)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |full n ω - trunc n ω| ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / L n) atTop (𝓝 0))
    (htrunc : ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ P.real {ω | ε ≤ |trunc n ω / L n - limit ω|}) atTop (𝓝 0)) :
    ∀ ε > (0 : ℝ),
      Tendsto (fun n ↦ P.real {ω | ε ≤ |full n ω / L n - limit ω|}) atTop (𝓝 0) :=
  (tendstoInMeasure_iff_real_tail P).mp
    (tendstoInMeasure_ratio P hL hbound hsmall ((tendstoInMeasure_iff_real_tail P).mpr htrunc))

private theorem norm_toLp_eq_sqrt_integral_sq {P : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ = Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  rw [norm_eq_sqrt_real_inner, L2.inner_def]
  apply congrArg Real.sqrt
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Reverse triangle in population L². Square integrability of the full
RMS follows from measurability and the bounded difference. -/
theorem populationRMS_residual_bound (P : Measure Ω) [IsProbabilityMeasure P]
    {full trunc : Ω → ℝ} {η : ℝ} (ht : MemLp trunc 2 P) (hf : AEStronglyMeasurable full P)
    (hbound : ∀ᵐ ω ∂P, |full ω - trunc ω| ≤ η) :
    |Real.sqrt (∫ ω, full ω ^ 2 ∂P) - Real.sqrt (∫ ω, trunc ω ^ 2 ∂P)| ≤ η := by
  have hη : 0 ≤ η := by
    obtain ⟨ω, hω⟩ := hbound.exists
    exact (abs_nonneg _).trans hω
  have hr : ∀ᵐ ω ∂P, ‖(full - trunc) ω‖ ≤ η := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hbound
  have hd : MemLp (full - trunc) 2 P := .of_bound (hf.sub ht.aestronglyMeasurable) η hr
  have hF : MemLp full 2 P := by simpa only [sub_add_cancel] using hd.add ht
  rw [← norm_toLp_eq_sqrt_integral_sq hF, ← norm_toLp_eq_sqrt_integral_sq ht]
  calc
    _ ≤ ‖hF.toLp full - ht.toLp trunc‖ := abs_norm_sub_norm_le _ _
    _ = (eLpNorm (full - trunc) 2 P).toReal := by rw [← hF.toLp_sub ht, Lp.norm_toLp]
    _ ≤ η := by
      have he : eLpNorm (full - trunc) 2 P ≤ ENNReal.ofReal η := by
        simpa using eLpNorm_le_of_ae_bound (p := 2) hr
      simpa only [ENNReal.toReal_ofReal hη] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

/-- Transfer the second-moment equivalent for a moving scale `L n`. Only the
truncation's square integrability and measurability of the full RMS are required. -/
theorem secondMoment_ratio (P : Measure Ω) [IsProbabilityMeasure P] {full trunc : ℕ → Ω → ℝ}
    {L η : ℕ → ℝ} (hL : ∀ n, 0 < L n) (ht : ∀ n, MemLp (trunc n) 2 P)
    (hf : ∀ n, AEStronglyMeasurable (full n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |full n ω - trunc n ω| ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / L n) atTop (𝓝 0))
    (htrunc : Tendsto (fun n ↦ (∫ ω, trunc n ω ^ 2 ∂P) / L n ^ 2) atTop (𝓝 1)) :
    Tendsto (fun n ↦ (∫ ω, full n ω ^ 2 ∂P) / L n ^ 2) atTop (𝓝 1) := by
  let T (n : ℕ) := ∫ ω, trunc n ω ^ 2 ∂P
  let F (n : ℕ) := ∫ ω, full n ω ^ 2 ∂P
  have hT (n) : 0 ≤ T n := integral_nonneg fun ω ↦ sq_nonneg _
  have hF (n) : 0 ≤ F n := integral_nonneg fun ω ↦ sq_nonneg _
  have hroot : Tendsto (fun n ↦ Real.sqrt (T n) / L n) atTop (𝓝 1) := by
    have h : Tendsto (fun n ↦ Real.sqrt (T n / L n ^ 2)) atTop (𝓝 1) := by
      simpa only [Real.sqrt_one] using htrunc.sqrt
    exact h.congr fun n ↦ by rw [Real.sqrt_div (hT n), Real.sqrt_sq (hL n).le]
  have hdist (n) : dist (Real.sqrt (T n) / L n) (Real.sqrt (F n) / L n) ≤ η n / L n := by
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hL n), abs_sub_comm]
    exact div_le_div_of_nonneg_right (populationRMS_residual_bound P (ht n) (hf n) (hbound n)) (hL n).le
  have hrootF : Tendsto (fun n ↦ Real.sqrt (F n) / L n) atTop (𝓝 1) :=
    hroot.congr_dist (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsmall
      (fun _ ↦ dist_nonneg) hdist)
  simpa only [div_pow, Real.sq_sqrt (hF _), one_pow] using hrootF.pow 2

/-- If the moving scale converges, the full second moment converges to its squared limit. -/
theorem secondMoment_limit (P : Measure Ω) [IsProbabilityMeasure P] {full trunc : ℕ → Ω → ℝ}
    {L η : ℕ → ℝ} {ℓ : ℝ} (hL : ∀ n, 0 < L n) (ht : ∀ n, MemLp (trunc n) 2 P)
    (hf : ∀ n, AEStronglyMeasurable (full n) P)
    (hbound : ∀ n, ∀ᵐ ω ∂P, |full n ω - trunc n ω| ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / L n) atTop (𝓝 0))
    (htrunc : Tendsto (fun n ↦ (∫ ω, trunc n ω ^ 2 ∂P) / L n ^ 2) atTop (𝓝 1))
    (hscale : Tendsto L atTop (𝓝 ℓ)) :
    Tendsto (fun n ↦ ∫ ω, full n ω ^ 2 ∂P) atTop (𝓝 (ℓ ^ 2)) := by
  have h := (secondMoment_ratio P hL ht hf hbound hsmall htrunc).mul (hscale.pow 2)
  simpa only [one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 (hL _).ne')] using h

end Probability

end MaternAudit.AliasTransfer
