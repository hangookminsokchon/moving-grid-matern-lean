import MaternAudit.Expectation
import MaternAudit.OverlapVariance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

/-!
# IID moments and relative concentration of ordered-pair averages

The two population laws entering the variance are the law of the kernel on an
independent pair and the law of its one-coordinate integral. Independence of
the coordinates gives the three- and four-index calculations used below.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace MaternAudit.IIDVariance

variable {Ω S ι : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {μ : Measure S} {X : ι → Ω → S} {H : S → S → ℝ} {δ U : ℝ}

/-- A family of measurable, independent draws with common law `μ`. -/
structure SampleLaw (P : Measure Ω) (μ : Measure S) (X : ι → Ω → S) : Prop where
  marginal : ∀ i, MeasurePreserving (X i) P μ
  independent : iIndepFun X P

/-- Restrict iid draws to any injective choice of indices. In particular use
`h.first n` for the first `n` draws of a sequence indexed by the naturals. -/
theorem SampleLaw.reindex (h : SampleLaw P μ X) {κ : Type*} {f : κ → ι}
    (hf : Function.Injective f) : SampleLaw P μ (fun i => X (f i)) :=
  ⟨fun i => h.marginal (f i), h.independent.precomp hf⟩

theorem SampleLaw.first {Y : ℕ → Ω → S} (h : SampleLaw P μ Y) (n : ℕ) :
    SampleLaw P μ (fun i : Fin n => Y i) := h.reindex Fin.val_injective

/-- Coordinate draws on the canonical finite product probability space. -/
theorem sampleLaw_pi (μ : Measure S) [IsProbabilityMeasure μ] (n : ℕ) :
    SampleLaw (Measure.pi fun _ : Fin n => μ) μ (fun i (x : Fin n → S) => x i) :=
  ⟨Expectation.product_marginal μ, Expectation.product_independent μ n⟩

/-- Deterministic assumptions on the real loss kernel. -/
structure KernelBounds (H : S → S → ℝ) (δ U : ℝ) : Prop where
  measurable : Measurable (Function.uncurry H)
  symmetric : ∀ x y, H x y = H y x
  diagonal : ∀ x, H x x = δ
  nonneg : ∀ x y, 0 ≤ H x y
  le_upper : ∀ x y, H x y ≤ U

/-- Mean with one sample point held fixed. -/
def projection (μ : Measure S) (H : S → S → ℝ) (x : S) : ℝ := ∫ y, H x y ∂μ

/-- The deterministic expectation of the normalized statistic for a row of size `n`. -/
def rowMean (μ : Measure S) (H : S → S → ℝ) (δ : ℝ) (n : ℕ) : ℝ :=
  δ / n + (1 - 1 / (n : ℝ)) * ∫ z, Function.uncurry H z ∂μ.prod μ

/-- Average over the entire ordered-pair array, including its diagonal. -/
def statistic {n : ℕ} (H : S → S → ℝ) (X : Fin n → Ω → S) : Ω → ℝ :=
  OverlapVariance.pairAverage (fun i j ω => H (X i ω) (X j ω))

omit [MeasurableSpace Ω] [MeasurableSpace S] in
theorem statistic_apply {n : ℕ} (H : S → S → ℝ) (X : Fin n → Ω → S) (ω : Ω) :
    statistic H X ω = (∑ i, ∑ j, H (X i ω) (X j ω)) / (n : ℝ) ^ 2 := by
  rw [statistic, OverlapVariance.pairAverage, div_eq_mul_inv, mul_comm]

private theorem KernelBounds.memLp_pair (h : KernelBounds H δ U) {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsFiniteMeasure ν] {f g : A → S} (hf : Measurable f) (hg : Measurable g) :
    MemLp (fun a => H (f a) (g a)) 2 ν := by
  apply MemLp.of_bound (h.measurable.comp (hf.prodMk hg)).aestronglyMeasurable U
  exact Eventually.of_forall fun a => by
    change ‖H (f a) (g a)‖ ≤ U
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h.nonneg _ _)] using h.le_upper (f a) (g a)

private theorem integral_of_law {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {ν : Measure A} {ν' : Measure B} {Y : A → B} (hY : MeasurePreserving Y ν ν')
    {f : B → ℝ} (hf : Measurable f) : (∫ a, f (Y a) ∂ν) = ∫ b, f b ∂ν' := by
  rw [← hY.map_eq, integral_map hY.measurable.aemeasurable hf.aestronglyMeasurable]

private theorem variance_of_law {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {ν : Measure A} {ν' : Measure B} {Y : A → B} (hY : MeasurePreserving Y ν ν')
    {f : B → ℝ} (hf : Measurable f) : variance (fun a => f (Y a)) ν = variance f ν' := by
  have hm : Measurable (fun a => f (Y a)) := hf.comp hY.measurable
  rw [variance_eq_integral hm.aemeasurable, variance_eq_integral hf.aemeasurable,
    integral_of_law hY hf]
  exact integral_of_law hY ((hf.sub_const _).pow_const 2)

private theorem product_law {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [IsProbabilityMeasure P] {ν : Measure A} {ν' : Measure B} {Y : Ω → A} {Z : Ω → B}
    (hY : MeasurePreserving Y P ν) (hZ : MeasurePreserving Z P ν') (hi : IndepFun Y Z P) :
    MeasurePreserving (fun ω => (Y ω, Z ω)) P (ν.prod ν') := by
  refine ⟨hY.measurable.prodMk hZ.measurable, ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map hY.measurable.aemeasurable
    hZ.measurable.aemeasurable).1 hi, hY.map_eq, hZ.map_eq]

theorem SampleLaw.pair_law [IsProbabilityMeasure P] (h : SampleLaw P μ X) {i j : ι} (hij : i ≠ j) :
    MeasurePreserving (fun ω => (X i ω, X j ω)) P (μ.prod μ) :=
  product_law (h.marginal i) (h.marginal j) (h.independent.indepFun hij)

/-- Functions of two disjoint pairs of coordinates are independent. -/
theorem disjoint_entries (hx : SampleLaw P μ X) (h : KernelBounds H δ U)
    {i j k l : ι} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    IndepFun (fun ω => H (X i ω) (X j ω)) (fun ω => H (X k ω) (X l ω)) P :=
  (hx.independent.indepFun_prodMk_prodMk (fun a => (hx.marginal a).measurable) i j k l
    hik hil hjk hjl).comp h.measurable h.measurable

theorem KernelBounds.measurable_projection (h : KernelBounds H δ U) (μ : Measure S) [SFinite μ] :
    Measurable (projection μ H) :=
  h.measurable.stronglyMeasurable.integral_prod_right.measurable

theorem KernelBounds.projection_nonneg (h : KernelBounds H δ U) (μ : Measure S) (x : S) :
    0 ≤ projection μ H x := integral_nonneg (h.nonneg x)

theorem KernelBounds.projection_le (h : KernelBounds H δ U) (μ : Measure S)
    [IsProbabilityMeasure μ] (x : S) : projection μ H x ≤ U := by
  calc
    _ ≤ ∫ _ : S, U ∂μ := integral_mono_of_nonneg (ae_of_all _ (h.nonneg x))
      (integrable_const _) (ae_of_all _ (h.le_upper x))
    _ = U := by simp

private theorem KernelBounds.memLp_projection (h : KernelBounds H δ U) (μ : Measure S)
    [IsProbabilityMeasure μ] : MemLp (projection μ H) 2 μ := by
  apply MemLp.of_bound (h.measurable_projection μ).aestronglyMeasurable U
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h.projection_nonneg μ x)] using h.projection_le μ x

theorem KernelBounds.pair_mean_eq (h : KernelBounds H δ U) (μ : Measure S)
    [IsProbabilityMeasure μ] :
    (∫ z, Function.uncurry H z ∂μ.prod μ) = ∫ x, projection μ H x ∂μ :=
  integral_prod _ ((h.memLp_pair _ measurable_fst measurable_snd).integrable one_le_two)

variable [IsProbabilityMeasure P] [IsProbabilityMeasure μ]

/-- The product law of three distinct coordinates, followed by Fubini, gives
the second moment of the one-coordinate projection. -/
theorem shared_product_integral (hx : SampleLaw P μ X) (h : KernelBounds H δ U)
    {i j l : ι} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    (∫ ω, H (X i ω) (X j ω) * H (X i ω) (X l ω) ∂P) =
      ∫ x, (projection μ H x) ^ 2 ∂μ := by
  have htriple := product_law (hx.marginal i) (hx.pair_law hjl)
    (hx.independent.indepFun_prodMk (fun a => (hx.marginal a).measurable)
      j l i hij.symm hil.symm).symm
  let F (z : S × (S × S)) := H z.1 z.2.1 * H z.1 z.2.2
  have hf : Measurable F := (h.measurable.comp (measurable_fst.prodMk
    (measurable_fst.comp measurable_snd))).mul (h.measurable.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hint : Integrable F (μ.prod (μ.prod μ)) :=
    (h.memLp_pair _ measurable_fst (measurable_fst.comp measurable_snd)).integrable_mul
      (h.memLp_pair _ measurable_fst (measurable_snd.comp measurable_snd))
  calc
    _ = ∫ z, F z ∂μ.prod (μ.prod μ) := integral_of_law htriple hf
    _ = ∫ x, (∫ yz : S × S, H x yz.1 * H x yz.2 ∂μ.prod μ) ∂μ := integral_prod F hint
    _ = _ := by simp only [integral_prod_mul, projection, sq]

theorem shared_covariance (hx : SampleLaw P μ X) (h : KernelBounds H δ U)
    {i j l : ι} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    OverlapVariance.covariance P (fun ω => H (X i ω) (X j ω)) (fun ω => H (X i ω) (X l ω)) =
      variance (projection μ H) μ := by
  have mean {a b : ι} (hab : a ≠ b) :
      (∫ ω, H (X a ω) (X b ω) ∂P) = ∫ x, projection μ H x ∂μ :=
    (integral_of_law (hx.pair_law hab) h.measurable).trans (h.pair_mean_eq μ)
  rw [OverlapVariance.covariance, shared_product_integral hx h hij hil hjl, mean hij, mean hil,
    variance_def' (h.memLp_projection μ)]
  simp only [Pi.pow_apply, sq]

variable {n : ℕ} {Y : Fin n → Ω → S}

/-- All inputs of the finite overlap count are consequences of the iid law. -/
theorem kernel_moments (hx : SampleLaw P μ Y) (h : KernelBounds H δ U) :
    OverlapVariance.KernelMoments P (fun i j ω => H (Y i ω) (Y j ω))
      (variance (Function.uncurry H) (μ.prod μ)) (variance (projection μ H) μ) where
  squareIntegrable i j := h.memLp_pair P (hx.marginal i).measurable (hx.marginal j).measurable
  diagonal i := ⟨δ, Eventually.of_forall fun ω => h.diagonal (Y i ω)⟩
  symmetric i j := Eventually.of_forall fun ω => h.symmetric (Y i ω) (Y j ω)
  offDiag_variance _ _ hij := variance_of_law (hx.pair_law hij) h.measurable
  shared_covariance _ _ _ hij hil hjl := shared_covariance hx h hij hil hjl
  disjoint_indep _ _ _ _ _ _ hki hkj hli hlj := disjoint_entries hx h hki.symm hli.symm hkj.symm hlj.symm

theorem expectation_statistic (hn : 0 < n) (hx : SampleLaw P μ Y) (h : KernelBounds H δ U) :
    (∫ ω, statistic H Y ω ∂P) = rowMean μ H δ n := by
  have he := Expectation.eq41_of_pairwise_indep P μ hn Y hx.marginal
    (fun {_ _} hij => hx.independent.indepFun hij) (Function.uncurry H) δ
    ((h.memLp_pair _ measurable_fst measurable_snd).integrable one_le_two)
    (Eventually.of_forall h.diagonal)
  simpa only [statistic, OverlapVariance.pairAverage, Expectation.pairAverage, rowMean,
    Function.uncurry_def, div_eq_mul_inv, mul_comm] using he

theorem variance_statistic (hn : 0 < n) (hx : SampleLaw P μ Y) (h : KernelBounds H δ U) :
    (n : ℝ) ^ 4 * variance (statistic H Y) P =
      2 * n * (n - 1 : ℝ) * variance (Function.uncurry H) (μ.prod μ) +
      4 * n * (n - 1 : ℝ) * (n - 2 : ℝ) * variance (projection μ H) μ :=
  OverlapVariance.variance_pairAverage hn (kernel_moments hx h)

/-- Upper bound by the two population second moments, with explicit coefficients. -/
theorem variance_le_second_moments (hn : 2 ≤ n) (hx : SampleLaw P μ Y) (h : KernelBounds H δ U) :
    variance (statistic H Y) P ≤
      2 * (∫ z, (Function.uncurry H z) ^ 2 ∂μ.prod μ) / (n : ℝ) ^ 2 +
      4 * (∫ x, (projection μ H x) ^ 2 ∂μ) / n := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  have hv := variance_nonneg (Function.uncurry H) (μ.prod μ)
  have hq := variance_nonneg (projection μ H) μ
  have hv' := variance_le_expectation_sq (μ := μ.prod μ) h.measurable.aestronglyMeasurable
  have hq' := variance_le_expectation_sq (μ := μ) (h.measurable_projection μ).aestronglyMeasurable
  simp only [Pi.pow_apply] at hv' hq'
  apply le_of_mul_le_mul_left _ (pow_pos hn0 4)
  calc
    _ = _ := variance_statistic (by omega) hx h
    _ ≤ 2 * (n : ℝ) * n * variance (Function.uncurry H) (μ.prod μ) +
        4 * n * n * n * variance (projection μ H) μ := by
      gcongr <;> linarith
    _ ≤ 2 * (n : ℝ) * n * (∫ z, (Function.uncurry H z) ^ 2 ∂μ.prod μ) +
        4 * n * n * n * (∫ x, (projection μ H x) ^ 2 ∂μ) := by gcongr
    _ = _ := by field_simp [hn0.ne']; ring

/-- A pointwise loss envelope and an almost-everywhere envelope on its one-coordinate
mean suffice for every iid row. The bounds and kernel may change between rows. -/
theorem variance_le_envelopes {Q : ℝ} (hn : 2 ≤ n) (hx : SampleLaw P μ Y)
    (h : KernelBounds H δ U) (hQ : ∀ᵐ x ∂μ, projection μ H x ≤ Q) :
    variance (statistic H Y) P ≤ 2 * U * Q / (n : ℝ) ^ 2 + 4 * Q ^ 2 / n := by
  obtain ⟨x, _⟩ := hQ.exists
  have hU : 0 ≤ U := (h.nonneg x x).trans (h.le_upper x x)
  have hmean : (∫ x, projection μ H x ∂μ) ≤ Q := by
    simpa using integral_mono_of_nonneg (ae_of_all _ (h.projection_nonneg μ))
      (integrable_const Q) hQ
  have hsecond : (∫ z, (Function.uncurry H z) ^ 2 ∂μ.prod μ) ≤ U * Q := by
    calc
      _ ≤ ∫ z, U * Function.uncurry H z ∂μ.prod μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _)
          (((h.memLp_pair _ measurable_fst measurable_snd).integrable one_le_two).const_mul U)
        exact ae_of_all _ fun z => by
          change (H z.1 z.2) ^ 2 ≤ U * H z.1 z.2
          rw [sq]
          exact mul_le_mul_of_nonneg_right (h.le_upper _ _) (h.nonneg _ _)
      _ = U * ∫ x, projection μ H x ∂μ := by rw [integral_const_mul, h.pair_mean_eq μ]
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean hU
  have hproj : (∫ x, (projection μ H x) ^ 2 ∂μ) ≤ Q ^ 2 := by
    simpa using integral_mono_of_nonneg (ae_of_all μ fun x => sq_nonneg (projection μ H x))
      (integrable_const (Q ^ 2)) (hQ.mono fun x hx => pow_le_pow_left₀ (h.projection_nonneg μ x) hx 2)
  refine (variance_le_second_moments hn hx h).trans ?_
  rw [mul_assoc 2 U Q]
  gcongr

omit [IsProbabilityMeasure μ] in
theorem statistic_memLp (hx : SampleLaw P μ Y) (h : KernelBounds H δ U) :
    MemLp (statistic H Y) 2 P :=
  (memLp_finset_sum Finset.univ fun i _ => memLp_finset_sum Finset.univ fun j _ =>
    h.memLp_pair P (hx.marginal i).measurable (hx.marginal j).measurable).const_mul _

/-- Chebyshev at any positive threshold, centered at the exact deterministic row mean. -/
theorem chebyshev_envelopes {Q t : ℝ} (hn : 2 ≤ n) (hx : SampleLaw P μ Y)
    (h : KernelBounds H δ U) (hQ : ∀ᵐ x ∂μ, projection μ H x ≤ Q) (ht : 0 < t) :
    P.real {ω | t ≤ |statistic H Y ω - rowMean μ H δ n|} ≤
      (2 * U * Q / (n : ℝ) ^ 2 + 4 * Q ^ 2 / n) / t ^ 2 := by
  have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (meas_ge_le_variance_div_sq (statistic_memLp hx h) ht)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg t))] at hp
  rw [← expectation_statistic (by omega) hx h]
  exact hp.trans (div_le_div_of_nonneg_right (variance_le_envelopes hn hx h hQ) (sq_nonneg t))

/-- Centered relative deviation for an arbitrary positive deterministic scale. -/
theorem relative_chebyshev_envelopes {Q scale ε : ℝ} (hn : 2 ≤ n) (hx : SampleLaw P μ Y)
    (h : KernelBounds H δ U) (hQ : ∀ᵐ x ∂μ, projection μ H x ≤ Q)
    (hs : 0 < scale) (hε : 0 < ε) :
    P.real {ω | ε ≤ |(statistic H Y ω - rowMean μ H δ n) / scale|} ≤
      (2 * U * Q / (n : ℝ) ^ 2 + 4 * Q ^ 2 / n) / (ε * scale) ^ 2 := by
  simpa only [abs_div, abs_of_pos hs, le_div_iff₀ hs] using
    chebyshev_envelopes hn hx h hQ (mul_pos hε hs)

end MaternAudit.IIDVariance
