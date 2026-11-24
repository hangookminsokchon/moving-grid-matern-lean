import MaternAudit.FullCovariance
import Mathlib.Probability.ProductMeasure

/-!
# Moving-grid Matérn limits for triangular arrays

Row `n` consists of `g.N n` independent draws from the same spatial design law.
Its probability space may depend on `n`. The joint law within each row is the
finite product, which is also the law of the corresponding prefix of a single
sequence of coordinate draws on the infinite product.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace MaternAudit.TriangularRows

open MaternParameters MaternProfile PairSpectrum IIDVariance

/-- Coordinate draws under the infinite product realize an iid reference family. -/
theorem sampleLaw_infinitePi {ι S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] :
    SampleLaw (Measure.infinitePi (fun _ : ι ↦ μ)) μ (fun i (x : ι → S) ↦ x i) := by
  classical
  have marginal (i : ι) (s : Set S) (hs : MeasurableSet s) :
      Measure.infinitePi (fun _ : ι ↦ μ) ((fun x : ι → S ↦ x i) ⁻¹' s) = μ s := by
    have he : (fun x : ι → S ↦ x i) ⁻¹' s =
        Set.pi (↑({i} : Finset ι)) (fun _ ↦ s) := by
      ext x
      simp [Set.mem_pi]
    rw [he]
    simpa using (Measure.infinitePi_pi (fun _ : ι ↦ μ) (s := {i})
      (t := fun _ ↦ s) (fun _ _ ↦ hs))
  constructor
  · intro i
    refine ⟨measurable_pi_apply i, Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply (measurable_pi_apply i) hs]
    exact marginal i s hs
  · apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro I sets hsets
    have he : (⋂ i ∈ I, (fun x : ι → S ↦ x i) ⁻¹' sets i) = Set.pi (↑I) sets := by
      ext x
      simp [Set.mem_pi]
    rw [he, Measure.infinitePi_pi (fun _ : ι ↦ μ) hsets]
    exact Finset.prod_congr rfl fun i hi ↦ (marginal i (sets i) (hsets i hi)).symm

/-- The vector of all observations in one iid row has its finite product law. -/
theorem measurePreserving_rowVector {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    {P : Measure A} [IsProbabilityMeasure P] {μ : Measure S} [IsProbabilityMeasure μ]
    {N : ℕ} {X : Fin N → A → S} (hx : SampleLaw P μ X) :
    MeasurePreserving (fun ω i ↦ X i ω) P (Measure.pi (fun _ : Fin N ↦ μ)) := by
  refine ⟨measurable_pi_lambda _ fun i ↦ (hx.marginal i).measurable, ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hx.marginal i).measurable.aemeasurable)).1
    hx.independent]
  exact congrArg Measure.pi (funext fun i ↦ (hx.marginal i).map_eq)

/-- Two iid rows of equal size and common design law have identical joint distributions. -/
theorem identDistrib_rowVectors {A B S : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace S]
    {P : Measure A} [IsProbabilityMeasure P] {Q : Measure B} [IsProbabilityMeasure Q]
    {μ : Measure S} [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → A → S} {Y : Fin N → B → S}
    (hx : SampleLaw P μ X) (hy : SampleLaw Q μ Y) :
    IdentDistrib (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) P Q := by
  have hX := measurePreserving_rowVector hx
  have hY := measurePreserving_rowVector hy
  exact ⟨hX.measurable.aemeasurable, hY.measurable.aemeasurable, hX.map_eq.trans hY.map_eq.symm⟩

variable {d : ℕ}

/-- Mean squared Fourier-tail entries over all ordered pairs of a finite row. -/
def rowTailEnergy (g : Grid) (ν : ℝ) (n : ℕ) : (Fin (g.N n) → E d) → ℝ :=
  statistic (physicalLoss (g.h n) (omitted ν (g.len n) (g.h n) (g.m n))) (fun i x ↦ x i)

/-- Frobenius RMS of the finite Fourier matrix minus the inverse Fourier covariance on a row. -/
def rowFullRMS (g : Grid) (ν : ℝ) (n : ℕ) (x : Fin (g.N n) → E d) : ℝ :=
  AliasTransfer.sampleRMS fun i j : Fin (g.N n) ↦
    PhysicalKernel.finiteGrid ν (g.len n) (g.h n) (g.m n) (x i) (x j) -
      PhysicalKernel.kernel ν (g.len n) (x i - x j)

private theorem measurable_pairSum {S : Type*} [MeasurableSpace S] {N : ℕ}
    {f : S × S → ℝ} (hf : Measurable f) :
    Measurable (fun x : Fin N → S ↦ ∑ i, ∑ j, f (x i, x j)) := by
  have pair (i j : Fin N) : Measurable (fun x : Fin N → S ↦ f (x i, x j)) := by
    change Measurable (f ∘ fun x : Fin N → S ↦ (x i, x j))
    exact hf.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦ pair i j

theorem measurable_rowTailEnergy (g : Grid) {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    Measurable (rowTailEnergy (d := d) g ν n) := by
  let c := omitted (d := d) ν (g.len n) (g.h n) (g.m n)
  have he : c = fun j ↦ amplitude d ν (g.len n) (g.R n) * PopulationLimit.coeff g ν n j :=
    funext (PopulationLimit.omitted_eq_amplitude_mul_coeff g ν n)
  have ha : 0 < amplitude d ν (g.len n) (g.R n) := mul_pos (cInfinity_pos hν)
    (Real.rpow_pos_of_pos (mul_pos (g.len_pos n) (g.R_pos n)) _)
  have hn (j) : 0 ≤ c j := by rw [he]; exact mul_nonneg ha.le (PopulationLimit.coeff_nonneg g ν n j)
  have hc : Summable c := he ▸ (PopulationLimit.summable_coeff g hν n).mul_left _
  have hm := (kernelBounds (g.h n) hn hc).measurable
  exact (measurable_pairSum (N := g.N n) hm).const_mul _

theorem measurable_rowFullRMS (g : Grid) (ν : ℝ) (n : ℕ) :
    Measurable (rowFullRMS (d := d) g ν n) := by
  let entry (p : E d × E d) := PhysicalKernel.finiteGrid ν (g.len n) (g.h n) (g.m n) p.1 p.2 -
    PhysicalKernel.kernel ν (g.len n) (p.1 - p.2)
  have he : Measurable entry := PhysicalKernel.measurable_error ν (g.len n) (g.h n) (g.m n)
  change Measurable fun x : Fin (g.N n) → E d ↦ AliasTransfer.sampleRMS (fun i j ↦ entry (x i, x j))
  simp only [AliasTransfer.sampleRMS_eq_sqrt_mean_sq]
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_pairSum (N := g.N n) (he.norm.pow_const 2)).div_const _)

private theorem deviation_eq {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure A} {Q : Measure B} {F : A → ℝ} {G : B → ℝ}
    (h : IdentDistrib F G P Q) (L ε : ℝ) :
    P.real {ω | ε ≤ |F ω / L - 1|} = Q.real {ω | ε ≤ |G ω / L - 1|} := by
  have hs : MeasurableSet {x : ℝ | ε ≤ |x / L - 1|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      ((measurable_id.div_const L).sub_const 1))
  exact congrArg ENNReal.toReal (h.measure_mem_eq hs)

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Sharp squared expectation and RMS probability limits for the Matérn tail on iid rows.
The rows may be coupled on a common space or sampled on different spaces. -/
theorem movingMatern_sharp_rows (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin (g.N n) → Ω n → E d} (hx : ∀ n, SampleLaw (P n) D.μ (X n)) :
    Tendsto (fun n ↦ (∫ ω, rowTailEnergy g ν n (fun i ↦ X n i ω) ∂P n) /
      MovingMatern.leadingSq g ν D n) atTop (𝓝 1) ∧
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (P n).real {ω |
      ε ≤ |Real.sqrt (rowTailEnergy g ν n (fun i ↦ X n i ω)) /
        Real.sqrt (MovingMatern.leadingSq g ν D n) - 1|}) atTop (𝓝 0) := by
  let Q := Measure.infinitePi (fun _ : ℕ ↦ D.μ)
  let coord (i : ℕ) (x : ℕ → E d) := x i
  have href : SampleLaw Q D.μ coord := sampleLaw_infinitePi D.μ
  obtain ⟨he, hp⟩ := MovingMatern.movingMatern_sharp hd hν g D href
  have law (n : ℕ) : IdentDistrib (MovingMatern.tailEnergy g ν coord n)
      (fun ω ↦ rowTailEnergy g ν n (fun i ↦ X n i ω)) Q (P n) :=
    (identDistrib_rowVectors (href.first (g.N n)) (hx n)).comp (measurable_rowTailEnergy g hν n)
  constructor
  · exact he.congr fun n ↦ congrArg (fun z ↦ z / MovingMatern.leadingSq g ν D n) (law n).integral_eq
  · intro ε hε
    exact (hp ε hε).congr fun n ↦ deviation_eq ((law n).comp Real.continuous_sqrt.measurable) _ ε

/-- Sharp squared expectation and RMS probability limits for the full covariance error on
iid rows, under the uniform alias bound and little-o condition of the original theorem. -/
theorem movingMatern_full_sharp_rows (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin (g.N n) → Ω n → E d} (hx : ∀ n, SampleLaw (P n) D.μ (X n))
    (η : ℕ → ℝ) (hbound : ∀ n, PhysicalKernel.AliasBound d ν (g.len n) (g.h n) (η n))
    (hsmall : Tendsto (fun n ↦ η n / FullCovariance.baseRate d ν g n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (∫ ω, rowFullRMS g ν n (fun i ↦ X n i ω) ^ 2 ∂P n) /
      MovingMatern.leadingSq g ν D n) atTop (𝓝 1) ∧
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ (P n).real {ω |
      ε ≤ |rowFullRMS g ν n (fun i ↦ X n i ω) /
        Real.sqrt (MovingMatern.leadingSq g ν D n) - 1|}) atTop (𝓝 0) := by
  let Q := Measure.infinitePi (fun _ : ℕ ↦ D.μ)
  let coord (i : ℕ) (x : ℕ → E d) := x i
  have href : SampleLaw Q D.μ coord := sampleLaw_infinitePi D.μ
  obtain ⟨he, hp⟩ := FullCovariance.movingMatern_full_sharp hd hν g D href η hbound hsmall
  have law (n : ℕ) : IdentDistrib (FullCovariance.fullRMS g ν coord n)
      (fun ω ↦ rowFullRMS g ν n (fun i ↦ X n i ω)) Q (P n) :=
    (identDistrib_rowVectors (href.first (g.N n)) (hx n)).comp (measurable_rowFullRMS g ν n)
  constructor
  · exact he.congr fun n ↦ congrArg (fun z ↦ z / MovingMatern.leadingSq g ν D n) (law n).sq.integral_eq
  · intro ε hε
    exact (hp ε hε).congr fun n ↦ deviation_eq (law n) _ ε

end MaternAudit.TriangularRows
