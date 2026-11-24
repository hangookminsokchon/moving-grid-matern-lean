import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The diagonal correction to equation (41)

`pairAverage` averages a real-valued loss over all ordered pairs of sample
indices. Under pairwise independence the off-diagonal terms have law `μ.prod μ`;
the diagonal terms evaluate the loss along `x ↦ (x, x)`. Both integrals are
taken under their own laws, which matters even for Borel laws without atoms.
-/

namespace MaternAudit.Expectation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] {N : ℕ}

/-- Mean of the entries of the loss matrix for the sample `x`. -/
noncomputable def pairAverage (L : S × S → ℝ) (x : Fin N → S) : ℝ :=
  (∑ i, ∑ j, L (x i, x j)) / (N : ℝ) ^ 2

/-- Projection onto one coordinate of the canonical finite product has law `μ`. -/
theorem product_marginal (μ : Measure S) [IsProbabilityMeasure μ] (i : Fin N) :
    MeasurePreserving (fun x : Fin N → S => x i) (Measure.pi fun _ : Fin N => μ) μ := by
  classical
  refine ⟨measurable_pi_apply i, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  change (Measure.pi fun _ : Fin N => μ) (Function.eval i ⁻¹' s) = μ s
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  simp [Function.update_apply, apply_ite]

/-- All coordinate projections of the finite product are mutually independent. -/
theorem product_independent (μ : Measure S) [IsProbabilityMeasure μ] (N : ℕ) :
    iIndepFun (fun (i : Fin N) (x : Fin N → S) => x i) (Measure.pi fun _ : Fin N => μ) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).2
  change (Measure.pi fun _ : Fin N => μ).map id = _
  rw [Measure.map_id]
  exact congrArg Measure.pi (funext fun i => (product_marginal μ i).map_eq.symm)

private theorem pullback_integral {P : Measure Ω} {ν : Measure S} {f : Ω → S} {g : S → ℝ}
    (hf : MeasurePreserving f P ν) (hg : Integrable g ν) :
    Integrable (fun ω => g (f ω)) P ∧ (∫ ω, g (f ω) ∂P) = ∫ x, g x ∂ν := by
  refine ⟨(hf.integrable_comp hg.aestronglyMeasurable).2 hg, ?_⟩
  rw [← hf.map_eq] at hg ⊢
  exact (integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable).symm

/-- On any probability space, pairwise independence and the common marginal
law suffice. The diagonal may depend on the sampled value. -/
theorem integral_pairAverage (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (hN : 0 < N) (X : Fin N → Ω → S)
    (hX : ∀ i, MeasurePreserving (X i) P μ)
    (hind : Pairwise fun i j => IndepFun (X i) (X j) P)
    (L : S × S → ℝ) (hL : Integrable L (μ.prod μ))
    (hdiag : Integrable (fun x => L (x, x)) μ) :
    (∫ ω, pairAverage L (fun i => X i ω) ∂P) =
      (∫ x, L (x, x) ∂μ) / N + (1 - 1 / (N : ℝ)) * ∫ z, L z ∂(μ.prod μ) := by
  let D := ∫ x, L (x, x) ∂μ
  let B := ∫ z, L z ∂(μ.prod μ)
  have entry (i j : Fin N) :
      Integrable (fun ω => L (X i ω, X j ω)) P ∧
      (∫ ω, L (X i ω, X j ω) ∂P) = (if j = i then D - B else 0) + B := by
    by_cases hij : i = j
    · subst j
      rw [if_pos (rfl : i = i), sub_add_cancel]
      exact pullback_integral (hX i) hdiag
    · have hjoint : MeasurePreserving (fun ω => (X i ω, X j ω)) P (μ.prod μ) := by
        refine ⟨(hX i).measurable.prodMk (hX j).measurable, ?_⟩
        rw [(indepFun_iff_map_prod_eq_prod_map_map (hX i).measurable.aemeasurable
          (hX j).measurable.aemeasurable).1 (hind hij), (hX i).map_eq, (hX j).map_eq]
      simpa only [if_neg (Ne.symm hij), zero_add] using pullback_integral hjoint hL
  have row (i : Fin N) :
      (∫ ω, ∑ j, L (X i ω, X j ω) ∂P) = D - B + (N : ℝ) * B := by
    rw [integral_finset_sum Finset.univ (fun j _ => (entry i j).1)]
    simp_rw [fun j => (entry i j).2]
    simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hrow (i : Fin N) : Integrable (fun ω => ∑ j, L (X i ω, X j ω)) P :=
    integrable_finset_sum Finset.univ fun j _ => (entry i j).1
  unfold pairAverage
  rw [integral_div, integral_finset_sum Finset.univ (fun i _ => hrow i)]
  simp_rw [row]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change N * (D - B + N * B) / (N : ℝ) ^ 2 = D / N + (1 - 1 / (N : ℝ)) * B
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp [hNr]
  ring

/-- Constant-diagonal form on an arbitrary probability space. Constancy
`μ`-almost everywhere on the diagonal suffices. -/
theorem eq41_of_pairwise_indep (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure S) [IsProbabilityMeasure μ] (hN : 0 < N) (X : Fin N → Ω → S)
    (hX : ∀ i, MeasurePreserving (X i) P μ)
    (hind : Pairwise fun i j => IndepFun (X i) (X j) P)
    (L : S × S → ℝ) (d : ℝ) (hL : Integrable L (μ.prod μ))
    (hd : ∀ᵐ x ∂μ, L (x, x) = d) :
    (∫ ω, pairAverage L (fun i => X i ω) ∂P) =
      d / N + (1 - 1 / (N : ℝ)) * ∫ z, L z ∂(μ.prod μ) := by
  have hconst : (fun x => L (x, x)) =ᵐ[μ] (fun _ => d) := hd
  have hdiag := (integrable_const d (μ := μ)).congr hconst.symm
  rw [integral_pairAverage P μ hN X hX hind L hL hdiag, integral_congr_ae hconst]
  simp

/-- Under the canonical iid product the common marginal and independence are
consequences of `Measure.pi`. -/
theorem eq41_pi (μ : Measure S) [IsProbabilityMeasure μ] (hN : 0 < N)
    (L : S × S → ℝ) (d : ℝ) (hL : Integrable L (μ.prod μ))
    (hd : ∀ᵐ x ∂μ, L (x, x) = d) :
    (∫ x, pairAverage L x ∂(Measure.pi fun _ : Fin N => μ)) =
      d / N + (1 - 1 / (N : ℝ)) * ∫ z, L z ∂(μ.prod μ) :=
  eq41_of_pairwise_indep (Measure.pi fun _ : Fin N => μ) μ hN
    (fun (i : Fin N) (x : Fin N → S) => x i) (fun i => product_marginal μ i)
    (fun {_ _} hij => (product_independent μ N).indepFun hij) L d hL hd

/-- For a real error function of the lag, the diagonal loss is `(e 0)²`.
The state space may be the real line or a Euclidean space of locations. -/
theorem eq41_squared_error [AddGroup S] (μ : Measure S) [IsProbabilityMeasure μ]
    (hN : 0 < N) (e : S → ℝ) (he : Integrable (fun z : S × S => e (z.1 - z.2) ^ 2) (μ.prod μ)) :
    (∫ x : Fin N → S, (∑ i, ∑ j, e (x i - x j) ^ 2) / (N : ℝ) ^ 2
      ∂(Measure.pi fun _ : Fin N => μ)) =
      e 0 ^ 2 / N + (1 - 1 / (N : ℝ)) * ∫ z : S × S, e (z.1 - z.2) ^ 2 ∂(μ.prod μ) :=
  eq41_pi μ hN (fun z => e (z.1 - z.2) ^ 2) (e 0 ^ 2) he (by simp)

end MaternAudit.Expectation
