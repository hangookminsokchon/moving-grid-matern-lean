import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Uniform tightness for sampled Fourier energy at all grid spacings in (0, 1].
The shift is measured in physical coordinates. -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace MaternAudit.SampleTightness

/-- A point on a lattice of spacing `H` with physical shift `α`. -/
abbrev samplePoint {d : ℕ} (H : ℝ) (α : Fin d → ℝ) (k : Fin d → ℤ) : Fin d → ℝ :=
  fun i ↦ H * (k i : ℝ) + α i

/-- Finite partial sums with a common pointwise total exhaust that total
uniformly on a compact parameter space. -/
private theorem compact_partial_mass {X ι : Type*} [TopologicalSpace X] [CompactSpace X]
    (u : ι → X → ℝ) (hc : ∀ k, Continuous (u k)) (hn : ∀ k x, 0 ≤ u k x)
    (I : ℝ) (ht : ∀ x, HasSum (fun k ↦ u k x) I) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ι, ∀ x, I - ε < ∑ k ∈ S, u k x := by
  classical
  let U (S : Finset ι) : Set X := {x | I - ε < ∑ k ∈ S, u k x}
  have hopen S : IsOpen (U S) :=
    isOpen_lt continuous_const (continuous_finset_sum S fun k _ ↦ hc k)
  have hcover : Set.univ ⊆ ⋃ S, U S := by
    intro x _
    apply Set.mem_iUnion.mpr
    exact ((ht x).eventually (eventually_gt_nhds (sub_lt_self I hε))).exists
  have hmono : Monotone U := by
    intro S T hST x hx
    exact lt_of_lt_of_le hx (Finset.sum_mono_set_of_nonneg (fun k ↦ hn k x) hST)
  obtain ⟨S, hS⟩ := isCompact_univ.elim_directed_cover U hopen hcover hmono.directed_le
  exact ⟨S, fun x ↦ hS (Set.mem_univ x)⟩

/-- Reconstruct an integer lattice index from its coordinatewise residues and quotients. -/
def residueEquiv (d s : ℕ) [NeZero s] :
    ((Fin d → Fin s) × (Fin d → ℤ)) ≃ (Fin d → ℤ) :=
  ((Equiv.piCongrRight (fun _ : Fin d ↦ Int.divModEquiv s)).trans
    ((Equiv.arrowProdEquivProdArrow (Fin d) (fun _ ↦ ℤ) (fun _ ↦ Fin s)).trans
      (Equiv.prodComm _ _))).symm

@[simp] theorem residueEquiv_apply {d s : ℕ} [NeZero s] (b : Fin d → Fin s)
    (k : Fin d → ℤ) (i : Fin d) :
    residueEquiv d s (b, k) i = k i * (s : ℤ) + ((b i).val : ℤ) := rfl

/-- Regroup a nonnegative sum by residue vectors. Summability on each coarse
lattice suffices because there are finitely many residue vectors. -/
theorem tsum_residues {d : ℕ} (s : ℕ) [NeZero s] (u : (Fin d → ℤ) → ℝ)
    (hn : ∀ r, 0 ≤ u r)
    (hs : ∀ b, Summable (fun k ↦ u (residueEquiv d s (b, k)))) :
    (∑' r, u r) = ∑ b, ∑' k, u (residueEquiv d s (b, k)) := by
  let v := u ∘ residueEquiv d s
  have hv : Summable v :=
    (summable_prod_of_nonneg (f := v) (fun p ↦ hn _)).2 ⟨hs, (hasSum_fintype _).summable⟩
  calc
    (∑' r, u r) = ∑' p, v p := ((residueEquiv d s).tsum_eq u).symm
    _ = ∑' b, ∑' k, v (b, k) := hv.tsum_prod
    _ = _ := tsum_fintype _

private theorem exists_coarse_spacing {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    ∃ s : ℕ, 0 < s ∧ h * s ∈ Set.Icc (1/2 : ℝ) 1 := by
  let s := ⌊1 / h⌋₊
  have hs : 1 ≤ s := (Nat.one_le_floor_iff _).mpr ((one_le_div hh).mpr h1)
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hu : (s : ℝ) ≤ 1 / h := Nat.floor_le (by positivity)
  have hl : 1 / h < (s : ℝ) + 1 := Nat.lt_floor_add_one _
  have hu' := (le_div_iff₀ hh).mp hu
  have hl' := (div_lt_iff₀ hh).mp hl
  refine ⟨s, hs, ?_, ?_⟩
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs') hh.le]
  · simpa [mul_comm] using hu'


/-- Physical energy outside the closed sup-norm ball of radius `K`. -/
abbrev tailEnergy {d : ℕ} (f : (Fin d → ℝ) → ℂ) (K : ℝ) (x : Fin d → ℝ) : ℝ :=
  if K < ‖x‖ then ‖f x‖ ^ 2 else 0

private theorem tailEnergy_nonneg {d : ℕ} (f : (Fin d → ℝ) → ℂ) (K : ℝ) (x : Fin d → ℝ) :
    0 ≤ tailEnergy f K x := by
  unfold tailEnergy
  split <;> positivity

private theorem tailEnergy_le {d : ℕ} (f : (Fin d → ℝ) → ℂ) (K : ℝ) (x : Fin d → ℝ) :
    tailEnergy f K x ≤ ‖f x‖ ^ 2 := by
  unfold tailEnergy
  split
  · exact le_rfl
  · exact sq_nonneg _

private theorem sum_add_tail_le {ι : Type*} (S : Finset ι) {u v : ι → ℝ}
    (hu : Summable u) (hv : Summable v) (hle : ∀ k, v k ≤ u k) (hz : ∀ k ∈ S, v k = 0) :
    (∑ k ∈ S, u k) + ∑' k, v k ≤ ∑' k, u k := by
  apply le_sub_iff_add_le.mp
  calc
    (∑ k ∈ S, u k) = ∑ k ∈ S, (u k - v k) :=
      Finset.sum_congr rfl fun k hk ↦ by rw [hz k hk, sub_zero]
    _ ≤ ∑' k, (u k - v k) := (hu.sub hv).sum_le_tsum S fun k _ ↦ sub_nonneg.mpr (hle k)
    _ = _ := hu.tsum_sub hv

/-- On the compact family of spacings and physical shifts, a single physical
radius captures all but `ε` of the normalized sampled energy. -/
theorem uniform_coarse_tail {d : ℕ} (f : (Fin d → ℝ) → ℂ) (hf : Continuous f) (I : ℝ)
    (hsum : ∀ H ∈ Set.Icc (1/2 : ℝ) 1, ∀ α : Fin d → ℝ, (∀ i, α i ∈ Set.Icc (0:ℝ) 1) →
      Summable (fun k : Fin d → ℤ ↦ ‖f (samplePoint H α k)‖ ^ 2))
    (hparseval : ∀ H ∈ Set.Icc (1/2 : ℝ) 1, ∀ α : Fin d → ℝ, (∀ i, α i ∈ Set.Icc (0:ℝ) 1) →
      H ^ d * (∑' k : Fin d → ℤ, ‖f (samplePoint H α k)‖ ^ 2) = I)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H ∈ Set.Icc (1/2 : ℝ) 1, ∀ α : Fin d → ℝ,
      (∀ i, α i ∈ Set.Icc (0:ℝ) 1) →
      H ^ d * (∑' k : Fin d → ℤ, tailEnergy f K (samplePoint H α k)) ≤ ε := by
  classical
  let P := Set.Icc (1/2 : ℝ) 1 × (Fin d → Set.Icc (0:ℝ) 1)
  let u (k : Fin d → ℤ) (p : P) :=
    (p.1 : ℝ) ^ d * ‖f (samplePoint p.1 (fun i ↦ p.2 i) k)‖ ^ 2
  have hc (k) : Continuous (u k) := by
    dsimp [u, samplePoint, P]
    fun_prop
  have hnon (k) (p : P) : 0 ≤ u k p :=
    mul_nonneg (pow_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 1/2) p.1.property.1) _) (sq_nonneg _)
  have ht (p : P) : HasSum (fun k ↦ u k p) I := by
    rw [← hparseval p.1 p.1.property (fun i ↦ p.2 i) (fun i ↦ (p.2 i).property)]
    exact (hsum p.1 p.1.property (fun i ↦ p.2 i) (fun i ↦ (p.2 i).property)).hasSum.mul_left _
  obtain ⟨S, hS⟩ := compact_partial_mass u hc hnon I ht hε
  let rad (k : Fin d → ℤ) := ‖fun i ↦ (k i : ℝ)‖
  let K := (∑ k ∈ S, rad k) + 1
  refine ⟨K, add_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) zero_le_one, ?_⟩
  intro H hH α hα
  let p : P := (⟨H,hH⟩, fun i ↦ ⟨α i,hα i⟩)
  let g (k : Fin d → ℤ) := ‖f (samplePoint H α k)‖ ^ 2
  let v (k : Fin d → ℤ) := tailEnergy f K (samplePoint H α k)
  have hfinite : I - ε < H ^ d * ∑ k ∈ S, g k := by
    simpa only [p, u, g, Finset.mul_sum] using hS p
  have hH0 : 0 ≤ H := le_trans (by norm_num : (0:ℝ) ≤ 1/2) hH.1
  have hαnorm : ‖α‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hα i).1] using (hα i).2
  have hzero (k) (hk : k ∈ S) : v k = 0 := by
    apply if_neg
    apply not_lt.mpr
    calc
      ‖samplePoint H α k‖ ≤ ‖H • (fun i ↦ (k i : ℝ))‖ + ‖α‖ :=
        norm_add_le (H • (fun i ↦ (k i : ℝ))) α
      _ ≤ rad k + 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hH0]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hH.2) hαnorm
      _ ≤ K := add_le_add_right (Finset.single_le_sum (f := rad) (fun _ _ ↦ norm_nonneg _) hk) 1
  have hgs : Summable g := hsum H hH α hα
  have hvg (k) : v k ≤ g k := tailEnergy_le _ _ _
  have hvs : Summable v := .of_nonneg_of_le (fun k ↦ tailEnergy_nonneg _ _ _) hvg hgs
  have hbound := mul_le_mul_of_nonneg_left (sum_add_tail_le S hgs hvs hvg hzero) (pow_nonneg hH0 d)
  have htotal : H ^ d * (∑' k, g k) = I := hparseval H hH α hα
  rw [mul_add, htotal] at hbound
  change H ^ d * (∑' k, v k) ≤ ε
  linarith

/-- Uniform tightness over all fine spacings `0 < h ≤ 1`. The sole analytic
inputs are continuity and the shifted sampled Parseval identity (with summability)
on coarse grids of spacing in `[1/2,1]`. The norm of a lattice point is the sup norm. -/
theorem uniform_sampled_energy_tight {d : ℕ} (f : (Fin d → ℝ) → ℂ) (hf : Continuous f) (I : ℝ)
    (hsum : ∀ H ∈ Set.Icc (1/2 : ℝ) 1, ∀ α : Fin d → ℝ, (∀ i, α i ∈ Set.Icc (0:ℝ) 1) →
      Summable (fun k : Fin d → ℤ ↦ ‖f (samplePoint H α k)‖ ^ 2))
    (hparseval : ∀ H ∈ Set.Icc (1/2 : ℝ) 1, ∀ α : Fin d → ℝ, (∀ i, α i ∈ Set.Icc (0:ℝ) 1) →
      H ^ d * (∑' k : Fin d → ℤ, ‖f (samplePoint H α k)‖ ^ 2) = I)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      h ^ d * (∑' r : Fin d → ℤ, if K < ‖fun i ↦ h * (r i : ℝ)‖ then
        ‖f (fun i ↦ h * (r i : ℝ))‖ ^ 2 else 0) ≤ ε := by
  classical
  obtain ⟨K, hK, htail⟩ := uniform_coarse_tail f hf I hsum hparseval ε hε
  refine ⟨K, hK, ?_⟩
  intro h hh h1
  obtain ⟨s, hs, hH⟩ := exists_coarse_spacing hh h1
  letI : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let H := h * (s : ℝ)
  let α (b : Fin d → Fin s) (i : Fin d) : ℝ := h * ((b i).val : ℝ)
  have hα (b : Fin d → Fin s) (i : Fin d) : α b i ∈ Set.Icc (0:ℝ) 1 := by
    have hb : ((b i).val : ℝ) ≤ s := by exact_mod_cast (b i).isLt.le
    exact ⟨mul_nonneg hh.le (Nat.cast_nonneg _), (mul_le_mul_of_nonneg_left hb hh.le).trans hH.2⟩
  let x (r : Fin d → ℤ) (i : Fin d) : ℝ := h * (r i : ℝ)
  have hpoint (b : Fin d → Fin s) (k : Fin d → ℤ) :
      x (residueEquiv d s (b, k)) = samplePoint H (α b) k := by
    funext i
    simp only [x, samplePoint, residueEquiv_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast, H, α]
    ring
  let v (r : Fin d → ℤ) := tailEnergy f K (x r)
  have hrow (b : Fin d → Fin s) : Summable (fun k ↦ v (residueEquiv d s (b, k))) := by
    simp only [v, hpoint]
    exact .of_nonneg_of_le (fun k ↦ tailEnergy_nonneg _ _ _) (fun k ↦ tailEnergy_le _ _ _)
      (hsum H hH (α b) (hα b))
  have hbnd (b : Fin d → Fin s) : H ^ d * (∑' k, v (residueEquiv d s (b, k))) ≤ ε := by
    simpa only [v, hpoint] using htail H hH (α b) (hα b)
  have hfac : (s : ℝ) ^ d * h ^ d = H ^ d := by rw [← mul_pow, mul_comm]
  change h ^ d * (∑' r, v r) ≤ ε
  rw [tsum_residues s v (fun r ↦ tailEnergy_nonneg _ _ _) hrow]
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  apply le_of_mul_le_mul_left _ (pow_pos hspos d)
  calc
    (s : ℝ) ^ d * (h ^ d * ∑ b, ∑' k, v (residueEquiv d s (b, k))) =
        ∑ b, H ^ d * ∑' k, v (residueEquiv d s (b, k)) := by
      rw [← mul_assoc, hfac, Finset.mul_sum]
    _ ≤ ∑ _b : Fin d → Fin s, ε := Finset.sum_le_sum fun b _ ↦ hbnd b
    _ = (s : ℝ) ^ d * ε := by simp [Fintype.card_fun, nsmul_eq_mul]

end MaternAudit.SampleTightness
