import Mathlib.Probability.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Variance of the average over ordered pairs

For a symmetric array with deterministic diagonal, two off-diagonal entries can
share both indices, exactly one index, or no indices. The finite sum below counts
these cases for all ordered pairs, including both orientations. The probability
result uses square-integrable entries, a common off-diagonal variance, a common
covariance for a three-index overlap, and independence for disjoint pairs.
-/

noncomputable section

open Finset MeasureTheory ProbabilityTheory

namespace MaternAudit.OverlapVariance

variable {N : ℕ}

/-- Covariance contributed by two ordered pairs, given the two overlap values. -/
def overlapWeight (v q : ℝ) (i j k l : Fin N) : ℝ :=
  if i = j ∨ k = l then 0
  else if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then v
  else if k = i ∨ k = j ∨ l = i ∨ l = j then q else 0

/-- Sum a function that is constant away from two distinct indices. -/
private theorem sum_two_exceptions (i j : Fin N) (hij : i ≠ j)
    (f : Fin N → ℝ) (a : ℝ) (hf : ∀ k, k ≠ i → k ≠ j → f k = a) :
    ∑ k, f k = f i + f j + ((N : ℝ) - 2) * a := by
  calc
    _ = ∑ k : Fin N, ((if k = i then f i - a else 0) +
        (if k = j then f j - a else 0) + a) := by
      apply sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp [hij]
      by_cases hkj : k = j
      · subst k
        simp [hij.symm]
      simp [hki, hkj, hf k hki hkj]
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A fixed off-diagonal pair has two ordered partners sharing both indices
and four choices of orientation for each of the other `N - 2` indices. -/
theorem overlap_row_sum (v q : ℝ) (i j : Fin N) (hij : i ≠ j) :
    ∑ k, ∑ l, overlapWeight v q i j k l = 2 * v + 4 * ((N : ℝ) - 2) * q := by
  let row (k : Fin N) := ∑ l, overlapWeight v q i j k l
  have endpoint (k : Fin N) (hk : k = i ∨ k = j) :
      row k = v + ((N : ℝ) - 2) * q := by
    dsimp only [row]
    rw [sum_two_exceptions i j hij _ q]
    · rcases hk with hk | hk <;> subst k <;> simp [overlapWeight, hij, hij.symm]
    · intro l hli hlj
      rcases hk with hk | hk <;> subst k <;>
        simp [overlapWeight, hij, hij.symm, hli, hli.symm, hlj, hlj.symm]
  have outside (k : Fin N) (hki : k ≠ i) (hkj : k ≠ j) : row k = 2 * q := by
    dsimp only [row]
    rw [sum_two_exceptions i j hij _ 0]
    · simp [overlapWeight, hij, hki, hkj, two_mul]
    · intro l hli hlj
      simp [overlapWeight, hij, hki, hkj, hli, hlj]
  change ∑ k, row k = _
  rw [sum_two_exceptions i j hij row (2 * q) outside,
    endpoint i (Or.inl rfl), endpoint j (Or.inr rfl)]
  ring

/-- The exact weighted counts of the two overlap classes over all four indices.
Setting one weight to one and the other to zero isolates either multiplicity. -/
theorem sum_overlapWeight (N : ℕ) (v q : ℝ) :
    (∑ i : Fin N, ∑ j, ∑ k, ∑ l, overlapWeight v q i j k l) =
      2 * N * (N - 1 : ℝ) * v + 4 * N * (N - 1 : ℝ) * (N - 2 : ℝ) * q := by
  let b := 2 * v + 4 * ((N : ℝ) - 2) * q
  have row (i : Fin N) : ∑ j, ∑ k, ∑ l, overlapWeight v q i j k l = (N - 1 : ℝ) * b := by
    calc
      _ = ∑ j : Fin N, ((if j = i then -b else 0) + b) := by
        apply sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j
          simp [overlapWeight]
        · simpa [h, b] using overlap_row_sum v q i j (Ne.symm h)
      _ = _ := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, if_true, sum_const, card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
  simp_rw [row]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, b]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Real covariance, written in terms of raw moments. We use it for L² entries. -/
def covariance (P : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  (∫ ω, X ω * Y ω ∂P) - (∫ ω, X ω ∂P) * ∫ ω, Y ω ∂P

private theorem covariance_congr {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') : covariance P X Y = covariance P X' Y' := by
  unfold covariance
  rw [integral_congr_ae (hX.mul hY), integral_congr_ae hX, integral_congr_ae hY]

private theorem covariance_comm (X Y : Ω → ℝ) : covariance P X Y = covariance P Y X := by
  simp only [covariance, mul_comm]

variable [IsProbabilityMeasure P]

private theorem covariance_self {X : Ω → ℝ} (hX : MemLp X 2 P) :
    covariance P X X = variance X P := by
  simp only [covariance, variance_def' hX, Pi.pow_apply, sq]

private theorem covariance_sum_left {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hY : MemLp Y 2 P) :
    covariance P (fun ω => ∑ i, X i ω) Y = ∑ i, covariance P (X i) Y := by
  simp only [covariance, sum_mul]
  rw [integral_finset_sum (f := fun i ω => X i ω * Y ω) univ
      (fun i _ => (hX i).integrable_mul hY),
    integral_finset_sum univ (fun i _ => (hX i).integrable one_le_two),
    sum_mul, sum_sub_distrib]

private theorem variance_sum_eq_sum_covariance {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) :
    variance (fun ω => ∑ i, X i ω) P = ∑ i, ∑ j, covariance P (X i) (X j) := by
  have hs := memLp_finset_sum univ (fun i _ => hX i)
  rw [← covariance_self hs, covariance_sum_left X _ hX hs]
  apply sum_congr rfl
  intro i _
  rw [covariance_comm, covariance_sum_left X _ hX (hX i)]
  exact sum_congr rfl fun j _ => covariance_comm (X j) (X i)

/-- The inputs supplied by the iid kernel calculation. The three-index
covariance is required in just one orientation. The diagonal may have a
different deterministic value at each index. -/
structure KernelMoments (P : Measure Ω) (K : Fin N → Fin N → Ω → ℝ) (v q : ℝ) : Prop where
  squareIntegrable : ∀ i j, MemLp (K i j) 2 P
  diagonal : ∀ i, ∃ d : ℝ, K i i =ᵐ[P] fun _ => d
  symmetric : ∀ i j, K i j =ᵐ[P] K j i
  offDiag_variance : ∀ i j, i ≠ j → variance (K i j) P = v
  shared_covariance : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → covariance P (K i j) (K i l) = q
  disjoint_indep : ∀ i j k l, i ≠ j → k ≠ l → k ≠ i → k ≠ j → l ≠ i → l ≠ j →
    IndepFun (K i j) (K k l) P

/-- Deterministic diagonal, symmetry, and disjoint independence determine all
four-index covariances from the two off-diagonal moments. -/
theorem KernelMoments.covariance_eq {K : Fin N → Fin N → Ω → ℝ} {v q : ℝ}
    (h : KernelMoments P K v q) (i j k l : Fin N) :
    covariance P (K i j) (K k l) = overlapWeight v q i j k l := by
  by_cases hij : i = j
  · subst j
    obtain ⟨d, hd⟩ := h.diagonal i
    rw [covariance_congr hd (Filter.EventuallyEq.rfl : K k l =ᵐ[P] K k l)]
    simp [overlapWeight, covariance, integral_const_mul]
  by_cases hkl : k = l
  · subst l
    obtain ⟨d, hd⟩ := h.diagonal k
    rw [covariance_congr (Filter.EventuallyEq.rfl : K i j =ᵐ[P] K i j) hd]
    simp [overlapWeight, covariance, integral_mul_const]
  have selfCov (s t : Fin N) (hst : s ≠ t) : covariance P (K s t) (K s t) = v :=
    (covariance_self (h.squareIntegrable s t)).trans (h.offDiag_variance s t hst)
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      simpa [overlapWeight, hij] using selfCov i j hij
    · simpa [overlapWeight, hij, hkl, hlj] using h.shared_covariance i j l hij hkl (Ne.symm hlj)
  by_cases hkj : k = j
  · subst k
    rw [covariance_congr (h.symmetric i j) (Filter.EventuallyEq.rfl : K j l =ᵐ[P] K j l)]
    by_cases hli : l = i
    · subst l
      simpa [overlapWeight, hij, hki] using selfCov j i hki
    · simpa [overlapWeight, hij, hkl, hki, hli] using
        h.shared_covariance j i l hki hkl (Ne.symm hli)
  by_cases hli : l = i
  · subst l
    rw [covariance_congr (Filter.EventuallyEq.rfl : K i j =ᵐ[P] K i j) (h.symmetric k i)]
    simpa [overlapWeight, hij, hki, hkj] using
      h.shared_covariance i j k hij (Ne.symm hki) (Ne.symm hkj)
  by_cases hlj : l = j
  · subst l
    rw [covariance_congr (h.symmetric i j) (h.symmetric k j)]
    simpa [overlapWeight, hij, hki, hkj] using
      h.shared_covariance j i k (Ne.symm hij) (Ne.symm hkj) (Ne.symm hki)
  have hind := h.disjoint_indep i j k l hij hkl hki hkj hli hlj
  have hprod := hind.integral_mul_of_integrable ((h.squareIntegrable i j).integrable one_le_two)
    ((h.squareIntegrable k l).integrable one_le_two)
  simp [overlapWeight, hij, hkl, hki, hkj, hli, hlj, covariance, ← Pi.mul_apply, hprod]

/-- Mean of all `N²` entries of the real array, including its diagonal. -/
def pairAverage (K : Fin N → Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ((N : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, K i j ω

/-- Exact variance from the entrywise covariance table. Disjoint entries may
be uncorrelated under this formulation. -/
theorem variance_pairAverage_of_covariances {K : Fin N → Fin N → Ω → ℝ} {v q : ℝ}
    (hN : 0 < N) (hK : ∀ i j, MemLp (K i j) 2 P)
    (hcov : ∀ i j k l, covariance P (K i j) (K k l) = overlapWeight v q i j k l) :
    (N : ℝ) ^ 4 * variance (pairAverage K) P =
      2 * N * (N - 1 : ℝ) * v + 4 * N * (N - 1 : ℝ) * (N - 2 : ℝ) * q := by
  have hsum := variance_sum_eq_sum_covariance
    (fun p : Fin N × Fin N => K p.1 p.2) (fun p => hK p.1 p.2)
  simp only [Fintype.sum_prod_type] at hsum
  simp_rw [hcov] at hsum
  rw [sum_overlapWeight] at hsum
  unfold pairAverage
  rw [variance_mul, hsum]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp [hNr]
  ring

/-- Exact variance identity for a symmetric array with the stated iid overlap moments. -/
theorem variance_pairAverage {K : Fin N → Fin N → Ω → ℝ} {v q : ℝ}
    (hN : 0 < N) (h : KernelMoments P K v q) :
    (N : ℝ) ^ 4 * variance (pairAverage K) P =
      2 * N * (N - 1 : ℝ) * v + 4 * N * (N - 1 : ℝ) * (N - 2 : ℝ) * q :=
  variance_pairAverage_of_covariances hN h.squareIntegrable h.covariance_eq

/-- Real-valued probability of a deviation of size at least `t`, using the
exact overlap coefficients in Chebyshev's inequality. -/
theorem chebyshev_pairAverage {K : Fin N → Fin N → Ω → ℝ} {v q t : ℝ}
    (hN : 0 < N) (h : KernelMoments P K v q) (ht : 0 < t) :
    P.real {ω | t ≤ |pairAverage K ω - ∫ x, pairAverage K x ∂P|} ≤
      (2 * N * (N - 1 : ℝ) * v + 4 * N * (N - 1 : ℝ) * (N - 2 : ℝ) * q) /
        ((N : ℝ) ^ 4 * t ^ 2) := by
  have hrow (i : Fin N) := memLp_finset_sum univ (fun j _ => h.squareIntegrable i j)
  have hZ : MemLp (pairAverage K) 2 P :=
    (memLp_finset_sum univ (fun i _ => hrow i)).const_mul _
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top (meas_ge_le_variance_div_sq hZ ht)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg t))] at hbound
  calc
    _ ≤ variance (pairAverage K) P / t ^ 2 := hbound
    _ = _ := by
      rw [← variance_pairAverage hN h]
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      field_simp [hNr, ht.ne']
      ring

end MaternAudit.OverlapVariance
