import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Matérn diagonal on the growing Fourier grid

For the one-dimensional Matérn kernel with `ν = ℓ = 1/2`, the integer grid
has weights `h / (1 + π² (h j)²)`. At zero all phases equal one. Keeping the
positive shell `m < j ≤ 2m` gives a lower bound for the full two-sided tail.

The finite and infinite cosine sums equal the corresponding complex Fourier
sums by symmetry of the frequency grid. The spatial image series is estimated
directly for every lag in `[-1,1]`. Evaluating the Fourier series of a
periodized exponential gives the spectral alias explicitly and discharges
the diagonal Poisson hypothesis in the conditional result.
-/

noncomputable section

namespace MaternAudit.DiagonalObstruction

open Filter
open scoped BigOperators Topology

/-- Spectral density in cycles per unit length. -/
def spectrum (ξ : ℝ) : ℝ := 1 / (1 + Real.pi ^ 2 * ξ ^ 2)

/-- The coefficient of the mode with integer index `j`, including its grid weight. -/
def weight (h : ℝ) (j : ℤ) : ℝ := h * spectrum (h * (j : ℝ))

theorem weight_nonneg {h : ℝ} (hh : 0 ≤ h) (j : ℤ) : 0 ≤ weight h j := by
  unfold weight spectrum
  positivity

/-- Absolute summability follows by comparison with the integer inverse-square series. -/
theorem summable_weight {h : ℝ} (hh : 0 < h) : Summable (weight h) := by
  have hp : Summable (fun j : ℤ => 1 / (j : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by decide)
  refine Summable.of_norm_bounded_eventually _
    (hp.mul_left (h / (Real.pi ^ 2 * h ^ 2))) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with j hj
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hd : 0 < Real.pi ^ 2 * (h * (j : ℝ)) ^ 2 :=
    mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero (mul_ne_zero hh.ne' hj'))
  rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hh.le j)]
  calc
    weight h j = h / (1 + Real.pi ^ 2 * (h * j) ^ 2) := by
      simp [weight, spectrum, div_eq_mul_inv]
    _ ≤ h / (Real.pi ^ 2 * (h * j) ^ 2) :=
      div_le_div_of_nonneg_left hh.le hd (by linarith)
    _ = _ := by
      field_simp [hh.ne', hj', Real.pi_ne_zero]
      ring

def band (m : ℕ) : Finset ℤ := Finset.Icc (-(m : ℤ)) (m : ℤ)

def positiveShell (m : ℕ) : Finset ℤ := Finset.Ioc (m : ℤ) ((m : ℤ) + m)

/-- Full two-sided omitted spectral mass at zero. -/
def tailAtZero (h : ℝ) (m : ℕ) : ℝ := ∑' j : {j : ℤ // j ∉ band m}, weight h j

theorem positiveShell_card (m : ℕ) : (positiveShell m).card = m := by
  simp [positiveShell, Int.card_Ioc]

/-- The `m` positive frequencies contribute at least `R / (1 + 4 π² R²)`, where `R = hm`. -/
theorem positiveShell_lower {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    (h * m) / (1 + 4 * Real.pi ^ 2 * (h * m) ^ 2) ≤
      ∑ j ∈ positiveShell m, weight h j := by
  let D := 1 + 4 * Real.pi ^ 2 * (h * m) ^ 2
  calc
    (h * m) / D = ∑ _j ∈ positiveShell m, h / D := by
      simp only [Finset.sum_const, positiveShell_card, nsmul_eq_mul]
      ring
    _ ≤ ∑ j ∈ positiveShell m, weight h j := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ioc.mp hj
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast (show (0 : ℤ) ≤ j by omega)
      have hjmax : (j : ℝ) ≤ (m : ℝ) + m := by exact_mod_cast hjhi
      have hξ : h * (j : ℝ) ≤ 2 * (h * m) := by
        calc
          _ ≤ h * ((m : ℝ) + m) := mul_le_mul_of_nonneg_left hjmax hh
          _ = _ := by ring
      have hs := pow_le_pow_left₀ (mul_nonneg hh hj0) hξ 2
      have hden := mul_le_mul_of_nonneg_left hs (sq_nonneg Real.pi)
      simp only [weight, spectrum, mul_one_div]
      apply div_le_div_of_nonneg_left hh (by positivity)
      dsimp [D]
      linarith only [hden]

theorem positiveShell_le_tail {h : ℝ} (hh : 0 < h) (m : ℕ) :
    ∑ j ∈ positiveShell m, weight h j ≤ tailAtZero h m := by
  have hd : Disjoint (band m) (positiveShell m) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact (not_lt_of_ge (Finset.mem_Icc.mp hj).2) (Finset.mem_Ioc.mp hk).1
  have hs := summable_weight hh
  have hu := hs.sum_le_tsum (band m ∪ positiveShell m) (fun j _ => weight_nonneg hh.le j)
  rw [Finset.sum_union hd, ← hs.sum_add_tsum_subtype_compl (band m)] at hu
  exact le_of_add_le_add_left hu

theorem tailAtZero_shell_lower {h : ℝ} (hh : 0 < h) (m : ℕ) :
    (h * m) / (1 + 4 * Real.pi ^ 2 * (h * m) ^ 2) ≤ tailAtZero h m :=
  (positiveShell_lower hh.le m).trans (positiveShell_le_tail hh m)

/-- Constant in the inverse-cutoff lower bound for `R ≥ 1`. -/
def shellConstant : ℝ := 1 / (1 + 4 * Real.pi ^ 2)

theorem shellConstant_pos : 0 < shellConstant := by unfold shellConstant; positivity

theorem tailAtZero_lower {h : ℝ} (hh : 0 < h) (m : ℕ) (hR : 1 ≤ h * m) :
    shellConstant / (h * m) ≤ tailAtZero h m := by
  apply le_trans _ (tailAtZero_shell_lower hh m)
  have hpos : 0 < h * m := zero_lt_one.trans_le hR
  unfold shellConstant
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [show 1 ≤ (h * m) ^ 2 from one_le_pow₀ hR]

def spacing (N : ℕ) : ℝ := 1 / (N : ℝ)

def cutoff (N : ℕ) : ℕ := N ^ 3

theorem growingGrid_radius {N : ℕ} (hN : 0 < N) :
    spacing N * cutoff N = (N : ℝ) ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [spacing, cutoff, Nat.cast_pow]
  field_simp [hn]
  ring

theorem growingGrid_tail_lower {N : ℕ} (hN : 0 < N) :
    shellConstant / (N : ℝ) ^ 2 ≤ tailAtZero (spacing N) (cutoff N) := by
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < spacing N := by unfold spacing; positivity
  rw [← growingGrid_radius hN]
  apply tailAtZero_lower hh
  rw [growingGrid_radius hN]
  exact one_le_pow₀ h1

/-- Unit-variance spatial kernel for `ν = ℓ = 1/2`. -/
def kernel (z : ℝ) : ℝ := Real.exp (-2 * |z|)

/-- Images at the two nonzero translates with index `±(n+1)`. -/
def imagePair (N : ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  kernel (z + ((n : ℝ) + 1) * N) + kernel (z - ((n : ℝ) + 1) * N)

def imageAlias (N : ℕ) (z : ℝ) : ℝ := ∑' n : ℕ, imagePair N z n

def aliasBound (N : ℕ) : ℝ :=
  2 * Real.exp (2 - 2 * (N : ℝ)) / (1 - Real.exp (-(2 * (N : ℝ))))

private theorem imagePair_nonneg (N : ℕ) (z : ℝ) (n : ℕ) : 0 ≤ imagePair N z n :=
  add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

private theorem imagePair_le {z : ℝ} (hz : |z| ≤ 1) (N n : ℕ) :
    imagePair N z n ≤
      (2 * Real.exp (2 - 2 * (N : ℝ))) * Real.exp (-(2 * (N : ℝ))) ^ n := by
  let u := ((n : ℝ) + 1) * N
  have hz' := abs_le.mp hz
  have hp : kernel (z + u) ≤ Real.exp (2 - 2 * u) := by
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (z + u)]
  have hm : kernel (z - u) ≤ Real.exp (2 - 2 * u) := by
    apply Real.exp_le_exp.mpr
    linarith [neg_le_abs (z - u)]
  have he : Real.exp (2 - 2 * u) =
      Real.exp (2 - 2 * (N : ℝ)) * Real.exp (-(2 * (N : ℝ))) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [u]
    ring
  change kernel (z + u) + kernel (z - u) ≤ _
  rw [he] at hp hm
  linarith

private theorem imageMajorant_hasSum {N : ℕ} (hN : 0 < N) :
    HasSum (fun n : ℕ =>
      (2 * Real.exp (2 - 2 * (N : ℝ))) * Real.exp (-(2 * (N : ℝ))) ^ n)
      (aliasBound N) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq : Real.exp (-(2 * (N : ℝ))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  simpa only [aliasBound, div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left (2 * Real.exp (2 - 2 * (N : ℝ)))

theorem summable_imagePair {N : ℕ} (hN : 0 < N) {z : ℝ} (hz : |z| ≤ 1) :
    Summable (imagePair N z) :=
  Summable.of_nonneg_of_le (imagePair_nonneg N z) (imagePair_le hz N)
    (imageMajorant_hasSum hN).summable

/-- Uniform spatial alias estimate obtained by summing the actual exponential kernel images. -/
theorem abs_imageAlias_le {N : ℕ} (hN : 0 < N) {z : ℝ} (hz : |z| ≤ 1) :
    |imageAlias N z| ≤ aliasBound N := by
  unfold imageAlias
  rw [abs_of_nonneg (tsum_nonneg (imagePair_nonneg N z))]
  exact ((summable_imagePair hN hz).tsum_le_tsum (imagePair_le hz N)
    (imageMajorant_hasSum hN).summable).trans_eq (imageMajorant_hasSum hN).tsum_eq

/-- The displayed alias envelope is smaller than every fixed inverse polynomial order. -/
theorem tendsto_pow_mul_aliasBound (p : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ p * aliasBound N) atTop (𝓝 0) := by
  have he : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ p * Real.exp (-(N : ℝ))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp tendsto_natCast_atTop_atTop
  have hq (x : ℝ) : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he₂ : Tendsto (fun N : ℕ => Real.exp (-(2 * (N : ℝ)))) atTop (𝓝 0) := by
    simpa only [hq, mul_zero] using he.mul he
  have hp₂ : Tendsto (fun N : ℕ => (N : ℝ) ^ p * Real.exp (-(2 * (N : ℝ)))) atTop (𝓝 0) := by
    simpa only [hq, ← mul_assoc, mul_zero] using hp.mul he
  have hden : Tendsto (fun N : ℕ => 1 - Real.exp (-(2 * (N : ℝ)))) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub he₂
  have hnum := hp₂.const_mul (2 * Real.exp 2)
  have hlim := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hlim' : Tendsto (fun N : ℕ =>
      (2 * Real.exp 2 * ((N : ℝ) ^ p * Real.exp (-(2 * (N : ℝ))))) /
        (1 - Real.exp (-(2 * (N : ℝ))))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using hlim
  refine hlim'.congr fun N => ?_
  unfold aliasBound
  rw [sub_eq_add_neg (2 : ℝ), Real.exp_add]
  ring

/-- Real Fourier approximation on the symmetric band. -/
def finiteKernel (h : ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ band m, weight h j * Real.cos (2 * Real.pi * (h * (j : ℝ)) * z)

/-- The cosine expansion on the entire integer frequency grid. -/
def infiniteKernel (h z : ℝ) : ℝ :=
  ∑' j : ℤ, weight h j * Real.cos (2 * Real.pi * (h * (j : ℝ)) * z)

/-- Weighted complex Fourier mode in the cycles-per-unit-length convention. -/
def fourierMode (h z : ℝ) (j : ℤ) : ℂ :=
  (weight h j : ℂ) * Complex.exp (((2 * Real.pi * (h * (j : ℝ)) * z : ℝ) : ℂ) * Complex.I)

private theorem fourierMode_re (h z : ℝ) (j : ℤ) : (fourierMode h z j).re =
    weight h j * Real.cos (2 * Real.pi * (h * (j : ℝ)) * z) := by
  rw [fourierMode, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

private theorem fourierMode_neg_im (h z : ℝ) (j : ℤ) :
    (fourierMode h z (-j)).im = -(fourierMode h z j).im := by
  have hw : weight h (-j) = weight h j := by simp [weight, spectrum]
  simp only [fourierMode, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im, hw,
    Int.cast_neg, mul_neg, neg_mul, Real.sin_neg]

theorem summable_fourierMode {h : ℝ} (hh : 0 < h) (z : ℝ) : Summable (fourierMode h z) := by
  refine Summable.of_norm_bounded (weight h) (summable_weight hh) fun j => ?_
  rw [fourierMode, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hh.le j)]

theorem summable_infiniteKernel {h : ℝ} (hh : 0 < h) (z : ℝ) :
    Summable (fun j : ℤ => weight h j * Real.cos (2 * Real.pi * (h * (j : ℝ)) * z)) := by
  simpa only [fourierMode_re] using (Complex.hasSum_re (summable_fourierMode hh z).hasSum).summable

/-- The finite real kernel is exactly the original complex Fourier approximation. -/
theorem finiteKernel_eq_fourierSum (h : ℝ) (m : ℕ) (z : ℝ) :
    (finiteKernel h m z : ℂ) = ∑ j ∈ band m, fourierMode h z j := by
  apply Complex.ext
  · simp only [finiteKernel, Complex.ofReal_re, Complex.re_sum, fourierMode_re]
  · rw [Complex.ofReal_im, Complex.im_sum]
    have hs : ∑ j ∈ band m, (fourierMode h z (-j)).im = ∑ j ∈ band m, (fourierMode h z j).im := by
      apply Finset.sum_equiv (Equiv.neg ℤ)
      · intro j
        simp only [band, Finset.mem_Icc, Equiv.neg_apply]
        omega
      · intro j _
        rfl
    simp_rw [fourierMode_neg_im, Finset.sum_neg_distrib] at hs
    linarith only [hs]

theorem infiniteKernel_eq_fourierSum {h : ℝ} (hh : 0 < h) (z : ℝ) :
    (infiniteKernel h z : ℂ) = ∑' j : ℤ, fourierMode h z j := by
  have hsum := summable_fourierMode hh z
  apply Complex.ext
  · simp only [infiniteKernel, Complex.ofReal_re, Complex.re_tsum hsum, fourierMode_re]
  · rw [Complex.ofReal_im, Complex.im_tsum hsum]
    have hs := (Equiv.neg ℤ).tsum_eq fun j => (fourierMode h z j).im
    simp only [Equiv.neg_apply, fourierMode_neg_im, tsum_neg] at hs
    linarith only [hs]

@[simp] theorem finiteKernel_zero (h : ℝ) (m : ℕ) :
    finiteKernel h m 0 = ∑ j ∈ band m, weight h j := by simp [finiteKernel]

/-- Spectral definition of the diagonal alias on the growing grid. -/
def gridAliasAtZero (N : ℕ) : ℝ := (∑' j : ℤ, weight (spacing N) j) - 1

theorem finiteKernel_zero_sub_one {N : ℕ} (hN : 0 < N) :
    finiteKernel (spacing N) (cutoff N) 0 - 1 =
      gridAliasAtZero N - tailAtZero (spacing N) (cutoff N) := by
  have hh : 0 < spacing N := by unfold spacing; positivity
  have hs := (summable_weight hh).sum_add_tsum_subtype_compl (band (cutoff N))
  rw [finiteKernel_zero]
  unfold gridAliasAtZero tailAtZero
  linarith only [hs]

/-- The diagonal part of normalized squared Frobenius error. -/
def diagonalEnergy (N : ℕ) (h : ℝ) (m : ℕ) : ℝ := (finiteKernel h m 0 - 1) ^ 2 / N

/-- Normalized squared Frobenius error at the specified locations. -/
def meanSquare {N : ℕ} (h : ℝ) (m : ℕ) (X : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N,
    (finiteKernel h m (X i - X j) - kernel (X i - X j)) ^ 2) / (N : ℝ) ^ 2

theorem diagonalEnergy_le_meanSquare {N : ℕ} (hN : 0 < N) (h : ℝ) (m : ℕ)
    (X : Fin N → ℝ) : diagonalEnergy N h m ≤ meanSquare h m X := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hrow (i : Fin N) : (finiteKernel h m 0 - 1) ^ 2 ≤
      ∑ j : Fin N, (finiteKernel h m (X i - X j) - kernel (X i - X j)) ^ 2 := by
    simpa only [sub_self, kernel, abs_zero, mul_zero, Real.exp_zero] using
      (Finset.single_le_sum
        (f := fun j : Fin N => (finiteKernel h m (X i - X j) - kernel (X i - X j)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  unfold diagonalEnergy meanSquare
  calc
    _ = (∑ _i : Fin N, (finiteKernel h m 0 - 1) ^ 2) / (N : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hn]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hrow i) (sq_nonneg _)

/-- A small positive spectral excess is the only alias control needed at zero.
Negative excess also satisfies this one-sided condition. -/
theorem growingGrid_diagonal_lower_of_alias {N : ℕ} (hN : 0 < N)
    (ha : gridAliasAtZero N ≤ shellConstant / (2 * (N : ℝ) ^ 2)) :
    shellConstant / (2 * (N : ℝ) ^ 2) / Real.sqrt N ≤
      Real.sqrt (diagonalEnergy N (spacing N) (cutoff N)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsplit : shellConstant / (N : ℝ) ^ 2 =
      2 * (shellConstant / (2 * (N : ℝ) ^ 2)) := by ring
  have ht := growingGrid_tail_lower hN
  rw [hsplit] at ht
  have herr : shellConstant / (2 * (N : ℝ) ^ 2) ≤
      |finiteKernel (spacing N) (cutoff N) 0 - 1| := by
    rw [finiteKernel_zero_sub_one hN]
    exact le_trans (by linarith only [ht, ha]) (neg_le_abs _)
  rw [diagonalEnergy, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs]
  exact div_le_div_of_nonneg_right herr (Real.sqrt_nonneg _)

private theorem eventually_rate_lt_diagonal_scale (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C / (N : ℝ) ^ 3 <
      shellConstant / (2 * (N : ℝ) ^ 2) / Real.sqrt N := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ),
      ht.eventually_gt_atTop ((2 * |C| / shellConstant) ^ 2)] with N hN hlarge
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc := shellConstant_pos
  have hs := Real.sqrt_lt_sqrt (sq_nonneg _) hlarge
  rw [Real.sqrt_sq (by positivity)] at hs
  have hC := (div_lt_iff₀ hc).mp hs
  rw [div_lt_iff₀ (pow_pos hn 3)]
  calc
    C < shellConstant / 2 * Real.sqrt N := by linarith [le_abs_self C]
    _ = shellConstant / 2 * ((N : ℝ) / Real.sqrt N) := by rw [Real.div_sqrt]
    _ = _ := by
      field_simp [hn.ne', (Real.sqrt_pos.mpr hn).ne']
      ring_nf
      rw [Real.sq_sqrt hn.le]
      ring

/-- Every constant in the proposed `N⁻³` rate fails, even after adding the full
uniform alias envelope. The conclusion already holds for diagonal energy alone. -/
theorem growingGrid_counterexample_of_small_alias (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      gridAliasAtZero N ≤ shellConstant / (2 * (N : ℝ) ^ 2) →
      aliasBound N + |C| / (N : ℝ) ^ 3 <
        Real.sqrt (diagonalEnergy N (spacing N) (cutoff N)) := by
  have ha := (tendsto_pow_mul_aliasBound 3).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_gt_atTop (0 : ℕ), ha,
    eventually_rate_lt_diagonal_scale (1 + |C|)] with N hN hsmall hgap
  intro hspec
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hb : aliasBound N < 1 / (N : ℝ) ^ 3 :=
    (lt_div_iff₀ (pow_pos hn 3)).mpr (by simpa [mul_comm] using hsmall)
  calc
    aliasBound N + |C| / (N : ℝ) ^ 3 < (1 + |C|) / (N : ℝ) ^ 3 := by
      rw [add_div]; linarith only [hb]
    _ < _ := hgap.trans_le (growingGrid_diagonal_lower_of_alias hN hspec)

private theorem eventually_imageAlias_small :
    ∀ᶠ N : ℕ in atTop, imageAlias N 0 ≤ shellConstant / (2 * (N : ℝ) ^ 2) := by
  have hc : 0 < shellConstant / 2 := half_pos shellConstant_pos
  have ha := (tendsto_pow_mul_aliasBound 2).eventually (gt_mem_nhds hc)
  filter_upwards [eventually_gt_atTop (0 : ℕ), ha] with N hN hsmall
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  apply (le_abs_self _).trans ((abs_imageAlias_le hN (by simp)).trans ?_)
  rw [← div_div, le_div_iff₀ (pow_pos hn 2)]
  exact le_of_lt (by simpa [mul_comm] using hsmall)

/-- Assuming Poisson summation only at zero, all location configurations violate the proposed
rate eventually. The `N` threshold is independent of the configuration. -/
theorem growingGrid_counterexample_of_poisson (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, gridAliasAtZero N = imageAlias N 0 →
      ∀ X : Fin N → ℝ, aliasBound N + |C| / (N : ℝ) ^ 3 <
        Real.sqrt (meanSquare (spacing N) (cutoff N) X) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_imageAlias_small,
    growingGrid_counterexample_of_small_alias C] with N hN hsmall hgap
  intro hpoisson X
  have hspec := hpoisson.symm ▸ hsmall
  exact (hgap hspec).trans_le
    (Real.sqrt_le_sqrt (diagonalEnergy_le_meanSquare hN (spacing N) (cutoff N) X))

section FourierIdentity

open MeasureTheory

/-- One term in the interval integral computing a Fourier coefficient. -/
private def modeExp (a : ℝ) (j : ℤ) (x : ℝ) : ℂ :=
  fourier (-j) (x : UnitAddCircle) * (Real.exp (a * x) : ℂ)

private def modeDenom (a : ℝ) (j : ℤ) : ℂ :=
  (a : ℂ) - ((2 * Real.pi * (j : ℝ) : ℝ) : ℂ) * Complex.I

private theorem modeDenom_ne {a : ℝ} (ha : a ≠ 0) (j : ℤ) : modeDenom a j ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  exact ha (by simpa [modeDenom] using hr)

private theorem continuous_modeExp (a : ℝ) (j : ℤ) : Continuous (modeExp a j) :=
  ((fourier (-j)).continuous.comp (AddCircle.continuous_mk' 1)).mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

private theorem modeExp_deriv (a : ℝ) (j : ℤ) (x : ℝ) :
    HasDerivAt (modeExp a j) (modeDenom a j * modeExp a j x) x := by
  have hr : HasDerivAt (fun y : ℝ => Real.exp (a * y)) (Real.exp (a * x) * a) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp (a * x)).comp x ((hasDerivAt_id x).const_mul a)
  convert (hasDerivAt_fourier_neg 1 j x).mul hr.ofReal_comp using 1
  simp only [modeDenom, modeExp, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    Complex.ofReal_one, div_one]
  ring

/-- Integrating the derivative of `modeExp` works also for frequency zero. -/
private theorem integral_modeExp {a : ℝ} (ha : a ≠ 0) (j : ℤ) :
    (∫ x in (0 : ℝ)..1, modeExp a j x) = ((Real.exp a : ℂ) - 1) / modeDenom a j := by
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ Set.uIcc (0 : ℝ) 1) => modeExp_deriv a j x)
    ((continuous_const.mul (continuous_modeExp a j)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hint
  apply (eq_div_iff (modeDenom_ne ha j)).mpr
  rw [mul_comm, hint]
  simp only [modeExp, AddCircle.coe_period (1 : ℝ), AddCircle.coe_zero, fourier_eval_zero,
    mul_one, mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- On the unit period this profile equals the sum of the two nearest exponential
images. Division by `1 - exp (-a)` accounts for all their translates. -/
private def profile (a x : ℝ) : ℂ :=
  (Real.exp (-a * x) : ℂ) + (Real.exp (-a) : ℂ) * (Real.exp (a * x) : ℂ)

private theorem exp_neg_mul_exp (a : ℝ) :
    (Real.exp (-a) : ℂ) * (Real.exp a : ℂ) = 1 := by
  norm_cast
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

private def periodProfile (a : ℝ) : C(UnitAddCircle, ℂ) where
  toFun := AddCircle.liftIco 1 0 (profile a)
  continuous_toFun := by
    apply AddCircle.liftIco_zero_continuous
    · simp only [profile, mul_zero, mul_one, Real.exp_zero, Complex.ofReal_one,
        exp_neg_mul_exp, add_comm]
    · unfold profile
      fun_prop

private theorem periodProfile_zero (a : ℝ) :
    periodProfile a 0 = 1 + (Real.exp (-a) : ℂ) := by
  change AddCircle.liftIco 1 0 (profile a) 0 = _
  rw [← AddCircle.coe_zero (1 : ℝ), AddCircle.liftIco_zero_coe_apply (Set.left_mem_Ico.mpr zero_lt_one)]
  simp [profile]

private theorem periodProfile_on_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (a : ℝ) :
    periodProfile a (x : UnitAddCircle) = profile a x := by
  rcases hx.2.eq_or_lt with rfl | hlt
  · rw [AddCircle.coe_period, periodProfile_zero]
    simp only [profile, mul_one, exp_neg_mul_exp, add_comm]
  · exact AddCircle.liftIco_zero_coe_apply (f := profile a) ⟨hx.1, hlt⟩

private theorem unit_fourier_re (j : ℤ) (x : ℝ) :
    (fourier j (x : UnitAddCircle)).re = Real.cos (2 * Real.pi * (j : ℝ) * x) := by
  rw [fourier_coe_apply, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

private theorem add_mode_fractions {a : ℝ} (ha : 0 < a) (j : ℤ) (q : ℂ) :
    (q - 1) / modeDenom (-a) j + (1 - q) / modeDenom a j =
      (1 - q) * ((2 * a / (a ^ 2 + (2 * Real.pi * (j : ℝ)) ^ 2) : ℝ) : ℂ) := by
  have hd : a ^ 2 + (2 * Real.pi * (j : ℝ)) ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg _)).ne'
  rw [Complex.ofReal_div, ← mul_div_assoc]
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hd)).mpr
  field_simp [modeDenom_ne ha.ne' j, modeDenom_ne (neg_ne_zero.mpr ha.ne') j]
  simp only [modeDenom, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_intCast]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem periodProfile_coeff {a : ℝ} (ha : 0 < a) (j : ℤ) :
    fourierCoeff (periodProfile a) j = (1 - (Real.exp (-a) : ℂ)) *
      ((2 * a / (a ^ 2 + (2 * Real.pi * (j : ℝ)) ^ 2) : ℝ) : ℂ) := by
  change fourierCoeff (AddCircle.liftIco 1 0 (profile a)) j = _
  rw [fourierCoeff_liftIco_eq, fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, div_one, one_smul, smul_eq_mul]
  have hprod (x : ℝ) : fourier (-j) (x : UnitAddCircle) * profile a x =
      modeExp (-a) j x + (Real.exp (-a) : ℂ) * modeExp a j x := by
    unfold profile modeExp
    ring
  simp only [fourier_coe_apply, zero_add, sub_zero] at hprod ⊢
  simp_rw [hprod]
  rw [intervalIntegral.integral_add ((continuous_modeExp (-a) j).intervalIntegrable 0 1)
    (((continuous_modeExp a j).intervalIntegrable 0 1).const_mul _),
    intervalIntegral.integral_const_mul, integral_modeExp (neg_ne_zero.mpr ha.ne'),
    integral_modeExp ha.ne', ← mul_div_assoc, mul_sub, exp_neg_mul_exp, mul_one]
  exact add_mode_fractions ha j _

private theorem weight_eq_circle_coeff {N : ℕ} (hN : 0 < N) (j : ℤ) :
    weight (spacing N) j = 2 * (2 * (N : ℝ)) /
      ((2 * (N : ℝ)) ^ 2 + (2 * Real.pi * (j : ℝ)) ^ 2) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : (2 * (N : ℝ)) ^ 2 + (2 * Real.pi * (j : ℝ)) ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos (by positivity)) (sq_nonneg _)).ne'
  unfold weight spectrum spacing
  field_simp [hn.ne', hden]
  ring

/-- Exact spectral alias for lags of magnitude at most one grid period. -/
theorem infiniteKernel_sub_kernel {N : ℕ} (hN : 0 < N) {z : ℝ} (hz : |z| ≤ N) :
    infiniteKernel (spacing N) z - kernel z =
      (Real.exp (-2 * |z|) + Real.exp (2 * |z|)) * Real.exp (-(2 * (N : ℝ))) /
        (1 - Real.exp (-(2 * (N : ℝ)))) := by
  let a := 2 * (N : ℝ)
  let q := Real.exp (-a)
  let x := |z| / (N : ℝ)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (abs_nonneg _) hn.le, (div_le_one hn).mpr hz⟩
  have ha : 0 < a := by dsimp [a]; positivity
  have hh : 0 < spacing N := by unfold spacing; positivity
  have hcoeff (j : ℤ) : fourierCoeff (periodProfile a) j =
      ((1 - q : ℝ) : ℂ) * (weight (spacing N) j : ℂ) := by
    rw [periodProfile_coeff ha, weight_eq_circle_coeff hN, Complex.ofReal_sub, Complex.ofReal_one]
  have hs : Summable (fourierCoeff (periodProfile a)) :=
    ((Complex.summable_ofReal.mpr (summable_weight hh)).mul_left ((1 - q : ℝ) : ℂ)).congr
      (fun j => (hcoeff j).symm)
  have hcos (j : ℤ) : Real.cos (2 * Real.pi * (j : ℝ) * x) =
      Real.cos (2 * Real.pi * (spacing N * (j : ℝ)) * z) := by
    have hphase : 2 * Real.pi * (j : ℝ) * x = 2 * Real.pi * (spacing N * (j : ℝ)) * |z| := by
      unfold x spacing
      ring
    rw [hphase]
    rcases le_total 0 z with hz' | hz'
    · rw [abs_of_nonneg hz']
    · rw [abs_of_nonpos hz', mul_neg, Real.cos_neg]
  have hax : a * x = 2 * |z| := by
    dsimp [a, x]
    field_simp [hn.ne']
    ring
  have hnax : -a * x = -2 * |z| := by linarith only [hax]
  have hmode (j : ℤ) : (fourierCoeff (periodProfile a) j • fourier j (x : UnitAddCircle)).re =
      (1 - q) * (weight (spacing N) j * Real.cos (2 * Real.pi * (spacing N * (j : ℝ)) * z)) := by
    rw [hcoeff, smul_eq_mul, mul_assoc, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      unit_fourier_re, hcos]
  have heval := (Complex.hasSum_re
    (has_pointwise_sum_fourier_series_of_summable hs (x : UnitAddCircle))).tsum_eq
  have hsum : (1 - q) * infiniteKernel (spacing N) z =
      Real.exp (-2 * |z|) + q * Real.exp (2 * |z|) := by
    simpa only [hmode, tsum_mul_left, periodProfile_on_Icc hx, profile, Complex.add_re,
      Complex.re_ofReal_mul, Complex.ofReal_re,
      hnax, hax, infiniteKernel, q] using heval
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  change infiniteKernel (spacing N) z - Real.exp (-2 * |z|) =
    (Real.exp (-2 * |z|) + Real.exp (2 * |z|)) * q / (1 - q)
  rw [eq_div_iff (sub_pos.mpr hq).ne']
  linarith only [hsum]

/-- The exponential envelope bounds the actual infinite-grid alias at every data lag. -/
theorem abs_infiniteKernel_sub_kernel_le {N : ℕ} (hN : 0 < N) {z : ℝ} (hz : |z| ≤ 1) :
    |infiniteKernel (spacing N) z - kernel z| ≤ aliasBound N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : Real.exp (-(2 * (N : ℝ))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp := Real.exp_le_exp.mpr (show -2 * |z| ≤ 2 by linarith [abs_nonneg z])
  have hm := Real.exp_le_exp.mpr (show 2 * |z| ≤ 2 by linarith)
  rw [infiniteKernel_sub_kernel hN (hz.trans hn),
    abs_of_nonneg (div_nonneg (by positivity) (sub_nonneg.mpr hq.le))]
  unfold aliasBound
  rw [sub_eq_add_neg (2 : ℝ), Real.exp_add, ← mul_assoc]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hp, hm])
    (Real.exp_pos _).le) (sub_nonneg.mpr hq.le)

/-- Fourier-series evaluation at zero gives the exact spectral alias. -/
theorem gridAliasAtZero_closedForm {N : ℕ} (hN : 0 < N) :
    gridAliasAtZero N = 2 * Real.exp (-(2 * (N : ℝ))) / (1 - Real.exp (-(2 * (N : ℝ)))) := by
  simpa [infiniteKernel, kernel, gridAliasAtZero, one_add_one_eq_two] using
    (infiniteKernel_sub_kernel hN (z := 0) (by simp))

end FourierIdentity

theorem imageAlias_zero_closedForm {N : ℕ} (hN : 0 < N) :
    imageAlias N 0 = 2 * Real.exp (-(2 * (N : ℝ))) / (1 - Real.exp (-(2 * (N : ℝ)))) := by
  let q := Real.exp (-(2 * (N : ℝ)))
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hterm (n : ℕ) : imagePair N 0 n = (2 * q) * q ^ n := by
    have hv : 0 ≤ ((n : ℝ) + 1) * N := by positivity
    have ha : -2 * (((n : ℝ) + 1) * N) =
        -(2 * (N : ℝ)) + (n : ℝ) * (-(2 * (N : ℝ))) := by ring
    simp only [imagePair, kernel, zero_add, zero_sub, abs_neg, abs_of_nonneg hv,
      ha, Real.exp_add, Real.exp_nat_mul, q]
    ring
  unfold imageAlias
  simp_rw [hterm]
  exact ((hasSum_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left (2 * q)).tsum_eq

/-- The specialized Poisson identity at zero, proved from the pointwise Fourier series. -/
theorem gridAliasAtZero_eq_imageAlias {N : ℕ} (hN : 0 < N) :
    gridAliasAtZero N = imageAlias N 0 :=
  (gridAliasAtZero_closedForm hN).trans (imageAlias_zero_closedForm hN).symm

/-- For every proposed constant, the actual grid has a diagonal RMS lower bound
of order `N^(-5/2)`. The diagonal energy alone exceeds
`(aliasBound N + |C| / N³)²`. The threshold is uniform over designs. -/
theorem growingGrid_counterexample (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      shellConstant / (2 * (N : ℝ) ^ 2) / Real.sqrt N ≤
        Real.sqrt (diagonalEnergy N (spacing N) (cutoff N)) ∧
      (aliasBound N + |C| / (N : ℝ) ^ 3) ^ 2 < diagonalEnergy N (spacing N) (cutoff N) ∧
      ∀ X : Fin N → ℝ, aliasBound N + |C| / (N : ℝ) ^ 3 <
        Real.sqrt (meanSquare (spacing N) (cutoff N) X) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_imageAlias_small,
    growingGrid_counterexample_of_small_alias C] with N hN hsmall hgap
  rw [← gridAliasAtZero_eq_imageAlias hN] at hsmall
  have hlt := hgap hsmall
  have hb : 0 ≤ aliasBound N := (abs_nonneg (imageAlias N 0)).trans (abs_imageAlias_le hN (by simp))
  have hrate : 0 ≤ aliasBound N + |C| / (N : ℝ) ^ 3 := by positivity
  have hd : 0 ≤ diagonalEnergy N (spacing N) (cutoff N) := by unfold diagonalEnergy; positivity
  refine ⟨growingGrid_diagonal_lower_of_alias hN hsmall, ?_, fun X =>
    hlt.trans_le (Real.sqrt_le_sqrt (diagonalEnergy_le_meanSquare hN (spacing N) (cutoff N) X))⟩
  exact ((sq_lt_sq₀ hrate (Real.sqrt_nonneg _)).mpr hlt).trans_eq (Real.sq_sqrt hd)

/-- The ratio of diagonal RMS to the proposed `N⁻³` rate tends to infinity. -/
theorem tendsto_scaled_diagonalRMS :
    Tendsto (fun N : ℕ => Real.sqrt (diagonalEnergy N (spacing N) (cutoff N)) * (N : ℝ) ^ 3)
      atTop atTop := by
  refine tendsto_atTop.2 fun C => ?_
  filter_upwards [growingGrid_counterexample C, eventually_rate_lt_diagonal_scale C,
    eventually_gt_atTop (0 : ℕ)] with N h hgap hN
  exact ((div_lt_iff₀ (by positivity : 0 < (N : ℝ) ^ 3)).mp (hgap.trans_le h.1)).le

end MaternAudit.DiagonalObstruction
