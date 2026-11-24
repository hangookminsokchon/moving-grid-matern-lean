import Std

/-!
# The finite iid correction to equation (41)

An atom list `μ` gives a point `x` weight `w` for each entry `(x, w)`.
If its total weight is `W > 0`, dividing by `W` gives a probability law.
`wordLaw μ n` lists all length-`n` draws with replacement and gives each
choice of atoms the product of its weights. Repeated values are allowed.
-/

namespace MaternAudit.PairCounting

open Std.Internal (mkRat)

variable {α β : Type}

/-- Sum over list positions, including repeated entries. -/
def sumOn (xs : List α) (f : α → Nat) : Nat := (xs.map f).sum

/-- Unnormalized integral against a finite list of weighted atoms. -/
def weightedSum (μ : List (α × Nat)) (f : α → Nat) : Nat :=
  sumOn μ (fun a => a.2 * f a.1)

def mass (μ : List (α × Nat)) : Nat := sumOn μ Prod.snd

/-- The atom list for the product law. The empty word has weight one. -/
def wordLaw (μ : List (α × Nat)) : Nat → List (List α × Nat)
  | 0 => [([], 1)]
  | n + 1 => μ.flatMap fun a =>
      (wordLaw μ n).map fun t => (a.1 :: t.1, a.2 * t.2)

/-- The sum over all ordered pairs of positions in a single sampled word. -/
def pairSum (K : α → α → Nat) (xs : List α) : Nat :=
  sumOn xs (fun x => sumOn xs (K x))

/-- Numerator for the expectation of a kernel on two independent draws. -/
def independentPair (μ : List (α × Nat)) (K : α → α → Nat) : Nat :=
  weightedSum μ (fun x => weightedSum μ (K x))

private theorem sumOn_cons (x : α) (xs : List α) (f : α → Nat) :
    sumOn (x :: xs) f = f x + sumOn xs f := rfl

private theorem sumOn_add (xs : List α) (f g : α → Nat) :
    sumOn xs (fun x => f x + g x) = sumOn xs f + sumOn xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumOn_cons, ih]; ac_rfl

private theorem sumOn_scale (xs : List α) (c : Nat) (f : α → Nat) :
    sumOn xs (fun x => c * f x) = c * sumOn xs f := by
  induction xs with
  | nil => simp [sumOn]
  | cons x xs ih => simp only [sumOn_cons, ih, Nat.mul_add]

private theorem weightedSum_add (μ : List (α × Nat)) (f g : α → Nat) :
    weightedSum μ (fun x => f x + g x) = weightedSum μ f + weightedSum μ g := by
  simp only [weightedSum, Nat.mul_add, sumOn_add]

private theorem weightedSum_scale (μ : List (α × Nat)) (c : Nat) (f : α → Nat) :
    weightedSum μ (fun x => c * f x) = c * weightedSum μ f := by
  unfold weightedSum
  rw [← sumOn_scale]
  exact congrArg (sumOn μ) (funext fun a => Nat.mul_left_comm a.2 c (f a.1))

private theorem weightedSum_const (μ : List (α × Nat)) (c : Nat) :
    weightedSum μ (fun _ => c) = mass μ * c := by
  unfold weightedSum mass
  rw [Nat.mul_comm (sumOn μ Prod.snd), ← sumOn_scale]
  exact congrArg (sumOn μ) (funext fun a => Nat.mul_comm a.2 c)

private theorem weightedSum_sumOn (μ : List (α × Nat)) (ys : List β) (K : α → β → Nat) :
    weightedSum μ (fun x => sumOn ys (K x)) =
      sumOn ys (fun y => weightedSum μ (fun x => K x y)) := by
  induction ys with
  | nil => exact (weightedSum_const μ 0).trans (Nat.mul_zero _)
  | cons y ys ih => simp only [sumOn_cons, weightedSum_add, ih]

private theorem weightedSum_swap (μ : List (α × Nat)) (K : α → α → Nat) :
    weightedSum μ (fun x => weightedSum μ (fun y => K y x)) = independentPair μ K := by
  change weightedSum μ (fun x => sumOn μ (fun a => a.2 * K a.1 x)) =
    sumOn μ (fun a => a.2 * weightedSum μ (K a.1))
  simp only [weightedSum_sumOn, weightedSum_scale]

private theorem weightedSum_cons (a : α × Nat) (μ : List (α × Nat)) (f : α → Nat) :
    weightedSum (a :: μ) f = a.2 * f a.1 + weightedSum μ f := rfl

private theorem weightedSum_append (μ ν : List (α × Nat)) (f : α → Nat) :
    weightedSum (μ ++ ν) f = weightedSum μ f + weightedSum ν f := by
  induction μ with
  | nil => simp [weightedSum, sumOn]
  | cons a μ ih => simp only [List.cons_append, weightedSum_cons, ih, Nat.add_assoc]

private theorem weightedSum_prepend (a : α × Nat) (ts : List (List α × Nat))
    (F : List α → Nat) :
    weightedSum (ts.map (fun t => (a.1 :: t.1, a.2 * t.2))) F =
      a.2 * weightedSum ts (fun xs => F (a.1 :: xs)) := by
  change sumOn (ts.map _) _ = a.2 * sumOn ts _
  rw [← sumOn_scale]
  simp [sumOn, List.map_map, Function.comp_def, Nat.mul_assoc]

private theorem weightedSum_extensions (μ : List (α × Nat)) (ts : List (List α × Nat))
    (F : List α → Nat) :
    weightedSum (μ.flatMap (fun a => ts.map (fun t => (a.1 :: t.1, a.2 * t.2)))) F =
      weightedSum μ (fun x => weightedSum ts (fun xs => F (x :: xs))) := by
  induction μ with
  | nil => rfl
  | cons a μ ih =>
    simp only [List.flatMap_cons, weightedSum_append, weightedSum_prepend, ih, weightedSum_cons]

private theorem wordLaw_succ_sum (μ : List (α × Nat)) (n : Nat) (F : List α → Nat) :
    weightedSum (wordLaw μ (n + 1)) F =
      weightedSum μ (fun x => weightedSum (wordLaw μ n) (fun xs => F (x :: xs))) :=
  weightedSum_extensions μ (wordLaw μ n) F

/-- Total weight of all words, hence the denominator of their product probability law. -/
theorem mass_wordLaw (μ : List (α × Nat)) (n : Nat) :
    mass (wordLaw μ n) = mass μ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := wordLaw_succ_sum μ n (fun _ => 1)
    simpa only [weightedSum_const, Nat.mul_one, Nat.one_mul, ih, Nat.pow_succ, Nat.mul_comm] using h

private theorem word_single (μ : List (α × Nat)) (n : Nat) (f : α → Nat) :
    weightedSum (wordLaw μ (n + 1)) (fun xs => sumOn xs f) =
      (n + 1) * mass μ ^ n * weightedSum μ f := by
  induction n with
  | zero =>
    rw [wordLaw_succ_sum]
    simp [wordLaw, weightedSum_cons, sumOn_cons, sumOn, weightedSum]
  | succ n ih =>
    rw [wordLaw_succ_sum]
    simp only [sumOn_cons, weightedSum_add, weightedSum_const, mass_wordLaw, ih, weightedSum_scale]
    simp only [Nat.pow_succ, Nat.succ_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul]
    ac_rfl

private theorem pairSum_cons (K : α → α → Nat) (x : α) (xs : List α) :
    pairSum K (x :: xs) = K x x + sumOn xs (K x) +
      sumOn xs (fun y => K y x) + pairSum K xs := by
  simp only [pairSum, sumOn_cons, sumOn_add]
  ac_rfl

private theorem word_pair_step (μ : List (α × Nat)) (K : α → α → Nat) (n : Nat) :
    weightedSum (wordLaw μ (n + 1 + 1)) (pairSum K) =
      mass μ ^ (n + 1) * weightedSum μ (fun x => K x x) +
      ((n + 1) * mass μ ^ n) * independentPair μ K +
      ((n + 1) * mass μ ^ n) * independentPair μ K +
      mass μ * weightedSum (wordLaw μ (n + 1)) (pairSum K) := by
  rw [wordLaw_succ_sum]
  simp only [pairSum_cons, weightedSum_add, weightedSum_const, mass_wordLaw, word_single,
    weightedSum_scale, weightedSum_swap μ K, independentPair]

/-- For `N = n + 1`, the two terms correspond to the `N` diagonal and
`N * (N - 1)` off-diagonal ordered index pairs. The common factor on the
left also makes the formula valid for a single draw and for zero total weight. -/
theorem iid_pair_sum (μ : List (α × Nat)) (K : α → α → Nat) (n : Nat) :
    mass μ * weightedSum (wordLaw μ (n + 1)) (pairSum K) =
      (n + 1) * mass μ ^ n *
        (mass μ * weightedSum μ (fun x => K x x) + n * independentPair μ K) := by
  induction n with
  | zero =>
    rw [wordLaw_succ_sum]
    simp [wordLaw, pairSum, sumOn, weightedSum]
  | succ n ih =>
    rw [word_pair_step, ih]
    simp only [Nat.pow_succ, Nat.succ_mul, Nat.mul_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul,
      Nat.mul_one]
    ac_rfl

-- In Lean 4.19, Std's rational constructor reduces a fraction by the gcd.
private theorem mkRat_components (a b : Nat) (hb : 0 < b) :
    (mkRat a b).num = ((a / a.gcd b : Nat) : Int) ∧ (mkRat a b).den = b / a.gcd b := by
  simp only [mkRat, beq_iff_eq, Nat.ne_of_gt hb, if_false, Std.Internal.Rat.normalize,
    Int.natAbs_ofNat]
  by_cases h : a.gcd b = 1 <;> simp [h, ← Int.ofNat_tdiv]

private theorem rat_ext {a b : Std.Internal.Rat} (hn : a.num = b.num) (hd : a.den = b.den) :
    a = b := by
  cases a; cases b; congr

private theorem mkRat_scale (k a b : Nat) (hk : 0 < k) (hb : 0 < b) :
    mkRat (k * a : Nat) (k * b) = mkRat a b := by
  obtain ⟨hn₁, hd₁⟩ := mkRat_components (k * a) (k * b) (Nat.mul_pos hk hb)
  obtain ⟨hn₂, hd₂⟩ := mkRat_components a b hb
  apply rat_ext
  · rw [hn₁, hn₂, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hk]
  · rw [hd₁, hd₂, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hk]

private theorem mkRat_eq_of_cross {a b c d : Nat} (hb : 0 < b) (hd : 0 < d)
    (h : a * d = c * b) : mkRat a b = mkRat c d := by
  calc
    mkRat a b = mkRat (d * a : Nat) (d * b) := (mkRat_scale d a b hd hb).symm
    _ = mkRat (b * c : Nat) (b * d) := by
      rw [Nat.mul_comm d a, h, Nat.mul_comm c b, Nat.mul_comm d b]
    _ = mkRat c d := mkRat_scale b c d hb hd

/-- Exact expectation of the ordered-pair average under the finite product law.
Writing `W` for the total weight, `D` for the diagonal weighted sum, and `P`
for the independent-pair weighted sum, the right side is the single fraction
`(W*D + (N-1)*P)/(N*W²) = (D/W)/N + ((N-1)/N)*(P/W²)`. -/
theorem iid_pair_mean (μ : List (α × Nat)) (K : α → α → Nat) (N : Nat)
    (hμ : 0 < mass μ) (hN : 0 < N) :
    mkRat (weightedSum (wordLaw μ N) (pairSum K)) (N ^ 2 * mass (wordLaw μ N)) =
      mkRat (mass μ * weightedSum μ (fun x => K x x) + (N - 1) * independentPair μ K : Nat)
        (N * mass μ ^ 2) := by
  cases N with
  | zero => exact False.elim (Nat.lt_irrefl 0 hN)
  | succ n =>
    rw [mass_wordLaw, Nat.succ_sub_one]
    apply mkRat_eq_of_cross (Nat.mul_pos (Nat.pow_pos hN) (Nat.pow_pos hμ))
      (Nat.mul_pos hN (Nat.pow_pos hμ))
    have h := congrArg (fun t => t * ((n + 1) * mass μ)) (iid_pair_sum μ K n)
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using h

/-- Squared Frobenius error divided by `N²`, for any integer-valued error
kernel with a constant diagonal `δ`. The two terms are `|δ|²/N` and
`((N-1)/N) E[|err(X,Y)|²]` for independent `X,Y` of law `μ/W`. -/
theorem eq41_finite_iid (μ : List (α × Nat)) (N : Nat) (hμ : 0 < mass μ) (hN : 0 < N)
    (err : α → α → Int) (δ : Int) (hδ : ∀ x, err x x = δ) :
    mkRat (weightedSum (wordLaw μ N) (pairSum (fun x y => (err x y).natAbs ^ 2)))
        (N ^ 2 * mass (wordLaw μ N)) =
      mkRat (mass μ ^ 2 * δ.natAbs ^ 2 +
        (N - 1) * independentPair μ (fun x y => (err x y).natAbs ^ 2) : Nat)
        (N * mass μ ^ 2) := by
  let K (x y : α) := (err x y).natAbs ^ 2
  have hdiag : mass μ * weightedSum μ (fun x => K x x) = mass μ ^ 2 * δ.natAbs ^ 2 := by
    simp only [K, hδ, weightedSum_const, Nat.pow_two, Nat.mul_assoc]
  have h := iid_pair_mean μ K N hμ hN
  rw [hdiag] at h
  exact h

end MaternAudit.PairCounting
