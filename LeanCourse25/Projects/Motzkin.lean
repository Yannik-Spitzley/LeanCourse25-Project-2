/-
Project 2: ## Project 2: Motzkin numbers: Definition, linear recursion, connection to Catalan
numbers, generating function and geometric interpreation
Authors: Yannik Spitzley
-/

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

import LeanCourse25.Projects.BinomialCatalan

open Nat BigOperators Finset PowerSeries


/-
# Motzkin numbers

The Motzkin numbers (https://oeis.org/A001006) enumerate many combinatorial objects, for example
the number of different ways of drawing non-intersecting chords between n points on a circle, where
not necessarily every point has to be connected with a chord. They also have interesting connections
to the Catalan numbers.

## Main definitions

* `motzkin n`: The n-th Motzkin number, defined recursively as
  `motzkin (n+1) = motzkin n + ∑ i ∈ range n, motzkin i * motzkin (n-1-i)` and `motzkin 0 = 1`.

* `motzkin_series`: The generating functions of the Motzkin numbers.

* `is_chord`: The property of an orderer pair (of ℕ × ℕ) to model a chord between 2 of n points on
  a circle.

* `are_chords_intersecting`: The property whether 2 chords are intersecting each other.

* `chord_configuration n`: A set of non-intersecting chords between n points on a circle.

## Main results

* `motzkin_eq_catalan`: Expresses the n-th Motzkin number in terms of the Catalan numbers with the
  identity `motzkin n = ∑ k ∈ range (n + 1), choose n (2 * k) * catalan k`.

* `catalan_eq_motzkin`: Expresses the (n+1)-th Catalan number in terms of the Motzkin numbers with
  the identity `catalan (n+1) = ∑ k ∈ range (n+1), choose n k * motzkin k`.

* `motzkin_linear_recurrence`: A linear recursion formula for the Motzkin numbers:
  `(n + 2) * motzkin n = (2 * n + 1) * motzkin (n - 1) + 3 * (n - 1) * motzkin (n - 2)`.

* `motzkin_series_eq_one_add_mul_add_sq`: The generating function `m(x)` of the Motzkin numbers
  satisfies the identity `m(x) = 1 + x*m(x) + x^2*m(x)^2`.

* `motzkin_series_closed_form_algebraic`: An explicit closed formula for the generating function:
  `(2 * X ^ 2 * motzkin_series - (1 - X)) ^ 2 = 1 - 2 * X - 3 * X ^ 2`.

* `motzkin_card_chord_configuration`: The number of non-intersecting chords between n points on a
  circle is exactly the n-th Motzkin number: `Fintype.card (chord_configuration n) = motzkin n`.
-/



/- # Main definition and simple theorems
    This section contains the main definition of the Motzkin numbers as well as some very
    simple theorems. -/

/-- The `n-th motzkin number` is defined by a standard recursion formula, that follows from the
    geometric interpretation. It can be used with `motzkin n`. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | (n + 1) => motzkin n + ∑ i ∈ (range n).attach,
      -- Show that both recursive calls use smaller indices
      have : i.1 < n + 1 := lt_succ_of_lt (mem_range.mp i.2)
      have : n - 1 - i.1 < n + 1 := by omega

      motzkin i.1 * motzkin (n - 1 - i.1)
termination_by n => n


/-- The first 2 Motzkin numbers. -/
@[simp]
theorem motzkin_zero : motzkin 0 = 1 := by rw [motzkin]

@[simp]
theorem motzkin_one : motzkin 1 = 1 := by simp [motzkin]





/- # Connection to the Catalan numbers
  This section will establish the connection between the Motzkin numbers and the Catalan numbers as
  each number can be expressed through the others. -/

/-- The expression of the `n-th motzkin number` in terms of the Catalan numbers. For better
    readability as its own definition.
    `Remark:` The sum usually only goes until `k = floor(n/2)`, which is mathematically equivalent
    to the given definition as the additional binomial coefficients are all 0. -/
private def motzkin_closed_form (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (choose n (2 * k)) * catalan k


/-- A technical lemma extending the range of sums as the additional binomial coefficients are 0. -/
private lemma inner_sum_extensions (n : ℕ) : ∀ i ∈ range n,
    ∑ a ∈ range (i + 1), ∑ b ∈ range (n - 1 - i + 1), choose i (2 * a) * catalan a *
      (choose (n - 1 - i) (2 * b) * catalan b) =
    ∑ a ∈ range n, ∑ b ∈ range (n-a), choose i (2 * a) * catalan a *
      (choose (n - 1 - i) (2 * b) * catalan b) := by

  -- Introduce i
  intro i hi

  -- Divide the goal into 2 separate goals, each taking care of the extension of one sum
  trans ∑ a ∈ range (i + 1), ∑ b ∈ range (n - a), choose i (2 * a) * catalan a *
      (choose (n - 1 - i) (2 * b) * catalan b)

  -- Goal 1: Extension of the inner sum
  · apply sum_congr rfl
    intro a ha

    apply sum_subset
    · grind
    · intro b _ hb_not
      rw [choose_eq_zero_of_lt (by grind : n - 1 - i < 2 * b)]
      simp

  -- Goal 2: Extension of the outer sum
  · apply sum_subset
    · grind
    · intro a _ ha_not
      rw [choose_eq_zero_of_lt (by grind)]
      simp


/-- A technical lemma to transform a triangular shaped sum `∑_{i=0}^n ∑_{k=0}^{n-i} [...]` to an
    equivalent diagonal shaped sum `∑_k ∑_{a+b=k} [...]`. -/
private lemma triangle_to_diagonal {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    ∑ a ∈ range n, ∑ b ∈ range (n - a), f a b =
    ∑ k ∈ range n, ∑ x ∈ antidiagonal k, f x.1 x.2 := by

  have h_lhs : (∑ a ∈ range n, ∑ b ∈ range (n - a), f a b) =
               (∑ x ∈ (range n).sigma (fun a => range (n - a)), f x.1 x.2) :=
    (sum_sigma (range n) (fun a => range (n - a)) (fun x => f x.1 x.2)).symm

  have h_rhs : (∑ k ∈ range n, ∑ x ∈ antidiagonal k, f x.1 x.2) =
               (∑ x ∈ (range n).sigma (fun k => antidiagonal k), f x.2.1 x.2.2) :=
    (sum_sigma (range n) (fun k => antidiagonal k) (fun x => f x.2.1 x.2.2)).symm
  rw [h_lhs, h_rhs]

  apply sum_bij (fun s _ => ⟨s.1 + s.2, (s.1, s.2)⟩)

  -- Goal 1
  · rintro ⟨a, b⟩ h
    simp only [mem_sigma, mem_range] at h ⊢
    rcases h with ⟨ha, hb⟩
    constructor
    · exact add_lt_of_lt_sub' hb
    · rw [mem_antidiagonal]

  -- Goal 2
  · grind

  -- Goal 3
  · rintro ⟨k, p⟩ h
    simp only [mem_sigma, mem_range, mem_antidiagonal] at h ⊢
    rcases p with ⟨x, y⟩
    use ⟨x, y⟩
    grind

  -- Goal 4
  · exact fun a ha ↦ rfl


/-- Main technical theorem: Rewrites a sum of products of Motzkin numbers (that can be expressed
    through Catalan numbers) to a sum of binomial coefficients and Catalan numbers. -/
private theorem convolution_identity_closed_form (n : ℕ) :
    ∑ i ∈ range n, motzkin_closed_form i * motzkin_closed_form (n - 1 - i) =
    ∑ k ∈ range n, (choose n (2 * k + 1)) * catalan (k + 1) := by

  -- Step 1: Unfold the definition.
  unfold motzkin_closed_form

  -- Step 2: Rewrite the product of nested sums.
  rw [sum_congr rfl (fun i _ => sum_mul _ _ _)]
  rw [sum_congr rfl (fun i _ => sum_congr rfl (fun a _ => mul_sum _ _ _))]

  -- Step 3: Extend the inner sums so they can be swapped with the outer sum.
  -- This is viable as the binomial coefficients in the new summands are 0.
  rw [sum_congr rfl (inner_sum_extensions n)]

  -- Step 4: Swap the outer sum to the inside.
  rw [sum_comm]
  rw [sum_congr rfl (fun a _ => sum_comm)]

  -- Step 5: Take the Catalan numbers out of the innermost sum and simplify the remaining sum with
  -- a variation of the Chu-Vandermonde identity.
  rw [sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => binomial_convolution n a b))]

  -- Step 6: Transform the triangular shaped sum to a diagonal shaped sum.
  rw [triangle_to_diagonal]

  -- Step 7: Simplify the inner sum to the product of a Catalan number and a binomial coefficient.
  rw [sum_congr rfl (simplify_catalan_sum n)]


/-- Main theorem 1: Expresses the n-th Motzkin number in terms of the Catalan numbers. -/
theorem motzkin_eq_catalan (n : ℕ) : motzkin n = motzkin_closed_form n := by
  -- We prove the theorem with strong induction
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [motzkin_closed_form] -- Base case n=0
    | (m + 1) => -- Induction step

      -- Step 1: Unfold the definition and simplify
      unfold motzkin
      simp

      -- Step 2: Use the induction hypothesis on the left hand side in the sum and the first summand
      have h_sum_rewrite_ih:
          (∑ i ∈ (range m).attach, motzkin ↑i * motzkin (m - 1 - ↑i)) =
          (∑ i ∈ range m, motzkin_closed_form i * motzkin_closed_form (m - 1 - i)) := by
        apply sum_bij (fun i _ => i.1)
        · exact fun a ha ↦ coe_mem a
        · exact fun a₁ ha₁ a₂ ha₂ a ↦ Subtype.eq a
        · intro b hb
          use ⟨b, hb⟩
          simp
        · intro x hx
          grind

      rw [h_sum_rewrite_ih, ih m (lt_succ_self m)]

      -- Step 3: Use the auxiliary lemma to replace the sum on the left hand side
      rw [convolution_identity_closed_form m]

      -- Step 4: Unfold the definition of the closed motzkin formulation
      unfold motzkin_closed_form

      -- Step 5: Split the k=0 term on both sides and simplify
      rw [sum_range_succ']
      conv_rhs => rw [sum_range_succ']
      simp

      -- Step 6: Use Pascal's identity to split the right sum into 2 sums
      simp_rw [mul_add, mul_one, choose_succ_succ, add_mul, sum_add_distrib]

      -- Step 7: Adjust the sum ranges on the left hand side to m+1
      rw [sum_subset (range_mono (by omega : m ≤ m + 1)) (fun x _ hx => by
        rw [mem_range, not_lt] at hx
        apply mul_eq_zero_of_left; apply choose_eq_zero_of_lt; omega)]

      rw [sum_subset (range_mono (by omega : m ≤ m + 1)) (fun x _ hx => by
        rw [mem_range, not_lt] at hx
        apply mul_eq_zero_of_left; apply choose_eq_zero_of_lt; omega)]

      ring


/-- Main theorem 2: Expresses any Catalan number in terms of the Motzkin numbers. -/
theorem catalan_eq_motzkin (n : ℕ) : catalan (n+1) = ∑ k ∈ range (n+1), choose n k * motzkin k := by

  -- Internally, we swap the sides of the equation
  apply symm

  -- Step 1: Use the first main theorem
  simp_rw [motzkin_eq_catalan, motzkin_closed_form]

  calc
    ∑ k ∈ range (n+1), choose n k * ∑ j ∈ range (k+1), choose k (2 * j) * catalan j

    -- Step 2: Move the binomial coefficient into the inner sum
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1), choose n k * (choose k (2 * j) * catalan j) := by
      rw [sum_congr rfl]
      intro x hx
      rw [mul_sum (range (x + 1)) (fun i ↦ x.choose (2 * i) * catalan i) (n.choose x)]

    -- Step 3 : Extend the inner sum
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1), choose n k * (choose k (2 * j) * catalan j) := by
      apply sum_congr rfl
      intro k hk
      rw [mem_range] at hk

      apply sum_subset (range_mono (by omega : k + 1 ≤ n + 1))
      intro j _ hj_out
      rw [choose_eq_zero_of_lt (by grind : k < 2 * j)]
      ring

    -- Step 4: Swap the inner with the outer sum
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1), choose n j * (choose j (2 * k) * catalan k) := by
      rw [sum_comm]

    -- Step 5: Simplify the new inner sum
    _ = ∑ k ∈ range (n + 1), (choose n (2 * k) * catalan k) * 2 ^ (n - 2 * k) := by
      simp_rw [sum_choose_mul_choose_mul_catalan]

    -- Step 6:
    _ = catalan (n + 1) := by rw [touchard_identity]





/- # A linear recursion formula
  This section will establish a simpler recursion formula, where the n-th Motzkin number depends
  only on the previous 2 Motzkin numbers. -/

/-- Main theorem 3: A linear recursion formula for the Motzkin numbers. -/
theorem motzkin_linear_recurrence (n : ℕ) (h_ge_2 : 2 ≤ n) :
  (n + 2) * motzkin n = (2 * n + 1) * motzkin (n - 1) + 3 * (n - 1) * motzkin (n - 2) := by

  -- Step 1: Expresses all Motzkin numbers through Catalan numbers and push the constant factors
  -- in the sums.
  simp_rw [motzkin_eq_catalan, motzkin_closed_form, mul_sum]

  -- Step 2: Clean the sum ranges
  have h_idx1 : n - 1 + 1 = n := by omega
  have h_idx2 : n - 2 + 1 = n - 1 := by omega
  rw [h_idx1, h_idx2]


  -- Step 3: Extend all sum ranges to n+1
  rw [sum_subset (range_mono (le_succ n))
      (by
        intro k _ hk_new
        have : n - 1 < 2 * k := by grind
        rw [choose_eq_zero_of_lt this, zero_mul, mul_zero]
      )]

  rw [sum_subset (range_mono (by omega : n - 1 ≤ n + 1))
      (by
        intro k _ hk_new
        have : n - 2 < 2 * k := by grind
        rw [choose_eq_zero_of_lt this, zero_mul, mul_zero]
      )]


  -- Step 4: Combine the sums
  rw [← sum_add_distrib]


  sorry





/- # Generating function
  This section will establish the generating function of the Motzkin numbers and give an explicit
  expression of it. -/

/-- The definition of the generating function of the Motzkin numbers. -/
def motzkin_series : PowerSeries ℚ := mk (fun n => (motzkin n : ℚ))


/-- Main theorem 4: An important identity satisfied by the generating function. -/
theorem motzkin_series_eq_one_add_mul_add_sq :
  motzkin_series = 1 + X * motzkin_series + X ^ 2 * motzkin_series ^ 2 := by

  -- Compare the coefficients
  ext n
  simp only [map_add, coeff_one]

  cases n with
  -- n=0
  | zero => simp [motzkin_series]
  | succ n =>
    rw [pow_two, mul_assoc, ← pow_one X]
    simp only [coeff_X_pow_mul]

    cases n with
    -- n = 1
    | zero => simp [motzkin_series]

    -- n ≥ 2
    | succ m =>

      rw [coeff_X_pow_mul]
      rw [pow_two, coeff_mul]
      rw [Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => coeff i motzkin_series * coeff j motzkin_series)]

      simp only [motzkin_series, coeff_mk]

      rw [motzkin.eq_def (m + 1 + 1)]
      simp
      rw [sum_attach (f := fun x => (motzkin x : ℚ) * (motzkin (m - x) : ℚ))]


/-- Main theorem 5: An explicit expression of the generating function. -/
theorem motzkin_series_closed_form_algebraic :
    (2 * X ^ 2 * motzkin_series - (1 - X)) ^ 2 = 1 - 2 * X - 3 * X ^ 2 := by

  -- Rearrange the terms and proceed with the previous theorem
  calc
    (2 * X ^ 2 * motzkin_series - (1 - X)) ^ 2
    _ = 4 * X ^ 2 * (1 + X * motzkin_series + X ^ 2 * motzkin_series ^ 2)
        - 4 * X ^ 2 * motzkin_series - 4 * X ^ 2 + (1 - X) ^ 2 := by ring
    _ = 1 - 2 * X - 3 * X ^ 2 := by
      rw [← motzkin_series_eq_one_add_mul_add_sq]
      ring





/- # Geometric interpretation
  This section will connect the formal definition through the given recursion formula and the
  geometric interpretation as the number of different ways of drawing non-intersecting chords
  between n points on a circle, where not necessarily every point has to be connected with a chord.

  We will model the `n` points on the circle with the indices `0, 1, ..., n-1`. -/

/-- A `chord` (on `n` points) is defined as an orderer pair `(i, j) : ℕ × ℕ` with `i < j < n`. -/
def is_chord (n : ℕ) (p : ℕ × ℕ) : Prop := p.1 < p.2 ∧ p.2 < n


/-- Two chords `(i, j)` and `(k, l)` `intersect` if and only if `i < k < j < l`. -/
def are_chords_intersecting (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2


/-- A `configuration` of chords on `n` points is a set of non-intersecting chords on `n` points. -/
structure chord_configuration (n : ℕ) where
  -- The chosen chords
  chords : Finset (ℕ × ℕ)
  -- All chords need to be in the correct structure and connect exactly two of the n points.
  valid_indices : ∀ p ∈ chords, is_chord n p
  -- No two chords can have a point in common
  disjoint : ∀ p ∈ chords, ∀ q ∈ chords, p ≠ q →
             ({p.1, p.2} : Finset ℕ) ∩ {q.1, q.2} = ∅
  -- No two chords are intersecting
  non_intersecting : ∀ p ∈ chords, ∀ q ∈ chords, ¬ are_chords_intersecting p q


/-- `chord_configuration n` is a finite set. -/
noncomputable instance (n : ℕ) : Fintype (chord_configuration n) := by

  -- Define the set of all possible chords (on n points)
  let valid_chords := ((range n).product (range n)).filter (fun x => x.1 < x.2)

  apply Fintype.ofInjective
    (fun c => (⟨c.chords, by
      -- We prove that c.chords in the powerset of valid_chords is
      rw [mem_powerset]
      intro p hp

      simp [valid_chords, mem_filter]
      obtain ⟨h_lt, h_bound⟩ := c.valid_indices p hp
      omega
    ⟩ : ↥(valid_chords.powerset)))

  -- Show injectivity
  intro c1 c2 h
  cases c1; cases c2
  simp at *
  exact h


/-- Main theorem 6: Geometric interpreation - the number of valid chord_configurations on n points
    is exactly the n-th Motzkin number. -/
theorem motzkin_card_chord_configuration (n : ℕ) :
    Fintype.card (chord_configuration n) = motzkin n := by

  /- Proof sketch:
    * We can partition the number of chord configurations into two disjunct subsets S₁ ∪ S₂: The
      ones that have a chord connecting the point n-1 and the ones that don't.

    * Case 1: Point n-1 is not connected through a chord. Then the points 0, 1, ..., n-2 can still
      be connected through a chord and we get a bijection S₁ ≃ chord_configuration n-1, which has
      by the induction hypothesis cardinality motzkin (n-1).

    * Case 2: Point n-1 is connected through a chord to point k < n-1. This divides the circle in
      two separate areas, one with the points 0, 1, 2, ..., k-1 and one with the points k+1, k+2,
      ..., n-2. As no other chord can intersect the given chord (k, n-1), we can count the
      combinations as motzkin k * motzkin (n-2-k). Summing up over all possible values of k,
      we get |S₂| = ∑ k ∈ range (n-1), motzkin k * motzkin (n-2-k).

    * Combining both statements, we get exactly the recursion formula from the definition.
  -/

  sorry
