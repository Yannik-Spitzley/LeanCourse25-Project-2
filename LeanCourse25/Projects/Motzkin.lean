/-
Project 2: Motzkin numbers: Definition, linear recursion, connection to Catalan numbers and generating function
Authors: Yannik Spitzley
-/
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Tactic

open Nat BigOperators Finset


/-
# Motzkin numbers

The Motzkin numbers (https://oeis.org/A001006) enumerate many combinatorical objects, for example
the number of different ways of drawing non-intersecting chords between n points on a circle, where
not necessarily every point has to be connected with a chord. They also have interesting connections
to the Cataln numbers.

## Main Definitions

* ToDo

## Main results

* ToDo
-/


-- # Main Definition
-- The recursive definition of the sequence of Motzkin numbers
def motzkin : ℕ → ℕ
  | 0 => 1
  | (n + 1) => motzkin n + ∑ i ∈ (range n).attach,
      -- Show that both recursive calls use smaller indices
      have : i.1 < n + 1 := by exact Nat.lt_succ_of_lt (mem_range.mp i.2)
      have : n - 1 - i.1 < n + 1 := by omega

      motzkin i.1 * motzkin (n - 1 - i.1)
termination_by n => n



-- # Simple theorems
@[simp]
theorem motzkin_zero : motzkin 0 = 1 := by rw [motzkin]

@[simp]
theorem motzkin_one : motzkin 1 = 1 := by simp [motzkin]



/- # Connection to the Catalan numbers (for better readability as its own definition)
  Note: The sum usually only goes until floor(n/2), which is mathematically equivalent as the
  additional binomial coefficients are all 0.-/
private def motzkin_closed_form (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), (choose n (2 * k)) * catalan k



/- # Technical lemmas
  We can extend the range of the sums as the additional binomial coefficients are 0.-/
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


-- A binomial identity
private lemma choose_mul_choose_sum (n r s : ℕ) :
    ∑ i ∈ range n, choose i r * choose (n - 1 - i) s = choose n (r + s + 1) := by

  -- Use induction
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]

    cases s with
    | zero =>
      specialize ih 0
      simp only [choose_zero_right, mul_one] at *
      rw [ih, add_comm, ← Nat.choose_succ_succ]

    | succ s =>
      simp

      -- Rewrite the sum into 2 separate sums
      have h_pascal : ∀ i ∈ range n,
          choose (n - i) (s + 1) = choose (n - 1 - i) (s + 1) + choose (n - 1 - i) s := by
        intro i hi
        have h_idx : n - i = (n - 1 - i) + 1 := by grind
        rw [h_idx, Nat.choose_succ_succ, add_comm]

      rw [sum_congr rfl (fun i hi => by rw [h_pascal i hi])]
      simp only [mul_add]
      rw [sum_add_distrib]

      -- Use the induction hypothesis
      rw [ih (s + 1), ih s, add_comm, add_assoc r s 1, ← Nat.choose_succ_succ]


-- A binomial identity similar to Vandermonde's identity.
private lemma binomial_identity (n a b : ℕ) :
    ∑ i ∈ range n, choose i (2 * a) * choose (n-1-i) (2 * b) = choose n (2 * a + 2 * b + 1) := by

  apply choose_mul_choose_sum


/- A sum similar to the above identity with additional constant factors inside. The factors are
  pulled out of the sum, which can be simplified using the above identity.-/
private lemma binomial_convolution (n a b : ℕ) :
    ∑ i ∈ range n, choose i (2 * a) * catalan a * (choose (n - 1 - i) (2 * b) * catalan b) =
    catalan a * catalan b * choose n (2 * a + 2 * b + 1) := by

  calc
    ∑ i ∈ range n, choose i (2 * a) * catalan a * (choose (n - 1 - i) (2 * b) * catalan b)
    -- Use commutivity and associativity inside the sum to prepare the constants for the next step
    _ = ∑ i ∈ range n, catalan a * (catalan b * (choose i (2*a) * choose (n-1-i) (2*b))) := by
      grind
    -- Pull the constants out of the sum and simplify the remaining sum
    _ = catalan a * catalan b * choose n (2 * a + 2 * b + 1) := by
      rw[← mul_sum, ← mul_sum, binomial_identity]
      ring


/- Transforms a triangular shaped sum `∑_{i=0}^n ∑_{k=0}^{n-i} [...] ` to an equivalent diagonal
  shaped sum `∑_k ∑_{a+b=k} [...]`. -/
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


/- Simplify a sum of Catalan numbers to the product of a single Catalan number and
  binomial coefficient. -/
private lemma simplify_catalan_sum (n : ℕ) : ∀ k ∈ range n,
    ∑ x ∈ antidiagonal k, catalan x.1 * catalan x.2 * choose n (2 * x.1 + 2 * x.2 + 1) =
    choose n (2 * k + 1) * catalan (k + 1) := by

  -- Introduce k
  intro k hk

  calc
    ∑ x ∈ antidiagonal k, catalan x.1 * catalan x.2 * choose n (2 * x.1 + 2 * x.2 + 1)

    -- Simplify the binomial coefficient to a constant
    _ = ∑ x ∈ antidiagonal k, catalan x.1 * catalan x.2 * choose n (2 * k + 1) := by
      rw [sum_congr rfl]
      intro x hx
      rw [mem_antidiagonal] at hx
      rw [← mul_add 2 x.1 x.2, hx]

    -- Pull the binomial coefficient out of the sum and use the Catalan recursion
    _ = choose n (2 * k + 1) * catalan (k + 1) := by rw [← sum_mul, ← catalan_succ', mul_comm]


/- Main technical lemma: Rewrites a sum of products of motzkin numbers (in closed formulation)
  to a sum of binomial coefficients and Catalan numbers. -/
private lemma convolution_identity_closed_form (n : ℕ) :
    ∑ i ∈ range n, motzkin_closed_form i * motzkin_closed_form (n - 1 - i) =
    ∑ k ∈ range n, (choose n (2 * k + 1)) * catalan (k + 1) := by

  -- Step 1: Unfold the definition.
  unfold motzkin_closed_form

  -- Step 2: Rewrite the product of nested sums.
  rw [sum_congr rfl (fun i _ => sum_mul _ _ _)]
  rw [sum_congr rfl (fun i _ => sum_congr rfl (fun a _ => mul_sum _ _ _))]

  -- Step 3: Extend the inner sums so they can be swaped with the outer sum.
  -- This is viable as the binomial coefficients in the new summands are 0.
  rw [sum_congr rfl (inner_sum_extensions n)]

  -- Step 4: Swap the outer sum to the inside.
  rw [sum_comm]
  rw [sum_congr rfl (fun a _ => sum_comm)]

  -- Step 5: Take the Catalan numbers out of the innermost sum and simplify the remaining sum with
  -- a binomial identity.
  rw [sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => binomial_convolution n a b))]

  -- Step 6: Transform the triangular shaped sum to a diagonal shaped sum.
  rw [triangle_to_diagonal]

  -- Step 7: Simplify the inner sum to the product of a Catalan number and a binomial coefficient.
  rw [sum_congr rfl (simplify_catalan_sum n)]



-- Main theorem 1: Expresses any Motzkin number in terms of the Catalan numbers
theorem motzkin_eq_closed_form (n : ℕ) : motzkin n = motzkin_closed_form n := by
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
      rw [Finset.sum_range_succ']
      conv_rhs => rw [Finset.sum_range_succ']
      simp

      -- Step 6: Use Pascal's idendity to split the right sum into 2 sums
      simp_rw [mul_add, mul_one, choose_succ_succ, add_mul, sum_add_distrib]

      -- Step 7: Adjust the sum ranges on the left hand side to m+1
      rw [sum_subset (Finset.range_mono (by omega : m ≤ m + 1)) (fun x _ hx => by
        rw [mem_range, not_lt] at hx
        apply mul_eq_zero_of_left; apply choose_eq_zero_of_lt; omega)]

      rw [sum_subset (Finset.range_mono (by omega : m ≤ m + 1)) (fun x _ hx => by
        rw [mem_range, not_lt] at hx
        apply mul_eq_zero_of_left; apply choose_eq_zero_of_lt; omega)]

      ring





-- Another technical lemma to simplify a sum
private lemma simplify_inner_sum (n j : ℕ) :
    ∑ k ∈ range (n + 1), choose n k * (choose k (2 * j) * catalan j) =
    (choose n (2 * j) * catalan j) * 2 ^ (n - 2 * j) := by

  -- Distinguish 2 cases
  by_cases h_le : 2 * j ≤ n

  -- Case 1: 2j <= n
  · -- Restrict the sum
    rw [← sum_subset (s₁ := Ico (2 * j) (n + 1))
        (by intro x hx; rw [mem_range]; exact (mem_Ico.mp hx).2)
        (by
            intro k hk_range hk_not_ico
            have hk_lt : k < 2 * j := by
              rw [mem_range] at hk_range; rw [mem_Ico] at hk_not_ico
              omega
            rw [choose_eq_zero_of_lt hk_lt, zero_mul]
            rfl
        )]

    -- Index shift
    rw [Finset.sum_Ico_eq_sum_range]

    calc
      ∑ x ∈ range (n + 1 - 2 * j), n.choose (2*j+x) * ((2*j+x).choose (2*j) * catalan j)

      -- Reorder terms and use an identity to transform the product of binomial coefficients
      _ = ∑ x ∈ range (n+1-2*j), (n.choose (2*j) * catalan j) * (n-2*j).choose (2*j+x - 2*j) := by
        rw [sum_congr rfl]
        intro x hx
        rw [← mul_assoc, choose_mul ?_ (le_add_right (2 * j) x)]
        · ring
        · grind

      -- Pull out constant terms and simplify
      _= (n.choose (2*j) * catalan j) * ∑ x ∈ range (n+1-2*j), (n-2*j).choose x := by
        simp
        exact Eq.symm
            (mul_sum (range (n + 1 - 2 * j)) (n - 2 * j).choose (n.choose (2 * j) * catalan j))

      -- Modify the sum range slightly
      _= (n.choose (2*j) * catalan j) * ∑ x ∈ range (n-2*j+1), (n-2*j).choose x := by
        rw [← tsub_add_eq_add_tsub h_le]

      -- Use another binomial identity to compute the sum
      _= (n.choose (2*j) * catalan j) * 2 ^ (n - 2 * j) := by rw [sum_range_choose]

  -- Case 2: 2j > n
  · rw [choose_eq_zero_of_lt (by omega), zero_mul, zero_mul]
    apply sum_eq_zero
    intro k hk
    rw [choose_eq_zero_of_lt (by grind : k < 2 * j)]
    ring


-- Touchard Identity
private lemma touchard_identity (n : ℕ) :
  ∑ k ∈ range (n + 1), (choose n (2 * k) * catalan k) * 2 ^ (n - 2 * k) = catalan (n + 1):= by
  sorry



-- Main theorem 2: Expresses any Catalan number in terms of the Motzkin numbers
theorem catalan_as_motzkin (n : ℕ) : catalan (n+1) = ∑ k ∈ range (n+1), choose n k * motzkin k := by

  -- Internally, we swap the sides of the equation
  apply Eq.symm

  -- Step 1: Use the first main theorem
  simp_rw [motzkin_eq_closed_form, motzkin_closed_form]

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

      apply sum_subset (Finset.range_mono (by omega : k + 1 ≤ n + 1))
      intro j _ hj_out
      rw [choose_eq_zero_of_lt (by grind : k < 2 * j)]
      ring

    -- Step 4: Swap the inner with the outer sum
    _ = ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1), choose n j * (choose j (2 * k) * catalan k) := by
      rw [sum_comm]

    -- Step 5: Simplify the new inner sum
    _ = ∑ k ∈ range (n + 1), (choose n (2 * k) * catalan k) * 2 ^ (n - 2 * k) := by
      simp_rw [simplify_inner_sum]

    -- Step 6:
    _ = catalan (n + 1) := by rw [touchard_identity]





-- Catalan Recursion
private lemma catalan_recurrence (n : ℕ) :
  (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by

  -- Express the catalan numbers in terms of the central binomial coefficient
  rw [catalan_eq_centralBinom_div, catalan_eq_centralBinom_div]

  -- Multiply both sides with n+1
  apply eq_of_mul_eq_mul_right (succ_pos n)

  -- Rearrange both sides
  rw [mul_comm _ (n + 1), mul_assoc]

  -- Simplify both sides
  rw [Nat.mul_div_cancel' (n + 1).succ_dvd_centralBinom, Nat.div_mul_cancel n.succ_dvd_centralBinom]

  -- Use an idendity of the central binomial coefficient
  rw [succ_mul_centralBinom_succ]
