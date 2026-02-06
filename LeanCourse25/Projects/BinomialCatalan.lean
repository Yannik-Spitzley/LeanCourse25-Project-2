/-
Project 2: Motzkin numbers: Definition, linear recursion, connection to Catalan numbers and
generating function
Authors: Yannik Spitzley
-/

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open Nat BigOperators Finset


/-
# Binomial and Catalan identities

Binomial coefficients and the Catalan numbers appear in a lot of interesting identities. This file
contains necessary identities for the proofs in `Motzkin.lean`.

## Main results

* `sum_choose_mul_choose`: A variation of the Chu-Vandermonde identity:
  `∑ i ∈ range n, choose i r * choose (n - 1 - i) s = choose n (r + s + 1)`.

* `touchard_identity`: Touchard's identity with an alternative recursion formula for the Catalan
  numbers: `∑ k ∈ range (n + 1), (choose n (2 * k) * catalan k) * 2 ^ (n - 2 * k) = catalan (n+1)`.

* `catalan_recurrence`: Gives another simple recursion formula for the Catalan numbers:
  `(n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n`.

* `sum_choose_mul_choose_mul_catalan`: Simplifies a certain sum of products of binomial
  coefficients and Catalan numbers to a single product:
  `∑ k ∈ range (n+1), n.choose k * k.choose (2*j) * catalan j = n.choose (2*j)*catalan j*2^(n-2*j)`
-/


/-- A variation of the Chu-Vandermonde identity: Simplifies a sum of products of binomial
    coefficients to a single binomial coefficient. -/
theorem sum_choose_mul_choose (n r s : ℕ) :
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
      rw [ih, add_comm, ← choose_succ_succ]

    | succ s =>
      simp

      -- Rewrite the sum into 2 separate sums
      have h_pascal : ∀ i ∈ range n,
          choose (n - i) (s + 1) = choose (n - 1 - i) (s + 1) + choose (n - 1 - i) s := by
        intro i hi
        have h_idx : n - i = (n - 1 - i) + 1 := by grind
        rw [h_idx, choose_succ_succ, add_comm]

      rw [sum_congr rfl (fun i hi => by rw [h_pascal i hi])]
      simp only [mul_add]
      rw [sum_add_distrib]

      -- Use the induction hypothesis
      rw [ih (s + 1), ih s, add_comm, add_assoc r s 1, ← choose_succ_succ]


/-- A technical lemma for an identity between binomial coefficients and the Catalan numbers. -/
lemma binomial_convolution (n a b : ℕ) :
    ∑ i ∈ range n, choose i (2 * a) * catalan a * (choose (n - 1 - i) (2 * b) * catalan b) =
    catalan a * catalan b * choose n (2 * a + 2 * b + 1) := by

  calc
    ∑ i ∈ range n, choose i (2 * a) * catalan a * (choose (n - 1 - i) (2 * b) * catalan b)
    -- Use commutativity and associativity inside the sum to prepare the constants for the next step
    _ = ∑ i ∈ range n, catalan a * (catalan b * (choose i (2*a) * choose (n-1-i) (2*b))) := by
      grind
    -- Pull the constants out of the sum and simplify the remaining sum
    _ = catalan a * catalan b * choose n (2 * a + 2 * b + 1) := by
      rw [← mul_sum, ← mul_sum, sum_choose_mul_choose]
      ring


/-- A technical lemma to simplify a sum of Catalan numbers to the product of a single Catalan
    number and binomial coefficient. -/
lemma simplify_catalan_sum (n : ℕ) : ∀ k ∈ range n,
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


/-- Touchard's identity: Gives an alternative recursion formula for the Catalan numbers. -/
theorem touchard_identity (n : ℕ) :
  ∑ k ∈ range (n + 1), (choose n (2 * k) * catalan k) * 2 ^ (n - 2 * k) = catalan (n + 1) := by
  sorry


/-- A simple recursion formula for the Catalan numbers. -/
theorem catalan_recurrence (n : ℕ) :
  (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by

  -- Express the catalan numbers in terms of the central binomial coefficient
  rw [catalan_eq_centralBinom_div, catalan_eq_centralBinom_div]

  -- Multiply both sides with n+1
  apply eq_of_mul_eq_mul_right (succ_pos n)

  -- Rearrange both sides
  rw [mul_comm _ (n + 1), mul_assoc]

  -- Simplify both sides
  rw [Nat.mul_div_cancel' (n + 1).succ_dvd_centralBinom, Nat.div_mul_cancel n.succ_dvd_centralBinom]

  -- Use an identity of the central binomial coefficient
  rw [succ_mul_centralBinom_succ]


/-- Simplifies a certain sum of products of binomial coefficients and Catalan numbers to a single
    product. -/
theorem sum_choose_mul_choose_mul_catalan (n j : ℕ) :
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
    rw [sum_Ico_eq_sum_range]

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
