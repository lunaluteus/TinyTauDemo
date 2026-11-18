/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli numerator tests below 100

A finite table evaluated by the kernel implements the rational Bernoulli
recurrence. This gives the arithmetic side of Kummer's criterion below 100.
See `/roadmap/index.qmd#rem-bernoulli-regular` @ `fab7b51d4239cbeaf0648041d4b248414760312d`.
-/

public section

open Finset

namespace TinyTauDemo

/-- The first `n` Bernoulli numbers in the positive-first convention, computed in order. -/
private def bernoulliTable : ℕ → List ℚ
  | 0 => []
  | n + 1 =>
    let values := bernoulliTable n
    values ++ [1 - ∑ i ∈ range n, (n.choose i : ℚ) / (n - i + 1) * values[i]?.getD 0]

private theorem bernoulliTable_length (n : ℕ) : (bernoulliTable n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bernoulliTable, ih]

private theorem bernoulliTable_get (n i : ℕ) (hi : i < n) :
    (bernoulliTable n)[i]?.getD 0 = bernoulli' i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [bernoulliTable]
    by_cases h : i < n
    · rw [List.getElem?_append_left (by rwa [bernoulliTable_length]), ih i h]
    · have he : i = n := by omega
      subst i
      rw [List.getElem?_append_right (by rw [bernoulliTable_length]), bernoulliTable_length,
        Nat.sub_self]
      change 1 - ∑ i ∈ range n, (n.choose i : ℚ) / (n - i + 1) *
        (bernoulliTable n)[i]?.getD 0 = bernoulli' n
      rw [bernoulli'_def]
      congr 1
      exact sum_congr rfl fun i h ↦ by rw [ih i (mem_range.mp h)]

/-- A witness for the first irregular index in the finite Bernoulli list. -/
theorem dvd_bernoulli_num_37 : (37 : ℤ) ∣ (bernoulli 32).num := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),
    ← bernoulliTable_get 33 32 (by decide)]
  decide +kernel

/-- The second exceptional Bernoulli numerator below 100. -/
theorem dvd_bernoulli_num_59 : (59 : ℤ) ∣ (bernoulli 44).num := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),
    ← bernoulliTable_get 45 44 (by decide)]
  decide +kernel

/-- The third exceptional Bernoulli numerator below 100. -/
theorem dvd_bernoulli_num_67 : (67 : ℤ) ∣ (bernoulli 58).num := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),
    ← bernoulliTable_get 59 58 (by decide)]
  decide +kernel

private theorem bernoulliTable_irregular_primes_below_100 :
    ((range 100).filter fun p ↦ p.Prime ∧ Odd p ∧
      ∃ k : Fin 49, 0 < k.val ∧ 2 * k.val ≤ p - 3 ∧
        (p : ℤ) ∣ ((bernoulliTable 97)[2 * k.val]?.getD 0).num) = {37, 59, 67} := by
  decide +kernel

/-- Among odd primes below 100, the Bernoulli numerator test fails at 37, 59, and 67. -/
theorem bernoulli_irregular_primes_below_100 {p : ℕ} (hp : p < 100)
    (hprime : p.Prime) (hodd : Odd p) :
    (∃ k : ℕ, 0 < k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num) ↔
      p = 37 ∨ p = 59 ∨ p = 67 := by
  have hmem : p ∈ ({37, 59, 67} : Finset ℕ) ↔ p = 37 ∨ p = 59 ∨ p = 67 := by simp
  rw [← hmem, ← bernoulliTable_irregular_primes_below_100, mem_filter,
    and_iff_right (mem_range.mpr hp), and_iff_right hprime, and_iff_right hodd]
  constructor
  · rintro ⟨k, hk, hlt, hdvd⟩
    have hkn : k < 49 := by omega
    have hkn' : 2 * k < 97 := by omega
    have hne : 2 * k ≠ 1 := by omega
    refine ⟨⟨k, hkn⟩, hk, hlt, ?_⟩
    change (p : ℤ) ∣ ((bernoulliTable 97)[2 * k]?.getD 0).num
    rwa [bernoulliTable_get 97 (2 * k) hkn', ← bernoulli_eq_bernoulli'_of_ne_one hne]
  · rintro ⟨k, hk, hlt, hdvd⟩
    have hkn' : 2 * k.val < 97 := by omega
    have hne : 2 * k.val ≠ 1 := by omega
    refine ⟨k.val, hk, hlt, ?_⟩
    rwa [bernoulliTable_get 97 (2 * k.val) hkn', ← bernoulli_eq_bernoulli'_of_ne_one hne] at hdvd

end TinyTauDemo
