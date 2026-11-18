/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Bernoulli.BernoulliTeichmuller

/-!
# Odd Teichmüller Bernoulli product

One factor supplies a single denominator of p. The divisibility of the normalized
product is then detected by the ordinary Bernoulli numerators.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `f606bbe053030c54bf1ead8056feefc1a552d822`.
-/

public section

open Finset

namespace TinyTauDemo

variable {p : ℕ} [Fact p.Prime]

private theorem padicInt_toZMod_eq_zero_iff_dvd (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

private theorem padicInt_toZMod_eq_zero_iff_exists (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ ∃ c : ℤ_[p], (x : ℚ_[p]) = (p : ℚ_[p]) * c := by
  rw [padicInt_toZMod_eq_zero_iff_dvd]
  change (∃ c : ℤ_[p], x = (p : ℤ_[p]) * c) ↔ _
  apply exists_congr
  intro c
  rw [← PadicInt.coe_inj, PadicInt.coe_mul, PadicInt.coe_natCast]

private theorem exists_integral_generalizedBernoulli_of_odd_index (hp2 : 2 < p)
    {i : ℕ} (hi : Odd i) (hd : ¬ (p - 1) ∣ i + 1) :
    ∃ c : ℤ_[p],
      (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1 = (c : ℚ_[p]) := by
  let S : ℤ_[p] := ∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i
  have hS : PadicInt.toZMod S = 0 := by
    dsimp only [S]
    rw [padicTeichWeightedSum_toZMod, ite_eq_right hd]
  obtain ⟨c, hc⟩ := (padicInt_toZMod_eq_zero_iff_exists S).mp hS
  have h := padicTeichmullerCharacter_generalizedBernoulli_one hp2 hi
  change (p : ℚ_[p]) * (padicTeichmullerCharacter ^ i).generalizedBernoulli 1 =
    (S : ℚ_[p]) at h
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact ⟨c, mul_left_cancel₀ hp0 (h.trans hc)⟩

/-- The product of the first generalized Bernoulli numbers of all odd
Teichmüller characters, multiplied by p to cancel the exceptional denominator,
is a p-adic integer divisible by p exactly when an ordinary Bernoulli numerator
in the irregularity range is divisible by p. -/
theorem padicTeichmuller_odd_generalizedBernoulli_product_dvd_iff (hp5 : 5 ≤ p) :
    (∃ c : ℤ_[p],
      (p : ℚ_[p]) *
        ∏ i ∈ (range (p - 1)).filter Odd,
          (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1 =
        (p : ℚ_[p]) * c) ↔
    ∃ k : ℕ, 0 < k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  classical
  let I := (range (p - 1)).filter Odd
  let J := I.erase (p - 2)
  let B (i : ℕ) := (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1
  let E : ℤ_[p] :=
    ∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ (p - 2)
  have hpo := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ := hpo
  have heo : Odd (p - 2) := ⟨m - 1, by omega⟩
  have he : p - 2 ∈ I := mem_filter.mpr ⟨mem_range.mpr (by omega), heo⟩
  have hE : (p : ℚ_[p]) * B (p - 2) = (E : ℚ_[p]) :=
    padicTeichmullerCharacter_generalizedBernoulli_one (by omega) heo
  have hEu : PadicInt.toZMod E ≠ 0 := by
    dsimp only [E]
    rw [padicTeichWeightedSum_toZMod, show p - 2 + 1 = p - 1 by omega,
      ite_eq_left (dvd_refl _)]
    exact neg_ne_zero.mpr one_ne_zero
  have hj (i : ℕ) (hi : i ∈ J) : Odd i ∧ i + 1 < p - 1 := by
    obtain ⟨hne, hx⟩ := mem_erase.mp hi
    obtain ⟨hl, ho⟩ := mem_filter.mp hx
    exact ⟨ho, by have := mem_range.mp hl; omega⟩
  have hci (i : ℕ) (hi : i ∈ J) : ∃ a : ℤ_[p], B i = (a : ℚ_[p]) := by
    obtain ⟨ho, hlt⟩ := hj i hi
    exact exists_integral_generalizedBernoulli_of_odd_index (by omega) ho
      (Nat.not_dvd_of_pos_of_lt (by omega) hlt)
  let a (i : ℕ) : ℤ_[p] := if hi : i ∈ J then (hci i hi).choose else 0
  have ha (i : ℕ) (hi : i ∈ J) : B i = (a i : ℚ_[p]) := by
    simp only [a, dite_eq_left hi]
    exact (hci i hi).choose_spec
  have hprod : (p : ℚ_[p]) * ∏ i ∈ I, B i = ((E * ∏ i ∈ J, a i : ℤ_[p]) : ℚ_[p]) := by
    rw [← mul_prod_erase I B he, ← mul_assoc, hE]
    change (E : ℚ_[p]) * (∏ i ∈ J, B i) =
      (algebraMap ℤ_[p] ℚ_[p]) (E * ∏ i ∈ J, a i)
    rw [map_mul, map_prod]
    congr 1
    exact prod_congr rfl ha
  have hnum (i : ℕ) (hi : i ∈ J) :
      PadicInt.toZMod (a i) = 0 ↔ (p : ℤ) ∣ (bernoulli (i + 1)).num := by
    obtain ⟨ho, hlt⟩ := hj i hi
    rw [padicInt_toZMod_eq_zero_iff_exists, ← ha i hi]
    exact padicTeichmullerCharacter_generalizedBernoulli_one_dvd_iff hp5 ho hlt
  change (∃ c : ℤ_[p], (p : ℚ_[p]) * ∏ i ∈ I, B i = (p : ℚ_[p]) * c) ↔ _
  rw [hprod, ← padicInt_toZMod_eq_zero_iff_exists, map_mul, mul_eq_zero]
  simp only [hEu, false_or, map_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, hiJ, hiN⟩
    obtain ⟨hi, hilt⟩ := hj i hiJ
    obtain ⟨k, hk⟩ := hi
    refine ⟨k + 1, by omega, by omega, ?_⟩
    rw [show 2 * (k + 1) = i + 1 by omega]
    exact (hnum i hiJ).mp hiN
  · rintro ⟨k, hk, hklt, hkN⟩
    have hJ : 2 * k - 1 ∈ J := by
      refine mem_erase.mpr ⟨by omega, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩⟩
      exact ⟨k - 1, by omega⟩
    refine ⟨2 * k - 1, hJ, (hnum _ hJ).mpr ?_⟩
    rwa [show 2 * k - 1 + 1 = 2 * k by omega]

end TinyTauDemo
