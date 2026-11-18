/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.Bernoulli

/-!
# The first Kummer congruence

For positive even indices prime to the modulus prime, the first Kummer
congruence follows from Faulhaber's formula and multiplication of nonzero
residues by a primitive root.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `60aea9909644d4d0d0ae3a81b56460003cbcd3b6`.
-/

public section

open Finset

namespace TinyTauDemo

/-- The binomial expansion truncates after the linear term for a square-zero increment. -/
theorem pow_add_square_zero {R : Type*} [CommRing R] (a b : R) (hb : b * b = 0)
    (n : ℕ) : (a + b) ^ (n + 1) = a ^ (n + 1) + (n + 1 : ℕ) * a ^ n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a + b), ih, pow_succ a, pow_succ a]
    push_cast
    calc
      _ = a ^ n * a * a + ((n : R) + 1 + 1) * (a ^ n * a) * b +
          ((n : R) + 1) * a ^ n * (b * b) := by ring
      _ = _ := by rw [hb, mul_zero, add_zero, pow_succ a n]

private theorem sum_pow_mod_mul (p g n : ℕ) (hp : 0 < p) (hg : g.Coprime p)
    (R : Type*) [CommRing R] :
    (∑ a ∈ range p, (((g * a) % p : ℕ) : R) ^ n) = ∑ a ∈ range p, (a : R) ^ n := by
  apply Finset.sum_bij (fun a _ ↦ (g * a) % p)
  · exact fun a _ ↦ mem_range.mpr (Nat.mod_lt _ hp)
  · intro a ha b hb he
    have hm : g * a ≡ g * b [MOD p] := he
    have hab := Nat.ModEq.cancel_left_of_coprime hg.symm.gcd_eq_one hm
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp ha),
      Nat.mod_eq_of_lt (mem_range.mp hb)] using hab
  · intro b hb
    have hsurj : Function.Surjective (fun a : Fin p ↦
        (⟨(g * (a : ℕ)) % p, Nat.mod_lt _ hp⟩ : Fin p)) := by
      apply Finite.surjective_of_injective
      intro a b hab
      apply Fin.ext
      have hm : g * (a : ℕ) ≡ g * (b : ℕ) [MOD p] := congrArg Fin.val hab
      have hm' := Nat.ModEq.cancel_left_of_coprime hg.symm.gcd_eq_one hm
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hm'
    obtain ⟨a, ha⟩ := hsurj ⟨b, mem_range.mp hb⟩
    exact ⟨a, mem_range.mpr a.isLt, congrArg Fin.val ha⟩
  · intro a ha
    rfl

private theorem power_sum_permutation_congruence {p g n : ℕ}
    (hp : 0 < p) (hg : g.Coprime p) (hn : 0 < n) :
    ((p : ℤ) ^ 2) ∣
      (((g : ℤ) ^ n - 1) * ∑ a ∈ range p, (a : ℤ) ^ n) -
        (n : ℤ) * p * ∑ a ∈ range p, ((g * a / p : ℕ) : ℤ) * ((g * a % p : ℕ) : ℤ) ^ (n - 1) := by
  let R := ZMod (p ^ 2)
  suffices h : ((g : R) ^ n - 1) * (∑ a ∈ range p, (a : R) ^ n) =
      (n : R) * p * ∑ a ∈ range p, ((g * a / p : ℕ) : R) * ((g * a % p : ℕ) : R) ^ (n - 1) by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change _ = (0 : R)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_sum, Int.cast_natCast,
      Int.cast_one]
    exact sub_eq_zero.mpr h
  have hterm (a : ℕ) : ((g : R) * a) ^ n = ((g * a % p : ℕ) : R) ^ n +
      ((n : R) * p) * (((g * a / p : ℕ) : R) * ((g * a % p : ℕ) : R) ^ (n - 1)) := by
    let b : R := ((g * a % p : ℕ) : R)
    let c : R := ((g * a / p : ℕ) : R)
    have hbc : b + (p : R) * c = (g : R) * a := by
      have h := congrArg (Nat.castRingHom R) (Nat.mod_add_div (g * a) p)
      rw [map_add, map_mul, map_mul] at h
      exact h
    have hp2 : (p : R) * (p : R) = 0 := by
      rw [← sq, ← Nat.cast_pow]
      exact ZMod.natCast_self (p ^ 2)
    have hsq : ((p : R) * c) * ((p : R) * c) = 0 := by
      rw [mul_mul_mul_comm, hp2, zero_mul]
    have h := pow_add_square_zero b ((p : R) * c) hsq (n - 1)
    rw [Nat.sub_add_cancel hn, hbc] at h
    change _ = b ^ n + ((n : R) * p) * (c * b ^ (n - 1))
    rw [h]
    ring
  have hsum := Finset.sum_congr (rfl : range p = range p) fun a _ ↦ hterm a
  simp only [mul_pow, ← mul_sum, sum_add_distrib] at hsum
  rw [sum_pow_mod_mul p g n hp hg R] at hsum
  linear_combination hsum

private abbrev pIntegrals (p : ℕ) [Fact p.Prime] : Subring ℚ :=
  (Rat.padicValuation p).integer

section Integrality

variable {p : ℕ} [Fact p.Prime]

private theorem inv_natCast_mem_pIntegrals {a : ℕ} (ha : ¬ p ∣ a) :
    ((a : ℚ)⁻¹) ∈ pIntegrals p := by
  change (Rat.padicValuation p) ((a : ℚ)⁻¹) ≤ 1
  rw [Rat.padicValuation_le_one_iff, Rat.inv_natCast_den_of_pos]
  · exact ha
  · exact Nat.pos_of_ne_zero (fun h ↦ ha (h ▸ dvd_zero _))

private theorem correction_term_mem_pIntegrals {a : ℕ} (ha : a.Prime) :
    (p : ℚ) * ((1 : ℚ) / a) ∈ pIntegrals p := by
  by_cases hab : p ∣ a
  · by_cases hpa : p = a
    · subst a
      rw [mul_one_div_cancel (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
      exact one_mem _
    · exact (hpa ((Nat.dvd_prime ha).mp hab |>.resolve_left (Fact.out : p.Prime).ne_one)).elim
  · rw [one_div]
    exact mul_mem (natCast_mem _ _) (inv_natCast_mem_pIntegrals hab)

/-- Multiplying a Bernoulli number by the prime clears its possible prime denominator. -/
theorem mul_bernoulli_mem_pIntegrals (n : ℕ) :
    (p : ℚ) * bernoulli n ∈ (Rat.padicValuation p).integer := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨a, ha⟩ := Bernoulli.vonStaudt_clausen k
    have hsum :
        (∑ a ∈ range (2 * k + 2) with a.Prime ∧ (a - 1) ∣ 2 * k,
          (p : ℚ) * ((1 : ℚ) / a)) ∈ pIntegrals p := by
      exact Subring.sum_mem _ fun q hq ↦ correction_term_mem_pIntegrals (mem_filter.mp hq).2.1
    have hB : (p : ℚ) * bernoulli (2 * k) =
        (p : ℚ) * a - ∑ a ∈ range (2 * k + 2) with a.Prime ∧ (a - 1) ∣ 2 * k,
          (p : ℚ) * ((1 : ℚ) / a) := by
      rw [← mul_sum, ← mul_sub, ha, add_sub_cancel_right]
    rw [hB]
    exact sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) hsum
  · by_cases hk : k = 0
    · subst k
      change (p : ℚ) * bernoulli 1 ∈ pIntegrals p
      rw [bernoulli_one, neg_div, mul_neg, neg_mem_iff]
      exact correction_term_mem_pIntegrals Nat.prime_two
    · rw [bernoulli_eq_zero_of_odd ⟨k, by omega⟩ (by omega), mul_zero]
      exact zero_mem _

/-- An even Bernoulli number is integral at primes whose predecessor does not divide the index. -/
theorem bernoulli_mem_pIntegrals {k : ℕ} (h : ¬ (p - 1) ∣ 2 * k) :
    bernoulli (2 * k) ∈ (Rat.padicValuation p).integer := by
  obtain ⟨a, ha⟩ := Bernoulli.vonStaudt_clausen k
  have hsum : (∑ a ∈ range (2 * k + 2) with a.Prime ∧ (a - 1) ∣ 2 * k,
      (1 : ℚ) / a) ∈ pIntegrals p := by
    apply Subring.sum_mem
    intro q hq
    obtain ⟨_, hq, hdq⟩ := mem_filter.mp hq
    rw [one_div]
    apply inv_natCast_mem_pIntegrals
    intro hd
    rcases (Nat.dvd_prime hq).mp hd with hp1 | rfl
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact h hdq
  apply_fun (fun x : ℚ ↦ x - ∑ a ∈ range (2 * k + 2) with a.Prime ∧ (a - 1) ∣ 2 * k,
    (1 : ℚ) / a) at ha
  simp only [add_sub_cancel_right] at ha
  rw [← ha]
  exact sub_mem (intCast_mem _ _) hsum

private theorem pow_div_mem_pIntegrals {m e : ℕ} (hm : m ≠ 0)
    (he : m.factorization p ≤ e) : (p : ℚ) ^ e / m ∈ pIntegrals p := by
  let d := m.factorization p
  let a := m / p ^ d
  have ha : ¬ p ∣ a :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (Nat.coprime_ordCompl Fact.out hm)
  have hdecomp : p ^ d * a = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hm_eq : (m : ℚ) = (p : ℚ) ^ d * a := by exact_mod_cast hdecomp.symm
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hrw : (p : ℚ) ^ e / m = (p : ℚ) ^ (e - d) / a := by
    rw [hm_eq, div_mul_eq_div_div]
    congr 1
    rw [div_eq_iff (pow_ne_zero d hp_ne), ← pow_add, Nat.sub_add_cancel he]
  rw [hrw, div_eq_mul_inv]
  exact mul_mem (pow_mem (natCast_mem _ _) _) (inv_natCast_mem_pIntegrals ha)

private theorem factorization_succ_le_sub_two (hp5 : 5 ≤ p) {d : ℕ} (hd : 2 ≤ d) :
    (d + 1).factorization p ≤ d - 2 := by
  by_contra! hb
  have hdvd : p ^ ((d - 2) + 1) ∣ d + 1 :=
    ((Fact.out : p.Prime).pow_dvd_iff_le_factorization (by omega)).2 (by omega)
  have hg (e : ℕ) : e + 3 < p ^ (e + 1) := by
    induction e with
    | zero => simpa using (show 3 < p by omega)
    | succ e ih =>
      rw [pow_succ]
      have htwo : 2 ≤ p := by omega
      have hf : e + 3 + 1 < p ^ (e + 1) * 2 := by omega
      exact hf.trans_le (Nat.mul_le_mul_left _ htwo)
  have h := hg (d - 2)
  rw [show d - 2 + 3 = d + 1 by omega] at h
  exact (not_lt_of_ge (Nat.le_of_dvd (by omega) hdvd)) h

private theorem faulhaber_remainder_mem_pIntegrals (hp5 : 5 ≤ p) {k : ℕ} (hk : 0 < k) :
    ((∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
      (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1)) / (p : ℚ) ^ 2) ∈ pIntegrals p := by
  rw [sum_div]
  apply Subring.sum_mem
  intro i hi
  have hi' := mem_range.mp hi
  have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases hlast : i + 1 = 2 * k
  · have hiodd : Odd i := ⟨k - 1, by omega⟩
    by_cases hi1 : i = 1
    · subst i
      simp only [Nat.choose_one_right, bernoulli_one]
      have hk1 : k = 1 := by omega
      subst k
      norm_num
      rw [show -(3 / 2 * (p : ℚ) ^ 2) / 3 / (p : ℚ) ^ 2 = -(2 : ℚ)⁻¹ by
        field_simp]
      apply neg_mem
      exact inv_natCast_mem_pIntegrals
        (fun hd ↦ (by omega : ¬ p ≤ 2) (Nat.le_of_dvd (by decide) hd))
    · simp [bernoulli_eq_zero_of_odd hiodd (by omega)]
  · let d := 2 * k - i
    have hd : 2 ≤ d := by omega
    have hchoose :
        (((2 * k + 1).choose i : ℚ)) / (2 * k + 1) =
          ((2 * k).choose i : ℚ) / ((d + 1 : ℕ) : ℚ) := by
      have he : 2 * k + 1 - i = d + 1 := by omega
      rw [← he, div_eq_div_iff (by positivity) (by exact_mod_cast (by omega : 2 * k + 1 - i ≠ 0))]
      exact_mod_cast (Nat.choose_mul_succ_eq (2 * k) i).symm
    have he : 2 * k + 1 - i = (d - 2) + 3 := by omega
    rw [show bernoulli i * ((2 * k + 1).choose i : ℚ) *
          (p : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1) / (p : ℚ) ^ 2 =
        bernoulli i * (p : ℚ) ^ (2 * k + 1 - i) / (p : ℚ) ^ 2 *
          (((2 * k + 1).choose i : ℚ) / (2 * k + 1)) by ring,
      hchoose, he, pow_add]
    convert mul_mem (mul_mem (mul_bernoulli_mem_pIntegrals i)
        (natCast_mem (pIntegrals p) ((2 * k).choose i)))
        (pow_div_mem_pIntegrals (by omega : d + 1 ≠ 0)
          (factorization_succ_le_sub_two hp5 hd)) using 1
    field_simp

/-- Dividing a prime-length even power sum by that prime gives the corresponding
Bernoulli number modulo the prime in the ring of integral rationals at that prime. -/
theorem faulhaber_p_divided_remainder_mem_pIntegrals (hp5 : 5 ≤ p) {k : ℕ}
    (hk : 0 < k) :
    (((∑ a ∈ range p, (a : ℚ) ^ (2 * k)) / (p : ℚ) - bernoulli (2 * k)) / (p : ℚ)) ∈
      (Rat.padicValuation p).integer := by
  rw [sum_range_pow, sum_range_succ, Nat.choose_succ_self_right,
    show 2 * k + 1 - 2 * k = 1 by omega]
  push_cast
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hlast : bernoulli (2 * k) * (2 * k + 1 : ℚ) * (p : ℚ) ^ 1 /
      (2 * k + 1 : ℚ) = (p : ℚ) * bernoulli (2 * k) := by
    have hkg : (2 * k + 1 : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hlast]
  convert faulhaber_remainder_mem_pIntegrals hp5 hk using 1
  field_simp
  ring

private theorem int_dvd_iff_div_mem_pIntegrals (a : ℤ) :
    (p : ℤ) ∣ a ↔ (a : ℚ) / (p : ℚ) ∈ pIntegrals p := by
  have hp : p.Prime := Fact.out
  have hd : ((a : ℚ) / (p : ℚ)).den ∣ p := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd a (p : ℤ)
  rw [← Rat.den_div_intCast_eq_one_iff a (p : ℤ) (by exact_mod_cast hp.ne_zero),
    Int.cast_natCast]
  change ((a : ℚ) / (p : ℚ)).den = 1 ↔
    (Rat.padicValuation p) ((a : ℚ) / (p : ℚ)) ≤ 1
  rw [Rat.padicValuation_le_one_iff]
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · simp [h, hp.not_dvd_one]
  · simp [h, hp.ne_one]

/-- For a rational integral at a prime, division by that prime preserves
integrality exactly when its numerator is divisible by the prime. -/
theorem num_dvd_iff_div_mem_pIntegrals {x : ℚ} (hx : x ∈ (Rat.padicValuation p).integer) :
    (p : ℤ) ∣ x.num ↔ x / (p : ℚ) ∈ (Rat.padicValuation p).integer := by
  have hd : ¬ p ∣ x.den := Rat.padicValuation_le_one_iff.mp hx
  have hnum : (x.num : ℚ) = (x.den : ℚ) * x := by
    have hne : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
    calc
      (x.num : ℚ) = (x.den : ℚ) * ((x.num : ℚ) / x.den) := by field_simp
      _ = _ := by rw [Rat.num_div_den]
  rw [int_dvd_iff_div_mem_pIntegrals, hnum, mul_div_assoc]
  constructor
  · intro h
    have hd' : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
    have h' := mul_mem (inv_natCast_mem_pIntegrals hd) h
    simpa only [← mul_assoc, inv_mul_cancel₀ hd', one_mul] using h'
  · exact mul_mem (natCast_mem _ _)

private theorem pIntegrals_div_natCast_iff {x : ℚ} {m : ℕ} (hm : ¬ p ∣ m) :
    x / (m : ℚ) ∈ pIntegrals p ↔ x ∈ pIntegrals p := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (fun h ↦ hm (h ▸ dvd_zero _))
  constructor
  · intro h
    have h' := mul_mem h (natCast_mem (pIntegrals p) m)
    simpa only [div_mul_cancel₀ _ hm'] using h'
  · intro h
    rw [div_eq_mul_inv]
    exact mul_mem h (inv_natCast_mem_pIntegrals hm)

private def powerSum (R : Type*) [Semiring R] (p n : ℕ) : R :=
  ∑ a ∈ range p, (a : R) ^ n

private def weightedPowerSum (R : Type*) [Semiring R] (p g n : ℕ) : R :=
  ∑ a ∈ range p, ((g * a / p : ℕ) : R) * ((g * a % p : ℕ) : R) ^ (n - 1)

private theorem bernoulli_div_congr_powers (hp5 : 5 ≤ p) {k g : ℕ}
    (hk : 0 < k) (hg : g.Coprime p) (hkp : ¬ p ∣ 2 * k) :
    ((((g : ℚ) ^ (2 * k) - 1) * (bernoulli (2 * k) / (2 * k : ℚ)) -
      weightedPowerSum ℚ p g (2 * k)) / (p : ℚ)) ∈ pIntegrals p := by
  have hp := (Fact.out : p.Prime)
  have hk' : 0 < 2 * k := by omega
  obtain ⟨a, ha⟩ := power_sum_permutation_congruence hp.pos hg hk'
  change ((g : ℤ) ^ (2 * k) - 1) * powerSum ℤ p (2 * k) -
    ((2 * k : ℕ) : ℤ) * p * weightedPowerSum ℤ p g (2 * k) = (p : ℤ) ^ 2 * a at ha
  have haQ := congrArg (Int.castRingHom ℚ) ha
  simp only [powerSum, weightedPowerSum, map_sub, map_mul, map_pow, map_one, map_sum,
    Int.coe_castRingHom, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] at haQ
  have he :
      (((g : ℚ) ^ (2 * k) - 1) * ((powerSum ℚ p (2 * k) / (p : ℚ)) / (2 * k : ℚ)) -
        weightedPowerSum ℚ p g (2 * k)) / (p : ℚ) = (a : ℚ) / (2 * k : ℚ) := by
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hk0 : (2 * k : ℚ) ≠ 0 := by positivity
    unfold powerSum weightedPowerSum
    field_simp
    linear_combination haQ
  have hl : ((a : ℚ) / (2 * k : ℚ)) ∈ pIntegrals p := by
    have h := (pIntegrals_div_natCast_iff hkp).mpr (intCast_mem (pIntegrals p) a)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hA : (((g : ℚ) ^ (2 * k) - 1) / (2 * k : ℚ)) ∈ pIntegrals p := by
    have h := (pIntegrals_div_natCast_iff hkp).mpr (sub_mem
      (pow_mem (natCast_mem (pIntegrals p) g) (2 * k)) (one_mem _))
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  have hrem := mul_mem hA (faulhaber_p_divided_remainder_mem_pIntegrals hp5 hk)
  have hf :
      ((((g : ℚ) ^ (2 * k) - 1) * ((powerSum ℚ p (2 * k) / (p : ℚ)) / (2 * k : ℚ)) -
        weightedPowerSum ℚ p g (2 * k)) / (p : ℚ)) ∈ pIntegrals p := he ▸ hl
  change (((g : ℚ) ^ (2 * k) - 1) / (2 * k : ℚ)) *
    (((powerSum ℚ p (2 * k) / (p : ℚ)) - bernoulli (2 * k)) / (p : ℚ)) ∈ pIntegrals p at hrem
  convert sub_mem hf hrem using 1
  ring

private theorem weightedPowerSum_sub_div_mem_pIntegrals {g n m : ℕ}
    (hm : 1 < m) (hmn : m ≤ n) (hd : (p - 1) ∣ n - m) :
    (weightedPowerSum ℚ p g n - weightedPowerSum ℚ p g m) / (p : ℚ) ∈ pIntegrals p := by
  have hp : p.Prime := Fact.out
  have hd' : (p - 1) ∣ (n - 1) - (m - 1) := by
    rwa [show n - 1 - (m - 1) = n - m by omega]
  have hdvd : (p : ℤ) ∣ weightedPowerSum ℤ p g n - weightedPowerSum ℤ p g m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [weightedPowerSum, Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast]
    apply sub_eq_zero.mpr
    apply sum_congr rfl
    intro i _
    congr 1
    have h := (ZMod.intCast_eq_intCast_iff _ _ p).mpr
      (Int.ModEq.pow_eq_pow hp hd' (by omega) (by omega) ((g * i % p : ℕ) : ℤ))
    simpa only [Int.cast_pow, Int.cast_natCast] using h
  have h := (int_dvd_iff_div_mem_pIntegrals _).mp hdvd
  simpa only [weightedPowerSum, Int.cast_sub, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast] using h

private theorem inverse_intCast_mem_pIntegrals {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) :
    ((z : ℚ)⁻¹) ∈ pIntegrals p := by
  change (Rat.padicValuation p) ((z : ℚ)⁻¹) ≤ 1
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ dvd_zero _)
  rw [Rat.padicValuation_le_one_iff, Rat.inv_intCast_den, ite_eq_right hz0]
  simpa only [← Int.natCast_dvd_natCast, Int.dvd_natAbs] using hz

/-- Kummer's first congruence modulo the prime, for positive even indices
coprime to the prime and nonzero modulo one less than the prime. -/
theorem bernoulli_div_sub_div_prime_mem_pIntegrals {k m : ℕ}
    (hp5 : 5 ≤ p) (hm : 0 < m) (hmk : m ≤ k)
    (hd : (p - 1) ∣ (2 * k - 2 * m)) (hdm : ¬ (p - 1) ∣ 2 * m)
    (hkp : ¬ p ∣ 2 * k) (hmp : ¬ p ∣ 2 * m) :
    ((bernoulli (2 * k) / (2 * k : ℚ) - bernoulli (2 * m) / (2 * m : ℚ)) / (p : ℚ)) ∈
      (Rat.padicValuation p).integer := by
  have hp : p.Prime := Fact.out
  have hk := hm.trans_le hmk
  have hdk : ¬ (p - 1) ∣ 2 * k := by
    intro h
    have h' := Nat.dvd_sub h hd
    rw [show 2 * k - (2 * k - 2 * m) = 2 * m by omega] at h'
    exact hdm h'
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hu' : orderOf u = p - 1 := hu.trans (Nat.card_eq_fintype_card.trans (ZMod.card_units p))
  let g := (u : ZMod p).val
  have hg : (g : ZMod p) = (u : ZMod p) := ZMod.natCast_zmod_val _
  have hcop : g.Coprime p := by
    apply ((hp.coprime_iff_not_dvd).mpr ?_).symm
    rw [← ZMod.natCast_eq_zero_iff, hg]
    exact Units.ne_zero _
  have hcoef : ¬ (p : ℤ) ∣ (g : ℤ) ^ (2 * k) - 1 := by
    intro h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    push_cast at h
    rw [hg] at h
    have he : u ^ (2 * k) = 1 := Units.ext (sub_eq_zero.mp h)
    exact hdk (hu' ▸ orderOf_dvd_iff_pow_eq_one.mpr he)
  have hK := bernoulli_div_congr_powers hp5 hk hcop hkp
  have hM := bernoulli_div_congr_powers hp5 hm hcop hmp
  have hT := weightedPowerSum_sub_div_mem_pIntegrals (g := g)
    (by omega : 1 < 2 * m) (by omega : 2 * m ≤ 2 * k) hd
  have hD : (((g : ℚ) ^ (2 * k) - (g : ℚ) ^ (2 * m)) / (p : ℚ)) ∈ pIntegrals p := by
    have h := (Int.ModEq.pow_eq_pow hp hd (by omega) (by omega) (g : ℤ)).symm.dvd
    have hi := (int_dvd_iff_div_mem_pIntegrals _).mp h
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast] using hi
  have hBm : bernoulli (2 * m) / (2 * m : ℚ) ∈ pIntegrals p := by
    have hh := (pIntegrals_div_natCast_iff hmp).mpr (bernoulli_mem_pIntegrals hdm)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hS := sub_mem (add_mem (sub_mem hK hM) hT) (mul_mem hD hBm)
  have hres : (((g : ℚ) ^ (2 * k) - 1) *
      (bernoulli (2 * k) / (2 * k : ℚ) - bernoulli (2 * m) / (2 * m : ℚ)) / (p : ℚ)) ∈
      pIntegrals p := by
    convert hS using 1
    ring
  have hi := inverse_intCast_mem_pIntegrals hcoef
  push_cast at hi
  have hcoef' : (g : ℚ) ^ (2 * k) - 1 ≠ 0 := by
    intro h
    apply hcoef
    have h0 : (g : ℤ) ^ (2 * k) - 1 = 0 := by exact_mod_cast h
    rw [h0]
    exact dvd_zero _
  have hmul := mul_mem hi hres
  simpa only [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hcoef', one_mul] using hmul

/-- Divisibility of Bernoulli numerators transfers along Kummer's first
congruence when both indices are coprime to the modulus prime. -/
theorem dvd_bernoulli_num_iff_of_congruent_even_indices {k m : ℕ}
    (hp5 : 5 ≤ p) (hm : 0 < m) (hmk : m ≤ k)
    (hd : (p - 1) ∣ (2 * k - 2 * m)) (hdm : ¬ (p - 1) ∣ 2 * m)
    (hkp : ¬ p ∣ 2 * k) (hmp : ¬ p ∣ 2 * m) :
    (p : ℤ) ∣ (bernoulli (2 * k)).num ↔ (p : ℤ) ∣ (bernoulli (2 * m)).num := by
  have hdk : ¬ (p - 1) ∣ 2 * k := by
    intro h
    have h' := Nat.dvd_sub h hd
    rw [show 2 * k - (2 * k - 2 * m) = 2 * m by omega] at h'
    exact hdm h'
  have h := bernoulli_div_sub_div_prime_mem_pIntegrals hp5 hm hmk hd hdm hkp hmp
  rw [num_dvd_iff_div_mem_pIntegrals (bernoulli_mem_pIntegrals hdk),
    num_dvd_iff_div_mem_pIntegrals (bernoulli_mem_pIntegrals hdm)]
  have hK := pIntegrals_div_natCast_iff (x := bernoulli (2 * k) / (p : ℚ)) hkp
  have hM := pIntegrals_div_natCast_iff (x := bernoulli (2 * m) / (p : ℚ)) hmp
  rw [← hK, ← hM]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · intro hA
    convert sub_mem hA h using 1
    ring
  · intro hB
    convert add_mem hB h using 1
    ring

end Integrality

end TinyTauDemo
