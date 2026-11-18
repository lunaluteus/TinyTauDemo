/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Bernoulli.KummerBernoulliCongruence
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
public import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.Teichmuller

/-!
# Teichmüller Bernoulli factors modulo a prime

Reduction modulo the squared prime identifies the first generalized Bernoulli
numbers of odd Teichmüller characters with ordinary integer power sums.
Kummer's first congruence then detects their divisibility by the prime from
the Bernoulli numerators of the corresponding small even indices. The exceptional
character contributes a first Bernoulli number of valuation minus one.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4e4554e0be56c8c2d2c6edbca48ac7d6ed9e4f16`.
-/

public section

open Finset IsLocalRing ValuativeRel TauCeti

namespace TinyTauDemo

section PowerSums

variable {p : ℕ} [Fact p.Prime]

private theorem int_prime_sq_dvd_iff_div_mem (a : ℤ) :
    ((p : ℤ) ^ 2) ∣ a ↔ (a : ℚ) / (p : ℚ) ^ 2 ∈ (Rat.padicValuation p).integer := by
  have hp : p.Prime := Fact.out
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd : ((a : ℚ) / (p : ℚ) ^ 2).den ∣ p ^ 2 := by
    apply Int.natCast_dvd_natCast.mp
    have h := Rat.den_dvd a ((p : ℤ) ^ 2)
    rw [Rat.divInt_eq_div, Int.cast_pow, Int.cast_natCast] at h
    simpa only [Nat.cast_pow] using h
  rw [← Rat.den_div_intCast_eq_one_iff a ((p : ℤ) ^ 2) (pow_ne_zero _ hpz)]
  push_cast
  change ((a : ℚ) / (p : ℚ) ^ 2).den = 1 ↔
    (Rat.padicValuation p) ((a : ℚ) / (p : ℚ) ^ 2) ≤ 1
  rw [Rat.padicValuation_le_one_iff]
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  rw [he]
  cases e with
  | zero => simp [hp.not_dvd_one]
  | succ e =>
    have h : p ∣ p ^ (e + 1) := dvd_pow_self _ (by omega)
    simp [h, hp.ne_one]

/-- For a positive even index outside the von Staudt–Clausen denominator condition,
divisibility of the power sum by the square of the prime detects divisibility
of the Bernoulli numerator by the prime. -/
theorem prime_sq_dvd_power_sum_iff_dvd_bernoulli_num
    (hp5 : 5 ≤ p) {k : ℕ} (hk : 0 < k) (hkd : ¬ (p - 1) ∣ 2 * k) :
    ((p : ℤ) ^ 2) ∣ ∑ a ∈ range p, (a : ℤ) ^ (2 * k) ↔
      (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  rw [int_prime_sq_dvd_iff_div_mem, num_dvd_iff_div_mem_pIntegrals (bernoulli_mem_pIntegrals hkd)]
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  have hd := faulhaber_p_divided_remainder_mem_pIntegrals hp5 hk
  have hd' :
      ((∑ a ∈ range p, (a : ℚ) ^ (2 * k)) / (p : ℚ) ^ 2 -
        bernoulli (2 * k) / (p : ℚ)) ∈ (Rat.padicValuation p).integer := by
    convert hd using 1
    ring
  constructor
  · intro h
    convert sub_mem h hd' using 1
    ring
  · intro h
    convert add_mem h hd' using 1
    ring

/-- The squared-prime power sums at the Teichmüller exponents detect
the Bernoulli numerators that enter the relative class-number criterion. -/
theorem prime_sq_dvd_teichmuller_power_sum_iff_bernoulli_num (hp5 : 5 ≤ p)
    {i : ℕ} (hi : Odd i) (hi_lt : i + 1 < p - 1) :
    ((p : ℤ) ^ 2) ∣ ∑ a ∈ range p, (a : ℤ) ^ (p * i + 1) ↔
      (p : ℤ) ∣ (bernoulli (i + 1)).num := by
  have hp : p.Prime := Fact.out
  have hpo := hp.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := (hpo.mul hi).add_odd odd_one
  obtain ⟨m, hm⟩ := hi.add_odd odd_one
  have hk' : p * i + 1 = 2 * k := by omega
  have hm' : i + 1 = 2 * m := by omega
  have hm0 : 0 < m := by omega
  have hmk : m ≤ k := by nlinarith
  have hmod : (p - 1) ∣ (2 * k - 2 * m) := by
    use i
    rw [← hk', ← hm', Nat.sub_mul]
    omega
  have hmd : ¬ (p - 1) ∣ 2 * m := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hkd : ¬ (p - 1) ∣ 2 * k := by
    intro h
    have h' := Nat.dvd_sub h hmod
    rw [show 2 * k - (2 * k - 2 * m) = 2 * m by omega] at h'
    exact hmd h'
  have hmp : ¬ p ∣ 2 * m := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hkp : ¬ p ∣ 2 * k := by
    rw [← hk']
    intro hd
    have h : p ∣ p * i := dvd_mul_right _ _
    have h1 := Nat.dvd_sub hd h
    rw [Nat.add_sub_cancel_left] at h1
    exact hp.not_dvd_one h1
  rw [hk', hm', prime_sq_dvd_power_sum_iff_dvd_bernoulli_num hp5 (by omega) hkd,
    dvd_bernoulli_num_iff_of_congruent_even_indices hp5 hm0 hmk hmod hmd hkp hmp]

end PowerSums

section Reduction

variable (p : ℕ) [Fact p.Prime]

/-- The Teichmüller lift of a natural number to the p-adic integers. -/
noncomputable def padicTeichNat (a : ℕ) : ℤ_[p] :=
  Padic.integerRingEquiv p (teichmullerLift ℚ_[p] (a : 𝓀[ℚ_[p]]))

private theorem padicTeichNat_sub_mem_maximalIdeal (a : ℕ) :
    padicTeichNat p a - (a : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
  let x := teichmullerLift ℚ_[p] (a : 𝓀[ℚ_[p]])
  let e := Padic.integerRingEquiv p
  change e x - (a : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p]
  have hm : x - (a : 𝒪[ℚ_[p]]) ∈ IsLocalRing.maximalIdeal _ := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    dsimp only [x]
    rw [map_sub, residue_teichmullerLift, map_natCast, sub_self]
  have h := Ideal.mem_map_of_mem e.toRingHom hm
  change e (x - (a : 𝒪[ℚ_[p]])) ∈ (IsLocalRing.maximalIdeal _).map e.toRingHom at h
  rw [map_sub, map_natCast] at h
  change e x - (a : ℤ_[p]) ∈ Ideal.map e (IsLocalRing.maximalIdeal 𝒪[ℚ_[p]]) at h
  rwa [IsLocalRing.map_ringEquiv_maximalIdeal e] at h

private theorem padicTeichNat_toZMod (a : ℕ) :
    PadicInt.toZMod (padicTeichNat p a) = (a : ZMod p) := by
  have h := padicTeichNat_sub_mem_maximalIdeal p a
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h
  exact h

/-- Modulo the square of the residue characteristic, the Teichmüller lift
of a natural number is given by its pth power. -/
theorem padicTeichNat_toZModPow_two (a : ℕ) :
    PadicInt.toZModPow 2 (padicTeichNat p a) = (a : ZMod (p ^ 2)) ^ p := by
  let x := teichmullerLift ℚ_[p] (a : 𝓀[ℚ_[p]])
  let Φ := PadicInt.toZModPow (p := p) 2
  let e := Padic.integerRingEquiv p
  have hx : x ^ p = x := by
    simpa only [Padic.natCard_residueField p] using
      teichmullerLift_pow_natCard ℚ_[p] (a : 𝓀[ℚ_[p]])
  have hme : e x - (a : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    padicTeichNat_sub_mem_maximalIdeal p a
  change Φ (e x) = _
  rw [← hx, map_pow, map_pow]
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hme
  obtain ⟨y, hy⟩ := hme
  have hxy : e x = (a : ℤ_[p]) + (p : ℤ_[p]) * y := by linear_combination hy
  rw [hxy, map_add, map_mul, map_natCast, map_natCast]
  have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
    rw [← sq, ← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hsq : ((p : ZMod (p ^ 2)) * Φ y) * ((p : ZMod (p ^ 2)) * Φ y) = 0 := by
    rw [mul_mul_mul_comm, hp2, zero_mul]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have H := pow_add_square_zero (a : ZMod (p ^ 2)) ((p : ZMod (p ^ 2)) * Φ y) hsq (p - 1)
  rw [Nat.sub_add_cancel hp0] at H
  have hz : (p : ZMod (p ^ 2)) * (a : ZMod (p ^ 2)) ^ (p - 1) *
      ((p : ZMod (p ^ 2)) * Φ y) = 0 := by
    rw [mul_mul_mul_comm, hp2, zero_mul]
  rwa [hz, add_zero] at H

/-- Reduction modulo the squared prime of the weighted Teichmüller sum
is the ordinary power sum at the corresponding exponent. -/
theorem padicTeichWeightedSum_toZModPow_two (i : ℕ) :
    PadicInt.toZModPow 2 (∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i) =
      ∑ a ∈ range p, (a : ZMod (p ^ 2)) ^ (p * i + 1) := by
  rw [map_sum]
  apply sum_congr rfl
  intro a _
  rw [map_mul, map_natCast, map_pow, padicTeichNat_toZModPow_two, ← pow_mul]
  exact (pow_succ' _ _).symm

end Reduction

variable {p : ℕ} [Fact p.Prime]

private noncomputable def residueFieldEquivZMod : 𝓀[ℚ_[p]] ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (Padic.integerRingEquiv p)).trans PadicInt.residueField

/-- The Teichmüller character modulo p with values in the p-adic field. -/
noncomputable def padicTeichmullerCharacter : DirichletCharacter ℚ_[p] p where
  toFun a := (teichmullerLift ℚ_[p] (residueFieldEquivZMod.symm a) : ℚ_[p])
  map_one' := by simp
  map_mul' a b := by simp
  map_nonunit' a ha := by
    obtain rfl : a = 0 := not_ne_iff.mp (mt isUnit_iff_ne_zero.mpr ha)
    simp

private theorem padicTeichmullerCharacter_apply (a : ZMod p) :
    padicTeichmullerCharacter a =
      (teichmullerLift ℚ_[p] (residueFieldEquivZMod.symm a) : ℚ_[p]) := rfl

private theorem padicTeichmullerCharacter_natCast (a : ℕ) :
    padicTeichmullerCharacter (a : ZMod p) = (padicTeichNat p a : ℚ_[p]) := by
  rw [padicTeichmullerCharacter_apply, map_natCast]
  exact (Padic.coe_integerRingEquiv_apply p _).symm

private theorem padicTeichmullerCharacter_neg_one (hp2 : 2 < p) :
    padicTeichmullerCharacter (-1 : ZMod p) = -1 := by
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [padicTeichmullerCharacter_apply, map_neg, map_one, teichmullerLift_neg_one]
  · rfl
  · simpa only [Padic.natCard_residueField p] using hp

/-- The Teichmüller character modulo an odd prime is odd. -/
theorem padicTeichmullerCharacter_odd (hp2 : 2 < p) : (padicTeichmullerCharacter (p := p)).Odd :=
  padicTeichmullerCharacter_neg_one hp2

private theorem padicTeichmullerCharacter_pow_ne_one (hp2 : 2 < p) {i : ℕ} (hi : Odd i) :
    (padicTeichmullerCharacter (p := p)) ^ i ≠ 1 := by
  intro h
  have hi0 : i ≠ 0 := by obtain ⟨k, hk⟩ := hi; omega
  have he := DFunLike.congr_fun h (-1 : ZMod p)
  rw [MulChar.pow_apply' _ hi0, padicTeichmullerCharacter_neg_one hp2,
    hi.neg_one_pow, MulChar.one_apply (isUnit_one.neg)] at he
  exact neg_ne_self.mpr one_ne_zero he

private theorem sum_zmod_eq_sum_range {R : Type*} [AddCommMonoid R] (f : ZMod p → R) :
    (∑ a : ZMod p, f a) = ∑ a ∈ range p, f (a : ZMod p) := by
  symm
  refine Finset.sum_bij' (fun a _ ↦ (a : ZMod p)) (fun a _ ↦ a.val)
    (fun _ _ ↦ mem_univ _) (fun a _ ↦ mem_range.mpr (ZMod.val_lt a))
    (fun a ha ↦ ZMod.val_natCast_of_lt (mem_range.mp ha)) (fun a _ ↦ ZMod.natCast_zmod_val a)
    (fun _ _ ↦ rfl)

/-- The weighted Teichmüller sum is p times the first generalized Bernoulli
number of the corresponding odd Teichmüller character. -/
theorem padicTeichmullerCharacter_generalizedBernoulli_one (hp2 : 2 < p) {i : ℕ} (hi : Odd i) :
    (p : ℚ_[p]) * (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1 =
      ((∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i : ℤ_[p]) : ℚ_[p]) := by
  rw [DirichletCharacter.natCast_mul_generalizedBernoulli_one_of_ne_one
    (padicTeichmullerCharacter_pow_ne_one hp2 hi), sum_zmod_eq_sum_range]
  change _ = (algebraMap ℤ_[p] ℚ_[p])
    (∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i)
  rw [map_sum]
  apply sum_congr rfl
  intro a ha
  have hi0 : i ≠ 0 := by obtain ⟨k, hk⟩ := hi; omega
  rw [MulChar.pow_apply' _ hi0, ZMod.val_natCast_of_lt (mem_range.mp ha),
    padicTeichmullerCharacter_natCast, map_mul, map_pow, map_natCast, mul_comm]
  rfl

/-- For the relevant odd exponents, the weighted Teichmüller sum is divisible
by the squared prime exactly when the associated ordinary numerator vanishes modulo the prime. -/
theorem padicTeichWeightedSum_dvd_sq_iff (hp5 : 5 ≤ p) {i : ℕ}
    (hi : Odd i) (hi_lt : i + 1 < p - 1) :
    ((p : ℤ_[p]) ^ 2) ∣ ∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i ↔
      (p : ℤ) ∣ (bernoulli (i + 1)).num := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    padicTeichWeightedSum_toZModPow_two, ← prime_sq_dvd_teichmuller_power_sum_iff_bernoulli_num
      hp5 hi hi_lt, ← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast]

/-- Divisibility in the p-adic integers of the first generalized Bernoulli number
of an odd Teichmüller character is detected by the ordinary Bernoulli numerator. -/
theorem padicTeichmullerCharacter_generalizedBernoulli_one_dvd_iff (hp5 : 5 ≤ p)
    {i : ℕ} (hi : Odd i) (hi_lt : i + 1 < p - 1) :
    (∃ c : ℤ_[p],
      (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1 = (p : ℚ_[p]) * c) ↔
      (p : ℤ) ∣ (bernoulli (i + 1)).num := by
  let B := (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1
  let S : ℤ_[p] := ∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i
  have hS : (p : ℚ_[p]) * B = (S : ℚ_[p]) :=
    padicTeichmullerCharacter_generalizedBernoulli_one (by omega) hi
  rw [← padicTeichWeightedSum_dvd_sq_iff hp5 hi hi_lt]
  change (∃ c : ℤ_[p], B = (p : ℚ_[p]) * c) ↔ (p : ℤ_[p]) ^ 2 ∣ S
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, PadicInt.ext ?_⟩
    rw [← hS, hc, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, pow_two, mul_assoc]
  · rintro ⟨c, hc⟩
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine ⟨c, mul_left_cancel₀ hp0 ?_⟩
    rw [hS, hc, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, pow_two, mul_assoc]

private theorem zmod_sum_power {n : ℕ} (hn : n ≠ 0) :
    (∑ a : ZMod p, a ^ n) = if (p - 1) ∣ n then -1 else 0 := by
  classical
  let e : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, _root_.Units.val_injective⟩
  have he : univ.map e = univ \ {0} := by
    ext a
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, e] using! (isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0)
  calc
    (∑ a : ZMod p, a ^ n) = ∑ a ∈ univ \ {(0 : ZMod p)}, a ^ n := by
      rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow hn, add_zero]
    _ = ∑ a : (ZMod p)ˣ, (a ^ n : ZMod p) := by simp [e, ← he, univ.sum_map e]
    _ = _ := by rw [FiniteField.sum_pow_units, ZMod.card]

/-- Reduction of the weighted Teichmüller sum modulo p distinguishes the exceptional
exponent from the ordinary Bernoulli factors. -/
theorem padicTeichWeightedSum_toZMod (i : ℕ) :
    PadicInt.toZMod (∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ i) =
      if (p - 1) ∣ i + 1 then -1 else 0 := by
  rw [map_sum, ← zmod_sum_power (p := p) (show i + 1 ≠ 0 by omega), sum_zmod_eq_sum_range]
  apply sum_congr rfl
  intro a _
  rw [map_mul, map_natCast, map_pow, padicTeichNat_toZMod, pow_succ']

/-- The Teichmüller character modulo p has exact order p − 1. -/
theorem orderOf_padicTeichmullerCharacter :
    orderOf (padicTeichmullerCharacter (p := p)) = p - 1 := by
  let χ := padicTeichmullerCharacter (p := p)
  have hχ : χ ^ (p - 1) = 1 := by
    rw [← ZMod.card_units p]
    exact χ.pow_card_eq_one
  apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hχ)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  rw [← ZMod.card_units p, ← Nat.card_eq_fintype_card,
    ← orderOf_eq_card_of_forall_mem_zpowers hg]
  apply orderOf_dvd_of_pow_eq_one
  have h := DFunLike.congr_fun (pow_orderOf_eq_one χ) (g : ZMod p)
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h
  rw [← ZMod.natCast_zmod_val (g : ZMod p)] at h
  rw [padicTeichmullerCharacter_natCast, ← PadicInt.coe_pow, ← PadicInt.coe_one,
    PadicInt.coe_inj] at h
  apply Units.ext
  have hz := congrArg (PadicInt.toZMod (p := p)) h
  rw [map_pow, map_one, padicTeichNat_toZMod] at hz
  simpa only [ZMod.natCast_zmod_val, Units.val_pow_eq_pow_val, Units.val_one] using hz

/-- The exceptional Teichmüller character has a nonintegral first generalized Bernoulli
number. Multiplying it by the residue prime gives an integer with nonzero reduction. -/
theorem padicTeichmullerCharacter_exceptional_generalizedBernoulli_one_not_integral (hp2 : 2 < p) :
    ¬ ∃ c : ℤ_[p],
      (padicTeichmullerCharacter (p := p) ^ (p - 2)).generalizedBernoulli 1 = (c : ℚ_[p]) := by
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hi : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := ho
    exact ⟨k - 1, by omega⟩
  rintro ⟨c, hc⟩
  have h := padicTeichmullerCharacter_generalizedBernoulli_one hp2 hi
  rw [hc] at h
  let S : ℤ_[p] := ∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ (p - 2)
  have hs : (p : ℤ_[p]) * c = S := by
    apply PadicInt.ext
    rw [PadicInt.coe_mul, PadicInt.coe_natCast]
    exact h
  have hres := congrArg (PadicInt.toZMod (p := p)) hs
  change PadicInt.toZMod ((p : ℤ_[p]) * c) =
    PadicInt.toZMod (∑ a ∈ range p, (a : ℤ_[p]) * (padicTeichNat p a) ^ (p - 2)) at hres
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul, padicTeichWeightedSum_toZMod,
    show p - 2 + 1 = p - 1 by omega, ite_eq_left (dvd_refl _)] at hres
  simp at hres

end TinyTauDemo
