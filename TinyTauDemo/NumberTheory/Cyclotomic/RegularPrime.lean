/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Regular primes

Regularity is the condition that the cyclotomic class group has no nontrivial prime torsion.
The definition uses the ring of integers of the cyclotomic field through its class number.
Equivalently, a fractional ideal is principal whenever its pth power is principal.
See `/roadmap/index.qmd#def-regular-prime` @ `bf7f5564b71833b39d09f2fe3230b9c22ec609e0`.
-/

public section

open NumberField
open scoped nonZeroDivisors

namespace TinyTauDemo

/-- An odd prime is regular if it does not divide the class number of its cyclotomic field. -/
structure RegularPrime (p : ℕ) : Prop where
  prime : p.Prime
  odd : Odd p
  not_dvd_classNumber : ¬ p ∣ classNumber (CyclotomicField p ℚ)

/-- Regularity is equivalent to the absence of nontrivial prime torsion in the class group. -/
theorem regularPrime_iff_no_classGroup_torsion {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    RegularPrime p ↔ ∀ c : ClassGroup (𝓞 (CyclotomicField p ℚ)), c ^ p = 1 → c = 1 := by
  constructor
  · intro hr c hc
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hc) with h | h
    · exact orderOf_eq_one_iff.mp h
    · have hd : orderOf c ∣ classNumber (CyclotomicField p ℚ) := orderOf_dvd_card
      exact (hr.not_dvd_classNumber (by simpa only [h] using hd)).elim
  · intro h
    refine ⟨hp, ho, fun hd ↦ ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ :=
      exists_prime_orderOf_dvd_card (G := ClassGroup (𝓞 (CyclotomicField p ℚ))) p hd
    have hcpow : c ^ p = 1 := by simpa only [hc] using pow_orderOf_eq_one c
    exact hp.ne_one (hc.symm.trans (orderOf_eq_one_iff.mpr (h c hcpow)))

/-- A regular prime is coprime to the class number of its cyclotomic field. -/
theorem RegularPrime.coprime_classNumber {p : ℕ} (hr : RegularPrime p) :
    p.Coprime (classNumber (CyclotomicField p ℚ)) :=
  hr.prime.coprime_iff_not_dvd.mpr hr.not_dvd_classNumber

/-- Over the cyclotomic field of a regular prime, a fractional ideal is principal if its
prime power is principal. -/
theorem RegularPrime.fractionalIdeal_isPrincipal_of_pow {p : ℕ} (hr : RegularPrime p)
    (I : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ))
    (hI : (↑(I ^ p) : Submodule (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)).IsPrincipal) :
    (I : Submodule (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)).IsPrincipal :=
  FractionalIdeal.isPrincipal.of_isPrincipal_pow_of_coprime hr.coprime_classNumber I hI

/-- At an odd prime, the fractional ideal principal-power criterion is equivalent to regularity. -/
theorem regularPrime_iff_fractionalIdeal_isPrincipal_of_pow {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    let K := CyclotomicField p ℚ
    let R := 𝓞 K
    RegularPrime p ↔ ∀ I : FractionalIdeal R⁰ K,
      ((I ^ p : FractionalIdeal R⁰ K) : Submodule R K).IsPrincipal →
        (I : Submodule R K).IsPrincipal := by
  dsimp only
  constructor
  · exact fun h ↦ h.fractionalIdeal_isPrincipal_of_pow
  · intro h
    refine (regularPrime_iff_no_classGroup_torsion hp ho).mpr fun c hc ↦ ?_
    let K := CyclotomicField p ℚ
    let R := 𝓞 K
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c
    let I : (FractionalIdeal R⁰ K)ˣ := FractionalIdeal.mk0 K J
    have hcI : ClassGroup.mk K I = c := (ClassGroup.mk_mk0 K J).trans hJ
    rw [← hcI, ← map_pow, ClassGroup.mk_eq_one_iff] at hc
    rw [← hcI, ClassGroup.mk_eq_one_iff]
    apply h (I : FractionalIdeal R⁰ K)
    exact_mod_cast hc

end TinyTauDemo
