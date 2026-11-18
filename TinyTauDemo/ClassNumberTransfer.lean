/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.RingTheory.ClassGroup.RelNorm

/-!
# Odd-prime divisibility and relative class-group norms

Extending a class and taking its relative norm raises it to the extension degree.
Cauchy's theorem then relates prime divisors of the class numbers to those of
the kernel of the relative norm, provided the prime is coprime to the extension degree.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4e4554e0be56c8c2d2c6edbca48ac7d6ed9e4f16`.
-/

public section

open NumberField

namespace TinyTauDemo

section FiniteGroups

variable {G H : Type*} [Group G] [Group H]

private theorem mulHom_dvd_card_or_dvd_ker [Finite G] (f : G →* H) {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card G) : p ∣ Nat.card H ∨ p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  have hfx : orderOf (f x) ∣ p := hx ▸ orderOf_map_dvd f x
  rcases (Nat.dvd_prime hp).mp hfx with hone | heq
  · right
    have hxker : x ∈ f.ker := MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp hone)
    rw [← hx]
    exact f.ker.orderOf_dvd_natCard hxker
  · left
    rw [← heq]
    exact orderOf_dvd_natCard (f x)

private theorem dvd_card_of_dvd_card_of_norm_extension [Finite H] (f : G →* H) (j : H →* G)
    (d : ℕ) (hcomp : ∀ x, f (j x) = x ^ d) {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (h : p ∣ Nat.card H) : p ∣ Nat.card G := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  have hj : orderOf (j x) ∣ p := hx ▸ orderOf_map_dvd j x
  have hne : orderOf (j x) ≠ 1 := by
    intro h1
    have hh : x ^ d = 1 := by rw [← hcomp, orderOf_eq_one_iff.mp h1, map_one]
    exact hpd (hx ▸ orderOf_dvd_iff_pow_eq_one.mpr hh)
  have he := ((Nat.dvd_prime hp).mp hj).resolve_left hne
  rw [← he]
  exact orderOf_dvd_natCard (j x)

end FiniteGroups

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

private theorem classNumber_eq_card : classNumber K = Nat.card (ClassGroup (𝓞 K)) :=
  Nat.card_eq_fintype_card.symm

/-- If a prime is coprime to the extension degree, it divides the class number upstairs
if and only if it divides the class number downstairs or the size of the norm kernel. -/
theorem dvd_classNumber_iff_dvd_base_or_dvd_normKernel {p : ℕ} (hp : p.Prime)
    (hpd : ¬ p ∣ Module.finrank K L) :
    p ∣ classNumber L ↔
      p ∣ classNumber K ∨ p ∣ Nat.card (ClassGroup.relNorm (R := 𝓞 K) (S := 𝓞 L)).ker := by
  rw [classNumber_eq_card K, classNumber_eq_card L]
  let f := ClassGroup.relNorm (R := 𝓞 K) (S := 𝓞 L)
  let j := ClassGroup.extendedHom (𝓞 K) (𝓞 L)
  constructor
  · exact mulHom_dvd_card_or_dvd_ker f hp
  · rintro (h | h)
    · have hd : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
        (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm
      have hcomp (a : ClassGroup (𝓞 K)) : f (j a) = a ^ Module.finrank K L := by
        rw [← hd]
        exact ClassGroup.relNorm_extendedHom a
      exact dvd_card_of_dvd_card_of_norm_extension f j _ hcomp hp hpd h
    · exact h.trans f.ker.card_subgroup_dvd_card

/-- For a CM field the odd-prime factors of the class number come from the maximal
real subfield and from the relative ideal class-group norm kernel. -/
theorem dvd_classNumber_iff_dvd_maximalRealSubfield_or_dvd_normKernel (K : Type*)
    [Field K] [NumberField K] [IsCMField K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ classNumber K ↔
      p ∣ classNumber (maximalRealSubfield K) ∨
        p ∣ Nat.card (ClassGroup.relNorm (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker := by
  apply dvd_classNumber_iff_dvd_base_or_dvd_normKernel _ _ hp
  rw [Algebra.IsQuadraticExtension.finrank_eq_two]
  exact fun h ↦ hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left hp.ne_one)

/-- For a prime cyclotomic field, divisibility by its odd conductor is controlled
by the class number of its maximal real subfield and the relative norm kernel. -/
theorem dvd_cyclotomicClassNumber_iff_dvd_maximalRealSubfield_or_dvd_normKernel
    (K : Type*) [Field K] [NumberField K] {p : ℕ} [IsCyclotomicExtension {p} ℚ K]
    (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ classNumber K ↔
      p ∣ classNumber (maximalRealSubfield K) ∨
        p ∣ Nat.card (ClassGroup.relNorm (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker := by
  have hpgt := hp.two_le
  have : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K
    ⟨p, rfl, by omega⟩
  exact dvd_classNumber_iff_dvd_maximalRealSubfield_or_dvd_normKernel K hp hp2

end TinyTauDemo
