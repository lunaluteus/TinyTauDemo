/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Congruences in the cyclotomic integers

A lift of the cyclotomic residue class yields a rational integer representative for a
prime power. Divisibility by the rational prime can also be read from the power basis.
See `/roadmap/index.qmd#lem-pth-power-congruence @ 6c0f6698381309f3cd30d37ec6e768d5c73ef541`.
-/

public section

namespace TinyTauDemo

/-- A residue modulo `π` determines a `p`-th power modulo `π ^ p` when
`π ^ (p - 1)` divides the prime `p`. -/
private theorem pow_sub_pow_dvd_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    {π x y : R} (hcast : π ^ (p - 1) ∣ (p : R)) (hxy : π ∣ x - y) :
    π ^ p ∣ x ^ p - y ^ p := by
  obtain ⟨t, ht⟩ := hxy
  rw [sub_eq_iff_eq_add.mp ht]
  apply hp.dvd_add_pow_sub_pow_of_dvd
  · rw [mul_pow]
    exact dvd_mul_right _ _
  · have hd := mul_dvd_mul hcast (dvd_mul_right π t)
    rwa [← pow_succ, Nat.sub_add_cancel hp.one_lt.le] at hd


open scoped NumberField
open IsCyclotomicExtension.Rat

/-- A p-th power in the cyclotomic integers is congruent to a rational integer and its
p-th power modulo the p-th power of the cyclotomic uniformizer. -/
theorem exists_int_pow_congruent {K : Type*} [Field K] [NumberField K] {p : ℕ}
    [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (a : 𝓞 K) : ∃ c : ℤ,
      (1 - hζ.toInteger) ^ p ∣ a ^ p - (c : 𝓞 K) ^ p ∧
      (1 - hζ.toInteger) ^ p ∣ (c : 𝓞 K) ^ p - c ∧
      (p : 𝓞 K) ∣ a ^ p - c := by
  have hgen : hζ.subOneIntegralPowerBasis.gen = hζ.toInteger - 1 := by
    rw [hζ.subOneIntegralPowerBasis_gen]
    rfl
  obtain ⟨r, hr⟩ := hζ.subOneIntegralPowerBasis.exists_gen_dvd_sub a
  rw [hgen, algebraMap_int_eq] at hr
  have hπ : Associated (1 - hζ.toInteger) (hζ.toInteger - 1) := by
    rw [← neg_sub, Associated.neg_left_iff]
  have hpc : Associated ((1 - hζ.toInteger) ^ (p - 1)) (p : 𝓞 K) :=
    hπ.pow_pow.trans (associated_zeta_sub_one_pow_prime p hζ)
  have hbase : (1 - hζ.toInteger) ∣ a - (r : 𝓞 K) := hπ.dvd.trans hr
  have hlift := pow_sub_pow_dvd_of_dvd_sub hp.out hpc.dvd hbase
  have hfermat : (p : ℤ) ∣ r ^ p - r := (Int.ModEq.pow_prime_eq_self hp.out r).symm.dvd
  have hcast : (p : 𝓞 K) ∣ (r : 𝓞 K) ^ p - r := by
    simpa only [Int.cast_natCast, Int.cast_sub, Int.cast_pow] using
      Int.cast_dvd_cast (α := 𝓞 K) _ _ hfermat
  have hpdiv : 1 - hζ.toInteger ∣ (p : 𝓞 K) :=
    (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hp.out.one_lt)).trans hpc.dvd
  have hconst := pow_sub_pow_dvd_of_dvd_sub hp.out hpc.dvd (hpdiv.trans hcast)
  -- The stronger congruence holds using the power of the initial integer lift.
  refine ⟨r ^ p, ?_, ?_, ?_⟩
  · simpa only [Int.cast_pow, sub_sub_sub_cancel_right] using dvd_sub hlift hconst
  · simpa only [Int.cast_pow] using hconst
  · simpa only [Int.cast_pow] using
      (hpc.symm.dvd.trans (pow_dvd_pow (1 - hζ.toInteger) (Nat.sub_le p 1))).trans hlift


open Module in
/-- Divisibility by a scalar in an algebra is equivalent to divisibility of each basis
coefficient. -/
private theorem algebraMap_dvd_sum_smul_iff {A B ι : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Fintype ι] (b : Basis ι A B) (p : A) (c : ι → A) :
    algebraMap A B p ∣ ∑ i, c i • b i ↔ ∀ i, p ∣ c i := by
  constructor
  · rintro ⟨y, hy⟩ i
    rw [← Algebra.smul_def] at hy
    have h := congrArg (fun z => b.repr z i) hy
    refine ⟨b.repr y i, ?_⟩
    simpa only [Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] using h
  · intro hc
    classical
    choose d hd using hc
    refine ⟨∑ i, d i • b i, ?_⟩
    rw [← Algebra.smul_def, Finset.smul_sum]
    simp_rw [smul_smul, ← hd]


/-- An integer linear combination of a cyclotomic power basis is divisible by the
rational prime exactly when all of its coefficients are. -/
theorem natCast_dvd_sum_smul_zeta_pow_iff {K : Type*} [Field K] [NumberField K] {p : ℕ}
    [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c : Fin hζ.integralPowerBasis.dim → ℤ) :
    (p : 𝓞 K) ∣ ∑ i, c i • hζ.toInteger ^ (i : ℕ) ↔ ∀ i, (p : ℤ) ∣ c i := by
  simpa only [map_natCast, PowerBasis.basis_eq_pow,
    hζ.integralPowerBasis_gen] using
    algebraMap_dvd_sum_smul_iff hζ.integralPowerBasis.basis (p : ℤ) c

end TinyTauDemo
