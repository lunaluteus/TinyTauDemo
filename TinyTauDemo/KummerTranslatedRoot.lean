/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# The translated root of a Kummer polynomial

Dividing the coefficients of `(πX + 1)^p - U` by `π^p` gives a monic equation
for `(r - 1) / π` when `r^p = U`, `π^(p-1) ∣ p`, and `π^p ∣ U - 1`.
See `/roadmap/index.qmd#rem-kummer-unit-proof` @
`908896c23e184ab55914aea0b3d6bbacbdcae5d2`.
-/

public section

open Polynomial

namespace TinyTauDemo

private theorem coeff_C_mul_X_add_one_pow {R : Type*} [CommRing R] (a : R) (m n : ℕ) :
    (((C a * X + 1) ^ m : R[X]).coeff n) = a ^ n * (m.choose n : R) := by
  rw [(Commute.one_right (C a * X)).add_pow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, one_pow, mul_one, mul_pow, ← C_pow, ← C_eq_natCast,
    coeff_mul_C, coeff_C_mul]
  rw [Finset.sum_eq_single n]
  · simp only [coeff_X_pow_self, mul_one]
  · intro j _ hjn
    simp [coeff_X_pow, hjn.symm]
  · simp only [Finset.mem_range, not_lt]
    intro hn
    rw [Nat.choose_eq_zero_of_lt (by omega : m < n), Nat.cast_zero, mul_zero]

/-- A translated Kummer root is integral when the constant and intermediate coefficients
are divisible by the required powers of the translating element. -/
theorem isIntegral_sub_one_div_of_prime_pow
    {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    {p : ℕ} (hp : p.Prime) {π U : R} {r : L}
    (hπ : algebraMap R L π ≠ 0) (hπp : π ^ (p - 1) ∣ (p : R))
    (hU : π ^ p ∣ U - 1) (hr : r ^ p = algebraMap R L U) :
    IsIntegral R ((r - 1) / algebraMap R L π) := by
  have hπ₀ : π ≠ 0 := fun h ↦ hπ (by rw [h, map_zero])
  let P : R[X] := (C π * X + 1) ^ p - C U
  have hdvd : C (π ^ p) ∣ P := by
    refine (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ ?_
    dsimp only [P]
    rw [coeff_sub, coeff_C_mul_X_add_one_pow]
    rcases eq_or_ne i 0 with rfl | hi
    · simpa [neg_sub] using (dvd_neg.mpr hU)
    rw [coeff_C_of_ne_zero hi, sub_zero]
    rcases lt_trichotomy i p with hip | rfl | hpi
    · have hcast : (p : R) ∣ (p.choose i : R) :=
        map_dvd (Nat.castRingHom R) (hp.dvd_choose_self hi hip)
      have hπi : π ∣ π ^ i := dvd_pow_self π hi
      rw [show π ^ p = π * π ^ (p - 1) by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]]
      exact mul_dvd_mul hπi (hπp.trans hcast)
    · simp
    · simp [Nat.choose_eq_zero_of_lt hpi]
  obtain ⟨Q, hQ⟩ := hdvd
  have hcoeff : P.coeff p = π ^ p := by
    dsimp only [P]
    rw [coeff_sub, coeff_C_mul_X_add_one_pow, coeff_C_of_ne_zero hp.ne_zero]
    simp
  have hdeg : P.natDegree = p := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ (hcoeff ▸ pow_ne_zero p hπ₀)
    dsimp only [P]
    rw [sub_eq_add_neg, ← map_neg, natDegree_add_C, natDegree_pow, ← C_1,
      natDegree_add_C, natDegree_C_mul_X _ hπ₀, mul_one]
  have hmonic : Q.Monic := by
    rw [Monic.def]
    have hlead : P.leadingCoeff = π ^ p := by rw [leadingCoeff, hdeg, hcoeff]
    rw [hQ, leadingCoeff_mul, leadingCoeff_C] at hlead
    exact mul_left_cancel₀ (pow_ne_zero p hπ₀) (hlead.trans (mul_one _).symm)
  let x := (r - 1) / algebraMap R L π
  have hx : algebraMap R L π * x + 1 = r := by
    dsimp only [x]
    rw [mul_comm, div_mul_cancel₀ _ hπ, sub_add_cancel]
  have hroot : aeval x P = 0 := by
    dsimp only [P]
    rw [map_sub, map_pow, map_add, map_mul, aeval_C, aeval_X, map_one, hx, hr, aeval_C,
      sub_self]
  rw [hQ, map_mul, aeval_C, map_pow] at hroot
  exact ⟨Q, hmonic, (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero p hπ)⟩

end TinyTauDemo
