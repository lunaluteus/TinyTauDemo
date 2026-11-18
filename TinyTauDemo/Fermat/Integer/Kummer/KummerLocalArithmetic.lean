/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicRamification
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.NormTrace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.Tactic.LinearCombination

/-!
# Local congruences for Kummer's unit lemma

The trace of an integer reduces to its residue times the cyclotomic degree.
The norm expansion at one then lifts a unit congruence to the required power of
the ramified prime. In the cubic case, the unit classification also shows that
primitive cubic units have no cube root. See `/roadmap/index.qmd#rem-kummer-unit-proof` @
`d2c4d4a566aab2eb4ba61e9bb96a4fcd4b9e7eaa`.
-/

public section

open NumberField
open scoped NumberField

namespace TinyTauDemo

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

private theorem trace_eq_sum_galois_smul [IsGalois ℚ K] (b : 𝓞 K) :
    ((Algebra.trace ℤ (𝓞 K) b : ℤ) : 𝓞 K) = ∑ σ : Gal(K/ℚ), σ • b := by
  apply RingOfIntegers.coe_injective
  rw [map_intCast, map_sum]
  -- The action on integers is the restriction of the action on the field.
  change ((Algebra.trace ℤ (𝓞 K) b : ℤ) : K) = ∑ σ : Gal(K/ℚ), σ (b : K)
  rw [← trace_eq_sum_automorphisms]
  simpa only [map_intCast] using congrArg (algebraMap ℚ K) (Algebra.coe_trace_int b)

/-- A cyclotomic integer whose trace is divisible by `p` vanishes modulo the prime above `p`. -/
theorem one_sub_dvd_of_dvd_trace (b : 𝓞 K)
    (hbTrace : (p : ℤ) ∣ Algebra.trace ℤ (𝓞 K) b) : 1 - hζ.toInteger ∣ b := by
  classical
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  let I : Ideal (𝓞 K) := Ideal.span {hζ.toInteger - 1}
  let q := Ideal.Quotient.mk I
  have hz : q hζ.toInteger = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hzσ (σ : Gal(K/ℚ)) : q (σ • (hζ.toInteger - 1)) = 0 := by
    rw [smul_sub, smul_one, map_sub, map_one,
      IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq p K σ
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_pow, hz, one_pow, sub_self]
  have hgen : hζ.subOneIntegralPowerBasis.gen = hζ.toInteger - 1 := by
    rw [hζ.subOneIntegralPowerBasis_gen]
    rfl
  obtain ⟨r, t, hrt⟩ := hζ.subOneIntegralPowerBasis.exists_gen_dvd_sub b
  rw [hgen, show algebraMap ℤ (𝓞 K) r = (r : 𝓞 K) by simp] at hrt
  have hb : b = (r : 𝓞 K) + (hζ.toInteger - 1) * t := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hrt
  have hq (σ : Gal(K/ℚ)) : q (σ • b) = q (r : 𝓞 K) := by
    have hσr : σ • (r : 𝓞 K) = r := map_intCast (MulSemiringAction.toRingHom _ _ σ) r
    rw [hb, smul_add, smul_mul', hσr, map_add, map_mul, hzσ, zero_mul, add_zero]
  have hpq : q (p : 𝓞 K) = 0 := by
    have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa only [zero_add, pow_one]
    have hζp : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa only [zero_add, pow_one] using hζ
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one p 0 hζp)
  have htrq : q ((Algebra.trace ℤ (𝓞 K) b : ℤ) : 𝓞 K) = 0 := by
    obtain ⟨d, hd⟩ := hbTrace
    rw [hd, Int.cast_mul, Int.cast_natCast, map_mul, hpq, zero_mul]
  rw [trace_eq_sum_galois_smul, map_sum] at htrq
  have hcard : Fintype.card (Gal(K/ℚ)) = p - 1 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime hp.out]
  simp only [hq, Finset.sum_const, Finset.card_univ, hcard] at htrq
  have hr0 : q (r : 𝓞 K) = 0 := by
    have hsub : (p - 1) • q (r : 𝓞 K) + q (r : 𝓞 K) = 0 := by
      calc
        _ = (p - 1 + 1) • q (r : 𝓞 K) := by simp only [add_nsmul, one_nsmul]
        _ = 0 := by rw [Nat.sub_add_cancel hp.out.one_lt.le, nsmul_eq_mul,
          ← map_natCast q, hpq, zero_mul]
    rwa [htrq, zero_add] at hsub
  have hqb : q b = 0 := by
    rw [← one_smul (Gal(K/ℚ)) b, hq, hr0]
  rw [← neg_sub, neg_dvd]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hqb)

/-- A unit congruent to an integer modulo `p` has `(p - 1)`-st power congruent
to one modulo the `p`-th power of the cyclotomic uniformizer. -/
theorem one_sub_pow_dvd_unit_pow_pred_sub_one (hp2 : p ≠ 2) (u : (𝓞 K)ˣ)
    (hcong : ∃ r : ℤ, (p : 𝓞 K) ∣ (u : 𝓞 K) - r) :
    (1 - hζ.toInteger) ^ p ∣ (u : 𝓞 K) ^ (p - 1) - 1 := by
  let π := 1 - hζ.toInteger
  have hpπ : π ^ (p - 1) ∣ (p : 𝓞 K) := by
    apply Ideal.span_singleton_le_span_singleton.mp
    rw [← Ideal.span_singleton_pow, hζ.span_natCast_eq_span_one_sub_pow]
  have hπp : π ∣ (p : 𝓞 K) :=
    (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hp.out.one_lt)).trans hpπ
  have hπnotUnit : ¬ IsUnit π := by
    rw [show π = -(hζ.toInteger - 1) by exact (neg_sub _ _).symm, IsUnit.neg_iff]
    exact hζ.zeta_sub_one_prime'.not_isUnit
  obtain ⟨r, hr⟩ := hcong
  have hrnd : ¬ (p : ℤ) ∣ r := by
    intro hdiv
    have hrd : (p : 𝓞 K) ∣ (r : 𝓞 K) := by
      simpa only [Int.cast_natCast] using Int.cast_dvd_cast (α := 𝓞 K) _ _ hdiv
    have hud : (p : 𝓞 K) ∣ (u : 𝓞 K) := (dvd_add hr hrd).trans (by rw [sub_add_cancel])
    exact hπnotUnit (isUnit_of_dvd_unit (hπp.trans hud) u.isUnit)
  have hcop : IsCoprime r (p : ℤ) := by
    rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd]
    exact hrnd
  have hfermat : (p : ℤ) ∣ r ^ (p - 1) - 1 :=
    (Int.ModEq.pow_card_sub_one_eq_one hp.out hcop).symm.dvd
  have hcast : (p : 𝓞 K) ∣ (r : 𝓞 K) ^ (p - 1) - 1 := by
    simpa only [Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one] using
      Int.cast_dvd_cast (α := 𝓞 K) _ _ hfermat
  have hdiff : (p : 𝓞 K) ∣ (u : 𝓞 K) ^ (p - 1) - (r : 𝓞 K) ^ (p - 1) :=
    hr.trans (sub_dvd_pow_sub_pow _ _ _)
  have hunit : (p : 𝓞 K) ∣ (u : 𝓞 K) ^ (p - 1) - 1 := by
    simpa only [sub_add_sub_cancel] using dvd_add hdiff hcast
  obtain ⟨b, hb⟩ := hunit
  have hpow : (u : 𝓞 K) ^ (p - 1) = 1 + (p : ℤ) • b := by
    simpa only [Algebra.smul_def, map_natCast, add_comm] using sub_eq_iff_eq_add.mp hb
  have hnorm : Algebra.norm ℤ ((u : 𝓞 K) ^ (p - 1)) = 1 := by
    rw [map_pow]
    rcases Int.isUnit_iff.mp (u.isUnit.map (Algebra.norm ℤ)) with h | h
    · rw [h, one_pow]
    · rw [h, (hp.out.even_sub_one hp2).neg_pow, one_pow]
  obtain ⟨d, hd⟩ := Algebra.norm_one_add_smul (p : ℤ) b
  rw [← hpow, hnorm] at hd
  have htrace : (p : ℤ) ∣ Algebra.trace ℤ (𝓞 K) b := by
    refine ⟨-d, mul_right_cancel₀ (Int.natCast_ne_zero.mpr hp.out.ne_zero) ?_⟩
    linear_combination -hd
  have hdvd := mul_dvd_mul hpπ (one_sub_dvd_of_dvd_trace hζ b htrace)
  rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, ← hb] at hdvd
  exact hdvd

/-- A cubic cyclotomic unit congruent to an integer modulo three is a cube. -/
theorem exists_unit_cube_of_congruent {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ)
    (hcong : ∃ r : ℤ, (3 : 𝓞 K) ∣ (u : 𝓞 K) - r) : ∃ v : (𝓞 K)ˣ, v ^ 3 = u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv : (hζ.toInteger - 1) ^ 2 ∣ (3 : 𝓞 K) :=
    (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime 3 hζ).dvd
  obtain ⟨r, hr⟩ := hcong
  rcases IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      hζ u ⟨r, hdiv.trans hr⟩ with h | h
  · exact ⟨1, by rw [h, one_pow]⟩
  · exact ⟨-1, by rw [h]; exact (show Odd (3 : ℕ) by decide).neg_one_pow⟩

section CubicUnits

variable {F : Type*} [Field F] {θ : F}

/-- The cube of a unit in the Eisenstein integers is `1` or `-1`. -/
theorem cubicCyclotomic_unit_cube_eq_one_or_neg_one [NumberField F]
    [IsCyclotomicExtension {3} ℚ F] (hθ : IsPrimitiveRoot θ 3)
    (u : (𝓞 F)ˣ) : u ^ 3 = 1 ∨ u ^ 3 = -1 := by
  let η := (hθ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : η ^ 3 = 1 := Units.ext hθ.toInteger_cube_eq_one
  have hη₂ : (η ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by decide, pow_mul, hη, one_pow]
  have hodd : Odd (3 : ℕ) := by decide
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem hθ u
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (one_pow 3)
  · exact Or.inr hodd.neg_one_pow
  · exact Or.inl hη
  · exact Or.inr (by rw [hodd.neg_pow, hη])
  · exact Or.inl hη₂
  · exact Or.inr (by rw [hodd.neg_pow, hη₂])

/-- The unit associated to a primitive cubic root is never the cube of an Eisenstein unit. -/
theorem primitive_cubic_unit_not_cube [NumberField F] [IsCyclotomicExtension {3} ℚ F]
    (hθ : IsPrimitiveRoot θ 3) :
    ¬ ∃ u : (𝓞 F)ˣ, u ^ 3 = (hθ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit := by
  rintro ⟨u, hu⟩
  rcases cubicCyclotomic_unit_cube_eq_one_or_neg_one hθ u with h | h
  · have hη : hθ.toInteger = 1 := congrArg Units.val (hu.symm.trans h)
    exact hθ.toInteger_isPrimitiveRoot.ne_one (by decide) hη
  · have hη : hθ.toInteger = -1 := congrArg Units.val (hu.symm.trans h)
    apply hθ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (l := 2) (by decide) (by decide)
    rw [hη, (show Even (2 : ℕ) by decide).neg_one_pow]

end CubicUnits

/-- The Eisenstein integers contain a primitive cubic unit with no cube root in their
unit group. -/
theorem exists_eisenstein_unit_not_cube :
    ∃ η : (𝓞 (CyclotomicField 3 ℚ))ˣ,
      IsPrimitiveRoot (η : 𝓞 (CyclotomicField 3 ℚ)) 3 ∧
        ¬ ∃ u : (𝓞 (CyclotomicField 3 ℚ))ˣ, u ^ 3 = η := by
  let : NeZero (3 : ℕ) := ⟨by decide⟩
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField 3 ℚ)
    (S := {3}) (n := 3) (by simp) (by decide)
  exact ⟨(hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit,
    hζ.toInteger_isPrimitiveRoot, primitive_cubic_unit_not_cube hζ⟩

end TinyTauDemo
