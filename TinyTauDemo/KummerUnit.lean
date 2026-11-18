/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.RegularPrime
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TinyTauDemo.KummerLocalArithmetic
import TinyTauDemo.KummerUnramified
import TinyTauDemo.UnramifiedCyclicDegree
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Kummer's unit lemma

Over the cyclotomic field of a regular prime, an integral unit congruent to a
rational integer modulo the prime is a power of an integral unit of that exponent.
The translated Kummer root makes the extension unramified, so regularity and the
first fundamental inequality force its degree to be one.

See `/roadmap/index.qmd#lem-kummer-unit` @ `ccf9193b87c3db948557ea5cf0a099894deb3498`.
-/

public section

open NumberField Polynomial
open scoped NumberField IntermediateField

namespace TinyTauDemo

section IntegralUnits

variable {K : Type*} [Field K] {p : ℕ}

/-- A field root of a positive power of an integral unit is itself an integral unit. -/
private theorem exists_unit_pow_eq_of_field_pow_eq (hp : 0 < p) (u : (𝓞 K)ˣ) (v : K)
    (hv : v ^ p = ((u : 𝓞 K) : K)) : ∃ w : (𝓞 K)ˣ, w ^ p = u := by
  have hvi : IsIntegral ℤ v := IsIntegral.of_pow hp (hv ▸ (u : 𝓞 K).isIntegral_coe)
  have hInv : (v⁻¹) ^ p = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := by
    rw [inv_pow, hv]
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  have hInvI : IsIntegral ℤ v⁻¹ :=
    IsIntegral.of_pow hp (hInv ▸ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K).isIntegral_coe)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne'] at hv
    exact u.ne_zero (RingOfIntegers.coe_injective (by simpa using hv.symm))
  let w : (𝓞 K)ˣ :=
    ⟨⟨v, hvi⟩, ⟨v⁻¹, hInvI⟩, RingOfIntegers.coe_injective (mul_inv_cancel₀ hv0),
      RingOfIntegers.coe_injective (inv_mul_cancel₀ hv0)⟩
  refine ⟨w, Units.ext (RingOfIntegers.coe_injective ?_)⟩
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact hv

/-- A unit is a `p`th power when its `(p - 1)`st power has a `p`th root in the field. -/
private theorem exists_unit_pow_eq_of_field_pow_eq_pred_pow (hp : 0 < p) (u : (𝓞 K)ˣ) (r : K)
    (hr : r ^ p = ((u : 𝓞 K) : K) ^ (p - 1)) : ∃ w : (𝓞 K)ˣ, w ^ p = u := by
  let a : K := ((u : 𝓞 K) : K)
  have ha : a ≠ 0 := fun h ↦ u.ne_zero (RingOfIntegers.coe_injective (h.trans
    (map_zero (algebraMap (𝓞 K) K)).symm))
  apply exists_unit_pow_eq_of_field_pow_eq hp u (a / r)
  change (a / r) ^ p = a
  have hp' : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  rw [div_pow, hr, hp']
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ ha)

end IntegralUnits

/-- Kummer's unit lemma over the cyclotomic field of a regular prime. -/
theorem RegularPrime.kummer_unit {p : ℕ} (hp : RegularPrime p)
    (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hu : ∃ c : ℤ, (p : 𝓞 (CyclotomicField p ℚ)) ∣ (u : 𝓞 (CyclotomicField p ℚ)) - c) :
    ∃ v : (𝓞 (CyclotomicField p ℚ))ˣ, v ^ p = u := by
  by_contra! hn
  let K := CyclotomicField p ℚ
  have : Fact p.Prime := ⟨hp.prime⟩
  have : NeZero p := ⟨hp.prime.ne_zero⟩
  have : IsCyclotomicExtension {p} ℚ K :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
    (Set.mem_singleton p) hp.prime.ne_zero
  let U := u ^ (p - 1)
  let a : K := ((U : 𝓞 K) : K)
  let P : K[X] := X ^ p - C a
  have hP : Irreducible P := X_pow_sub_C_irreducible_of_prime hp.prime fun r hr ↦ by
    have hr' : r ^ p = ((u : 𝓞 K) : K) ^ (p - 1) := by
      simpa only [a, U, Units.val_pow_eq_pow_val, map_pow] using hr
    obtain ⟨v, hv⟩ := exists_unit_pow_eq_of_field_pow_eq_pred_pow hp.prime.pos u r hr'
    exact hn v hv
  let L := P.SplittingField
  have : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L P
  have : NumberField L := NumberField.of_module_finite K L
  have hroots : (primitiveRoots p K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots hp.prime.pos).mpr hζ⟩
  have : IsGalois K L := isGalois_of_isSplittingField_X_pow_sub_C hroots hP L
  have : IsCyclic Gal(L/K) := isCyclic_of_isSplittingField_X_pow_sub_C hroots hP L
  have hdegree : Module.finrank K L = p := finrank_of_isSplittingField_X_pow_sub_C hroots hP L
  let r := rootOfSplitsXPowSubC hp.prime.pos a L
  have hr : r ^ p = algebraMap K L a := rootOfSplitsXPowSubC_pow a L
  have hrU : r ^ p = algebraMap (𝓞 K) L (U : 𝓞 K) := by
    rw [hr, IsScalarTower.algebraMap_apply (𝓞 K) K L]
  have hgen : K⟮r⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hroots hP hr
  have hp2 : p ≠ 2 := by
    have := hp.prime.odd_iff.mp hp.odd
    omega
  have hU : (1 - hζ.toInteger) ^ p ∣ (U : 𝓞 K) - 1 := by
    simpa only [U, Units.val_pow_eq_pow_val] using one_sub_pow_dvd_unit_pow_pred_sub_one hζ hp2 u hu
  have hcop : (Module.finrank K L).Coprime (classNumber K) := by
    rw [hdegree]
    exact hp.coprime_classNumber
  have : IsCMField K := IsCyclotomicExtension.Rat.isCMField K
    ⟨p, Set.mem_singleton p, hp.prime.odd_iff.mp hp.odd⟩
  have htrivial := finrank_eq_one_of_unramified_cyclic_of_coprime_classNumber K L
    (isUnramifiedAt_of_kummer_unit hζ U hrU hgen hU) (IsTotallyComplex.isComplex ·) hcop
  exact hp.prime.ne_one (hdegree.symm.trans htrivial)

end TinyTauDemo
