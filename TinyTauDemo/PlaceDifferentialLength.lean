/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.TameRamificationIndex
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree

/-!
# Ramification of local differentials at function-field places

The DVR valuation of the image of a uniformizer is the place ramification
index. This identifies the relative differential length with the local
contribution to the tame different.
See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `b73a2cb4cf6f8a5b848f4016cc46b4611bb200a2`.
-/

public section

open TauCeti IsLocalRing

namespace TinyTauDemo

private theorem place_isUniformizer_of_irreducible {k F : Type*}
    [Field k] [Field F] [Algebra k F] (P : Place k F) :
    ∀ {u : P.integers}, Irreducible u → P.valuation.IsUniformizer (u : F) := by
  rw [P.integers_def]
  intro u hu
  have : IsDiscreteValuationRing P.valuation.valuationSubring :=
    Valuation.valuationSubring_isDiscreteValuationRing_of_surjective
      P.valuation P.valuation_surjective
  exact Valuation.isUniformizer_of_maximalIdeal_eq_span P.valuation hu.maximalIdeal_eq

/-- The valuation of a nonzero element of the local ring is the normalized order of the place. -/
theorem addVal_placeIntegers_eq_ord {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) {x : P.integers} (hx : x ≠ 0) :
    (IsDiscreteValuationRing.addVal P.integers x).toNat = (P.ord (x : F)).toNat := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible P.integers
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hu
  have hu₀ : (u : F) ≠ 0 := fun h ↦ hu.ne_zero (Subtype.ext h)
  have hv₀ : ((v : P.integers) : F) ≠ 0 := fun h ↦ v.ne_zero (Subtype.ext h)
  have hu_ord : P.ord (u : F) = 1 := P.isUniformizer_iff_ord_eq_one.mp
    (place_isUniformizer_of_irreducible P hu)
  have hv_ord : P.ord ((v : P.integers) : F) = 0 :=
    (P.isUnit_iff_ord_eq_zero hv₀).mp v.isUnit
  have hx_ord : P.ord (x : F) = (n : ℤ) := by
    rw [hv, Subring.coe_mul, Subring.coe_pow, P.ord_mul hv₀ (pow_ne_zero _ hu₀),
      P.ord_pow, hu_ord, hv_ord, mul_one, zero_add]
  rw [IsDiscreteValuationRing.addVal_def _ v hu n hv, ENat.toNat_natCast, hx_ord, Int.toNat_natCast]

section Extension

variable {k F L : Type*} [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    [Algebra.IsIntegral F L] (P : Place k L)

/-- The DVR valuation after the map of place rings is the place ramification index on a
base uniformizer. -/
theorem addVal_algebraMap_place_uniformizer {t : (P.restrict k F).integers}
    (ht : Irreducible t) :
    (IsDiscreteValuationRing.addVal P.integers
      (algebraMap (P.restrict k F).integers P.integers t)).toNat = P.ramificationIdx F := by
  have ht₀ : (t : F) ≠ 0 := fun h ↦ ht.ne_zero (Subtype.ext h)
  have hmap₀ : algebraMap (P.restrict k F).integers P.integers t ≠ 0 := by
    intro h
    have h' := congrArg (fun a : P.integers ↦ (a : L)) h
    rw [Place.coe_algebraMap_integers, Subring.coe_zero] at h'
    exact ht₀ ((map_eq_zero_iff _ (algebraMap F L).injective).mp h')
  have ht_ord : (P.restrict k F).ord (t : F) = 1 :=
    (P.restrict k F).isUniformizer_iff_ord_eq_one.mp
      (place_isUniformizer_of_irreducible (P.restrict k F) ht)
  rw [addVal_placeIntegers_eq_ord P hmap₀, Place.coe_algebraMap_integers,
    Place.ord_algebraMap_restrict k F P, ht_ord, mul_one, Int.toNat_natCast]

/-- The local relative differential length is the normalized place ramification
index minus one. This is the same local contribution as the tame different. -/
theorem length_relativeKaehlerDifferential_placeIntegers [CharZero k]
    [Module.Finite (P.restrict k F).integers Ω[(P.restrict k F).integers⁄k]]
    [Module.Finite P.integers Ω[P.integers⁄k]]
    [Module.IsTorsionFree P.integers Ω[P.integers⁄k]] [Nontrivial Ω[P.integers⁄k]]
    (hA : Subsingleton Ω[ResidueField (P.restrict k F).integers⁄k])
    (hB : Subsingleton Ω[ResidueField P.integers⁄k])
    {t : (P.restrict k F).integers} {u : P.integers} (ht : Irreducible t) (hu : Irreducible u) :
    Module.length P.integers Ω[P.integers⁄(P.restrict k F).integers] =
      ↑(P.ramificationIdx F - 1 : ℕ) := by
  have : CharZero (ResidueField P.integers) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField P.integers)).injective
  have hmap₀ : algebraMap (P.restrict k F).integers P.integers t ≠ 0 := by
    intro h
    have h' := congrArg (fun a : P.integers ↦ (a : L)) h
    rw [Place.coe_algebraMap_integers, Subring.coe_zero] at h'
    exact ht.ne_zero (Subtype.ext ((map_eq_zero_iff _ (algebraMap F L).injective).mp h'))
  rw [length_relativeKaehlerDifferential_eq_addVal_sub_one_of_finite hA hB ht hu hmap₀,
    addVal_algebraMap_place_uniformizer P ht]

end Extension

end TinyTauDemo
