/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.TameDifferentials
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The local differential length and ramification index

For an extension of discrete valuation rings, the local length formula
uses the ramification index of the target maximal ideal.
See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `86aa35292310f4aab67f58a8b69693bf1ec59284`.
-/

public section

open IsLocalRing

namespace TinyTauDemo

/-- The ramification index of a local map of DVRs is the valuation of the
image of a source uniformizer. -/
theorem ramificationIdx_maximalIdeal_eq_toNat_addVal {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    {t : A} (ht : Irreducible t) (ht₀ : algebraMap A B t ≠ 0) :
    (maximalIdeal B).ramificationIdx A =
      (IsDiscreteValuationRing.addVal B (algebraMap A B t)).toNat := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht₀ hu
  let Q := maximalIdeal B
  let L := Localization.AtPrime Q
  have hunder : Q.under A = maximalIdeal A := maximalIdeal_comap (algebraMap A B)
  have hmap : (maximalIdeal A).map (algebraMap A B) = Q ^ e := by
    change (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e
    rw [ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hv,
      ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr v.isUnit,
      Ideal.top_mul, ← Ideal.span_singleton_pow, ← hu.maximalIdeal_eq]
  have hL : (maximalIdeal A).map (algebraMap A L) = maximalIdeal L ^ e := by
    rw [IsScalarTower.algebraMap_eq A B L, ← Ideal.map_map, hmap, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
      (IsDiscreteValuationRing.not_a_field B) L
  change Q.ramificationIdx A = _
  rw [Ideal.ramificationIdx_def, hunder, hL,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast,
    IsDiscreteValuationRing.addVal_def _ v hu e hv, ENat.toNat_natCast]

/-- The length of the relative differentials of a local tame map of curve
rings is the ramification index minus one. -/
theorem length_relativeKaehlerDifferential_eq_ramificationIdx_sub_one {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsLocalHom (algebraMap A B)] [CharZero (ResidueField B)]
    [Module.Finite A Ω[A⁄k]] [Module.Finite B Ω[B⁄k]]
    [Module.IsTorsionFree B Ω[B⁄k]] [Nontrivial Ω[B⁄k]]
    (hA : Subsingleton Ω[ResidueField A⁄k]) (hB : Subsingleton Ω[ResidueField B⁄k])
    {t : A} {u : B} (ht : Irreducible t) (hu : Irreducible u)
    (ht₀ : algebraMap A B t ≠ 0) :
    Module.length B Ω[B⁄A] = ↑((maximalIdeal B).ramificationIdx A - 1 : ℕ) := by
  rw [ramificationIdx_maximalIdeal_eq_toNat_addVal ht ht₀]
  exact length_relativeKaehlerDifferential_eq_addVal_sub_one_of_finite hA hB ht hu ht₀

end TinyTauDemo
