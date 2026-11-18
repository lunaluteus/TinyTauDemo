/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The cyclotomic cover of the integer spectrum

The spectrum of the ring of integers is finite and flat over the integer
spectrum. For an odd prime cyclotomic field, restricting to the complement
of the prime gives an étale morphism.
See `/roadmap/index.qmd#rem-arithmetic-surface @ c137a8d08b3fea0a76fca0aae70cebc6f1dbbe7c`.
-/

public section

open AlgebraicGeometry CategoryTheory NumberField

namespace TinyTauDemo

/-- The structural morphism from the spectrum of the ring of integers of a number field. -/
noncomputable def ringOfIntegersSpecHom (K : Type) [Field K] [NumberField K] :
    Spec (CommRingCat.of (𝓞 K)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 K)))

/-- The ring of integers of a number field is finite and flat over the integers. -/
theorem ringOfIntegersSpecHom_finite_flat (K : Type) [Field K] [NumberField K] :
    IsFinite (ringOfIntegersSpecHom K) ∧ Flat (ringOfIntegersSpecHom K) := by
  rw [ringOfIntegersSpecHom, IsFinite.SpecMap_iff, Flat.SpecMap_iff]
  change (algebraMap ℤ (𝓞 K)).Finite ∧ (algebraMap ℤ (𝓞 K)).Flat
  exact ⟨RingHom.finite_algebraMap.mpr inferInstance,
    RingHom.flat_algebraMap_iff.mpr inferInstance⟩

/-- The cyclotomic cover is étale over the basic open complementary to the odd prime. -/
theorem ringOfIntegersSpecHom_etale_away {K : Type} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    Etale (ringOfIntegersSpecHom K ∣_ PrimeSpectrum.basicOpen (R := ℤ) (p : ℤ)) := by
  let φ := CommRingCat.ofHom (algebraMap ℤ (𝓞 K))
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme) :=
    HasRingHomProperty.stableUnderComposition RingHom.Etale.stableUnderComposition
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition (by
      intro X Y g hg
      have : IsIso g := hg
      infer_instance)
  refine (MorphismProperty.arrow_mk_iso_iff @Etale
    (SpecMapRestrictBasicOpenIso φ (p : ℤ))).mpr ?_
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  let A := Localization.Away (p : ℤ)
  let B := Localization.Away (algebraMap ℤ (𝓞 K) (p : ℤ))
  let _ : Algebra A B := (Localization.awayMap (algebraMap ℤ (𝓞 K)) (p : ℤ)).toAlgebra
  change Algebra.Etale A B
  have : Algebra.Etale ℤ A := Algebra.Etale.of_isLocalizationAway (p : ℤ)
  have : Algebra.Etale ℤ B := by
    change Algebra.Etale ℤ (Localization.Away (algebraMap ℤ (𝓞 K) (p : ℤ)))
    rw [map_natCast]
    exact hζ.etale_localizationAway_natCast hp2
  have := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := A) (A := B) (Subsingleton.elim _ _)
  exact Algebra.Etale.of_restrictScalars ℤ A B

end TinyTauDemo
