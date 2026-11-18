/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Points and local rings of an affine Dedekind scheme

The generic residue field is the fraction field. At a nonzero prime, the stalk
is a discrete valuation ring and its order is the inverse adic valuation.
See `/roadmap/index.qmd#rem-scheme-dedekind` @
`26c70d14054d806f59c50c3fd58695904527c61d`.
-/

public section

namespace PrimeSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Every nonzero prime of a Dedekind domain gives a closed point. The zero
prime does so exactly in the field case. -/
theorem isClosed_singleton_iff_ne_bot_or_isField (x : PrimeSpectrum R) :
    IsClosed ({x} : Set (PrimeSpectrum R)) ↔ x ≠ ⊥ ∨ IsField R := by
  rw [isClosed_singleton_iff_isMaximal]
  constructor
  · intro hx
    by_cases hR : IsField R
    · exact Or.inr hR
    · left
      intro h
      exact Ring.ne_bot_of_isMaximal_of_not_isField hx hR (congrArg asIdeal h)
  · rintro (hx | hR)
    · apply x.isPrime.isMaximal_of_ne_bot
      intro h
      exact hx (PrimeSpectrum.ext h)
    · let I := hR.toField
      infer_instance

end PrimeSpectrum

namespace AlgebraicGeometry

open TopologicalSpace
open scoped nonZeroDivisors

section FractionField

variable (R : CommRingCat) [IsDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The residue field at the generic point of an affine integral scheme is the
fraction field of its coordinate ring. -/
noncomputable def Spec.fractionRingEquivGenericResidueField :
    K ≃+* (Spec R).residueField (genericPoint (Spec R)) :=
  (IsLocalization.algEquiv R⁰ K (Spec R).functionField).toRingEquiv.trans
    (RingEquiv.ofBijective ((Spec R).residue (genericPoint (Spec R))).hom
      ⟨((Spec R).residue (genericPoint (Spec R))).hom.injective, (Spec R).residue_surjective _⟩)

/-- The generic residue field identification is compatible with the map from `R`. -/
@[simp] theorem Spec.fractionRingEquivGenericResidueField_algebraMap (r : R) :
    Spec.fractionRingEquivGenericResidueField R K (algebraMap R K r) =
      (Spec R).residue (genericPoint (Spec R)) (algebraMap R (Spec R).functionField r) := by
  simp [Spec.fractionRingEquivGenericResidueField]
  rfl

end FractionField

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An affine Dedekind scheme has a discrete valuation ring at each point distinct
from its generic point. The generic stalk is its fraction field. -/
theorem Spec.stalk_isDiscreteValuationRing_iff_ne_genericPoint (x : Spec (.of R)) :
    IsDiscreteValuationRing ((Spec (.of R)).presheaf.stalk x) ↔
      x ≠ genericPoint (Spec (.of R)) := by
  constructor
  · intro h hx
    subst x
    let : IsDiscreteValuationRing (Spec (.of R)).functionField := h
    exact IsDiscreteValuationRing.not_isField (Spec (.of R)).functionField
      (Semifield.toIsField (Spec (.of R)).functionField)
  · intro hx
    have hprime : x.asIdeal ≠ ⊥ := fun h ↦
      hx ((PrimeSpectrum.ext h).trans (genericPoint_eq_bot_of_affine (.of R)).symm)
    let : x.asIdeal.IsPrime := x.isPrime
    let S := (Spec (.of R)).presheaf.stalk x
    let : Algebra R S := StructureSheaf.stalkAlgebra R x
    let : IsLocalization.AtPrime S x.asIdeal := StructureSheaf.IsLocalization.to_stalk R x
    exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hprime S

/-- In a nonfield Dedekind spectrum the closed points are exactly those with
a discrete valuation ring as their stalk. -/
theorem Spec.isClosed_singleton_iff_stalk_isDiscreteValuationRing
    (hR : ¬ IsField R) (x : Spec (.of R)) :
    IsClosed ({x} : Set (Spec (.of R))) ↔
      IsDiscreteValuationRing ((Spec (.of R)).presheaf.stalk x) := by
  rw [Spec.stalk_isDiscreteValuationRing_iff_ne_genericPoint, genericPoint_eq_bot_of_affine]
  exact (PrimeSpectrum.isClosed_singleton_iff_ne_bot_or_isField x).trans (or_iff_left hR)

end AlgebraicGeometry

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

/-- The local order at a height-one prime is the inverse of the associated
multiplicatively valued adic valuation. -/
theorem ordFrac_eq_inv_adicValuation
    {R S K : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] (v : HeightOneSpectrum R) [IsLocalization.AtPrime S v.asIdeal]
    [IsDiscreteValuationRing S] [Field K] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] [IsFractionRing R K] [IsFractionRing S K] (x : K) :
    Ring.ordFrac S x = (v.valuation K x)⁻¹ := by
  let w := IsDiscreteValuationRing.maximalIdeal S
  have hw : v.valuation K = w.valuation K := by
    refine Valuation.eq_valuation_of_forall_mem_asIdeal_iff (w.valuation_surjective K) ?_ ?_
    · intro r
      rw [IsScalarTower.algebraMap_apply R S K]
      exact w.valuation_le_one (algebraMap R S r)
    · intro r
      rw [IsScalarTower.algebraMap_apply R S K, w.valuation_lt_one_iff_mem]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S v.asIdeal r).symm
  rw [Ring.ordFrac_eq_valuation_inv, hw]

end IsDedekindDomain.HeightOneSpectrum
