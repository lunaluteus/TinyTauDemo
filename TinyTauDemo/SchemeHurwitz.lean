/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.SerreDuality
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
public import TinyTauDemo.HurwitzFibreCount
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Tactic.NormNum

/-!
# The numerical Riemann–Hurwitz formula for schemes

A dominant morphism of proper regular curves induces a finite extension of
their function fields. Comparing genera and reindexing the different by the
codimension-one points gives the scheme formula.
See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `403fbccd18f6bf4daf7cc7d42871f27446906a75`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order
open TauCeti TauCeti.AlgebraicGeometry

universe u

/-- The map on function fields agrees with the map on each stalk under the canonical inclusions. -/
theorem AlgebraicGeometry.Scheme.Hom.functionFieldMap_algebraMap_stalk_apply
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (x : X) (a : Y.presheaf.stalk (f x)) :
    f.functionFieldMap (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  obtain ⟨U, hx, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  let : Nonempty U := ⟨⟨_, hx⟩⟩
  let : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
  rw [Y.algebraMap_germ_eq_germToFunctionField, f.germ_stalkMap_apply]
  have h := congrArg (fun g ↦ g s) (f.germToFunctionField_functionFieldMap U)
  exact h.trans (X.algebraMap_germ_eq_germToFunctionField (show x ∈ f ⁻¹ᵁ U from hx)
    (f.app U s)).symm

namespace TinyTauDemo

section FiniteFunctionFields

variable {k F L : Type u} [Field k] [Field F] [Field L] [Algebra k F] [Algebra k L]
  [Algebra F L] [IsScalarTower k F L]

/-- An extension between two algebraic function fields over the same constants is finite. -/
theorem finiteDimensional_of_functionFields
    (hF : IsFunctionField k F) (hL : IsFunctionField k L) : FiniteDimensional F L := by
  have h := trdeg_add_eq k F (A := L)
  rw [hF.trdeg_eq_one, hL.trdeg_eq_one] at h
  have hz : Algebra.trdeg F L = 0 := by
    by_contra hne
    have hle := add_le_add_left (Cardinal.one_le_iff_ne_zero.mpr hne) (1 : Cardinal)
    rw [add_comm (Algebra.trdeg F L) 1, h] at hle
    norm_num at hle
  have : Algebra.IsAlgebraic F L := trdeg_eq_zero_iff.mp hz
  have : Algebra.EssFiniteType k L := hL.essFiniteType
  have : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp k F L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end FiniteFunctionFields

variable {k : Type u} [Field k]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X.IsCurveOver k] [Y.IsCurveOver k]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y))]

private theorem valuativeExistenceOfProper {U V : Scheme} (f : U ⟶ V) [IsProper f] :
    ValuativeCriterion.Existence f := by
  have h : UniversallyClosed f := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

private theorem coheight_le_one_of_isCurveOver (k : Type u) [Field k]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))] [Z.IsCurveOver k] (z : Z) : coheight z ≤ 1 := by
  have h := coheight_le_topologicalKrullDim z
  rw [Scheme.IsCurveOver.topologicalKrullDim_eq_one k] at h
  exact_mod_cast h

private theorem curveIsSeparated (k : Type u) [Field k] (Z : Scheme.{u})
    [Z.Over (Spec (.of k))] [Z.IsCurveOver k] : Z.IsSeparated := by
  constructor
  rw [← terminal.comp_from (Z ↘ Spec (.of k))]
  infer_instance

/-- Closed points of a regular proper curve correspond to the places of its function field. -/
noncomputable def curveCodimensionOnePointEquivPlace (k : Type u) [Field k]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))] [Z.IsCurveOver k]
    [∀ z : CodimensionOnePoint Z, IsDiscreteValuationRing (Z.presheaf.stalk (z : Z))] :
    CodimensionOnePoint Z ≃ Place k Z.functionField := by
  let : Z.IsSeparated := curveIsSeparated k Z
  exact CodimensionOnePoint.equivPlace
    (valuativeExistenceOfProper (Z ↘ Spec (.of k))) (coheight_le_one_of_isCurveOver k Z)

/-- The place of a codimension-one point is the normalized valuation of its local ring. -/
theorem curveCodimensionOnePointEquivPlace_apply (k : Type u) [Field k]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))] [Z.IsCurveOver k]
    [∀ z : CodimensionOnePoint Z, IsDiscreteValuationRing (Z.presheaf.stalk (z : Z))]
    (z : CodimensionOnePoint Z) :
    curveCodimensionOnePointEquivPlace k Z z = Z.toPlace (k := k) (z : Z) := by
  let : Z.IsSeparated := curveIsSeparated k Z
  unfold curveCodimensionOnePointEquivPlace
  exact CodimensionOnePoint.equivPlace_apply _ _ _

/-- Over algebraically closed constants, the genus of a regular proper curve
agrees with the genus of its function field. -/
theorem genus_eq_genus_of_regularProperCurve [IsAlgClosed k]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))] [Z.IsCurveOver k]
    [∀ z : CodimensionOnePoint Z, IsDiscreteValuationRing (Z.presheaf.stalk (z : Z))] :
    letI := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Z) k)
    Z.genus k = genus k Z.functionField := by
  let : Z.IsSeparated := curveIsSeparated k Z
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : IsNoetherian Z := {}
  exact SchemeWeilDivisor.genus_eq_genus_functionField
    (valuativeExistenceOfProper (Z ↘ Spec (.of k))) (coheight_le_one_of_isCurveOver k Z)
    (Scheme.IsCurveOver.isFunctionField (k := k) (X := Z)) isIntegrallyClosedIn_of_isAlgClosed

variable [IsAlgClosed k] [CharZero k]

/-- Riemann–Hurwitz for a dominant morphism of regular proper curves, with the
ramification term indexed by the codimension-one points of the source. -/
theorem hurwitz_genus_formula_of_regularProperCurveHom
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f] :
    letI : Algebra Y.functionField X.functionField := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    letI : IsScalarTower k Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
    let hY := Scheme.IsCurveOver.isFunctionField (k := k) (X := Y)
    let hX := Scheme.IsCurveOver.isFunctionField (k := k) (X := X)
    letI := finiteDimensional_of_functionFields hY hX
    letI : CharZero Y.functionField :=
      charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
    let e := curveCodimensionOnePointEquivPlace k X
    letI := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
    letI := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k)
    2 * (X.genus k : ℤ) - 2 =
      Module.finrank Y.functionField X.functionField * (2 * (Y.genus k : ℤ) - 2) +
        ∑ x ∈ (Divisor.tameDifferent k X.functionField hY).support.map e.symm.toEmbedding,
          ((Place.ramificationIdx Y.functionField (e x) : ℤ) - 1) := by
  let : Algebra Y.functionField X.functionField := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let : IsScalarTower k Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let : FiniteDimensional Y.functionField X.functionField :=
    finiteDimensional_of_functionFields
      (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y))
      (Scheme.IsCurveOver.isFunctionField (k := k) (X := X))
  let : CharZero Y.functionField :=
    charZero_of_injective_algebraMap (algebraMap k Y.functionField).injective
  dsimp only
  rw [genus_eq_genus_of_regularProperCurve X, genus_eq_genus_of_regularProperCurve Y,
    Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
  exact hurwitz_genus_formula_of_isAlgClosed
    (Scheme.IsCurveOver.isFunctionField (k := k) (X := Y))
    (Scheme.IsCurveOver.isFunctionField (k := k) (X := X))

end TinyTauDemo
