/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.DifferentialMonomorphism
import TinyTauDemo.SchemeHurwitz
import TauCeti.AlgebraicGeometry.LineBundle.Germ
import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import Mathlib.RingTheory.Unramified.Field

/-!
# Relative differential length at closed points of smooth curves

At a closed point the local ring of a smooth integral curve is a discrete
valuation ring. The absolute differential stalk is free of rank one, and the
residue field is finite separable over the base field in characteristic zero.
These facts give the length formula for a dominant map of smooth curves.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `82b6a524e4181b9a17b86406e8500becee53a4f0`.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- A rank-one trivialization gives a linear coordinate on the stalk at a point
of its domain. -/
def stalkLinearEquivOfTrivialization {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (x : X) (hi : x ∈ U) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] M.presheaf.stalk x := by
  let s := M.trivializationGenerator t
  let v := M.presheaf.germ U x hi s
  let F : X.presheaf.stalk x →ₗ[X.presheaf.stalk x] M.presheaf.stalk x :=
    { toFun := fun r ↦ r • v
      map_add' := fun a b ↦ add_smul a b v
      map_smul' := fun a b ↦ mul_smul a b v }
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨W, hWU, hW, r₀, rfl⟩ := X.presheaf.exists_le_germ_eq r hi
    let iWU : W ⟶ U := homOfLE hWU
    change X.presheaf.germ W x hW r₀ • M.presheaf.germ U x hi s = 0 at hr
    rw [← M.presheaf.germ_res_apply iWU x hW, ← Scheme.Modules.germ_smul,
      ← (M.presheaf.germ W x hW).hom.map_zero] at hr
    let sW : Γ(M, W) := M.presheaf.map iWU.op s
    let rW : Γ(X, W) := r₀
    obtain ⟨V, hv, j, j', h⟩ := M.presheaf.germ_eq x hW hW (rW • sW) 0 hr
    have hsmul : M.presheaf.map j.op (rW • sW) =
        X.presheaf.map j.op rW • M.presheaf.map j.op sW :=
      M.val.map_smul j.op rW sW
    have hcomp : M.presheaf.map j.op sW = M.presheaf.map (j ≫ iWU).op s := by
      dsimp only [sW]
      exact (ConcreteCategory.congr_hom (M.presheaf.map_comp iWU.op j.op) s).symm
    rw [hsmul, hcomp, map_zero] at h
    have hh := congrArg (M.trivializationCoordinate t (j ≫ iWU)) h
    rw [map_smul, M.trivializationCoordinate_map_trivializationGenerator, map_zero,
      smul_eq_mul, mul_one] at hh
    rw [← X.presheaf.germ_res_apply j x hv]
    change X.presheaf.germ V x hv (X.presheaf.map j.op rW) = 0
    rw [hh, map_zero]
  · intro z
    obtain ⟨W, hWU, hW, m, rfl⟩ := M.presheaf.exists_le_germ_eq z hi
    let iWU : W ⟶ U := homOfLE hWU
    let r := M.trivializationCoordinate t iWU m
    refine ⟨X.presheaf.germ W x hW r, ?_⟩
    change X.presheaf.germ W x hW r • M.presheaf.germ U x hi s = _
    rw [← M.presheaf.germ_res_apply iWU x hW, ← Scheme.Modules.germ_smul]
    congr 1
    apply (M.trivializationCoordinate t iWU).injective
    rw [map_smul, M.trivializationCoordinate_map_trivializationGenerator]
    exact mul_one r

/-- The stalk basis is the germ of the generating section of the trivialization. -/
theorem stalkLinearEquivOfTrivialization_apply {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (t : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (x : X) (hx : x ∈ U) (r : X.presheaf.stalk x) :
    stalkLinearEquivOfTrivialization M t x hx r =
      r • M.presheaf.germ U x hx (M.trivializationGenerator t) :=
  by unfold stalkLinearEquivOfTrivialization; rfl

private def invertibleStalkLinearEquiv {X : Scheme.{u}} (L : InvertibleSheaf X) (x : X) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L.obj.presheaf.stalk x := by
  have h := L.obj.exists_mem_trivialization x
  exact stalkLinearEquivOfTrivialization L.obj h.choose_spec.choose x
    h.choose_spec.choose_spec

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

set_option backward.isDefEq.respectTransparency false in
private def smoothCurveKaehlerEquiv [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    (x : X) : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k] :=
  let L : InvertibleSheaf X := ⟨X.relativeDifferentials k, isInvertible_relativeDifferentials k⟩
  (invertibleStalkLinearEquiv L x).trans (X.relativeDifferentialsStalkEquiv k x)

/-- A smooth integral curve has a discrete valuation ring at each closed point. -/
theorem isDiscreteValuationRing_stalk_of_closed_smoothCurve
    [IsIntegral X] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] (x : X) (hx : IsClosed {x}) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have h := (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ Spec (.of k)) 1).mp
    inferInstance
  have := h.1
  have := isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k)) x
  exact TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr (h.2 x hx)

set_option backward.isDefEq.respectTransparency false in
private theorem subsingleton_closed_residueDifferentials [CharZero k]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X) (hx : IsClosed {x}) :
    Subsingleton Ω[IsLocalRing.ResidueField (X.presheaf.stalk x)⁄k] := by
  let f := X ↘ Spec (.of k)
  have hn := f.residueDegree_ne_zero_of_isClosed hx
  have he := f.residueDegree_eq_finrank x
  rw [← Scheme.residueFieldBaseAlgebra_eq_compHom k X x] at he
  have hf : Module.Finite k (X.residueField x) :=
    Module.finite_of_finrank_pos (Nat.pos_of_ne_zero (he ▸ hn))
  have hu : Algebra.FormallyUnramified k (X.residueField x) :=
    Algebra.FormallyUnramified.of_isSeparable k (X.residueField x)
  exact inferInstanceAs (Subsingleton Ω[X.residueField x⁄k])

private theorem stalkMap_injective_of_dominant_curves {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] (x : X) :
    Function.Injective (f.stalkMap x) := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply f.functionFieldMap.hom.injective
  rw [f.functionFieldMap_algebraMap_stalk_apply, f.functionFieldMap_algebraMap_stalk_apply, hab]

/-- A morphism over a field between smooth curves sends closed points to closed points. -/
theorem isClosed_image_of_smoothCurveHom {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (x : X) (hx : IsClosed {x}) : IsClosed {f x} := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType (f ≫ (Y ↘ Spec (.of k))) := by
    rw [comp_over f (Spec (.of k))]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (.of k))
  exact f.closedPoints_subset_preimage_closedPoints hx

section Length

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [IsIntegral X] [IsIntegral Y] [CharZero k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f] (x : X)

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x

attribute [local instance] algebraStalkMap

set_option backward.isDefEq.respectTransparency false in
/-- At every closed point of a dominant morphism of smooth integral curves in
characteristic zero, the relative differential stalk has length equal to the local
ramification index minus one. -/
theorem length_morphismRelativeDifferentials_stalk_of_closed_smoothCurves
    (hx : IsClosed {x}) :
    Module.length B ((morphismRelativeDifferentials k f).presheaf.stalk x) =
      ↑((IsLocalRing.maximalIdeal B).ramificationIdx A - 1 : ℕ) := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of k))
  have hy : IsClosed {f x} := isClosed_image_of_smoothCurveHom (k := k) f x hx
  have : IsDiscreteValuationRing A :=
    isDiscreteValuationRing_stalk_of_closed_smoothCurve (k := k) (f x) hy
  have : IsDiscreteValuationRing B :=
    isDiscreteValuationRing_stalk_of_closed_smoothCurve (k := k) x hx
  let ea := smoothCurveKaehlerEquiv (k := k) (f x)
  let eb := smoothCurveKaehlerEquiv (k := k) x
  have : Module.Finite A Ω[A⁄k] := Module.Finite.of_surjective ea.toLinearMap ea.surjective
  have : Module.Finite B Ω[B⁄k] := Module.Finite.of_surjective eb.toLinearMap eb.surjective
  have : Module.Free B Ω[B⁄k] := Module.Free.of_equiv eb
  have : Nontrivial Ω[B⁄k] := eb.injective.nontrivial
  have : CharZero (IsLocalRing.ResidueField B) :=
    charZero_of_injective_algebraMap (algebraMap k (X.residueField x)).injective
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨v, hv⟩ := IsDiscreteValuationRing.exists_irreducible B
  exact length_morphismRelativeDifferentials_stalk k f x
    (subsingleton_closed_residueDifferentials (f x) hy)
    (subsingleton_closed_residueDifferentials x hx) ht hv
    ((map_ne_zero_iff _ (stalkMap_injective_of_dominant_curves f x)).mpr ht.ne_zero)

/-- A closed point has nonzero relative differentials precisely when its local
ramification index is greater than one. -/
theorem nontrivial_morphismRelativeDifferentials_stalk_iff_ramified
    (hx : IsClosed {x}) : Nontrivial ((morphismRelativeDifferentials k f).presheaf.stalk x) ↔
      1 < (IsLocalRing.maximalIdeal B).ramificationIdx A := by
  rw [← Module.length_pos_iff (R := B),
    length_morphismRelativeDifferentials_stalk_of_closed_smoothCurves f x hx]
  exact_mod_cast Nat.sub_pos_iff_lt

end Length

end

end TinyTauDemo
