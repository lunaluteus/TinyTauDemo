/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.PullbackStalk
public import TinyTauDemo.RelativeDifferentialSheaf
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
import TinyTauDemo.SchemeHurwitz
import TauCeti.AlgebraicGeometry.LineBundle.Germ
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Etale.Field

/-!
# Short exactness of the differential sheaf sequence for curves

A dominant morphism of curves in characteristic zero induces a separable
extension at the generic point. The pullback of the target differential sheaf
is invertible, so injectivity at the generic stalk gives a monomorphism.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `6a5e0c4054932c37eb1c977c31a738196704b232`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open scoped TensorProduct

namespace TinyTauDemo

universe u

set_option backward.isDefEq.respectTransparency false in
/-- A map out of an invertible sheaf on an integral scheme is monic if it is
injective on the generic stalk. -/
theorem mono_of_injective_genericStalk {X : Scheme.{u}} [IsIntegral X]
    {M N : X.Modules} [SheafOfModules.isInvertible X M] (g : M ⟶ N)
    (hg : Function.Injective
      (PresheafOfModules.stalkMapCommRing (S := X.presheaf) (genericPoint X) g.val)) : Mono g := by
  let L : InvertibleSheaf X := ⟨M, inferInstance⟩
  have hmono : Mono g.val := by
    apply PresheafOfModules.mono_of_injective
    intro U a b hab
    let V := U.unop
    by_cases hV : Nonempty V
    · let x := genericPoint X
      have hx : x ∈ V := Scheme.genericPoint_mem V
      have hgerm := L.germ_injective_of_isIntegral x hx
      apply hgerm
      apply hg
      have ha := PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x g.val V hx a
      have hb := PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x g.val V hx b
      exact ha.trans ((congrArg (N.presheaf.germ V x hx) hab).trans hb.symm)
    · apply TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      intro x hx
      exact (hV ⟨⟨x, hx⟩⟩).elim
  constructor
  intro Z a b h
  apply SheafOfModules.hom_ext
  apply (cancel_mono g.val).mp
  exact congrArg (fun g' ↦ g'.val) h

section GenericPullback

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegral X] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

local notation "η" => genericPoint X
local notation "A" => Y.presheaf.stalk (f (genericPoint X))
local notation "B" => X.presheaf.stalk (genericPoint X)

set_option backward.isDefEq.respectTransparency false in
/-- For a morphism generically formally étale into a smooth curve, the first
map of differential transitivity is a monomorphism. -/
theorem differentialPullback_mono_of_formallyEtale_generic
    (h : letI := algebraStalkMap f η; Algebra.FormallyEtale A B) :
    Mono (differentialPullback k f) := by
  let := algebraStalkMap f η
  let : Algebra.FormallyEtale A B := h
  let : Algebra k B := Scheme.stalkBaseAlgebra k X η
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap k f η c).symm
  let := isInvertible_relativeDifferentials (X := Y) k
  apply mono_of_injective_genericStalk
  change Function.Injective (differentialPullbackStalk k f η)
  let e := pullbackStalkEquiv f η (Y.relativeDifferentials k)
  let ek := X.relativeDifferentialsStalkEquiv k η
  let eb := (Y.relativeDifferentialsStalkEquiv k (f η)).baseChange A B _ _
  have he := differentialPullbackStalk_eq_mapBaseChange k f η
  intro v w hvw
  obtain ⟨v, rfl⟩ := e.surjective v
  obtain ⟨w, rfl⟩ := e.surjective w
  apply congrArg e
  apply eb.injective
  apply (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B).injective
  have heq := congrArg ek hvw
  have he' := congrArg (fun g ↦ g v) he
  have he'' := congrArg (fun g ↦ g w) he
  exact he'.symm.trans (heq.trans he'')

end GenericPullback

section DominantCurves

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

local notation "η" => genericPoint X
local notation "A" => Y.presheaf.stalk (f (genericPoint X))
local notation "B" => X.presheaf.stalk (genericPoint X)

private theorem isField_genericStalk {Z : Scheme.{u}} [IsIntegral Z] {z : Z}
    (hz : z = genericPoint Z) : IsField (Z.presheaf.stalk z) := by
  subst z
  exact Field.toIsField Z.functionField

private theorem isFunctionField_genericStalk {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [Z.IsCurveOver k] {z : Z} (hz : z = genericPoint Z) :
    let : Field (Z.presheaf.stalk z) := (isField_genericStalk hz).toField
    let : Algebra k (Z.presheaf.stalk z) := Scheme.stalkBaseAlgebra k Z z
    TauCeti.IsFunctionField k (Z.presheaf.stalk z) := by
  subst z
  have ha : Scheme.stalkBaseAlgebra k Z (genericPoint Z) = Scheme.functionFieldBaseAlgebra k Z := by
    apply Algebra.algebra_ext
    intro c
    change Scheme.baseRingToStalk k Z (genericPoint Z) c = Scheme.baseRingToFunctionField k Z c
    rw [Scheme.baseRingToStalk_apply, Scheme.baseRingToFunctionField_apply]
  dsimp only
  rw [ha]
  exact Scheme.IsCurveOver.isFunctionField (X := Z) (k := k)

set_option backward.isDefEq.respectTransparency false in
/-- A dominant morphism of curves in characteristic zero induces a formally
étale extension at the generic stalks. -/
theorem formallyEtale_genericStalk_of_dominant_curve [CharZero k]
    [X.IsCurveOver k] [Y.IsCurveOver k] [IsDominant f] :
    let _ : Algebra A B := algebraStalkMap f η
    Algebra.FormallyEtale A B := by
  let := algebraStalkMap f η
  let : Field A := (isField_genericStalk f.genericPoint_eq_of_isDominant).toField
  let : Field B := (isField_genericStalk (rfl : η = genericPoint X)).toField
  let : Algebra k A := Scheme.stalkBaseAlgebra k Y (f η)
  have hA := isFunctionField_genericStalk (k := k) f.genericPoint_eq_of_isDominant
  have hB := isFunctionField_genericStalk (k := k) (rfl : η = genericPoint X)
  let : Algebra k B := Scheme.stalkBaseAlgebra k X η
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap k f η c).symm
  let : FiniteDimensional A B := finiteDimensional_of_functionFields hA hB
  let : CharZero A := charZero_of_injective_algebraMap (algebraMap k A).injective
  exact Algebra.FormallyEtale.of_isSeparable A B

variable [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]

/-- For a dominant morphism of integral curves in characteristic zero, the first
map in the differential transitivity sequence is monic. -/
theorem differentialPullback_mono_of_dominant_curve [CharZero k]
    [X.IsCurveOver k] [Y.IsCurveOver k] [IsDominant f] :
    Mono (differentialPullback k f) :=
  differentialPullback_mono_of_formallyEtale_generic f
    (formallyEtale_genericStalk_of_dominant_curve (k := k) f)

/-- The differential transitivity sequence of a dominant morphism into a smooth integral curve
in characteristic zero is short exact. -/
theorem differentialTransitivity_shortExact [CharZero k] [X.IsCurveOver k] [Y.IsCurveOver k]
    [IsDominant f] : (differentialTransitivity k f).ShortExact := by
  let := differentialPullback_mono_of_dominant_curve (k := k) f
  exact differentialTransitivity_shortExact_of_mono k f

end DominantCurves

end TinyTauDemo
