/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.ClosedDifferentialLength
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Local orders for the ramification divisor

In local bases a morphism of line bundles is multiplication by a scalar.
The order of that scalar is the length of the stalk of its cokernel.
For differential pullback on smooth curves in characteristic zero, this order
is the ramification index minus one.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `82b6a524e4181b9a17b86406e8500becee53a4f0`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TinyTauDemo

universe u

set_option backward.isDefEq.respectTransparency false in
/-- At a point with chosen stalk bases, the cokernel length of a map of line
bundles is the order of the scalar describing the map. -/
theorem length_stalk_cokernel_eq_ord {X : Scheme.{u}} {L M : X.Modules} (φ : L ⟶ M) (x : X)
    (eL : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L.presheaf.stalk x)
    (eM : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] M.presheaf.stalk x) :
    Module.length (X.presheaf.stalk x) ((cokernel φ).presheaf.stalk x) =
      Ring.ord (X.presheaf.stalk x) (eM.symm ((modulesStalkFunctor x).map φ (eL 1))) := by
  let B := X.presheaf.stalk x
  let A := modulesStalkFunctor x
  let g := A.map φ
  let a := eM.symm (g (eL 1))
  let I : Ideal B := Ideal.span {a}
  let q : A.obj M ⟶ ModuleCat.of B (B ⧸ I) :=
    ModuleCat.ofHom ((I : Submodule B B).mkQ.comp eM.symm.toLinearMap)
  have hscal (r : B) : eM.symm (g (eL r)) = r * a := by
    conv_lhs => rw [← mul_one r]
    change eM.symm (g (eL (r • (1 : B)))) = r * a
    rw [map_smul, g.hom.map_smul, map_smul]
    rfl
  have hexact : Function.Exact g.hom q.hom := by
    intro m
    change (Ideal.Quotient.mk I) (eM.symm m) = 0 ↔ ∃ p, g p = m
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨eL r, eM.symm.injective ((hscal r).trans hr)⟩
    · rintro ⟨p, hp⟩
      obtain ⟨r, rfl⟩ := eL.surjective p
      exact ⟨r, (hscal r).symm.trans (congrArg eM.symm hp)⟩
  have hsurj : Function.Surjective q.hom :=
    (Ideal.Quotient.mk_surjective (I := I)).comp eM.symm.surjective
  let hq := ModuleCat.isColimitCokernelCofork g q hexact hsurj
  let hc := isColimitOfHasCokernelOfPreservesColimit A φ
  let E := (IsColimit.coconePointUniqueUpToIso hc hq).toLinearEquiv
  exact E.length_eq

section DifferentialCoefficient

open scoped TensorProduct

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f] (x : X)

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
set_option quotPrecheck false in
local notation "L" => (Scheme.Modules.pullback f).obj (Y.relativeDifferentials k)
set_option quotPrecheck false in
local notation "M" => X.relativeDifferentials k

attribute [local instance] algebraStalkMap

set_option backward.isDefEq.respectTransparency false in
/-- The local scalar of differential pullback, read in any trivializations on the two
stalks, has order equal to the ramification index minus one at a closed point. -/
theorem ord_differentialPullbackStalk_eq_ramificationIdx_sub_one
    (hx : IsClosed {x}) (eL : B ≃ₗ[B] (L).presheaf.stalk x)
    (eM : B ≃ₗ[B] (M).presheaf.stalk x) :
    Ring.ord B (eM.symm ((modulesStalkFunctor x).map (differentialPullback k f) (eL 1))) =
      ↑((IsLocalRing.maximalIdeal B).ramificationIdx A - 1 : ℕ) := by
  calc
    _ = Module.length B ((cokernel (differentialPullback k f)).presheaf.stalk x) :=
      (length_stalk_cokernel_eq_ord (differentialPullback k f) x eL eM).symm
    _ = Module.length B (KaehlerDifferential A B) :=
      (cokernelDifferentialPullbackStalkEquiv k f x).length_eq
    _ = Module.length B ((morphismRelativeDifferentials k f).presheaf.stalk x) :=
      (morphismRelativeDifferentialsStalkEquiv k f x).length_eq.symm
    _ = _ := length_morphismRelativeDifferentials_stalk_of_closed_smoothCurves f x hx

end DifferentialCoefficient

end TinyTauDemo
