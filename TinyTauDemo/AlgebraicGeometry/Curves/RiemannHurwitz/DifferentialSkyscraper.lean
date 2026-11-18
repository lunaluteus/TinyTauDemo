/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.CartierRamification
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import Mathlib.RingTheory.Etale.Field

/-!
# Relative differentials supported at the ramified closed points

The generic relative differential stalk vanishes by separability.
At closed points the relative differential length is the ramification index
minus one. The ramification divisor gives finite support, so the relative
sheaf is the product of the skyscraper sheaves of its ramified stalks.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `47de891dbad61dd2d022f66f89e9d847d1294027`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable {k : Type u} [Field k]

section Support

variable [CharZero k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]

local notation "η" => genericPoint X
local notation "A" => Y.presheaf.stalk (f (genericPoint X))
local notation "B" => X.presheaf.stalk (genericPoint X)

set_option backward.isDefEq.respectTransparency false in
/-- In characteristic zero the relative differential sheaf of a dominant curve
map vanishes at the generic point. -/
theorem subsingleton_morphismRelativeDifferentials_genericStalk :
    Subsingleton ((morphismRelativeDifferentials k f).presheaf.stalk η) := by
  let := algebraStalkMap f η
  have : Algebra.FormallyEtale A B := formallyEtale_genericStalk_of_dominant_curve (k := k) f
  have : Subsingleton (KaehlerDifferential A B) := inferInstance
  exact (morphismRelativeDifferentialsStalkEquiv k f η).injective.subsingleton

variable
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]

attribute [local instance] algebraStalkMap

set_option backward.isDefEq.respectTransparency false in
/-- A closed point supports relative differentials exactly when its
ramification index is greater than one. -/
theorem nontrivial_morphismRelativeDifferentials_stalk_iff (x : X) (hx : IsClosed {x}) :
    Nontrivial ((morphismRelativeDifferentials k f).presheaf.stalk x) ↔
      1 < (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
        (Y.presheaf.stalk (f x)) := by
  rw [← not_subsingleton_iff_nontrivial, ← Module.length_eq_zero_iff (R := X.presheaf.stalk x),
    length_morphismRelativeDifferentials_stalk_of_closed_smoothCurves (k := k) f x hx]
  norm_cast
  omega

set_option backward.isDefEq.respectTransparency false in
/-- A dominant smooth curve map has finitely many ramified closed points,
and the relative differential sheaf vanishes at all other points. -/
theorem finite_support_morphismRelativeDifferentials :
    ∃ s : Finset X,
      (∀ x, x ∈ s ↔ IsClosed {x} ∧
        1 < (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
          (Y.presheaf.stalk (f x))) ∧
      ∀ x ∉ s, Subsingleton ((morphismRelativeDifferentials k f).presheaf.stalk x) := by
  classical
  let := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  obtain ⟨D, _, _, hcoeff⟩ := exists_effectiveCartierRamificationDivisor (k := k) f
  let s := D.toWeilDivisor.support.image (Subtype.val : CodimensionOnePoint X → X)
  have hc (y : X) : Order.coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have hclosed (y : CodimensionOnePoint X) : IsClosed {(y : X)} :=
    TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hc y.property
  have hvan (x : X) (hx : x ∉ s) :
      Subsingleton ((morphismRelativeDifferentials k f).presheaf.stalk x) := by
    by_cases hgen : x = genericPoint X
    · subst x
      exact subsingleton_morphismRelativeDifferentials_genericStalk (k := k) f
    · let y : CodimensionOnePoint X :=
        ⟨x, (Scheme.coheight_eq_one_iff_ne_genericPoint
          (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le).mpr hgen⟩
      have hy : y ∉ D.toWeilDivisor.support := fun hy ↦ hx (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      have hz : WeilDivisor.coeff D.toWeilDivisor y = 0 := Finsupp.notMem_support_iff.mp hy
      have he := hcoeff y
      rw [hz] at he
      apply (Module.length_eq_zero_iff (R := X.presheaf.stalk x)).mp
      refine (length_morphismRelativeDifferentials_stalk_of_closed_smoothCurves
        (k := k) f x (hclosed y)).trans ?_
      exact_mod_cast he.symm
  refine ⟨s, fun x ↦ ⟨?_, ?_⟩, hvan⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨hclosed y, ?_⟩
    have hn : WeilDivisor.coeff D.toWeilDivisor y ≠ 0 := Finsupp.mem_support_iff.mp hy
    rw [hcoeff y] at hn
    have hn' : (IsLocalRing.maximalIdeal (X.presheaf.stalk (y : X))).ramificationIdx
        (Y.presheaf.stalk (f y)) - 1 ≠ 0 := by exact_mod_cast hn
    omega
  · rintro ⟨hx, hram⟩
    by_contra hn
    exact (not_subsingleton_iff_nontrivial.mpr
      ((nontrivial_morphismRelativeDifferentials_stalk_iff (k := k) f x hx).mpr hram))
      (hvan x hn)

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- The relative differential sheaf of a dominant morphism of smooth curves in
characteristic zero is the finite product of its stalk skyscrapers at the
ramified closed points. Its product projections are the canonical germ maps. -/
theorem morphismRelativeDifferentials_isSkyscraper :
    let M := morphismRelativeDifferentials k f
    ∃ s : Finset X,
      (∀ x, x ∈ s ↔ IsClosed {x} ∧
        1 < (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).ramificationIdx
          (Y.presheaf.stalk (f x))) ∧
      ∃ e : M ≅ ∏ᶜ fun z : s ↦ modulesStalkSkyscraper M (z : X),
        ∀ z : s, e.hom ≫ Pi.π _ z = modulesStalkSkyscraperProjection M (z : X) := by
  obtain ⟨s, hmem, hvan⟩ := finite_support_morphismRelativeDifferentials (k := k) f
  let M := morphismRelativeDifferentials k f
  have hc (x : X) (hx : x ∈ s) : IsClosed {x} := ((hmem x).mp hx).1
  let e := isoPiModulesStalkSkyscraper M s hvan hc
  exact ⟨s, hmem, e, fun z ↦ isoPiModulesStalkSkyscraper_hom_π M s hvan hc z⟩

end Support

end TinyTauDemo
