/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Principal

/-!
# Nonconstant morphisms of proper curves

A morphism between proper integral curves over a field is proper. A dominant morphism has
finite fibres, hence is finite by Zariski's main theorem, and its closed dense image is the
entire target. A morphism with two distinct image points is dominant.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `f0a3b3dec25a0c6b0b6f61e1f6b1a5be8ffec3f1`.
-/

public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

section Points

variable (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [hX : X.IsCurveOver k]

include hX

private theorem isClosed_singleton_of_ne_genericPoint (x : X) (hx : x ≠ genericPoint X) :
    IsClosed {x} := by
  have hdim := (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  refine isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one (fun y ↦ ?_)
    ((Scheme.coheight_eq_one_iff_ne_genericPoint hdim).mpr hx)
  exact_mod_cast (coheight_le_topologicalKrullDim y).trans hdim

private theorem not_isClosed_singleton_genericPoint : ¬ IsClosed {genericPoint X} := by
  intro h
  have he := (genericPoint_spec X).def
  rw [h.closure_eq] at he
  have : Subsingleton X := Set.subsingleton_univ_iff.mp (he ▸ Set.subsingleton_singleton)
  have hdim := topologicalKrullDim_zero_of_discreteTopology X
  rw [Scheme.IsCurveOver.topologicalKrullDim_eq_one k] at hdim
  exact (not_le_of_gt zero_lt_one) hdim

private theorem finite_closed_of_genericPoint_not_mem {s : Set X} (hs : IsClosed s)
    (hη : genericPoint X ∉ s) : s.Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let U : X.Opens := ⟨sᶜ, hs.isOpen_compl⟩
  let : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  refine ((SchemeWeilDivisor.finite_setOfPred_not_mem U).image Subtype.val).subset ?_
  intro x hx
  have hdim := (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  have hxη : x ≠ genericPoint X := fun e ↦ hη (e ▸ hx)
  let z : CodimensionOnePoint X := ⟨x, (Scheme.coheight_eq_one_iff_ne_genericPoint hdim).mpr hxη⟩
  exact ⟨z, fun h ↦ h hx, rfl⟩

end Points

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [hX : X.IsCurveOver k] [hY : Y.IsCurveOver k]
    (f : X ⟶ Y) [hf : f.IsOver (Spec (.of k))]

include hX hY hf

/-- A morphism over a field between proper curves is proper. -/
theorem isProper_of_properCurveHom : IsProper f := by
  have : IsProper (f ≫ (Y ↘ Spec (.of k))) := by
    rw [comp_over f (Spec (.of k))]
    infer_instance
  exact IsProper.of_comp f (Y ↘ Spec (.of k))

variable [IsDominant f]

/-- The fibre of a dominant morphism of proper curves above any point is finite. -/
theorem finite_fibre_of_dominant_properCurveHom (y : Y) : (f ⁻¹' {y}).Finite := by
  have hproper := isProper_of_properCurveHom (k := k) f
  have hη := f.genericPoint_eq_of_isDominant
  by_cases hy : y = genericPoint Y
  · subst y
    refine (Set.finite_singleton (genericPoint X)).subset fun x hx ↦ ?_
    change f x = genericPoint Y at hx
    by_contra hxη
    have hclosed := f.isClosedMap _ (isClosed_singleton_of_ne_genericPoint k X x hxη)
    rw [Set.image_singleton, hx] at hclosed
    exact not_isClosed_singleton_genericPoint k Y hclosed
  · have hclosed := isClosed_singleton_of_ne_genericPoint k Y y hy
    exact finite_closed_of_genericPoint_not_mem k X (hclosed.preimage f.continuous)
      (fun h ↦ hy ((Set.mem_singleton_iff.mp h).symm.trans hη))

/-- A dominant morphism of proper curves is locally quasi-finite. -/
theorem locallyQuasiFinite_of_dominant_properCurveHom : LocallyQuasiFinite f := by
  have := isProper_of_properCurveHom (k := k) f
  exact LocallyQuasiFinite.of_finite_preimage_singleton f
    (finite_fibre_of_dominant_properCurveHom (k := k) f)

/-- A dominant morphism of proper curves is surjective. -/
theorem surjective_of_dominant_properCurveHom : Surjective f := by
  have := isProper_of_properCurveHom (k := k) f
  exact Surjective.of_universallyClosed_of_isDominant f

/-- A dominant morphism of proper curves is finite. -/
theorem isFinite_of_dominant_properCurveHom : IsFinite f := by
  have := isProper_of_properCurveHom (k := k) f
  have := locallyQuasiFinite_of_dominant_properCurveHom (k := k) f
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

omit [IsDominant f] in
/-- A morphism of proper curves with two distinct image points is finite and surjective. -/
theorem finite_and_surjective_of_nonconstant_properCurveHom
    (h : ∃ x y : X, f x ≠ f y) : IsFinite f ∧ Surjective f := by
  have hd : IsDominant f := by
    apply isDominant_iff_genericPoint_eq.mpr
    by_contra hη
    have hclosed := isClosed_singleton_of_ne_genericPoint k Y (f (genericPoint X)) hη
    have he (x : X) : f x = f (genericPoint X) :=
      Set.mem_singleton_iff.mp (((genericPoint_specializes x).map f.continuous).mem_closed
        hclosed (Set.mem_singleton _))
    obtain ⟨x, y, hxy⟩ := h
    exact hxy ((he x).trans (he y).symm)
  exact ⟨isFinite_of_dominant_properCurveHom (k := k) f,
    surjective_of_dominant_properCurveHom (k := k) f⟩

end TinyTauDemo
