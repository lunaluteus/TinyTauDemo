/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.ProjectiveHypersurface
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TauCeti.RingTheory.Smooth.Jacobian

/-!
# The forward Jacobian criterion for projective plane hypersurfaces

The affine criterion generalizes the presentation proof for the Fermat charts.
It uses Tau Ceti's smoothness criterion after inverting a Jacobian minor.
See `/roadmap/index.qmd#rem-scheme-curves-recall @ ce3fed2d7209ae176aaa251ce23f48d13fd004d5`.
-/

public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace TinyTauDemo

universe u

section Affine

variable {k : Type u} [CommRing k]

/-- A two-variable hypersurface is standard smooth of relative dimension one on the
basic open where either of its partial derivatives is invertible. -/
theorem standardSmoothOne_quotient_localizationAway_pderiv (f : MvPolynomial (Fin 2) k)
    (i : Fin 2) :
    RingHom.IsStandardSmoothOfRelativeDimension 1
      (algebraMap k (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))) := by
  let I : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {f}
  let A := MvPolynomial (Fin 2) k ⧸ I
  let q : MvPolynomial (Fin 2) k →ₐ[k] A := Ideal.Quotient.mkₐ k I
  let G : Algebra.Generators k A (Fin 2) :=
    Algebra.Generators.ofAlgHom q (Ideal.Quotient.mkₐ_surjective k I)
  have hG : G.ker = I := by
    rw [Algebra.Generators.ker_ofAlgHom]
    exact Ideal.Quotient.mkₐ_ker k I
  let P (i : Fin 2) : Algebra.PreSubmersivePresentation k A (Fin 2) (Fin 1) :=
    { toPresentation :=
        { toGenerators := G
          relation := fun _ => f
          span_range_relation_eq_ker := by
            rw [hG, Set.range_const] }
      map := fun _ => i
      map_inj := fun x y _ => Subsingleton.elim x y }
  have hP (i : Fin 2) : (P i).jacobian = q (pderiv i f) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_one,
      Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
      Algebra.Generators.algebraMap_apply]
    change aeval (q ∘ X) (pderiv i f) = _
    rw [show aeval (q ∘ X) = q by ext; simp]
  let T := Localization.Away (q (pderiv i f))
  have : IsLocalization.Away (P i).jacobian T := by
    rw [hP]
    exact inferInstanceAs
      (IsLocalization.Away (q (pderiv i f)) (Localization.Away (q (pderiv i f))))
  have hDim := (P i).isStandardSmoothOfRelativeDimension_localizationAway T
  have hd : (P i).dimension = 1 := by simp [Algebra.Presentation.dimension]
  rw [hd] at hDim
  change (algebraMap k T).IsStandardSmoothOfRelativeDimension 1
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr hDim

/-- A two-variable hypersurface whose equation and partials generate the unit ideal is
locally standard smooth of relative dimension one. -/
theorem locally_standardSmoothOne_quotient_of_unit_gradient (f : MvPolynomial (Fin 2) k)
    (hf : Ideal.span (insert f (Set.range fun i => pderiv i f)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (MvPolynomial (Fin 2) k ⧸ (Ideal.span {f} : Ideal _))) := by
  let q := Ideal.Quotient.mk (Ideal.span {f})
  have hqf : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hSpan : Ideal.span (Set.range fun i => q (pderiv i f)) = ⊤ := by
    have h := congrArg (Ideal.map q) hf
    rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq] at h
    change Ideal.span (insert (q f) (q '' Set.range fun i => pderiv i f)) = ⊤ at h
    rwa [hqf, Ideal.span_insert_zero, ← Set.range_comp] at h
  refine ⟨_, hSpan, ?_⟩
  rintro a ⟨i, rfl⟩
  exact standardSmoothOne_quotient_localizationAway_pderiv f i

end Affine

namespace ProjectiveHypersurface

variable {k : Type u} [Field k] {d : ℕ} {F : MvPolynomial (Fin 3) k}
  (hF : F.IsHomogeneous d)

private theorem insertNth_one_ne_zero {K : Type*} [Field K] (i : Fin 3) (a : Fin 2 → K) :
    i.insertNth (α := fun _ ↦ K) (1 : K) a ≠ 0 := by
  intro h
  have hcoord := congrFun h i
  exact one_ne_zero ((Fin.insertNth_apply_same (α := fun _ ↦ K) i (1 : K) a).symm.trans hcoord)

/-- If the gradient is nonzero at every projective zero over an algebraically closed
extension, the plane hypersurface is smooth of relative dimension one. -/
theorem smoothOne_of_forall_exists_pderiv_ne_zero {K : Type*} [Field K] [Algebra k K]
    [IsAlgClosed K]
    (hJac : ∀ b : Fin 3 → K, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0) :
    SmoothOfRelativeDimension 1 (toSpec hF) := by
  let f : Proj (grading hF) ⟶ Spec (.of k) := toSpec hF
  let U (i : Fin 3) := Proj.basicOpen (grading hF) (coord F i)
  let 𝒰 := (Proj (grading hF)).openCoverOfIsOpenCover U
    (TopologicalSpace.IsOpenCover.mk (iSup_basicOpen_eq_top hF))
  have hAffine (i : 𝒰.I₀) : IsAffine (𝒰.X i) :=
    Proj.isAffineOpen_basicOpen (grading hF) (coord F i) (coord_mem_degree_one hF i) Nat.one_pos
  have hprop : HasRingHomProperty (@SmoothOfRelativeDimension.{u} 1)
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)) := inferInstance
  change SmoothOfRelativeDimension 1 f
  refine HasRingHomProperty.of_source_openCover 𝒰 fun i ↦ ?_
  apply HasRingHomProperty.appTop (@SmoothOfRelativeDimension 1)
  change SmoothOfRelativeDimension 1 ((U i).ι ≫ f)
  let e := basicOpenIsoSpec hF i
  have hc : affineChart hF i ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing F i))) :=
    affineChart_comp_toSpec hF i
  have hs : SmoothOfRelativeDimension 1 (affineChart hF i ≫ f) := by
    rw [hc]
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
    apply locally_standardSmoothOne_quotient_of_unit_gradient
    apply TauCeti.span_insert_range_pderiv_dehomogenize_eq_top (K := K) hF
    intro a ha
    exact hJac _ (insertNth_one_ne_zero i a) ha
  have hcomp := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension 1)
    e.hom _ hs
  have he := basicOpenIsoSpec_hom_affineChart hF i
  change e.hom ≫ affineChart hF i = (U i).ι at he
  rwa [← Category.assoc, he] at hcomp

end ProjectiveHypersurface

end TinyTauDemo
