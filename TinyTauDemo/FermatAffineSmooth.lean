/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatEquation
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.RingTheory.Smooth.Jacobian

/-!
# Smoothness of the dehomogenized Fermat equations

The equation and the two partial derivatives generate the unit ideal on each
chart. The Jacobian criterion then gives relative dimension one and smoothness.
See `/roadmap/index.qmd#prp-fermat-genus` @ `acad2219963be552a5a2e3f90b6e76114117f1e6`.
-/

public section

open MvPolynomial

namespace TinyTauDemo

section Algebra

variable {k : Type*} [CommRing k]

private theorem locally_standardSmoothOne_quotient_of_unit_gradient (f : MvPolynomial (Fin 2) k)
    (hf : Ideal.span (insert f (Set.range fun i => pderiv i f)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (MvPolynomial (Fin 2) k ⧸ (Ideal.span {f} : Ideal _))) := by
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
  have hqf : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hSpan : Ideal.span (Set.range fun i => q (pderiv i f)) = ⊤ := by
    have h := congrArg (Ideal.map q.toRingHom) hf
    rw [Ideal.map_top, Ideal.map_span, Set.image_insert_eq] at h
    change Ideal.span (insert (q f) (q '' Set.range fun i => pderiv i f)) = ⊤ at h
    rwa [hqf, Ideal.span_insert_zero, ← Set.range_comp] at h
  refine ⟨_, hSpan, ?_⟩
  rintro a ⟨i, rfl⟩
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

end Algebra

variable (k : Type*) [Field k] [CharZero k]

/-- The equation in the affine chart where coordinate i is normalized to one. -/
noncomputable abbrev fermatAffineEquation (n : ℕ) (i : Fin 3) : MvPolynomial (Fin 2) k :=
  TauCeti.dehomogenize (R := k) i (fermatEquation k n)

/-- The coordinate ring of the affine equation in the i-th standard chart. -/
noncomputable abbrev FermatAffineRing (n : ℕ) (i : Fin 3) :=
  MvPolynomial (Fin 2) k ⧸ (Ideal.span {fermatAffineEquation k n i} : Ideal _)

/-- Each dehomogenized Fermat equation defines a smooth affine curve of relative dimension one. -/
theorem fermatAffine_locally_standardSmoothOne {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap k (FermatAffineRing k n i)) := by
  apply locally_standardSmoothOne_quotient_of_unit_gradient
  apply TauCeti.span_insert_range_pderiv_dehomogenize_eq_top
    (K := AlgebraicClosure k) (fermatEquation_isHomogeneous k n)
  intro a _
  apply fermatEquation_exists_aeval_pderiv_ne_zero hn
  intro h
  have he := congrFun h i
  exact one_ne_zero (by simpa only [Fin.insertNth_apply_same, Pi.zero_apply] using he)

end TinyTauDemo
