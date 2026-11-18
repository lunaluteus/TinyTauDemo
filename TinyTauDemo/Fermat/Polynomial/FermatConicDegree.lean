/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Polynomial.FermatProjectiveDegree
import Mathlib.Tactic.Ring

/-!
# The degree of the polynomial parametrization of the Fermat conic

The primitive Pythagorean coordinates have degree two and extend to a
morphism with function-field degree one.

See `/roadmap/index.qmd#rem-scheme-curves-recall` @ `908a59d4524abf373e750d7aa89b7fb264e01000`.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The usual polynomial coordinates on the projective Fermat conic. -/
noncomputable def pythagoreanCoordinates : Fin 3 → k[X] :=
  ![X ^ 2 - 1, 2 * X, X ^ 2 + 1]

omit [CharZero k] in
private theorem pythagoreanCoordinates_eval_eq_zero :
    MvPolynomial.aeval (pythagoreanCoordinates k) (fermatEquation k 2) = 0 := by
  rw [aeval_fermatEquation_eq_zero_iff_coordinates]
  change (X ^ 2 - 1 : k[X]) ^ 2 + (2 * X) ^ 2 = (X ^ 2 + 1) ^ 2
  ring

private theorem pythagoreanCoordinates_span :
    Ideal.span (Set.range (pythagoreanCoordinates k)) = ⊤ := by
  let I := Ideal.span (Set.range (pythagoreanCoordinates k))
  have hmem (i : Fin 3) : pythagoreanCoordinates k i ∈ I :=
    Ideal.subset_span ⟨i, rfl⟩
  have htwo : (2 : k[X]) ∈ I := by
    have h := I.sub_mem (hmem 2) (hmem 0)
    change (X ^ 2 + 1) - (X ^ 2 - 1) ∈ I at h
    convert h using 1
    ring
  refine I.eq_top_of_isUnit_mem htwo ?_
  have hC : C (2 : k) = (2 : k[X]) := map_ofNat C 2
  rw [← hC]
  exact (isUnit_iff_ne_zero.mpr (by norm_num : (2 : k) ≠ 0)).map C

private theorem pythagoreanCoordinates_max_degree :
    max (pythagoreanCoordinates k 0).natDegree
      (max (pythagoreanCoordinates k 1).natDegree (pythagoreanCoordinates k 2).natDegree) = 2 := by
  change max (X ^ 2 - 1 : k[X]).natDegree
    (max (2 * X : k[X]).natDegree (X ^ 2 + 1 : k[X]).natDegree) = 2
  have hl : (1 : k[X]).natDegree < (X ^ 2 : k[X]).natDegree := by simp
  rw [natDegree_sub_eq_left_of_natDegree_lt hl, natDegree_add_eq_left_of_natDegree_lt hl]
  simp

variable [IsAlgClosed k]

/-- The primitive Pythagorean coordinates have maximum degree two and define an
actual morphism to the Fermat conic with function-field degree one. -/
theorem pythagoreanCoordinates_projectiveLineMap_degree_one :
    let _ := fermatProjective_isIntegral k (by decide : 0 < 2)
    (max (pythagoreanCoordinates k 0).natDegree
      (max (pythagoreanCoordinates k 1).natDegree (pythagoreanCoordinates k 2).natDegree) = 2) ∧
    ∃ (hF : MvPolynomial.aeval (pythagoreanCoordinates k) (fermatEquation k 2) = 0)
      (hp : Ideal.span (Set.range (pythagoreanCoordinates k)) = ⊤)
      (f : projectiveLine k ⟶ fermatProjective k 2),
      f ≫ fermatProjectiveToSpec k 2 = (projectiveLine k ↘ Spec (.of k)) ∧
      projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap (pythagoreanCoordinates k) hF hp ∧
      ∃ _ : IsDominant f,
        let _ : Algebra (fermatProjective k 2).functionField (projectiveLine k).functionField :=
          f.functionFieldMap.hom.toAlgebra
        Module.finrank (fermatProjective k 2).functionField
          (projectiveLine k).functionField = 1 := by
  let hF := pythagoreanCoordinates_eval_eq_zero k
  let hp := pythagoreanCoordinates_span k
  have hM := pythagoreanCoordinates_max_degree k
  obtain ⟨f, ⟨hbase, hf⟩, -⟩ := existsUnique_fermatProjectiveLineMap _ hF hp
  have hM' : 0 < max (pythagoreanCoordinates k 0).natDegree
      (max (pythagoreanCoordinates k 1).natDegree (pythagoreanCoordinates k 2).natDegree) := by
    rw [hM]
    decide
  have hd := fermatProjectiveLineMap_degree_of_pos (by decide : 0 < 2)
    (x := pythagoreanCoordinates k 0) (y := pythagoreanCoordinates k 1)
    (z := pythagoreanCoordinates k 2) hF hp hM' f hf
  let := fermatProjective_isIntegral k (by decide : 0 < 2)
  dsimp only at hd ⊢
  obtain ⟨hD, hdegree⟩ := hd
  refine ⟨hM, hF, hp, f, hbase, hf, hD, ?_⟩
  omega

end TinyTauDemo
