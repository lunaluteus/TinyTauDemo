/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Projective.PlanePolynomialMap
public import TinyTauDemo.Fermat.Polynomial.FermatPolynomialMap

/-!
# Extending polynomial Fermat coordinates to the projective line

See `/roadmap/index.qmd#rem-scheme-curves-recall` @ `659046d7f13ad754bd0e36712b5fe02840fd1035`.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial
open TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- A polynomial-coordinate map on the affine chart extends uniquely to a morphism
from the projective line to the projective Fermat scheme. -/
theorem existsUnique_fermatProjectiveLineMap (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤) :
    ∃! f : projectiveLine k ⟶ fermatProjective k n,
      f ≫ fermatProjectiveToSpec k n = (projectiveLine k ↘ Spec (.of k)) ∧
        projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap p hF hp := by
  let : (fermatProjective k n).Over (Spec (.of k)) := ⟨fermatProjectiveToSpec k n⟩
  let : IsProper (fermatProjective k n ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (fermatProjectiveToSpec k n))
  exact existsUnique_projectiveLineMap_extending_polynomialChart k
    (fermatAffineMap p hF hp) (fermatAffineMap_toSpec p hF hp)

/-- A projective extension of the affine Fermat map has the reflected polynomials as
its coordinates on the chart at infinity. -/
theorem fermatProjectiveLineMap_on_infinity_chart (p : Fin 3 → k[X]) {M : ℕ}
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hmax : ∃ i, p i ≠ 0 ∧ (p i).natDegree = M)
    (f : projectiveLine k ⟶ fermatProjective k n)
    (hfS : f ≫ fermatProjectiveToSpec k n = (projectiveLine k ↘ Spec (.of k)))
    (hf : projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap p hF hp) :
    projectiveLinePolynomialChart k 1 ≫ f =
      fermatAffineMap (fun i ↦ (p i).reflect M)
        (aeval_reflect_eq_zero_of_isHomogeneous p (fermatEquation_isHomogeneous k n) hdeg hF)
        (span_range_reflect_eq_top p hp hdeg hmax) := by
  rw [fermatAffineMap_eq_specMap] at hf ⊢
  exact ProjectiveHypersurface.projectiveLineMap_on_infinity_chart
    (fermatEquation_isHomogeneous k n) p hF hp hdeg hmax f hfS hf

end TinyTauDemo
