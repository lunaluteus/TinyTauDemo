/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatProjective
public import TinyTauDemo.AlgebraicGeometry.Projective.PlanePolynomialMap
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Morphisms defined by Fermat coordinates

A tuple of sections on an affine scheme gives a morphism to the projective Fermat
scheme when its entries generate the unit ideal and satisfy the equation.
The construction specializes the coordinate morphism of a projective hypersurface.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace TinyTauDemo

universe u

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B] {n : ℕ}

/-- Evaluate the homogeneous Fermat coordinate ring at the given tuple. -/
noncomputable def fermatCoordinateEval (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) : FermatCoordinateRing k n →ₐ[k] B :=
  ProjectiveHypersurface.coordinateEval p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF)

/-- Evaluation on a polynomial class agrees with evaluation of the polynomial. -/
@[simp]
theorem fermatCoordinateEval_mk (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (a : MvPolynomial (Fin 3) k) :
    fermatCoordinateEval (k := k) p hF (Ideal.Quotient.mk (fermatIdeal k n) a) =
      MvPolynomial.aeval p a :=
  ProjectiveHypersurface.coordinateEval_mk p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF) a

/-- A tuple generating the unit ideal defines a morphism from its spectrum to the Fermat scheme. -/
noncomputable def fermatSpecMap (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) : Spec (.of B) ⟶ fermatProjective k n :=
  ProjectiveHypersurface.specMap (fermatEquation_isHomogeneous k n) p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF) hp

/-- The Fermat construction is the hypersurface coordinate morphism. -/
theorem fermatSpecMap_eq_specMap (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) :
    fermatSpecMap (k := k) p hF hp =
      ProjectiveHypersurface.specMap (fermatEquation_isHomogeneous k n) p
        ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF) hp := by
  rfl

/-- The coordinate morphism commutes with the structure maps to the base. -/
@[reassoc]
theorem fermatSpecMap_toSpec (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) :
    fermatSpecMap (k := k) p hF hp ≫ fermatProjectiveToSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) :=
  ProjectiveHypersurface.specMap_toSpec (fermatEquation_isHomogeneous k n) p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF) hp

/-- When a coordinate is a unit, the morphism lands in its degree-one chart. -/
theorem fermatSpecMap_eq_awayLift
    (p : Fin 3 → B) (hpF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) (i : Fin 3) (hi : IsUnit (p i)) :
    fermatSpecMap (k := k) p hpF hp = Spec.map (CommRingCat.ofHom
      (Away.lift (fermatGrading k n) (fermatCoordinateEval (k := k) p hpF).toRingHom
        (f := Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i))
        (by
          change IsUnit
            (fermatCoordinateEval (k := k) p hpF (Ideal.Quotient.mk _ (MvPolynomial.X i)))
          rwa [fermatCoordinateEval_mk, MvPolynomial.aeval_X]))) ≫
      Proj.awayι (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i))
        (fermatCoord_mem_degree_one i) one_pos :=
  ProjectiveHypersurface.specMap_eq_awayLift (fermatEquation_isHomogeneous k n) p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hpF) hp i hi

/-- The inverse image of the coordinate chart is the basic open of that coordinate. -/
theorem fermatSpecMap_preimage_basicOpen (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤) (i : Fin 3) :
    fermatSpecMap (k := k) p hF hp ⁻¹ᵁ
      Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) =
        (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv (p i)) :=
  ProjectiveHypersurface.specMap_preimage_basicOpen (fermatEquation_isHomogeneous k n) p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF) hp i

/-- Rescaling all homogeneous coordinates by a common unit preserves the morphism. -/
theorem fermatSpecMap_eq_of_unit_rescale (p q : Fin 3 → B)
    (hFp : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤)
    (hFq : q 0 ^ n + q 1 ^ n = q 2 ^ n) (hq : Ideal.span (Set.range q) = ⊤)
    (c : Bˣ) (hc : ∀ i, q i = (c : B) * p i) :
    fermatSpecMap (k := k) p hFp hp = fermatSpecMap (k := k) q hFq hq :=
  ProjectiveHypersurface.specMap_eq_of_unit_rescale (fermatEquation_isHomogeneous k n) p q
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hFp) hp
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n q).mpr hFq) hq c hc

/-- Pulling the coordinate morphism back along an algebra homomorphism evaluates its coordinates. -/
theorem fermatSpecMap_comp_SpecMap {C : Type u} [CommRing C] [Algebra k C] (φ : B →ₐ[k] C)
    (p : Fin 3 → B) (hFp : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤)
    (hFq : φ (p 0) ^ n + φ (p 1) ^ n = φ (p 2) ^ n)
    (hq : Ideal.span (Set.range fun i ↦ φ (p i)) = ⊤) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fermatSpecMap (k := k) p hFp hp =
      fermatSpecMap (k := k) (fun i ↦ φ (p i)) hFq hq :=
  ProjectiveHypersurface.specMap_comp_SpecMap (fermatEquation_isHomogeneous k n) φ p
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hFp) hp
    ((aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n (fun i ↦ φ (p i))).mpr hFq) hq

end TinyTauDemo
