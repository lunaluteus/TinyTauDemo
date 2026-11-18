/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatProjective
public import TinyTauDemo.Fermat.Curve.FermatAffineSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import TinyTauDemo.AlgebraicGeometry.Projective.PlaneJacobian
import Mathlib.FieldTheory.AlgebraicClosure
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Affine charts of the projective Fermat scheme

The charts and smoothness criterion for a general projective hypersurface
specialize to the Fermat equation.
See `/roadmap/index.qmd#prp-fermat-genus` @ `40dfab7e513657bb92e859b30e7ad8f1b8c18a2d`.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial TauCeti.GradedAlgebra
open HomogeneousLocalization

namespace TinyTauDemo

universe u

section Charts

variable (k : Type u) [Field k]

/-- Dehomogenization identifies the coordinate ring of each projective standard open with
the quotient by the corresponding affine Fermat equation. -/
noncomputable def fermatAwayEquivAffine {n : ℕ} (_hn : 0 < n) (i : Fin 3) :
    Away (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (X i)) ≃+*
      FermatAffineRing k n i :=
  ProjectiveHypersurface.awayEquivChart (fermatEquation_isHomogeneous k n) i

/-- The chart equivalence sends a homogeneous fraction to its dehomogenized numerator. -/
theorem fermatAwayEquivAffine_mk {n : ℕ} (hn : 0 < n) (i : Fin 3) (m : ℕ)
    (p : MvPolynomial (Fin 3) k) (hp : p.IsHomogeneous m) :
    fermatAwayEquivAffine k hn i (Away.mk (fermatGrading k n) (fermatCoord_mem_degree_one i) m
      (Ideal.Quotient.mk (fermatIdeal k n) p) (by
        simpa only [Nat.nsmul_eq_mul, mul_one] using
          mk_mem_quotientPiece (homogeneousSubmodule (Fin 3) k) (fermatIdeal k n) hp)) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize (R := k) i p) :=
  ProjectiveHypersurface.awayEquivChart_mk (fermatEquation_isHomogeneous k n) i m p hp

/-- Each coordinate basic open is the spectrum of the appropriate dehomogenized ring. -/
noncomputable def fermatBasicOpenIsoSpecAffine {n : ℕ} (_hn : 0 < n) (i : Fin 3) :
    (Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (X i))).toScheme ≅
      Spec (.of (FermatAffineRing k n i)) :=
  ProjectiveHypersurface.basicOpenIsoSpec (fermatEquation_isHomogeneous k n) i

/-- The map from the dehomogenized Fermat scheme to its projective closure. -/
noncomputable def fermatAffineChart {n : ℕ} (_hn : 0 < n) (i : Fin 3) :
    Spec (.of (FermatAffineRing k n i)) ⟶ fermatProjective k n :=
  ProjectiveHypersurface.affineChart (fermatEquation_isHomogeneous k n) i

/-- The affine chart inclusion factors through the homogeneous localization. -/
theorem fermatAffineChart_eq_awayι {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    fermatAffineChart k hn i = Spec.map
      (CommRingCat.ofHom (fermatAwayEquivAffine k hn i).toRingHom) ≫
      Proj.awayι (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (X i))
        (fermatCoord_mem_degree_one i) Nat.one_pos :=
  ProjectiveHypersurface.affineChart_eq_awayι (fermatEquation_isHomogeneous k n) i

instance {n : ℕ} (hn : 0 < n) (i : Fin 3) : IsOpenImmersion (fermatAffineChart k hn i) :=
  inferInstanceAs (IsOpenImmersion
    (ProjectiveHypersurface.affineChart (fermatEquation_isHomogeneous k n) i))

/-- The affine chart inclusion respects the structure maps to the coefficient field. -/
theorem fermatAffineChart_comp_toSpec {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    fermatAffineChart k hn i ≫ fermatProjectiveToSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k (FermatAffineRing k n i))) :=
  ProjectiveHypersurface.affineChart_comp_toSpec (fermatEquation_isHomogeneous k n) i

end Charts

variable (k : Type u) [Field k]

/-- A Fermat curve is smooth of relative dimension one over any field in which its degree
is nonzero. -/
theorem fermatProjective_smoothOne_of_natCast_ne_zero {n : ℕ}
    (hn : (n : k) ≠ 0) : SmoothOfRelativeDimension 1 (fermatProjectiveToSpec k n) := by
  let K := AlgebraicClosure k
  have hK : (n : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k K)]
    exact fun h ↦ hn ((algebraMap k K).injective (h.trans (map_zero _).symm))
  exact ProjectiveHypersurface.smoothOne_of_forall_exists_pderiv_ne_zero
    (K := K) (fermatEquation_isHomogeneous k n)
    (fun b hb _ ↦ fermatEquation_exists_aeval_pderiv_ne_zero_of_natCast_ne_zero hK b hb)

variable [CharZero k] [IsAlgClosed k]

/-- The projective Fermat scheme is smooth of relative dimension one for every positive exponent
over an algebraically closed field of characteristic zero. -/
theorem fermatProjective_smoothOne {n : ℕ} (hn : 0 < n) :
    SmoothOfRelativeDimension 1 (fermatProjectiveToSpec k n) :=
  ProjectiveHypersurface.smoothOne_of_forall_exists_pderiv_ne_zero
    (K := k) (fermatEquation_isHomogeneous k n)
    (fun b hb _ ↦ fermatEquation_exists_aeval_pderiv_ne_zero hn b hb)

end TinyTauDemo
