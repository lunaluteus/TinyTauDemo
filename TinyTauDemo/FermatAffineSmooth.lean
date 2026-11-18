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
import TinyTauDemo.PlaneJacobian

/-!
# Smoothness of the dehomogenized Fermat equations

The equation and the two partial derivatives generate the unit ideal on each
chart. The Jacobian criterion then gives relative dimension one and smoothness.
See `/roadmap/index.qmd#prp-fermat-genus` @ `acad2219963be552a5a2e3f90b6e76114117f1e6`.
-/

public section

open MvPolynomial

namespace TinyTauDemo

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
