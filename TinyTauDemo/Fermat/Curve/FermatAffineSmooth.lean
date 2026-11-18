/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatEquation
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TinyTauDemo.AlgebraicGeometry.Projective.PlaneJacobian

/-!
# Smoothness of the dehomogenized Fermat equations

The equation and the two partial derivatives generate the unit ideal on each
chart. The Jacobian criterion then gives relative dimension one and smoothness.
See `/roadmap/index.qmd#prp-fermat-genus` @ `b2c9a29565e4747906e07cca00173aa6354b72f0`.
-/

public section

open MvPolynomial

namespace TinyTauDemo

variable (k : Type*) [Field k]

/-- The equation in the affine chart where coordinate i is normalized to one. -/
noncomputable abbrev fermatAffineEquation (n : ℕ) (i : Fin 3) : MvPolynomial (Fin 2) k :=
  TauCeti.dehomogenize (R := k) i (fermatEquation k n)

/-- The coordinate ring of the affine equation in the i-th standard chart. -/
noncomputable abbrev FermatAffineRing (n : ℕ) (i : Fin 3) :=
  MvPolynomial (Fin 2) k ⧸ (Ideal.span {fermatAffineEquation k n i} : Ideal _)

/-- The affine equation in the chart `Z = 1`. -/
theorem fermatAffineEquation_last (n : ℕ) :
    fermatAffineEquation k n 2 = X (0 : Fin 2) ^ n + X 1 ^ n - 1 := by
  have h0 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 0) = X 0 := by simp; rfl
  have h1 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 1) = X 1 := by simp; rfl
  have h2 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 2) = 1 := by simp
  change TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k n) = _
  simp only [fermatEquation_def, map_sub, map_add, map_pow, h0, h1, h2, one_pow]

section Evaluation

variable {k} {n : ℕ}

/-- Evaluate the coordinates on the last Fermat chart at an affine rational point. -/
noncomputable def fermatLastChartEval {a b : k} (h : a ^ n + b ^ n = 1) :
    FermatAffineRing k n 2 →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval ![a, b]) (by
    intro p hp
    obtain ⟨f, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp [fermatAffineEquation_last, h])

@[simp] theorem fermatLastChartEval_mk {a b : k} (h : a ^ n + b ^ n = 1)
    (p : MvPolynomial (Fin 2) k) :
    fermatLastChartEval h (Ideal.Quotient.mkₐ k _ p) = aeval ![a, b] p := by
  unfold fermatLastChartEval
  rfl

end Evaluation

variable [CharZero k]

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
