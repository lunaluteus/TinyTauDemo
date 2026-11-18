/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The homogeneous Fermat equation

The Fermat polynomial on projective coordinates is homogeneous of the stated degree and has
no nonzero point where all partial derivatives vanish in characteristic zero.
See `/roadmap/index.qmd#prp-fermat-genus @ 043043ffcec6f4232273321a224bc7d77c9ec441`.
-/

namespace TinyTauDemo

open MvPolynomial

/-- The Fermat polynomial in homogeneous coordinates. -/
@[expose]
public noncomputable def fermatEquation (k : Type*) [CommRing k] (n : ℕ) :
    MvPolynomial (Fin 3) k :=
  X 0 ^ n + X 1 ^ n - X 2 ^ n

/-- The homogeneous Fermat equation as an expression in the three coordinates. -/
public theorem fermatEquation_def (k : Type*) [CommRing k] (n : ℕ) :
    fermatEquation k n = X 0 ^ n + X 1 ^ n - X 2 ^ n := rfl

/-- Every monomial of the Fermat polynomial has degree `n`. -/
public theorem fermatEquation_isHomogeneous (k : Type*) [CommRing k] (n : ℕ) :
    (fermatEquation k n).IsHomogeneous n :=
  ((isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)).sub (isHomogeneous_X_pow _ _)

/-- The Fermat polynomial has a nonzero partial derivative at every nonzero coordinate vector. -/
public theorem fermatEquation_exists_aeval_pderiv_ne_zero {k K : Type*} [CommRing k]
    [Field K] [CharZero K] [Algebra k K] {n : ℕ} (hn : 0 < n)
    (b : Fin 3 → K) (hb : b ≠ 0) :
    ∃ i, aeval b (pderiv i (fermatEquation k n)) ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra! h
    exact hb (funext h)
  refine ⟨i, ?_⟩
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  fin_cases i
  · change b 0 ≠ 0 at hi
    simp [fermatEquation, pderiv_X, hnK, hi]
  · change b 1 ≠ 0 at hi
    simp [fermatEquation, pderiv_X, hnK, hi]
  · change b 2 ≠ 0 at hi
    simp [fermatEquation, pderiv_X, hnK, hi]

/-- Evaluating the homogeneous polynomial gives the Fermat equation on the coordinates. -/
public theorem aeval_fermatEquation_eq_zero_iff_coordinates {k B : Type*}
    [CommRing k] [CommRing B] [Algebra k B] (n : ℕ) (p : Fin 3 → B) :
    aeval p (fermatEquation k n) = 0 ↔ p 0 ^ n + p 1 ^ n = p 2 ^ n := by
  simp [fermatEquation, sub_eq_zero]

/-- On the chart with third coordinate one, the Fermat equation is `xⁿ + yⁿ = 1`. -/
public theorem aeval_fermatEquation_eq_zero_iff {k K : Type*} [CommRing k] [CommRing K]
    [Algebra k K] (n : ℕ) (x y : K) :
    aeval ![x, y, 1] (fermatEquation k n) = 0 ↔ x ^ n + y ^ n = 1 := by
  simpa using aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n ![x, y, 1]

end TinyTauDemo
