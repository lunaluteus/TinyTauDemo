/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.Coprime.Basic

/-!
# Primitive Fermat solutions

This module defines the primitive triples common to the integer and polynomial Fermat equations.
See `/roadmap/index.qmd#def-primitive-solution @ e8657a4ef437e8f0f5e42d5e79b3f71aed4adc7f`.
-/

namespace TinyTauDemo

/-- A solution of `x ^ n + y ^ n = z ^ n` with nonzero, pairwise coprime coordinates,
at least one of which is a nonunit. The definition uses Mathlib's Bézout coprimality
and applies independently of the exponent bounds in individual theorems. -/
public structure PrimitiveFermatSolution {R : Type*} [CommRing R] (n : ℕ) (x y z : R) : Prop where
  eq : x ^ n + y ^ n = z ^ n
  coprime_xy : IsCoprime x y
  coprime_yz : IsCoprime y z
  coprime_zx : IsCoprime z x
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  z_ne_zero : z ≠ 0
  not_all_units : ¬ (IsUnit x ∧ IsUnit y ∧ IsUnit z)

/-- A primitive solution in a domain has nonzero coordinate product. -/
public theorem PrimitiveFermatSolution.xyz_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} {x y z : R} (h : PrimitiveFermatSolution n x y z) : x * y * z ≠ 0 :=
  mul_ne_zero (mul_ne_zero h.x_ne_zero h.y_ne_zero) h.z_ne_zero

end TinyTauDemo
