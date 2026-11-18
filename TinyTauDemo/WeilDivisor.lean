/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Group.Equiv.TypeTags
import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Basic

/-!
# Weil divisors of a Dedekind domain

The exponents of the height-one primes identify the group of nonzero fractional ideals with
the free abelian group on the height-one spectrum. We express Tau Ceti's
`WeilDivisor.fractionalIdealDivisorAddEquiv` using the multiplicative group of ideals.
See `/roadmap/index.qmd#rem-scheme-dedekind @ 03c4debea0506c626cb05b3cca9d44b387a26cd7`.
-/

public section

open IsDedekindDomain
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors

namespace FractionalIdeal

variable (R K : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The Weil divisor group isomorphism sends a nonzero fractional ideal to its prime exponents.
The exponent function has finite support by `FractionalIdeal.finite_factors`. -/
noncomputable def divisorMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  AddEquiv.toMultiplicativeRight
    (TauCeti.AlgebraicGeometry.WeilDivisor.fractionalIdealDivisorAddEquiv R K)

/-- The coefficient of a height-one prime is its exponent in the fractional ideal. -/
@[simp]
theorem divisorMulEquiv_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    (divisorMulEquiv R K I).toAdd v = count K v I := by
  -- Remove the multiplicative tags to apply the coefficient formula.
  change coeff (fractionalIdealDivisorAddEquiv R K (Additive.ofMul I)) v = count K v I
  simpa only [fractionalIdealDivisorAddEquiv_apply, toMul_ofMul] using
    coeff_fractionalIdealDivisor R K (Additive.ofMul I) v

end FractionalIdeal
