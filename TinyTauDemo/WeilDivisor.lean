/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Weil divisors of a Dedekind domain

The exponents of the height-one primes identify the group of nonzero fractional ideals with
the free abelian group on the height-one spectrum. The construction uses Mathlib's
`FractionalIdeal.finprod_heightOneSpectrum_factorization'`.
See `/roadmap/index.qmd#rem-scheme-dedekind @ 43a36e205c8b8491dce220ebef9160287330d502`.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

variable (R K : Type*) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The Weil divisor group isomorphism sends a nonzero fractional ideal to its prime exponents.
The exponent function has finite support by `FractionalIdeal.finite_factors`. -/
noncomputable def divisorMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) := by
  let exponents (I : (FractionalIdeal R⁰ K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
    Finsupp.ofSupportFinite (fun v ↦ count K v I)
      (Filter.eventually_cofinite.mp (finite_factors (I : FractionalIdeal R⁰ K)))
  refine MulEquiv.ofBijective
    ({ toFun := fun I ↦ Multiplicative.ofAdd (exponents I)
       map_one' := ?_
       map_mul' := ?_ } : (FractionalIdeal R⁰ K)ˣ →* _) ⟨?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    ext v
    exact count_one K v
  · intro I J
    apply Multiplicative.toAdd.injective
    ext v
    exact count_mul K v I.ne_zero J.ne_zero
  · intro I J h
    have hexp (v : HeightOneSpectrum R) :
        count K v I = count K v J :=
      DFunLike.congr_fun (Multiplicative.ofAdd.injective h) v
    apply Units.ext
    rw [← finprod_heightOneSpectrum_factorization' K I.ne_zero,
      ← finprod_heightOneSpectrum_factorization' K J.ne_zero]
    exact finprod_congr fun v ↦ congrArg _ (hexp v)
  · intro d
    let I : FractionalIdeal R⁰ K :=
      d.toAdd.prod fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n
    have hI : I ≠ 0 :=
      Finsupp.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
    refine ⟨Units.mk0 I hI, Multiplicative.toAdd.injective ?_⟩
    ext v
    exact count_finsuppProd K v d.toAdd

/-- The coefficient of a height-one prime is its exponent in the fractional ideal. -/
@[simp]
theorem divisorMulEquiv_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    (divisorMulEquiv R K I).toAdd v = count K v I := by
  unfold divisorMulEquiv
  rfl

end FractionalIdeal
