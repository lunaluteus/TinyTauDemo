/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Orders of principal fractional ideals

Mathlib's multiplicative valuation is the exponential of the negative additive order.
See `/roadmap/index.qmd#rem-scheme-dedekind @ 74c76f14c420048048cf89f5ba74cdcd77806bd5`.
-/

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The height-one valuation of a nonzero element is the exponential of the negative
of the corresponding coefficient of its principal fractional ideal. -/
public theorem valuation_eq_exp_neg_count_spanSingleton (v : HeightOneSpectrum R)
    {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-count K v (spanSingleton R⁰ x)) := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ x
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.property
  have hr : r ≠ 0 := by
    rintro rfl
    simp [IsFractionRing.mk'_eq_div] at hx
  have hfrac : spanSingleton R⁰ (IsLocalization.mk' K r s) =
      spanSingleton R⁰ (algebraMap R K (s : R))⁻¹ *
        (↑(Ideal.span ({r} : Set R)) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, ← map_mul, IsFractionRing.mk'_eq_div,
      div_eq_inv_mul]
  rw [v.valuation_of_mk', v.intValuation_if_neg hr, v.intValuation_if_neg hs,
    count_well_defined K v (spanSingleton_ne_zero_iff.mpr hx) hfrac, ← WithZero.exp_sub]
  congr 1
  ring

end FractionalIdeal
