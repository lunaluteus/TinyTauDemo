/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Orders of principal fractional ideals

Mathlib's multiplicative valuation is the exponential of the negative additive order.
The formula follows from Tau Ceti's `FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation`.
See `/roadmap/index.qmd#rem-scheme-dedekind @ 03c4debea0506c626cb05b3cca9d44b387a26cd7`.
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
  have h := count_toPrincipalIdeal_eq_neg_log_valuation K v (Units.mk0 x hx)
  rw [coe_toPrincipalIdeal, Units.val_mk0] at h
  rw [h, neg_neg, WithZero.exp_log ((v.valuation K).ne_zero_iff.mpr hx)]

end FractionalIdeal
