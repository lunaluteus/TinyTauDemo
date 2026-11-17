/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.Polynomial.Radical
import Mathlib.NumberTheory.FLT.MasonStothers

/-!
# Mason–Stothers in characteristic zero

Mathlib's `Polynomial.abc` gives either the degree bound or zero derivatives. In
characteristic zero, the nonconstant hypothesis excludes the second case.
For `a + b = c`, coprimality of `a` and `b` implies pairwise coprimality.
See `/roadmap/index.qmd#thm-mason-stothers @ 5fcc91096c22183372a667d09b61a33cf8734ceb`.
-/

namespace Polynomial

open UniqueFactorizationMonoid

open scoped Classical in
/-- Over a field of characteristic zero, the maximal degree in a nonconstant coprime
sum is strictly less than the degree of the radical of the product. -/
public theorem masonStothers {k : Type*} [Field k] [CharZero k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (hsum : a + b = c)
    (hnonconstant : 0 < max a.natDegree (max b.natDegree c.natDegree)) :
    max a.natDegree (max b.natDegree c.natDegree) + 1 ≤ (radical (a * b * c)).natDegree := by
  classical
  have hzero : a + b + (-c) = 0 := by rw [hsum, add_neg_cancel]
  rcases Polynomial.abc ha hb (neg_ne_zero.mpr hc) hab hzero with ⟨h₁, h₂, h₃⟩ | h
  · simp only [mul_neg, UniqueFactorizationDomain.radical_neg, natDegree_neg] at h₁ h₂ h₃
    omega
  · rw [derivative_neg, neg_eq_zero] at h
    simp only [derivative_eq_zero] at h
    simp [h.1, h.2.1, h.2.2] at hnonconstant

end Polynomial
