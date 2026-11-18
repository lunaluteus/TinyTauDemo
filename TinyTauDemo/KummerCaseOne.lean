/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.RegularPrime
import FltRegular.CaseI.Statement

/-!
# Kummer's first case

`FltRegular.caseI` proves the regular-prime obstruction in the difference form of the equation.
Oddness turns it into the symmetric equation.
See `/roadmap/index.qmd#thm-kummer-case-1 @ e8f2c6a0a00069e58360c6b66ef94656c5a6de6f`.
-/

namespace TinyTauDemo

/-- The symmetric Fermat equation at a regular prime has no integer solutions whose
coordinate product is coprime to the exponent. -/
public theorem kummer_case_I {p : ℕ} (hr : RegularPrime p) {x y z : ℤ}
    (hndvd : ¬ (p : ℤ) ∣ x * y * z) : x ^ p + y ^ p + z ^ p ≠ 0 := by
  intro h
  have : Fact p.Prime := ⟨hr.prime⟩
  refine FltRegular.caseI (a := x) (b := y) (c := -z) hr.coprime_classNumber ?_ ?_
  · simpa only [mul_neg, dvd_neg] using hndvd
  · simpa only [hr.odd.neg_pow] using eq_neg_of_add_eq_zero_left h

end TinyTauDemo
