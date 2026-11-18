/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.NumberField.Index.Discriminant

/-!
# The index of an integral generator and its discriminant

The polynomial discriminant is related to the field discriminant by the square of the
cardinality of the additive quotient by the generated order. Casting this identity to
the rationals gives the discriminant of the rational power basis.
See `/roadmap/index.qmd#rem-ramification-disc-recall @ ac966279dffb3868e9777cbeb736cfbe55a73f63`.
-/

public section

namespace TauCeti.NumberField.IntegralPrimitiveElement

variable {K : Type*} [Field K] [NumberField K]

/-- The rational power-basis discriminant equals the field discriminant times the square
of the index, expressed as the cardinality of the additive quotient. -/
theorem discr_powerBasis_eq_card_quotient_sq_mul_discr (θ : IntegralPrimitiveElement K) :
    Algebra.discr ℚ θ.powerBasis.basis =
      (Nat.card θ.Quotient : ℚ) ^ 2 * (_root_.NumberField.discr K : ℚ) := by
  rw [θ.discr_powerBasis_eq_minpoly_discr, θ.discr_minpoly_eq_index_sq_mul_discr,
    θ.index_def]
  push_cast
  rfl

/-- The square of each divisor of the index divides the integral polynomial discriminant. -/
theorem sq_dvd_discr_minpoly_of_dvd_index (θ : IntegralPrimitiveElement K) {p : ℕ}
    (hp : p ∣ θ.index) : (p : ℤ) ^ 2 ∣ (minpoly ℤ θ.1).discr := by
  rw [θ.discr_minpoly_eq_index_sq_mul_discr]
  exact (pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr hp) 2).mul_right _

end TauCeti.NumberField.IntegralPrimitiveElement
