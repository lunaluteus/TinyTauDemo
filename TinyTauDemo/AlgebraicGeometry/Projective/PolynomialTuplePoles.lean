/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.RatFunc

/-!
# Common pole divisor of projective polynomial coordinates

See `/roadmap/index.qmd#rem-scheme-curves-recall @ 0ce794f8b09e1d3bf189ed3c18dd9c1894d2a4a7`.
-/

public section

open Polynomial TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

variable {k : Type*} [Field k]

/-- The poles of a rational function, with the zero function assigned the zero divisor. -/
noncomputable def rationalPoleDivisor (r : RatFunc k) : Divisor k (RatFunc k) := by
  classical
  exact if h : r = 0 then 0 else Divisor.poles (IsFunctionField.ratFunc k) (Units.mk0 r h)

/-- The coefficient of the rational pole divisor is the negative part of the order. -/
theorem rationalPoleDivisor_coeff (r : RatFunc k) (P : Place k (RatFunc k)) :
    (rationalPoleDivisor r).coeff P = max (-P.ord r) 0 := by
  classical
  by_cases h : r = 0
  · subst r
    simp [rationalPoleDivisor]
  · rw [rationalPoleDivisor, dite_eq_right h, Divisor.coeff_poles, Units.val_mk0]

/-- The pole divisor agrees with Tau Ceti's pole divisor on units. -/
theorem rationalPoleDivisor_coe_unit (r : (RatFunc k)ˣ) :
    rationalPoleDivisor (r : RatFunc k) = Divisor.poles (IsFunctionField.ratFunc k) r := by
  rw [rationalPoleDivisor, dite_eq_right r.ne_zero]
  congr
  exact Units.ext rfl

/-- The ratio of two coordinate polynomials in the rational function field. -/
noncomputable abbrev polynomialRatio (p q : k[X]) : RatFunc k :=
  algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q

private theorem coeff_rationalPoleDivisor_ratio_infty (x z : k[X]) (hz : z ≠ 0) :
    (rationalPoleDivisor (polynomialRatio x z)).coeff (Place.infty k) =
      max ((x.natDegree : ℤ) - z.natDegree) 0 := by
  rw [rationalPoleDivisor_coeff]
  by_cases hx : x = 0
  · subst x
    simp only [polynomialRatio, map_zero, zero_div, Place.ord_zero, neg_zero, max_self,
      natDegree_zero, Nat.cast_zero, zero_sub]
    omega
  · rw [Place.ord_infty, neg_neg, RatFunc.intDegree_div
      (RatFunc.algebraMap_ne_zero hx) (RatFunc.algebraMap_ne_zero hz),
      RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]

private theorem coeff_rationalPoleDivisor_ratio_adic_le
    {q : k[X]} (hq : Irreducible q) (x z : k[X]) (hz : z ≠ 0) :
    (rationalPoleDivisor (polynomialRatio x z)).coeff (Place.adicOfIrreducible hq) ≤
      (multiplicity q z : ℤ) := by
  rw [rationalPoleDivisor_coeff]
  by_cases hx : x = 0
  · subst x
    simp [polynomialRatio]
  · rw [(Place.adicOfIrreducible hq).ord_div (RatFunc.algebraMap_ne_zero hx)
      (RatFunc.algebraMap_ne_zero hz),
      Place.ord_adicOfIrreducible_algebraMap hq hx,
      Place.ord_adicOfIrreducible_algebraMap hq hz]
    omega

private theorem coeff_rationalPoleDivisor_ratio_adic_of_not_dvd
    {q x z : k[X]} (hq : Irreducible q) (hx : ¬ q ∣ x) (hz : z ≠ 0) :
    (rationalPoleDivisor (polynomialRatio x z)).coeff (Place.adicOfIrreducible hq) =
      (multiplicity q z : ℤ) := by
  have hx₀ : x ≠ 0 := fun he ↦ hx (he ▸ dvd_zero q)
  rw [rationalPoleDivisor_coeff,
    (Place.adicOfIrreducible hq).ord_div (RatFunc.algebraMap_ne_zero hx₀)
      (RatFunc.algebraMap_ne_zero hz),
    Place.ord_adicOfIrreducible_algebraMap hq hx₀,
    Place.ord_adicOfIrreducible_algebraMap hq hz, multiplicity_eq_zero_of_not_dvd hx]
  omega

private theorem coeff_rationalPoleDivisor_nonneg (r : RatFunc k) (P : Place k (RatFunc k)) :
    0 ≤ (rationalPoleDivisor r).coeff P := by
  rw [rationalPoleDivisor_coeff]
  exact le_max_right _ _

/-- For polynomial coordinates generating the unit ideal, the common pole divisor of the
two ratios is the zero divisor of the denominator, plus the residual pole at infinity. -/
theorem rationalPoleDivisor_ratio_sup {x y z : k[X]}
    (hspan : Ideal.span ({x, y, z} : Set k[X]) = ⊤) (hz : z ≠ 0) :
    rationalPoleDivisor (polynomialRatio x z) ⊔ rationalPoleDivisor (polynomialRatio y z) =
      Divisor.zeros (IsFunctionField.ratFunc k)
        (Units.mk0 (algebraMap k[X] (RatFunc k) z) (RatFunc.algebraMap_ne_zero hz)) +
        ((max x.natDegree (max y.natDegree z.natDegree) : ℤ) - z.natDegree) •
          WeilDivisor.ofPoint (Place.infty k) := by
  refine WeilDivisor.ext fun P ↦ ?_
  rw [WeilDivisor.coeff_sup, WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul,
    Divisor.coeff_zeros, Units.val_mk0]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible P with rfl | ⟨q, hq, rfl⟩
  · rw [coeff_rationalPoleDivisor_ratio_infty _ _ hz,
      coeff_rationalPoleDivisor_ratio_infty _ _ hz, WeilDivisor.coeff_ofPoint_self,
      Place.ord_infty, RatFunc.intDegree_polynomial]
    omega
  · rw [WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq), mul_zero, add_zero,
      Place.ord_adicOfIrreducible_algebraMap hq hz]
    have hmul : max (multiplicity q z : ℤ) 0 = multiplicity q z := max_eq_left (by positivity)
    change max _ _ = max (multiplicity q z : ℤ) 0
    rw [hmul]
    have hxl := coeff_rationalPoleDivisor_ratio_adic_le hq x z hz
    have hyl := coeff_rationalPoleDivisor_ratio_adic_le hq y z hz
    refine le_antisymm (max_le hxl hyl) ?_
    by_cases hqz : q ∣ z
    · have hxy : ¬ q ∣ x ∨ ¬ q ∣ y := by
        by_contra! h
        apply hq.not_isUnit
        apply Ideal.span_singleton_eq_top.mp
        apply top_unique
        rw [← hspan]
        apply Ideal.span_le.mpr
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact Ideal.mem_span_singleton.mpr h.1
        · exact Ideal.mem_span_singleton.mpr h.2
        · exact Ideal.mem_span_singleton.mpr hqz
      rcases hxy with hqx | hqy
      · rw [coeff_rationalPoleDivisor_ratio_adic_of_not_dvd hq hqx hz]
        exact le_max_left _ _
      · rw [coeff_rationalPoleDivisor_ratio_adic_of_not_dvd hq hqy hz]
        exact le_max_right _ _
    · rw [multiplicity_eq_zero_of_not_dvd hqz, Nat.cast_zero]
      exact (coeff_rationalPoleDivisor_nonneg _ _).trans (le_max_left _ _)

/-- The degree of the common pole divisor is the maximum coordinate degree. -/
theorem rationalPoleDivisor_ratio_sup_degree {x y z : k[X]}
    (hspan : Ideal.span ({x, y, z} : Set k[X]) = ⊤) (hz : z ≠ 0) :
    Divisor.degree (rationalPoleDivisor (polynomialRatio x z) ⊔
      rationalPoleDivisor (polynomialRatio y z)) =
        max x.natDegree (max y.natDegree z.natDegree) := by
  rw [rationalPoleDivisor_ratio_sup hspan hz, Divisor.degree_add, Divisor.degree_zsmul,
    Divisor.degree_ofPoint, Place.degree_infty, Divisor.degree_zeros_algebraMap hz]
  push_cast
  omega

end TinyTauDemo
