/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.RationalLogDerivative
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Polynomial.Radical

/-!
# Logarithmic differentiation of polynomials

Mathlib defines the universal Kähler derivation and identifies the Kähler differentials of
the polynomial algebra with the free module on the differential of `X`. We use polynomial
differentiation to express the logarithmic derivative of a split polynomial in terms of its
distinct roots and their multiplicities.
See `/roadmap/index.qmd#def-kahler-log-deriv @ 635eb9e5ecf5fa452a2ad4cdc26e365576f0ae7d`.
-/

public section

namespace Polynomial

open EuclideanDomain UniqueFactorizationMonoid

variable {k : Type*} [Field k]

open scoped Classical in
/-- Multiplying the logarithmic derivative by the radical gives a polynomial of degree
strictly less than the degree of that radical. -/
theorem exists_degree_lt_radical_logDerivative (p : k[X]) (hp : p ≠ 0) :
    ∃ q : k[X], q.degree < (radical p).degree ∧
      RatFunc.logDerivative (Additive.ofMul (Units.mk0 _ (RatFunc.algebraMap_ne_zero hp))) =
        algebraMap k[X] (RatFunc k) q / algebraMap k[X] (RatFunc k) (radical p) := by
  obtain ⟨q, hq⟩ := divRadical_dvd_derivative p
  have hdeg : (divRadical p).degree + (radical p).degree = p.degree := by
    rw [← degree_mul, divRadical_mul_radical]
  refine ⟨q, ?_, ?_⟩
  · have hder := degree_derivative_lt hp
    rw [hq, degree_mul, ← hdeg] at hder
    exact lt_of_add_lt_add_left hder
  · have hqp : algebraMap k[X] (RatFunc k) p.derivative =
        algebraMap k[X] (RatFunc k) (divRadical p) * algebraMap k[X] (RatFunc k) q := by
      rw [hq, map_mul]
    have hpf : algebraMap k[X] (RatFunc k) p =
        algebraMap k[X] (RatFunc k) (divRadical p) * algebraMap k[X] (RatFunc k) (radical p) := by
      rw [← map_mul, divRadical_mul_radical]
    rw [RatFunc.logDerivative_algebraMap p hp, hqp, hpf,
      mul_div_mul_left _ _ (RatFunc.algebraMap_ne_zero (divRadical_ne_zero hp))]

/-- For a polynomial written as a product of powers of linear factors, the logarithmic
derivative is the sum of the simple fractions with multiplicities as numerators. -/
private theorem logDerivative_eq_sum_of_eq_prod
    {p : k[X]} (hp : p ≠ 0) (s : Finset k) (e : k → ℕ) (c : k) (hc : c ≠ 0)
    (h : p = C c * ∏ a ∈ s, (X - C a) ^ e a) :
    RatFunc.logDerivative (Additive.ofMul (Units.mk0 _ (RatFunc.algebraMap_ne_zero hp))) =
      ∑ a ∈ s, (e a : RatFunc k) / algebraMap k[X] (RatFunc k) (X - C a) := by
  let uc : (RatFunc k)ˣ := Units.mk0 _ (RatFunc.algebraMap_ne_zero (C_ne_zero.mpr hc))
  let u : k → (RatFunc k)ˣ := fun a =>
    Units.mk0 _ (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
  have hp_rep : Units.mk0 _ (RatFunc.algebraMap_ne_zero hp) = uc * ∏ a ∈ s, u a ^ e a := by
    apply Units.ext
    simp [uc, u, h, map_prod, map_pow]
  have huc : RatFunc.logDerivative (Additive.ofMul uc) = 0 := by
    dsimp only [uc]
    rw [RatFunc.logDerivative_algebraMap _ (C_ne_zero.mpr hc), derivative_C, map_zero,
      _root_.zero_div]
  have hu (a : k) : RatFunc.logDerivative (Additive.ofMul (u a)) =
      (algebraMap k[X] (RatFunc k) (X - C a))⁻¹ := by
    dsimp only [u]
    rw [RatFunc.logDerivative_algebraMap _ (X_sub_C_ne_zero a), derivative_sub,
      derivative_X, derivative_C, sub_zero, map_one, one_div]
  rw [hp_rep, ofMul_mul, map_add, huc, zero_add, ofMul_prod, map_sum]
  simp only [ofMul_pow, map_nsmul, hu, nsmul_eq_mul, div_eq_mul_inv]

open scoped Classical in
/-- The radical of a nonzero split polynomial is the product of the linear factors at
its distinct roots. -/
theorem radical_eq_prod_roots_of_splits {p : k[X]} (hp : p ≠ 0) (hs : p.Splits) :
    radical p = ∏ a ∈ p.roots.toFinset, (X - C a) := by
  have hconst : IsUnit (C p.leadingCoeff) :=
    isUnit_C.mpr (leadingCoeff_ne_zero.mpr hp).isUnit
  conv_lhs => rw [hs.eq_prod_roots, radical_mul_of_isUnit_left hconst]
  have hirr : ∀ q ∈ p.roots.map (fun a ↦ X - C a), Irreducible q := by
    intro q hq
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hq
    exact irreducible_X_sub_C a
  have hnorm : normalize ∘ (fun a : k ↦ X - C a) = (fun a : k ↦ X - C a) :=
    _root_.funext fun a ↦ (monic_X_sub_C a).normalize_eq_self
  have hfactor : normalizedFactors (p.roots.map (fun a ↦ X - C a)).prod =
      p.roots.map (fun a ↦ X - C a) := by
    rw [normalizedFactors_prod_eq _ hirr, Multiset.map_map, hnorm]
  have himage : primeFactors (p.roots.map (fun a ↦ X - C a)).prod =
      p.roots.toFinset.image (fun a ↦ X - C a) := by
    ext q
    simp [mem_primeFactors, hfactor]
  rw [radical, himage]
  exact Finset.prod_image fun a _ b _ h ↦ C_inj.mp (sub_right_injective h)

open scoped Classical in
/-- The degree of the radical of a nonzero split polynomial counts its distinct roots. -/
theorem natDegree_radical_eq_card_roots_of_splits {p : k[X]} (hp : p ≠ 0) (hs : p.Splits) :
    (radical p).natDegree = p.roots.toFinset.card := by
  rw [radical_eq_prod_roots_of_splits hp hs, natDegree_finsetProd_X_sub_C_eq_card]

open scoped Classical in
/-- The logarithmic derivative of a nonzero split polynomial has one simple-fraction
term for each distinct root, with numerator equal to its multiplicity. -/
theorem logDerivative_eq_sum_roots_of_splits {p : k[X]} (hp : p ≠ 0) (hs : p.Splits) :
    RatFunc.logDerivative (Additive.ofMul (Units.mk0 _ (RatFunc.algebraMap_ne_zero hp))) =
      ∑ a ∈ p.roots.toFinset, (p.rootMultiplicity a : RatFunc k) /
        algebraMap k[X] (RatFunc k) (X - C a) := by
  apply logDerivative_eq_sum_of_eq_prod hp _ _ _ (leadingCoeff_ne_zero.mpr hp)
  exact hs.eq_prod_roots.trans (congrArg _ prod_multiset_root_eq_finset_root)

open scoped Classical in
/-- Clearing the radical denominator in the simple-fraction expansion gives the explicit
polynomial numerator obtained by omitting each root factor in turn. -/
theorem logDerivative_eq_radical_fraction_of_splits {p : k[X]} (hp : p ≠ 0) (hs : p.Splits) :
    RatFunc.logDerivative (Additive.ofMul (Units.mk0 _ (RatFunc.algebraMap_ne_zero hp))) =
      algebraMap k[X] (RatFunc k)
        (∑ a ∈ p.roots.toFinset, C (p.rootMultiplicity a : k) *
          ∏ b ∈ p.roots.toFinset.erase a, (X - C b)) /
        algebraMap k[X] (RatFunc k) (radical p) := by
  simp only [logDerivative_eq_sum_roots_of_splits hp hs, map_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [← div_eq_mul_inv]
  have hf : radical p = (X - C a) * (∏ b ∈ p.roots.toFinset.erase a, (X - C b)) := by
    rw [radical_eq_prod_roots_of_splits hp hs]
    exact (Finset.mul_prod_erase _ (fun b ↦ X - C b) ha).symm
  have hcast (n : ℕ) : algebraMap k[X] (RatFunc k) (C (n : k)) = (n : RatFunc k) := by
    simp only [map_natCast]
  rw [map_mul, hcast, hf, map_mul, mul_div_mul_right _ _
    (RatFunc.algebraMap_ne_zero (Finset.prod_ne_zero_iff.mpr fun b _ ↦ X_sub_C_ne_zero b))]

open scoped Classical in
/-- The explicit numerator of a split polynomial's logarithmic derivative has degree
strictly smaller than the radical denominator. -/
theorem logDerivative_numerator_degree_lt {p : k[X]} (hp : p ≠ 0) (hs : p.Splits) :
    (∑ b ∈ p.roots.toFinset, C (p.rootMultiplicity b : k) *
      ∏ t ∈ p.roots.toFinset.erase b, (X - C t)).degree < (radical p).degree := by
  obtain ⟨q, hdegree, hquotient⟩ := exists_degree_lt_radical_logDerivative p hp
  rw [logDerivative_eq_radical_fraction_of_splits hp hs] at hquotient
  have heq := RatFunc.algebraMap_injective k
    ((div_left_inj' (RatFunc.algebraMap_ne_zero radical_ne_zero)).mp hquotient)
  simpa only [heq] using hdegree

open scoped Classical in
/-- In characteristic zero the cleared numerator is nonzero at each root, so a root
factor cannot cancel from the radical denominator. -/
theorem logDerivative_numerator_eval_ne_zero [CharZero k] {p : k[X]} {a : k}
    (ha : a ∈ p.roots) :
    (∑ b ∈ p.roots.toFinset, C (p.rootMultiplicity b : k) *
      ∏ t ∈ p.roots.toFinset.erase b, (X - C t)).eval a ≠ 0 := by
  simp only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  have ha' : a ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ha
  rw [Finset.sum_eq_single_of_mem a ha']
  · apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt <| by
        rw [← count_roots]; exact Multiset.count_pos.mpr ha)
    · exact Finset.prod_ne_zero_iff.mpr fun _ ht ↦ sub_ne_zero.mpr (Finset.ne_of_mem_erase ht).symm
  · intro b _ hba
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hba.symm, ha'⟩) (sub_self a), mul_zero]

end Polynomial
