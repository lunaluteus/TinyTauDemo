/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
public import TauCeti.FieldTheory.FunctionField.Differential.RatFunc.Basic

/-!
# Tame Riemann–Hurwitz and finite fibres

Over algebraically closed constants of characteristic zero, each place has degree one
and its contribution to the different is its ramification index minus one.
See `/roadmap/index.qmd#thm-riemann-hurwitz-recall @ 1c4dad461408b9adac6d5698769a2b616a9cc434`.
-/

public section

open TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

section FibreIdentity

variable {k F L : Type*} [Field k] [IsAlgClosed k]
  [Field F] [Field L] [Algebra k F] [Algebra k L] [Algebra F L]
  [IsScalarTower k F L] [FiniteDimensional F L]

/-- Over algebraically closed constants, the total excess ramification in the
fibres of a finite set is the degree of its conorm minus the size of its support. -/
theorem sum_ramification_excess_above_finset (hF : IsFunctionField k F) (hL : IsFunctionField k L)
    (s : Finset (Place k F)) :
    let D := Divisor.conorm k L (WeilDivisor.ofFinset s)
    ∑ P ∈ D.support, ((Place.ramificationIdx F P : ℤ) - 1) =
      Module.finrank F L * s.card - (D.support.card : ℤ) := by
  classical
  let D := Divisor.conorm k L (WeilDivisor.ofFinset s)
  -- Use the conorm named in the statement for the calculation of its support.
  change ∑ P ∈ D.support, ((Place.ramificationIdx F P : ℤ) - 1) =
    Module.finrank F L * s.card - (D.support.card : ℤ)
  have hdegree : Divisor.degree D = (Module.finrank F L : ℤ) * s.card := by
    unfold D
    rw [Divisor.degree_conorm_of_finrank_eq_one k L hF (Module.finrank_self k),
      Divisor.degree_eq_weilDivisorDegree_of_isAlgClosed hF, WeilDivisor.degree_ofFinset]
  rw [Divisor.degree_apply_of_isAlgClosed hL] at hdegree
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← hdegree]
  congr 1
  refine Finset.sum_congr rfl fun P hP ↦ ?_
  have hr : P.restrict k F ∈ s := by
    simpa only [D, Divisor.mem_support_conorm_iff, WeilDivisor.support_ofFinset] using hP
  change _ = WeilDivisor.coeff D P
  simp [D, hr, WeilDivisor.coeff_ofFinset]

end FibreIdentity

variable {k F L : Type*} [Field k] [IsAlgClosed k] [CharZero k]
  [Field F] [Field L] [Algebra k F] [Algebra k L] [Algebra F L]
  [IsScalarTower k F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]

private theorem hurwitz_tame_degree
    (hF : IsFunctionField k F) (hL : IsFunctionField k L) :
    2 * (genus k L : ℤ) - 2 =
      Module.finrank F L * (2 * (genus k F : ℤ) - 2) +
        Divisor.degree (Divisor.tameDifferent k L hF) := by
  rw [← geometricDegree_eq_finrank F k L]
  exact (two_mul_genus_sub_two_eq_iff_forall_isTame hF hL
    isIntegrallyClosedIn_of_isAlgClosed isIntegrallyClosedIn_of_isAlgClosed).2
      fun P ↦ Place.isTame_of_charZero k F P

/-- In characteristic zero the canonical divisor of the pulled-back differential is the
conorm of its divisor plus the tame different, whose coefficient at each place is `e - 1`. -/
theorem weilDifferentialDivisor_cotrace_eq_conorm_add_tameDifferent
    (hF : IsFunctionField k F) (hL : IsFunctionField k L)
    (ω : weilDifferentialSpace k F) (hω : ω ≠ 0) :
    weilDifferentialDivisor hL isIntegrallyClosedIn_of_isAlgClosed
        (weilDifferentialCotrace k L hF hL ω).2
        (fun h ↦ hω ((weilDifferentialCotrace_eq_zero_iff hF hL).mp
          ((ZeroMemClass.coe_eq_zero (x := weilDifferentialCotrace k L hF hL ω)).mp h))) =
      Divisor.conorm k L (weilDifferentialDivisor hF isIntegrallyClosedIn_of_isAlgClosed
        ω.2 (mt (ZeroMemClass.coe_eq_zero (x := ω)).mp hω)) +
        Divisor.tameDifferent k L hF := by
  rw [weilDifferentialDivisor_weilDifferentialCotrace hF hL
    isIntegrallyClosedIn_of_isAlgClosed isIntegrallyClosedIn_of_isAlgClosed ω hω]
  congr 1
  exact ((Divisor.tameDifferent_eq_different_iff k L hF).2
    fun P ↦ Place.isTame_of_charZero k F P).symm

/-- Over algebraically closed constants of characteristic zero, the ramification
term of Riemann–Hurwitz is the sum of the excess ramification indices. -/
theorem hurwitz_genus_formula_of_isAlgClosed
    (hF : IsFunctionField k F) (hL : IsFunctionField k L) :
    2 * (genus k L : ℤ) - 2 =
      Module.finrank F L * (2 * (genus k F : ℤ) - 2) +
        ∑ P ∈ (Divisor.tameDifferent k L hF).support, ((Place.ramificationIdx F P : ℤ) - 1) := by
  rw [hurwitz_tame_degree hF hL, Divisor.degree_apply_of_isAlgClosed hL]
  congr 1
  exact Finset.sum_congr rfl fun _ _ ↦ Divisor.coeff_tameDifferent k L hF _

/-- A genus-zero cover of degree `d` has at least `s * d - (2 * d - 2)` distinct
places above any finite set of `s` places. -/
theorem card_places_above_lower_bound_of_genus_zero
    (hF : IsFunctionField k F) (hL : IsFunctionField k L)
    (hgenusF : genus k F = 0) (hgenusL : genus k L = 0) (s : Finset (Place k F)) :
    (s.card : ℤ) * Module.finrank F L - (2 * Module.finrank F L - 2) ≤
      ((Divisor.conorm k L (WeilDivisor.ofFinset s)).support.card : ℤ) := by
  classical
  let D : Divisor k L := Divisor.conorm k L (WeilDivisor.ofFinset s)
  have hbound : D - WeilDivisor.ofFinset D.support ≤ Divisor.tameDifferent k L hF := by
    refine WeilDivisor.le_iff.mpr fun P ↦ ?_
    have hp : P ∈ D.support ↔ P.restrict k F ∈ s := by
      simp only [D, Divisor.mem_support_conorm_iff, WeilDivisor.support_ofFinset]
    rw [WeilDivisor.coeff_sub, WeilDivisor.coeff_ofFinset, Divisor.coeff_tameDifferent]
    by_cases hP : P ∈ D.support
    · have hr := hp.mp hP
      simp [D, hP, hr, WeilDivisor.coeff_ofFinset]
    · have hzero := not_ne_iff.mp fun hn ↦ hP (WeilDivisor.mem_support_iff.mpr hn)
      rw [hzero, ite_eq_right hP, sub_zero, sub_nonneg]
      exact_mod_cast Place.ramificationIdx_pos F P
  have hdegrees := Divisor.degree_le_of_le hbound
  have hdegreeD : Divisor.degree D = (Module.finrank F L : ℤ) * s.card := by
    unfold D
    rw [Divisor.degree_conorm_of_finrank_eq_one k L hF (Module.finrank_self k),
      Divisor.degree_eq_weilDivisorDegree_of_isAlgClosed hF, WeilDivisor.degree_ofFinset]
  have hDsupport : Divisor.degree (WeilDivisor.ofFinset D.support : Divisor k L) =
      (D.support.card : ℤ) := by
    rw [Divisor.degree_eq_weilDivisorDegree_of_isAlgClosed hL, WeilDivisor.degree_ofFinset]
  rw [map_sub, hdegreeD, hDsupport] at hdegrees
  have hh := hurwitz_tame_degree hF hL
  rw [hgenusF, hgenusL] at hh
  -- The divisor support used in the coefficient estimate is the fibre union in the statement.
  change _ ≤ (D.support.card : ℤ)
  rw [mul_comm (s.card : ℤ)]
  omega

end TinyTauDemo
