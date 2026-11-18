/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Dirichlet.DirichletLZero
public import TinyTauDemo.NumberTheory.Bernoulli.OddBernoulliTransport
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Absolute values in the odd Dirichlet functional equation

For an odd complex character of prime conductor, the Gauss sum has modulus
the square root of the conductor. The completed functional equation compares
the absolute value at one with the generalized Bernoulli value of the inverse
character at zero. Inversion permutes the odd characters.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `19d05f674280fce4d59c513fd4da7aafdc84ca61`.
-/

public section

open Complex Finset
open scoped Real ComplexConjugate

namespace TinyTauDemo

private theorem odd_ne_one {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) :
    χ ≠ 1 := by
  intro h
  rw [DirichletCharacter.Odd, h, MulChar.one_apply isUnit_one.neg] at hχ
  exact (by norm_num : (1 : ℂ) ≠ -1) hχ

private theorem odd_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) :
    χ⁻¹.Odd := by
  rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', hχ, inv_neg, inv_one]

private theorem conjugate_gaussSum_std {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) :
    conj (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar⁻¹ := by
  simp only [gaussSum, map_sum, map_mul]
  refine sum_congr rfl fun x _ ↦ congrArg₂ (· * ·) ?_ ?_
  · exact MulChar.star_apply' χ x
  · rw [AddChar.inv_apply, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
      ← Circle.coe_inv_eq_conj, ← AddChar.inv_apply, AddChar.inv_apply']

private theorem norm_gaussSum_std_of_ne_one {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt p := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p)
  rw [← conjugate_gaussSum_std, Complex.mul_conj, ZMod.card] at h
  have hsq := congrArg Complex.re h
  simp only [Complex.ofReal_re, Complex.natCast_re, Complex.normSq_eq_norm_sq] at hsq
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

private theorem norm_cpow_half_nat {p : ℕ} (hp : 0 < (p : ℝ)) :
    ‖(p : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt p := by
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp, Real.sqrt_eq_rpow]
  norm_num [Complex.div_ofNat_re]

private theorem norm_rootNumber_of_odd {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ.Odd) :
    ‖χ.rootNumber‖ = 1 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  simp only [DirichletCharacter.rootNumber, ite_eq_right hχ.not_even, pow_one, norm_div,
    Complex.norm_I, div_one, norm_gaussSum_std_of_ne_one (odd_ne_one hχ), norm_cpow_half_nat hp]
  exact div_self (Real.sqrt_pos.2 hp).ne'

private theorem gammaReal_two : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Gammaℝ_def, show -(2 : ℂ) / 2 = -1 by norm_num, Complex.cpow_neg_one,
    show (2 : ℂ) / 2 = 1 by norm_num, Complex.Gamma_one, mul_one]

/-- For an odd character of prime level, the functional equation relates the absolute value
at one to that of its inverse character's first generalized Bernoulli number. -/
theorem norm_dirichletLFunction_one_eq {p : ℕ} [Fact p.Prime]
    {χ : DirichletCharacter ℂ p} (hχ : χ.Odd) :
    ‖χ.LFunction 1‖ = (π / Real.sqrt p) * ‖χ⁻¹.generalizedBernoulli 1‖ := by
  have hprim : χ.IsPrimitive := (Nat.dvd_prime (Fact.out : p.Prime)).mp
    χ.conductor_dvd_level |>.resolve_left
      (fun h ↦ odd_ne_one hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  have hχi := odd_inv hχ
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hL₁ := χ.LFunction_eq_completed_div_gammaFactor 1 (Or.inl one_ne_zero)
  have hL₀ := χ⁻¹.LFunction_eq_completed_div_gammaFactor 0 (Or.inr hp1)
  rw [hχ.gammaFactor_def, show (1 : ℂ) + 1 = 2 by norm_num, gammaReal_two] at hL₁
  rw [hχi.gammaFactor_def, zero_add, Gammaℝ_one, div_one,
    dirichletLFunction_zero_eq_neg_generalizedBernoulli (odd_ne_one hχi)] at hL₀
  have he := hprim.completedLFunction_one_sub 0
  rw [sub_zero, zero_sub, Complex.cpow_neg, ← hL₀] at he
  rw [hL₁, he, norm_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    norm_mul, norm_mul, norm_neg, norm_inv, norm_cpow_half_nat hp, norm_rootNumber_of_odd hχ,
    mul_one, div_inv_eq_mul]
  ring

/-- Exactly half of the complex characters modulo an odd prime are odd. -/
theorem card_oddDirichletCharacters_complex {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    (oddDirichletCharacters p ℂ).card = (p - 1) / 2 := by
  classical
  let := Fintype.ofFinite (DirichletCharacter ℂ p)
  let S := oddDirichletCharacters p ℂ
  let T := (univ : Finset (DirichletCharacter ℂ p)).filter (fun χ ↦ ¬χ.Odd)
  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have hzero : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = 1 + 1 := by norm_num
        _ = -1 + 1 := by rw [h]
        _ = 0 := neg_add_cancel 1
    have := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hp2) this
  obtain ⟨ψ, hψ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod p) ℂ hneg
  let χ₀ : DirichletCharacter ℂ p := ψ
  have hodd : χ₀.Odd := χ₀.even_or_odd.resolve_left hψ
  have htoggle (χ : DirichletCharacter ℂ p) : (χ₀ * χ : DirichletCharacter ℂ p).Odd ↔ ¬χ.Odd := by
    change χ₀ (-1) * χ (-1) = -1 ↔ _
    rw [hodd, neg_one_mul, neg_inj]
    exact ⟨fun h ↦ (show χ.Even from h).not_odd, fun h ↦ χ.even_or_odd.resolve_right h⟩
  have hcard : T.card = S.card := by
    refine card_bij (fun χ _ ↦ χ₀ * χ) ?_ ?_ ?_
    · intro χ hχ
      exact mem_oddDirichletCharacters.mpr ((htoggle χ).mpr (mem_filter.mp hχ).2)
    · exact fun a _ b _ hab ↦ mul_left_cancel hab
    · intro χ hχ
      let a := χ₀⁻¹ * χ
      have ha : χ₀ * a = χ := by simp [a]
      refine ⟨a, mem_filter.mpr ⟨mem_univ _, (htoggle a).mp ?_⟩, ha⟩
      rw [ha]
      exact mem_oddDirichletCharacters.mp hχ
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (DirichletCharacter ℂ p)))
    DirichletCharacter.Odd
  have hfilter : (univ : Finset (DirichletCharacter ℂ p)).filter DirichletCharacter.Odd = S := by
    ext χ
    simp [S]
  have hfull : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (MulChar.mulEquiv_units (ZMod p) ℂ).some.toEquiv,
      Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hfilter, show ({a ∈ (univ : Finset (DirichletCharacter ℂ p)) | ¬a.Odd}) = T from rfl,
    hcard, card_univ, hfull] at hsum
  change S.card = _
  omega

/-- The first generalized Bernoulli numbers of all odd characters have a real product. -/
theorem exists_real_oddBernoulli_product {p : ℕ} [Fact p.Prime] :
    ∃ r : ℝ, (∏ χ ∈ oddDirichletCharacters p ℂ, χ.generalizedBernoulli 1) = (r : ℂ) := by
  apply Complex.conj_eq_iff_real.mp
  have hn := (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'
  exact map_prod_oddDirichletCharacters_generalizedBernoulli
    (Complex.conjAe.restrictScalars ℚ).toAlgHom (Complex.isPrimitiveRoot_exp (p - 1) hn)

/-- The product of the odd values at one has an explicit absolute value in terms of the
full odd generalized Bernoulli product. -/
theorem norm_prod_odd_dirichletLFunction_one {p : ℕ} [Fact p.Prime] (hp2 : 2 < p) :
    ‖∏ χ ∈ oddDirichletCharacters p ℂ, χ.LFunction 1‖ =
      (π / Real.sqrt p) ^ ((p - 1) / 2) *
        ‖∏ χ ∈ oddDirichletCharacters p ℂ, χ.generalizedBernoulli 1‖ := by
  classical
  let S := oddDirichletCharacters p ℂ
  rw [norm_prod, norm_prod]
  calc
    _ = ∏ χ ∈ S, (π / Real.sqrt p) * ‖χ⁻¹.generalizedBernoulli 1‖ := by
      exact prod_congr rfl fun χ hχ ↦
        norm_dirichletLFunction_one_eq (mem_oddDirichletCharacters.mp hχ)
    _ = _ := by
      rw [prod_mul_distrib, prod_const, card_oddDirichletCharacters_complex hp2]
      congr 1
      apply prod_bij (fun χ _ ↦ χ⁻¹)
      · exact fun χ hχ ↦
          mem_oddDirichletCharacters.mpr (odd_inv (mem_oddDirichletCharacters.mp hχ))
      · exact fun a _ b _ hab ↦ inv_injective hab
      · exact fun χ hχ ↦ ⟨χ⁻¹, mem_oddDirichletCharacters.mpr
          (odd_inv (mem_oddDirichletCharacters.mp hχ)), inv_inv χ⟩
      · intros
        rfl

end TinyTauDemo
