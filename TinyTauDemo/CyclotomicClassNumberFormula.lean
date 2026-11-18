/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.CyclotomicBernoulliReduction
public import TinyTauDemo.CyclotomicOddEulerProduct
public import TinyTauDemo.CyclotomicResidueRatio
public import TinyTauDemo.DirichletOddFunctionalEquation
public import TinyTauDemo.RegularPrime
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# The relative class number formula and Bernoulli irregularity

The ratio of cyclotomic to real Dedekind-zeta residues is the product of the
odd L-values at one. Combine the odd functional equation with the explicit
class-number expression of the residue ratio to obtain the relative
class-number formula, up to sign, and the criterion for the norm kernel.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `19d05f674280fce4d59c513fd4da7aafdc84ca61`.
-/

public section

open NumberField Finset
open scoped Real ComplexConjugate

namespace TinyTauDemo

variable (K : Type*) [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ K]

private theorem sqrt_nat_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Real.sqrt_mul hx, ih, pow_succ']

/-- The relative class number formula for an odd prime conductor, in absolute value. -/
theorem cyclotomic_relative_classNumber_eq_norm_oddBernoulli (hp2 : 2 < p) :
    (2 : ℝ) ^ ((p - 3) / 2) * classNumber K =
      (classNumber (maximalRealSubfield K) : ℝ) * (p : ℝ) *
        ‖∏ χ ∈ oddDirichletCharacters p ℂ, χ.generalizedBernoulli 1‖ := by
  have hresidue := cyclotomic_dedekindZeta_residue_div_eq_prod_odd_LFunction (p := p) K
  let h : ℝ := classNumber K
  let r : ℝ := classNumber (maximalRealSubfield K)
  let B := ∏ χ ∈ oddDirichletCharacters p ℂ, χ.generalizedBernoulli 1
  let m := (p - 1) / 2
  let a := (p - 3) / 2
  let c : ℝ := (π / Real.sqrt p) ^ m
  have hq : 0 < c := by dsimp only [c]; positivity
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : 0 < r := by
    dsimp only [r]
    exact_mod_cast Nat.pos_of_ne_zero (classNumber_ne_zero (maximalRealSubfield K))
  have hc2 : (2 : ℝ) ^ m = 2 * 2 ^ a := by
    rw [show m = a + 1 by dsimp [m, a]; omega, pow_succ']
  have hc : (2 * π) ^ m / ((2 * p : ℝ) * Real.sqrt ((p : ℝ) ^ m)) =
      (2 : ℝ) ^ a / p * c := by
    rw [sqrt_nat_pow (Nat.cast_nonneg p), mul_pow, hc2]
    dsimp only [c]
    rw [div_pow]
    field_simp
  have hz : 0 ≤ dedekindZeta_residue K / dedekindZeta_residue (maximalRealSubfield K) := by
    rw [cyclotomic_dedekindZeta_residue_div_explicit (K := K) (p := p) (by omega)]
    positivity
  have hn := congrArg norm hresidue
  rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz,
    norm_prod_odd_dirichletLFunction_one hp2,
    cyclotomic_dedekindZeta_residue_div_explicit (K := K) (p := p) (by omega)] at hn
  change (2 * π) ^ m / ((2 * p : ℝ) * Real.sqrt ((p : ℝ) ^ m)) * (h / r) = c * ‖B‖ at hn
  rw [hc, mul_right_comm, mul_comm c] at hn
  have he := mul_right_cancel₀ hq.ne' hn
  change (2 : ℝ) ^ a * h = r * p * ‖B‖
  field_simp [hp.ne', hr.ne'] at he
  nlinarith only [he]

/-- The relative class number formula in complex coefficients with an unspecified sign. -/
theorem cyclotomic_relative_classNumber_eq_signed_oddBernoulli (hp2 : 2 < p) :
    ∃ b : ℕ, (2 : ℂ) ^ ((p - 3) / 2) * (classNumber K : ℂ) =
      (-1 : ℂ) ^ b * (classNumber (maximalRealSubfield K) : ℂ) * (p : ℂ) *
        ∏ χ ∈ oddDirichletCharacters p ℂ, χ.generalizedBernoulli 1 := by
  obtain ⟨r, hr⟩ := exists_real_oddBernoulli_product (p := p)
  have hn := cyclotomic_relative_classNumber_eq_norm_oddBernoulli K hp2
  rw [hr, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hr]
  rcases le_total 0 r with h | h
  · rw [abs_of_nonneg h] at hn
    refine ⟨0, ?_⟩
    have hnc := congrArg Complex.ofReal hn
    push_cast at hnc
    simpa only [pow_zero, one_mul] using hnc
  · rw [abs_of_nonpos h] at hn
    refine ⟨1, ?_⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg Complex.ofReal hn

/-- An odd conductor divides the relative norm kernel exactly when it is Bernoulli irregular. -/
theorem dvd_cyclotomicNormKernel_iff_bernoulliIrregular (hp2 : 2 < p) :
    p ∣ Nat.card (ClassGroup.relNorm (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker ↔
      BernoulliIrregular p := by
  have hp : p.Prime := Fact.out
  by_cases hp5 : 5 ≤ p
  · obtain ⟨b, hb⟩ := cyclotomic_relative_classNumber_eq_signed_oddBernoulli K hp2
    exact dvd_cyclotomicNormKernel_iff_bernoulliIrregular_of_complex_oddProduct_eq K hp5 hb
  · obtain ⟨j, hj⟩ := hp.odd_of_ne_two (by omega)
    have h3 : p = 3 := by omega
    clear hj j
    subst p
    have hnot : ¬ 3 ∣ classNumber K := by
      rw [classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid K)]
      decide
    refine iff_of_false (fun hd ↦ hnot
      ((dvd_cyclotomicClassNumber_iff_dvd_maximalRealSubfield_or_dvd_normKernel
        K hp (by decide)).mpr (Or.inr hd))) ?_
    rw [bernoulliIrregular_iff]
    rintro ⟨_, k, hk, hk', _⟩
    omega

/-- Divisibility of the full cyclotomic class number combines the real-subfield
class number and the Bernoulli criterion for the relative norm kernel. -/
theorem dvd_cyclotomicClassNumber_iff_dvd_real_or_bernoulliIrregular (hp2 : 2 < p) :
    p ∣ classNumber K ↔ p ∣ classNumber (maximalRealSubfield K) ∨ BernoulliIrregular p := by
  rw [dvd_cyclotomicClassNumber_iff_dvd_maximalRealSubfield_or_dvd_normKernel
      K (Fact.out : p.Prime) (by omega), dvd_cyclotomicNormKernel_iff_bernoulliIrregular K hp2]

/-- An odd prime is regular if its real class number is prime to it and it passes the
ordinary Bernoulli numerator test. -/
theorem regularPrime_iff_not_dvd_real_and_not_bernoulliIrregular {q : ℕ}
    (hq : q.Prime) (ho : Odd q) :
    RegularPrime q ↔ ¬ q ∣ classNumber (maximalRealSubfield (CyclotomicField q ℚ)) ∧
      ¬ BernoulliIrregular q := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  have h2 : 2 < q := by
    have := hq.two_le
    obtain ⟨j, hj⟩ := ho
    omega
  have hd := dvd_cyclotomicClassNumber_iff_dvd_real_or_bernoulliIrregular (CyclotomicField q ℚ) h2
  exact ⟨fun h ↦ not_or.mp (mt hd.mpr h.not_dvd_classNumber),
    fun h ↦ ⟨hq, ho, mt hd.mp (not_or.mpr h)⟩⟩

/-- A Bernoulli numerator in the irregularity range certifies divisibility of the
full prime cyclotomic class number. -/
theorem bernoulliIrregular_dvd_cyclotomicClassNumber {q : ℕ} (hq : BernoulliIrregular q) :
    q ∣ classNumber (CyclotomicField q ℚ) := by
  obtain ⟨hp, i, hi, hip, _⟩ := bernoulliIrregular_iff.mp hq
  let : Fact q.Prime := ⟨hp⟩
  let : NeZero q := ⟨hp.ne_zero⟩
  let : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) :=
    CyclotomicField.isCyclotomicExtension q ℚ
  exact (dvd_cyclotomicClassNumber_iff_dvd_real_or_bernoulliIrregular (CyclotomicField q ℚ)
    (by omega)).mpr (Or.inr hq)

/-- Infinitely many primes congruent to three modulo four divide their own cyclotomic
class numbers. -/
theorem infinite_irregularPrime_mod_four :
    {q : ℕ | q.Prime ∧ q % 4 = 3 ∧ q ∣ classNumber (CyclotomicField q ℚ)}.Infinite := by
  refine Set.Infinite.mono ?_ infinite_bernoulliIrregular_mod_four
  intro q h
  change BernoulliIrregular q ∧ q % 4 = 3 at h
  exact ⟨(bernoulliIrregular_iff.mp h.1).1, h.2, bernoulliIrregular_dvd_cyclotomicClassNumber h.1⟩

end TinyTauDemo
