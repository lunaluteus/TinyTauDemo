/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Bernoulli.BernoulliIrregular
public import TinyTauDemo.NumberTheory.ClassFieldTheory.ClassNumberTransfer
public import TinyTauDemo.NumberTheory.Bernoulli.OddBernoulliTransport

/-!
# The Bernoulli test for the relative norm kernel

The complex odd-character class-number identity reduces the relative class-number
divisibility to the ordinary Bernoulli numerator test. The cokernel of the class
norm has order prime to the conductor, so the reduction only needs the size
of the kernel.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9c6724bb1701e787d07354e649919213e3c27e1a`.
-/

public section

open Finset NumberField

namespace TinyTauDemo

variable (K : Type*) [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ K]

/-- The complex relative class number formula up to sign gives the numerical
Bernoulli criterion for the norm kernel in an odd prime cyclotomic field. -/
theorem dvd_cyclotomicNormKernel_iff_bernoulliIrregular_of_complex_oddProduct_eq
    (hp5 : 5 ≤ p) {b : ℕ}
    (hformula : (2 : ℂ) ^ ((p - 3) / 2) * (classNumber K : ℂ) =
      (-1 : ℂ) ^ b * (classNumber (maximalRealSubfield K) : ℂ) * (p : ℂ) *
        ∏ ψ ∈ oddDirichletCharacters p ℂ, ψ.generalizedBernoulli 1) :
    p ∣ Nat.card (ClassGroup.relNorm (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker ↔
      BernoulliIrregular p := by
  let L := maximalRealSubfield K
  let N := ClassGroup.relNorm (R := 𝓞 L) (S := 𝓞 K)
  let d := N.range.index
  let n := Nat.card N.ker
  have hCM : IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, by omega⟩
  have hdeg : ¬ p ∣ Module.finrank L K := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  obtain ⟨hd, hn⟩ := classNumber_relNorm_index L K p (Fact.out : p.Prime) hdeg
  have hnc : (classNumber K : ℂ) * (d : ℂ) = (n : ℂ) * (classNumber L : ℂ) := by
    exact_mod_cast hn
  have hplus : (classNumber L : ℂ) ≠ 0 := by exact_mod_cast classNumber_ne_zero L
  have heq : (2 : ℂ) ^ ((p - 3) / 2) * (n : ℂ) =
      (-1 : ℂ) ^ b * (d : ℂ) * (p : ℂ) *
        ∏ ψ ∈ oddDirichletCharacters p ℂ, ψ.generalizedBernoulli 1 := by
    apply mul_right_cancel₀ hplus
    rw [mul_assoc, ← hnc, ← mul_assoc, hformula]
    ring
  rw [bernoulliIrregular_iff, and_iff_right (Fact.out : p.Prime)]
  exact dvd_iff_bernoulli_irregular_of_complex_oddProduct_eq hp5 hd heq

end TinyTauDemo
