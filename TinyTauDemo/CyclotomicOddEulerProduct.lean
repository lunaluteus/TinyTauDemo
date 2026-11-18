/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.CyclotomicEulerProduct
public import TinyTauDemo.CyclotomicRealPrimeFactors
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TinyTauDemo.OddBernoulliTransport
import Mathlib.NumberTheory.MulChar.Duality

/-!
# The odd Dirichlet product for a cyclotomic zeta quotient

The ratio of the Dedekind zeta functions of a prime cyclotomic field and
its maximal real subfield is the product over the odd characters. Its
right limit at one gives the ratio of the residues.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `19d05f674280fce4d59c513fd4da7aafdc84ca61`.
-/

public section

open Filter NumberField
open scoped BigOperators NumberField Topology

namespace TinyTauDemo

section Residue

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]

/-- On the real axis, the ratio of two Dedekind zeta functions tends from the right
to the ratio of their residues at one. -/
theorem tendsto_dedekindZeta_div_nhdsGT :
    Tendsto (fun s : ℝ ↦ dedekindZeta K s / dedekindZeta L s) (𝓝[>] (1 : ℝ))
      (𝓝 ((dedekindZeta_residue K : ℂ) / dedekindZeta_residue L)) := by
  have hn : (dedekindZeta_residue L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero L)
  apply ((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).div
    (tendsto_sub_one_mul_dedekindZeta_nhdsGT L) hn).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 1 < s at hs
  have hne : (s : ℂ) - 1 ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hs.ne')
  exact mul_div_mul_left _ _ hne

/-- A finite factorization of a Dedekind-zeta quotient by odd Dirichlet series on the
real interval above one gives the corresponding residue identity at one. -/
theorem dedekindZeta_residue_div_eq_prod_odd_LFunction_of_factorization {p : ℕ} [NeZero p]
    (S : Finset (DirichletCharacter ℂ p)) (hS : ∀ χ ∈ S, χ.Odd)
    (hEuler : ∀ s : ℝ, 1 < s →
      dedekindZeta K s / dedekindZeta L s = ∏ χ ∈ S, LSeries (χ ·) (s : ℂ)) :
    (dedekindZeta_residue K : ℂ) / dedekindZeta_residue L =
      ∏ χ ∈ S, χ.LFunction 1 := by
  have hprod : Tendsto (fun s : ℝ ↦ ∏ χ ∈ S, χ.LFunction (s : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (∏ χ ∈ S, χ.LFunction 1)) := by
    apply tendsto_finsetProd
    intro χ hχ
    have hn : χ ≠ 1 := by
      intro he
      have hh := hS χ hχ
      rw [DirichletCharacter.Odd, he, MulChar.one_apply (isUnit_one.neg)] at hh
      exact (by norm_num : (1 : ℂ) ≠ -1) hh
    have hc : ContinuousAt χ.LFunction 1 :=
      (χ.differentiableAt_LFunction 1 (Or.inr hn)).continuousAt
    exact hc.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)
  refine tendsto_nhds_unique_of_eventuallyEq (tendsto_dedekindZeta_div_nhdsGT K L) hprod ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 1 < s at hs
  rw [hEuler s hs]
  apply Finset.prod_congr rfl
  intro χ _
  exact (χ.LFunction_eq_LSeries (by simpa only [Complex.ofReal_re] using hs)).symm

end Residue

private theorem finprod_even_mul_prod_odd {m : ℕ} [Fact m.Prime] (f : DirichletCharacter ℂ m → ℂ) :
    (∏ᶠ χ : {χ : DirichletCharacter ℂ m // χ.Even}, f χ.val) *
      (∏ χ ∈ oddDirichletCharacters m ℂ, f χ) = ∏ᶠ χ : DirichletCharacter ℂ m, f χ := by
  let E := {χ : DirichletCharacter ℂ m | χ.Even}
  let O := {χ : DirichletCharacter ℂ m | χ.Odd}
  have hdisj : Disjoint E O := Set.disjoint_left.mpr (fun χ hE hO ↦ χ.not_even_and_odd ⟨hE, hO⟩)
  have hcover : E ∪ O = Set.univ := Set.eq_univ_of_forall (fun χ ↦ χ.even_or_odd)
  have hO : O.toFinite.toFinset = oddDirichletCharacters m ℂ := by
    ext χ
    simp [O]
  rw [← hO]
  change (∏ᶠ χ : E, f χ.val) * (∏ χ ∈ O.toFinite.toFinset, f χ) =
    ∏ᶠ χ, f χ
  rw [finprod_set_coe_eq_finprod_mem, ← finprod_mem_univ f, ← hcover,
    finprod_mem_union hdisj E.toFinite O.toFinite, finprod_mem_eq_finite_toFinset_prod f O.toFinite]

variable (K : Type*) [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ K]

/-- The quotient of the cyclotomic and real-subfield local Euler factors consists of
the odd Dirichlet factors. At the conductor, the two Dedekind factors coincide. -/
theorem cyclotomic_dedekindLocalFactor_eq_real_mul_prod_odd (q : Nat.Primes) (s : ℂ) :
    dedekindLocalFactor K q s = dedekindLocalFactor (maximalRealSubfield K) q s *
      ∏ χ ∈ oddDirichletCharacters p ℂ, (1 - χ (q : ℕ) * (q : ℂ) ^ (-s))⁻¹ := by
  by_cases h : (q : ℕ) = p
  · obtain rfl : q = (⟨p, hp.out⟩ : Nat.Primes) := Subtype.ext h
    rw [cyclotomic_real_dedekindLocalFactor_conductor K]
    change _ = _ * ∏ χ ∈ oddDirichletCharacters p ℂ, (1 - χ (p : ℕ) * (p : ℂ) ^ (-s))⁻¹
    simp only [ZMod.natCast_self, MulChar.map_zero, zero_mul, sub_zero, inv_one,
      Finset.prod_const_one, mul_one]
  · rw [cyclotomic_dedekindLocalFactor_eq_prod_dirichletCharacter K q h,
      cyclotomic_real_dedekindLocalFactor_eq_prod_even K q h]
    exact (finprod_even_mul_prod_odd (m := p) (fun χ ↦ (1 - χ (q : ℕ) * (q : ℂ) ^ (-s))⁻¹)).symm

/-- In the absolutely convergent half-plane, the cyclotomic Dedekind zeta function
divided by that of its maximal real subfield is the product of the odd Dirichlet series. -/
theorem cyclotomic_dedekindZeta_div_eq_prod_odd {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s / dedekindZeta (maximalRealSubfield K) s =
      ∏ χ ∈ oddDirichletCharacters p ℂ, LSeries (χ ·) s :=
  dedekindZeta_div_eq_prod_dirichlet_of_localFactors K (maximalRealSubfield K)
    (oddDirichletCharacters p ℂ) hs
    (fun q ↦ cyclotomic_dedekindLocalFactor_eq_real_mul_prod_odd K q s)

/-- The cyclotomic-to-real ratio of residues at one equals the product of the odd
Dirichlet L-values at one. -/
theorem cyclotomic_dedekindZeta_residue_div_eq_prod_odd_LFunction :
    (dedekindZeta_residue K : ℂ) / dedekindZeta_residue (maximalRealSubfield K) =
      ∏ χ ∈ oddDirichletCharacters p ℂ, χ.LFunction 1 :=
  dedekindZeta_residue_div_eq_prod_odd_LFunction_of_factorization K (maximalRealSubfield K)
    (oddDirichletCharacters p ℂ) (fun χ hχ ↦ mem_oddDirichletCharacters.mp hχ)
    (fun s hs ↦ cyclotomic_dedekindZeta_div_eq_prod_odd K
      (by simpa only [Complex.ofReal_re] using hs))

end TinyTauDemo
