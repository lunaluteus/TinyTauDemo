/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial coordinates on the chart at infinity

Reflecting every coordinate at the same degree `M` implements the substitution
`s^M p(s⁻¹)`. This preserves the unit ideal of the coordinates and every homogeneous
equation that they satisfy.
See `/roadmap/index.qmd#rem-scheme-curves-recall @ bfa7759fd8ba44b8e13df934ebe5c27f37f987eb`.
-/

public section

open Polynomial

namespace TinyTauDemo

variable {k ι : Type*} [Field k]

private theorem exists_aeval_ne_zero_of_span_range_eq_top (p : ι → k[X])
    (hp : Ideal.span (Set.range p) = ⊤) {L : Type*} [Field L] [Algebra k L] (x : L) :
    ∃ i, aeval x (p i) ≠ 0 := by
  by_contra! h
  have hle : Ideal.span (Set.range p) ≤ RingHom.ker (aeval x).toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [hp, top_le_iff] at hle
  have hm : (1 : k[X]) ∈ RingHom.ker (aeval x).toRingHom := by rw [hle]; exact Submodule.mem_top
  exact one_ne_zero (by simpa only [RingHom.mem_ker, AlgHom.coe_toRingHom, map_one] using hm)

/-- The denominator-cleared coordinates on the chart at infinity generate the unit ideal.
At the origin, a coordinate of maximal degree has nonzero constant term. -/
theorem span_range_reflect_eq_top (p : ι → k[X]) {M : ℕ}
    (hp : Ideal.span (Set.range p) = ⊤)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hmax : ∃ i, p i ≠ 0 ∧ (p i).natDegree = M) :
    Ideal.span (Set.range (fun i ↦ (p i).reflect M)) = ⊤ := by
  by_contra hproper
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hproper
  let : J.IsMaximal := hJ
  let L := k[X] ⧸ J
  let : Field L := Ideal.Quotient.field J
  let q : k[X] →ₐ[k] L := IsScalarTower.toAlgHom k k[X] L
  let s := q X
  have hzero (i : ι) : aeval s ((p i).reflect M) = 0 := by
    dsimp only [s]
    rw [aeval_algHom_apply, aeval_X_left_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span ⟨i, rfl⟩))
  rcases eq_or_ne s 0 with hs | hs
  · obtain ⟨i, hp₀, hM⟩ := hmax
    have hz := hzero i
    rw [hs, ← coeff_zero_eq_aeval_zero', coeff_reflect, revAt_zero, ← hM, ← leadingCoeff] at hz
    exact (leadingCoeff_ne_zero.mpr hp₀) ((algebraMap k L).injective (hz.trans (map_zero _).symm))
  · let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
    obtain ⟨i, hi⟩ := exists_aeval_ne_zero_of_span_range_eq_top p hp s⁻¹
    apply hi
    have he := eval₂_reflect_eq_zero_iff (algebraMap k L) s⁻¹ M (p i) (hdeg i)
    rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def] at he
    exact he.mp (hzero i)

/-- Reflecting all coordinates at the same degree preserves a homogeneous equation
as an identity of polynomials on the chart at infinity. -/
theorem aeval_reflect_eq_zero_of_isHomogeneous
    (p : ι → k[X]) {M n : ℕ} {F : MvPolynomial ι k} (hF : F.IsHomogeneous n)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hp : MvPolynomial.aeval p F = 0) :
    MvPolynomial.aeval (fun i ↦ (p i).reflect M) F = 0 := by
  let L := FractionRing k[X]
  let q : k[X] →ₐ[k] L := IsScalarTower.toAlgHom k k[X] L
  let s := q X
  have hq : Function.Injective q := IsFractionRing.injective k[X] L
  have hs : s ≠ 0 := fun h ↦ X_ne_zero (hq (h.trans (map_zero q).symm))
  let : Invertible s⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  let g : ι → L := fun i ↦ q ((p i).reflect M)
  let v : k[X] →ₐ[k] L := aeval s⁻¹
  have heq : s⁻¹ ^ M • g = v ∘ p := by
    funext i
    have h := eval₂_reflect_mul_pow (algebraMap k L) s⁻¹ M (p i) (hdeg i)
    rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def] at h
    dsimp only [s] at h
    rw [aeval_algHom_apply, aeval_X_left_apply] at h
    simpa only [Pi.smul_apply, smul_eq_mul, g, v, Function.comp_apply,
      mul_comm (s⁻¹ ^ M)] using h
  have horig : MvPolynomial.aeval (v ∘ p) F = 0 := by
    change MvPolynomial.aeval (fun i ↦ v (p i)) F = 0
    rw [← MvPolynomial.comp_aeval_apply, hp, map_zero]
  rw [← heq, hF.aeval_smul, smul_eq_mul] at horig
  have hg : MvPolynomial.aeval g F = 0 :=
    (mul_eq_zero.mp horig).resolve_left (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero hs)))
  apply hq
  rw [map_zero, MvPolynomial.comp_aeval_apply]
  exact hg

end TinyTauDemo
