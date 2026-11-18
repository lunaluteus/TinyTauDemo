/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The fundamental ramification identity and total ramification

The fundamental identity counts a finite separable extension by local ramification and
inertia degrees. If the extended ideal is a power of full degree, this identity forces
the generator of that power to generate the unique prime over the given prime.
Mathlib gives the factorization and its exponents in `Ideal.map_algebraMap_eq_finsetProd_pow`
and `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`.
See `/roadmap/index.qmd#rem-ramification-disc-recall @ ac966279dffb3868e9777cbeb736cfbe55a73f63`.
-/

public section

open scoped BigOperators
open Module UniqueFactorizationMonoid

namespace Ideal

private theorem totallyRamified_of_map_eq_pow_finrank_aux {A B : Type*}
    [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥) (I : Ideal B)
    (hpow : p.map (algebraMap A B) = I ^ finrank A B) :
    p.primesOver B = {I} ∧ I.ramificationIdx A = finrank A B ∧ I.inertiaDeg A = 1 := by
  classical
  have hpmap : p.map (algebraMap A B) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  have hsum := sum_ramification_inertia_eq_finrank (R := A) (S := B) (p := p)
  have hterm (q : p.primesOver B) :
      q.1.ramificationIdx A = finrank A B ∧ q.1.inertiaDeg A = 1 := by
    have hepos : 0 < q.1.ramificationIdx A := ramificationIdx_pos A q.1
    have hfpos : 0 < q.1.inertiaDeg A := inertiaDeg_pos q.1 A
    have hbound : q.1.ramificationIdx A * q.1.inertiaDeg A ≤ finrank A B := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun q : p.primesOver B =>
        q.1.ramificationIdx A * q.1.inertiaDeg A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    have hdvd : finrank A B ∣ q.1.ramificationIdx A := by
      rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p q.1 hpmap, hpow,
        normalizedFactors_pow, Multiset.count_nsmul]
      exact dvd_mul_right _ _
    have he : q.1.ramificationIdx A = finrank A B :=
      (Nat.le_mul_of_pos_right _ hfpos).trans hbound |>.antisymm (Nat.le_of_dvd hepos hdvd)
    have hf : q.1.inertiaDeg A = 1 := by
      apply Nat.le_antisymm _ hfpos
      have hle : q.1.ramificationIdx A * q.1.inertiaDeg A ≤ q.1.ramificationIdx A * 1 :=
        (mul_one (q.1.ramificationIdx A)).symm ▸ he.symm ▸ hbound
      exact Nat.le_of_mul_le_mul_left hle hepos
    exact ⟨he, hf⟩
  obtain ⟨q⟩ := (inferInstance : Nonempty (p.primesOver B))
  have hpos : 0 < finrank A B := (hterm q).1 ▸ ramificationIdx_pos A q.1
  have hconst : ∑ Q : p.primesOver B, (finrank A B) = finrank A B := by
    simpa only [(hterm _).1, (hterm _).2, mul_one] using hsum
  have hcard : Fintype.card (p.primesOver B) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hconst
    exact Nat.eq_of_mul_eq_mul_right hpos (hconst.trans (one_mul _).symm)
  obtain ⟨Q, hQ⟩ := Fintype.card_eq_one_iff.mp hcard
  have hset : p.primesOver B = {Q.1} :=
    Set.eq_singleton_iff_unique_mem.mpr
      ⟨Q.2, fun q hq => congrArg Subtype.val (hQ ⟨q, hq⟩)⟩
  have hQpow : p.map (algebraMap A B) = Q.1 ^ finrank A B := by
    rw [map_algebraMap_eq_finsetProd_pow hp]
    refine (Finset.prod_eq_single Q.1 ?_ ?_).trans ?_
    · intro P hP hne
      have hmem : P ∈ ({Q.1} : Set (Ideal B)) := hset ▸ (Set.mem_toFinset.mp hP)
      exact (hne (Set.mem_singleton_iff.mp hmem)).elim
    · intro hnot
      exact (hnot (Set.mem_toFinset.mpr Q.2)).elim
    · rw [(hterm Q).1]
  have heq : I = Q.1 := pow_left_injective hpos.ne' (hpow.symm.trans hQpow)
  rw [heq]
  exact ⟨hset, hterm Q⟩

section IntegralClosure

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
  [FiniteDimensional (FractionRing A) K] [Algebra.IsSeparable (FractionRing A) K]

omit [Algebra.IsSeparable (FractionRing A) K] in
private theorem finrank_integralClosure_eq_finrank :
    finrank A (integralClosure A K) = finrank (FractionRing A) K := by
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr
    (IsScalarTower.algebraMap_eq A (FractionRing A) K ▸
      (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A)))
  have : IsFractionRing (integralClosure A K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension A (FractionRing A) K _
  exact (IsFractionRing.finrank_eq A (FractionRing A) (integralClosure A K) K).symm

private theorem integralClosure_isTorsionFree : IsTorsionFree A (integralClosure A K) := by
  have : IsTorsionFree A K := IsTorsionFree.trans_faithfulSMul A (FractionRing A) K
  exact IsIntegralClosure.isTorsionFree A K

open scoped Classical in
/-- The sum of ramification indices times inertia degrees in the integral closure is the
degree of the finite separable extension of fraction fields. -/
theorem sum_ramification_inertia_integralClosure (p : Ideal A) [p.IsPrime] :
    let B := integralClosure A K
    let _ : Module.Finite A B := IsIntegralClosure.finite A (FractionRing A) K B
    let _ : Fintype (p.primesOver B) := (Algebra.QuasiFinite.finite_primesOver p).fintype
    ∑ Q : p.primesOver B, Q.1.ramificationIdx A * Q.1.inertiaDeg A =
      finrank (FractionRing A) K := by
  have : Module.Finite A (integralClosure A K) :=
    IsIntegralClosure.finite A (FractionRing A) K _
  have := integralClosure_isTorsionFree (A := A) (K := K)
  let _ : Fintype (p.primesOver (integralClosure A K)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  dsimp only
  rw [← finrank_integralClosure_eq_finrank]
  exact sum_ramification_inertia_eq_finrank (S := integralClosure A K) (p := p)

/-- If the extension of a nonzero prime ideal is the full-degree power of a principal ideal,
that principal ideal is the unique prime above it and the residue extension is trivial. -/
theorem total_ramification_of_map_eq_span_pow (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (u : integralClosure A K)
    (hpow : p.map (algebraMap A (integralClosure A K)) =
      (span {u}) ^ finrank (FractionRing A) K) :
    let P : Ideal (integralClosure A K) := span {u}
    p.primesOver (integralClosure A K) = {P} ∧
      P.ramificationIdx A = finrank (FractionRing A) K ∧ P.inertiaDeg A = 1 ∧
      Nonempty ((A ⧸ p) ≃+* (integralClosure A K ⧸ P)) := by
  intro P
  have : p.IsMaximal := Ideal.IsPrime.isMaximal ‹p.IsPrime› hp
  have : Module.Finite A (integralClosure A K) :=
    IsIntegralClosure.finite A (FractionRing A) K _
  have := integralClosure_isTorsionFree (A := A) (K := K)
  have hdegree := finrank_integralClosure_eq_finrank (A := A) (K := K)
  obtain ⟨hset, he, hf⟩ := totallyRamified_of_map_eq_pow_finrank_aux p hp P
    (by simpa only [hdegree] using hpow)
  have hP : P ∈ p.primesOver (integralClosure A K) := by simp [hset]
  have : P.IsPrime := hP.1
  have : P.LiesOver p := hP.2
  have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  let fld : Field (A ⧸ p) := Ideal.Quotient.field p
  have : Module.Free (A ⧸ p) (integralClosure A K ⧸ P) :=
    @Module.Free.of_divisionRing _ _ fld.toDivisionRing _ _
  have hf' : finrank (A ⧸ p) (integralClosure A K ⧸ P) = 1 :=
    (inertiaDeg_eq_of_isMaximal p P).symm.trans hf
  have hbij := (Algebra.finrank_eq_one_iff_bijective_algebraMap
    (F := A ⧸ p) (E := integralClosure A K ⧸ P)).mp hf'
  exact ⟨hset, he.trans hdegree, hf, ⟨RingEquiv.ofBijective _ hbij⟩⟩

end IntegralClosure

end Ideal
