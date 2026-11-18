/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatLineExtension
public import TinyTauDemo.FermatCharts
public import TinyTauDemo.FermatRational
import TinyTauDemo.FermatPolynomialMap
import TinyTauDemo.ChartFunctionField
import TinyTauDemo.FermatDegree
import TinyTauDemo.FermatAffineEval

/-!
# Degree of the polynomial-coordinate map to the Fermat curve

See `/roadmap/index.qmd#rem-scheme-curves-recall @ b87f50dc05d3e4cdf59e8fd97e1a93d6eb8e8bc8`.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial TauCeti.AlgebraicGeometry
open scoped IntermediateField

namespace TinyTauDemo

universe u

private theorem isCoprime_of_mem_prime {R : Type*} [CommRing R] {a b : R}
    (h : ∀ P : Ideal R, P.IsPrime → a ∈ P → b ∈ P → False) : IsCoprime a b := by
  apply (Ideal.isCoprime_span_singleton_iff a b).mp
  apply Ideal.coprime_of_no_prime_ge
  intro P ha hb hp
  exact h P hp (ha (Ideal.mem_span_singleton_self a)) (hb (Ideal.mem_span_singleton_self b))

private theorem primitiveFermatSolution_of_span_eq_top {k : Type*} [Field k]
    {n : ℕ} {x y z : k[X]} (hn : 0 < n) (heq : x ^ n + y ^ n = z ^ n)
    (hp : Ideal.span (Set.range (![x, y, z] : Fin 3 → k[X])) = ⊤)
    (hM : 0 < max x.natDegree (max y.natDegree z.natDegree)) :
    PrimitiveFermatSolution n x y z := by
  have habsurd (P : Ideal k[X]) (hP : P.IsPrime)
      (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P) : False := by
    apply hP.ne_top
    rw [eq_top_iff, ← hp, Ideal.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  have hxy : IsCoprime x y := isCoprime_of_mem_prime fun P hP hx hy ↦
    habsurd P hP hx hy (hP.mem_of_pow_mem n (heq ▸ P.add_mem
      (P.pow_mem_of_mem hx n hn) (P.pow_mem_of_mem hy n hn)))
  have hyz : IsCoprime y z := isCoprime_of_mem_prime fun P hP hy hz ↦
    habsurd P hP (hP.mem_of_pow_mem n ((eq_sub_of_add_eq heq).symm ▸ P.sub_mem
      (P.pow_mem_of_mem hz n hn) (P.pow_mem_of_mem hy n hn))) hy hz
  have hzx : IsCoprime z x := isCoprime_of_mem_prime fun P hP hz hx ↦
    habsurd P hP hx (hP.mem_of_pow_mem n ((eq_sub_of_add_eq' heq).symm ▸ P.sub_mem
      (P.pow_mem_of_mem hz n hn) (P.pow_mem_of_mem hx n hn))) hz
  have hdegree (ha : x.natDegree = 0) (hb : y.natDegree = 0) (hc : z.natDegree = 0) : False := by
    simp [ha, hb, hc] at hM
  refine ⟨heq, hxy, hyz, hzx, ?_, ?_, ?_, ?_⟩
  · intro hx
    have hy : y.natDegree = 0 := natDegree_eq_zero_of_isUnit (hxy.symm.isUnit_of_dvd
      (hx ▸ dvd_zero y))
    have hz : n * y.natDegree = n * z.natDegree := by
      simpa [hx, zero_pow hn.ne', natDegree_pow] using congrArg natDegree heq
    exact hdegree (hx ▸ natDegree_zero) hy ((Nat.eq_of_mul_eq_mul_left hn hz).symm.trans hy)
  · intro hy
    have hx : x.natDegree = 0 := natDegree_eq_zero_of_isUnit (hxy.isUnit_of_dvd
      (hy ▸ dvd_zero x))
    have hz : n * x.natDegree = n * z.natDegree := by
      simpa [hy, zero_pow hn.ne', natDegree_pow] using congrArg natDegree heq
    exact hdegree hx (hy ▸ natDegree_zero) ((Nat.eq_of_mul_eq_mul_left hn hz).symm.trans hx)
  · intro hz
    have hx : x.natDegree = 0 := natDegree_eq_zero_of_isUnit (hzx.symm.isUnit_of_dvd
      (hz ▸ dvd_zero x))
    have hpow : x ^ n = -(y ^ n) := eq_neg_of_add_eq_zero_left (by
      simpa [hz, zero_pow hn.ne'] using heq)
    have hy : n * x.natDegree = n * y.natDegree := by
      simpa only [natDegree_neg, natDegree_pow] using congrArg natDegree hpow
    exact hdegree hx ((Nat.eq_of_mul_eq_mul_left hn hy).symm.trans hx) (hz ▸ natDegree_zero)
  · rintro ⟨hx, hy, hz⟩
    exact hdegree (natDegree_eq_zero_of_isUnit hx) (natDegree_eq_zero_of_isUnit hy)
      (natDegree_eq_zero_of_isUnit hz)

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {n : ℕ} {x y z : k[X]}

/-- The projective morphism defined by a primitive Fermat tuple is dominant, and its degree
times the degree of the plane Fermat curve is the maximum polynomial coordinate degree. -/
theorem PrimitiveFermatSolution.projectiveLineMap_degree
    (h : PrimitiveFermatSolution n x y z) (hn : 0 < n)
    (hF : MvPolynomial.aeval ![x, y, z] (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range (![x, y, z] : Fin 3 → k[X])) = ⊤)
    (f : projectiveLine k ⟶ fermatProjective k n)
    (hf : projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap ![x, y, z] hF hp) :
    have := fermatProjective_isIntegral k hn
    ∃ _ : IsDominant f,
      let : Algebra (fermatProjective k n).functionField (projectiveLine k).functionField :=
        f.functionFieldMap.hom.toAlgebra
      max x.natDegree (max y.natDegree z.natDegree) =
        n * Module.finrank (fermatProjective k n).functionField
          (projectiveLine k).functionField := by
  have := fermatProjective_isIntegral k hn
  let p : Fin 3 → k[X] := ![x, y, z]
  let φ := Algebra.ofId k[X] (RatFunc k)
  let φk : k[X] →ₐ[k] RatFunc k :=
    ⟨φ.toRingHom, fun _ ↦ (IsScalarTower.algebraMap_apply k k[X] (RatFunc k) _).symm⟩
  let a := φ x / φ z
  let b := φ y / φ z
  let E := k⟮a, b⟯
  let ψ := fermatAffineEval (k := k) a b h.ratFunc_div_pow_add_div_pow
  have hz : φk (p 2) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr h.z_ne_zero
  have hψ : ∀ P : MvPolynomial (Fin 2) k, ψ (Ideal.Quotient.mk _ P) =
      MvPolynomial.aeval ![φk (p 0) / φk (p 2), φk (p 1) / φk (p 2)] P :=
    fermatAffineEval_mk _ _ _
  have hchart := fermatAffineMap_comp_SpecMap_eq_lastChart hn p hF hp φk hz ψ hψ
  have hinj : Function.Injective ψ := h.fermatAffineEval_ratFunc_injective hn
  let : IsDomain (FermatAffineRing k n 2) := Function.Injective.isDomain ψ.toRingHom hinj
  let hrel : a ^ n + b ^ n = 1 := h.ratFunc_div_pow_add_div_pow
  let ha : Transcendental k a := h.transcendental_ratFunc_div hn
  let : Algebra (FermatAffineRing k n 2) E := fermatAffineAdjoinAlgebra (k := k) hrel
  let : IsFractionRing (FermatAffineRing k n 2) E :=
    fermatAffineAdjoin_isFractionRing (k := k) hrel hn ha
  have hι : (algebraMap E (RatFunc k)).comp (algebraMap (FermatAffineRing k n 2) E) =
      ψ.toRingHom := RingHom.ext (fermatAffineAdjoin_algebraMap (k := k) hrel)
  obtain ⟨hD, hdegree⟩ := exists_isDominant_finrank_eq_of_affineCharts
    (R := .of k[X]) (S := .of (FermatAffineRing k n 2))
    (projectiveLinePolynomialChart k 0) (fermatAffineChart k hn 2) (RatFunc k) E f (by
      rw [hf, hι]
      exact hchart)
  refine ⟨hD, ?_⟩
  dsimp only at hdegree ⊢
  rw [hdegree]
  exact h.max_eq_mul_finrank_adjoin_ratFunc hn

/-- The degree formula for any polynomial Fermat coordinates that generate the unit ideal
and have positive maximum degree. -/
theorem fermatProjectiveLineMap_degree_of_pos (hn : 0 < n)
    (hF : MvPolynomial.aeval ![x, y, z] (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range (![x, y, z] : Fin 3 → k[X])) = ⊤)
    (hM : 0 < max x.natDegree (max y.natDegree z.natDegree))
    (f : projectiveLine k ⟶ fermatProjective k n)
    (hf : projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap ![x, y, z] hF hp) :
    have := fermatProjective_isIntegral k hn
    ∃ _ : IsDominant f,
      let : Algebra (fermatProjective k n).functionField (projectiveLine k).functionField :=
        f.functionFieldMap.hom.toAlgebra
      max x.natDegree (max y.natDegree z.natDegree) =
        n * Module.finrank (fermatProjective k n).functionField
          (projectiveLine k).functionField := by
  have heq : x ^ n + y ^ n = z ^ n := by
    apply sub_eq_zero.mp
    have h := hF
    rw [fermatEquation_def, map_sub, map_add, map_pow, map_pow, map_pow,
      MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X] at h
    exact h
  exact (primitiveFermatSolution_of_span_eq_top hn heq hp hM).projectiveLineMap_degree
    hn hF hp f hf

/-- Every primitive polynomial Fermat solution defines a dominant projective morphism over
the coefficient field with the degree given by the coordinate tuple. -/
theorem PrimitiveFermatSolution.exists_projectiveLineMap_degree
    (h : PrimitiveFermatSolution n x y z) (hn : 0 < n) :
    have := fermatProjective_isIntegral k hn
    ∃ f : projectiveLine k ⟶ fermatProjective k n,
      f ≫ fermatProjectiveToSpec k n = (projectiveLine k ↘ Spec (.of k)) ∧
      (∃ (hF : MvPolynomial.aeval ![x, y, z] (fermatEquation k n) = 0)
        (hp : Ideal.span (Set.range (![x, y, z] : Fin 3 → k[X])) = ⊤),
        projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap ![x, y, z] hF hp) ∧
      ∃ _ : IsDominant f,
        let : Algebra (fermatProjective k n).functionField (projectiveLine k).functionField :=
          f.functionFieldMap.hom.toAlgebra
        max x.natDegree (max y.natDegree z.natDegree) =
          n * Module.finrank (fermatProjective k n).functionField
            (projectiveLine k).functionField := by
  have := fermatProjective_isIntegral k hn
  let p : Fin 3 → k[X] := ![x, y, z]
  have hF : MvPolynomial.aeval p (fermatEquation k n) = 0 := by
    rw [fermatEquation_def, map_sub, map_add, map_pow, map_pow, map_pow,
      MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact sub_eq_zero.mpr h.eq
  have hp : Ideal.span (Set.range p) = ⊤ := by
    let I := Ideal.span (Set.range p)
    have hx : x ∈ I := Ideal.subset_span ⟨0, rfl⟩
    have hy : y ∈ I := Ideal.subset_span ⟨1, rfl⟩
    obtain ⟨a, b, hcop⟩ := h.coprime_xy
    have hone : (1 : k[X]) ∈ I := hcop ▸ I.add_mem (I.mul_mem_left a hx) (I.mul_mem_left b hy)
    exact I.eq_top_of_isUnit_mem hone isUnit_one
  obtain ⟨f, ⟨hf, hc⟩, -⟩ := existsUnique_fermatProjectiveLineMap p hF hp
  exact ⟨f, hf, ⟨hF, hp, hc⟩, h.projectiveLineMap_degree hn hF hp f hc⟩

end TinyTauDemo
