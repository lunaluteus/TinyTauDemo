/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.PlanePolynomialMap
public import TinyTauDemo.PlaneJacobianIntegral
public import TinyTauDemo.FermatLineExtension
public import TinyTauDemo.PlaneFieldDegree
import TinyTauDemo.ChartFunctionField
import TauCeti.FieldTheory.FunctionField.PlaneCurve.ConstantField
import TauCeti.RingTheory.MvPolynomial.CommonZero

/-!
# Degree of the map defined by a polynomial plane-curve tuple

See `/roadmap/index.qmd#rem-scheme-curves-recall @ 0ce794f8b09e1d3bf189ed3c18dd9c1894d2a4a7`.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial TauCeti TauCeti.AlgebraicGeometry
open scoped IntermediateField

namespace TinyTauDemo.ProjectiveHypersurface

universe u

variable {k : Type u} [Field k] {d : ℕ} {F : MvPolynomial (Fin 3) k}
  (hF : F.IsHomogeneous d)

/-- A polynomial tuple with the unit ideal condition defines a unique projective-line map
to a projective plane hypersurface extending its affine coordinate map over the base. -/
theorem existsUnique_projectiveLineMap (p : Fin 3 → k[X])
    (hP : MvPolynomial.aeval p F = 0) (hp : Ideal.span (Set.range p) = ⊤) :
    ∃! f : projectiveLine k ⟶ scheme hF,
      f ≫ toSpec hF = (projectiveLine k ↘ Spec (.of k)) ∧
        projectiveLinePolynomialChart k 0 ≫ f = specMap hF p hP hp := by
  let : (scheme hF).Over (Spec (.of k)) := ⟨toSpec hF⟩
  let : IsProper (scheme hF ↘ Spec (.of k)) := inferInstanceAs (IsProper (toSpec hF))
  exact existsUnique_projectiveLineMap_extending_polynomialChart k
    (specMap hF p hP hp) (specMap_toSpec hF p hP hp)

private theorem plane_ker_aeval {g : MvPolynomial (Fin 2) k}
    (hg : Irreducible g) {L : Type u} [Field L] [Algebra k L] (a : Fin 2 → L)
    (ha : MvPolynomial.aeval a g = 0) (j : Fin 2) (htr : Transcendental k (a j)) :
    RingHom.ker (MvPolynomial.aeval a).toRingHom = Ideal.span {g} := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 j
  let r := MvPolynomial.renameEquiv k e.symm
  have hvec : ![a (e 0), a (e 1)] = a ∘ e := by
    ext i
    fin_cases i <;> rfl
  have heval (q : MvPolynomial (Fin 2) k) :
      MvPolynomial.aeval ![a (e 0), a (e 1)] (r q) = MvPolynomial.aeval a q := by
    rw [hvec]
    change MvPolynomial.aeval (a ∘ e) (MvPolynomial.rename e.symm q) = _
    rw [MvPolynomial.aeval_rename]
    congr 1
    ext i
    simp
  have hg' : Irreducible (r g) := (MulEquiv.irreducible_iff r.toMulEquiv).mpr hg
  have htr' : Transcendental k (a (e 0)) := by simpa [e] using htr
  have hker : RingHom.ker (MvPolynomial.aeval ![a (e 0), a (e 1)]).toRingHom =
      Ideal.span {r g} := ker_aeval_eq_span_singleton_of_irreducible hg' htr' ((heval g).trans ha)
  ext q
  constructor
  · intro hq
    have hq' : r q ∈ RingHom.ker
        (MvPolynomial.aeval ![a (e 0), a (e 1)]).toRingHom := by
      rw [RingHom.mem_ker]
      exact (heval q).trans (RingHom.mem_ker.mp hq)
    rw [hker, Ideal.mem_span_singleton] at hq'
    exact Ideal.mem_span_singleton.mpr ((map_dvd_iff r).mp hq')
  · intro hq
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, ha, zero_mul]

variable [IsAlgClosed k]

private theorem normalizedChartEval_injective
    (hJac : ∀ b : Fin 3 → k, b ≠ 0 → MvPolynomial.aeval b F = 0 →
      ∃ j, MvPolynomial.aeval b (MvPolynomial.pderiv j F) ≠ 0)
    {L : Type u} [Field L] [Algebra k L] (p : Fin 3 → L) (hP : MvPolynomial.aeval p F = 0)
    (i : Fin 3) (hi : p i ≠ 0) (j : Fin 2)
    (htr : Transcendental k (p (i.succAbove j) / p i)) :
    Function.Injective (normalizedChartEval hF p hP i hi) := by
  let a : Fin 2 → L := fun l ↦ p (i.succAbove l) / p i
  let g := dehomogenize i F
  have hfg : MvPolynomial.aeval a g = 0 := by
    have hz : Ideal.Quotient.mk (Ideal.span {dehomogenize i F}) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)
    rw [← normalizedChartEval_mk hF p hP i hi, hz, map_zero]
  have hunit : ¬ IsUnit g := fun h ↦ not_isUnit_zero (hfg ▸ h.map (MvPolynomial.aeval a))
  have hirr : Irreducible g := by
    have hh := TauCeti.irreducible_map_dehomogenize (K := k) (by decide : 2 ≤ 2) hF hJac i hunit
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using hh
  have hker := plane_ker_aeval hirr a hfg j htr
  apply (injective_iff_map_eq_zero _).mpr
  intro q hq
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [normalizedChartEval_mk] at hq
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hker]
  exact RingHom.mem_ker.mpr hq

omit [IsAlgClosed k] in
private theorem normalizedChartEval_range
    {L : Type u} [Field L] [Algebra k L] (p : Fin 3 → L) (hP : MvPolynomial.aeval p F = 0)
    (i : Fin 3) (hi : p i ≠ 0) (e : Fin 2 ≃ Fin 2) :
    (normalizedChartEval hF p hP i hi).range =
      Algebra.adjoin k {p (i.succAbove (e 0)) / p i, p (i.succAbove (e 1)) / p i} := by
  let A := ChartRing F i
  let q : MvPolynomial (Fin 2) k →ₐ[k] A := Ideal.Quotient.mkₐ k _
  let f := normalizedChartEval hF p hP i hi
  let a : Fin 2 → L := fun j ↦ p (i.succAbove j) / p i
  have hq : q.range = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective k _)
  have hcomp : f.comp q = MvPolynomial.aeval a := by
    apply MvPolynomial.algHom_ext
    intro j
    change f (Ideal.Quotient.mk _ (MvPolynomial.X j)) = _
    exact normalizedChartEval_mk hF p hP i hi _
  have hpair : Set.range a = {a (e 0), a (e 1)} := by
    rw [show Set.range a = Set.range (a ∘ e) from (e.surjective.range_comp a).symm]
    ext c
    simp [Function.comp_def, Fin.exists_fin_two, eq_comm]
  have heval := congrArg AlgHom.range hcomp
  rw [AlgHom.range_comp, hq, Algebra.map_top, MvPolynomial.aeval_range, hpair] at heval
  exact heval

/-- The degree of the actual projective extension is the degree of the field generated
by the two normalized coordinate ratios on a chart with a transcendental ratio. -/
theorem projectiveLineMap_finrank_eq_chartCoordinates (hd : 0 < d) (hF₀ : F ≠ 0)
    (hJac : ∀ b : Fin 3 → k, b ≠ 0 → MvPolynomial.aeval b F = 0 →
      ∃ j, MvPolynomial.aeval b (MvPolynomial.pderiv j F) ≠ 0)
    (p : Fin 3 → k[X]) (hP : MvPolynomial.aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) (i : Fin 3) (hi : p i ≠ 0) (e : Fin 2 ≃ Fin 2)
    (ht : Transcendental k (polynomialRatio (p (i.succAbove (e 0))) (p i)))
    (f : projectiveLine k ⟶ scheme hF)
    (hf : projectiveLinePolynomialChart k 0 ≫ f = specMap hF p hP hp) :
    have := isIntegral_of_forall_exists_pderiv_ne_zero hF hd hF₀ hJac
    ∃ _ : IsDominant f,
      let : Algebra (scheme hF).functionField (projectiveLine k).functionField :=
        f.functionFieldMap.hom.toAlgebra
      Module.finrank (scheme hF).functionField (projectiveLine k).functionField =
        Module.finrank k⟮polynomialRatio (p (i.succAbove (e 0))) (p i),
          polynomialRatio (p (i.succAbove (e 1))) (p i)⟯ (RatFunc k) := by
  have := isIntegral_of_forall_exists_pderiv_ne_zero hF hd hF₀ hJac
  let φ := IsScalarTower.toAlgHom k k[X] (RatFunc k)
  let q := φ ∘ p
  have hqF : MvPolynomial.aeval q F = 0 := by
    change MvPolynomial.aeval (fun i ↦ φ (p i)) F = 0
    rw [← MvPolynomial.comp_aeval_apply (f := p) φ F, hP, map_zero]
  have hq : Ideal.span (Set.range q) = ⊤ := by
    rw [show q = φ ∘ p from rfl, Set.range_comp, ← Ideal.map_span, hp, Ideal.map_top]
  have hi' : q i ≠ 0 := RatFunc.algebraMap_ne_zero hi
  let ψ := normalizedChartEval hF q hqF i hi'
  have hψ : Function.Injective ψ := normalizedChartEval_injective hF hJac q hqF i hi' (e 0) ht
  let R := ChartRing F i
  let : IsDomain R := Function.Injective.isDomain ψ.toRingHom hψ
  let G := FractionRing R
  let ι : G →ₐ[k] RatFunc k := IsFractionRing.liftAlgHom hψ
  let : Algebra G (RatFunc k) := ι.toRingHom.toAlgebra
  have hι : (algebraMap G (RatFunc k)).comp (algebraMap R G) = ψ.toRingHom := by
    apply RingHom.ext
    intro a
    change ι (algebraMap R G a) = ψ a
    rw [IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap]
    rfl
  obtain ⟨hdom, hdeg⟩ := exists_isDominant_finrank_eq_of_affineCharts
    (R := .of k[X]) (S := .of R)
    (projectiveLinePolynomialChart k 0) (affineChart hF i) (RatFunc k) G f (by
      rw [hf, hι]
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specMap hF p hP hp =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ affineChart hF i
      rw [specMap_comp_SpecMap hF φ p hP hp hqF hq]
      exact specMap_eq_affineChart hF q hqF hq i hi')
  let a := polynomialRatio (p (i.succAbove (e 0))) (p i)
  let b := polynomialRatio (p (i.succAbove (e 1))) (p i)
  have hE : ι.fieldRange = k⟮a, b⟯ :=
    IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq hψ
      (normalizedChartEval_range hF q hqF i hi' e)
  let eG := (AlgEquiv.ofInjectiveField ι).trans (IntermediateField.equivOfEq hE)
  have heG : Module.finrank G (RatFunc k) = Module.finrank k⟮a, b⟯ (RatFunc k) := by
    apply Algebra.finrank_eq_of_equiv_equiv eG.toRingEquiv (RingEquiv.refl (RatFunc k))
    apply RingHom.ext
    intro a
    rfl
  exact ⟨hdom, hdeg.trans heG⟩

omit [IsAlgClosed k] in
private theorem exists_transcendental_ratio (p : Fin 3 → k[X])
    (hp : Ideal.span (Set.range p) = ⊤) (i : Fin 3) (hi : p i ≠ 0)
    (hM : 0 < max (p 0).natDegree (max (p 1).natDegree (p 2).natDegree)) :
    ∃ j : Fin 2, Transcendental k (polynomialRatio (p (i.succAbove j)) (p i)) := by
  by_contra! hn
  have htr (j : Fin 3) : ¬ Transcendental k (polynomialRatio (p j) (p i)) := by
    refine Fin.succAboveCases i ?_ hn j
    have hh : polynomialRatio (p i) (p i) = (1 : RatFunc k) :=
      div_self (RatFunc.algebraMap_ne_zero hi)
    rw [hh, Transcendental, not_not]
    exact isAlgebraic_one
  have hc (j : Fin 3) : ∃ c : k, p j = p i * C c := by
    obtain ⟨c, hc⟩ := not_not.mp fun h ↦
      htr j (RatFunc.transcendental_of_ne_C _ h)
    refine ⟨c, (RatFunc.algebraMap_injective k) ?_⟩
    rw [map_mul, RatFunc.algebraMap_C, mul_comm]
    exact (div_eq_iff (RatFunc.algebraMap_ne_zero hi)).mp hc
  have hu : IsUnit (p i) := by
    apply Ideal.span_singleton_eq_top.mp
    apply top_unique
    rw [← hp, Ideal.span_le, Set.range_subset_iff]
    intro j
    obtain ⟨c, hc⟩ := hc j
    exact Ideal.mem_span_singleton.mpr ⟨C c, hc⟩
  have h0 (j : Fin 3) : (p j).natDegree = 0 := by
    obtain ⟨c, hc⟩ := hc j
    rw [hc]
    exact (natDegree_mul_le.trans (by simp [natDegree_eq_zero_of_isUnit hu])).antisymm
      (Nat.zero_le _)
  simp [h0] at hM

private def coordinatePermutation (i : Fin 3) (e : Fin 2 ≃ Fin 2) : Fin 3 ≃ Fin 3 :=
  (finSuccEquiv' (2 : Fin 3)).trans ((Equiv.optionCongr e).trans (finSuccEquiv' i).symm)

private theorem coordinatePermutation_last (i : Fin 3) (e : Fin 2 ≃ Fin 2) :
    coordinatePermutation i e 2 = i := by
  apply (finSuccEquiv' i).injective
  simp [coordinatePermutation]

private theorem coordinatePermutation_other (i : Fin 3) (e : Fin 2 ≃ Fin 2) (j : Fin 2) :
    coordinatePermutation i e ((2 : Fin 3).succAbove j) = i.succAbove (e j) := by
  apply (finSuccEquiv' i).injective
  simp [coordinatePermutation]

private theorem max_three_perm (q : Fin 3 → ℕ) (e : Fin 3 ≃ Fin 3) :
    max (q (e 0)) (max (q (e 1)) (q (e 2))) = max (q 0) (max (q 1) (q 2)) := by
  have hb (a : Fin 3 → ℕ) (j : Fin 3) : a j ≤ max (a 0) (max (a 1) (a 2)) := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hc (j : Fin 3) : q j ≤ max (q (e 0)) (max (q (e 1)) (q (e 2))) := by
    obtain ⟨l, rfl⟩ := e.surjective j
    exact hb (q ∘ e) l
  exact le_antisymm (max_le (hb q _) (max_le (hb q _) (hb q _)))
    (max_le (hc 0) (max_le (hc 1) (hc 2)))

/-- A primitive polynomial tuple of positive maximum degree defines a dominant map
to a smooth plane curve. Its maximum degree is the plane degree times the degree
of the actual projective extension. -/
theorem projectiveLineMap_degree (hd : 0 < d) (hF₀ : F ≠ 0)
    (hJac : ∀ b : Fin 3 → k, b ≠ 0 → MvPolynomial.aeval b F = 0 →
      ∃ j, MvPolynomial.aeval b (MvPolynomial.pderiv j F) ≠ 0)
    (p : Fin 3 → k[X]) (hP : MvPolynomial.aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤)
    (hM : 0 < max (p 0).natDegree (max (p 1).natDegree (p 2).natDegree))
    (f : projectiveLine k ⟶ scheme hF)
    (hf : projectiveLinePolynomialChart k 0 ≫ f = specMap hF p hP hp) :
    have := isIntegral_of_forall_exists_pderiv_ne_zero hF hd hF₀ hJac
    ∃ _ : IsDominant f,
      let : Algebra (scheme hF).functionField (projectiveLine k).functionField :=
        f.functionFieldMap.hom.toAlgebra
      max (p 0).natDegree (max (p 1).natDegree (p 2).natDegree) =
        d * Module.finrank (scheme hF).functionField (projectiveLine k).functionField := by
  have := isIntegral_of_forall_exists_pderiv_ne_zero hF hd hF₀ hJac
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra! hz
    simp [hz] at hM
  obtain ⟨j, hj⟩ := exists_transcendental_ratio p hp i hi hM
  let e := Equiv.swap 0 j
  have ht : Transcendental k (polynomialRatio (p (i.succAbove (e 0))) (p i)) := by
    simpa [e] using hj
  obtain ⟨hdom, hfin⟩ :=
    projectiveLineMap_finrank_eq_chartCoordinates hF hd hF₀ hJac p hP hp i hi e ht f hf
  let σ := coordinatePermutation i e
  have hσ2 : σ 2 = i := coordinatePermutation_last i e
  have hσ0 : σ 0 = i.succAbove (e 0) := coordinatePermutation_other i e 0
  have hσ1 : σ 1 = i.succAbove (e 1) := coordinatePermutation_other i e 1
  let G := MvPolynomial.rename σ.symm F
  have hG : G.IsHomogeneous d := hF.rename_isHomogeneous
  have hG₀ : G ≠ 0 := fun he ↦ hF₀ ((MvPolynomial.rename_injective σ.symm σ.symm.injective)
    (he.trans (map_zero (MvPolynomial.rename σ.symm)).symm))
  have hJacG (c : Fin 3 → k) (hc : c ≠ 0) (hcG : MvPolynomial.aeval c G = 0) :
      ∃ l, MvPolynomial.aeval c (MvPolynomial.pderiv l G) ≠ 0 := by
    have hcn : c ∘ σ.symm ≠ 0 := by
      intro h
      apply hc
      funext l
      simpa [Function.comp_def] using congrFun h (σ l)
    have hzero : MvPolynomial.aeval (c ∘ σ.symm) F = 0 := by
      rw [← MvPolynomial.aeval_rename]
      exact hcG
    obtain ⟨l, hl⟩ := hJac _ hcn hzero
    refine ⟨σ.symm l, ?_⟩
    change MvPolynomial.aeval c (MvPolynomial.pderiv (σ.symm l) (MvPolynomial.rename σ.symm F)) ≠ 0
    rwa [MvPolynomial.pderiv_rename σ.symm.injective, MvPolynomial.aeval_rename]
  let x := p (σ 0)
  let y := p (σ 1)
  let z := p (σ 2)
  have hz : z ≠ 0 := by simpa [z, hσ2] using hi
  have hx : Transcendental k (polynomialRatio x z) := by simpa [x, z, hσ0, hσ2] using ht
  have hspan : Ideal.span ({x, y, z} : Set k[X]) = ⊤ := by
    have hs : ({x, y, z} : Set k[X]) = Set.range (p ∘ σ) := by
      ext v
      simp only [x, y, z, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
        Function.comp_apply]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      · rintro ⟨l, rfl⟩
        fin_cases l
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    rwa [hs, σ.surjective.range_comp]
  let φ := IsScalarTower.toAlgHom k k[X] (RatFunc k)
  let q := fun j ↦ φ (p j)
  have hq : MvPolynomial.aeval q F = 0 := by
    rw [← MvPolynomial.comp_aeval_apply (f := p) φ F, hP, map_zero]
  have hr : MvPolynomial.aeval
      ![polynomialRatio x z, polynomialRatio y z, (1 : RatFunc k)] G = 0 := by
    change MvPolynomial.aeval
      ![polynomialRatio x z, polynomialRatio y z, (1 : RatFunc k)]
        (MvPolynomial.rename σ.symm F) = 0
    rw [MvPolynomial.aeval_rename]
    have heq : (![polynomialRatio x z, polynomialRatio y z, (1 : RatFunc k)] ∘ σ.symm) =
        (φ z)⁻¹ • q := by
      funext l
      obtain ⟨j, rfl⟩ := σ.surjective l
      rw [Function.comp_apply, σ.symm_apply_apply]
      fin_cases j
      · exact div_eq_inv_mul _ _
      · exact div_eq_inv_mul _ _
      · exact (inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero hz)).symm
    rw [heq, hF.aeval_smul, hq, smul_zero]
  have hdeg := max_natDegree_eq_mul_finrank_planeCoordinateField hG hG₀ hJacG hspan hz hx hr
  refine ⟨hdom, ?_⟩
  let : IsDominant f := hdom
  let : Algebra (scheme hF).functionField (projectiveLine k).functionField :=
    f.functionFieldMap.hom.toAlgebra
  change _ = d * Module.finrank (scheme hF).functionField (projectiveLine k).functionField
  have hf' : Module.finrank (scheme hF).functionField (projectiveLine k).functionField =
      Module.finrank k⟮polynomialRatio x z, polynomialRatio y z⟯ (RatFunc k) := by
    have hx' : x = p (i.succAbove (e 0)) := congrArg p hσ0
    have hy' : y = p (i.succAbove (e 1)) := congrArg p hσ1
    have hz' : z = p i := congrArg p hσ2
    rw [hx', hy', hz']
    exact hfin
  rw [hf', ← hdeg]
  exact (max_three_perm (fun l ↦ (p l).natDegree) σ).symm

end TinyTauDemo.ProjectiveHypersurface
