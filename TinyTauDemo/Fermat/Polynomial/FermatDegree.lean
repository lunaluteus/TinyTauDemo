/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Polynomial.FermatRational
import TauCeti.FieldTheory.FunctionField.Different.PlaneCurve
import TauCeti.RingTheory.MvPolynomial.CommonZero
import TinyTauDemo.Fermat.Curve.FermatEquation

/-!
# The degree of the field inclusion defined by polynomial Fermat coordinates

The degree of the reduced ratio `x / z` is the maximum coordinate degree.
The affine Fermat projection has degree `n` over the first coordinate,
so the tower law gives the degree of the inclusion of the field generated
by the two normalized coordinates.
See `/roadmap/index.qmd#rem-scheme-curves-recall @ b87f50dc05d3e4cdf59e8fd97e1a93d6eb8e8bc8`.
-/

public section

open Polynomial IntermediateField
open scoped IntermediateField

namespace TinyTauDemo

private theorem natDegree_num_denom_of_isCoprime {k : Type*} [Field k]
    {p q : k[X]} (hpq : IsCoprime p q) (hq : q ≠ 0) :
    let f := algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q
    f.num.natDegree = p.natDegree ∧ f.denom.natDegree = q.natDegree := by
  intro f
  have hcross := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr (show f = _ from rfl)
  have hd : Associated q f.denom := associated_of_dvd_dvd
    (hpq.symm.dvd_of_dvd_mul_left ⟨f.num, hcross.symm.trans (mul_comm f.num q)⟩)
    ((RatFunc.denom_dvd hq).mpr ⟨p, rfl⟩)
  obtain ⟨u, hu⟩ := hd
  have hn : Associated p f.num := by
    refine ⟨u, ?_⟩
    apply mul_right_cancel₀ hq
    rw [hcross, ← hu]
    ac_rfl
  exact ⟨natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hn).symm,
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (show Associated q f.denom from
      ⟨u, hu⟩)).symm⟩

variable {k : Type*} [Field k] {n : ℕ} {x y z : k[X]}

/-- The degree of the rational projection `x / z` equals the maximum polynomial
coordinate degree of a primitive Fermat tuple. -/
theorem PrimitiveFermatSolution.finrank_adjoin_x_div_z_eq_max
    (h : PrimitiveFermatSolution n x y z) (hn : 0 < n) :
    let a := algebraMap k[X] (RatFunc k) x / algebraMap k[X] (RatFunc k) z
    Module.finrank k⟮a⟯ (RatFunc k) = max x.natDegree (max y.natDegree z.natDegree) := by
  intro a
  have hbound : y.natDegree ≤ max x.natDegree z.natDegree := by
    have hy : y ^ n = z ^ n - x ^ n := eq_sub_of_add_eq' h.eq
    have hle := natDegree_sub_le (z ^ n) (x ^ n)
    rw [← hy, natDegree_pow, natDegree_pow, natDegree_pow, max_mul_mul_left] at hle
    exact (Nat.le_of_mul_le_mul_left hle hn).trans (by rw [max_comm])
  obtain ⟨hx, hz⟩ := natDegree_num_denom_of_isCoprime h.coprime_zx.symm h.z_ne_zero
  rw [RatFunc.finrank_eq_max_natDegree a, hx, hz]
  omega

private theorem fermatAffine_as_bivariate (k : Type*) [Field k] (n : ℕ) :
    (Bivariate.equivMvPolynomial k).symm (TauCeti.dehomogenize (2 : Fin 3) (fermatEquation k n)) =
      X ^ n - C (1 - X ^ n) := by
  have h0 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (MvPolynomial.X 0) =
      MvPolynomial.X 0 := by simp; rfl
  have h1 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (MvPolynomial.X 1) =
      MvPolynomial.X 1 := by simp; rfl
  have h2 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (MvPolynomial.X 2) = 1 := by simp
  simp only [fermatEquation_def, map_sub, map_add, map_pow, h0, h1, h2, map_one, one_pow,
    Bivariate.equivMvPolynomial_symm_X_0, Bivariate.equivMvPolynomial_symm_X_1]
  ring

/-- The Fermat coordinate projection has degree `n` when the second coordinate
generates the field over the rational field of the first coordinate. -/
theorem fermatProjection_finrank
    [CharZero k] [IsAlgClosed k] {F : Type*} [Field F]
    [Algebra k F] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    (hn : 0 < n) {b : F} (hgen : (RatFunc k)⟮b⟯ = ⊤)
    (h : (algebraMap (RatFunc k) F RatFunc.X) ^ n + b ^ n = 1) :
    Module.finrank (RatFunc k) F = n := by
  let g := TauCeti.dehomogenize (2 : Fin 3) (fermatEquation k n)
  have hpoly : (Bivariate.equivMvPolynomial k).symm g = X ^ n - C (1 - X ^ n) :=
    fermatAffine_as_bivariate k n
  have hdeg : ((Bivariate.equivMvPolynomial k).symm g).natDegree = n := by
    rw [hpoly, natDegree_X_pow_sub_C]
  have hnonunit : ¬ IsUnit g := by
    intro hu
    have := natDegree_eq_zero_of_isUnit (hu.map (Bivariate.equivMvPolynomial k).symm)
    exact hn.ne' (hdeg.symm.trans this)
  have hirr : Irreducible g := by
    have hh := TauCeti.irreducible_map_dehomogenize (K := k) (by decide : 2 ≤ 2)
      (fermatEquation_isHomogeneous k n)
      (fun v hv _ ↦ fermatEquation_exists_aeval_pderiv_ne_zero hn v hv) (2 : Fin 3) hnonunit
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using hh
  have hmon : ((Bivariate.equivMvPolynomial k).symm g).Monic := by
    rw [hpoly]
    exact monic_X_pow_sub_C _ hn.ne'
  have hy : MvPolynomial.aeval ![algebraMap (RatFunc k) F RatFunc.X, b] g = 0 := by
    dsimp only [g]
    have hcoords : (2 : Fin 3).insertNth (1 : F) ![algebraMap (RatFunc k) F RatFunc.X, b] =
        ![algebraMap (RatFunc k) F RatFunc.X, b, (1 : F)] := by
      ext i
      fin_cases i <;> rfl
    rw [TauCeti.aeval_dehomogenize, hcoords]
    exact (aeval_fermatEquation_eq_zero_iff n _ _).mpr h
  exact (TauCeti.finrank_ratFunc_eq_natDegree_of_aeval_eq_zero hirr hmon hgen hy).trans hdeg

/-- In a primitive Fermat tuple, the maximum polynomial coordinate degree is
`n` times the degree of the inclusion of the field generated by the normalized coordinates. -/
theorem PrimitiveFermatSolution.max_eq_mul_finrank_adjoin_ratFunc
    [IsAlgClosed k] [CharZero k] (h : PrimitiveFermatSolution n x y z) (hn : 0 < n) :
    let a := algebraMap k[X] (RatFunc k) x / algebraMap k[X] (RatFunc k) z
    let b := algebraMap k[X] (RatFunc k) y / algebraMap k[X] (RatFunc k) z
    max x.natDegree (max y.natDegree z.natDegree) =
      n * Module.finrank k⟮a, b⟯ (RatFunc k) := by
  intro a b
  let A := k⟮a⟯
  let E := k⟮a, b⟯
  let a' := AdjoinPair.gen₁ k a b
  let b' := AdjoinPair.gen₂ k a b
  have ha : Transcendental k a := h.transcendental_ratFunc_div hn
  have hAE : A ≤ E := IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (mem_adjoin_pair_left k a b))
  let j := IntermediateField.inclusion hAE
  let e := RatFunc.algEquivOfTranscendental a ha
  let : Algebra A E := j.toRingHom.toAlgebra
  let : Module A E := Algebra.toModule
  let : SMul A E := Algebra.toSMul
  let : IsScalarTower A E (RatFunc k) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ show (r : RatFunc k) = (j r : RatFunc k) from rfl
  let : Algebra (RatFunc k) A := e.toAlgHom.toRingHom.toAlgebra
  let : Algebra (RatFunc k) E := (j.comp e.toAlgHom).toRingHom.toAlgebra
  let : IsScalarTower (RatFunc k) A E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower k (RatFunc k) E :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((j.comp e.toAlgHom).commutes r).symm
  have hX : algebraMap (RatFunc k) E RatFunc.X = a' := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X a ha
  have hgenk : k⟮a', b'⟯ = ⊤ := by
    apply IntermediateField.lift_injective E
    simp only [IntermediateField.lift_adjoin, Set.image_pair, IntermediateField.lift_top]
    rfl
  have hrel : a' ^ n + b' ^ n = 1 := by
    apply (algebraMap E (RatFunc k)).injective
    simp only [map_add, map_pow, map_one]
    exact h.ratFunc_div_pow_add_div_pow
  have hgen : (RatFunc k)⟮b'⟯ = ⊤ := by
    have ha' : a' ∈ (RatFunc k)⟮b'⟯ := by
      rw [← hX]
      exact IntermediateField.algebraMap_mem _ _
    have hb' : b' ∈ (RatFunc k)⟮b'⟯ := mem_adjoin_simple_self _ _
    have hle : k⟮a', b'⟯ ≤ ((RatFunc k)⟮b'⟯).restrictScalars k := by
      rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨(IntermediateField.mem_restrictScalars k).mpr ha',
        (IntermediateField.mem_restrictScalars k).mpr hb'⟩
    rw [hgenk] at hle
    exact eq_top_iff.mpr fun r _ ↦
      (IntermediateField.mem_restrictScalars k).mp (hle IntermediateField.mem_top)
  have hproj : Module.finrank (RatFunc k) E = n :=
    fermatProjection_finrank hn hgen (by rw [hX]; exact hrel)
  have hKA : Module.finrank (RatFunc k) A = 1 := Module.finrank_of_bijective_algebraMap e.bijective
  have hdegAE := Module.finrank_mul_finrank (RatFunc k) A E
  rw [hKA, one_mul, hproj] at hdegAE
  have hdeg := (Module.finrank_mul_finrank A E (RatFunc k)).symm
  rw [hdegAE] at hdeg
  exact (h.finrank_adjoin_x_div_z_eq_max hn).symm.trans hdeg

end TinyTauDemo
