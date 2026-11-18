/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.CyclotomicClassNumberFormula
public import TinyTauDemo.CyclotomicReflection
public import TinyTauDemo.UnramifiedCoprimeTower
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Reflection from an unramified extension of the real subfield

The compositum with the prime cyclotomic field preserves the degree and
unramifiedness of a cyclic prime-degree extension of the real subfield.
Kummer reflection then gives a divisor of the relative norm kernel and
the ordinary Bernoulli numerator criterion.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9e49cf86a2f12f4c30fb1657d2e228b79f3a2a77`.
-/

public section

open NumberField IsDedekindDomain
open scoped NumberField

namespace TinyTauDemo

universe u v w

/-- Form the coprime-degree compositum of an abelian extension and an
unramified abelian extension inside an algebraic closure. -/
private theorem of_unramified_coprime_abelian_compositum
    {F : Type u} {K : Type v} {H : Type w} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field H] [NumberField H] [Algebra F K] [Algebra F H]
    [IsAbelianGalois F K] [IsAbelianGalois F H]
    (hcop : (Module.finrank F K).Coprime (Module.finrank F H))
    (hunr : ∀ x : HeightOneSpectrum (𝓞 H), Algebra.IsUnramifiedAt (𝓞 F) x.asIdeal)
    {P : Prop}
    (h : ∀ (L : Type v) [Field L] [NumberField L] [Algebra K L] [Algebra F L]
      [IsScalarTower F K L] [IsAbelianGalois F L],
      Module.finrank K L = Module.finrank F H →
      (∀ x : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) x.asIdeal) → P) : P := by
  let : FiniteDimensional F K := inferInstance
  let : FiniteDimensional F H := inferInstance
  let Ω := AlgebraicClosure K
  let i : K →ₐ[F] Ω := IsScalarTower.toAlgHom F K Ω
  let j : H →ₐ[F] Ω := IsAlgClosed.lift
  let E := i.fieldRange
  let T := j.fieldRange
  let L := ↥(E ⊔ T)
  have : FiniteDimensional F E := i.equivFieldRange.toLinearEquiv.finiteDimensional
  have : FiniteDimensional F T := j.equivFieldRange.toLinearEquiv.finiteDimensional
  have : FiniteDimensional F L := IntermediateField.finiteDimensional_sup E T
  have : NumberField L := NumberField.of_module_finite F L
  have : IsAbelianGalois F E := IsAbelianGalois.of_algHom i.equivFieldRange.symm.toAlgHom
  have : IsAbelianGalois F T := IsAbelianGalois.of_algHom j.equivFieldRange.symm.toAlgHom
  have : IsAbelianGalois F L := IsAbelianGalois.sup E T
  have hE := i.equivFieldRange.toLinearEquiv.finrank_eq
  have hT := j.equivFieldRange.toLinearEquiv.finrank_eq
  have hld : E.LinearDisjoint T :=
    IntermediateField.LinearDisjoint.of_finrank_coprime (by rwa [← hE, ← hT])
  have hL : Module.finrank F L = Module.finrank F K * Module.finrank F H := calc
    _ = Module.finrank F E * Module.finrank F T := hld.finrank_sup
    _ = _ := congrArg₂ (· * ·) hE.symm hT.symm
  let iL : K →ₐ[F] L := (IntermediateField.inclusion le_sup_left).comp i.rangeRestrict
  let jL : H →ₐ[F] L := (IntermediateField.inclusion le_sup_right).comp j.rangeRestrict
  let : Algebra K L := iL.toRingHom.toAlgebra
  let : Algebra H L := jL.toRingHom.toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' iL.comp_algebraMap.symm
  have : IsScalarTower F H L := IsScalarTower.of_algebraMap_eq' jL.comp_algebraMap.symm
  have hKL : Module.finrank K L = Module.finrank F H := by
    have hh := Module.finrank_mul_finrank F K L
    rw [hL] at hh
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos hh
  have hHL : Module.finrank H L = Module.finrank F K := by
    have hh := Module.finrank_mul_finrank F H L
    rw [hL, Nat.mul_comm (Module.finrank F K)] at hh
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos hh
  have : IsGalois K L := (IsAbelianGalois.tower_top F K L).toIsGalois
  have : IsGalois H L := (IsAbelianGalois.tower_top F H L).toIsGalois
  have hunrKL := isUnramifiedAt_of_coprime_galois_towers (E := K) (L := L)
    (show (Module.finrank K L).Coprime (Module.finrank H L) by
      simpa only [hKL, hHL] using hcop.symm) hunr
  exact h L hKL hunrKL

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
variable {H : Type*} [Field H] [NumberField H] [Algebra (maximalRealSubfield K) H]
  [IsGalois (maximalRealSubfield K) H]

/-- An unramified cyclic extension of degree p of the real subfield of a prime
cyclotomic field forces p to divide the relative class-group norm kernel. -/
theorem dvd_relativeNormKernel_of_unramified_real_extension
    (hp2 : 2 < p) (hH : Module.finrank (maximalRealSubfield K) H = p)
    (hunr : ∀ x : HeightOneSpectrum (𝓞 H),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) x.asIdeal) :
    p ∣ Nat.card (ClassGroup.relNorm
      (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker := by
  let F := ↥(maximalRealSubfield K)
  have hp : p.Prime := Fact.out
  have hKF : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hcop : (Module.finrank F K).Coprime (Module.finrank F H) := by
    rw [hKF, hH]
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hp2)).symm
  have : IsCyclic (H ≃ₐ[F] H) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank F H).trans hH)
  have : IsAbelianGalois F K := IsAbelianGalois.of_isCyclic F K
  have : IsAbelianGalois F H := IsAbelianGalois.of_isCyclic F H
  refine of_unramified_coprime_abelian_compositum hcop hunr ?_
  intro L fldL nfL algKL algFL tower hAbel hdeg hunrKL
  let algCan : Algebra F L := Algebra.ofSubsemiring (maximalRealSubfield K)
  have hAlg : algCan = algFL := Algebra.algebra_ext _ _ (fun x ↦ by
    change algebraMap K L (algebraMap F K x) = @algebraMap F L _ _ algFL x
    exact (@IsScalarTower.algebraMap_apply F K L _ _ _ _ algKL algFL tower x).symm)
  have hAbelCan : @IsAbelianGalois F L _ fldL algCan := hAlg.symm ▸ hAbel
  exact @dvd_relativeNormKernel_of_unramified_abelian_tower p _ K L _ _ fldL nfL algKL
    _ _ hAbelCan hp2 (hdeg.trans hH) hunrKL

omit [IsCMField K] in
/-- An unramified cyclic extension of degree p of the maximal real subfield
implies the ordinary Bernoulli numerator criterion at p. -/
theorem bernoulliIrregular_of_unramified_real_extension
    (hp2 : 2 < p) (hH : Module.finrank (maximalRealSubfield K) H = p)
    (hunr : ∀ x : HeightOneSpectrum (𝓞 H),
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield K)) x.asIdeal) :
    BernoulliIrregular p := by
  have : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp2⟩
  exact (dvd_cyclotomicNormKernel_iff_bernoulliIrregular K hp2).mp
    (dvd_relativeNormKernel_of_unramified_real_extension hp2 hH hunr)

end TinyTauDemo
