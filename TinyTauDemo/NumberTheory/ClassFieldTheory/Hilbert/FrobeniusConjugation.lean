/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Frobenius under conjugation in a tower

An automorphism over the bottom field permutes primes and restricts to the normal middle
field. The residue field cardinalities are preserved, so a conjugate Frobenius is the
Frobenius at the conjugate prime.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `e74e1464a9abce7e83e565c5ccdf1957b5935bc6`.
-/

public section

open NumberField IsDedekindDomain
open scoped NumberField Pointwise

namespace TinyTauDemo

variable {K E M : Type} [Field K] [Field E] [Field M] [Algebra K E] [Algebra E M]
  [Algebra K M] [IsScalarTower K E M] [Normal K E]

/-- Conjugation over the ground field preserves automorphisms over the normal middle field. -/
def scalarTowerConjugate (g : M ≃ₐ[K] M) : (M ≃ₐ[E] M) →* (M ≃ₐ[E] M) := by
  let f (σ : M ≃ₐ[E] M) : M ≃ₐ[E] M :=
    { (g * σ.restrictScalars K * g⁻¹).toRingEquiv with
      commutes' := fun x ↦ by
        change g (σ (g⁻¹ (algebraMap E M x))) = algebraMap E M x
        rw [← AlgEquiv.restrictNormal_commutes g⁻¹ E, σ.commutes,
          AlgEquiv.restrictNormal_commutes]
        exact g.apply_symm_apply _ }
  have hf (σ : M ≃ₐ[E] M) :
      (f σ).restrictScalars K = g * σ.restrictScalars K * g⁻¹ := rfl
  exact {
    toFun := f
    map_one' := AlgEquiv.restrictScalars_injective K (by
      change (f 1).restrictScalars K = 1
      rw [hf]
      change g * (AlgEquiv.restrictScalarsHom K) (1 : M ≃ₐ[E] M) * g⁻¹ = 1
      rw [map_one, mul_one, mul_inv_cancel])
    map_mul' := fun σ τ ↦ AlgEquiv.restrictScalars_injective K (by
      change (f (σ * τ)).restrictScalars K =
        (f σ).restrictScalars K * (f τ).restrictScalars K
      simp only [hf]
      change g * (AlgEquiv.restrictScalarsHom K) (σ * τ) * g⁻¹ =
        (g * σ.restrictScalars K * g⁻¹) * (g * τ.restrictScalars K * g⁻¹)
      rw [map_mul]
      group
      rfl) }

/-- The ambient restriction of relative conjugation is the ordinary group conjugation. -/
theorem scalarTowerConjugate_restrictScalars (g : M ≃ₐ[K] M) (σ : M ≃ₐ[E] M) :
    ((scalarTowerConjugate g) σ).restrictScalars K =
      g * σ.restrictScalars K * g⁻¹ := by
  rw [scalarTowerConjugate]
  rfl

/-- Contracting a conjugate prime to a normal intermediate field gives the conjugate contracted
prime, under the restricted automorphism. -/
theorem under_smul_restrictNormal_of_tower (g : M ≃ₐ[K] M) (Q : Ideal (𝓞 M)) :
    (g • Q).under (𝓞 E) = g.restrictNormal E • Q.under (𝓞 E) := by
  ext x
  simp only [Ideal.under_def, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [← algebraMap_restrictNormal_smul]
  have hg : (g⁻¹).restrictNormal E = (g.restrictNormal E)⁻¹ :=
    map_inv (AlgEquiv.restrictNormalHom E) g
  rw [hg]

private theorem natCard_quotient_under_smul_restrictNormal (g : M ≃ₐ[K] M)
    (Q : Ideal (𝓞 M)) :
    Nat.card (𝓞 E ⧸ (g • Q).under (𝓞 E)) = Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) := by
  rw [under_smul_restrictNormal_of_tower]
  let P : Ideal (𝓞 E) := Q.under (𝓞 E)
  let a : E ≃ₐ[K] E := g.restrictNormal E
  let f : 𝓞 E ≃+* 𝓞 E := MulSemiringAction.toRingEquiv (E ≃ₐ[K] E) (𝓞 E) a
  change Nat.card (𝓞 E ⧸ a • P) = Nat.card (𝓞 E ⧸ P)
  have hf : a • P = P.map f := Ideal.pointwise_smul_def P
  let ef : (𝓞 E ⧸ P) ≃+* (𝓞 E ⧸ a • P) := Ideal.quotientEquiv P (a • P) f hf
  exact Nat.card_congr ef.symm.toEquiv

private theorem scalarTowerConjugate_smul (g : M ≃ₐ[K] M) (σ : M ≃ₐ[E] M)
    (x : 𝓞 M) :
    scalarTowerConjugate g σ • x = g • (σ • (g⁻¹ • x)) := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul_eq_apply]
  rw [← AlgEquiv.restrictScalars_apply K (scalarTowerConjugate g σ),
    scalarTowerConjugate_restrictScalars]
  rfl

/-- Conjugating arithmetic Frobenius over a normal intermediate field produces arithmetic
Frobenius at the conjugate prime. -/
theorem isArithFrobAt_scalarTowerConjugate {g : M ≃ₐ[K] M} {σ : M ≃ₐ[E] M}
    {Q : Ideal (𝓞 M)} (hQ : IsArithFrobAt (𝓞 E) σ Q) :
    IsArithFrobAt (𝓞 E) (scalarTowerConjugate g σ) (g • Q) := by
  intro x
  change scalarTowerConjugate g σ • x -
      x ^ Nat.card (𝓞 E ⧸ (g • Q).under (𝓞 E)) ∈ g • Q
  rw [natCard_quotient_under_smul_restrictNormal, scalarTowerConjugate_smul,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, smul_pow', inv_smul_smul]
  exact hQ (g⁻¹ • x)

private theorem injective_scalarTowerConjugate (g : M ≃ₐ[K] M) :
    Function.Injective (scalarTowerConjugate (E := E) g) := by
  intro a b h
  apply AlgEquiv.restrictScalars_injective K
  apply (MulAut.conj g).injective
  have hh := congrArg (fun σ : M ≃ₐ[E] M ↦ σ.restrictScalars K) h
  rw [scalarTowerConjugate_restrictScalars, scalarTowerConjugate_restrictScalars] at hh
  exact hh

private theorem scalarTowerConjugate_mem_inertia (g : M ≃ₐ[K] M) (σ : M ≃ₐ[E] M)
    (Q : Ideal (𝓞 M)) (hh : σ ∈ Q.inertia (M ≃ₐ[E] M)) :
    scalarTowerConjugate g σ ∈ (g • Q).inertia (M ≃ₐ[E] M) := by
  apply Ideal.mem_inertia.mpr
  intro x
  rw [scalarTowerConjugate_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    smul_sub, inv_smul_smul]
  exact (Ideal.mem_inertia.mp hh) (g⁻¹ • x)

/-- Ambient conjugation preserves unramifiedness over the normal middle field. -/
theorem isUnramifiedAt_smul_of_normal_scalarTower [NumberField E] [NumberField M] [IsGalois E M]
    (g : M ≃ₐ[K] M) (Q : Ideal (𝓞 M)) [Q.IsPrime]
    (h : Algebra.IsUnramifiedAt (𝓞 E) Q) :
    Algebra.IsUnramifiedAt (𝓞 E) (g • Q : Ideal (𝓞 M)) := by
  rw [Ideal.isUnramifiedAt_iff_inertia_eq_bot] at h ⊢
  apply le_antisymm _ bot_le
  intro σ hσ
  have hc : scalarTowerConjugate g⁻¹ σ ∈ Q.inertia (M ≃ₐ[E] M) := by
    simpa only [inv_smul_smul] using scalarTowerConjugate_mem_inertia g⁻¹ σ (g • Q) hσ
  rw [h, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.mpr
    (injective_scalarTowerConjugate g⁻¹ (hc.trans (map_one _).symm))

/-- The height-one prime obtained by conjugating its underlying ideal. -/
def conjugateHeightOnePrime (g : M ≃ₐ[K] M) (Q : HeightOneSpectrum (𝓞 M)) :
    HeightOneSpectrum (𝓞 M) :=
  ⟨g • Q.asIdeal, inferInstance, fun h ↦
    Q.ne_bot (MulAction.injective g (by simpa only [smul_bot] using h))⟩

@[simp]
theorem conjugateHeightOnePrime_asIdeal (g : M ≃ₐ[K] M) (Q : HeightOneSpectrum (𝓞 M)) :
    (conjugateHeightOnePrime g Q).asIdeal = g • Q.asIdeal := by
  rw [conjugateHeightOnePrime]

omit [Normal K E] in
/-- An ambient conjugate gives the same base prime after contraction through the intermediate
field. -/
theorem conjugateHeightOnePrime_under_under [NumberField K] [NumberField E] [NumberField M]
    (g : M ≃ₐ[K] M) (Q : HeightOneSpectrum (𝓞 M)) :
    ((conjugateHeightOnePrime g Q).under (𝓞 E)).under (𝓞 K) =
      (Q.under (𝓞 E)).under (𝓞 K) := by
  apply HeightOneSpectrum.ext
  change ((g • Q.asIdeal).under (𝓞 E)).under (𝓞 K) =
    (Q.asIdeal.under (𝓞 E)).under (𝓞 K)
  rw [Ideal.under_under, Ideal.under_under, Ideal.under_smul]

end TinyTauDemo
