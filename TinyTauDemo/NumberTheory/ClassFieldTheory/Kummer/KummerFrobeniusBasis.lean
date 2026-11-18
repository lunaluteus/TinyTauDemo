/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
public import TauCeti.NumberTheory.NumberField.Frobenius.SplitBasis
public import TauCeti.NumberTheory.NumberField.Kummer.Unramified
import TauCeti.RingTheory.DedekindDomain.SInteger.Rank
import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# A Frobenius basis for the Kummer field of S-units

The first fundamental inequality supplies the Frobenius generation hypothesis
in the basis extraction. For the Kummer field of S-units, every place outside S
is unramified when S contains the places above the prime exponent.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField TauCeti.NumberFieldArithmetic
open scoped AdicCompletionExtension NumberField

namespace TinyTauDemo

/-- A finite set of primes containing those above a nonzero integer and whose classes
generate the ordinary class group. -/
theorem exists_finset_classGroup_generators_containing_natCast
    (K : Type*) [Field K] [NumberField K] (n : ℕ) [NeZero n] :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      Subgroup.closure (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) =
        ⊤ ∧ ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S := by
  classical
  have hn : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hI : (Ideal.span {(n : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    simpa using hn
  let T := {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}
  have hT : T.Finite := by
    simpa only [T, ← Ideal.dvd_span_singleton] using Ideal.finite_factors hI
  obtain ⟨V, hV, hc⟩ := ClassGroup.exists_finite_closure_classGroupMk_image_eq_top
    (R := 𝓞 K)
  let S := (hV.union hT).toFinset
  have hSV : V ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) := by
    simpa only [S, Set.Finite.coe_toFinset] using Set.subset_union_left
  refine ⟨S, eq_top_mono (Subgroup.closure_mono (Set.image_mono hSV)) hc, fun v hv ↦ ?_⟩
  change v ∈ (hV.union hT).toFinset
  rw [Set.Finite.mem_toFinset]
  exact Or.inr hv

section General

variable {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [IsGalois K M]

/-- Frobenius basis at split primes for the top of an exponent-prime abelian tower. -/
theorem exists_finset_frobeniusBasis_of_prime_exponent {p : ℕ} (hp : p.Prime)
    (hexp : Monoid.exponent (M ≃ₐ[K] M) ∣ p)
    (hab : ∀ σ τ : M ≃ₐ[K] M, Commute σ τ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      Subgroup.closure (artinElementAway hab S hur '' T) =
        (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range ∧
      p ^ T.card = Module.finrank L M ∧
      ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 := by
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let r : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M) := AlgEquiv.restrictScalarsHom K
  have hr : Function.Injective r := AlgEquiv.restrictScalarsHom_injective K
  have : Group.IsSolvable (M ≃ₐ[L] M) := Group.isSolvable_of_comm fun σ τ ↦
    hr (by simpa only [map_mul] using (hab (r σ) (r τ)).eq)
  exact TauCeti.NumberField.exists_finset_closure_artinElementAway_eq_range_restrictScalarsHom
    hp hexp hab S hur
    (TauCeti.ClassFieldTheory.closure_isArithFrobAt_eq_top_tower (L := L) (M := M) S)

end General

section Kummer

open TauCeti IntermediateField

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] (Δ : Subgroup Kˣ)

/-- The exponent of the automorphism group of a Kummer field divides the
degree of the radicals used to construct it. -/
theorem exponent_algEquiv_kummerField_dvd :
    Monoid.exponent (kummerField E n Δ ≃ₐ[K] kummerField E n Δ) ∣ n := by
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun σ ↦ ?_
  apply AlgEquiv.coe_toAlgHom_injective
  refine algHom_ext_of_eq_adjoin K kummerField_def fun x ⟨a, ha, hx⟩ ↦ ?_
  let y : kummerField E n Δ := ⟨x, mem_kummerField_of_pow_eq ha hx⟩
  have hy : y ^ n = algebraMap K (kummerField E n Δ) a := Subtype.ext (by simpa using hx)
  have hy0 := ne_zero_of_pow_eq_algebraMap hy
  let χ : (kummerField E n Δ ≃ₐ[K] kummerField E n Δ) →* kummerField E n Δ :=
    { toFun τ := τ y / y
      map_one' := div_self hy0
      map_mul' τ ρ := τ.mul_apply_div_self_of_pow_eq ρ hy }
  have hc : χ (σ ^ n) = 1 := by
    rw [map_pow]
    change (σ y / y) ^ n = 1
    rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self ((map_ne_zero _).mpr a.ne_zero)]
  exact (div_eq_one_iff_eq hy0).mp hc

end Kummer

section SUnits

open TauCeti IntermediateField
open scoped IsMulCommutative

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [HasEnoughRootsOfUnity K p]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)

local notation "M" => kummerField (SeparableClosure K) p
  (Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K)

include hpS in
/-- The maximal Kummer field of S-units is unramified outside S if S contains the primes
over the exponent. -/
theorem kummerField_sUnits_isUnramifiedAt_of_not_mem (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S) (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  TauCeti.NumberField.isUnramifiedIn_kummerField_of_valuation_eq_one
    (E := SeparableClosure K) (Δ := Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K)
    (fun h ↦ hv (hpS v h))
    (fun _ ha ↦ (Set.mem_unit_iff _ K).mp ha v hv) Q inferInstance inferInstance

/-- Milne's Frobenius basis for the S-unit Kummer field over an arbitrary
intermediate field. -/
theorem exists_finset_frobeniusBasis_kummerField_sUnits
    (L : IntermediateField K M) [NumberField L] :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      Subgroup.closure
        (artinElementAway (fun σ τ : M ≃ₐ[K] M ↦ mul_comm σ τ) S
          (kummerField_sUnits_isUnramifiedAt_of_not_mem S hpS) '' T) =
        (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range ∧
      p ^ T.card = Module.finrank L M ∧
      ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1 :=
  exists_finset_frobeniusBasis_of_prime_exponent hp.out
    (exponent_algEquiv_kummerField_dvd K (SeparableClosure K) p _)
    (fun σ τ ↦ mul_comm σ τ) S (kummerField_sUnits_isUnramifiedAt_of_not_mem S hpS)

end SUnits

end TinyTauDemo
