/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.KummerNormIndex
public import TinyTauDemo.KummerFrobeniusBasis
public import TinyTauDemo.KummerFrobeniusPower
public import TinyTauDemo.KummerUnitSurjectivity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# The second fundamental inequality for S-unit Kummer subfields

The ordinary S-unit Kummer field supplies auxiliary Frobenius basis places.
They give the local unit approximation required by the auxiliary idele index
computation, which bounds the norm index by the degree of the subfield.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField IntermediateField TauCeti TauCeti.GlobalNumberFields
  TauCeti.NumberFieldArithmetic
open scoped NumberField AdicCompletionExtension IsMulCommutative

namespace TinyTauDemo

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [HasEnoughRootsOfUnity K p]

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)

local notation "U" => Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "M" => kummerField (SeparableClosure K) p U

include hpS in
/-- If S contains the primes above p and its classes generate the class group,
the norm index of any subfield of the S-unit exponent-p Kummer field divides
the degree of that subfield. -/
theorem index_range_ideleClassNormMap_dvd_finrank_of_kummerField_sUnits
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (L : IntermediateField K M) [NumberField L] :
    (ideleClassNormMap K L).range.index ∣ Module.finrank K L := by
  classical
  have : IsAbelianGalois K L := IsAbelianGalois.tower_bot K L M
  have : Normal K L := inferInstance
  obtain ⟨T, hST, hgen, hsize, hdegree⟩ := exists_finset_frobeniusBasis_kummerField_sUnits S hpS L
  have havoid (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T) : (p : 𝓞 K) ∉ v.asIdeal :=
    fun he ↦ Finset.disjoint_left.mp hST (hpS v he) hv
  have hroots (a : Kˣ) : ∃ x : SeparableClosure K, x ^ p = algebraMap K (SeparableClosure K) a :=
    IsAlgClosed.exists_pow_nat_eq _ hp.out.pos
  have hrootsM (a : Kˣ) (ha : a ∈ U) : ∃ x : M, x ^ p = algebraMap K M a := by
    obtain ⟨x, hx⟩ := hroots a
    exact ⟨⟨x, mem_kummerField_of_pow_eq ha hx⟩, Subtype.ext hx⟩
  have hgenM : kummerField M p U = ⊤ := by
    rw [kummerField_def (K := K) (E := M) (n := p) (Δ := U)]
    exact adjoin_pow_eq_algebraMap_kummerField_eq_top
      (K := K) (E := SeparableClosure K) (n := p) (Δ := U)
  have hlocal (a : Kˣ) (ha : a ∈ U) :
      (∀ v ∈ T, ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) a) ↔
        ∃ b : L, b ^ p = algebraMap K L a := by
    obtain ⟨r, hr⟩ := hrootsM a ha
    exact exists_local_pow_iff_exists_intermediate_pow_of_frobeniusBasis
      (fun (σ τ : M ≃ₐ[K] M) ↦ by
        change σ * τ = τ * σ
        exact mul_comm σ τ) S T hST (kummerField_sUnits_isUnramifiedAt_of_not_mem S hpS)
      hgen hdegree hr
  have hs := unitLocalPowerClassMap_surjective_of_local_roots_of_finrank
    S T hST havoid hgenM hrootsM hlocal hsize.symm
  have hexpM := exponent_algEquiv_kummerField_dvd K (SeparableClosure K) p U
  have hexp : Monoid.exponent Gal(L/K) ∣ p :=
    (MonoidHom.exponent_dvd (f := AlgEquiv.restrictNormalHom L)
      (AlgEquiv.restrictNormalHom_surjective M)).trans hexpM
  have hur : ∀ v ∉ S, v ∉ T →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
    intro v hv _
    obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 M) v
    let v := w.under (𝓞 K)
    let q := w.under (𝓞 L)
    have hq : q.asIdeal.LiesOver v.asIdeal := ⟨(Ideal.under_under w.asIdeal).symm⟩
    have : w.asIdeal.LiesOver v.asIdeal := inferInstance
    have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
      kummerField_sUnits_isUnramifiedAt_of_not_mem S hpS v hv w.asIdeal
    exact ⟨⟨q, hq⟩, Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) q.asIdeal w.asIdeal⟩
  have hdM : Module.finrank K M = p ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [show Module.finrank K M = (powMonoidHom p : Kˣ →* Kˣ).range.relIndex U from
      finrank_kummerField (E := SeparableClosure K) (n := p) (Δ := U) (fun a _ ↦ hroots a)]
    rw [relIndex_range_powMonoidHom_sUnits_numberField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, add_comm]
  apply index_norm_dvd_finrank_of_auxiliary_unit_powers L S T hST hcl hpS
    (exists_sUnit_of_surjective_unitLocalPowerClassMap S T hST hs) hexp hdegree hur
  let : Module.Free L M := Module.Free.of_divisionRing L M
  rw [hsize, Module.finrank_mul_finrank K L M, hdM]

end TinyTauDemo
