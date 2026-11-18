/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.NumberTheory.NumberField.Frobenius.SplitBasis
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import TauCeti.FieldTheory.Kummer.Degree

/-!
# Detecting a Kummer root by a Frobenius basis

A fixed radical lies in the intermediate field precisely when it has a root
in every completion selected by the Frobenius basis.

See J. S. Milne, *Class Field Theory*, VII, Lemma 6.3.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField TauCeti.NumberFieldArithmetic
open scoped NumberField AdicCompletionExtension

namespace TinyTauDemo

variable {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [IsGalois K M]

/-- A radical in M has a root in the intermediate field L if and only if it has a
root in each completion indexed by a Frobenius basis for M/L. The chosen places
of L above that basis have local degree one. This is Milne VII, Lemma 6.3. -/
theorem exists_local_pow_iff_exists_intermediate_pow_of_frobeniusBasis
    {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    (hab : ∀ σ τ : M ≃ₐ[K] M, Commute σ τ)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (hgen : Subgroup.closure (artinElementAway hab S hur '' T) =
      (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range)
    (hdeg : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    {a : K} {r : M} (hr : r ^ n = algebraMap K M a) :
    (∀ v ∈ T, ∃ c : v.adicCompletion K, c ^ n = algebraMap K (v.adicCompletion K) a) ↔
      ∃ b : L, b ^ n = algebraMap K L a := by
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  constructor
  · intro hc
    have hstab : Subgroup.closure (artinElementAway hab S hur '' T) ≤
        MulAction.stabilizer (M ≃ₐ[K] M) r := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 M) v
      let v := w.under (𝓞 K)
      have hw : w.asIdeal.LiesOver v.asIdeal := inferInstance
      have hvS : v ∉ S := fun h ↦ Finset.disjoint_left.mp hST h hv
      have hf := isArithFrobAt_artinElementAway hab S hur hvS w.asIdeal
      obtain ⟨c, hcv⟩ := hc v hv
      have hpow : (algebraMap M (w.adicCompletion M) r) ^ n =
          algebraMap K (w.adicCompletion M) a := by
        rw [← map_pow, hr, ← IsScalarTower.algebraMap_apply]
      have hg := TauCeti.mem_range_algebraMap_of_pow_eq hpow hcv
      change artinElementAway hab S hur v ∈ MulAction.stabilizer (M ≃ₐ[K] M) r
      apply MulAction.mem_stabilizer_iff.mpr
      exact HeightOneSpectrum.apply_eq_self_of_algebraMap_mem_range
        ⟨_, hf.mem_stabilizer⟩ hg
    rw [hgen] at hstab
    have hrange : r ∈ (algebraMap L M).range :=
      (IsGalois.mem_range_algebraMap_iff_fixed r).mpr fun σ ↦ by
        have hs := hstab (show (AlgEquiv.restrictScalarsHom K) σ ∈ _ from ⟨σ, rfl⟩)
        exact (MulAction.mem_stabilizer_iff.mp hs)
    obtain ⟨b, hb⟩ := hrange
    exact ⟨b, (algebraMap L M).injective (by
      rw [map_pow, hb, hr, ← IsScalarTower.algebraMap_apply])⟩
  · rintro ⟨b, hb⟩ v hv
    obtain ⟨w, hw⟩ := hdeg v hv
    let : w.1.asIdeal.LiesOver v.asIdeal := w.property
    obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hw).surjective
      (algebraMap L (w.1.adicCompletion L) b)
    exact ⟨c, (algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective (by
      rw [map_pow, hc, ← map_pow, hb, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply])⟩

end TinyTauDemo
