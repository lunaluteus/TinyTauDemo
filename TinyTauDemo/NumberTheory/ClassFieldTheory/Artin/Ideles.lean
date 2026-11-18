/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Artin.Finite
public import TauCeti.NumberTheory.ClassFieldTheory.Global.ArtinAtInfinitePlace
public import TauCeti.NumberTheory.ClassFieldTheory.Global.FrobeniusGeneration
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Units
import Mathlib.FieldTheory.Galois.Abelian

/-!
# The product of local Artin symbols

The local symbols of an idele are trivial at almost every finite place. Their product with the
archimedean symbols kills idele norms. Single-place ideles give the decomposition automorphisms,
so Frobenius generation gives surjectivity for solvable Galois extensions.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IsDedekindDomain TauCeti TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped NumberField NumberField.LiesOver Pointwise AdicCompletionExtension TensorProduct

namespace TinyTauDemo

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

private theorem finiteLocalArtinAt_eq_one_of_localNorm (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ)
    (hx : x ∈ (Algebra.normUnits (v.adicCompletion K) (S := v.adicCompletion K ⊗[K] L)).range) :
    finiteLocalArtinAt K L v x = 1 := by
  obtain ⟨u, hu⟩ := (mem_range_normUnits_adicCompletion_iff K L v x).mp hx
  rw [← hu, map_finprod _ (Set.toFinite _)]
  apply finprod_eq_one_of_forall_eq_one
  intro w
  let : w.1.asIdeal.LiesOver v.asIdeal := w.2
  exact finiteLocalArtinAt_eq_one_of_mem_normGroup v w.1
    (mem_normGroup_iff.mpr ⟨u w, (Algebra.coe_normUnits _ _).symm⟩)

private theorem infiniteLocalArtinAt_eq_one_of_localNorm (v : InfinitePlace K)
    (x : v.Completionˣ)
    (hx : x ∈ (Algebra.normUnits v.Completion (S := v.Completion ⊗[K] L)).range) :
    infiniteLocalArtinAt K L v x = 1 := by
  obtain ⟨u, hu⟩ := (mem_range_normUnits_completion_iff K L v x).mp hx
  rw [← hu, map_finprod _ (Set.toFinite _)]
  apply finprod_eq_one_of_forall_eq_one
  intro w
  let : w.1.LiesOver v := w.2
  exact normGroup_le_ker_infiniteLocalArtinAt v w.1
    (mem_normGroup_iff.mpr ⟨u w, (Algebra.coe_normUnits _ _).symm⟩)

/-- The finite local symbols of an idele have finite support. -/
theorem hasFiniteMulSupport_finiteLocalArtinAt_idele (x : IdeleGroup (𝓞 K) K) :
    Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) ↦ finiteLocalArtinAt K L v (v.ideleFiniteCoord x)) := by
  apply Filter.eventually_cofinite.mp
  have hx := (FiniteAdeleRing.isUnit_iff.mp (IdeleGroup.toFiniteIdele (𝓞 K) K x).isUnit).2
  filter_upwards [eventually_isUnramifiedAt_liesOver K L, hx] with v hv hu
  have hU : ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
    obtain ⟨P, hP, hPv⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
    have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
    exact ⟨⟨⟨P, hP.isPrime, hP0⟩, hPv⟩, hv _⟩
  obtain ⟨u, he, -⟩ := exists_unit_preimages_of_isUnramifiedAt K L v (v.ideleFiniteCoord x)
    (by simpa using hu) hU
  exact finiteLocalArtinAt_eq_one_of_localNorm K L v _ ((mem_range_normUnits_adicCompletion_iff
    K L v _).mpr ⟨u, he⟩)

/-- The product of all finite and infinite local Artin symbols of an idele. -/
noncomputable def ideleArtinMap :
    IdeleGroup (𝓞 K) K →* Abelianization (L ≃ₐ[K] L) where
  toFun x :=
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), finiteLocalArtinAt K L v (v.ideleFiniteCoord x)) *
      ∏ w : InfinitePlace K, infiniteLocalArtinAt K L w (w.ideleInfiniteCoord x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [finprod_mul_distrib (hasFiniteMulSupport_finiteLocalArtinAt_idele K L x)
      (hasFiniteMulSupport_finiteLocalArtinAt_idele K L y), Finset.prod_mul_distrib,
      mul_mul_mul_comm]

/-- Evaluating the global symbol takes the product over all places. -/
theorem ideleArtinMap_apply (x : IdeleGroup (𝓞 K) K) :
    ideleArtinMap K L x =
      (∏ᶠ v : HeightOneSpectrum (𝓞 K), finiteLocalArtinAt K L v (v.ideleFiniteCoord x)) *
        ∏ w : InfinitePlace K, infiniteLocalArtinAt K L w (w.ideleInfiniteCoord x) := by
  rw [ideleArtinMap]
  rfl

/-- At an idele concentrated at a finite place, the product gives that local symbol. -/
theorem ideleArtinMap_ofAdicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ideleArtinMap K L (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) = finiteLocalArtinAt K L v x := by
  rw [ideleArtinMap_apply]
  rw [finprod_eq_single _ v (fun v' hv' ↦ by
    rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hv', map_one])]
  simp

/-- Every idele norm has trivial product of local Artin symbols. -/
theorem ideleArtinMap_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    ideleArtinMap K L (ideleNormMap K L x) = 1 := by
  rw [ideleArtinMap_apply]
  simp only [finiteLocalArtinAt_eq_one_of_localNorm K L _
      _ (mem_range_normUnits_ideleFiniteCoord_ideleNormMap K L x _),
    infiniteLocalArtinAt_eq_one_of_localNorm K L _
      _ (mem_range_normUnits_ideleInfiniteCoord_ideleNormMap K L x _),
    finprod_one, Finset.prod_const_one, one_mul]

/-- The idele product surjects onto the abelianized Galois group of a solvable extension. The
finite decomposition automorphisms occur at single-place ideles and include Frobenius. -/
theorem surjective_ideleArtinMap [Group.IsSolvable (L ≃ₐ[K] L)] :
    Function.Surjective (ideleArtinMap K L) := by
  let f := ideleArtinMap K L
  have hF : (⊤ : Subgroup (L ≃ₐ[K] L)) ≤ f.range.comap Abelianization.of := by
    rw [← closure_isArithFrobAt_eq_top (K := K) (L := L) ∅, Subgroup.closure_le]
    rintro σ ⟨v, _, ⟨w, hw⟩, hσ⟩
    let : w.asIdeal.LiesOver v.asIdeal := hw
    obtain ⟨x, hx⟩ := exists_finiteLocalArtinAt_eq_decomposition v w ⟨σ, hσ.mem_stabilizer⟩
    exact ⟨IdeleGroup.ofAdicCompletion (𝓞 K) K v x,
      (ideleArtinMap_ofAdicCompletion K L v x).trans hx⟩
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  exact hF (Subgroup.mem_top z)

end TinyTauDemo
