/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.Unramified.Locus
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic

/-!
# Unramified cyclic extensions and the class number

At the finite places, the local norm criterion supplies norms of units in
unramified extensions. The ordinary class group controls the remaining
idele classes. Coprimality with the extension degree makes every idele
class a norm, so the first fundamental inequality forces degree one.

See `/roadmap/index.qmd#rem-kummer-unit-proof` @ `ccf9193b87c3db948557ea5cf0a099894deb3498`.

The proof uses Tau Ceti's finite-idèle description of the class group,
the placewise norm criterion, and the first fundamental inequality for
cyclic extensions.
-/

public section

open NumberField IsDedekindDomain TauCeti TauCeti.GlobalNumberFields
open scoped NumberField

namespace TinyTauDemo

section FiniteUnitRepresentatives

variable {K : Type} [Field K] [NumberField K]

/-- When an exponent is coprime to the class number, an idele class is a product of a power
of that exponent and the class of an idele that is a unit at every finite place. -/
private theorem exists_idele_finite_units_mul_pow_of_coprime_classNumber
    (x : IdeleGroup (𝓞 K) K) {d : ℕ} (hcop : d.Coprime (classNumber K)) :
    ∃ (z : IdeleGroup (𝓞 K) K) (m : ℕ),
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (v.ideleFiniteCoord z : v.adicCompletion K) = 1) ∧
      (x : IdeleClassGroup (𝓞 K) K) =
        (z : IdeleClassGroup (𝓞 K) K) * (((x : IdeleClassGroup (𝓞 K) K) ^ d) ^ m) := by
  let g := (FiniteAdeleRing.toClassGroup (𝓞 K) K).comp (IdeleGroup.toFiniteIdele (𝓞 K) K)
  let c := g x
  have hord : orderOf c ∣ classNumber K := orderOf_dvd_card
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := c) (hcop.of_dvd_right hord)
  let b := (x ^ d) ^ m
  have hb : g b = g x := by simpa only [b, c, map_pow] using hm
  have hker : IdeleGroup.toFiniteIdele (𝓞 K) K (x * b⁻¹) ∈
      FiniteAdeleRing.integralUnits (𝓞 K) K ⊔ (FiniteAdeleRing.unitEmbedding (𝓞 K) K).range := by
    rw [← FiniteAdeleRing.ker_toClassGroup, MonoidHom.mem_ker]
    change g (x * b⁻¹) = 1
    rw [map_mul, map_inv, hb, mul_inv_cancel]
  obtain ⟨f, hf, _, ⟨a, rfl⟩, hfa⟩ := Subgroup.mem_sup.mp hker
  let z := x * b⁻¹ * (IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹
  have hz : IdeleGroup.toFiniteIdele (𝓞 K) K z ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
    dsimp only [z]
    rw [map_mul, map_inv, IdeleGroup.toFiniteIdele_unitEmbedding, ← hfa, mul_inv_cancel_right]
    exact hf
  refine ⟨z, m, fun v => ?_, ?_⟩
  · have hv := FiniteAdeleRing.mem_integralUnits_iff.mp hz v
    rw [IdeleGroup.coe_toFiniteIdele] at hv
    rw [HeightOneSpectrum.coe_ideleFiniteCoord]
    exact hv
  · have ha : (IdeleGroup.unitEmbedding (𝓞 K) K a)⁻¹ ∈
        IdeleGroup.principalSubgroup (𝓞 K) K :=
      (IdeleGroup.principalSubgroup (𝓞 K) K).inv_mem ⟨a, rfl⟩
    have hb' : (b : IdeleClassGroup (𝓞 K) K) = ((x : IdeleClassGroup (𝓞 K) K) ^ d) ^ m := by
      simp only [b, QuotientGroup.mk_pow]
    rw [← hb']
    dsimp only [z]
    rw [QuotientGroup.mk_mul_of_mem _ ha, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      inv_mul_cancel_right]

end FiniteUnitRepresentatives

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem ideleClass_mem_normRange_of_finite_units
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (x : IdeleGroup (𝓞 K) K)
    (hvalued : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) :
    (x : IdeleClassGroup (𝓞 K) K) ∈ (ideleClassNormMap K L).range := by
  have hnorm : x ∈ (ideleNormMap K L).toMonoidHom.range := by
    refine (mem_range_ideleNormMap_iff K L x).mpr ⟨fun v => ?_, fun v => ?_⟩
    · obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := 𝓞 L) v.asIdeal
      have hQ0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hQ.isPrime, hQv⟩
      let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ.isPrime, hQ0⟩
      obtain ⟨u, hu, -⟩ :=
        exists_unit_preimages_of_isUnramifiedAt K L v (v.ideleFiniteCoord x) (hvalued v)
          ⟨⟨w, hQv⟩, hunr w⟩
      exact (mem_range_normUnits_adicCompletion_iff K L v _).mpr ⟨u, hu⟩
    · exact mem_range_normUnits_completion_of_isComplex L (hcomplex v) (v.ideleInfiniteCoord x)
  obtain ⟨y, hy⟩ := hnorm
  refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
  change ideleClassNormMap K L (y : IdeleClassGroup (𝓞 L) L) = (x : IdeleClassGroup (𝓞 K) K)
  rw [ideleClassNormMap_mk]
  exact congrArg (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)) hy

private theorem surjective_ideleClassNormMap_of_unramified_of_coprime_classNumber
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hcop : (Module.finrank K L).Coprime (classNumber K)) :
    Function.Surjective (ideleClassNormMap K L) := by
  intro c
  change c ∈ (ideleClassNormMap K L).range
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨z, m, hz, hclass⟩ := exists_idele_finite_units_mul_pow_of_coprime_classNumber x hcop
  have hNz := ideleClass_mem_normRange_of_finite_units K L hunr hcomplex z hz
  have hNx : (x : IdeleClassGroup (𝓞 K) K) ^ Module.finrank K L ∈ (ideleClassNormMap K L).range :=
    ⟨ideleClassExtension K L x, ideleClassNormMap_ideleClassExtension K L x⟩
  rw [hclass]
  exact (ideleClassNormMap K L).range.mul_mem hNz ((ideleClassNormMap K L).range.pow_mem hNx m)

/-- A cyclic extension over a totally imaginary number field is trivial if it is unramified
at each finite place and its degree is coprime to the class number. -/
theorem finrank_eq_one_of_unramified_cyclic_of_coprime_classNumber
    [IsGalois K L] [IsCyclic Gal(L/K)]
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (hcop : (Module.finrank K L).Coprime (classNumber K)) :
    Module.finrank K L = 1 :=
  ClassFieldTheory.finrank_eq_one_of_surjective_ideleClassNormMap K L
    (surjective_ideleClassNormMap_of_unramified_of_coprime_classNumber K L hunr hcomplex hcop)

end TinyTauDemo
