/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The local tame differential length

For a local map of smooth curve rings the differential of a uniformizer
pulls back to a unit times the uniformizer to the ramification exponent
minus one. The transitivity sequence identifies the relative differentials
with the quotient by that power of the maximal ideal.
See `/roadmap/index.qmd#thm-riemann-hurwitz-recall @ 86aa35292310f4aab67f58a8b69693bf1ec59284`.
-/

public section

open KaehlerDifferential IsLocalRing
open scoped TensorProduct

namespace TinyTauDemo

private theorem range_mapBaseChange_of_span_eq_top {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    {t : A} (ht : Submodule.span A {D k A t} = ⊤) :
    LinearMap.range (KaehlerDifferential.mapBaseChange k A B) =
      Submodule.span B {D k B (algebraMap A B t)} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine TensorProduct.inductionOn x (motive := fun y ↦
      mapBaseChange k A B y ∈ Submodule.span B {D k B (algebraMap A B t)}) ?_ ?_
    · intro b y
      have hy : y ∈ Submodule.span A {D k A t} := by rw [ht]; trivial
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [← TensorProduct.smul_tmul, mapBaseChange_tmul, KaehlerDifferential.map_D]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨1 ⊗ₜ[A] D k A t, by simp⟩

/-- If the residue characteristic does not divide the exponent, differentiating
a unit times a uniformizer to that exponent lowers the uniformizer order by one. -/
theorem differential_unit_mul_uniformizer_pow {k B : Type*}
    [CommRing k] [CommRing B] [Algebra k B] [IsDomain B] [IsDiscreteValuationRing B]
    {u : B} (hu : Irreducible u) (coord : Ω[B⁄k] ≃ₗ[B] B)
    (hcoord : coord (D k B u) = 1) {e : ℕ} (he : 0 < e)
    (heunit : IsUnit (e : B)) (v : Bˣ) :
    ∃ w : Bˣ, coord (D k B ((v : B) * u ^ e)) = (w : B) * u ^ (e - 1) := by
  let c := (e : B) * (v : B) + u * coord (D k B (v : B))
  have hu_mem : u ∈ maximalIdeal B := by
    rw [hu.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hc : IsUnit c := by
    apply notMem_maximalIdeal.mp
    intro h
    have hx : (e : B) * (v : B) ∈ maximalIdeal B := by
      simpa only [c, add_sub_cancel_right] using
        (maximalIdeal B).sub_mem h ((maximalIdeal B).mul_mem_right (coord (D k B (v : B))) hu_mem)
    exact (notMem_maximalIdeal.mpr (heunit.mul v.isUnit)) hx
  have hpow : coord (D k B (u ^ e)) = (e : B) * u ^ (e - 1) := by
    rw [(D k B).leibniz_pow, map_nsmul, map_smul, hcoord, smul_eq_mul, mul_one, nsmul_eq_mul]
  refine ⟨hc.unit, ?_⟩
  rw [hc.unit_spec, (D k B).leibniz, map_add]
  simp only [map_smul, hpow, smul_eq_mul]
  rw [show u ^ e = u ^ (e - 1) * u from by
    rw [← pow_succ, Nat.sub_add_cancel he]]
  dsimp only [c]
  ring

/-- At a tame map of local curve rings, the relative Kähler differential module
is the quotient by the maximal ideal to the ramification exponent minus one.
The assumptions on the two parameters state that their differentials generate
the absolute differential modules, as they do at smooth rational points. -/
noncomputable def relativeKaehlerDifferentialEquivQuotient {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsDomain B] [IsDiscreteValuationRing B]
    {t : A} {u : B} (hu : Irreducible u) (ht : Submodule.span A {D k A t} = ⊤)
    (coord : Ω[B⁄k] ≃ₗ[B] B) (hcoord : coord (D k B u) = 1)
    {e : ℕ} (he : 0 < e) (heunit : IsUnit (e : B)) (v : Bˣ)
    (hmap : algebraMap A B t = (v : B) * u ^ e) :
    Ω[B⁄A] ≃ₗ[B] B ⧸ maximalIdeal B ^ (e - 1) := by
  let g := KaehlerDifferential.map k A B B
  let f := g.comp coord.symm.toLinearMap
  have hsur : Function.Surjective f := (KaehlerDifferential.map_surjective k A B).comp
    coord.symm.surjective
  have hker : LinearMap.ker g = Submodule.span B {D k B (algebraMap A B t)} := by
    rw [← KaehlerDifferential.range_mapBaseChange]
    exact range_mapBaseChange_of_span_eq_top ht
  have hker' : LinearMap.ker f = (maximalIdeal B ^ (e - 1) : Ideal B) := calc
    LinearMap.ker f = (LinearMap.ker g).map coord.toLinearMap := by
      ext r
      constructor
      · intro hr
        exact ⟨coord.symm r, hr, coord.apply_symm_apply r⟩
      · rintro ⟨y, hy, rfl⟩
        change g (coord.symm (coord y)) = 0
        rwa [coord.symm_apply_apply, ← LinearMap.mem_ker]
    _ = Ideal.span {coord (D k B (algebraMap A B t))} := by
      rw [hker, Submodule.map_span, Set.image_singleton]
      rfl
    _ = (maximalIdeal B ^ (e - 1) : Ideal B) := by
      obtain ⟨w, hw⟩ := differential_unit_mul_uniformizer_pow hu coord hcoord he heunit v
      rw [hmap, hw, ← Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_eq_top.mpr w.isUnit, Ideal.top_mul, ← Ideal.span_singleton_pow,
        ← hu.maximalIdeal_eq]
  exact (f.quotKerEquivOfSurjective hsur).symm.trans (Submodule.quotEquivOfEq _ _ hker')

/-- Over a discrete valuation ring of residue characteristic zero, the local
relative differential module has length equal to the ramification exponent minus one. -/
theorem length_relativeKaehlerDifferential_of_charZero_residueField {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsDomain B] [IsDiscreteValuationRing B] [CharZero (ResidueField B)]
    {t : A} {u : B} (hu : Irreducible u) (ht : Submodule.span A {D k A t} = ⊤)
    (coord : Ω[B⁄k] ≃ₗ[B] B) (hcoord : coord (D k B u) = 1)
    {e : ℕ} (he : 0 < e) (v : Bˣ) (hmap : algebraMap A B t = (v : B) * u ^ e) :
    Module.length B Ω[B⁄A] = ↑(e - 1 : ℕ) := by
  have heunit : IsUnit (e : B) := by
    apply notMem_maximalIdeal.mp
    intro he_mem
    have hzero := (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal B)).mpr he_mem
    change algebraMap B (ResidueField B) (e : B) = 0 at hzero
    rw [map_natCast] at hzero
    exact (Nat.cast_ne_zero.mpr he.ne') hzero
  rw [(relativeKaehlerDifferentialEquivQuotient hu ht coord hcoord he heunit v hmap).length_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- Over a local ring with finite differentials and formally unramified
residue field, the differential of a generator of the maximal ideal generates
the module of differentials. -/
theorem span_differential_uniformizer_eq_top {k B : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [IsDomain B] [IsDiscreteValuationRing B] [Module.Finite B Ω[B⁄k]]
    (hres : Subsingleton Ω[ResidueField B⁄k]) {u : B} (hu : Irreducible u) :
    Submodule.span B {D k B u} = ⊤ := by
  let F := B ⧸ maximalIdeal B
  have : Subsingleton Ω[F⁄k] := hres
  let I := RingHom.ker (algebraMap B F)
  let l := KaehlerDifferential.kerCotangentToTensor k B F
  have hI : I = Ideal.span {u} := by
    change RingHom.ker (Ideal.Quotient.mk (maximalIdeal B)) = _
    rw [Ideal.mk_ker, hu.maximalIdeal_eq]
  have hs : Function.Surjective l := by
    apply LinearMap.range_eq_top.mp
    have hrange : LinearMap.range l =
        (LinearMap.ker (KaehlerDifferential.mapBaseChange k B F)).restrictScalars B :=
      KaehlerDifferential.range_kerCotangentToTensor k B F Ideal.Quotient.mk_surjective
    have hker : LinearMap.ker (KaehlerDifferential.mapBaseChange k B F) = ⊤ := by
      rw [LinearMap.ker_eq_top]
      exact Subsingleton.elim _ _
    rw [hrange, hker, Submodule.restrictScalars_top]
  let q := (maximalIdeal B • (⊤ : Submodule B Ω[B⁄k])).mkQ
  let E := TensorProduct.quotTensorEquivQuotSMul Ω[B⁄k] (maximalIdeal B)
  let f := LinearMap.toSpanSingleton B Ω[B⁄k] (D k B u)
  have hq (z : I) : E (l (I.toCotangent z)) = q (D k B z) := by
    change E (KaehlerDifferential.kerCotangentToTensor k B F (I.toCotangent z)) = _
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ _
  have hsur : Function.Surjective (q.comp f) := by
    intro y
    obtain ⟨c, hc⟩ := hs (E.symm y)
    obtain ⟨z, rfl⟩ := I.toCotangent_surjective c
    have hz : (z : B) ∈ Ideal.span {u} := hI ▸ z.prop
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hz
    let z₀ : I := ⟨u, hI.symm ▸ Ideal.mem_span_singleton_self u⟩
    have hz' : b • z₀ = z := Subtype.ext hb
    refine ⟨b, ?_⟩
    have hh := congrArg E hc
    rw [E.apply_symm_apply, ← hz', map_smul, map_smul, map_smul, hq] at hh
    change q (b • D k B u) = y
    rw [map_smul]
    exact hh
  have hf : Function.Surjective f := LinearMap.surjective_of_surjective_comp_mkQ f
    (maximalIdeal B) (maximalIdeal_le_jacobson ⊥) hsur
  rw [← LinearMap.range_toSpanSingleton]
  exact LinearMap.range_eq_top.mpr hf

/-- For a local map of DVRs sending a base uniformizer to a nonzero element,
the relative differential length is one less than the valuation of its image.
The differential generator hypotheses hold for smooth curve local rings. -/
theorem length_relativeKaehlerDifferential_eq_addVal_sub_one {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsLocalHom (algebraMap A B)] [CharZero (ResidueField B)]
    {t : A} {u : B} (ht : Irreducible t) (hu : Irreducible u)
    (ht₁ : Submodule.span A {D k A t} = ⊤) (ht₂ : algebraMap A B t ≠ 0)
    (coord : Ω[B⁄k] ≃ₗ[B] B) (hcoord : coord (D k B u) = 1) :
    Module.length B Ω[B⁄A] =
      ↑((IsDiscreteValuationRing.addVal B (algebraMap A B t)).toNat - 1 : ℕ) := by
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht₂ hu
  have hpos : 0 < e := by
    by_contra! h
    have he : e = 0 := by omega
    rw [he, pow_zero, mul_one] at hv
    exact ht.not_isUnit (isUnit_of_map_unit (algebraMap A B) t (hv.symm ▸ v.isUnit))
  rw [IsDiscreteValuationRing.addVal_def _ v hu e hv, ENat.toNat_natCast]
  exact length_relativeKaehlerDifferential_of_charZero_residueField
    hu ht₁ coord hcoord hpos v hv

/-- For the local map of DVRs, the differential generators are automatic
when the differential modules are finite, the residue differentials vanish,
and the target differential module is torsion-free and nonzero. -/
theorem length_relativeKaehlerDifferential_eq_addVal_sub_one_of_finite {k A B : Type*}
    [CommRing k] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsLocalHom (algebraMap A B)] [CharZero (ResidueField B)]
    [Module.Finite A Ω[A⁄k]] [Module.Finite B Ω[B⁄k]]
    [Module.IsTorsionFree B Ω[B⁄k]] [Nontrivial Ω[B⁄k]]
    (hA : Subsingleton Ω[ResidueField A⁄k]) (hB : Subsingleton Ω[ResidueField B⁄k])
    {t : A} {u : B} (ht : Irreducible t) (hu : Irreducible u)
    (ht₂ : algebraMap A B t ≠ 0) :
    Module.length B Ω[B⁄A] =
      ↑((IsDiscreteValuationRing.addVal B (algebraMap A B t)).toNat - 1 : ℕ) := by
  have hgen := span_differential_uniformizer_eq_top hB hu
  have hne : D k B u ≠ 0 := by
    intro h
    rw [h, Submodule.span_singleton_eq_bot.mpr rfl] at hgen
    exact bot_ne_top hgen
  let f := LinearMap.toSpanSingleton B Ω[B⁄k] (D k B u)
  have hf : Function.Bijective f :=
    ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton B hne),
      LinearMap.range_eq_top.mp ((LinearMap.range_toSpanSingleton (D k B u)).trans hgen)⟩
  let coord := (LinearEquiv.ofBijective f hf).symm
  have hcoord : coord (D k B u) = 1 := by
    apply coord.symm.injective
    rw [coord.symm_apply_apply]
    exact (LinearMap.toSpanSingleton_apply_one _ _ _).symm
  exact length_relativeKaehlerDifferential_eq_addVal_sub_one ht hu
    (span_differential_uniformizer_eq_top hA ht) ht₂ coord hcoord

end TinyTauDemo
