/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Kummer.KummerSecondInequality
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.CoprimeNorm
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import TauCeti.NumberTheory.ClassFieldTheory.ClassField
import TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.Kummer.SUnitRadical

/-!
# The idele-class norm index in prime degree

The Kummer norm bound applies to all prime-degree extensions after adjoining roots of unity.
Descent through the auxiliary extension gives the norm index over the original base. The two
fundamental inequalities then give vanishing of the first idele-class cohomology of finite layers.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open IsDedekindDomain NumberField TauCeti TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open IntermediateField
open scoped NumberField

namespace TinyTauDemo

set_option maxHeartbeats 600000 in
-- Transporting the norm subgroup through the two intermediate fields needs extra reduction.
/-- For a prime-degree Galois extension of a number field containing the relevant roots of unity,
the idele-class norm index divides the degree. -/
theorem index_range_ideleClassNormMap_dvd_of_primitive_root
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] {p : ℕ} (hp : p.Prime) (hd : Module.finrank F E = p)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p) : (ideleClassNormMap F E).range.index ∣ p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : HasEnoughRootsOfUnity F p := ⟨⟨ζ, hζ⟩, rootsOfUnity.isCyclic F p⟩
  let ι : E →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let R := ι.fieldRange
  let e : E ≃ₐ[F] R := ι.equivFieldRange
  have : FiniteDimensional F R := e.toLinearEquiv.finiteDimensional
  have : NumberField R := .of_module_finite F _
  have : IsGalois F R := IsGalois.of_algEquiv e
  have hdR : Module.finrank F R = p := e.toLinearEquiv.finrank_eq.symm.trans hd
  have hcR : Nat.card Gal(R/F) = p := (IsGalois.card_aut_eq_finrank F R).trans hdR
  have : IsCyclic Gal(R/F) := isCyclic_of_prime_card hcR
  obtain ⟨T, hT, hgen⟩ := ClassGroup.exists_finite_closure_classGroupMk_image_eq_top (R := 𝓞 F)
  have hnonzero : Ideal.span ({(p : 𝓞 F)} : Set (𝓞 F)) ≠ ⊥ :=
    fun h ↦ hp.ne_zero (Nat.cast_eq_zero.mp (Ideal.span_singleton_eq_bot.mp h))
  let P := (Ideal.finite_factors hnonzero).toFinset
  let S := hT.toFinset ∪ P ∪ NumberField.Chebotarev.ramifiedPrimes F R
  have hpS (v : HeightOneSpectrum (𝓞 F)) (hv : (p : 𝓞 F) ∈ v.asIdeal) : v ∈ S := by
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Set.Finite.mem_toFinset _ |>.mpr (Ideal.dvd_iff_le.mpr
      (v.asIdeal.span_singleton_le_iff_mem.mpr hv))
  have hTS : T ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) := fun v hv ↦
    Finset.mem_union_left _ (Finset.mem_union_left _ (hT.mem_toFinset.mpr hv))
  have hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 F)))) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact Subgroup.closure_mono (Set.image_mono hTS)
  have hunr (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ (S : Set (HeightOneSpectrum (𝓞 F)))) :
      ∃ w : HeightOneSpectrum (𝓞 R),
        w.asIdeal.LiesOver v.asIdeal ∧ Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := by
    obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 F) (𝓞 R) v
    have hnr : w.under (𝓞 F) ∉ NumberField.Chebotarev.ramifiedPrimes F R :=
      fun h ↦ hv (Finset.mem_union_right _ (hw ▸ h))
    exact ⟨w, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩,
      (NumberField.Chebotarev.under_notMem_ramifiedPrimes_iff_isUnramifiedAt w).mp hnr⟩
  have hsub := TauCeti.NumberField.le_kummerField_sUnits_of_isCyclic
    (F := R) (n := p) hcl (hdR ▸ dvd_refl p) hunr
  let L := IntermediateField.restrict hsub
  let e' := e.trans (IntermediateField.restrictAlgEquiv hsub)
  have : FiniteDimensional F L := e'.toLinearEquiv.finiteDimensional
  have : NumberField L := .of_module_finite F _
  have hdL : Module.finrank F L = p := e'.toLinearEquiv.finrank_eq.symm.trans hd
  have hidx : (ideleClassNormMap F L).range.index ∣ Module.finrank F L :=
    index_range_ideleClassNormMap_dvd_finrank_of_kummerField_sUnits S hpS hcl L
  have hEq := congrArg Subgroup.index (range_ideleClassNormMap_eq_of_algEquiv e')
  change (ideleClassNormMap F E).range.index = (ideleClassNormMap F L).range.index at hEq
  exact hEq.dvd.trans (hidx.trans hdL.dvd)

private theorem normQuotient_dvd_of_primitive_root
    {K : Type} [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))
    {p : ℕ} (hp : p.Prime) (hd : L.degree = p)
    (hsub : L.ground.toSubgroup ≤
      (adjoin K {x : SeparableClosure K | x ^ p = 1}).fixingSubgroup) :
    Nat.card (L.NormQuotient (globalFormation K)) ∣ p := by
  let F := fixedField L.ground.toSubgroup
  let E := fixedField L.top.toSubgroup
  have hFE : F ≤ E := fixedField_le (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)
  let : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
  have : IsScalarTower F E (SeparableClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have : NumberField F := .of_module_finite K _
  have : NumberField E := .of_module_finite K _
  have : IsGalois F E := L.isGalois_of_fixedField rfl rfl
  let e : L.Gal ≃* (E ≃ₐ[F] E) := L.galEquivOfFixedField rfl rfl
  have hcard : Nat.card (E ≃ₐ[F] E) = p := by
    rw [← Nat.card_congr e.toEquiv, ← NormalLayer.degree_eq_natCard_gal, hd]
  have hpfin := (IsGalois.card_aut_eq_finrank F E).symm.trans hcard
  let : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) p
  have hζmem : ζ ∈ F := by
    apply fixedField_le hsub
    rw [InfiniteGalois.fixedField_fixingSubgroup]
    exact subset_adjoin K _ hζ.pow_eq_one
  have hprim : IsPrimitiveRoot (⟨ζ, hζmem⟩ : F) p :=
    (IsPrimitiveRoot.map_iff_of_injective F.val.injective).mp hζ
  rw [← Nat.card_congr (L.ideleClassNormQuotientEquiv (F := F) (L := E) rfl rfl).toEquiv,
    Nat.card_congr Additive.ofMul.symm, ← Subgroup.index_eq_card]
  exact index_range_ideleClassNormMap_dvd_of_primitive_root F E hp hpfin hprim

/-- The norm index of a prime-degree layer divides the degree of the layer. -/
theorem natCard_ideleClassNormQuotient_dvd_of_prime_degree
    {K : Type} [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))
    (hp : L.degree.Prime) :
    Nat.card (L.NormQuotient (globalFormation K)) ∣ L.degree :=
  NormalLayer.natCard_normQuotient_dvd_prime_of_adjoin_nth_roots (globalFormation K)
    hp (fun L' hd hs ↦ normQuotient_dvd_of_primitive_root L' hp hd hs) L rfl

private theorem layer_two_inequalities_of_prime_degree
    {K : Type} [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K))
    (hp : L.degree.Prime) :
    TateCohomology.herbrandQuotient (L.rep (globalFormation K)) = L.degree ∧
      Nat.card (L.NormQuotient (globalFormation K)) ∣ L.degree := by
  let : Fact (Nat.card L.Gal).Prime := ⟨L.degree_eq_natCard_gal ▸ hp⟩
  have : IsCyclic L.Gal := isCyclic_of_prime_card rfl
  exact ⟨herbrandQuotient_rep_globalFormation_eq_degree L,
    natCard_ideleClassNormQuotient_dvd_of_prime_degree L hp⟩

/-- The first idele-class cohomology of every finite layer vanishes. -/
theorem subsingleton_ideleClassLayer_H1
    {K : Type} [Field K] [NumberField K] (L : NormalLayer (AbsoluteGaloisGroup K)) :
    Subsingleton (L.H (globalFormation K) 1) :=
  L.subsingleton_h1_of_herbrandQuotient_of_prime_degree _ fun L' _ _ hp ↦
    layer_two_inequalities_of_prime_degree L' hp

/-- In a prime-degree Galois extension of number fields, the idele-class norm index equals the
degree. -/
theorem index_range_ideleClassNormMap_eq_of_prime_degree
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (hp : (Module.finrank K L).Prime) :
    (ideleClassNormMap K L).range.index = Module.finrank K L := by
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let N := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K L)
  have hN : N.degree = Module.finrank K L := by
    rw [NormalLayer.degree_eq_natCard_gal, Nat.card_congr (layerGalEquiv ι).toEquiv,
      IsGalois.card_aut_eq_finrank]
  have hdiv := natCard_ideleClassNormQuotient_dvd_of_prime_degree N (hN ▸ hp)
  rw [hN, ← Nat.card_congr (globalLayerNormQuotientEquiv K L).toEquiv,
    Nat.card_congr Additive.ofMul.symm, ← Subgroup.index_eq_card] at hdiv
  have hc : Nat.card Gal(L/K) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  let : Fact (Module.finrank K L).Prime := ⟨hp⟩
  have : IsCyclic Gal(L/K) := isCyclic_of_prime_card hc
  exact le_antisymm (Nat.le_of_dvd hp.pos hdiv) (finrank_le_index_range_ideleClassNormMap K L)

end TinyTauDemo
