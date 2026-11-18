/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.KummerAuxiliaryIndex
public import TinyTauDemo.KummerLocalPowerPrinciple
public import TauCeti.NumberTheory.NumberField.Units.SUnit
import TauCeti.NumberTheory.ClassFieldTheory.Global.ExponentNorms

/-!
# The global index of the auxiliary Kummer idele subgroup

The exact local index divides by the contribution of the principal S-units.
The local power principle computes that contribution by ordinary S-unit powers.
The resulting idele-class index bounds the norm index in Milne VII, §6.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField TauCeti TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped AdicCompletionExtension NumberField

namespace TinyTauDemo

private theorem relIndex_ker_mul_index_map_of_surjective {G H : Type*}
    [CommGroup G] [Group H] (f : G →* H) (hf : Function.Surjective f) (A : Subgroup G) :
    A.relIndex f.ker * (A.map f).index = A.index := by
  rw [Subgroup.index_map, f.range_eq_top_of_surjective hf, Subgroup.index_top, mul_one,
    ← Subgroup.relIndex_sup_left f.ker A]
  exact Subgroup.relIndex_mul_index le_sup_left

variable {K : Type} [Field K] [NumberField K]

/-- The auxiliary Kummer subgroup mapped into the idele class group. -/
noncomputable def auxiliaryKummerIdeleClassSubgroup
    (S R : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (auxiliaryKummerIdeleSubgroup S R n).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

/-- With no extra places, the auxiliary subgroup is the ordinary Kummer idele subgroup. -/
theorem auxiliaryKummerIdeleSubgroup_self
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    auxiliaryKummerIdeleSubgroup S S n = kummerIdeleSubgroup S n := by
  ext x
  rw [mem_auxiliaryKummerIdeleSubgroup_iff, mem_kummerIdeleSubgroup_iff]

private noncomputable def sUnitToKummerIdeles
    (R : Finset (HeightOneSpectrum (𝓞 K))) :
    (Set.unit (R : Set (HeightOneSpectrum (𝓞 K))) K) →* kummerIdeleSubgroup R 1 := by
  let g := (IdeleGroup.unitEmbedding (𝓞 K) K).comp
    (Set.unit (R : Set (HeightOneSpectrum (𝓞 K))) K).subtype
  refine g.codRestrict (kummerIdeleSubgroup R 1) fun u ↦ ?_
  change IdeleGroup.unitEmbedding (𝓞 K) K u.1 ∈ kummerIdeleSubgroup R 1
  rw [mem_kummerIdeleSubgroup_one_iff R]
  exact (IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff
    (R := 𝓞 K) (K := K) (T := (R : Set (HeightOneSpectrum (𝓞 K)))) u.1).mpr u.2

variable {p : ℕ} [hp : Fact p.Prime] [HasEnoughRootsOfUnity K p]
  [DecidableEq (HeightOneSpectrum (𝓞 K))]

/-- The principal contribution to the idele-class index of the auxiliary Kummer subgroup. -/
theorem index_auxiliaryKummerIdeleClassSubgroup_mul_pow
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hT : ∀ y : (v : T) → (v.1.adicCompletion K)ˣ,
      (∀ v, Valued.v (y v : v.1.adicCompletion K) = 1) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v : T,
        (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u)⁻¹ * y v ∈
          (powMonoidHom p).range) :
    (auxiliaryKummerIdeleClassSubgroup S (S ∪ T) p).index * p ^ T.card =
      p ^ (S.card + Fintype.card (InfinitePlace K)) := by
  classical
  let R := S ∪ T
  let U := (R : Set (HeightOneSpectrum (𝓞 K))).unit K
  let J := kummerIdeleSubgroup R 1
  let E := auxiliaryKummerIdeleSubgroup S R p
  let A := E.subgroupOf J
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  let f := q.comp J.subtype
  have hSR : S ⊆ R := Finset.subset_union_left
  have hE : E ≤ J := by
    intro x hx
    exact (mem_kummerIdeleSubgroup_one_iff R x).mpr
      ((mem_auxiliaryKummerIdeleSubgroup_iff S R p x).mp hx).2.2
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨x, hx, hxc⟩ := IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq hcl c
    exact ⟨⟨x, (mem_kummerIdeleSubgroup_one_iff R x).mpr
      (fun v hv ↦ hx v (fun h ↦ hv (hSR h)))⟩, hxc⟩
  let j : U →* J := sUnitToKummerIdeles R
  have hker : j.range = f.ker := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    change (∃ u : U, j u = x) ↔ (x.val : IdeleClassGroup (𝓞 K) K) = 1
    rw [QuotientGroup.eq_one_iff]
    have hx := (mem_kummerIdeleSubgroup_one_iff R x.1).mp x.2
    rw [IdeleGroup.mem_principalSubgroup_iff_exists_mem_unit hx]
    exact ⟨fun ⟨u, hu⟩ ↦ ⟨u.1, u.2, congrArg Subtype.val hu⟩,
      fun ⟨u, hu, he⟩ ↦ ⟨⟨u, hu⟩, Subtype.ext he⟩⟩
  have hpow : A.comap j = (powMonoidHom p : Kˣ →* Kˣ).range.subgroupOf U := by
    ext u
    change IdeleGroup.unitEmbedding (𝓞 K) K (u : Kˣ) ∈ E ↔
      (u : Kˣ) ∈ (powMonoidHom p : Kˣ →* Kˣ).range
    rw [mem_auxiliaryKummerIdeleSubgroup_iff]
    simp only [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
      InfinitePlace.ideleInfiniteCoord_unitEmbedding]
    refine ⟨fun h ↦ ?_, fun hu ↦ ?_⟩
    · apply mem_range_powMonoidHom_of_mem_sUnits_of_local_power S T hST hcl hpS hT
        (a := u.1) ?_ h.1 h.2.1
      simpa only [U, R, Finset.coe_union] using u.2
    · obtain ⟨a, ha⟩ := hu
      have hpw : a ^ p = (u : Kˣ) := ha
      have hrest := (IdeleGroup.forall_valued_ideleFiniteCoord_unitEmbedding_eq_one_iff
        (R := 𝓞 K) (K := K) (T := (R : Set (HeightOneSpectrum (𝓞 K)))) u.1).mpr u.2
      refine ⟨fun v _ ↦ ?_, fun w ↦ ?_, ?_⟩
      · exact ⟨Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a,
          (map_pow _ _ _).symm.trans (congrArg _ hpw)⟩
      · exact ⟨Units.map (algebraMap K w.Completion).toMonoidHom a,
          (map_pow _ _ _).symm.trans (congrArg _ hpw)⟩
      · intro v hv
        have hv' : v ∉ (R : Set (HeightOneSpectrum (𝓞 K))) := by
          simpa only [Finset.mem_coe] using hv
        simpa only [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding] using hrest v hv'
  have hra : A.relIndex f.ker = (powMonoidHom p : Kˣ →* Kˣ).range.relIndex U := by
    rw [← hker, MonoidHom.range_eq_map, ← Subgroup.relIndex_comap,
      Subgroup.relIndex_top_right, hpow]
    rfl
  have hmap : A.map f = auxiliaryKummerIdeleClassSubgroup S R p := by
    change (E.subgroupOf J).map (q.comp J.subtype) = E.map q
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hE]
  have hcount := relIndex_ker_mul_index_map_of_surjective f hf A
  have hcardR : Nat.card (R : Set (HeightOneSpectrum (𝓞 K))) = R.card := by
    change Nat.card ↥R = R.card
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hra, hmap, relIndex_range_powMonoidHom_sUnits_numberField K (R : Set _) p,
    hcardR] at hcount
  change _ = E.relIndex J at hcount
  rw [relIndex_auxiliaryKummerIdeleSubgroup_eq_pow S R p hSR hpS] at hcount
  have hR : R.card = S.card + T.card := Finset.card_union_of_disjoint hST
  let s := S.card + Fintype.card (InfinitePlace K)
  have hsR : Fintype.card (InfinitePlace K) + R.card = s + T.card := by
    rw [hR]
    dsimp [s]
    omega
  have hcount' : p ^ (s + T.card) * (auxiliaryKummerIdeleClassSubgroup S R p).index =
      p ^ (s + s) := by
    simpa only [hsR, two_mul] using hcount
  have hmul : p ^ s * (p ^ T.card * (auxiliaryKummerIdeleClassSubgroup S R p).index) =
      p ^ s * p ^ s := by
    rw [← mul_assoc, ← pow_add p s T.card, ← pow_add p s s]
    exact hcount'
  exact (mul_comm _ _).trans (Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos s) hmul)


omit [DecidableEq (HeightOneSpectrum (𝓞 K))] in
/-- The exact idele-class index of the ordinary Kummer subgroup. -/
theorem index_kummerIdeleClassSubgroup_eq_pow
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (kummerIdeleClassSubgroup S p).index = p ^ (S.card + Fintype.card (InfinitePlace K)) := by
  classical
  have h := index_auxiliaryKummerIdeleClassSubgroup_mul_pow S ∅ (Finset.disjoint_empty_right S)
    hcl hpS (fun _ _ ↦ ⟨1, one_mem _, fun v ↦ (Finset.notMem_empty _ v.2).elim⟩)
  simp only [Finset.union_empty, Finset.card_empty, pow_zero, mul_one] at h
  have he : auxiliaryKummerIdeleClassSubgroup S S p = kummerIdeleClassSubgroup S p := by
    ext c
    rw [auxiliaryKummerIdeleClassSubgroup, auxiliaryKummerIdeleSubgroup_self, Subgroup.mem_map,
      mem_kummerIdeleClassSubgroup_iff]
    rfl
  rwa [he] at h

section Norm

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

omit hp [HasEnoughRootsOfUnity K p] in
/-- The auxiliary Kummer idele-class subgroup is contained in the norm group if
the extra places split completely and the remaining places outside S are unramified. -/
theorem auxiliaryKummerIdeleClassSubgroup_le_range_norm
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hexp : Monoid.exponent Gal(L/K) ∣ p)
    (hT : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T → ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    auxiliaryKummerIdeleClassSubgroup S (S ∪ T) p ≤ (ideleClassNormMap K L).range := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨hfin, hinf, hrest⟩ := (mem_auxiliaryKummerIdeleSubgroup_iff _ _ _ _).mp hx
  have hn : x ∈ (ideleNormMap K L).toMonoidHom.range := by
    refine mem_range_ideleNormMap_of_exponent_dvd K L hexp
      (S := (S : Set _)) (T := (T : Set _)) hT hU ?_ ?_ ?_
    · intro v hv
      rw [powerSubgroup_eq_range_powMonoidHom]
      exact hfin v hv
    · intro v hvS hvT
      exact hrest v (by simpa only [Finset.mem_union, not_or] using ⟨hvS, hvT⟩)
    · intro w
      rw [powerSubgroup_eq_range_powMonoidHom]
      exact hinf w
  obtain ⟨y, hy⟩ := hn
  exact ⟨(y : IdeleClassGroup (𝓞 L) L), (ideleClassNormMap_mk y).trans
    (congrArg (fun z : IdeleGroup (𝓞 K) K ↦ (z : IdeleClassGroup (𝓞 K) K)) hy)⟩

omit [DecidableEq (HeightOneSpectrum (𝓞 K))] in
/-- The norm index divides the degree once the S-unit residues at the auxiliary places
surject onto the local unit power classes. The displayed degree equation comes from
the degree of the S-unit Kummer field and the size of a Frobenius basis. -/
theorem index_norm_dvd_finrank_of_auxiliary_unit_powers
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hTpow : ∀ y : (v : T) → (v.1.adicCompletion K)ˣ,
      (∀ v, Valued.v (y v : v.1.adicCompletion K) = 1) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v : T,
        (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u)⁻¹ * y v ∈
          (powMonoidHom p).range)
    (hexp : Monoid.exponent Gal(L/K) ∣ p)
    (hT : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T → ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal)
    (hdeg : Module.finrank K L * p ^ T.card = p ^ (S.card + Fintype.card (InfinitePlace K))) :
    (ideleClassNormMap K L).range.index ∣ Module.finrank K L := by
  classical
  have hi := index_auxiliaryKummerIdeleClassSubgroup_mul_pow S T hST hcl hpS hTpow
  have heq : (auxiliaryKummerIdeleClassSubgroup S (S ∪ T) p).index = Module.finrank K L :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos _) (hi.trans hdeg.symm)
  rw [← heq]
  exact Subgroup.index_dvd_of_le (auxiliaryKummerIdeleClassSubgroup_le_range_norm L S T hexp hT hU)

end Norm

end TinyTauDemo
