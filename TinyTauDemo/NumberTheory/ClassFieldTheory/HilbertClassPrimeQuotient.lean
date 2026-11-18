/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Topology.Algebra.Group.Units

/-!
# Prime-index quotients of ordinary idele classes

If a prime divides the class number, the ordinary class group maps onto a cyclic group
of that order. Composing with the ideal class of a finite idele gives a prime-index
quotient of the idele class group that kills ideles integral at every finite place.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9e49cf86a2f12f4c30fb1657d2e228b79f3a2a77`.
-/

public section

open IsDedekindDomain NumberField TauCeti
open scoped NumberField BigOperators

namespace TinyTauDemo

/-- A prime divisor of the order of a finite abelian group gives a corresponding
cyclic quotient. -/
theorem exists_surjective_monoidHom_zmod_of_prime_dvd_card
    (G : Type*) [CommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (h : p ∣ Nat.card G) :
    ∃ f : G →* Multiplicative (ZMod p), Function.Surjective f := by
  classical
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  have he : Nat.card G = ∏ i, n i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    change (∏ i, Nat.card (ZMod (n i))) = _
    simp only [Nat.card_zmod]
  rw [he] at h
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff n).mp h
  let g : Multiplicative (ZMod (n i)) →* Multiplicative (ZMod p) :=
    (ZMod.castHom hi (ZMod p)).toAddMonoidHom.toMultiplicative
  let v : ((j : ι) → Multiplicative (ZMod (n j))) →* Multiplicative (ZMod (n i)) :=
    Pi.evalMonoidHom _ i
  have hv : Function.Surjective v := by
    intro x
    exact ⟨Function.update 1 i x, by simp [v]⟩
  have hg : Function.Surjective g := ZMod.castHom_surjective hi
  exact ⟨g.comp (v.comp e.toMonoidHom), hg.comp (hv.comp e.surjective)⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The ordinary ideal class of the finite component of an idele class. -/
noncomputable def ideleClassToOrdinaryClass : IdeleClassGroup (𝓞 K) K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup (𝓞 K) K)
    ((FiniteAdeleRing.toClassGroup (𝓞 K) K).comp (IdeleGroup.toFiniteIdele (𝓞 K) K))
    (by
      rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, IdeleGroup.toFiniteIdele_unitEmbedding,
        ← MonoidHom.mem_ker, FiniteAdeleRing.ker_toClassGroup]
      exact Subgroup.mem_sup.mpr ⟨1, one_mem _, _, ⟨u, rfl⟩, one_mul _⟩)

theorem ideleClassToOrdinaryClass_surjective :
    Function.Surjective (ideleClassToOrdinaryClass K) := by
  intro c
  obtain ⟨f, hf⟩ := FiniteAdeleRing.toClassGroup_surjective (R := 𝓞 K) (K := K) c
  refine ⟨(IdeleGroup.ofFiniteIdele (𝓞 K) K f : IdeleGroup (𝓞 K) K), ?_⟩
  change (FiniteAdeleRing.toClassGroup (𝓞 K) K) (IdeleGroup.toFiniteIdele (𝓞 K) K
    (IdeleGroup.ofFiniteIdele (𝓞 K) K f)) = c
  rwa [IdeleGroup.toFiniteIdele_ofFiniteIdele]

theorem ideleClassToOrdinaryClass_eq_one_of_finite_units (x : IdeleGroup (𝓞 K) K)
    (hx : IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K) :
    ideleClassToOrdinaryClass K x = 1 := by
  change (FiniteAdeleRing.toClassGroup (𝓞 K) K) (IdeleGroup.toFiniteIdele (𝓞 K) K x) = 1
  rw [← MonoidHom.mem_ker, FiniteAdeleRing.ker_toClassGroup]
  exact Subgroup.mem_sup.mpr ⟨_, hx, 1, one_mem _, mul_one _⟩

private theorem isOpen_ideleCharacter_ker_of_finite_units
    {G : Type*} [Group G] (f : IdeleClassGroup (𝓞 K) K →* G)
    (hf : ∀ x : IdeleGroup (𝓞 K) K,
      IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K → f x = 1) :
    IsOpen (f.ker : Set (IdeleClassGroup (𝓞 K) K)) := by
  let U := (FiniteAdeleRing.integralUnits (𝓞 K) K).comap (IdeleGroup.toFiniteIdele (𝓞 K) K)
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  have hfin : Continuous (IdeleGroup.toFiniteIdele (𝓞 K) K) := by
    apply Units.continuous_iff.mpr
    constructor
    · simpa only [Function.comp_def, IdeleGroup.coe_toFiniteIdele] using
        (continuous_snd.comp (Units.continuous_val :
          Continuous (fun x : IdeleGroup (𝓞 K) K ↦ (x : AdeleRing (𝓞 K) K))))
    · simpa only [Function.comp_def, ← map_inv, IdeleGroup.coe_toFiniteIdele] using
        (continuous_snd.comp (Units.continuous_coe_inv :
          Continuous (fun x : IdeleGroup (𝓞 K) K ↦
            ((x⁻¹ : IdeleGroup (𝓞 K) K) : AdeleRing (𝓞 K) K))))
  have hU : IsOpen (U : Set (IdeleGroup (𝓞 K) K)) := by
    apply IsOpen.preimage hfin
    rw [FiniteAdeleRing.integralUnits_eq_units_integralAdeles]
    exact Submonoid.isOpen_units (FiniteAdeleRing.isOpen_integralAdeles (𝓞 K) K)
  have hmap : IsOpen (U.map q : Set (IdeleClassGroup (𝓞 K) K)) := by
    change IsOpen ((QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) ''
      (U : Set (IdeleGroup (𝓞 K) K)))
    exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hU
  apply Subgroup.isOpen_mono _ hmap
  rintro _ ⟨x, hx, rfl⟩
  exact MonoidHom.mem_ker.mpr (hf x hx)

/-- A prime factor of the class number gives a cyclic quotient of the idele class group
that kills every idele whose finite component is integral. -/
theorem exists_ideleClass_prime_quotient_of_dvd_classNumber {p : ℕ} (hp : p.Prime)
    (h : p ∣ classNumber K) :
    ∃ f : IdeleClassGroup (𝓞 K) K →* Multiplicative (ZMod p),
      Function.Surjective f ∧ f.ker.index = p ∧
      IsOpen (f.ker : Set (IdeleClassGroup (𝓞 K) K)) ∧
        ∀ x : IdeleGroup (𝓞 K) K,
          IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K → f x = 1 := by
  have hd : p ∣ Nat.card (ClassGroup (𝓞 K)) := by
    simpa only [Nat.card_eq_fintype_card, classNumber] using h
  obtain ⟨g, hg⟩ := exists_surjective_monoidHom_zmod_of_prime_dvd_card
    (ClassGroup (𝓞 K)) hp hd
  let f := g.comp (ideleClassToOrdinaryClass K)
  have hf : Function.Surjective f := hg.comp (ideleClassToOrdinaryClass_surjective K)
  have hkill (x : IdeleGroup (𝓞 K) K)
      (hx : IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K) :
      f x = 1 := by
    change g (ideleClassToOrdinaryClass K x) = 1
    rw [ideleClassToOrdinaryClass_eq_one_of_finite_units K x hx, map_one]
  refine ⟨f, hf, ?_, isOpen_ideleCharacter_ker_of_finite_units K f hkill, hkill⟩
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf, Subgroup.card_top]
  exact Nat.card_zmod p

end TinyTauDemo
