/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# A local power principle with auxiliary split places

If the S-units realize every local unit power class at T, a radical that is
a local p-th power at S and infinity, and is a unit outside S and T, is a
global p-th power. This specializes Milne VII, Proposition 6.10.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField TauCeti TauCeti.ClassFieldTheory
open scoped NumberField

namespace TinyTauDemo

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [HasEnoughRootsOfUnity K p]

omit [NumberField K] hp [HasEnoughRootsOfUnity K p] in
private theorem relIndex_powMonoidHom_zpowers_dvd (a : Kˣ) :
    (powMonoidHom p : Kˣ →* Kˣ).range.relIndex (Subgroup.zpowers a) ∣ p := by
  have hle : Subgroup.zpowers (a ^ p) ≤ (powMonoidHom p : Kˣ →* Kˣ).range :=
    Subgroup.zpowers_le.mpr ⟨a, rfl⟩
  refine (Subgroup.relIndex_dvd_of_le_left _ hle).trans ?_
  rw [← zpow_natCast, Subgroup.relIndex_zpowers_zpow]
  exact Nat.gcd_dvd_left _ _

/-- Under the S-unit approximation condition at T, a local p-th power at S and
infinity with trivial valuations outside S and T is a global p-th power. -/
theorem mem_range_powMonoidHom_of_mem_sUnits_of_local_power
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hT : ∀ y : (v : T) → (v.1.adicCompletion K)ˣ,
      (∀ v, Valued.v (y v : v.1.adicCompletion K) = 1) →
      ∃ u ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v : T,
        (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u)⁻¹ * y v ∈
          (powMonoidHom p).range)
    {a : Kˣ} (ha : a ∈ ((S ∪ T : Set (HeightOneSpectrum (𝓞 K)))).unit K)
    (hfin : ∀ v ∈ S, Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom p).range)
    (hinf : ∀ w : InfinitePlace K, Units.map (algebraMap K w.Completion).toMonoidHom a ∈
      (powMonoidHom p).range) :
    a ∈ (powMonoidHom p : Kˣ →* Kˣ).range := by
  let Δ := Subgroup.zpowers a
  have hid : (powMonoidHom p : Kˣ →* Kˣ).range.relIndex Δ ∣ p :=
    relIndex_powMonoidHom_zpowers_dvd a
  have : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex Δ := ⟨fun he ↦
    hp.out.ne_zero (Nat.zero_dvd.mp (he ▸ hid))⟩
  let M := kummerField (SeparableClosure K) p Δ
  have hroot (b : Kˣ) : ∃ r : SeparableClosure K, r ^ p = algebraMap K (SeparableClosure K) b :=
    IsAlgClosed.exists_pow_nat_eq _ hp.out.pos
  have hd : Module.finrank K M ∣ p := by
    rw [show Module.finrank K M = (powMonoidHom p : Kˣ →* Kˣ).range.relIndex Δ from
      finrank_kummerField (E := SeparableClosure K) (n := p) (Δ := Δ) (fun b _ ↦ hroot b)]
    exact hid
  have hloc {F : Type} [Field F] [Algebra K F]
      (hf : Units.map (algebraMap K F).toMonoidHom a ∈ (powMonoidHom p).range)
      (b : Kˣ) (hb : b ∈ Δ) : ∃ c : F, c ^ p = algebraMap K F b := by
    have hle : Δ ≤ (powMonoidHom p : Fˣ →* Fˣ).range.comap
        (Units.map (algebraMap K F).toMonoidHom) := Subgroup.zpowers_le.mpr hf
    obtain ⟨c, hc⟩ := hle hb
    exact ⟨c, congrArg Units.val hc⟩
  have hMsurj : Function.Surjective (TauCeti.GlobalNumberFields.ideleClassNormMap K M) :=
    ideleClassNormMap_kummerField_surjective_of_forall_exists_mem_unit S T hST hcl hpS
      (Subgroup.zpowers_le.mpr ha) (fun v hv ↦ hloc (hfin v hv))
      (fun w ↦ hloc (hinf w)) hd hT
  have hMone : Module.finrank K M = 1 := by
    rcases (Nat.dvd_prime hp.out).mp hd with hone | hprime
    · exact hone
    · have : Fact (Module.finrank K M).Prime := ⟨hprime ▸ hp.out⟩
      have : IsCyclic Gal(M/K) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
      exact finrank_eq_one_of_surjective_ideleClassNormMap K M hMsurj
  obtain ⟨r, hr⟩ := hroot a
  let rM : M := ⟨r, mem_kummerField_of_pow_eq (Subgroup.mem_zpowers a) hr⟩
  have hrM : rM ^ p = algebraMap K M a := Subtype.ext hr
  obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hMone).surjective rM
  have hcp : c ^ p = (a : K) := (algebraMap K M).injective (by rw [map_pow, hc, hrM])
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.out.ne_zero] at hcp
    exact a.ne_zero hcp.symm
  exact ⟨Units.mk0 c hc0, Units.ext hcp⟩

end TinyTauDemo
