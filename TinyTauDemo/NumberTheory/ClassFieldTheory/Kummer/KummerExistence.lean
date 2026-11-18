/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.NumberTheory.NumberField.Kummer.Unramified
import TinyTauDemo.NumberTheory.ClassFieldTheory.Kummer.KummerFrobeniusBasis
import TinyTauDemo.NumberTheory.ClassFieldTheory.Kummer.KummerNormIndex
import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Norm
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# Realization of open prime-order idele-class characters

An open character kernel contains a ray subgroup, so an enlarged set of places
makes it contain the Kummer idele-class subgroup. Its exact index then identifies
it with the kernel of the Artin map for the S-unit Kummer field. Factoring the
character through that Galois group and taking a fixed field gives the cyclic
extension, using the norm-kernel identities for the Artin maps.

See J. S. Milne, *Class Field Theory*, VII, Lemma 9.3.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9fa8b1e51d60a6568520e89a452494ca038d4a2a`.
-/

public section

open IsDedekindDomain NumberField IntermediateField TauCeti TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields
open scoped NumberField

namespace TinyTauDemo

section OpenKernel

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G]

local notation "Jₖ" => IdeleGroup (𝓞 K) K
local notation "Cₖ" => IdeleClassGroup (𝓞 K) K

/-- The local power conditions of a Kummer idele imply triviality under an exponent-`n`
character that is trivial on a ray subgroup supported in `S`. -/
theorem kummerIdeleClassSubgroup_le_ker_of_raySubgroup_le
    (χ : Cₖ →* G) {n : ℕ} (hn : ∀ g : G, g ^ n = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : Modulus K)
    (hmS : m.support ⊆ S) (hmχ : raySubgroup m ≤ χ.ker) :
    kummerIdeleClassSubgroup S n ≤ χ.ker := by
  classical
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_kummerIdeleClassSubgroup_iff S n c).mp hc
  obtain ⟨hf, hi, hrest⟩ := (mem_kummerIdeleSubgroup_iff S n x).mp hx
  choose a ha using fun v : S ↦ hf v.1 v.2
  choose b hb using hi
  let yfin (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
    if hv : v ∈ S then a ⟨v, hv⟩ else 1
  have hyunits : ∀ᶠ v in Filter.cofinite, yfin v ∈ (v.adicCompletionIntegers K).units :=
    S.eventually_cofinite_notMem.mono fun v hv ↦ by simp [yfin, hv]
  let y := ideleOfUnits b yfin hyunits
  let z := (y ^ n)⁻¹ * x
  have hzS (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) : v.ideleFiniteCoord z = 1 := by
    have hloc : (yfin v) ^ n = v.ideleFiniteCoord x := by
      simpa only [yfin, dite_eq_left hv, powMonoidHom_apply] using ha ⟨v, hv⟩
    rw [show z = (y ^ n)⁻¹ * x from rfl, map_mul, map_inv, map_pow]
    rw [show v.ideleFiniteCoord y = yfin v by simp [y], hloc, inv_mul_cancel]
  have hzSc (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
      v.ideleFiniteCoord z = v.ideleFiniteCoord x := by
    rw [show z = (y ^ n)⁻¹ * x from rfl, map_mul, map_inv, map_pow]
    simp [y, yfin, hv]
  have hzinf (w : InfinitePlace K) : w.ideleInfiniteCoord z = 1 := by
    rw [show z = (y ^ n)⁻¹ * x from rfl, map_mul, map_inv, map_pow]
    rw [show w.ideleInfiniteCoord y = b w by simp [y],
      show b w ^ n = w.ideleInfiniteCoord x from hb w, inv_mul_cancel]
  have hz : z ∈ ideleCongruenceSubgroup m := by
    refine mem_ideleCongruenceSubgroup_iff.mpr ⟨fun v _ ↦ ?_, fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · by_cases hv : v ∈ S
      · rw [hzS v hv, Units.val_one, map_one]
      · rw [hzSc v hv]
        exact hrest v hv
    · rw [hzS v (hmS ((m.mem_support_iff v).mpr hv)), Units.val_one, sub_self, map_zero]
      exact zero_le
    · rw [hzinf w.1, Units.val_one, map_one]
      exact one_pos
  have hχz : χ (z : Cₖ) = 1 := hmχ (mem_raySubgroup_iff.mpr ⟨z, hz, rfl⟩)
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)
  change χ (q x) = 1
  rw [show x = y ^ n * z by simp [z], map_mul, map_mul, map_pow, map_pow,
    hn, show χ (q z) = 1 from hχz, mul_one]

/-- Any character with open kernel and image killed by `n` kills the Kummer idele-class subgroup
for every superset of a finite `S` containing the primes above `n` and generating the ideal
class group. -/
theorem exists_kummerIdeleClassSubgroup_le_ker_of_isOpen
    (χ : Cₖ →* G) {n : ℕ} [NeZero n] (hn : ∀ g : G, g ^ n = 1)
    (hχ : IsOpen (χ.ker : Set Cₖ)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      Subgroup.closure
        (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S' →
        kummerIdeleClassSubgroup S' n ≤ χ.ker := by
  classical
  obtain ⟨m, hm⟩ := exists_raySubgroup_le_of_isOpen χ.ker hχ
  obtain ⟨T, hcl, hnT⟩ := exists_finset_classGroup_generators_containing_natCast K n
  let S := T ∪ m.support
  have hTS : T ⊆ S := Finset.subset_union_left
  have hmS : m.support ⊆ S := Finset.subset_union_right
  refine ⟨S, eq_top_mono (Subgroup.closure_mono (Set.image_mono hTS)) hcl,
    fun v hv ↦ hTS (hnT v hv), fun S' hSS' ↦ ?_⟩
  exact kummerIdeleClassSubgroup_le_ker_of_raySubgroup_le χ hn S' m (hmS.trans hSS') hm

end OpenKernel

section ArtinQuotient

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [IsGalois K M] [FiniteDimensional K M]
    {G : Type*} [Group G]

local notation "Cₖ" => IdeleClassGroup (𝓞 K) K

/-- A subgroup contained in the kernel of a surjective Artin map is that kernel if its
index is the degree of the extension. -/
theorem ker_artin_eq_of_le_of_index_eq_finrank
    (α : Cₖ →* Gal(M/K)) (hα : Function.Surjective α)
    (H : Subgroup Cₖ) (hle : H ≤ α.ker) (hidx : H.index = Module.finrank K M) :
    α.ker = H := by
  have hαidx : α.ker.index = Module.finrank K M := by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
      IsGalois.card_aut_eq_finrank]
  have : α.ker.FiniteIndex := ⟨hαidx.trans_ne Module.finrank_pos.ne'⟩
  exact (Subgroup.eq_of_index_dvd_index hle (by rw [hidx, hαidx])).symm

/-- If a character factors through an Artin map and the restricted Artin kernels are the norm
subgroups, the fixed field of the factored kernel realizes the character. -/
theorem exists_artin_factor_fixedField_norm_range_eq_ker
    (χ : Cₖ →* G) (hχ : Function.Surjective χ)
    (α : Cₖ →* Gal(M/K)) (hα : Function.Surjective α) (hle : α.ker ≤ χ.ker)
    (hrec : ∀ (L : IntermediateField K M) [Normal K L],
      Module.finrank K L = Nat.card G →
      ((AlgEquiv.restrictNormalHom L).comp α).ker = (ideleClassNormMap K L).range) :
    ∃ φ : Gal(M/K) →* G, φ.comp α = χ ∧ Function.Surjective φ ∧
      let L := IntermediateField.fixedField φ.ker
      IsGalois K L ∧ Module.finrank K L = Nat.card G ∧
        Nonempty (Gal(L/K) ≃* G) ∧ (ideleClassNormMap K L).range = χ.ker := by
  let e := QuotientGroup.quotientKerEquivOfSurjective α hα
  let φ : Gal(M/K) →* G := (QuotientGroup.lift α.ker χ hle).comp e.symm.toMonoidHom
  have hφ : φ.comp α = χ := by
    apply MonoidHom.ext
    intro x
    change QuotientGroup.lift α.ker χ hle (e.symm (α x)) = χ x
    have hx : e.symm (α x) = QuotientGroup.mk x := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hx, QuotientGroup.lift_mk]
  have hφs : Function.Surjective φ := by
    intro g
    obtain ⟨x, rfl⟩ := hχ g
    exact ⟨α x, DFunLike.congr_fun hφ x⟩
  let L := IntermediateField.fixedField φ.ker
  have hGal : IsGalois K L := IsGalois.of_fixedField_normal_subgroup φ.ker
  let eL : Gal(L/K) ≃* G :=
    (IsGalois.normalAutEquivQuotient φ.ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hdeg : Module.finrank K L = Nat.card G := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr eL.toEquiv
  have hres : (AlgEquiv.restrictNormalHom L).ker = φ.ker :=
    (IntermediateField.restrictNormalHom_ker L).trans
      (IntermediateField.fixingSubgroup_fixedField φ.ker)
  have hnorm : (ideleClassNormMap K L).range = χ.ker := by
    rw [← hrec L hdeg]
    ext x
    have hcomp : φ (α x) = χ x := DFunLike.congr_fun hφ x
    change (AlgEquiv.restrictNormalHom L) (α x) = 1 ↔ χ x = 1
    change α x ∈ (AlgEquiv.restrictNormalHom L).ker ↔ _
    rw [hres, MonoidHom.mem_ker, hcomp]
  exact ⟨φ, hφ, hφs, hGal, hdeg, ⟨eL⟩, hnorm⟩

end ArtinQuotient

section KummerField

variable {K : Type} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  [IsSepClosed Ω] {p : ℕ} [hp : Fact p.Prime] [HasEnoughRootsOfUnity K p]

local notation "Cₖ" => IdeleClassGroup (𝓞 K) K
local notation "Uₛ" S => Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "Mₛ" S => kummerField Ω p (Uₛ S)

private theorem finrank_sUnitKummer_eq_pow (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.finrank K (Mₛ S) = p ^ (S.card + Fintype.card (InfinitePlace K)) := by
  let : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  rw [finrank_kummerField (fun a _ ↦ IsSepClosed.exists_pow_nat_eq _ p),
    relIndex_range_powMonoidHom_sUnits_numberField,
    Nat.card_coe_set_eq, Set.ncard_coe_finset, add_comm]

/-- The power-class subgroup is the Artin kernel of the full S-unit Kummer field.
The Artin map kills norms, and the computed power-class index equals the extension degree. -/
theorem ker_artin_eq_kummerIdeleClassSubgroup_of_index
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hidx : (kummerIdeleClassSubgroup S p).index = p ^ (S.card + Fintype.card (InfinitePlace K)))
    (α : Cₖ →* Gal((Mₛ S)/K)) (hα : Function.Surjective α)
    (hnorm : (ideleClassNormMap K (Mₛ S)).range ≤ α.ker) :
    α.ker = kummerIdeleClassSubgroup S p := by
  have hle := kummerIdeleClassSubgroup_le_range_ideleClassNormMap K (Mₛ S)
    (exponent_algEquiv_kummerField_dvd K Ω p (Uₛ S)) S
    (TauCeti.NumberField.ramifiedSupport_kummerField_sUnits_subset
      (E := Ω) S hpS)
  exact ker_artin_eq_of_le_of_index_eq_finrank α hα _ (hle.trans hnorm)
    (hidx.trans (finrank_sUnitKummer_eq_pow (Ω := Ω) S).symm)

/-- A choice of `S` supporting the character and generating the class group gives a factor of
the Artin map whose kernel cuts out a cyclic extension with the desired norm subgroup. -/
theorem exists_cyclic_norm_realization_at_good_S_of_artin {G : Type*} [Group G]
    (χ : Cₖ →* G) (hχ : Function.Surjective χ) (hcard : Nat.card G = p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hS : kummerIdeleClassSubgroup S p ≤ χ.ker)
    (α : Cₖ →* Gal((Mₛ S)/K)) (hα : Function.Surjective α)
    (hnorm : (ideleClassNormMap K (Mₛ S)).range ≤ α.ker)
    (hrec : ∀ (L : IntermediateField K (Mₛ S)) [Normal K L], Module.finrank K L = p →
      ((AlgEquiv.restrictNormalHom L).comp α).ker = (ideleClassNormMap K L).range) :
    ∃ φ : Gal((Mₛ S)/K) →* G, φ.comp α = χ ∧ Function.Surjective φ ∧
      let L := IntermediateField.fixedField φ.ker
      IsGalois K L ∧ IsCyclic Gal(L/K) ∧ Module.finrank K L = p ∧
        (ideleClassNormMap K L).range = χ.ker := by
  have heq := ker_artin_eq_kummerIdeleClassSubgroup_of_index S hpS
    (index_kummerIdeleClassSubgroup_eq_pow S hcl hpS) α hα hnorm
  obtain ⟨φ, hφ, hφs, hL, hdeg, ⟨e⟩, hNorm⟩ :=
    exists_artin_factor_fixedField_norm_range_eq_ker χ hχ α hα (heq ▸ hS)
      (fun L _ hdeg ↦ hrec L (hdeg.trans hcard))
  have : IsCyclic G := isCyclic_of_prime_card hcard
  exact ⟨φ, hφ, hφs, hL, isCyclic_of_surjective e.symm e.symm.surjective, hdeg.trans hcard, hNorm⟩

end KummerField

end TinyTauDemo
