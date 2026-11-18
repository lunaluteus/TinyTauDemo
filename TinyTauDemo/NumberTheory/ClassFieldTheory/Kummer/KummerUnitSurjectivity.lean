/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.NumberField.Units.LocalPowerClass
public import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.NumberTheory.NumberField.Global.Places.UnitPowerClasses
import TauCeti.NumberTheory.NumberField.Units.SUnit

/-!
# Surjectivity of the S-unit local power-class map

The relative Kummer degree counts the image of the S-units modulo powers in the
intermediate field. The local root criterion identifies the kernel of the map to
the local unit classes. Away from the exponent each local factor has the same
cardinality, so a Frobenius basis gives surjectivity.

See J. S. Milne, *Class Field Theory*, VII, Lemma 6.9.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField TauCeti
open scoped NumberField

namespace TinyTauDemo

section Degree

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M]
  {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n] {Δ : Subgroup Kˣ}

local notation "j" => Units.map (RingHom.toMonoidHom (algebraMap K L))
local notation "Pₖ" => MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)
local notation "Pₗ" => MonoidHom.range (powMonoidHom n : Lˣ →* Lˣ)

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
private theorem kummerField_map_eq_top (hgen : kummerField M n Δ = ⊤) :
    kummerField M n (Δ.map j) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_top]
  apply top_unique
  rw [← hgen, kummerField_le_iff]
  intro a ha x hx
  change x ∈ kummerField M n (Δ.map j)
  refine mem_kummerField_of_pow_eq (Subgroup.mem_map_of_mem j ha) ?_
  change x ^ n = algebraMap L M (algebraMap K L (a : K))
  rwa [← IsScalarTower.algebraMap_apply K L M]

/-- The relative degree of a Kummer extension is the index of the elements of the radical
subgroup that become powers over the intermediate field. -/
theorem finrank_eq_relIndex_pow_comap_of_kummerField_eq_top
    [(Pₖ).IsFiniteRelIndex Δ] (hgen : kummerField M n Δ = ⊤)
    (hroots : ∀ a ∈ Δ, ∃ x : M, x ^ n = algebraMap K M a) :
    Module.finrank L M = ((Pₗ).comap j).relIndex Δ := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  have : HasEnoughRootsOfUnity L n :=
    ⟨⟨_, hζ.map_of_injective (algebraMap K L).injective⟩, rootsOfUnity.isCyclic L n⟩
  have hle : (Pₖ).map j ≤ Pₗ := by
    rintro _ ⟨a, ⟨b, hb⟩, rfl⟩
    refine ⟨j b, ?_⟩
    rw [← hb]
    exact (map_pow j b n).symm
  have hfin : ((Pₖ).map j).IsFiniteRelIndex (Δ.map j) :=
    Subgroup.IsFiniteRelIndex.map j inferInstance
  have : (Pₗ).IsFiniteRelIndex (Δ.map j) := Subgroup.isFiniteRelIndex_of_le_left _ hle
  have hgenL : kummerField M n (Δ.map j) = ⊤ := kummerField_map_eq_top hgen
  have hdegree := finrank_kummerField (K := L) (E := M) (n := n) (Δ := Δ.map j) (by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx⟩ := hroots a ha
    refine ⟨x, ?_⟩
    change x ^ n = algebraMap L M (algebraMap K L (a : K))
    rwa [← IsScalarTower.algebraMap_apply K L M])
  rw [hgenL, IntermediateField.topEquiv.toLinearEquiv.finrank_eq, ← Subgroup.relIndex_comap]
    at hdegree
  exact hdegree

end Degree

section Local

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n]
  [HasEnoughRootsOfUnity K n]
  (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)

local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "T₀" => (T : Set (HeightOneSpectrum (𝓞 K)))

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
private theorem card_unitFiltrationZero_powerClasses (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (unitFiltration (v.adicCompletion K) 0 ⧸ (powMonoidHom n).range) =
      Nat.card ((v.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom n).range) := by
  let e : unitFiltration (v.adicCompletion K) 0 ≃* (v.adicCompletionIntegers K)ˣ :=
    unitFiltrationZeroEquivIntegerUnits.trans
      (Units.mapEquiv (v.integerEquivAdicCompletionIntegers (K := K)).toMulEquiv)
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card, ← e.map_range_powMonoidHom,
    Subgroup.index_map_equiv]

omit [NeZero n] in
/-- The finite product of local unit power classes away from `n` has cardinality `n ^ #T`. -/
theorem card_unitLocalPowerClasses (hT : ∀ v ∈ T, (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card (Set.UnitLocalPowerClasses T₀ n) = n ^ T.card := by
  change Nat.card ((v : T) → unitFiltration (v.1.adicCompletion K) 0 ⧸
    (powMonoidHom n).range) = _
  rw [Nat.card_pi]
  simp only [card_unitFiltrationZero_powerClasses (n := n)]
  rw [Finset.prod_coe_sort T (fun v ↦
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom n).range))]
  exact GlobalNumberFields.prod_card_unitPowerClasses n T hT

variable {L M : Type*} [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

local notation "Uₛ" => Set.unit S₀ K
local notation "j" => Units.map (RingHom.toMonoidHom (algebraMap K L))
local notation "Pₖ" => MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)
local notation "Pₗ" => MonoidHom.range (powMonoidHom n : Lˣ →* Lˣ)

/-- The local unit power-class map is surjective when its kernel is the `S`-units that are
powers in `L` and `T` has one place for each generator of the relative Kummer extension. -/
theorem unitLocalPowerClassMap_surjective_of_ker_of_finrank
    (hT : ∀ v ∈ T, (n : 𝓞 K) ∉ v.asIdeal)
    (hgen : kummerField M n Uₛ = ⊤)
    (hroots : ∀ a ∈ Uₛ, ∃ x : M, x ^ n = algebraMap K M a)
    (hker : (Set.unitLocalPowerClassMap S₀ T₀ (by exact_mod_cast hST) n).ker =
      ((Pₗ).comap j).subgroupOf Uₛ)
    (hdegree : Module.finrank L M = n ^ T.card) :
    Function.Surjective (Set.unitLocalPowerClassMap S₀ T₀ (by exact_mod_cast hST) n) := by
  let : Finite S₀ := S.finite_toSet.to_subtype
  have : (Pₖ).IsFiniteRelIndex Uₛ := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero,
      relIndex_range_powMonoidHom_sUnits_numberField]
    exact pow_ne_zero _ (NeZero.ne n)
  let f := Set.unitLocalPowerClassMap S₀ T₀ (by exact_mod_cast hST) n
  have hcard := card_unitLocalPowerClasses (n := n) T hT
  have : Finite (Set.UnitLocalPowerClasses T₀ n) :=
    Nat.finite_of_card_ne_zero (hcard.trans_ne (pow_ne_zero _ (NeZero.ne n)))
  have heq : Nat.card f.range = Nat.card (Set.UnitLocalPowerClasses T₀ n) := by
    calc
      _ = Nat.card (Uₛ ⧸ f.ker) :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv.symm
      _ = ((Pₗ).comap j).relIndex Uₛ := by rw [← Subgroup.index_eq_card, hker, Subgroup.relIndex]
      _ = Module.finrank L M :=
        (finrank_eq_relIndex_pow_comap_of_kummerField_eq_top hgen hroots).symm
      _ = _ := hdegree.trans hcard.symm
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq f.range heq)

/-- The counting form of Milne VII, Lemma 6.9. The local root criterion at the selected
places identifies the kernel, and the relative degree then gives surjectivity. -/
theorem unitLocalPowerClassMap_surjective_of_local_roots_of_finrank
    (hT : ∀ v ∈ T, (n : 𝓞 K) ∉ v.asIdeal)
    (hgen : kummerField M n Uₛ = ⊤)
    (hroots : ∀ a ∈ Uₛ, ∃ x : M, x ^ n = algebraMap K M a)
    (hlocal : ∀ a ∈ Uₛ, (∀ v ∈ T, ∃ c : v.adicCompletion K,
      c ^ n = algebraMap K (v.adicCompletion K) (a : K)) ↔
      ∃ b : L, b ^ n = algebraMap K L (a : K))
    (hdegree : Module.finrank L M = n ^ T.card) :
    Function.Surjective (Set.unitLocalPowerClassMap S₀ T₀ (by exact_mod_cast hST) n) := by
  refine unitLocalPowerClassMap_surjective_of_ker_of_finrank S T hST hT hgen hroots ?_ hdegree
  ext u
  rw [MonoidHom.mem_ker, Set.unitLocalPowerClassMap_eq_one_iff _ _ _ (NeZero.ne n),
    Subtype.forall]
  change (∀ v ∈ T, ∃ c : v.adicCompletion K,
    c ^ n = algebraMap K (v.adicCompletion K) (u : Kˣ)) ↔ _
  rw [hlocal u.1 u.2, Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨Units.mk0 b (ne_zero_of_pow_eq_algebraMap hb), Units.ext hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg (fun x : Lˣ ↦ (x : L)) hb⟩

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
/-- Surjectivity on local power classes supplies the simultaneous unit approximation
used by the idelic norm lemma. -/
theorem exists_sUnit_of_surjective_unitLocalPowerClassMap
    (hsurj : Function.Surjective (Set.unitLocalPowerClassMap S₀ T₀ (by exact_mod_cast hST) n))
    (y : (v : T) → (v.1.adicCompletion K)ˣ)
    (hy : ∀ v, Valued.v (y v : v.1.adicCompletion K) = 1) :
    ∃ u ∈ Uₛ, ∀ v : T,
      (Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom u)⁻¹ * y v ∈
        (powMonoidHom n).range := by
  let y' (v : T) : unitFiltration (v.1.adicCompletion K) 0 :=
    ⟨y v, v.1.mem_unitFiltration_zero_adicCompletion_iff.mpr (hy v)⟩
  obtain ⟨u, hu⟩ := hsurj (fun v ↦ QuotientGroup.mk (y' ⟨v.1, v.2⟩))
  refine ⟨u.1, u.2, fun v ↦ ?_⟩
  let v₀ : T₀ := ⟨v.1, v.2⟩
  have he := congrFun hu v₀
  rw [Set.unitLocalPowerClassMap_apply] at he
  obtain ⟨b, hb⟩ := QuotientGroup.eq.mp he
  exact ⟨b.1, congrArg Subtype.val hb⟩

end Local

end TinyTauDemo
