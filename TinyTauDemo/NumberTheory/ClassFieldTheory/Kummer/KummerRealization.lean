/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Kummer.KummerExistence
public import TinyTauDemo.NumberTheory.ClassFieldTheory.Artin.Classes

/-!
# Realizing prime-order idele-class characters by cyclic extensions

The Artin map of the S-unit Kummer extension factors an open prime-order character.
Restricting Artin to the fixed field of the factored kernel identifies its norm subgroup
with the character kernel.

See J. S. Milne, *Class Field Theory*, VII, Lemma 9.3.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9fa8b1e51d60a6568520e89a452494ca038d4a2a`.
-/

public section

open IsDedekindDomain NumberField IntermediateField TauCeti TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields
open scoped NumberField IsMulCommutative

namespace TinyTauDemo

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  {p : ℕ} [hp : Fact p.Prime] [HasEnoughRootsOfUnity K p]

local notation "Cₖ" => IdeleClassGroup (𝓞 K) K
local notation "Uₛ" S => Set.unit (S : Set (HeightOneSpectrum (𝓞 K))) K
local notation "Mₛ" S => kummerField Ω p (Uₛ S)

private theorem ker_restrict_ideleClassAbelianArtinMap_eq_range_ideleClassNormMap
    {M : Type} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]
    (L : IntermediateField K M) [NumberField L] (hL : (Module.finrank K L).Prime) :
    ((AlgEquiv.restrictNormalHom L).comp (ideleClassAbelianArtinMap K M)).ker =
      (ideleClassNormMap K L).range := by
  rw [ideleClassAbelianArtinMap_restrict]
  exact ker_ideleClassAbelianArtinMap_eq_of_prime_degree K L hL

/-- At a chosen `S` supporting a prime-order idele-class character, the character factors
surjectively through Artin of the S-unit Kummer field. The fixed field of the resulting
kernel has the prescribed norm subgroup. -/
theorem exists_cyclic_norm_realization_at_good_S {G : Type*} [Group G]
    (χ : Cₖ →* G) (hχ : Function.Surjective χ) (hcard : Nat.card G = p)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hcl : Subgroup.closure
      (HeightOneSpectrum.classGroupMk '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤)
    (hpS : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hS : kummerIdeleClassSubgroup S p ≤ χ.ker) :
    ∃ φ : Gal((Mₛ S)/K) →* G,
      φ.comp (ideleClassAbelianArtinMap K (Mₛ S)) = χ ∧ Function.Surjective φ ∧
      let L := IntermediateField.fixedField φ.ker
      IsGalois K L ∧ IsCyclic Gal(L/K) ∧ Module.finrank K L = p ∧
        (ideleClassNormMap K L).range = χ.ker := by
  refine exists_cyclic_norm_realization_at_good_S_of_artin (Ω := Ω) χ hχ hcard S hcl hpS hS
    _ (surjective_ideleClassAbelianArtinMap K (Mₛ S))
    (range_ideleClassNormMap_le_ker_ideleClassAbelianArtinMap K (Mₛ S)) fun L _ hdeg ↦ ?_
  have : NumberField L := NumberField.of_module_finite K L
  have hprime : (Module.finrank K L).Prime := hdeg.symm ▸ hp.out
  exact ker_restrict_ideleClassAbelianArtinMap_eq_range_ideleClassNormMap L hprime

/-- Every surjective prime-order idele-class character with open kernel has that kernel
as the norm subgroup of a cyclic extension of the same degree. The extension lies in the
S-unit Kummer field of some finite `S`. -/
theorem exists_cyclic_norm_realization {G : Type*} [Group G]
    (χ : Cₖ →* G) (hχ : Function.Surjective χ) (hopen : IsOpen (χ.ker : Set Cₖ))
    (hcard : Nat.card G = p) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (L : IntermediateField K (Mₛ S)),
      IsGalois K L ∧ IsCyclic Gal(L/K) ∧ Module.finrank K L = p ∧
      (ideleClassNormMap K L).range = χ.ker := by
  have hann (g : G) : g ^ p = 1 := hcard ▸ pow_card_eq_one'
  obtain ⟨S, hcl, hpS, hS⟩ := exists_kummerIdeleClassSubgroup_le_ker_of_isOpen χ hann hopen
  obtain ⟨φ, -, -, hL, hcyc, hdeg, hnorm⟩ :=
    exists_cyclic_norm_realization_at_good_S (Ω := Ω) χ hχ hcard S hcl hpS (hS S le_rfl)
  exact ⟨S, IntermediateField.fixedField φ.ker, hL, hcyc, hdeg, hnorm⟩

end TinyTauDemo
