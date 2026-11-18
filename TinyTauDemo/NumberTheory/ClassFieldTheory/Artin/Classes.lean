/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Artin.Principal
import TauCeti.FieldTheory.Galois.Restriction

/-!
# Global Artin reciprocity on idele classes

The product formula makes the Artin product descend to idele classes. In abelian extensions
the result is a surjection to the Galois group. Its kernel is the norm group whenever the norm
index divides the degree, in particular in prime degree.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IsDedekindDomain TauCeti TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped NumberField IsMulCommutative

namespace TinyTauDemo

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

section Galois

variable [IsGalois K L]

/-- The idele Artin product is compatible with restriction to a Galois subextension. -/
theorem ideleArtinMap_comp {M : Type} [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (j : M →ₐ[K] L) :
    (Abelianization.map j.restrictNormalHom).comp (ideleArtinMap K L) = ideleArtinMap K M := by
  ext x
  rw [MonoidHom.comp_apply, ideleArtinMap_apply, map_mul,
    map_finprod _ (hasFiniteMulSupport_finiteLocalArtinAt_idele K L x), map_prod,
    ideleArtinMap_apply]
  congr 1
  · apply finprod_congr
    intro v
    rw [finiteLocalArtinAt_apply, finiteLocalArtinAt_apply, ← MonoidHom.comp_apply,
      decompositionRestrict_comp]
  · apply Finset.prod_congr rfl
    intro w _
    rw [← MonoidHom.comp_apply, infiniteLocalArtinAt_comp]

/-- The principal ideles have trivial global Artin product. -/
theorem ideleArtinMap_unitEmbedding (a : Kˣ) :
    ideleArtinMap K L (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let E := j.fieldRange
  have : FiniteDimensional K E := j.equivFieldRange.toLinearEquiv.finiteDimensional
  have : NumberField E := .of_module_finite K _
  have : IsGalois K E := IsGalois.of_algEquiv j.equivFieldRange
  have h := DFunLike.congr_fun (ideleArtinMap_comp K E j.equivFieldRange.toAlgHom)
    (IdeleGroup.unitEmbedding (𝓞 K) K a)
  rw [MonoidHom.comp_apply,
    ideleArtinMap_unitEmbedding_intermediateField, map_one] at h
  exact h.symm

private theorem principalSubgroup_le_ker_ideleArtinMap :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ (ideleArtinMap K L).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleArtinMap_unitEmbedding K L a

/-- The global Artin map is the product of local Artin symbols on idele classes. -/
noncomputable def ideleClassArtinMap :
    IdeleClassGroup (𝓞 K) K →* Abelianization (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleArtinMap K L) (principalSubgroup_le_ker_ideleArtinMap K L)

@[simp]
theorem ideleClassArtinMap_mk (x : IdeleGroup (𝓞 K) K) :
    ideleClassArtinMap K L (x : IdeleClassGroup (𝓞 K) K) = ideleArtinMap K L x := by
  rw [ideleClassArtinMap, QuotientGroup.lift_mk]

/-- The Artin map on idele classes is compatible with restriction to Galois subextensions. -/
theorem ideleClassArtinMap_comp {M : Type} [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (j : M →ₐ[K] L) :
    (Abelianization.map j.restrictNormalHom).comp (ideleClassArtinMap K L) =
      ideleClassArtinMap K M := by
  apply QuotientGroup.monoidHom_ext
  ext x
  simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, ideleClassArtinMap_mk] using
    DFunLike.congr_fun (ideleArtinMap_comp K L j) x

/-- Every idele class norm lies in the kernel of the global Artin map. -/
theorem range_ideleClassNormMap_le_ker_ideleClassArtinMap :
    (ideleClassNormMap K L).range ≤ (ideleClassArtinMap K L).ker := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  change ideleClassArtinMap K L (ideleClassNormMap K L (x : IdeleClassGroup (𝓞 L) L)) = 1
  rw [ideleClassNormMap_mk, ideleClassArtinMap_mk, ideleArtinMap_ideleNormMap]

/-- The Artin map surjects onto the abelianization for a solvable extension. -/
theorem surjective_ideleClassArtinMap [Group.IsSolvable (L ≃ₐ[K] L)] :
    Function.Surjective (ideleClassArtinMap K L) := by
  intro y
  obtain ⟨x, rfl⟩ := surjective_ideleArtinMap K L y
  exact ⟨(x : IdeleClassGroup (𝓞 K) K), ideleClassArtinMap_mk K L x⟩

end Galois

section Abelian

variable [IsAbelianGalois K L]

/-- For an abelian extension the Artin map takes values in the Galois group. -/
noncomputable def ideleClassAbelianArtinMap : IdeleClassGroup (𝓞 K) K →* (L ≃ₐ[K] L) :=
  Abelianization.equivOfComm.symm.toMonoidHom.comp (ideleClassArtinMap K L)

@[simp]
theorem abelianization_of_ideleClassAbelianArtinMap (c : IdeleClassGroup (𝓞 K) K) :
    Abelianization.of (ideleClassAbelianArtinMap K L c) = ideleClassArtinMap K L c := by
  rw [ideleClassAbelianArtinMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact Abelianization.equivOfComm.apply_symm_apply _

/-- The Artin map of an abelian extension is surjective. -/
theorem surjective_ideleClassAbelianArtinMap :
    Function.Surjective (ideleClassAbelianArtinMap K L) :=
  Abelianization.equivOfComm.symm.surjective.comp (surjective_ideleClassArtinMap K L)

/-- The Artin map commutes with restriction to an intermediate field in an abelian extension. -/
theorem ideleClassAbelianArtinMap_restrict (M : IntermediateField K L) [NumberField M] :
    (AlgEquiv.restrictNormalHom M).comp (ideleClassAbelianArtinMap K L) =
      ideleClassAbelianArtinMap K M := by
  refine MonoidHom.ext fun c ↦ ?_
  apply (Abelianization.equivOfComm (H := M ≃ₐ[K] M)).injective
  change Abelianization.of _ = Abelianization.of _
  rw [MonoidHom.comp_apply, abelianization_of_ideleClassAbelianArtinMap,
    ← Abelianization.map_of, abelianization_of_ideleClassAbelianArtinMap,
    ← MonoidHom.comp_apply, ← M.restrictNormalHom_val, ideleClassArtinMap_comp]

/-- The norm group of an abelian extension lies in the kernel of its Artin map. -/
theorem range_ideleClassNormMap_le_ker_ideleClassAbelianArtinMap :
    (ideleClassNormMap K L).range ≤ (ideleClassAbelianArtinMap K L).ker := by
  intro c hc
  apply (Abelianization.equivOfComm (H := L ≃ₐ[K] L)).injective
  change Abelianization.of (ideleClassAbelianArtinMap K L c) = Abelianization.of 1
  rw [abelianization_of_ideleClassAbelianArtinMap, map_one]
  exact range_ideleClassNormMap_le_ker_ideleClassArtinMap K L hc

/-- If the norm index divides the degree, the Artin kernel is exactly the norm group. -/
theorem ker_ideleClassAbelianArtinMap_eq_of_index_dvd
    (h : (ideleClassNormMap K L).range.index ∣ Module.finrank K L) :
    (ideleClassAbelianArtinMap K L).ker = (ideleClassNormMap K L).range := by
  let f := ideleClassAbelianArtinMap K L
  have hidx : f.ker.index = Module.finrank K L := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (surjective_ideleClassAbelianArtinMap K L),
      Subgroup.card_top, IsGalois.card_aut_eq_finrank]
  exact (Subgroup.eq_of_index_dvd_index
    (range_ideleClassNormMap_le_ker_ideleClassAbelianArtinMap K L) (hidx ▸ h)).symm

/-- For a prime-degree abelian extension the Artin kernel is exactly the norm group. -/
theorem ker_ideleClassAbelianArtinMap_eq_of_prime_degree (hp : (Module.finrank K L).Prime) :
    (ideleClassAbelianArtinMap K L).ker = (ideleClassNormMap K L).range :=
  ker_ideleClassAbelianArtinMap_eq_of_index_dvd K L
    (index_range_ideleClassNormMap_eq_of_prime_degree K L hp).dvd

end Abelian

end TinyTauDemo
