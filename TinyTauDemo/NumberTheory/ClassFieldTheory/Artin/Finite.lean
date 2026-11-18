/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.DecompositionRestrict
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import Mathlib.FieldTheory.Galois.Abelian
import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# The finite local Artin symbol in a number field extension

The absolute local Artin map restricts to the abelianized decomposition group and then maps to
the abelianized global Galois group. For abelian extensions the completed norm group is its
kernel. The symbol detects unramifiedness through the units of the completed integer ring.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti TauCeti.ClassFieldTheory
open scoped NumberField Pointwise AdicCompletionExtension

namespace TinyTauDemo

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The local Artin symbol at a finite place, read in the abelianized global Galois group. -/
noncomputable def finiteLocalArtinAt (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Abelianization (L ≃ₐ[K] L) :=
  (decompositionRestrict K (v.adicCompletion K) L).comp (artinMap (v.adicCompletion K))

theorem finiteLocalArtinAt_apply (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    finiteLocalArtinAt K L v x =
      decompositionRestrict K (v.adicCompletion K) L (artinMap (v.adicCompletion K) x) := by
  rw [finiteLocalArtinAt, MonoidHom.comp_apply]

variable {K L} (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Evaluate the finite Artin symbol by restricting the local Artin symbol on the completion
to the global field. -/
theorem finiteLocalArtinAt_eq_map_localArtinMap (x : (v.adicCompletion K)ˣ)
    (ι : w.adicCompletion L →ₐ[v.adicCompletion K]
      SeparableClosure (v.adicCompletion K)) :
    finiteLocalArtinAt K L v x =
      Abelianization.map ((AlgEquiv.restrictNormalHom L).comp
        (AlgEquiv.restrictScalarsHom K))
        (Additive.toMul (localArtinMap (v.adicCompletion K)
          (w.adicCompletion L) ι (Additive.ofMul x))) := by
  let B := v.adicCompletion K
  let W := w.adicCompletion L
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (artinMap B x)
  have hlocal := artinMap_restrict B W ι x τ hτ
  let D : (W ≃ₐ[B] W) →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  let j : L →ₐ[K] AlgebraicClosure B :=
    ((((separableClosure B (AlgebraicClosure B)).val.comp ι).restrictScalars K).comp
      (IsScalarTower.toAlgHom K L W))
  rw [finiteLocalArtinAt, MonoidHom.comp_apply, ← hτ, hlocal, toMul_ofMul,
    Abelianization.map_of]
  apply decompositionRestrict_mk j τ _
  intro y
  let σW := ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv B τ)
  change (separableClosure B (AlgebraicClosure B)).val
      (ι (algebraMap L W (D σW y))) = _
  have hD : algebraMap L W (D σW y) = σW (algebraMap L W y) :=
    AlgEquiv.restrictNormal_commutes (σW.restrictScalars K) L y
  rw [hD]
  change (separableClosure B (AlgebraicClosure B)).val
    (ι (ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv B τ) (algebraMap L W y))) = _
  rw [AlgHom.restrictNormalHom_commutes]
  exact coe_absoluteGaloisGroupRestrictEquiv_apply B τ (ι (algebraMap L W y))
/-- The finite Artin symbol is the local symbol of the completed extension, mapped through
the decomposition subgroup. -/
theorem finiteLocalArtinAt_eq_of_decompositionHom {x : (v.adicCompletion K)ˣ}
    (ι : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K))
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
    (h : localArtinMap (v.adicCompletion K) (w.adicCompletion L) ι (Additive.ofMul x) =
      Additive.ofMul (Abelianization.of (decompositionHom v w σ))) :
    finiteLocalArtinAt K L v x = Abelianization.of (σ : L ≃ₐ[K] L) := by
  rw [finiteLocalArtinAt_eq_map_localArtinMap v w x ι, h, toMul_ofMul, Abelianization.map_of]
  exact congrArg Abelianization.of
    (restrictNormalHom_restrictScalarsHom_decompositionHom (v := v) σ)

/-- Every ideal decomposition automorphism occurs as the local symbol of a completion unit. -/
theorem exists_finiteLocalArtinAt_eq_decomposition
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ∃ x : (v.adicCompletion K)ˣ, finiteLocalArtinAt K L v x =
      Abelianization.of (σ : L ≃ₐ[K] L) := by
  let ι : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  obtain ⟨x, hx⟩ := surjective_localArtinMap (v.adicCompletion K) (w.adicCompletion L) ι
    (Additive.ofMul (Abelianization.of (decompositionHom v w σ)))
  exact ⟨Additive.toMul x, finiteLocalArtinAt_eq_of_decompositionHom v w ι σ hx⟩

/-- Norms from a completed field have trivial global finite local symbol. -/
theorem finiteLocalArtinAt_eq_one_of_mem_normGroup {x : (v.adicCompletion K)ˣ}
    (h : x ∈ normGroup (v.adicCompletion K) (w.adicCompletion L)) :
    finiteLocalArtinAt K L v x = 1 := by
  let ι : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  have h₁ := (localArtinMap_eq_zero_iff (v.adicCompletion K) (w.adicCompletion L) ι x).mpr h
  simpa using finiteLocalArtinAt_eq_of_decompositionHom v w ι 1 (by simpa using h₁)

/-- An automorphism of a completed Galois extension is determined by its restriction to the
global field. -/
theorem injective_restrictNormalHom_adicCompletion : Function.Injective
    ((AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K) :
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) →* (L ≃ₐ[K] L)) := by
  intro f g h
  obtain ⟨σ, rfl⟩ := decompositionHom_surjective v w f
  obtain ⟨τ, rfl⟩ := decompositionHom_surjective v w g
  apply congrArg (decompositionHom v w)
  apply Subtype.ext
  simpa only [restrictNormalHom_restrictScalarsHom_decompositionHom] using h

open scoped IsMulCommutative in
/-- For an abelian global extension, the finite local Artin symbol is one exactly on norms
from the completed extension. -/
theorem finiteLocalArtinAt_eq_one_iff_mem_normGroup [IsMulCommutative (L ≃ₐ[K] L)]
    (x : (v.adicCompletion K)ˣ) :
    finiteLocalArtinAt K L v x = 1 ↔
      x ∈ normGroup (v.adicCompletion K) (w.adicCompletion L) := by
  let B := v.adicCompletion K
  let W := w.adicCompletion L
  let ι : W →ₐ[B] SeparableClosure B := IsSepClosed.lift
  let D : (W ≃ₐ[B] W) →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  have hD : Function.Injective D := injective_restrictNormalHom_adicCompletion v w
  have hmap : Function.Injective (Abelianization.map D) := by
    intro a b h
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
    change Abelianization.map D (Abelianization.of α) =
      Abelianization.map D (Abelianization.of β) at h
    rw [Abelianization.map_of, Abelianization.map_of] at h
    exact congrArg Abelianization.of (hD (Abelianization.equivOfComm.injective h))
  rw [finiteLocalArtinAt_eq_map_localArtinMap v w x ι]
  change Abelianization.map D _ = 1 ↔ _
  rw [← map_one (Abelianization.map D), hmap.eq_iff, toMul_eq_one,
    localArtinMap_eq_zero_iff]

open scoped IsMulCommutative in
/-- In an abelian extension, a finite prime is unramified exactly when the finite local
Artin symbol is trivial on all units of the completed integer ring. -/
theorem isUnramifiedAt_iff_unitFiltration_le_ker_finiteLocalArtinAt
    [IsMulCommutative (L ≃ₐ[K] L)] :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ↔
      unitFiltration (v.adicCompletion K) 0 ≤ (finiteLocalArtinAt K L v).ker := by
  let B := v.adicCompletion K
  let W := w.adicCompletion L
  let D : (W ≃ₐ[B] W) →* (L ≃ₐ[K] L) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  have hD : Function.Injective D := injective_restrictNormalHom_adicCompletion v w
  let : IsAbelianGalois B W := {
    is_comm.comm := fun a b ↦ hD (by rw [map_mul, map_mul, mul_comm]) }
  calc
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ↔ IsUnramified B W := by
      rw [isUnramified_iff_ramificationIndex_eq_one, ramificationIndex_adicCompletion v w,
        Ideal.ramificationIdx_eq_one_iff]
    _ ↔ conductorExponent B W = 0 := (conductorExponent_eq_zero_iff B W).symm
    _ ↔ unitFiltration B 0 ≤ normGroup B W := by
      rw [← Nat.le_zero, conductorExponent_le_iff]
    _ ↔ unitFiltration B 0 ≤ (finiteLocalArtinAt K L v).ker := by
      exact forall₂_congr fun x _ ↦
        (finiteLocalArtinAt_eq_one_iff_mem_normGroup v w x).symm

end TinyTauDemo
