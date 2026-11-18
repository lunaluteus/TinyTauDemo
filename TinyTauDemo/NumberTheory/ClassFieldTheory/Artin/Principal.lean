/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.BrauerReciprocity
public import TinyTauDemo.NumberTheory.ClassFieldTheory.Artin.Ideles
import TauCeti.Algebra.Module.CharacterModule
import TauCeti.NumberTheory.ClassFieldTheory.Global.CharacterCarry

/-!
# The Artin product on principal ideles

Testing the product with a Galois character turns it into the sum of the local invariants of a
global carry class. The Brauer sum formula gives the principal-idele product formula.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IsDedekindDomain TauCeti TauCeti.ClassFieldTheory ContCohomology
open scoped NumberField

namespace TinyTauDemo

/-- The product of the local Artin symbols of a principal idele is one. -/
theorem ideleArtinMap_unitEmbedding_intermediateField
    (K : Type) [Field K] [NumberField K] (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [NumberField E] [IsGalois K E] (a : Kˣ) :
    ideleArtinMap K E (IdeleGroup.unitEmbedding (𝓞 K) K a) = 1 := by
  classical
  let x := IdeleGroup.unitEmbedding (𝓞 K) K a
  change Additive.ofMul (ideleArtinMap K E x) = 0
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  let χ₀ : Additive (E ≃ₐ[K] E) →+ AddCircle (1 : ℚ) :=
    χ.comp Abelianization.of.toAdditive
  let χG : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ) :=
    χ₀.comp (AlgEquiv.restrictNormalHom (K₁ := SeparableClosure K) E).toAdditive
  have hχ : IsOpen (χG.ker : Set (Additive (AbsoluteGaloisGroup K))) :=
    E.isOpen_ker_comp_restrictNormalHom χ₀
  let τ (v : HeightOneSpectrum (𝓞 K)) :
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K) := IsSepClosed.lift
  let τ' (w : InfinitePlace K) :
      SeparableClosure K →ₐ[K] SeparableClosure w.Completion := IsSepClosed.lift
  choose σ hσ using fun v : HeightOneSpectrum (𝓞 K) ↦ QuotientGroup.mk_surjective
    (artinMap (v.adicCompletion K) (Units.map (algebraMap K (v.adicCompletion K)) a))
  choose σ' hσ' using fun w : InfinitePlace K ↦ QuotientGroup.mk_surjective
    (infiniteArtinAt w (Units.map (algebraMap K w.Completion) a))
  let X := unitsRepH2Equiv K
    (characterCarryCocycle χG hχ (baseUnitsEquivInvariants K (.ofMul a)))
  have hsum := sumLocalInv_brLocalization_characterCarryCocycle_eq_finsum
    χG hχ a τ σ τ' σ' hσ hσ'
  have hzero : sumLocalInv K (brLocalization K X) = 0 :=
    sumLocalInv_brLocalization_eq_zero K X
  change sumLocalInv K (brLocalization K X) = _ at hsum
  rw [hzero] at hsum
  let f (v : HeightOneSpectrum (𝓞 K)) := finiteLocalArtinAt K E v (v.ideleFiniteCoord x)
  let g (w : InfinitePlace K) := infiniteLocalArtinAt K E w (w.ideleInfiniteCoord x)
  have hrest (u : AbsoluteGaloisGroup K) :
      E.val.restrictNormalHom u =
        AlgEquiv.restrictNormalHom (K₁ := SeparableClosure K) E u := by
    refine AlgEquiv.ext fun z ↦ Subtype.ext ?_
    change E.val (E.val.restrictNormalHom u z) = _
    rw [AlgHom.restrictNormalHom_commutes]
    exact (AlgEquiv.restrictNormal_commutes u E z).symm
  have hfinite (v : HeightOneSpectrum (𝓞 K)) :
      χ (.ofMul (f v)) = χG (.ofMul (absoluteGaloisGroupMap (τ v)
        (absoluteGaloisGroupRestrictEquiv (v.adicCompletion K) (σ v)))) := by
    change χ (.ofMul (finiteLocalArtinAt K E v (v.ideleFiniteCoord
      (IdeleGroup.unitEmbedding (𝓞 K) K a)))) = _
    rw [HeightOneSpectrum.ideleFiniteCoord_unitEmbedding, finiteLocalArtinAt_apply]
    erw [← hσ v]
    rw [decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap E.val (τ v), hrest]
    rfl
  have hinfinite (w : InfinitePlace K) :
      χ (.ofMul (g w)) = χG (.ofMul (absoluteGaloisGroupMap (τ' w)
        (absoluteGaloisGroupRestrictEquiv w.Completion (σ' w)))) := by
    change χ (.ofMul (infiniteLocalArtinAt K E w (w.ideleInfiniteCoord
      (IdeleGroup.unitEmbedding (𝓞 K) K a)))) = _
    rw [InfinitePlace.ideleInfiniteCoord_unitEmbedding, infiniteLocalArtinAt_apply]
    erw [← hσ' w]
    rw [decompositionRestrict_mk_eq_restrictNormalHom_absoluteGaloisGroupMap E.val (τ' w), hrest]
    rfl
  simp_rw [← hfinite, ← hinfinite] at hsum
  have hf : Function.HasFiniteMulSupport f := hasFiniteMulSupport_finiteLocalArtinAt_idele K E x
  rw [ideleArtinMap_apply]
  change χ (.ofMul ((∏ᶠ v, f v) * ∏ w, g w)) = 0
  rw [ofMul_mul, map_add, finprod_eq_prod f hf]
  simp only [ofMul_prod, map_sum]
  rw [← finsum_eq_sum_of_support_subset _ (s := hf.toFinset)]
  · exact hsum.symm
  · intro v hv
    apply hf.mem_toFinset.mpr
    intro he
    exact hv (by simp [he])

end TinyTauDemo
