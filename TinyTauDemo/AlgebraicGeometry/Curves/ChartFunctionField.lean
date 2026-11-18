/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Dominant
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The generic point of an affine chart

See `/roadmap/index.qmd#rem-scheme-curves-recall @ b87f50dc05d3e4cdf59e8fd97e1a93d6eb8e8bc8`.
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

set_option maxHeartbeats 400000 in
-- The stalk and affine fraction-ring identifications require extra definitional reduction.
/-- The generic point of an integral scheme can be read as the generic point of
any nonempty affine chart, with its function field identified with a fraction field
of the chart ring. -/
theorem exists_functionFieldEquiv_of_affineChart {X : Scheme.{u}} [IsIntegral X]
    {R : CommRingCat.{u}} [IsDomain R] (i : Spec R ⟶ X) [IsOpenImmersion i]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    ∃ e : X.functionField ≃+* F,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X) =
        Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ i := by
  let : IsDominant i := isDominant_iff_genericPoint_eq.mpr (genericPoint_eq_of_isOpenImmersion i)
  have hIsoSpecializes {x y : X} (h : x = y) :
      IsIso (X.presheaf.stalkSpecializes (specializes_of_eq h)) := by
    subst y
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  let : IsIso (X.presheaf.stalkSpecializes
      (specializes_of_eq i.genericPoint_eq_of_isDominant)) :=
    hIsoSpecializes i.genericPoint_eq_of_isDominant
  let d : X.functionField ⟶ (Spec R).functionField :=
    X.presheaf.stalkSpecializes (specializes_of_eq i.genericPoint_eq_of_isDominant) ≫
      i.stalkMap (genericPoint (Spec R))
  let : IsIso d := by dsimp [d]; infer_instance
  let j := (asIso d).commRingCatIsoToRingEquiv
  let e : (Spec R).functionField ≃+* F :=
    IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl R)
  refine ⟨j.trans e, ?_⟩
  change Spec.map (CommRingCat.ofHom (e.toRingHom.comp j.toRingHom)) ≫
      X.fromSpecStalk (genericPoint X) = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map d ≫ X.fromSpecStalk (genericPoint X) = _
  have hd : Spec.map d ≫ X.fromSpecStalk (genericPoint X) =
      (Spec R).fromSpecStalk (genericPoint (Spec R)) ≫ i := by
    dsimp only [d]
    rw [Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hSA : (Spec R).fromSpecStalk (genericPoint (Spec R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField)) :=
    Spec.fromSpecStalk_eq' R _
  rw [hd, hSA, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  apply RingHom.ext
  intro a
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (RingEquiv.refl R) a

/-- A comparison of the generic-point maps on two affine charts identifies the
degree of a scheme morphism with the degree of the corresponding field inclusion. -/
theorem exists_isDominant_finrank_eq_of_affineCharts
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (i : Spec R ⟶ X) (j : Spec S ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (F G : Type u) [Field F] [Field G] [Algebra R F] [Algebra S G] [Algebra G F]
    [IsFractionRing R F] [IsFractionRing S G]
    (f : X ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ i ≫ f =
      Spec.map (CommRingCat.ofHom ((algebraMap G F).comp (algebraMap S G))) ≫ j) :
    ∃ _ : IsDominant f,
      let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
      Module.finrank Y.functionField X.functionField = Module.finrank G F := by
  obtain ⟨eX, heX⟩ := exists_functionFieldEquiv_of_affineChart i F
  obtain ⟨eY, heY⟩ := exists_functionFieldEquiv_of_affineChart j G
  let γ := eX.symm.toRingHom.comp ((algebraMap G F).comp eY.toRingHom)
  have hinv : eX.symm.toRingHom.comp eX.toRingHom = RingHom.id X.functionField := by
    apply RingHom.ext
    intro a
    exact eX.symm_apply_apply a
  have hg : Spec.map (CommRingCat.ofHom γ) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
    have ha : Spec.map (CommRingCat.ofHom γ) ≫ Y.fromSpecStalk (genericPoint Y) =
        Spec.map (CommRingCat.ofHom eX.symm.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap G F)) ≫
            (Spec.map (CommRingCat.ofHom eY.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y))) := by
      simp only [γ, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
    have hb : Spec.map (CommRingCat.ofHom ((algebraMap G F).comp (algebraMap S G))) ≫ j =
        Spec.map (CommRingCat.ofHom (algebraMap G F)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap S G)) ≫ j := by
      simp only [CommRingCat.ofHom_comp, Spec.map_comp_assoc]
    rw [ha, heY, ← hb, ← h,
      ← Category.assoc (Spec.map (CommRingCat.ofHom (algebraMap R F))) i f, ← heX]
    have hi : Spec.map (CommRingCat.ofHom eX.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom eX.toRingHom) = 𝟙 (Spec (.of (X.functionField : Type u))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hinv]
      simp
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom eX.symm.toRingHom)), hi]
    exact Category.id_comp _
  let : IsDominant f := f.isDominant_of_SpecMap_fromSpecStalk (CommRingCat.ofHom γ) hg
  have hγ : CommRingCat.ofHom γ = f.functionFieldMap :=
    (f.eq_functionFieldMap_iff _).mpr hg
  refine ⟨‹IsDominant f›, ?_⟩
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv eY eX
  apply RingHom.ext
  intro a
  change algebraMap G F (eY a) = eX (f.functionFieldMap a)
  rw [← hγ]
  change algebraMap G F (eY a) = eX (eX.symm (algebraMap G F (eY a)))
  exact (eX.apply_symm_apply _).symm

end AlgebraicGeometry
