/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatCharts
public import TinyTauDemo.FermatAffineFunctionField
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv
import TauCeti.FieldTheory.FunctionField.PlaneCurve.Basic

/-!
# The function field of the projective Fermat scheme

See `/roadmap/index.qmd#prp-fermat-genus` @ `fbc988a5bcd0d78cdb5b294d62d21b7c0f620a09`.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped IntermediateField

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k]

noncomputable instance fermatProjective_over (n : ℕ) :
    (fermatProjective k n).Over (Spec (.of k)) :=
  ⟨fermatProjectiveToSpec k n⟩

variable {n : ℕ}

private noncomputable abbrev zChart (hn : 0 < n) :
    Spec (.of (FermatAffineRing k n 2)) ⟶ fermatProjective k n :=
  fermatAffineChart k hn 2

private theorem zChart_over (hn : 0 < n) :
    zChart k hn ≫ (fermatProjective k n ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (FermatAffineRing k n 2))) :=
  fermatAffineChart_comp_toSpec k hn 2

private theorem zChart_nonempty (hn : 0 < n) :
    Nonempty (Spec (.of (FermatAffineRing k n 2))) :=
  PrimeSpectrum.nonempty_iff_nontrivial.mpr (fermatAffineRing_nontrivial_two k hn)

private theorem zChart_isAffineOpen (hn : 0 < n) : IsAffineOpen (zChart k hn ''ᵁ ⊤) := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

private theorem zChartOpen_nonempty (hn : 0 < n) : Nonempty (zChart k hn ''ᵁ ⊤) := by
  obtain ⟨a⟩ := zChart_nonempty k hn
  exact ⟨⟨zChart k hn a, ⟨a, trivial, rfl⟩⟩⟩

private noncomputable def zChartSections (hn : 0 < n) :
    Γ(fermatProjective k n, zChart k hn ''ᵁ ⊤) ≃+* FermatAffineRing k n 2 :=
  ((zChart k hn).appIso ⊤ ≪≫ Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv

private theorem zChartSections_appLE (hn : 0 < n) (a : Γ(Spec (.of k), ⊤)) :
    zChartSections k hn ((fermatProjective k n ↘ Spec (.of k)).appLE ⊤ _ le_top a) =
      algebraMap k (FermatAffineRing k n 2) ((Scheme.ΓSpecIso (.of k)).hom a) := by
  suffices h : (fermatProjective k n ↘ Spec (.of k)).appLE ⊤ _ le_top ≫
        ((zChart k hn).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      (Scheme.ΓSpecIso (.of k)).hom ≫
        CommRingCat.ofHom (algebraMap k (FermatAffineRing k n 2)) by
    change (((zChart k hn).appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom)
      ((fermatProjective k n ↘ Spec (.of k)).appLE ⊤ _ le_top a) = _
    rw [← CommRingCat.comp_apply, h]
    rfl
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv, Iso.inv_hom_id_assoc, Scheme.Hom.appIso_hom',
    reassoc_of% Scheme.Hom.appLE_comp_appLE (zChart k hn)
      (fermatProjective k n ↘ Spec (.of k)) ⊤ (zChart k hn ''ᵁ ⊤) ⊤ le_top
      (Scheme.Hom.preimage_image_eq _ _).ge]
  rw [show Scheme.Hom.appLE _ ⊤ ⊤ _ = Scheme.Hom.appTop _ from Scheme.Hom.appLE_eq_app _,
    zChart_over, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

variable [CharZero k] [IsAlgClosed k]

private theorem zChartRing_isDomain (hn : 0 < n) : IsDomain (FermatAffineRing k n 2) := by
  have := fermatProjective_isIntegral k hn
  have := zChart_nonempty k hn
  exact (affine_isIntegral_iff _).mp (isIntegral_of_isOpenImmersion (zChart k hn))

/-- The function field of the projective model is the fraction field of its last affine chart. -/
noncomputable def fermatProjectiveFunctionFieldEquiv (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    (fermatProjective k n).functionField ≃ₐ[k] FractionRing (FermatAffineRing k n 2) := by
  have := fermatProjective_isIntegral k hn
  have := zChartRing_isDomain k hn
  have := zChartOpen_nonempty k hn
  have := functionField_isFractionRing_of_isAffineOpen _ _ (zChart_isAffineOpen k hn)
  refine AlgEquiv.ofRingEquiv (f := IsFractionRing.ringEquivOfRingEquiv (zChartSections k hn))
    fun c => ?_
  rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField,
    Scheme.baseRingToFunctionField_eq_comp_appLE k _ (zChart k hn ''ᵁ ⊤), RingHom.comp_apply]
  refine (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _).trans ?_
  rw [CommRingCat.comp_apply, zChartSections_appLE, Iso.inv_hom_id_apply]
  exact (IsScalarTower.algebraMap_apply k _ (FractionRing (FermatAffineRing k n 2)) c).symm

/-- The function field of the projective Fermat curve has the Fermat plane-curve genus. -/
theorem genus_fermatProjective_functionField (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    TauCeti.genus k (fermatProjective k n).functionField = (n - 1) * (n - 2) / 2 := by
  have := fermatProjective_isIntegral k hn
  have := zChartRing_isDomain k hn
  let e := fermatProjectiveFunctionFieldEquiv k hn
  have hg := TauCeti.genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv (fun c => e.commutes c)
  rw [← hg]
  exact genus_fermatAffineFractionField (n := n) k _ hn

/-- The two coordinate ratios on the last chart generate the function field of the projective
curve, and the first ratio is transcendental. -/
theorem fermatProjective_functionField_coordinates (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    let F := (fermatProjective k n).functionField
    ∃ x y : F, Transcendental k x ∧ k⟮x, y⟯ = ⊤ ∧ x ^ n + y ^ n = 1 := by
  have := fermatProjective_isIntegral k hn
  have := zChartRing_isDomain k hn
  let e := fermatProjectiveFunctionFieldEquiv k hn
  obtain ⟨x, y, hx, hgen, hxy⟩ :=
    fermatAffineFractionField_coordinates (n := n) k (FractionRing (FermatAffineRing k n 2)) hn
  refine ⟨e.symm x, e.symm y, ?_, ?_, ?_⟩
  · exact (not_congr (isAlgebraic_algHom_iff e.symm.toAlgHom e.symm.injective)).mpr hx
  · let f := e.symm.toAlgHom
    change IntermediateField.adjoin k {f x, f y} = ⊤
    rw [← Set.image_pair, ← IntermediateField.adjoin_map _ _ f, hgen, ← AlgHom.fieldRange_eq_map]
    exact e.symm.fieldRange_eq_top
  · have h := congrArg e.symm hxy
    simpa only [map_add, map_pow, map_one] using h

/-- The function field of the projective Fermat model is an algebraic function field over k. -/
theorem fermatProjective_isFunctionField (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    TauCeti.IsFunctionField k (fermatProjective k n).functionField := by
  have := fermatProjective_isIntegral k hn
  obtain ⟨x, y, hx, hgen, hxy⟩ := fermatProjective_functionField_coordinates k hn
  let g : MvPolynomial (Fin 2) k := MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1
  have hg : g ≠ 0 := by
    intro he
    have h0 := congrArg (MvPolynomial.aeval (fun _ : Fin 2 => (0 : k))) he
    simp [g, zero_pow hn.ne'] at h0
  exact TauCeti.isFunctionField_of_aeval_eq_zero hg hx hgen (by simp [g, hxy])

/-- The coefficient field is the exact constant field of the projective Fermat curve. -/
theorem fermatProjective_isIntegrallyClosedIn (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    IsIntegrallyClosedIn k (fermatProjective k n).functionField := by
  have := fermatProjective_isIntegral k hn
  obtain ⟨x, y, hx, hgen, hxy⟩ := fermatProjective_functionField_coordinates k hn
  exact isIntegrallyClosedIn_of_fermatEquation hn hx hgen hxy

end TinyTauDemo
