/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatSchemeGenus
public import TinyTauDemo.AlgebraicGeometry.Curves.ProjectiveLineCharts
import TinyTauDemo.AlgebraicGeometry.Curves.DenseOpenExtension
import TinyTauDemo.AlgebraicGeometry.Curves.ChartFunctionField
public import TinyTauDemo.AlgebraicGeometry.Curves.FiniteCurveMorphisms
import TinyTauDemo.AlgebraicGeometry.Curves.ProjectiveLineDifferentials
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The projection of the Fermat curve to the projective line

The last affine chart gives the map defined by the ratio `X/Z`. The map extends
uniquely to the curve. The extension has degree equal to the exponent, as is
computed on the function fields of the two affine charts.

See `/roadmap/index.qmd#prp-fermat-genus` @ `baac39b56ab0e308195904f79c46c65fadbb5c32`.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial
open TauCeti.AlgebraicGeometry
open scoped IntermediateField

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k] {n : ℕ}

/-- The projection to the first coordinate on the chart `Z ≠ 0`. The target
coordinate `t` maps to `X/Z`. -/
noncomputable def fermatProjectionOnLastChart (n : ℕ) :
    Spec (.of (FermatAffineRing k n 2)) ⟶ projectiveLine k :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := k)
    (Ideal.Quotient.mk _ (MvPolynomial.X (0 : Fin 2)) :
      FermatAffineRing k n 2)).toRingHom) ≫ projectiveLinePolynomialChart k 0

/-- The last-chart projection is induced by evaluation at the image of `X₀`. -/
theorem fermatProjectionOnLastChart_def (n : ℕ) :
    fermatProjectionOnLastChart k n =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := k)
        (Ideal.Quotient.mk _ (MvPolynomial.X (0 : Fin 2)) :
          FermatAffineRing k n 2)).toRingHom) ≫ projectiveLinePolynomialChart k 0 := by
  unfold fermatProjectionOnLastChart
  rfl

private theorem fermatProjectionOnLastChart_toSpec (n : ℕ) :
    fermatProjectionOnLastChart k n ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (FermatAffineRing k n 2))) := by
  rw [fermatProjectionOnLastChart, Category.assoc, projectiveLinePolynomialChart_toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  exact (Polynomial.aeval _).commutes a

variable [CharZero k] [IsAlgClosed k]

/-- The concrete last-chart coordinate projection extends uniquely to a
morphism from the projective Fermat curve to the projective line. -/
theorem existsUnique_fermatProjection (hn : 0 < n) :
    ∃! f : fermatProjective k n ⟶ projectiveLine k,
      f.IsOver (Spec (.of k)) ∧
        fermatAffineChart k hn 2 ≫ f = fermatProjectionOnLastChart k n := by
  let X := fermatProjective k n
  let Y := projectiveLine k
  let S := Spec (.of k)
  let : IsIntegral X := fermatProjective_isIntegral k hn
  let : SmoothOfRelativeDimension 1 (X ↘ S) := fermatProjective_smoothOne k hn
  let i := fermatAffineChart k hn 2
  let U := i.opensRange
  let g := i.isoOpensRange.inv ≫ fermatProjectionOnLastChart k n
  let : g.IsOver S := by
    rw [Scheme.Hom.isOver_iff]
    change (i.isoOpensRange.inv ≫ fermatProjectionOnLastChart k n) ≫ (Y ↘ S) = U.ι ≫ (X ↘ S)
    rw [Category.assoc, fermatProjectionOnLastChart_toSpec k n,
      ← fermatAffineChart_comp_toSpec k hn 2, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp]
    rfl
  have hU : Dense (U : Set X) := by
    apply U.isOpen.dense
    have : Nonempty (Spec (.of (FermatAffineRing k n 2))) :=
      PrimeSpectrum.nonempty_iff_nontrivial.mpr (fermatAffineRing_nontrivial_two k hn)
    obtain ⟨x⟩ := this
    exact ⟨i x, ⟨x, rfl⟩⟩
  obtain ⟨f, ⟨hfS, hfU⟩, hfuniq⟩ :=
    existsUnique_hom_extending_denseOpen_of_smoothCurve k U hU g
  refine ⟨f, ⟨hfS, ?_⟩, fun f' hf' ↦ ?_⟩
  · change i ≫ f = fermatProjectionOnLastChart k n
    rw [← i.isoOpensRange_hom_ι, Category.assoc, hfU]
    simp [g]
  · apply hfuniq
    refine ⟨hf'.1, ?_⟩
    have hchart : i ≫ f' = fermatProjectionOnLastChart k n := hf'.2
    rw [← cancel_epi i.isoOpensRange.hom, i.isoOpensRange_hom_ι_assoc, hchart]
    simp [g]

/-- The projective Fermat projection with affine coordinate `X/Z`. -/
noncomputable def fermatProjection (hn : 0 < n) :
    fermatProjective k n ⟶ projectiveLine k := (existsUnique_fermatProjection k hn).exists.choose

instance (hn : 0 < n) : (fermatProjection k hn).IsOver (Spec (.of k)) :=
  (existsUnique_fermatProjection k hn).exists.choose_spec.1

/-- On the last affine chart, the projective Fermat projection is the actual
coordinate morphism `t ↦ X/Z`. -/
theorem fermatAffineChart_comp_fermatProjection (hn : 0 < n) :
    fermatAffineChart k hn 2 ≫ fermatProjection k hn = fermatProjectionOnLastChart k n :=
  (existsUnique_fermatProjection k hn).exists.choose_spec.2

/-- The actual projection from the Fermat curve to the projective line is
dominant and has degree `n` on function fields. -/
private theorem fermatProjection_degree (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    ∃ _ : IsDominant (fermatProjection k hn),
      let : Algebra (projectiveLine k).functionField (fermatProjective k n).functionField :=
        (fermatProjection k hn).functionFieldMap.hom.toAlgebra
      Module.finrank (projectiveLine k).functionField (fermatProjective k n).functionField = n := by
  let : IsIntegral (fermatProjective k n) := fermatProjective_isIntegral k hn
  let A := FermatAffineRing k n 2
  let i := fermatAffineChart k hn 2
  let j := projectiveLinePolynomialChart k 0
  have : Nonempty (Spec (.of A)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr (fermatAffineRing_nontrivial_two k hn)
  have : IsDomain A := (affine_isIntegral_iff _).mp (isIntegral_of_isOpenImmersion i)
  let F := FractionRing A
  let x₀ : A := Ideal.Quotient.mk _ (MvPolynomial.X (0 : Fin 2))
  let y₀ : A := Ideal.Quotient.mk _ (MvPolynomial.X (1 : Fin 2))
  let x := algebraMap A F x₀
  let y := algebraMap A F y₀
  obtain ⟨hx, hgen, hxy⟩ := fermatAffineFractionField_explicit_coordinates k F hn
  have hx' : Transcendental k x := hx
  have hgen' : k⟮x, y⟯ = ⊤ := hgen
  let e := RatFunc.algEquivOfTranscendental x hx'
  let φ := (IntermediateField.val k⟮x⟯).comp e.toAlgHom
  let : Algebra (RatFunc k) F := φ.toRingHom.toAlgebra
  let : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have hX : algebraMap (RatFunc k) F RatFunc.X = x :=
    RatFunc.algEquivOfTranscendental_X x hx'
  let E := (RatFunc k)⟮y⟯
  have hgenRat : E = ⊤ := by
    have hle : k⟮x, y⟯ ≤ E.restrictScalars k := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro a (he | ha)
      · subst a
        change x ∈ E
        rw [← hX]
        exact E.algebraMap_mem RatFunc.X
      · have he : a = y := Set.mem_singleton_iff.mp ha
        subst a
        exact IntermediateField.mem_adjoin_simple_self _ _
    apply top_unique
    intro a _
    have ha : a ∈ (⊤ : IntermediateField k F) := trivial
    rw [← hgen'] at ha
    exact hle ha
  have hdegree : Module.finrank (RatFunc k) F = n := by
    apply fermatProjection_finrank (k := k) hn hgenRat
    rw [hX]
    exact hxy
  let ψ := IsScalarTower.toAlgHom k k[X] (RatFunc k)
  let η := IsScalarTower.toAlgHom k A F
  have heval : φ.comp ψ = η.comp (Polynomial.aeval x₀) := by
    apply Polynomial.algHom_ext
    change φ (algebraMap k[X] (RatFunc k) X) = η ((Polynomial.aeval x₀) X)
    rw [RatFunc.algebraMap_X, Polynomial.aeval_X]
    exact hX
  have hComm : (algebraMap (RatFunc k) F).comp (algebraMap k[X] (RatFunc k)) =
      (algebraMap A F).comp (Polynomial.aeval (R := k) x₀).toRingHom :=
    congrArg AlgHom.toRingHom heval
  have hChart : Spec.map (CommRingCat.ofHom (algebraMap A F)) ≫ i ≫ fermatProjection k hn =
      Spec.map (CommRingCat.ofHom ((algebraMap (RatFunc k) F).comp
        (algebraMap k[X] (RatFunc k)))) ≫ j := by
    rw [show i ≫ fermatProjection k hn = fermatProjectionOnLastChart k n from
      fermatAffineChart_comp_fermatProjection k hn, fermatProjectionOnLastChart_def,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap A F).comp
      (Polynomial.aeval (R := k) x₀).toRingHom)) ≫ j = _
    rw [hComm]
  obtain ⟨hdom, hfin⟩ := AlgebraicGeometry.exists_isDominant_finrank_eq_of_affineCharts
    i j F (RatFunc k) (fermatProjection k hn) hChart
  exact ⟨hdom, hfin.trans hdegree⟩

instance fermatProjection_isDominant (hn : 0 < n) : IsDominant (fermatProjection k hn) :=
  (fermatProjection_degree k hn).choose

/-- The function-field degree of the actual projective Fermat projection is `n`. -/
theorem fermatProjection_functionField_finrank (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    let : Algebra (projectiveLine k).functionField (fermatProjective k n).functionField :=
      (fermatProjection k hn).functionFieldMap.hom.toAlgebra
    Module.finrank (projectiveLine k).functionField (fermatProjective k n).functionField = n :=
  (fermatProjection_degree k hn).choose_spec


/-- The projection of the Fermat curve is finite. -/
instance fermatProjection_isFinite (hn : 0 < n) : IsFinite (fermatProjection k hn) := by
  let := fermatProjective_isCurveOver k hn
  let := projectiveLine_isCurveOver k
  exact isFinite_of_dominant_properCurveHom (k := k) _

/-- The projection of the Fermat curve is surjective. -/
instance fermatProjection_surjective (hn : 0 < n) : Surjective (fermatProjection k hn) := by
  let := fermatProjective_isCurveOver k hn
  let := projectiveLine_isCurveOver k
  exact surjective_of_dominant_properCurveHom (k := k) _

end TinyTauDemo
