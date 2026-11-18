/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.CurveCanonicalDegree
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.FieldTheory.FunctionField.Differential.Comparison
import TauCeti.FieldTheory.FunctionField.Place.Equiv
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Canonical differentials of the projective line

The standard charts give the projective line smooth relative dimension one.
The rational differential of the affine coordinate identifies the relative
Kähler sheaf with the divisor sheaf of minus twice the point at infinity.
The canonical degree is minus two and the genus is zero.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `f0a3b3dec25a0c6b0b6f61e1f6b1a5be8ffec3f1`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry
open scoped IntermediateField

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k]

local notation "P₁" => projectiveLine k
local notation "F₁" => Scheme.functionField (projectiveLine k)
local notation "S₀" => Spec (CommRingCat.of k)

private theorem projectiveLine_dim : topologicalKrullDim P₁ = 1 := by
  rw [topologicalKrullDim_eq_toNat_trdeg_functionField k,
    (projectiveLine.functionFieldEquiv k).trdeg_eq,
    (IsFunctionField.ratFunc k).trdeg_eq_one]
  simp

/-- The projective line over a field is an integral proper curve. -/
theorem projectiveLine_isCurveOver : (P₁).IsCurveOver k where
  topologicalKrullDim_eq_one := projectiveLine_dim k

private theorem projectiveLine_smooth : Smooth (P₁ ↘ S₀) := by
  let 𝒰 : (P₁).OpenCover := Scheme.Cover.mkOfCovers (Fin 2) (fun _ ↦ Spec (.of _))
    (projectiveLine.awayι k) (projectiveLine.exists_eq_awayι k) (fun _ ↦ inferInstance)
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ RingHom.Smooth inferInstance
  apply hloc.of_openCover 𝒰
  change ∀ i : Fin 2, Smooth (projectiveLine.awayι k i ≫ (P₁ ↘ S₀))
  intro i
  rw [projectiveLine.awayι_over, HasRingHomProperty.Spec_iff (P := @Smooth),
    CommRingCat.hom_ofHom, RingHom.smooth_algebraMap]
  let : Algebra.Smooth k (Polynomial k) := {}
  exact Algebra.Smooth.of_equiv (projectiveLine.awayEquivPolynomial k i).symm

/-- The projective line is smooth of relative dimension one. -/
theorem projectiveLine_smoothOfRelativeDimension : SmoothOfRelativeDimension 1 (P₁ ↘ S₀) := by
  have := projectiveLine_smooth k
  exact smoothOfRelativeDimension_of_topologicalKrullDim_eq _ (projectiveLine_dim k)

private theorem projectiveLine_isIntegrallyClosedIn : IsIntegrallyClosedIn k F₁ :=
  (projectiveLine.functionFieldEquiv k).isIntegrallyClosedIn.mpr isIntegrallyClosedIn_ratFunc

set_option backward.isDefEq.respectTransparency false in
/-- The projective line over a field has genus zero. -/
theorem projectiveLine_genus :
    let _ := projectiveLine_isCurveOver k
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := P₁) k)
    (P₁).genus k = 0 := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := P₁) k)
  let e := projectiveLine.functionFieldEquiv k
  have h := genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv (fun c ↦ e.commutes c)
  have : (P₁).IsSeparated := by
    constructor
    rw [← terminal.comp_from (P₁ ↘ S₀)]
    infer_instance
  have : IsNoetherian P₁ :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (P₁ ↘ S₀)
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (P₁ ↘ S₀) }
  have hE : ValuativeCriterion.Existence (P₁ ↘ S₀) := by
    have hU : UniversallyClosed (P₁ ↘ S₀) := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hU
    exact hU.1
  have hg := SchemeWeilDivisor.genus_eq_genus_functionField hE
    (fun x ↦ by exact_mod_cast (coheight_le_topologicalKrullDim x).trans (projectiveLine_dim k).le)
    (Scheme.IsCurveOver.isFunctionField (X := P₁) (k := k))
    (projectiveLine_isIntegrallyClosedIn k)
  exact hg.trans (h.symm.trans (genus_ratFunc k))

/-- The canonical differential line bundle on the projective line has degree minus two. -/
theorem projectiveLine_eulerDegree_relativeDifferentials [PerfectField k] :
    let _ := projectiveLine_smoothOfRelativeDimension k
    (InvertibleSheaf.relativeDifferentials k P₁).eulerDegree k = -2 := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  have h := eulerDegree_relativeDifferentials_of_smoothProperCurve k P₁
    (projectiveLine_isIntegrallyClosedIn k)
  dsimp only at h
  rw [projectiveLine_genus k] at h
  simpa using h

/-- The rational function `X₁/X₀` on the standard affine chart of the projective line. -/
noncomputable def projectiveLineCoordinate : F₁ :=
  (projectiveLine.functionFieldEquiv k).symm RatFunc.X

private theorem projectiveLineCoordinate_transcendental :
    Transcendental k (projectiveLineCoordinate k) := by
  intro ht
  exact RatFunc.transcendental_X (by
    simpa [projectiveLineCoordinate] using ht.algHom (projectiveLine.functionFieldEquiv k).toAlgHom)

/-- The isomorphism to the rational function field identifies the places of the two fields. -/
noncomputable def projectiveLinePlaceEquiv : Place k F₁ ≃ Place k (RatFunc k) :=
  Place.equivOfRingEquiv (RingEquiv.refl k) (projectiveLine.functionFieldEquiv k).toRingEquiv
    (fun c ↦ (projectiveLine.functionFieldEquiv k).commutes c)

/-- The codimension-one point associated to the place at infinity. -/
noncomputable def projectiveLineInfinity : CodimensionOnePoint P₁ := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  exact (curveCodimensionOnePointEquivPlace k P₁).symm
    ((projectiveLinePlaceEquiv k).symm (Place.infty k))

set_option backward.isDefEq.respectTransparency false in
private theorem projectiveLine_order_coordinate (Q : Place k F₁) :
    Q.ord (projectiveLineCoordinate k) = (projectiveLinePlaceEquiv k Q).ord RatFunc.X := by
  exact (Place.ord_equivOfRingEquiv (RingEquiv.refl k)
    (projectiveLine.functionFieldEquiv k).toRingEquiv
    (fun c ↦ (projectiveLine.functionFieldEquiv k).commutes c) Q RatFunc.X).symm

private theorem projectiveLine_toPlace_infinity :
    let _ := projectiveLine_isCurveOver k
    let _ := projectiveLine_smoothOfRelativeDimension k
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
    (P₁).toPlace (k := k) (projectiveLineInfinity k : P₁) =
      (projectiveLinePlaceEquiv k).symm (Place.infty k) := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  dsimp only
  rw [← curveCodimensionOnePointEquivPlace_apply k P₁, projectiveLineInfinity,
    Equiv.apply_symm_apply]

/-- The reciprocal affine coordinate has order one at infinity. -/
theorem projectiveLine_order_inv_coordinate_at_infinity :
    let _ := projectiveLine_isCurveOver k
    let _ := projectiveLine_smoothOfRelativeDimension k
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
    ((P₁).toPlace (k := k) (projectiveLineInfinity k : P₁)).ord
      (projectiveLineCoordinate k)⁻¹ = 1 := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  dsimp only
  rw [Place.ord_inv, projectiveLine_order_coordinate, projectiveLine_toPlace_infinity,
    Equiv.apply_symm_apply, Place.ord_infty, RatFunc.intDegree_X]
  decide

/-- The reciprocal affine coordinate is a uniformizer at the point at infinity. -/
theorem projectiveLine_inv_coordinate_isUniformizer :
    let _ := projectiveLine_isCurveOver k
    let _ := projectiveLine_smoothOfRelativeDimension k
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
    ((P₁).toPlace (k := k) (projectiveLineInfinity k : P₁)).valuation.IsUniformizer
      (projectiveLineCoordinate k)⁻¹ := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  exact (((P₁).toPlace (k := k) (projectiveLineInfinity k : P₁)).isUniformizer_iff_ord_eq_one).mpr
    (projectiveLine_order_inv_coordinate_at_infinity k)

/-- In the reciprocal coordinate `s = t⁻¹`, the rational differential `dt` is `-s⁻² ds`. -/
theorem projectiveLine_differential_coordinate :
    let s := (projectiveLineCoordinate k)⁻¹
    KaehlerDifferential.D k F₁ (projectiveLineCoordinate k) =
      -((s ^ 2)⁻¹) • KaehlerDifferential.D k F₁ s := by
  let t := projectiveLineCoordinate k
  let s := t⁻¹
  let δ := KaehlerDifferential.D k F₁
  change δ t = -((s ^ 2)⁻¹) • δ s
  have ht : t ≠ 0 := (projectiveLineCoordinate_transcendental k).ne_zero
  have h := δ.leibniz s t
  rw [show s * t = 1 from inv_mul_cancel₀ ht, Derivation.map_one_eq_zero] at h
  have h' : s • δ t = -(t • δ s) := eq_neg_of_add_eq_zero_left h.symm
  calc
    δ t = s⁻¹ • (s • δ t) := (inv_smul_smul₀ (inv_ne_zero ht) _).symm
    _ = -((s ^ 2)⁻¹) • δ s := by simp [h', s, smul_smul, pow_two]

/-- The point at infinity lies outside the chart `D₊(X₀)`. -/
theorem projectiveLineInfinity_not_mem_affineChart :
    (projectiveLineInfinity k : P₁) ∉ (projectiveLine.awayι k 0 ''ᵁ ⊤) := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  let x : P₁ := projectiveLineInfinity k
  intro hx
  have hx' : projectiveLineCoordinate k ∈ ((P₁).toPlace (k := k) x).integers := by
    rw [projectiveLineCoordinate, projectiveLine.functionFieldEquiv_symm_X,
      ← (P₁).algebraMap_germ_eq_germToFunctionField hx]
    exact (P₁).algebraMap_stalk_mem_toPlace_integers x _
  have hord := (((P₁).toPlace (k := k) x).mem_integers_iff_ord_nonneg).mp hx'
  dsimp only [x] at hord
  rw [projectiveLine_order_coordinate, projectiveLine_toPlace_infinity,
    Equiv.apply_symm_apply, Place.ord_infty,
    RatFunc.intDegree_X] at hord
  omega

variable [CharZero k]

private theorem projectiveLine_order_weilDifferential
    (hF : IsFunctionField k F₁) (hk : IsIntegrallyClosedIn k F₁) (Q : Place k F₁) :
    let ht := projectiveLineCoordinate_transcendental k
    let _ := hF.finiteDimensional_adjoin ht
    weilDifferentialOrder hF hk (weilDifferentialOfSeparating hF ht).2
      (coe_weilDifferentialOfSeparating_ne_zero hF ht) Q =
    (-2 : ℤ) * (WeilDivisor.ofPoint (Place.infty k)).coeff (projectiveLinePlaceEquiv k Q) := by
  let ht := projectiveLineCoordinate_transcendental k
  let _ := hF.finiteDimensional_adjoin ht
  let _ := ratFuncAlgebraOfTranscendental ht
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental ht
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental ht
  let e := projectiveLine.functionFieldEquiv k
  have hmap : IsScalarTower.toAlgHom k (RatFunc k) F₁ = e.symm.toAlgHom := by
    apply RatFunc.algHom_ext
    exact algebraMap_ratFuncAlgebraOfTranscendental_X ht
  have hfin : Module.finrank (RatFunc k) F₁ = 1 := by
    apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    change Function.Bijective (IsScalarTower.toAlgHom k (RatFunc k) F₁)
    rw [hmap]
    exact e.symm.bijective
  have he : Place.ramificationIdx (RatFunc k) Q = 1 := by
    have hle := Place.ramificationIdx_le_finrank (RatFunc k) Q
    have hpos := Place.ramificationIdx_pos (RatFunc k) Q
    omega
  have hd := (Divisor.coeff_different_add_one_eq_ramificationIdx_iff
    (IsFunctionField.ratFunc k) Q).mpr (Place.isTame_of_charZero k (RatFunc k) Q)
  rw [he, Nat.cast_one, add_eq_right] at hd
  dsimp only
  rw [← coeff_weilDifferentialDivisor, weilDifferentialDivisor_weilDifferentialOfSeparating,
    WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul, hd, add_zero, Divisor.coeff_poles,
    Units.val_mk0, projectiveLine_order_coordinate]
  rw [← Divisor.poles_X, Divisor.coeff_poles, Units.val_mk0]

set_option backward.isDefEq.respectTransparency false in
/-- The rational differential of `X₁/X₀` identifies the canonical sheaf with the sheaf of the
Weil divisor that has coefficient minus two at infinity and zero elsewhere. -/
noncomputable def projectiveLine_relativeDifferentialsIsoInfinity :
    (P₁).relativeDifferentials k ≅
      SchemeWeilDivisor.sheaf ((-2 : ℤ) • WeilDivisor.ofPoint (projectiveLineInfinity k)) := by
  let := projectiveLine_isCurveOver k
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := P₁)
  have := LocallyOfFiniteType.isLocallyNoetherian (P₁ ↘ Spec (.of k))
  have := isInvertible_relativeDifferentials (X := P₁) k
  let ht := projectiveLineCoordinate_transcendental k
  let hF := Scheme.IsCurveOver.isFunctionField (k := k) (X := P₁)
  let _ := hF.finiteDimensional_adjoin ht
  let hk := projectiveLine_isIntegrallyClosedIn k
  let K : SchemeWeilDivisor P₁ := (-2 : ℤ) • WeilDivisor.ofPoint (projectiveLineInfinity k)
  refine relativeDifferentialsIsoDivisorSheaf ht hF hk (fun x ↦ ?_) K (fun y ↦ ?_)
  · exact_mod_cast (coheight_le_topologicalKrullDim x).trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  · dsimp only [K]
    rw [WeilDivisor.coeff_zsmul, projectiveLine_order_weilDifferential]
    congr 1
    have h (z : CodimensionOnePoint P₁) :
        (projectiveLinePlaceEquiv k ((P₁).toPlace (k := k) (z : P₁)) = Place.infty k) ↔
          z = projectiveLineInfinity k := by
      rw [← Equiv.eq_symm_apply, ← projectiveLine_toPlace_infinity,
        ← curveCodimensionOnePointEquivPlace_apply k P₁,
        ← curveCodimensionOnePointEquivPlace_apply k P₁, Equiv.apply_eq_iff_eq]
    by_cases hy : y = projectiveLineInfinity k
    · rw [hy, WeilDivisor.coeff_ofPoint_self, (h _).mpr rfl, WeilDivisor.coeff_ofPoint_self]
    · rw [WeilDivisor.coeff_ofPoint_of_ne hy, WeilDivisor.coeff_ofPoint_of_ne (mt (h _).mp hy)]

end TinyTauDemo
