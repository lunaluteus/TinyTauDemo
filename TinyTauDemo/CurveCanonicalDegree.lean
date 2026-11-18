/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.CartierRamification
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import TauCeti.AlgebraicGeometry.CartierDivisor.WeilComparison

/-!
# Canonical degrees and Riemann–Hurwitz for smooth proper curves

The relative differential line bundle has degree `2g - 2` over a perfect exact
constant field. The canonical-sheaf twist adds the degree of the effective
ramification divisor, and the degree of the pullback of the target canonical
line bundle scales by the extension degree in characteristic zero. Over
algebraically closed constants the correction term is the sum of the
local ramification indices minus one.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `9b9ee87967b2eead614c7f821927fa415c834846`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Order TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

section CurveHypotheses

variable (k : Type u) [hField : Field k] (X : Scheme.{u})
    [hOver : X.Over (Spec (.of k))] [hCurve : X.IsCurveOver k]

include hCurve

private theorem curve_coheight_le_one (x : X) : coheight x ≤ 1 := by
  exact_mod_cast (coheight_le_topologicalKrullDim x).trans
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le

private theorem curve_isSeparated : X.IsSeparated := by
  constructor
  rw [← terminal.comp_from (X ↘ Spec (.of k))]
  infer_instance

private theorem curve_valuativeExistence : ValuativeCriterion.Existence (X ↘ Spec (.of k)) := by
  have h : UniversallyClosed (X ↘ Spec (.of k)) := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

private theorem curve_locallyNoetherian : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))

private theorem curve_noetherian : IsNoetherian X where
  toIsLocallyNoetherian := curve_locallyNoetherian k X
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

set_option backward.isDefEq.respectTransparency false in
/-- On a smooth proper integral curve over a perfect exact constant field, the
Euler-characteristic degree of the relative differential line bundle is 2g - 2. -/
theorem eulerDegree_relativeDifferentials_of_smoothProperCurve [PerfectField k]
    (hk : IsIntegrallyClosedIn k X.functionField) :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
    (InvertibleSheaf.relativeDifferentials k X).eulerDegree k = 2 * (X.genus k : ℤ) - 2 := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
  have := curve_isSeparated k X
  have := curve_noetherian k X
  have hInv := isInvertible_relativeDifferentials (X := X) k
  let L : InvertibleSheaf X := ⟨X.relativeDifferentials k, hInv⟩
  have e : (InvertibleSheaf.relativeDifferentials k X).obj ≅ L.obj :=
    eqToIso (InvertibleSheaf.relativeDifferentials_obj k X)
  exact (InvertibleSheaf.eulerDegree_congr k e).trans
    (eulerDegree_relativeDifferentials (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
      hk (curve_coheight_le_one k X) (curve_valuativeExistence k X))

set_option backward.isDefEq.respectTransparency false in
/-- On a smooth proper integral curve over a perfect exact constant field, the
space of global relative differentials is finite dimensional and has dimension the genus. -/
theorem finrank_globalRelativeDifferentials_of_smoothProperCurve [PerfectField k]
    (hk : IsIntegrallyClosedIn k X.functionField) :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
    FiniteDimensional k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 0) ∧
      Module.finrank k (Scheme.Modules.Cohomology (X.relativeDifferentials k) 0) = X.genus k := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
  have := curve_isSeparated k X
  have := curve_noetherian k X
  have hInv := isInvertible_relativeDifferentials (X := X) k
  let L : InvertibleSheaf X := ⟨X.relativeDifferentials k, hInv⟩
  exact ⟨InvertibleSheaf.finiteDimensional_cohomology_zero k (curve_coheight_le_one k X) L,
    finrank_cohomology_zero_relativeDifferentials
      (Scheme.IsCurveOver.isFunctionField (X := X) (k := k)) hk
        (curve_coheight_le_one k X) (curve_valuativeExistence k X)⟩

end CurveHypotheses

section RamificationDegree

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]

set_option backward.isDefEq.respectTransparency false in
/-- Taking Euler-characteristic degrees of the canonical-sheaf twist adds the
residue-weighted degree of the ramification divisor to the degree of the pullback. -/
theorem eulerDegree_relativeDifferentials_eq_pullback_add_ramification :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    (InvertibleSheaf.relativeDifferentials k X).eulerDegree k =
      ((InvertibleSheaf.pullback f).obj (InvertibleSheaf.relativeDifferentials k Y)).eulerDegree k +
        SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) (curveRamificationDivisor k f) := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  have := curve_noetherian k X
  have := curve_locallyNoetherian k X
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
  let hdim := curve_coheight_le_one k X
  let M := InvertibleSheaf.relativeDifferentials k X
  let L := (InvertibleSheaf.pullback f).obj (InvertibleSheaf.relativeDifferentials k Y)
  obtain ⟨D, -, ⟨e⟩, hD⟩ := exists_effectiveCartierRamificationDivisor_with_WeilDivisor (k := k) f
  let W := D.toInvertibleSheaf
  let eM : M.obj ≅ X.relativeDifferentials k :=
    eqToIso (InvertibleSheaf.relativeDifferentials_obj k X)
  let eL : (Scheme.Modules.pullback f).obj (Y.relativeDifferentials k) ≅ L.obj :=
    eqToIso (by
      dsimp only [L]
      rw [InvertibleSheaf.pullback_obj_obj, InvertibleSheaf.relativeDifferentials_obj])
  let eW : D.sheaf ≅ W.obj :=
    eqToIso (Scheme.CartierDivisor.toInvertibleSheaf_obj D).symm
  let eT : M.obj ≅ (L.tensorProduct W).obj :=
    eM ≪≫ e ≪≫ (eL ⊗ᵢ eW) ≪≫ (InvertibleSheaf.tensorProductObjIso L W).symm
  have hsum : (L.tensorProduct W).eulerDegree k = L.eulerDegree k + W.eulerDegree k := by
    simpa only [← LineBundleClass.mk_tensorProduct, LineBundleClass.eulerDegree_mk] using
      LineBundleClass.eulerDegree_mul k hdim (LineBundleClass.mk L) (LineBundleClass.mk W)
  have hdeg : W.eulerDegree k =
      SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) (curveRamificationDivisor k f) := by
    rw [← hD]
    exact InvertibleSheaf.eulerDegree_eq_relativeDegree k hdim
      (eW.symm ≪≫ D.sheafIsoToWeilDivisor hdim)
  exact (InvertibleSheaf.eulerDegree_congr k eT).trans (hsum.trans (congrArg _ hdeg))

local notation "F" => Y.functionField
local notation "L" => X.functionField

set_option backward.isDefEq.respectTransparency false in
/-- The numerical Riemann--Hurwitz formula with the residue-weighted degree of
the actual ramification divisor. The base is the exact constant field of both curves. -/
theorem hurwitz_genus_formula_of_smoothProperCurves
    (hkX : IsIntegrallyClosedIn k L) (hkY : IsIntegrallyClosedIn k F) :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := Y)
    let _ : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k)
    2 * (X.genus k : ℤ) - 2 =
      Module.finrank F L * (2 * (Y.genus k : ℤ) - 2) +
        SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) (curveRamificationDivisor k f) := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := Y)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k)
  have := curve_noetherian k X
  have := curve_noetherian k Y
  have := curve_isSeparated k X
  have := curve_isSeparated k Y
  let : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let hF := Scheme.IsCurveOver.isFunctionField (X := Y) (k := k)
  let hL := Scheme.IsCurveOver.isFunctionField (X := X) (k := k)
  let : FiniteDimensional F L := finiteDimensional_of_functionFields hF hL
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  let e := SchemeWeilDivisor.equivFunctionFieldDivisor (curve_valuativeExistence k X)
    (curve_coheight_le_one k X)
  let D := Divisor.tameDifferent k L hF
  have he : curveCodimensionOnePointEquivPlace k X =
      CodimensionOnePoint.equivPlace (curve_valuativeExistence k X)
        (curve_coheight_le_one k X) := by
    ext x
    rw [curveCodimensionOnePointEquivPlace_apply, CodimensionOnePoint.equivPlace_apply]
  have hD : curveRamificationDivisor k f = e.symm D := by
    dsimp only [e, D]
    rw [curveRamificationDivisor_eq_reindex_tameDifferent,
      SchemeWeilDivisor.equivFunctionFieldDivisor_eq_domCongr, Finsupp.domCongr_symm, he]
  have hdeg : SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) (curveRamificationDivisor k f) =
      Divisor.degree D :=
    (congrArg (SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k))) hD).trans
      (SchemeWeilDivisor.relativeDegree_equivFunctionFieldDivisor_symm _ _ D)
  have hGX : X.genus k = genus k L :=
    SchemeWeilDivisor.genus_eq_genus_functionField (curve_valuativeExistence k X)
      (curve_coheight_le_one k X) hL hkX
  have hGY : Y.genus k = genus k F :=
    SchemeWeilDivisor.genus_eq_genus_functionField (curve_valuativeExistence k Y)
      (curve_coheight_le_one k Y) hF hkY
  have h :=
    (two_mul_genus_sub_two_eq_iff_forall_isTame hF hL hkY hkX).2
      fun P ↦ Place.isTame_of_charZero k F P
  rw [geometricDegree_eq_finrank F k L] at h
  dsimp only
  rw [hGX, hGY, hdeg]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The degree of the actual pullback of the target canonical line bundle scales
by the degree of the function-field extension. -/
theorem eulerDegree_pullback_relativeDifferentials
    (hkX : IsIntegrallyClosedIn k L) (hkY : IsIntegrallyClosedIn k F) :
    let _ : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    ((InvertibleSheaf.pullback f).obj (InvertibleSheaf.relativeDifferentials k Y)).eulerDegree k =
      Module.finrank F L * (InvertibleSheaf.relativeDifferentials k Y).eulerDegree k := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := Y)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k)
  let : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  have h := eulerDegree_relativeDifferentials_eq_pullback_add_ramification (k := k) f
  have hh := hurwitz_genus_formula_of_smoothProperCurves (k := k) f hkX hkY
  dsimp only at h hh ⊢
  rw [← eulerDegree_relativeDifferentials_of_smoothProperCurve k X hkX,
    ← eulerDegree_relativeDifferentials_of_smoothProperCurve k Y hkY] at hh
  exact add_right_cancel (h.symm.trans hh)

end RamificationDegree

section LocalIndexSum

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [X.IsCurveOver k] [Y.IsCurveOver k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]

/-- The support of the ramification divisor consists exactly of the points with local
ramification index strictly larger than one. -/
theorem mem_support_curveRamificationDivisor_iff (z : CodimensionOnePoint X) :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    let _ := algebraStalkMap f z
    z ∈ (curveRamificationDivisor k f).support ↔
      1 < (IsLocalRing.maximalIdeal (X.presheaf.stalk (z : X))).ramificationIdx
        (Y.presheaf.stalk (f z)) := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  let := algebraStalkMap f z
  dsimp only
  rw [WeilDivisor.mem_support_iff, coeff_curveRamificationDivisor_eq_localIndex]
  omega

variable [IsAlgClosed k]

/-- Over an algebraically closed field, the degree of the actual ramification divisor is
the sum of the local ramification indices minus one. -/
theorem relativeDegree_curveRamificationDivisor_eq_localIndex_sum :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    SchemeWeilDivisor.relativeDegree (X ↘ Spec (.of k)) (curveRamificationDivisor k f) =
      ∑ z ∈ (curveRamificationDivisor k f).support,
        let _ := algebraStalkMap f z
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk (z : X))).ramificationIdx
          (Y.presheaf.stalk (f z)) : ℤ) - 1 := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  dsimp only
  rw [SchemeWeilDivisor.relativeDegree_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  let := algebraStalkMap f z
  have hdeg : (X ↘ Spec (.of k)).residueDegree (z : X) = 1 :=
    (X.toPlace_degree_eq_residueDegree (k := k) (z : X)).symm.trans
      ((X.toPlace (k := k) (z : X)).degree_eq_one_of_isAlgClosed_of_isFunctionField
        (Scheme.IsCurveOver.isFunctionField (X := X) (k := k)))
  change (curveRamificationDivisor k f).coeff z * _ = _
  rw [hdeg, Nat.cast_one, mul_one, coeff_curveRamificationDivisor_eq_localIndex]
  have hpos := (mem_support_curveRamificationDivisor_iff (k := k) f z).mp hz
  omega

/-- Riemann–Hurwitz on smooth proper curves, with the correction term the explicit sum of
local ramification indices minus one over the support of the ramification divisor. -/
theorem hurwitz_genus_formula_of_smoothProperCurves_localIndex_sum :
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := Y)
    let _ : Algebra Y.functionField X.functionField := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
    let _ := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k)
    2 * (X.genus k : ℤ) - 2 =
      Module.finrank Y.functionField X.functionField * (2 * (Y.genus k : ℤ) - 2) +
        ∑ z ∈ (curveRamificationDivisor k f).support,
          let _ := algebraStalkMap f z
          ((IsLocalRing.maximalIdeal (X.presheaf.stalk (z : X))).ramificationIdx
            (Y.presheaf.stalk (f z)) : ℤ) - 1 := by
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := Y)
  let : Algebra Y.functionField X.functionField := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := X) k)
  let := finiteDimensional_cohomology_one_trivial_of_isProper k
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k)
  have h := hurwitz_genus_formula_of_smoothProperCurves (k := k) f
    isIntegrallyClosedIn_of_isAlgClosed isIntegrallyClosedIn_of_isAlgClosed
  dsimp only at h ⊢
  rw [relativeDegree_curveRamificationDivisor_eq_localIndex_sum] at h
  exact h

end LocalIndexSum

end TinyTauDemo
