/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.DifferentialRamificationOrder
public import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.SchemeRamificationDivisor
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
import TauCeti.AlgebraicGeometry.CartierDivisor.WeilComparison
import TauCeti.AlgebraicGeometry.Modules.RationalEmbedding
import TauCeti.AlgebraicGeometry.LineBundle.Pullback
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The effective Cartier ramification divisor

A monomorphism of line bundles on an integral scheme determines an effective
Cartier divisor through its local multipliers. The target bundle is the tensor
product of the source with the divisor sheaf. For pullback of differentials on
smooth proper curves in characteristic zero, the multiplicities of this divisor
are the local ramification indices minus one.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `f59d0ca264bd30e7f0d1b6748710096b3da07d71`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

noncomputable section

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem app_injective_of_mono {L M : X.Modules} (φ : L ⟶ M) [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  exact (ModuleCat.mono_iff_injective (F.map φ)).mp inferInstance

/-- The regular coefficient of a map in two local bases on a common open subset. -/
def lineMapCoefficient {L M : X.Modules} (φ : L ⟶ M)
    {U V W : X.Opens}
    (tL : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.over U)
    (tM : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    (i : W ⟶ U) (j : W ⟶ V) : Γ(X, W) :=
  M.trivializationCoordinate tM j (φ.app W (L.presheaf.map i.op (L.trivializationGenerator tL)))

set_option backward.isDefEq.respectTransparency false in
private theorem app_map {L M : X.Modules} (φ : L ⟶ M)
    {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) :
    φ.app V (L.presheaf.map i.op s) = M.presheaf.map i.op (φ.app U s) :=
  PresheafOfModules.naturality_apply φ.val i.op s

section RationalScalar

variable [IsIntegral X] {L M : X.Modules} (φ : L ⟶ M)
    {UL UM : X.Opens}
    (eL : SheafOfModules.free (R := X.ringCatSheaf.over UL) PUnit ≅ L.over UL)
    (eM : SheafOfModules.free (R := X.ringCatSheaf.over UM) PUnit ≅ M.over UM)
    (hL : Dense (UL : Set X)) (hM : Dense (UM : Set X)) [Nonempty UL]

private def rationalLineMapScalar : X.functionField :=
  M.rationalFunction eM hM UL (φ.app UL (L.trivializationGenerator eL)) /
    L.rationalFunction eL hL UL (L.trivializationGenerator eL)

set_option backward.isDefEq.respectTransparency false in
private theorem rationalFunction_app_eq_mul {W : X.Opens} [Nonempty W] (s : Γ(L, W)) :
    M.rationalFunction eM hM W (φ.app W s) =
      rationalLineMapScalar φ eL eM hL hM * L.rationalFunction eL hL W s := by
  let Z := W ⊓ UL
  let i : Z ⟶ W := homOfLE inf_le_left
  let j : Z ⟶ UL := homOfLE inf_le_right
  have : Nonempty Z := Opens.nonempty_coeSort.mpr
    (hL.inter_open_nonempty W W.isOpen (Opens.nonempty_coeSort.mp ‹Nonempty W›))
  let sZ : Γ(L, Z) := L.presheaf.map i.op s
  let r := L.trivializationCoordinate eL j sZ
  let sL := L.trivializationGenerator eL
  have hsZ : sZ = r • L.presheaf.map j.op sL :=
    L.eq_trivializationCoordinate_smul_map_trivializationGenerator eL j sZ
  have hLs : L.rationalFunction eL hL W s =
      X.germToFunctionField Z r * L.rationalFunction eL hL UL sL := by
    rw [← L.rationalFunction_map eL hL i s]
    change L.rationalFunction eL hL Z sZ = _
    rw [hsZ, L.rationalFunction_smul, L.rationalFunction_map]
  have hMs : M.rationalFunction eM hM W (φ.app W s) =
      X.germToFunctionField Z r * M.rationalFunction eM hM UL (φ.app UL sL) := by
    rw [← M.rationalFunction_map eM hM i (φ.app W s), ← app_map]
    change M.rationalFunction eM hM Z (φ.app Z sZ) = _
    rw [hsZ, Scheme.Modules.Hom.app_smul, M.rationalFunction_smul, app_map,
      M.rationalFunction_map]
  rw [hLs, hMs]
  have hne : L.rationalFunction eL hL UL sL ≠ 0 :=
    (L.isUnit_rationalFunction_trivializationGenerator eL hL eL).ne_zero
  change _ = (M.rationalFunction eM hM UL (φ.app UL sL) /
    L.rationalFunction eL hL UL sL) *
      (X.germToFunctionField Z r * L.rationalFunction eL hL UL sL)
  rw [mul_left_comm, div_mul_cancel₀ _ hne]

variable [SheafOfModules.isInvertible X M] [Mono φ]

set_option backward.isDefEq.respectTransparency false in
private theorem rationalLineMapScalar_ne_zero : rationalLineMapScalar φ eL eM hL hM ≠ 0 := by
  apply div_ne_zero
  · intro hz₀
    have hz := (M.rationalFunction_eq_zero_iff eM hM UL _).mp hz₀
    apply L.trivializationGenerator_ne_zero eL
    apply app_injective_of_mono φ UL
    exact hz.trans ((φ.app UL).hom.map_zero).symm
  · exact (L.isUnit_rationalFunction_trivializationGenerator eL hL eL).ne_zero

end RationalScalar

set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism of invertible sheaves on an integral scheme defines an effective
Cartier divisor with the local coefficients of the map as equations. The target
line bundle is the tensor product of the source line bundle and the divisor sheaf. -/
theorem exists_effectiveCartierDivisor_twist_of_lineMap {X : Scheme.{u}} [IsIntegral X]
    (L M : InvertibleSheaf X) (φ : L.obj ⟶ M.obj) [Mono φ] :
    ∃ D : Scheme.CartierDivisor X, D.IsEffective ∧
      Nonempty (M.obj ≅ (L.tensorProduct D.toInvertibleSheaf).obj) ∧
      ∀ {U V W : X.Opens} [Nonempty W]
        (tL : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
        (tM : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.obj.over V)
        (i : W ⟶ U) (j : W ⟶ V) {x : X} (_ : x ∈ W),
        ∃ q : X.functionFieldˣ, D.IsLocalEquationAt x q ∧
          (q : X.functionField) = X.germToFunctionField W (lineMapCoefficient φ tL tM i j) := by
  obtain ⟨UL, hUL, hL, ⟨eL⟩⟩ := TauCeti.SheafOfModules.exists_dense_open_trivialization L.obj
  obtain ⟨UM, -, hM, ⟨eM⟩⟩ := TauCeti.SheafOfModules.exists_dense_open_trivialization M.obj
  let _ : Nonempty UL := ⟨⟨genericPoint X, hUL⟩⟩
  obtain ⟨DL, hDL⟩ := L.obj.exists_cartierDivisor_restrict_eq eL hL
  obtain ⟨DM, hDM⟩ := M.obj.exists_cartierDivisor_restrict_eq eM hM
  let r := Units.mk0 (rationalLineMapScalar φ eL eM hL hM)
    (rationalLineMapScalar_ne_zero φ eL eM hL hM)
  let D := DM + -DL + Scheme.principalCartierDivisor X r
  have heq {U V W : X.Opens} [Nonempty W]
      (tL : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.obj.over U)
      (tM : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.obj.over V)
      (i : W ⟶ U) (j : W ⟶ V) {x : X} (hx : x ∈ W) :
      ∃ q : X.functionFieldˣ, D.IsLocalEquationAt x q ∧
        (q : X.functionField) = X.germToFunctionField W (lineMapCoefficient φ tL tM i j) := by
    let _ : Nonempty U := ⟨⟨x, i.le hx⟩⟩
    let _ : Nonempty V := ⟨⟨x, j.le hx⟩⟩
    let uL := L.obj.trivializationGeneratorRationalUnit eL hL tL
    let uM := M.obj.trivializationGeneratorRationalUnit eM hM tM
    have hLE : DL.IsLocalEquationAt x uL⁻¹ :=
      Scheme.CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
        (by simpa only [ofMul_inv] using (hDL U tL).symm) (i.le hx)
    have hME : DM.IsLocalEquationAt x uM⁻¹ :=
      Scheme.CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
        (by simpa only [ofMul_inv] using (hDM V tM).symm) (j.le hx)
    have hr := Scheme.CartierDivisor.isLocalEquationAt_principalCartierDivisor x r
    let q := uM⁻¹ * uL * r
    refine ⟨q, ?_, ?_⟩
    · simpa only [D, q, inv_inv] using (hME.mul hLE.inv).mul hr
    · let s := L.obj.presheaf.map i.op (L.obj.trivializationGenerator tL)
      let c := lineMapCoefficient φ tL tM i j
      have hcoord : φ.app W s =
          c • M.obj.presheaf.map j.op (M.obj.trivializationGenerator tM) :=
        M.obj.eq_trivializationCoordinate_smul_map_trivializationGenerator tM j (φ.app W s)
      have h1 : M.obj.rationalFunction eM hM W (φ.app W s) =
          X.germToFunctionField W c * (uM : X.functionField) := by
        rw [hcoord, M.obj.rationalFunction_smul, M.obj.rationalFunction_map,
          M.obj.coe_trivializationGeneratorRationalUnit]
      have h2 : M.obj.rationalFunction eM hM W (φ.app W s) =
          (r : X.functionField) * (uL : X.functionField) := by
        rw [rationalFunction_app_eq_mul φ eL eM hL hM,
          L.obj.coe_trivializationGeneratorRationalUnit, ← L.obj.rationalFunction_map eL hL i]
        rfl
      change ((uM⁻¹ * uL * r : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField W c
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      calc
        _ = (uM : X.functionField)⁻¹ * ((r : X.functionField) * (uL : X.functionField)) := by
          ring
        _ = (uM : X.functionField)⁻¹ * (X.germToFunctionField W c * (uM : X.functionField)) := by
          rw [← h2, h1]
        _ = X.germToFunctionField W c := by
          rw [mul_left_comm, inv_mul_cancel₀ uM.ne_zero, mul_one]
  refine ⟨D, ?_, ?_, @heq⟩
  · apply Scheme.CartierDivisor.isEffective_iff_exists.mpr
    intro x
    obtain ⟨U, tL, hU⟩ := L.obj.exists_mem_trivialization x
    obtain ⟨V, tM, hV⟩ := M.obj.exists_mem_trivialization x
    let W := U ⊓ V
    have hx : x ∈ W := ⟨hU, hV⟩
    let _ : Nonempty W := ⟨⟨x, hx⟩⟩
    let i : W ⟶ U := homOfLE inf_le_left
    let j : W ⟶ V := homOfLE inf_le_right
    obtain ⟨q, hq, hq'⟩ := heq tL tM i j hx
    refine ⟨q, hq, X.presheaf.germ W x hx (lineMapCoefficient φ tL tM i j), ?_⟩
    exact (Scheme.algebraMap_germ_eq_germToFunctionField _ hx
      (lineMapCoefficient φ tL tM i j)).trans hq'.symm
  · apply LineBundleClass.mk_eq_mk_iff.mp
    rw [LineBundleClass.mk_tensorProduct]
    have hCL : DL.toLineBundleClass = LineBundleClass.mk L :=
      Scheme.CartierDivisor.toLineBundleClass_eq_mk_iff.mpr
        ⟨(Scheme.CartierDivisor.isoSheafOfRestrictEq hDL).symm⟩
    have hCM : DM.toLineBundleClass = LineBundleClass.mk M :=
      Scheme.CartierDivisor.toLineBundleClass_eq_mk_iff.mpr
        ⟨(Scheme.CartierDivisor.isoSheafOfRestrictEq hDM).symm⟩
    have hCD : D.toLineBundleClass = LineBundleClass.mk D.toInvertibleSheaf :=
      Scheme.CartierDivisor.toLineBundleClass_eq_mk_iff.mpr
        ⟨eqToIso (Scheme.CartierDivisor.toInvertibleSheaf_obj D).symm⟩
    rw [← hCD, show D = _ from rfl, Scheme.CartierDivisor.toLineBundleClass_add,
      Scheme.CartierDivisor.toLineBundleClass_add,
      Scheme.CartierDivisor.toLineBundleClass_principalCartierDivisor,
      Scheme.CartierDivisor.toLineBundleClass_neg, hCL, hCM, mul_one, mul_left_comm,
      mul_inv_cancel, mul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem lineMapCoefficient_germ_eq_stalk {X : Scheme.{u}} {L M : X.Modules}
    (φ : L ⟶ M) {U V W : X.Opens}
    (tL : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ L.over U)
    (tM : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    (i : W ⟶ U) (j : W ⟶ V) (x : X) (hx : x ∈ W) :
    X.presheaf.germ W x hx (lineMapCoefficient φ tL tM i j) =
      (stalkLinearEquivOfTrivialization M tM x (j.le hx)).symm
        ((modulesStalkFunctor x).map φ (stalkLinearEquivOfTrivialization L tL x (i.le hx) 1)) := by
  apply (stalkLinearEquivOfTrivialization M tM x (j.le hx)).injective
  rw [LinearEquiv.apply_symm_apply, stalkLinearEquivOfTrivialization_apply,
    stalkLinearEquivOfTrivialization_apply, one_smul,
    ← L.presheaf.germ_res_apply i x hx, modulesStalkFunctor_map_germ,
    ← M.presheaf.germ_res_apply j x hx, ← Scheme.Modules.germ_smul]
  have h := M.eq_trivializationCoordinate_smul_map_trivializationGenerator tM j
    (φ.app W (L.presheaf.map i.op (L.trivializationGenerator tL)))
  exact congrArg (M.presheaf.germ W x hx) h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem cartierOrder_eq_of_localEquation_ord {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] (D : Scheme.CartierDivisor X)
    (x : CodimensionOnePoint X) (q : X.functionFieldˣ) (hq : D.IsLocalEquationAt x q)
    (a : X.presheaf.stalk (x : X))
    (ha : (q : X.functionField) = algebraMap (X.presheaf.stalk (x : X)) X.functionField a)
    (n : ℕ) (hn : Ring.ord (X.presheaf.stalk (x : X)) a = ↑n) :
    D.orderAt x = n := by
  obtain ⟨U, hx, hU⟩ := Scheme.CartierDivisor.isLocalEquationAt_iff.mp hq
  let _ : Nonempty U := ⟨⟨x, hx⟩⟩
  rw [D.orderAt_eq_of_restrict_eq_rationalUnitClass x U hx (Additive.ofMul q) hU.symm,
    SchemeWeilDivisor.orderAt_apply, toMul_ofMul]
  apply (X.ord_eq_iff x.property q.ne_zero).mpr
  have ha₀ : a ≠ 0 := fun hz ↦ q.ne_zero (ha.trans (hz ▸ map_zero _))
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (x : X)) :=
    krullDimLE_of_coheight_le x.property.le
  rw [ha, Scheme.ordHom, Ring.ordFrac_eq_ord (X.presheaf.stalk (x : X)) ha₀]
  simp [Ring.ordMonoidWithZeroHom, mem_nonZeroDivisors_iff_ne_zero.mpr ha₀, hn]

section RamificationDivisor

open MonoidalCategory
open scoped TensorProduct

private theorem coheight_le_one_of_curve {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsCurveOver k] (y : X) : Order.coheight y ≤ 1 := by
  exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le

/-- The local ring at a codimension-one point of a smooth integral curve is a DVR. -/
theorem isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [X.IsCurveOver k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    (x : CodimensionOnePoint X) : IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
  isDiscreteValuationRing_stalk_of_closed_smoothCurve (k := k) (x : X)
    (TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one
      (coheight_le_one_of_curve (k := k)) x.property)

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]

set_option backward.isDefEq.respectTransparency false in
/-- The differential pullback of a dominant morphism of smooth proper curves in
characteristic zero defines the effective ramification divisor. The canonical
sheaf is the pullback of the target canonical sheaf twisted by this divisor,
whose Weil coefficient at each closed point is the ramification index minus one. -/
theorem exists_effectiveCartierRamificationDivisor :
    let _ : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let _ : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
    let _ : IsNoetherian X := ⟨⟩
    ∃ D : Scheme.CartierDivisor X, D.IsEffective ∧
      Nonempty (X.relativeDifferentials k ≅
        (Scheme.Modules.pullback f).obj (Y.relativeDifferentials k) ⊗ D.sheaf) ∧
      ∀ x : CodimensionOnePoint X,
        let A := Y.presheaf.stalk (f x)
        let B := X.presheaf.stalk (x : X)
        let _ : Algebra A B := algebraStalkMap f x
        WeilDivisor.coeff D.toWeilDivisor x =
          (((IsLocalRing.maximalIdeal B).ramificationIdx A - 1 : ℕ) : ℤ) := by
  let := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  have := isInvertible_relativeDifferentials (X := Y) k
  have := isInvertible_relativeDifferentials (X := X) k
  let L : InvertibleSheaf X :=
    ⟨(Scheme.Modules.pullback f).obj (Y.relativeDifferentials k),
      SheafOfModules.isInvertible_pullback f (Y.relativeDifferentials k)⟩
  let M : InvertibleSheaf X := ⟨X.relativeDifferentials k, isInvertible_relativeDifferentials k⟩
  let φ : L.obj ⟶ M.obj := differentialPullback k f
  have : Mono φ := differentialPullback_mono_of_dominant_curve f
  obtain ⟨D, hD, ⟨e⟩, he⟩ := exists_effectiveCartierDivisor_twist_of_lineMap L M φ
  refine ⟨D, hD, ⟨e ≪≫ InvertibleSheaf.tensorProductObjIso L D.toInvertibleSheaf ≪≫
    (tensorLeft L.obj).mapIso (eqToIso (Scheme.CartierDivisor.toInvertibleSheaf_obj D))⟩, ?_⟩
  intro x
  have hx : IsClosed {(x : X)} :=
    TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one
      (coheight_le_one_of_curve (k := k)) x.property
  obtain ⟨U, tL, hU⟩ := L.obj.exists_mem_trivialization (x : X)
  obtain ⟨V, tM, hV⟩ := M.obj.exists_mem_trivialization (x : X)
  let W := U ⊓ V
  have hW : (x : X) ∈ W := ⟨hU, hV⟩
  let _ : Nonempty W := ⟨⟨x, hW⟩⟩
  let i : W ⟶ U := homOfLE inf_le_left
  let j : W ⟶ V := homOfLE inf_le_right
  let c := lineMapCoefficient φ tL tM i j
  obtain ⟨q, hq, hq'⟩ := he tL tM i j hW
  let a := X.presheaf.germ W x hW c
  have hq'' : (q : X.functionField) = algebraMap (X.presheaf.stalk (x : X)) X.functionField a :=
    hq'.trans (Scheme.algebraMap_germ_eq_germToFunctionField _ hW c).symm
  have hn := ord_differentialPullbackStalk_eq_ramificationIdx_sub_one f x hx
    (stalkLinearEquivOfTrivialization L.obj tL x hU)
    (stalkLinearEquivOfTrivialization M.obj tM x hV)
  rw [Scheme.CartierDivisor.coeff_toWeilDivisor]
  apply cartierOrder_eq_of_localEquation_ord D x q hq a hq''
  change Ring.ord _ (X.presheaf.germ W x hW c) = _
  rw [lineMapCoefficient_germ_eq_stalk φ tL tM i j x hW]
  exact hn

set_option backward.isDefEq.respectTransparency false in
/-- The effective Cartier divisor twisting the canonical sheaves has Weil
divisor equal to the tame different transported from the function field. -/
theorem exists_effectiveCartierRamificationDivisor_with_WeilDivisor
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    let _ : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let _ : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
    let _ : IsNoetherian X := ⟨⟩
    ∃ D : Scheme.CartierDivisor X, D.IsEffective ∧
      Nonempty (X.relativeDifferentials k ≅
        (Scheme.Modules.pullback f).obj (Y.relativeDifferentials k) ⊗ D.sheaf) ∧
      D.toWeilDivisor = curveRamificationDivisor k f := by
  let := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  obtain ⟨D, hD, e, hc⟩ := exists_effectiveCartierRamificationDivisor (k := k) f
  refine ⟨D, hD, e, ?_⟩
  ext x
  exact (hc x).trans (coeff_curveRamificationDivisor_eq_localIndex k f x).symm

set_option backward.isDefEq.respectTransparency false in
/-- The effective Weil ramification divisor gives the canonical sheaf twist and
has finite-support coefficients equal to the local ramification indices minus one. -/
theorem exists_effectiveWeilRamificationDivisor :
    let _ : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    let _ := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
    ∃ D : SchemeWeilDivisor X, D.IsEffective ∧
      Nonempty (X.relativeDifferentials k ≅
        (Scheme.Modules.pullback f).obj (Y.relativeDifferentials k) ⊗ SchemeWeilDivisor.sheaf D) ∧
      ∀ x : CodimensionOnePoint X,
        let A := Y.presheaf.stalk (f x)
        let B := X.presheaf.stalk (x : X)
        let _ : Algebra A B := algebraStalkMap f x
        WeilDivisor.coeff D x = (((IsLocalRing.maximalIdeal B).ramificationIdx A - 1 : ℕ) : ℤ) := by
  let := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve (k := k) (X := X)
  obtain ⟨D, -, ⟨e⟩, hD⟩ := exists_effectiveCartierRamificationDivisor (k := k) f
  refine ⟨D.toWeilDivisor, (WeilDivisor.isEffective_iff _).mpr ?_, ⟨e ≪≫
    (tensorLeft _).mapIso (D.sheafIsoToWeilDivisor (coheight_le_one_of_curve (k := k)))⟩, hD⟩
  intro x
  rw [hD x]
  exact Int.natCast_nonneg _

end RamificationDivisor

end

end TinyTauDemo
