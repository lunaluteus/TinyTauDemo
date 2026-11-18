/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.ClosedDifferentialLength
public import TinyTauDemo.PlaceDifferentialLength
public import TinyTauDemo.SchemeHurwitz

/-!
# The ramification divisor and the local rings of a curve

The place of a point with a discrete valuation stalk restricts to the place
of its image under a dominant curve morphism. The associated ramification
index agrees with the index of the map on local rings. Reindexing the tame
different therefore gives a Weil divisor with coefficients equal to the
lengths of the actual relative differential stalks.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `f59d0ca264bd30e7f0d1b6748710096b3da07d71`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace TinyTauDemo

private theorem addVal_toNat_map_equiv {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    (e : A ≃+* B) {a : A} (ha : a ≠ 0) :
    (IsDiscreteValuationRing.addVal B (e a)).toNat =
      (IsDiscreteValuationRing.addVal A a).toNat := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha ht
  have het : Irreducible (e t) := (MulEquiv.irreducible_iff e).mpr ht
  let w := v.map e.toMonoidHom
  have hmap : e a = w * e t ^ n := by
    change e a = e v * e t ^ n
    rw [hv, map_mul, map_pow]
  rw [IsDiscreteValuationRing.addVal_def _ w het n hmap,
    IsDiscreteValuationRing.addVal_def _ v ht n hv]

section Places

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "F" => Y.functionField
local notation "L" => X.functionField
local notation "P" => X.toPlace (k := k) x
local notation "Q" => Y.toPlace (k := k) (f x)

/-- At a pair of discrete valuation stalks the place of the source restricts to
the place of its image. -/
theorem toPlace_restrict_eq_of_dominant_curveHom :
    letI : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    letI : IsScalarTower k F L :=
      IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
    letI := finiteDimensional_of_functionFields
      (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
      (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
    Place.restrict k F P = Q := by
  dsimp only
  let : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let := finiteDimensional_of_functionFields
    (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
    (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
  apply (Place.restrict_eq_iff_integers_le k F P Q).mpr
  intro r hr
  obtain ⟨a, rfl⟩ := (Y.mem_toPlace_integers_iff_exists_stalk (k := k) (f x) r).mp hr
  change f.functionFieldAlgHom k (algebraMap A F a) ∈ (Place.integers P)
  rw [Scheme.Hom.functionFieldAlgHom_apply, f.functionFieldMap_algebraMap_stalk_apply]
  exact X.algebraMap_stalk_mem_toPlace_integers x _

/-- The local ring ramification index matches the normalized index of the
function-field place attached to the source point. -/
theorem ramificationIdx_stalk_eq_toPlace :
    letI : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    letI : IsScalarTower k F L :=
      IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
    letI := finiteDimensional_of_functionFields
      (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
      (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
    letI : Algebra A B := algebraStalkMap f x
    (IsLocalRing.maximalIdeal B).ramificationIdx A = Place.ramificationIdx F P := by
  dsimp only
  let : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let := finiteDimensional_of_functionFields
    (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
    (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
  let : Algebra A B := algebraStalkMap f x
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hz : f.stalkMap x t ≠ 0 := by
    intro h
    have hh := f.functionFieldMap_algebraMap_stalk_apply x t
    rw [h, map_zero] at hh
    exact ht.ne_zero ((map_eq_zero_iff _ (IsFractionRing.injective A F)).mp
      ((map_eq_zero_iff _ (f.functionFieldMap).hom.injective).mp hh))
  rw [ramificationIdx_maximalIdeal_eq_toNat_addVal ht hz]
  let eX := X.stalkToPlaceIntegersAlgEquiv (k := k) x
  let eY := Y.stalkToPlaceIntegersAlgEquiv (k := k) (f x)
  let b := f.stalkMap x t
  have hb : eX b ≠ 0 := (map_ne_zero_iff _ eX.injective).mpr hz
  refine (addVal_toNat_map_equiv eX.toRingEquiv hz).symm.trans
    ((addVal_placeIntegers_eq_ord P hb).trans ?_)
  change (Place.ord P ((X.stalkToPlaceIntegersAlgEquiv (k := k) x (f.stalkMap x t) :
    Place.integers P) : L)).toNat = _
  rw [Scheme.coe_stalkToPlaceIntegersAlgEquiv, ← f.functionFieldMap_algebraMap_stalk_apply]
  have hmap (a : F) : algebraMap F L a = f.functionFieldMap a := by
    change f.functionFieldAlgHom k a = f.functionFieldMap a
    rw [Scheme.Hom.functionFieldAlgHom_apply]
  rw [← hmap, Place.ord_algebraMap_restrict k F P, toPlace_restrict_eq_of_dominant_curveHom k f x]
  have ht' : Irreducible (eY t) := (MulEquiv.irreducible_iff eY).mpr ht
  have hord : Place.ord Q (algebraMap A F t) = 1 := by
    -- Identify the order by transporting the uniformizer through the stalk equivalence.
    have hh := (addVal_toNat_map_equiv eY.toRingEquiv ht.ne_zero).symm.trans
      (addVal_placeIntegers_eq_ord Q ht'.ne_zero)
    change (IsDiscreteValuationRing.addVal A t).toNat =
      (Place.ord Q ((Y.stalkToPlaceIntegersAlgEquiv (k := k) (f x) t :
        Place.integers Q) : F)).toNat at hh
    rw [Scheme.coe_stalkToPlaceIntegersAlgEquiv] at hh
    have h1 := IsDiscreteValuationRing.addVal_def t (1 : Aˣ) ht 1 (by simp)
    rw [h1, ENat.toNat_natCast] at hh
    have hnonneg : 0 ≤ Place.ord Q (algebraMap A F t) :=
      (Place.mem_integers_iff_ord_nonneg Q).mp (Y.algebraMap_stalk_mem_toPlace_integers (f x) t)
    omega
  rw [hord, mul_one, Int.toNat_natCast]

end Places

section Divisor

variable (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsDominant f]

local notation "F" => Y.functionField
local notation "L" => X.functionField

/-- The tame different, viewed as a Weil divisor on the source curve. -/
noncomputable def curveRamificationDivisor
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    SchemeWeilDivisor X :=
  letI : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  letI : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let hF := Scheme.IsCurveOver.isFunctionField (X := Y) (k := k)
  let hL := Scheme.IsCurveOver.isFunctionField (X := X) (k := k)
  letI := finiteDimensional_of_functionFields hF hL
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  (Finsupp.domCongr (curveCodimensionOnePointEquivPlace k X).symm)
    (Divisor.tameDifferent k L hF)

private theorem coeff_curveRamificationDivisor_eq_toPlace
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (z : CodimensionOnePoint X) :
    letI : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
    letI : IsScalarTower k F L :=
      IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
    letI := finiteDimensional_of_functionFields
      (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
      (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
    (curveRamificationDivisor k f).coeff z =
      (Place.ramificationIdx F (X.toPlace (k := k) (z : X)) : ℤ) - 1 := by
  let : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let := finiteDimensional_of_functionFields
    (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
    (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  dsimp only [curveRamificationDivisor]
  rw [WeilDivisor.coeff, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    Equiv.symm_symm, curveCodimensionOnePointEquivPlace_apply]
  exact Divisor.coeff_tameDifferent _ _ _ _

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of k))]
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

private theorem codimensionOne_isClosed (hdim : topologicalKrullDim X ≤ 1)
    (z : CodimensionOnePoint X) : IsClosed {(z : X)} := by
  apply isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one _ z.property
  intro x
  exact_mod_cast (coheight_le_topologicalKrullDim x).trans hdim

set_option backward.isDefEq.respectTransparency false in
/-- The tame different has coefficient equal to the local ramification index minus one. -/
theorem coeff_curveRamificationDivisor_eq_localIndex
    (z : CodimensionOnePoint X) :
    letI : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk (z : X)) := algebraStalkMap f z
    (curveRamificationDivisor k f).coeff z =
      (((IsLocalRing.maximalIdeal (X.presheaf.stalk (z : X))).ramificationIdx
        (Y.presheaf.stalk (f z)) - 1 : ℕ) : ℤ) := by
  let x : X := z
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := algebraStalkMap f x
  have hx := codimensionOne_isClosed (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le z
  have hy := isClosed_image_of_smoothCurveHom (k := k) f x hx
  let : IsDiscreteValuationRing (Y.presheaf.stalk (f x)) :=
    isDiscreteValuationRing_stalk_of_closed_smoothCurve (k := k) (f x) hy
  let : Algebra F L := (f.functionFieldAlgHom k).toRingHom.toAlgebra
  let : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((f.functionFieldAlgHom k).commutes r).symm
  let := finiteDimensional_of_functionFields
    (Scheme.IsCurveOver.isFunctionField (X := Y) (k := k))
    (Scheme.IsCurveOver.isFunctionField (X := X) (k := k))
  have epos := Place.ramificationIdx_pos F (X.toPlace (k := k) (z : X))
  rw [coeff_curveRamificationDivisor_eq_toPlace, ramificationIdx_stalk_eq_toPlace k f (z : X)]
  omega

/-- The coefficient of the tame ramification divisor is the actual relative
differential length at each codimension-one point. -/
theorem length_morphismRelativeDifferentials_stalk_eq_ramificationDivisor_coeff
    (z : CodimensionOnePoint X) :
    Module.length (X.presheaf.stalk (z : X))
        ((morphismRelativeDifferentials k f).presheaf.stalk (z : X)) =
      ↑(((curveRamificationDivisor k f).coeff z).toNat : ℕ) := by
  let : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk (z : X)) := algebraStalkMap f z
  have hx := codimensionOne_isClosed (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le z
  rw [length_morphismRelativeDifferentials_stalk_of_closed_smoothCurves f (z : X) hx,
    coeff_curveRamificationDivisor_eq_localIndex]
  rfl

end Divisor

end TinyTauDemo
