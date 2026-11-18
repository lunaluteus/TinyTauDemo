/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Dedekind.ClassGroup
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Picard
import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Effectivity
import TinyTauDemo.AlgebraicGeometry.Dedekind.DedekindSpectrum
import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Congr

/-!
# The Picard group of an affine Dedekind scheme

On the spectrum of a Dedekind domain, the order of a rational function at a
codimension-one point is the adic order of the corresponding prime ideal.
Reindexing divisors therefore identifies the ideal class group with the Picard group.
An ideal whose prime exponents give the divisor `D` determines the line bundle `𝒪(-D)`.
See `/roadmap/index.qmd#rem-scheme-dedekind @ 6c898bb09f74494b1e1688ff9200e2195612718c`.
-/

public section

open AlgebraicGeometry CategoryTheory IsDedekindDomain Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors

namespace TinyTauDemo

universe u

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- Every point of the spectrum of a Dedekind domain has codimension at most one. -/
theorem spec_coheight_le_one (x : Spec (.of R)) : coheight x ≤ 1 := by
  rw [← idealHeight_eq_coheight]
  let : x.asIdeal.IsPrime := x.isPrime
  exact_mod_cast (Ideal.height_le_ringKrullDim_of_isPrime (I := x.asIdeal)).trans
    (Order.KrullDimLE.krullDim_le (n := 1))

/-- The height-one primes of a Dedekind domain are the codimension-one points of its spectrum. -/
def heightOneSpectrumEquivCodimensionOneSpec :
    HeightOneSpectrum R ≃ CodimensionOnePoint (Spec (.of R)) where
  toFun v :=
    let x : Spec (.of R) := ⟨v.asIdeal, v.isPrime⟩
    ⟨x, le_antisymm (spec_coheight_le_one R x) (le_of_not_gt fun h ↦
      v.ne_bot (Ideal.height_eq_zero_iff_eq_bot.mp
        ((idealHeight_eq_coheight (.of R) x).trans (Order.lt_one_iff.mp h))))⟩
  invFun x := ⟨x.1.asIdeal, x.1.isPrime,
    Ideal.ne_bot_of_height_eq_one ((idealHeight_eq_coheight (.of R) x).trans x.property)⟩
  left_inv _ := HeightOneSpectrum.ext rfl
  right_inv _ := Subtype.ext (PrimeSpectrum.ext rfl)

private theorem spec_stalk_dvr (x : CodimensionOnePoint (Spec (.of R))) :
    IsDiscreteValuationRing ((Spec (.of R)).presheaf.stalk (x : Spec (.of R))) := by
  apply (Spec.stalk_isDiscreteValuationRing_iff_ne_genericPoint x.1).mpr
  rw [genericPoint_eq_bot_of_affine]
  intro hx
  exact (Ideal.ne_bot_of_height_eq_one
    ((idealHeight_eq_coheight (.of R) x).trans x.property)) (congrArg PrimeSpectrum.asIdeal hx)

local instance : IsNoetherian (Spec (.of R)) := isNoetherian_Spec.mpr inferInstance

noncomputable local instance : Algebra R (Spec (.of R)).functionField :=
  instAlgebraCarrierFunctionFieldSpec (.of R)

local instance : IsFractionRing R (Spec (.of R)).functionField :=
  functionField_isFractionRing_of_affine (.of R)

local instance : ∀ x : CodimensionOnePoint (Spec (.of R)),
    IsDiscreteValuationRing ((Spec (.of R)).presheaf.stalk (x : Spec (.of R))) :=
  spec_stalk_dvr R

local instance : Fact (∀ x : Spec (.of R), coheight x ≤ 1) :=
  ⟨spec_coheight_le_one R⟩

/-- The prime exponents identify invertible fractional ideals with Weil divisors
on the spectrum of a Dedekind domain. -/
noncomputable def fractionalIdealDivisorSpecAddEquiv :
    Additive (FractionalIdeal R⁰ (Spec (.of R)).functionField)ˣ ≃+
      SchemeWeilDivisor (Spec (.of R)) :=
  (fractionalIdealDivisorAddEquiv R (Spec (.of R)).functionField).trans
    (Finsupp.domCongr (heightOneSpectrumEquivCodimensionOneSpec R))

/-- The coefficient at the point of a prime is the exponent of that prime in the ideal. -/
@[simp]
theorem coeff_fractionalIdealDivisorSpecAddEquiv
    (I : (FractionalIdeal R⁰ (Spec (.of R)).functionField)ˣ)
    (v : HeightOneSpectrum R) :
    WeilDivisor.coeff (fractionalIdealDivisorSpecAddEquiv R (Additive.ofMul I))
      (heightOneSpectrumEquivCodimensionOneSpec R v) =
        FractionalIdeal.count (Spec (.of R)).functionField v I := by
  let e := heightOneSpectrumEquivCodimensionOneSpec R
  change WeilDivisor.coeff (Finsupp.domCongr e _) (e v) = _
  rw [Finsupp.domCongr_apply, WeilDivisor.coeff, Finsupp.equivMapDomain_apply,
    e.symm_apply_apply]
  change WeilDivisor.coeff
    (fractionalIdealDivisorAddEquiv R (Spec (.of R)).functionField (Additive.ofMul I)) v = _
  rw [fractionalIdealDivisorAddEquiv_apply]
  exact coeff_fractionalIdealDivisor R (Spec (.of R)).functionField (Additive.ofMul I) v

private theorem specOrderAt_eq_adicOrd
    (v : HeightOneSpectrum R) (f : Additive (Spec (.of R)).functionFieldˣ) :
    SchemeWeilDivisor.orderAt (heightOneSpectrumEquivCodimensionOneSpec R v) f =
      adicOrd R (Spec (.of R)).functionField v f := by
  let X := Spec (.of R)
  let x := heightOneSpectrumEquivCodimensionOneSpec R v
  let S := X.presheaf.stalk (x : X)
  let : IsDiscreteValuationRing S := spec_stalk_dvr R x
  let : Algebra R S := StructureSheaf.stalkAlgebra R x.1
  let : IsLocalization.AtPrime S v.asIdeal := StructureSheaf.IsLocalization.to_stalk R x.1
  let : IsScalarTower R S X.functionField := IsScalarTower.of_algebraMap_eq
    (R := R) (S := S) (A := X.functionField) fun r ↦ by
    have hg := (genericPoint_spec X).specializes (Set.mem_univ (x : X))
    change StructureSheaf.toStalk R (genericPoint X) r =
      (X.presheaf.stalkSpecializes hg) (StructureSheaf.toStalk R (x : X) r)
    exact (StructureSheaf.toStalk_stalkSpecializes_apply hg r).symm
  have hval :
      X.ordHom (x : X) x.property (f.toMul : X.functionField) =
        (v.valuation X.functionField (f.toMul : X.functionField))⁻¹ := by
    change Ring.ordFrac S _ = _
    exact v.ordFrac_eq_inv_adicValuation _
  rw [SchemeWeilDivisor.orderAt_apply, adicOrd_apply,
    X.ord_eq_unzero_ordHom x.property (Units.ne_zero _), WithZero.toAdd_unzero_eq_log,
    hval, WithZero.log_inv]

private theorem specPrincipalDivisor_eq_reindex
    (f : Additive (Spec (.of R)).functionFieldˣ) :
    Finsupp.domCongr (heightOneSpectrumEquivCodimensionOneSpec R)
      ((OrderSystem.ofDedekindDomain R (Spec (.of R)).functionField).principalDivisor f) =
      (OrderSystem.ofScheme (Spec (.of R))).principalDivisor f := by
  let e := heightOneSpectrumEquivCodimensionOneSpec R
  apply WeilDivisor.ext_iff.mpr
  intro x
  obtain ⟨v, rfl⟩ := e.surjective x
  change WeilDivisor.coeff (Finsupp.domCongr e _) (e v) = _
  rw [Finsupp.domCongr_apply, WeilDivisor.coeff, Finsupp.equivMapDomain_apply,
    e.symm_apply_apply]
  change WeilDivisor.coeff _ v = WeilDivisor.coeff _ (e v)
  rw [OrderSystem.coeff_principalDivisor, OrderSystem.coeff_principalDivisor,
    OrderSystem.ofDedekindDomain_ord, OrderSystem.ofScheme_ord]
  exact (specOrderAt_eq_adicOrd R v f).symm

private noncomputable def classGroupAddEquivPicardSpec :
    Additive (ClassGroup R) ≃+ Additive (LineBundleClass (Spec (.of R))) := by
  let X := Spec (.of R)
  let e := OrderSystem.classGroupCongr (heightOneSpectrumEquivCodimensionOneSpec R)
    (AddEquiv.refl (Additive X.functionFieldˣ)) (fun f ↦ by
      rw [AddEquiv.refl_apply]
      exact specPrincipalDivisor_eq_reindex R f)
  exact (WeilDivisor.classGroupAddEquiv R X.functionField).symm.trans
    (e.trans ((AddEquiv.neg _).trans (SchemeWeilDivisor.classGroupAddEquivLineBundleClass X)))

/-- The ideal class group of a Dedekind domain is the Picard group of its affine spectrum. -/
noncomputable def classGroupMulEquivPicardSpec :
    ClassGroup R ≃* LineBundleClass (Spec (.of R)) :=
  AddEquiv.toMultiplicative (classGroupAddEquivPicardSpec R)

/-- The class of a fractional ideal maps to the line bundle of the negative of its divisor. -/
theorem classGroupMulEquivPicardSpec_mk
    (I : (FractionalIdeal R⁰ (Spec (.of R)).functionField)ˣ) :
    classGroupMulEquivPicardSpec R (ClassGroup.mk (Spec (.of R)).functionField I) =
      SchemeWeilDivisor.toLineBundleClass (spec_coheight_le_one R)
        (-fractionalIdealDivisorSpecAddEquiv R (Additive.ofMul I)) := by
  apply Additive.ofMul.injective
  change classGroupAddEquivPicardSpec R (Additive.ofMul (ClassGroup.mk _ I)) = _
  simp only [classGroupAddEquivPicardSpec, AddEquiv.trans_apply, AddEquiv.neg_apply,
    WeilDivisor.classGroupAddEquiv_symm_ofMul_mk, OrderSystem.classGroupCongr_divisorClass]
  rw [← map_neg, SchemeWeilDivisor.classGroupAddEquivLineBundleClass_apply,
    SchemeWeilDivisor.classGroupToLineBundleClass_divisorClass]
  simp only [fractionalIdealDivisorSpecAddEquiv, AddEquiv.trans_apply,
    fractionalIdealDivisorAddEquiv_apply]

/-- The global rational sections of the line bundle attached to a fractional ideal
are precisely the members of that ideal. -/
theorem mem_sections_neg_fractionalIdealDivisor_iff
    (I : (FractionalIdeal R⁰ (Spec (.of R)).functionField)ˣ)
    (s : Γ(Scheme.rationalFunctions (Spec (.of R)), ⊤)) :
    s ∈ SchemeWeilDivisor.sections
      (-fractionalIdealDivisorSpecAddEquiv R (Additive.ofMul I)) ⊤ ↔
      Scheme.rationalFunctionsEquiv (⊤ : (Spec (.of R)).Opens) s ∈
        (I : FractionalIdeal R⁰ (Spec (.of R)).functionField) := by
  let X := Spec (.of R)
  let K := X.functionField
  let z := Scheme.rationalFunctionsEquiv (⊤ : X.Opens) s
  let e := heightOneSpectrumEquivCodimensionOneSpec R
  let D := fractionalIdealDivisorSpecAddEquiv R (Additive.ofMul I)
  rw [SchemeWeilDivisor.mem_sections_iff]
  change (z = 0 ∨ ∀ y : CodimensionOnePoint X, (y : X) ∈ (⊤ : X.Opens) →
    -WeilDivisor.coeff (-D) y ≤ X.ord z y) ↔ z ∈ (I : FractionalIdeal R⁰ K)
  rcases eq_or_ne z 0 with h₀ | h₀
  · simp only [h₀, true_or, FractionalIdeal.zero_mem]
  simp only [h₀, false_or]
  let u := Units.mk0 z h₀
  let J := toPrincipalIdeal R K u
  have hspan : ((J : FractionalIdeal R⁰ K) ≤ I) ↔ z ∈ (I : FractionalIdeal R⁰ K) := by
    dsimp only [J, u]
    rw [coe_toPrincipalIdeal, Units.val_mk0]
    exact FractionalIdeal.spanSingleton_le_iff_mem
  have hmul : ((J * I⁻¹ : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) ≤ 1 ↔
      (J : FractionalIdeal R⁰ K) ≤ I := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val,
      mul_inv_le_iff₀ (bot_lt_iff_ne_bot.mpr I.ne_zero), one_mul]
  have hdiv :
      fractionalIdealDivisor R K (Additive.ofMul (J * I⁻¹)) =
        fractionalIdealDivisor R K (Additive.ofMul J) -
          fractionalIdealDivisor R K (Additive.ofMul I) := by
    change fractionalIdealDivisor R K (Additive.ofMul J - Additive.ofMul I) = _
    rw [map_sub]
  have heff :
      IsEffective (fractionalIdealDivisor R K (Additive.ofMul (J * I⁻¹))) ↔
        ((J * I⁻¹ : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) ≤ 1 :=
    isEffective_fractionalIdealDivisor_iff (Additive.ofMul (J * I⁻¹))
  rw [← hspan, ← hmul, ← heff, hdiv, isEffective_iff]
  simp only [WeilDivisor.coeff_sub, WeilDivisor.coeff_fractionalIdealDivisor, sub_nonneg,
    toMul_ofMul]
  have hD (v : HeightOneSpectrum R) :
      WeilDivisor.coeff D (e v) = FractionalIdeal.count K v I := by
    exact coeff_fractionalIdealDivisorSpecAddEquiv R I v
  have hord (v : HeightOneSpectrum R) : X.ord z (e v) = FractionalIdeal.count K v J := by
    have h := specOrderAt_eq_adicOrd R v (Additive.ofMul u)
    rwa [SchemeWeilDivisor.orderAt_apply, adicOrd_eq_fractionalIdeal_count] at h
  constructor
  · intro h v
    simpa only [WeilDivisor.coeff_neg, neg_neg, hD, hord] using h (e v) trivial
  · intro h y _
    obtain ⟨v, rfl⟩ := e.surjective y
    simpa only [WeilDivisor.coeff_neg, neg_neg, hD, hord] using h v

end TinyTauDemo
