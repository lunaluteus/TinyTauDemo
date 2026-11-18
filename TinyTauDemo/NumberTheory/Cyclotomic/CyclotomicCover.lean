/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicDifferentials
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TinyTauDemo.AlgebraicGeometry.Dedekind.IntegerFibres
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Polynomial.Div
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# The cyclotomic cover of the integer spectrum

The spectrum of the ring of integers is finite and flat over the integer
spectrum. For an odd prime cyclotomic field, restricting to the complement
of the prime gives an étale morphism. The scheme-theoretic fibre at the prime
is the spectrum of a truncated polynomial ring over its residue field.
Its nonreducedness makes the complement of the prime the largest étale base open.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `34239e77e326c658dcbc8f1ce9b3526b80d0405f`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField Polynomial

namespace TinyTauDemo

/-- The structural morphism from the spectrum of the ring of integers of a number field. -/
noncomputable def ringOfIntegersSpecHom (K : Type) [Field K] [NumberField K] :
    Spec (CommRingCat.of (𝓞 K)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 K)))

/-- The ring of integers of a number field is finite and flat over the integers. -/
theorem ringOfIntegersSpecHom_finite_flat (K : Type) [Field K] [NumberField K] :
    IsFinite (ringOfIntegersSpecHom K) ∧ Flat (ringOfIntegersSpecHom K) := by
  rw [ringOfIntegersSpecHom, IsFinite.SpecMap_iff, Flat.SpecMap_iff]
  change (algebraMap ℤ (𝓞 K)).Finite ∧ (algebraMap ℤ (𝓞 K)).Flat
  exact ⟨RingHom.finite_algebraMap.mpr inferInstance,
    RingHom.flat_algebraMap_iff.mpr inferInstance⟩

/-- The cyclotomic cover is étale over the basic open complementary to the odd prime. -/
theorem ringOfIntegersSpecHom_etale_away {K : Type} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    Etale (ringOfIntegersSpecHom K ∣_ PrimeSpectrum.basicOpen (R := ℤ) (p : ℤ)) := by
  let φ := CommRingCat.ofHom (algebraMap ℤ (𝓞 K))
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme) :=
    HasRingHomProperty.stableUnderComposition RingHom.Etale.stableUnderComposition
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition (by
      intro X Y g hg
      have : IsIso g := hg
      infer_instance)
  refine (MorphismProperty.arrow_mk_iso_iff @Etale
    (SpecMapRestrictBasicOpenIso φ (p : ℤ))).mpr ?_
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  let A := Localization.Away (p : ℤ)
  let B := Localization.Away (algebraMap ℤ (𝓞 K) (p : ℤ))
  let _ : Algebra A B := (Localization.awayMap (algebraMap ℤ (𝓞 K)) (p : ℤ)).toAlgebra
  change Algebra.Etale A B
  have : Algebra.Etale ℤ A := Algebra.Etale.of_isLocalizationAway (p : ℤ)
  have : Algebra.Etale ℤ B := by
    change Algebra.Etale ℤ (Localization.Away (algebraMap ℤ (𝓞 K) (p : ℤ)))
    rw [map_natCast]
    exact hζ.etale_localizationAway_natCast hp2
  have := IsScalarTower.of_algebraMap_eq'
    (R := ℤ) (S := A) (A := B) (Subsingleton.elim _ _)
  exact Algebra.Etale.of_restrictScalars ℤ A B

/-- The scheme-theoretic fibre of the cyclotomic cover at the rational prime is the spectrum
of the ring of integers modulo the `(p - 1)`st power of the unique prime above it. -/
noncomputable def ringOfIntegersSpecHom_fiber_prime {K : Type} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    (ringOfIntegersSpecHom K).fiber (primeIntPoint p) ≅
      Spec (CommRingCat.of (𝓞 K ⧸ (Ideal.span {1 - hζ.toInteger}) ^ (p - 1))) := by
  let I := (primeIntPoint p).asIdeal
  let _ : I.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let e : (ℤ ⧸ I) ≃ₐ[ℤ] I.ResidueField :=
    .ofBijective (IsScalarTower.toAlgHom ℤ (ℤ ⧸ I) I.ResidueField)
      (I.bijective_algebraMap_quotient_residueField)
  let m : I.Fiber (𝓞 K) ≃+*
      (𝓞 K ⧸ I.map (algebraMap ℤ (𝓞 K))) :=
    ((Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : 𝓞 K ≃ₐ[ℤ] 𝓞 K)).toRingEquiv).trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (𝓞 K) I).symm.toRingEquiv
  have hI : I.map (algebraMap ℤ (𝓞 K)) = Ideal.span {1 - hζ.toInteger} ^ (p - 1) := by
    change (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 K)) = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast, hζ.span_natCast_eq_span_one_sub_pow]
  exact Arrow.leftFunc.mapIso (Spec.fiberToSpecResidueFieldIso ℤ (𝓞 K) (primeIntPoint p)) ≪≫
    Scheme.Spec.mapIso ((m.trans (Ideal.quotEquivOfEq hI)).symm.toCommRingCatIso).op

/-- Modulo the rational prime, the cyclotomic integer ring is a truncated polynomial ring. -/
noncomputable def cyclotomicQuotientPrimeEquivTruncated {K : Type} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) ≃+* (ZMod p)[X] ⧸ Ideal.span {(X : (ZMod p)[X]) ^ (p - 1)} := by
  have hgen : Algebra.adjoin ℤ {hζ.toInteger} = ⊤ := by
    rw [← hζ.integralPowerBasis_gen]
    exact hζ.integralPowerBasis.adjoin_gen_eq_top
  have hnot : ¬ p ∣ RingOfIntegers.exponent hζ.toInteger := by
    rw [RingOfIntegers.exponent_eq_one_iff.mpr hgen]
    exact hp.out.not_dvd_one
  have hmin : minpoly ℤ hζ.toInteger = cyclotomic p ℤ := calc
    minpoly ℤ hζ.toInteger = minpoly ℤ (hζ.toInteger : K) :=
      (RingOfIntegers.minpoly_coe _).symm
    _ = minpoly ℤ ζ := congrArg (minpoly ℤ) hζ.coe_toInteger
    _ = cyclotomic p ℤ := (cyclotomic_eq_minpoly hζ hp.out.pos).symm
  have hcycl : cyclotomic p (ZMod p) = (X - 1) ^ (p - 1) := by
    simpa only [one_mul, cyclotomic_one] using
      (cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) hp.out.not_dvd_one)
  refine (RingOfIntegers.ZModXQuotSpanEquivQuotSpan hnot).symm.trans
    (Ideal.quotientEquiv _ _ (Polynomial.taylorEquiv (1 : ZMod p)).toRingEquiv ?_)
  rw [hmin, map_cyclotomic_int, hcycl, Ideal.map_span, Set.image_singleton]
  simp [Polynomial.taylorEquiv, Polynomial.taylor_X]

/-- The scheme-theoretic fibre of the cyclotomic cover at the rational prime is a
thickened point of length `p - 1`. -/
noncomputable def ringOfIntegersSpecHom_fiber_prime_truncated {K : Type} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    (ringOfIntegersSpecHom K).fiber (primeIntPoint p) ≅
      Spec (CommRingCat.of ((ZMod p)[X] ⧸ Ideal.span {(X : (ZMod p)[X]) ^ (p - 1)})) := by
  refine ringOfIntegersSpecHom_fiber_prime hζ ≪≫ Scheme.Spec.mapIso ?_
  exact ((Ideal.quotEquivOfEq hζ.span_natCast_eq_span_one_sub_pow.symm).trans
    (cyclotomicQuotientPrimeEquivTruncated hζ)).symm.toCommRingCatIso.op

variable {K : Type} [Field K] [NumberField K]
  {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- The fibre of the odd-prime cyclotomic cover over the ramified point is nonreduced. -/
theorem not_isReduced_ringOfIntegersSpecHom_fiber_prime (hζ : IsPrimitiveRoot ζ p)
    (hp2 : p ≠ 2) :
    ¬ AlgebraicGeometry.IsReduced ((ringOfIntegersSpecHom K).fiber (primeIntPoint p)) := by
  let I : Ideal (ZMod p)[X] := Ideal.span {(X : (ZMod p)[X]) ^ (p - 1)}
  let x : (ZMod p)[X] ⧸ I := Ideal.Quotient.mk I X
  have hx : x ^ (p - 1) = 0 := by
    dsimp only [x]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  intro h
  have hred : AlgebraicGeometry.IsReduced (Spec (.of ((ZMod p)[X] ⧸ I))) :=
    isReduced_of_isOpenImmersion (ringOfIntegersSpecHom_fiber_prime_truncated hζ).inv
  have : IsReduced ((ZMod p)[X] ⧸ I) := (affine_isReduced_iff _).mp hred
  have hz : x = 0 := eq_zero_of_pow_eq_zero hx
  have hd : (X : (ZMod p)[X]) ^ (p - 1) ∣ X :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hlt : 1 < p - 1 := by have := hp.out.two_le; omega
  have hc := Polynomial.X_pow_dvd_iff.mp hd 1 hlt
  exact one_ne_zero ((Polynomial.coeff_X_one).symm.trans hc)

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of the odd-prime cyclotomic cover to a base open is étale exactly when the
open lies in the complement of the ramified prime. -/
theorem ringOfIntegersSpecHom_restrict_etale_iff (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2)
    (U : (Spec (.of ℤ)).Opens) :
    Etale (ringOfIntegersSpecHom K ∣_ U) ↔ U ≤ PrimeSpectrum.basicOpen (R := ℤ) (p : ℤ) := by
  let f := ringOfIntegersSpecHom K
  let y := primeIntPoint p
  let D : (Spec (.of ℤ)).Opens := PrimeSpectrum.basicOpen (R := ℤ) (p : ℤ)
  constructor
  · intro hU x hx hxD
    have hxy : x = y := by
      apply PrimeSpectrum.ext
      have hle : Ideal.span {(p : ℤ)} ≤ x.asIdeal := by
        rw [Ideal.span_singleton_le_iff_mem]
        exact hxD
      exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le x.isPrime.ne_top hle).symm
    subst x
    let b := (Spec (.of ℤ)).fromSpecResidueField y
    let j := IsOpenImmersion.lift U.ι b (by
      rw [Scheme.range_fromSpecResidueField]
      rintro x rfl
      exact ⟨⟨y, hx⟩, rfl⟩)
    have hj : j ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
    have : GeometricallyReduced (f ∣_ U) := inferInstance
    have hr : AlgebraicGeometry.IsReduced (pullback (f ∣_ U) j) :=
      GeometricallyReduced.geometrically_isReduced j _ _ (.of_hasPullback _ _)
    have hcart := (IsPullback.of_hasPullback (f ∣_ U) j).paste_horiz
      (isPullback_morphismRestrict f U).flip
    rw [hj] at hcart
    exact not_isReduced_ringOfIntegersSpecHom_fiber_prime hζ hp2
      (isReduced_of_isOpenImmersion hcart.isoPullback.inv)
  · intro hUD
    change U ≤ D at hUD
    let g := (Spec (.of ℤ)).homOfLE hUD
    let i := (Spec (.of (𝓞 K))).homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ D from
      (Scheme.Hom.preimage_mono f hUD))
    have hg : g ≫ D.ι = U.ι := Scheme.homOfLE_ι _ _
    have hi : i ≫ (f ⁻¹ᵁ D).ι = (f ⁻¹ᵁ U).ι := Scheme.homOfLE_ι _ _
    have hc : (f ∣_ U) ≫ g = i ≫ f ∣_ D := by
      rw [← cancel_mono D.ι, Category.assoc, hg, Category.assoc, morphismRestrict_ι f U,
        morphismRestrict_ι f D, ← Category.assoc, hi]
    have hcart : IsPullback (f ∣_ U) i g (f ∣_ D) := by
      refine IsPullback.of_bot (v₂₁ := (f ⁻¹ᵁ D).ι) (v₂₂ := D.ι) ?_ hc
        (isPullback_morphismRestrict f D)
      rw [hg, hi]
      exact isPullback_morphismRestrict f U
    exact MorphismProperty.of_isPullback hcart.flip
      (ringOfIntegersSpecHom_etale_away hζ hp2)

end TinyTauDemo
