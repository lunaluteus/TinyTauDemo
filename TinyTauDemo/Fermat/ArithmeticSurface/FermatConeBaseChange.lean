/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatProjective
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of the affine Fermat cone

The cone coordinate ring embeds into its scalar extension along an embedding of coefficient
rings: express the equation as a monic polynomial in the first coordinate, and use the
compatibility of monic division with coefficient maps. Over a characteristic-zero domain,
extend coefficients to the algebraic closure of its fraction field to prove integrality.

See `/roadmap/index.qmd#rem-arithmetic-surface @ 8b15d73ad96ab5091df8cf67cc1af9bd0caa8263`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField MvPolynomial
open scoped TensorProduct

namespace TinyTauDemo

private theorem fermatEquation_finSuccEquiv_monic (R : Type*) [CommRing R] [Nontrivial R]
    {n : ℕ} (hn : 0 < n) : (finSuccEquiv R 2 (fermatEquation R n)).Monic := by
  have h1 : (1 : Fin 3) = (0 : Fin 2).succ := rfl
  have h2 : (2 : Fin 3) = (1 : Fin 2).succ := rfl
  rw [fermatEquation_def, map_sub, map_add, map_pow, finSuccEquiv_X_zero,
    h1, map_pow, finSuccEquiv_X_succ, h2, map_pow, finSuccEquiv_X_succ,
    ← map_pow, ← map_pow, add_sub_assoc, ← map_sub]
  exact (Polynomial.monic_X_pow_add_C _ hn.ne')

private theorem fermatEquation_dvd_of_map_dvd {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) {n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin 3) R} (h : fermatEquation S n ∣ g.map f) :
    fermatEquation R n ∣ g := by
  have hcomm (q : MvPolynomial (Fin 3) R) :
      finSuccEquiv S 2 (q.map f) =
        (finSuccEquiv R 2 q).map (MvPolynomial.map f) := by
    apply Polynomial.ext
    intro i
    ext a
    simp only [Polynomial.coeff_map, finSuccEquiv_coeff_coeff, MvPolynomial.coeff_map]
  have heq : (fermatEquation R n).map f = fermatEquation S n := by
    simp [fermatEquation_def]
  rw [← heq] at h
  have hh := map_dvd (finSuccEquiv S 2) h
  rw [hcomm, hcomm] at hh
  have hd := (Polynomial.map_dvd_map _ (MvPolynomial.map_injective f hf)
    (fermatEquation_finSuccEquiv_monic R hn)).mp hh
  obtain ⟨q, hq⟩ := hd
  refine ⟨(finSuccEquiv R 2).symm q, (finSuccEquiv R 2).injective ?_⟩
  rwa [map_mul, AlgEquiv.apply_symm_apply]

/-- The Fermat cone over a characteristic-zero domain is integral in every positive degree. -/
theorem fermatCoordinateRing_isDomain_of_charZero (R : Type*) [CommRing R] [IsDomain R]
    [CharZero R] {n : ℕ} (hn : 0 < n) : IsDomain (FermatCoordinateRing R n) := by
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hI : fermatIdeal R n ≤ (fermatIdeal K n).comap (MvPolynomial.map f) := by
    apply Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ?_)
    change MvPolynomial.map f (fermatEquation R n) ∈ fermatIdeal K n
    rw [show MvPolynomial.map f (fermatEquation R n) = fermatEquation K n by
      simp [fermatEquation_def]]
    exact Ideal.mem_span_singleton_self _
  let q := Ideal.quotientMap (fermatIdeal K n) (MvPolynomial.map f) hI
  have hq : Function.Injective q := by
    apply (injective_iff_map_eq_zero q).mpr
    intro x hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (fermatIdeal K n) (g.map f) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, fermatIdeal, Ideal.mem_span_singleton] at hx ⊢
    exact fermatEquation_dvd_of_map_dvd f hf hn hx
  let : IsDomain (FermatCoordinateRing K n) := fermatCoordinateRing_isDomain K hn
  exact Function.Injective.isDomain q hq

/-- Base change of the integral affine Fermat cone gives the Fermat cone with coefficients
in the new ring. -/
noncomputable def tensorFermatConeEquiv (R : Type*) [CommRing R] (n : ℕ) :
    R ⊗[ℤ] FermatCoordinateRing ℤ n ≃ₐ[R] FermatCoordinateRing R n := by
  let A := MvPolynomial (Fin 3) ℤ
  let F := fermatEquation ℤ n
  let I := fermatIdeal ℤ n
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 3) ℤ R
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := ℤ) R A R I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span {fermatEquation R n} =
    (I.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := R))).map e.toRingHom
  rw [show I = Ideal.span {F} from rfl, Ideal.map_span, Set.image_singleton,
    Ideal.map_span, Set.image_singleton]
  congr 2
  change fermatEquation R n = e (1 ⊗ₜ[ℤ] F)
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  simp [F, fermatEquation_def]

/-- The actual base change of the integral affine Fermat cone to the ring of integers of
a number field, in particular to the prime cyclotomic ring, is an integral scheme. -/
theorem isIntegral_fermatCone_baseChange_ringOfIntegers (K : Type) [Field K] [NumberField K]
    {n : ℕ} (hn : 0 < n) : IsIntegral
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ (FermatCoordinateRing ℤ n))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝓞 K))))) := by
  have hIntegral : IsIntegral (Spec (.of (FermatCoordinateRing (𝓞 K) n))) :=
    (affine_isIntegral_iff _).mpr (fermatCoordinateRing_isDomain_of_charZero _ hn)
  let e := pullbackSymmetry _ _ ≪≫ pullbackSpecIso ℤ (𝓞 K) (FermatCoordinateRing ℤ n) ≪≫
    Scheme.Spec.mapIso ((tensorFermatConeEquiv (𝓞 K) n).symm.toRingEquiv.toCommRingCatIso).op
  exact @IsIntegral.of_isIso _ _ hIntegral e.inv inferInstance

end TinyTauDemo
