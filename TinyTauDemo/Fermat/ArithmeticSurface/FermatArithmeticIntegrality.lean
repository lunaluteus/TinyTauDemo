/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatProjective
import TinyTauDemo.Fermat.ArithmeticSurface.FermatConeBaseChange
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Integrality of the Fermat scheme over the integers

The homogeneous equation is irreducible over the algebraic closure of the rationals.
Its coefficient of `X₀^n` is one, so a constant factor after extending coefficients
already comes from an integer unit. The projective model is integral over any
characteristic-zero domain by integrality of its cone coordinate ring.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `2a0cfce18730a72e3af59be8ebaa793115ffd6d3`.
-/

public section

open AlgebraicGeometry MvPolynomial

namespace TinyTauDemo

private theorem coeff_fermatEquation_zero_pow (R : Type*) [CommRing R]
    {n : ℕ} (hn : 0 < n) :
    (fermatEquation R n).coeff (Finsupp.single (0 : Fin 3) n) = 1 := by
  classical
  have hne (i : Fin 3) (hi : i ≠ 0) :
      Finsupp.single i n ≠ Finsupp.single (0 : Fin 3) n := by
    intro h
    have hh := congrArg (fun a : Fin 3 →₀ ℕ ↦ a i) h
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hi] at hh
    exact hn.ne' hh
  simp [fermatEquation_def, coeff_X_pow, hne 1 (by decide), hne 2 (by decide)]

/-- The homogeneous Fermat equation over `ℤ` is irreducible in every positive degree. -/
theorem fermatEquation_int_irreducible {n : ℕ} (hn : 0 < n) :
    Irreducible (fermatEquation ℤ n) := by
  let K := AlgebraicClosure ℚ
  let f : MvPolynomial (Fin 3) ℤ →+* MvPolynomial (Fin 3) K :=
    MvPolynomial.map (algebraMap ℤ K)
  have hmap : f (fermatEquation ℤ n) = fermatEquation K n := by
    simp [f, fermatEquation_def]
  have hK : Irreducible (fermatEquation K n) := fermatEquation_irreducible hn
  have hunit (a b : MvPolynomial (Fin 3) ℤ) (hab : fermatEquation ℤ n = a * b)
      (ha : IsUnit (f a)) : IsUnit a := by
    have haK : f a = C ((f a).coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp (isUnit_iff_totalDegree_of_isReduced.mp ha).2
    have haC : a = C (a.coeff 0) := by
      apply MvPolynomial.map_injective (algebraMap ℤ K) (RingHom.injective_int _)
      simpa only [f, MvPolynomial.coeff_map, MvPolynomial.map_C] using haK
    have hcoeff := congrArg (fun p : MvPolynomial (Fin 3) ℤ ↦ p.coeff (Finsupp.single 0 n)) hab
    change (fermatEquation ℤ n).coeff (Finsupp.single 0 n) =
      (a * b).coeff (Finsupp.single 0 n) at hcoeff
    rw [coeff_fermatEquation_zero_pow ℤ hn, haC, coeff_C_mul] at hcoeff
    rw [haC]
    exact (isUnit_iff_dvd_one.mpr ⟨_, hcoeff⟩).map C
  refine ⟨fun hu ↦ hK.not_isUnit (hmap ▸ hu.map f), fun a b hab ↦ ?_⟩
  have habK : fermatEquation K n = f a * f b := by rw [← hmap, hab, map_mul]
  rcases hK.isUnit_or_isUnit habK with ha | hb
  · exact Or.inl (hunit a b hab ha)
  · exact Or.inr (hunit b a (hab.trans (mul_comm _ _)) hb)

/-- The homogeneous coordinate ring of the integral Fermat model is a domain. -/
theorem fermatCoordinateRing_int_isDomain {n : ℕ} (hn : 0 < n) :
    IsDomain (FermatCoordinateRing ℤ n) := by
  have hf := (fermatEquation_int_irreducible hn).prime
  have : (fermatIdeal ℤ n).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  exact Ideal.Quotient.isDomain _

/-- The projective Fermat scheme over a characteristic-zero domain is integral
in every positive degree. -/
theorem fermatProjective_isIntegral_of_charZero (R : Type*) [CommRing R] [IsDomain R]
    [CharZero R] {n : ℕ} (hn : 0 < n) : IsIntegral (fermatProjective R n) := by
  let : IsDomain (FermatCoordinateRing R n) := fermatCoordinateRing_isDomain_of_charZero R hn
  let a : FermatCoordinateRing R n := Ideal.Quotient.mk _ (X 0)
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem (fermatGrading R n) Nat.one_pos
    (fermatCoord_mem_degree_one (k := R) (n := n) 0)
  let g : MvPolynomial (Fin 3) R →ₐ[R] R := aeval (![1, 0, 1] : Fin 3 → R)
  have hg : g (fermatEquation R n) = 0 := by
    simp [g, fermatEquation_def, zero_pow hn.ne']
  let φ : FermatCoordinateRing R n →ₐ[R] R := Ideal.Quotient.liftₐ _ g (by
    intro p hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rw [map_mul, hg, zero_mul])
  have ha : φ a = 1 := by change g (X 0) = 1; simp [g]
  apply Proj.isIntegral_of_isDomain (fermatGrading R n)
  intro he
  rw [he] at hmem
  have ha0 : a = 0 := Ideal.mem_bot.mp hmem
  exact one_ne_zero (ha.symm.trans (ha0 ▸ map_zero φ))

/-- The projective Fermat scheme over `ℤ` is integral in every positive degree. -/
theorem fermatProjective_int_isIntegral {n : ℕ} (hn : 0 < n) :
    IsIntegral (fermatProjective ℤ n) :=
  fermatProjective_isIntegral_of_charZero ℤ hn

end TinyTauDemo
