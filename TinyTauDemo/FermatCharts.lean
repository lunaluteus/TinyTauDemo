/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatProjective
public import TinyTauDemo.FermatAffineSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Affine charts of the projective Fermat scheme

Degree-zero localization at a coordinate is the dehomogenized equation ring.
The resulting three affine charts give smoothness of the projective scheme.
See `/roadmap/index.qmd#prp-fermat-genus` @ `acad2219963be552a5a2e3f90b6e76114117f1e6`.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial TauCeti.GradedAlgebra
open HomogeneousLocalization

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k]

private noncomputable abbrev coord (n : ℕ) (i : Fin 3) : FermatCoordinateRing k n :=
  Ideal.Quotient.mk (fermatIdeal k n) (X i)

private noncomputable def chartQuotient (n : ℕ) (i : Fin 3) :
    FermatCoordinateRing k n →+* FermatAffineRing k n i :=
  Ideal.Quotient.lift (fermatIdeal k n)
    ((Ideal.Quotient.mk _).comp (TauCeti.dehomogenize (R := k) i).toRingHom) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hd : fermatEquation k n ∣ a := Ideal.mem_span_singleton.mp ha
      exact Ideal.mem_span_singleton.mpr (map_dvd (TauCeti.dehomogenize (R := k) i) hd))

private theorem chartQuotient_mk (n : ℕ) (i : Fin 3) (p : MvPolynomial (Fin 3) k) :
    chartQuotient k n i (Ideal.Quotient.mk (fermatIdeal k n) p) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize (R := k) i p) := rfl

private theorem chartQuotient_coord (n : ℕ) (i : Fin 3) :
    chartQuotient k n i (coord k n i) = 1 := by
  rw [chartQuotient_mk, TauCeti.dehomogenize_X, Fin.insertNth_apply_same, map_one]

private noncomputable def awayToAffine (n : ℕ) (i : Fin 3) :
    Away (fermatGrading k n) (coord k n i) →+* FermatAffineRing k n i :=
  Away.lift (fermatGrading k n) (chartQuotient k n i)
    (chartQuotient_coord k n i ▸ isUnit_one)

private theorem awayToAffine_mk (n : ℕ) (i : Fin 3) (m : ℕ) (p : MvPolynomial (Fin 3) k)
    (hp : p.IsHomogeneous m) :
    awayToAffine k n i (Away.mk (fermatGrading k n) (fermatCoord_mem_degree_one i) m
      (Ideal.Quotient.mk (fermatIdeal k n) p) (by
        simpa only [Nat.nsmul_eq_mul, mul_one] using
          mk_mem_quotientPiece (homogeneousSubmodule (Fin 3) k) (fermatIdeal k n) hp)) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize (R := k) i p) := by
  unfold awayToAffine
  have hu (h : IsUnit (chartQuotient k n i (coord k n i))) : h.unit = 1 :=
    Units.ext ((IsUnit.unit_spec h).trans (chartQuotient_coord k n i))
  rw [Away.lift_mk, hu, one_pow, inv_one, Units.val_one, mul_one, chartQuotient_mk]

private theorem awayToAffine_surjective (n : ℕ) (i : Fin 3) :
    Function.Surjective (awayToAffine k n i) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨P, hP, hPp⟩ :=
    TauCeti.exists_isHomogeneous_dehomogenize_eq i (le_refl p.totalDegree)
  refine ⟨Away.mk (fermatGrading k n) (fermatCoord_mem_degree_one i) p.totalDegree
    (Ideal.Quotient.mk (fermatIdeal k n) P) ?_, ?_⟩
  · simpa only [Nat.nsmul_eq_mul, mul_one] using
      mk_mem_quotientPiece (homogeneousSubmodule (Fin 3) k) (fermatIdeal k n) hP
  · rw [awayToAffine_mk k n i _ _ hP, hPp]

private theorem coord_ne_zero {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    coord k n i ≠ 0 := by
  have hpoint (x y : k) (hxy : x ^ n + y ^ n = 1) (hi : (![x, y, 1] : Fin 3 → k) i = 1) :
      coord k n i ≠ 0 := by
    intro h
    let e : MvPolynomial (Fin 3) k →ₐ[k] k := aeval ![x, y, 1]
    have hker : fermatIdeal k n ≤ RingHom.ker e.toRingHom := by
      apply Ideal.span_le.mpr
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      exact RingHom.mem_ker.mpr (hp.symm ▸ (aeval_fermatEquation_eq_zero_iff n x y).mpr hxy)
    have hzero := RingHom.mem_ker.mp (hker (Ideal.Quotient.eq_zero_iff_mem.mp h))
    change e (X i) = 0 at hzero
    rw [show e (X i) = 1 by rw [aeval_X, hi]] at hzero
    exact one_ne_zero hzero
  fin_cases i
  · exact hpoint 1 0 (by simp [zero_pow hn.ne']) rfl
  · exact hpoint 0 1 (by simp [zero_pow hn.ne']) rfl
  · exact hpoint 1 0 (by simp [zero_pow hn.ne']) rfl

variable [CharZero k] [IsAlgClosed k]

private theorem fermatEquation_dvd_of_dehomogenize_dvd {n d : ℕ} (hn : 0 < n) (i : Fin 3)
    {p : MvPolynomial (Fin 3) k} (hp : p.IsHomogeneous d)
    (h : fermatAffineEquation k n i ∣ TauCeti.dehomogenize (R := k) i p) :
    fermatEquation k n ∣ p := by
  obtain ⟨w, hw⟩ := h
  let m := w.totalDegree
  obtain ⟨W, hW, hWw⟩ := TauCeti.exists_isHomogeneous_dehomogenize_eq i (le_refl m)
  have hL : (p * X i ^ (n + m)).IsHomogeneous (d + (n + m)) :=
    hp.mul (isHomogeneous_X_pow i (n + m))
  have hR : (fermatEquation k n * W * X i ^ d).IsHomogeneous (d + (n + m)) := by
    rw [add_comm d]
    exact ((fermatEquation_isHomogeneous k n).mul hW).mul (isHomogeneous_X_pow i d)
  have hEq := TauCeti.dehomogenize_injOn i _ hL hR (by
    simp only [map_mul, map_pow, TauCeti.dehomogenize_X, Fin.insertNth_apply_same, one_pow,
      mul_one, hWw]
    exact hw)
  have hprime := (fermatEquation_irreducible (k := k) hn).prime
  have hdvd : fermatEquation k n ∣ p * X i ^ (n + m) :=
    ⟨W * X i ^ d, hEq.trans (mul_assoc _ _ _)⟩
  rcases hprime.dvd_mul.mp hdvd with hP | hX
  · exact hP
  · have hz : coord k n i = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (hprime.dvd_of_dvd_pow hX))
    exact (coord_ne_zero k hn i hz).elim

private theorem awayToAffine_injective {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    Function.Injective (awayToAffine k n i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective (fermatGrading k n) (fermatCoord_mem_degree_one i) x
  have ha' : a ∈ fermatGrading k n d := by simpa only [Nat.nsmul_eq_mul, mul_one] using ha
  obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha'
  rw [awayToAffine_mk k n i _ _ hp] at hx
  have hpd : fermatAffineEquation k n i ∣ TauCeti.dehomogenize (R := k) i p :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have hz : Ideal.Quotient.mk (fermatIdeal k n) p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (fermatEquation_dvd_of_dehomogenize_dvd k hn i hp hpd))
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, hz, val_zero, Localization.mk_zero]

/-- Dehomogenization identifies the coordinate ring of each projective standard open with
the quotient by the corresponding affine Fermat equation. -/
noncomputable def fermatAwayEquivAffine {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    Away (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (X i)) ≃+*
      FermatAffineRing k n i :=
  RingEquiv.ofBijective (awayToAffine k n i) ⟨awayToAffine_injective k hn i,
    awayToAffine_surjective k n i⟩

/-- Each coordinate basic open is the spectrum of the appropriate dehomogenized ring. -/
noncomputable def fermatBasicOpenIsoSpecAffine {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    (Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (X i))).toScheme ≅
      Spec (.of (FermatAffineRing k n i)) :=
  (Proj.basicOpenIsoSpec _ _ (fermatCoord_mem_degree_one i) Nat.one_pos).trans
    (Scheme.Spec.mapIso ((fermatAwayEquivAffine k hn i).toCommRingCatIso.op)).symm

omit [CharZero k] [IsAlgClosed k] in
private theorem awayToAffine_algebraMap (n : ℕ) (i : Fin 3) (c : k) :
    awayToAffine k n i (algebraMap k (Away (fermatGrading k n) (coord k n i)) c) =
      algebraMap k (FermatAffineRing k n i) c := by
  unfold awayToAffine
  change Away.lift _ _ _ (algebraMap (fermatGrading k n 0) _
    (algebraMap k (fermatGrading k n 0) c)) = _
  rw [Away.lift_algebraMap, SetLike.GradeZero.coe_algebraMap]
  change chartQuotient k n i
    (Ideal.Quotient.mk (fermatIdeal k n) (algebraMap k (MvPolynomial (Fin 3) k) c)) = _
  rw [chartQuotient_mk, AlgHom.commutes]
  rfl

private theorem smoothOne_hasRingHomProperty :
    HasRingHomProperty (@SmoothOfRelativeDimension.{u} 1)
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)) := inferInstance

private theorem fermatAway_smoothOne {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    SmoothOfRelativeDimension 1 (Proj.awayι (fermatGrading k n) (coord k n i)
      (fermatCoord_mem_degree_one i) Nat.one_pos ≫ fermatProjectiveToSpec k n) := by
  change SmoothOfRelativeDimension 1 (Proj.awayι (fermatGrading k n) (coord k n i)
    (fermatCoord_mem_degree_one i) Nat.one_pos ≫ (Proj.toSpecZero (fermatGrading k n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (fermatGrading k n 0)))))
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  have := smoothOne_hasRingHomProperty.{u}
  change SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k (Away (fermatGrading k n) (coord k n i)))))
  let e := fermatAwayEquivAffine k hn i
  have hcomp : algebraMap k (Away (fermatGrading k n) (coord k n i)) =
      e.symm.toRingHom.comp (algebraMap k (FermatAffineRing k n i)) := by
    apply RingHom.ext
    intro c
    apply e.injective
    change e (algebraMap k _ c) = e (e.symm (algebraMap k _ c))
    rw [RingEquiv.apply_symm_apply]
    exact awayToAffine_algebraMap k n i c
  have : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := by
    change IsIso (Spec.map e.toCommRingCatIso.inv)
    infer_instance
  rw [hcomp, CommRingCat.ofHom_comp, Spec.map_comp]
  have hs : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k (FermatAffineRing k n i)))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
      (fermatAffine_locally_standardSmoothOne k hn i)
  exact HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension 1) _ _ hs

/-- The projective Fermat scheme is smooth of relative dimension one for every positive exponent
over an algebraically closed field of characteristic zero. -/
theorem fermatProjective_smoothOne {n : ℕ} (hn : 0 < n) :
    SmoothOfRelativeDimension 1 (fermatProjectiveToSpec k n) := by
  let f : Proj (fermatGrading k n) ⟶ Spec (.of k) := fermatProjectiveToSpec k n
  change SmoothOfRelativeDimension 1 f
  have := smoothOne_hasRingHomProperty.{u}
  let U (i : Fin 3) := Proj.basicOpen (fermatGrading k n) (coord k n i)
  let 𝒰 := (Proj (fermatGrading k n)).openCoverOfIsOpenCover U
    (TopologicalSpace.IsOpenCover.mk (fermatProjective_iSup_basicOpen k n))
  have hAffine (i : 𝒰.I₀) : IsAffine (𝒰.X i) :=
    Proj.isAffineOpen_basicOpen (fermatGrading k n) (coord k n i)
      (fermatCoord_mem_degree_one i) Nat.one_pos
  refine HasRingHomProperty.of_source_openCover 𝒰 fun i => ?_
  apply HasRingHomProperty.appTop (@SmoothOfRelativeDimension 1)
  change SmoothOfRelativeDimension 1 ((U i).ι ≫ f)
  let e := Proj.basicOpenIsoSpec (fermatGrading k n) (coord k n i)
    (fermatCoord_mem_degree_one i) Nat.one_pos
  have hi : SmoothOfRelativeDimension 1 (Proj.awayι (fermatGrading k n) (coord k n i)
      (fermatCoord_mem_degree_one i) Nat.one_pos ≫ f) := fermatAway_smoothOne k hn i
  have hcomp := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension 1)
    e.hom _ hi
  change SmoothOfRelativeDimension 1 (e.hom ≫
    Proj.awayι (fermatGrading k n) (coord k n i)
      (fermatCoord_mem_degree_one i) Nat.one_pos ≫ f) at hcomp
  rw [← Proj.basicOpenIsoSpec_inv_ι, Category.assoc] at hcomp
  change SmoothOfRelativeDimension 1 (e.hom ≫ e.inv ≫ (U i).ι ≫ f) at hcomp
  rwa [Iso.hom_inv_id_assoc] at hcomp

end TinyTauDemo
