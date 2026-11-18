/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatProjective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import TinyTauDemo.ProjectiveHypersurface
import Mathlib.RingTheory.AdjoinRoot

/-!
# Flatness of the Fermat scheme over the integers

Each of the three standard charts is presented by a monic polynomial over
an affine line. The chart rings are therefore flat over the integers.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `9e67cd30d8cddde6c85f771621ddad4efe1defa0`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

namespace TinyTauDemo

private theorem fermatChartEquation_monic {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    ((MvPolynomial.finSuccEquiv ℤ 1)
      (TauCeti.dehomogenize (R := ℤ) i (fermatEquation ℤ n))).Monic := by
  let e := MvPolynomial.finSuccEquiv ℤ 1
  let B := MvPolynomial (Fin 1) ℤ
  have h0 : e (X (0 : Fin 2)) = (Polynomial.X : Polynomial B) :=
    MvPolynomial.finSuccEquiv_X_zero
  have h1 : e (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := ℤ) (j := (0 : Fin 1))
  have hmonic (a b : B) : (Polynomial.X ^ n + Polynomial.C a - Polynomial.C b).Monic := by
    rw [add_sub_assoc, ← map_sub]
    exact Polynomial.monic_X_pow_add_C _ hn.ne'
  have hdiag (j : Fin 3) : TauCeti.dehomogenize (R := ℤ) j (X j) = 1 := by simp
  have hoff (j : Fin 3) (r : Fin 2) :
      TauCeti.dehomogenize (R := ℤ) j (X (j.succAbove r)) = X r := by simp
  change (e (TauCeti.dehomogenize (R := ℤ) i (fermatEquation ℤ n))).Monic
  simp only [fermatEquation_def, map_sub, map_add, map_pow]
  let H (j : Fin 3) := (e (TauCeti.dehomogenize (R := ℤ) j (X 0)) ^ n +
    e (TauCeti.dehomogenize (R := ℤ) j (X 1)) ^ n -
      e (TauCeti.dehomogenize (R := ℤ) j (X 2)) ^ n).Monic
  change H i
  have hcase0 : H 0 := by
    dsimp only [H]
    have h01 : TauCeti.dehomogenize (R := ℤ) (0 : Fin 3) (X 1) = X 0 := hoff 0 0
    have h02 : TauCeti.dehomogenize (R := ℤ) (0 : Fin 3) (X 2) = X 1 := hoff 0 1
    rw [hdiag 0, h01, h02, map_one, one_pow, h0, h1, add_comm, ← map_pow Polynomial.C]
    simpa only [map_one] using hmonic 1 (X 0 ^ n)
  have hcase1 : H 1 := by
    dsimp only [H]
    have h10 : TauCeti.dehomogenize (R := ℤ) (1 : Fin 3) (X 0) = X 0 := hoff 1 0
    have h12 : TauCeti.dehomogenize (R := ℤ) (1 : Fin 3) (X 2) = X 1 := hoff 1 1
    rw [h10, hdiag 1, h12, map_one, one_pow, h0, h1, ← map_pow Polynomial.C]
    simpa only [map_one] using hmonic 1 (X 0 ^ n)
  have hcase2 : H 2 := by
    dsimp only [H]
    have h20 : TauCeti.dehomogenize (R := ℤ) (2 : Fin 3) (X 0) = X 0 := hoff 2 0
    have h21 : TauCeti.dehomogenize (R := ℤ) (2 : Fin 3) (X 1) = X 1 := hoff 2 1
    rw [h20, h21, hdiag 2, map_one, one_pow, h0, h1, ← map_pow Polynomial.C]
    simpa only [map_one] using hmonic (X 0 ^ n) 1
  fin_cases i
  exacts [hcase0, hcase1, hcase2]

private theorem fermatChartRing_flat {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    Module.Flat ℤ (ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i) := by
  let e := MvPolynomial.finSuccEquiv ℤ 1
  let F := TauCeti.dehomogenize (R := ℤ) i (fermatEquation ℤ n)
  let B := MvPolynomial (Fin 1) ℤ
  let Q := Polynomial B ⧸ Ideal.span {e F}
  let e' : ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i ≃ₐ[ℤ] Q :=
    Ideal.quotientEquivAlg _ _ e (by
      rw [Ideal.map_span, Set.image_singleton]
      rfl)
  have : Module.Free B Q := (fermatChartEquation_monic hn i).free_quotient
  have : Module.Flat ℤ Q := Module.Flat.trans ℤ B Q
  exact Module.Flat.of_linearEquiv e'.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The positive-degree integral Fermat scheme is flat over the integer spectrum. -/
theorem fermatProjectiveToSpec_int_flat {n : ℕ} (hn : 0 < n) :
    Flat (fermatProjectiveToSpec ℤ n) := by
  let F := fermatEquation_isHomogeneous ℤ n
  let f := ProjectiveHypersurface.toSpec F
  let U := fun i : Fin 3 ↦ Proj.basicOpen (ProjectiveHypersurface.grading F)
    (ProjectiveHypersurface.coord (fermatEquation ℤ n) i)
  change Flat f
  have hloc : IsZariskiLocalAtSource @Flat :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ RingHom.Flat inferInstance
  apply hloc.of_iSup_eq_top U (ProjectiveHypersurface.iSup_basicOpen_eq_top F)
  intro i
  have hflat : Flat (ProjectiveHypersurface.affineChart F i ≫ f) := by
    dsimp only [f]
    rw [ProjectiveHypersurface.affineChart_comp_toSpec, HasRingHomProperty.Spec_iff (P := @Flat),
      CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    exact fermatChartRing_flat hn i
  have hfac : (U i).ι ≫ f =
      (ProjectiveHypersurface.basicOpenIsoSpec F i).hom ≫
        (ProjectiveHypersurface.affineChart F i ≫ f) := by
    rw [← Category.assoc, ProjectiveHypersurface.basicOpenIsoSpec_hom_affineChart]
  rw [hfac]
  infer_instance

end TinyTauDemo
