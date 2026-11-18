/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatProjective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TinyTauDemo.AlgebraicGeometry.Projective.ProjectiveHypersurface
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Group.Int.Units
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.Algebra.Ring.Int.Field
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Flatness and dimension of the Fermat scheme over the integers

Each of the three standard charts is presented by a monic polynomial over
an affine line. Each chart is flat over the integers and has Krull dimension two.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `027c4b61e59169b60bcae3dd1dcdf45fdd82d1f4`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

namespace TinyTauDemo

private noncomputable abbrev fermatChartPolynomial (n : ℕ) (i : Fin 3) :
    Polynomial (MvPolynomial (Fin 1) ℤ) :=
  (MvPolynomial.finSuccEquiv ℤ 1) (TauCeti.dehomogenize (R := ℤ) i (fermatEquation ℤ n))

private theorem fermatChartEquation_eq_X_pow_add_C (n : ℕ) (i : Fin 3) :
    ∃ a : MvPolynomial (Fin 1) ℤ,
      fermatChartPolynomial n i = Polynomial.X ^ n + Polynomial.C a := by
  let e := MvPolynomial.finSuccEquiv ℤ 1
  let B := MvPolynomial (Fin 1) ℤ
  have h0 : e (X (0 : Fin 2)) = (Polynomial.X : Polynomial B) :=
    MvPolynomial.finSuccEquiv_X_zero
  have h1 : e (X (1 : Fin 2)) = Polynomial.C (X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := ℤ) (j := (0 : Fin 1))
  have hpoly (a b : B) : ∃ c : B,
      Polynomial.X ^ n + Polynomial.C a - Polynomial.C b = Polynomial.X ^ n + Polynomial.C c :=
    ⟨a - b, by rw [add_sub_assoc, map_sub]⟩
  have hdiag (j : Fin 3) : TauCeti.dehomogenize (R := ℤ) j (X j) = 1 := by simp
  have hoff (j : Fin 3) (r : Fin 2) :
      TauCeti.dehomogenize (R := ℤ) j (X (j.succAbove r)) = X r := by simp
  simp only [fermatChartPolynomial, fermatEquation_def, map_sub, map_add, map_pow]
  let H (j : Fin 3) := ∃ a : B, e (TauCeti.dehomogenize (R := ℤ) j (X 0)) ^ n +
    e (TauCeti.dehomogenize (R := ℤ) j (X 1)) ^ n -
      e (TauCeti.dehomogenize (R := ℤ) j (X 2)) ^ n = Polynomial.X ^ n + Polynomial.C a
  change H i
  have hcase0 : H 0 := by
    dsimp only [H]
    have h01 : TauCeti.dehomogenize (R := ℤ) (0 : Fin 3) (X 1) = X 0 := hoff 0 0
    have h02 : TauCeti.dehomogenize (R := ℤ) (0 : Fin 3) (X 2) = X 1 := hoff 0 1
    rw [hdiag 0, h01, h02, map_one, one_pow, h0, h1, add_comm, ← map_pow Polynomial.C]
    simpa only [map_one] using hpoly 1 (X 0 ^ n)
  have hcase1 : H 1 := by
    dsimp only [H]
    have h10 : TauCeti.dehomogenize (R := ℤ) (1 : Fin 3) (X 0) = X 0 := hoff 1 0
    have h12 : TauCeti.dehomogenize (R := ℤ) (1 : Fin 3) (X 2) = X 1 := hoff 1 1
    rw [h10, hdiag 1, h12, map_one, one_pow, h0, h1, ← map_pow Polynomial.C]
    simpa only [map_one] using hpoly 1 (X 0 ^ n)
  have hcase2 : H 2 := by
    dsimp only [H]
    have h20 : TauCeti.dehomogenize (R := ℤ) (2 : Fin 3) (X 0) = X 0 := hoff 2 0
    have h21 : TauCeti.dehomogenize (R := ℤ) (2 : Fin 3) (X 1) = X 1 := hoff 2 1
    rw [h20, h21, hdiag 2, map_one, one_pow, h0, h1, ← map_pow Polynomial.C]
    simpa only [map_one] using hpoly (X 0 ^ n) 1
  fin_cases i
  exacts [hcase0, hcase1, hcase2]

private theorem fermatChartEquation_monic {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    (fermatChartPolynomial n i).Monic := by
  obtain ⟨a, ha⟩ := fermatChartEquation_eq_X_pow_add_C n i
  rw [ha]
  exact Polynomial.monic_X_pow_add_C _ hn.ne'

private noncomputable def fermatChartRingEquiv (n : ℕ) (i : Fin 3) :
    ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i ≃ₐ[ℤ]
      AdjoinRoot (fermatChartPolynomial n i) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.finSuccEquiv ℤ 1) (by
    rw [Ideal.map_span, Set.image_singleton]
    rfl)

private theorem fermatChartRing_flat {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    Module.Flat ℤ (ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i) := by
  let B := MvPolynomial (Fin 1) ℤ
  let Q := AdjoinRoot (fermatChartPolynomial n i)
  have : Module.Free B Q := (fermatChartEquation_monic hn i).free_quotient
  have : Module.Flat ℤ Q := Module.Flat.trans ℤ B Q
  exact Module.Flat.of_linearEquiv (fermatChartRingEquiv n i).toLinearEquiv

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

/-- The coordinate ring of each standard chart of the integer Fermat model has dimension two. -/
theorem fermatChartRing_int_krullDim {n : ℕ} (hn : 0 < n) (i : Fin 3) :
    ringKrullDim (ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i) = 2 := by
  let B := MvPolynomial (Fin 1) ℤ
  let g : Polynomial B := fermatChartPolynomial n i
  have hmonic : g.Monic := fermatChartEquation_monic hn i
  have hdeg : 0 < g.degree := by
    obtain ⟨a, ha⟩ := fermatChartEquation_eq_X_pow_add_C n i
    change g = Polynomial.X ^ n + Polynomial.C a at ha
    rw [ha, Polynomial.degree_X_pow_add_C hn]
    exact_mod_cast hn
  have : Algebra.IsIntegral B (AdjoinRoot g) := AdjoinRoot.isIntegral_of_monic hmonic
  have : FaithfulSMul B (AdjoinRoot g) := AdjoinRoot.faithfulSMul_of_monic_of_degree_pos hmonic hdeg
  rw [ringKrullDim_eq_of_ringEquiv (fermatChartRingEquiv n i).toRingEquiv,
    TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := B)]
  dsimp only [B]
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  simp [one_add_one_eq_two]

/-- The projective Fermat scheme over the integers has Krull dimension two. -/
theorem fermatProjective_int_krullDim {n : ℕ} (hn : 0 < n) :
    topologicalKrullDim (fermatProjective ℤ n) = 2 := by
  let F := fermatEquation_isHomogeneous ℤ n
  let U := fun i : Fin 3 ↦ Proj.basicOpen (ProjectiveHypersurface.grading F)
    (ProjectiveHypersurface.coord (fermatEquation ℤ n) i)
  change topologicalKrullDim (ProjectiveHypersurface.scheme F) = 2
  have hcover (x : ProjectiveHypersurface.scheme F) :
      ∃ i, x ∈ Set.range (ProjectiveHypersurface.affineChart F i) := by
    have hx : x ∈ iSup U := by
      rw [show iSup U = ⊤ from ProjectiveHypersurface.iSup_basicOpen_eq_top F]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨i, (ProjectiveHypersurface.basicOpenIsoSpec F i).hom ⟨x, hi⟩, ?_⟩
    change ((ProjectiveHypersurface.basicOpenIsoSpec F i).hom ≫
      ProjectiveHypersurface.affineChart F i) ⟨x, hi⟩ = x
    rw [ProjectiveHypersurface.basicOpenIsoSpec_hom_affineChart]
    rfl
  rw [TauCeti.topologicalKrullDim_eq_iSup_of_isOpenEmbedding
    (fun i ↦ ProjectiveHypersurface.affineChart F i)
    (fun i ↦ (ProjectiveHypersurface.affineChart F i).isOpenEmbedding) hcover]
  have hdim (i : Fin 3) :
      topologicalKrullDim (Spec (.of (ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i))) =
        2 := by
    rw [show topologicalKrullDim
        (Spec (.of (ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i))) =
        ringKrullDim (ProjectiveHypersurface.ChartRing (fermatEquation ℤ n) i) from
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _]
    exact fermatChartRing_int_krullDim hn i
  simp_rw [hdim, iSup_const]

/-- The integer spectrum has no structure morphism to the spectrum of a field. -/
theorem isEmpty_specInt_to_spec_field (k : Type) [Field k] :
    IsEmpty (Spec (CommRingCat.of ℤ) ⟶ Spec (CommRingCat.of k)) := by
  refine ⟨fun f ↦ ?_⟩
  let g : k →+* ℤ := (Spec.preimage f).hom
  have htwo : (2 : k) ≠ 0 := by
    intro h
    have hg := congrArg g h
    exact (by decide : (2 : ℤ) ≠ 0) (by simpa only [map_ofNat, map_zero] using hg)
  have hu : IsUnit (g 2) := (isUnit_iff_ne_zero.mpr htwo).map g
  rw [map_ofNat] at hu
  rw [Int.isUnit_iff] at hu
  norm_num at hu

end TinyTauDemo
