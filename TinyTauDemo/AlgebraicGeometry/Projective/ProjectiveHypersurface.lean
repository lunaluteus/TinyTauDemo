/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Projective.AmbientProjectiveCharts
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.Finiteness.Quotient
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Standard charts of a projective hypersurface

This generalizes the projective construction and affine chart proofs for
the Fermat equation in `TinyTauDemo.FermatProjective` and `TinyTauDemo.FermatCharts`.
See `/roadmap/index.qmd#rem-scheme-curves-recall @ ce3fed2d7209ae176aaa251ce23f48d13fd004d5`.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial TauCeti.GradedAlgebra

namespace TinyTauDemo.ProjectiveHypersurface

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] {m d : ℕ} {F : MvPolynomial (Fin (m + 1)) R}

/-- The homogeneous equation ring of the hypersurface. -/
abbrev CoordinateRing (F : MvPolynomial (Fin (m + 1)) R) :=
  MvPolynomial (Fin (m + 1)) R ⧸ Ideal.span {F}

variable (hF : F.IsHomogeneous d)

include hF in
/-- The defining principal ideal is homogeneous. -/
theorem ideal_isHomogeneous :
    (Ideal.span {F} : Ideal _).IsHomogeneous (homogeneousSubmodule (Fin (m + 1)) R) := by
  apply Ideal.homogeneous_span
  intro f hf
  rw [Set.mem_singleton_iff] at hf
  exact ⟨d, hf.symm ▸ hF⟩

/-- The grading on the homogeneous equation ring induced by total degree. -/
@[expose]
noncomputable def grading (_ : F.IsHomogeneous d) : ℕ → Submodule R (CoordinateRing F) :=
  quotientPiece (homogeneousSubmodule (Fin (m + 1)) R) (Ideal.span {F})

noncomputable instance : GradedAlgebra (grading hF) :=
  gradedAlgebraQuotientPiece (homogeneousSubmodule (Fin (m + 1)) R) (Ideal.span {F})
    (ideal_isHomogeneous hF)

/-- The residue class of a projective coordinate. -/
noncomputable abbrev coord (F : MvPolynomial (Fin (m + 1)) R) (i : Fin (m + 1)) :
    CoordinateRing F :=
  Ideal.Quotient.mk _ (X i)

/-- The coordinate classes are elements of degree one. -/
theorem coord_mem_degree_one (i : Fin (m + 1)) : coord F i ∈ grading hF 1 :=
  mk_mem_quotientPiece _ _ (isHomogeneous_X (R := R) i)

/-- The projective scheme defined by a homogeneous equation. -/
@[expose]
noncomputable def scheme : Scheme := Proj (grading hF)

/-- The structure morphism of the projective hypersurface. -/
@[expose]
noncomputable def toSpec : scheme hF ⟶ Spec (.of R) :=
  Proj.toSpecZero (grading hF) ≫ Spec.map (CommRingCat.ofHom (algebraMap R _))

private noncomputable def gradedQuotient :
    homogeneousSubmodule (Fin (m + 1)) R →+*ᵍ grading hF where
  toRingHom := Ideal.Quotient.mk _
  map_mem := mk_mem_quotientPiece _ _

private theorem gradedQuotient_surjective : Function.Surjective (gradedQuotient hF) :=
  Ideal.Quotient.mk_surjective

/-- The inclusion of the hypersurface in its ambient projective space. -/
noncomputable def inclusion : scheme hF ⟶ ambient R m :=
  Proj.map (gradedQuotient hF)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (gradedQuotient_surjective hF))

instance : IsClosedImmersion (inclusion hF) :=
  Proj.isClosedImmersion_map _ _ (gradedQuotient_surjective hF)

private theorem gradeZero_algebraMap_surjective :
    Function.Surjective (algebraMap R (grading hF 0)) := by
  rintro ⟨z, hz⟩
  obtain ⟨p, hp, hq⟩ := (mem_quotientPiece_iff _ _).mp hz
  have hp' : p.IsHomogeneous 0 := hp
  have hC : p = C (p.coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp'.totalDegree_le)
  refine ⟨p.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk (Ideal.span {F}) (C (p.coeff 0)) = z
  rw [← hC]
  exact hq

instance : IsProper (toSpec hF) := by
  have : IsScalarTower R (grading hF 0) (CoordinateRing F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType R (CoordinateRing F) := inferInstance
  have : Algebra.FiniteType (grading hF 0) (CoordinateRing F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap R (grading hF 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (gradeZero_algebraMap_surjective hF)
  have h₁ : IsProper (Proj.toSpecZero (grading hF)) := inferInstance
  have h₂ : IsProper (Spec.map (CommRingCat.ofHom (algebraMap R (grading hF 0)))) :=
    inferInstance
  exact MorphismProperty.comp_mem @IsProper _ _ h₁ h₂

/-- The standard opens defined by the coordinate variables cover the hypersurface. -/
theorem iSup_basicOpen_eq_top :
    ⨆ i : Fin (m + 1), Proj.basicOpen (grading hF) (coord F i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi z hz
  obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff _ _).mp hz
  have hpI := mem_idealOfVars_of_isHomogeneous hi hp
  change Ideal.Quotient.mk (Ideal.span {F}) p ∈ Ideal.span
    (Set.range (Ideal.Quotient.mk (Ideal.span {F}) ∘
      (X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) R)))
  rw [Set.range_comp, ← Ideal.map_span]
  exact Ideal.mem_map_of_mem _ hpI

/-- The coordinate ring on the affine chart obtained by normalizing coordinate `i`. -/
noncomputable abbrev ChartRing (F : MvPolynomial (Fin (m + 1)) R) (i : Fin (m + 1)) :=
  MvPolynomial (Fin m) R ⧸ (Ideal.span {TauCeti.dehomogenize i F} : Ideal _)

private noncomputable def chartQuotient (i : Fin (m + 1)) : CoordinateRing F →+* ChartRing F i :=
  Ideal.Quotient.lift (Ideal.span {F})
    ((Ideal.Quotient.mk _).comp (TauCeti.dehomogenize (R := R) i).toRingHom) (by
      intro a ha
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hd : F ∣ a := Ideal.mem_span_singleton.mp ha
      exact Ideal.mem_span_singleton.mpr (map_dvd (TauCeti.dehomogenize (R := R) i) hd))

private theorem chartQuotient_mk (i : Fin (m + 1)) (p : MvPolynomial (Fin (m + 1)) R) :
    chartQuotient (F := F) i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize (R := R) i p) := rfl

private theorem chartQuotient_coord (i : Fin (m + 1)) :
    chartQuotient i (coord F i) = 1 := by
  rw [chartQuotient_mk, TauCeti.dehomogenize_X, Fin.insertNth_apply_same, map_one]

private noncomputable def awayToAffine (i : Fin (m + 1)) :
    Away (grading hF) (coord F i) →+* ChartRing F i :=
  Away.lift (grading hF) (chartQuotient i) (chartQuotient_coord (F := F) i ▸ isUnit_one)

private theorem awayToAffine_mk (i : Fin (m + 1)) (e : ℕ)
    (p : MvPolynomial (Fin (m + 1)) R) (hp : p.IsHomogeneous e) :
    awayToAffine hF i (Away.mk (grading hF) (coord_mem_degree_one hF i) e
      (Ideal.Quotient.mk (Ideal.span {F}) p) (by
        simpa only [Nat.nsmul_eq_mul, mul_one, grading] using
          mk_mem_quotientPiece (homogeneousSubmodule (Fin (m + 1)) R) (Ideal.span {F}) hp)) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize (R := R) i p) := by
  unfold awayToAffine
  have hu (h : IsUnit (chartQuotient i (coord F i))) : h.unit = 1 :=
    Units.ext ((IsUnit.unit_spec h).trans (chartQuotient_coord i))
  rw [Away.lift_mk, hu, one_pow, inv_one, Units.val_one, mul_one, chartQuotient_mk]

private theorem awayToAffine_surjective (i : Fin (m + 1)) :
    Function.Surjective (awayToAffine hF i) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨P, hP, hPp⟩ :=
    TauCeti.exists_isHomogeneous_dehomogenize_eq i (le_refl p.totalDegree)
  refine ⟨Away.mk (grading hF) (coord_mem_degree_one hF i) p.totalDegree
    (Ideal.Quotient.mk _ P) ?_, ?_⟩
  · simpa only [Nat.nsmul_eq_mul, mul_one, grading] using
      mk_mem_quotientPiece (homogeneousSubmodule (Fin (m + 1)) R) (Ideal.span {F}) hP
  · rw [awayToAffine_mk hF i _ _ hP, hPp]

include hF in
private theorem exists_dvd_mul_pow_of_dehomogenize_dvd (i : Fin (m + 1)) {e : ℕ}
    {p : MvPolynomial (Fin (m + 1)) R} (hp : p.IsHomogeneous e)
    (h : TauCeti.dehomogenize i F ∣ TauCeti.dehomogenize i p) :
    ∃ l : ℕ, F ∣ p * X i ^ l := by
  obtain ⟨w, hw⟩ := h
  let s := w.totalDegree
  obtain ⟨W, hW, hWw⟩ := TauCeti.exists_isHomogeneous_dehomogenize_eq i (le_refl s)
  have hL : (p * X i ^ (d + s)).IsHomogeneous (e + (d + s)) :=
    hp.mul (isHomogeneous_X_pow i (d + s))
  have hR : (F * W * X i ^ e).IsHomogeneous (e + (d + s)) := by
    rw [add_comm e]
    exact (hF.mul hW).mul (isHomogeneous_X_pow i e)
  have hEq := TauCeti.dehomogenize_injOn i _ hL hR (by
    simp only [map_mul, map_pow, TauCeti.dehomogenize_X, Fin.insertNth_apply_same, one_pow,
      mul_one, hWw]
    exact hw)
  exact ⟨d + s, W * X i ^ e, hEq.trans (mul_assoc _ _ _)⟩

private theorem awayToAffine_injective (i : Fin (m + 1)) :
    Function.Injective (awayToAffine hF i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨e, a, ha, rfl⟩ := Away.mk_surjective (grading hF) (coord_mem_degree_one hF i) x
  have ha' : a ∈ grading hF e := by simpa only [Nat.nsmul_eq_mul, mul_one, grading] using ha
  obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha'
  rw [awayToAffine_mk hF i _ _ hp] at hx
  have hpd : TauCeti.dehomogenize i F ∣ TauCeti.dehomogenize i p :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  obtain ⟨l, hl⟩ := exists_dvd_mul_pow_of_dehomogenize_dvd hF i hp hpd
  have hz : Ideal.Quotient.mk (Ideal.span {F}) (p * X i ^ l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hl)
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨coord F i ^ l, ⟨l, rfl⟩⟩, ?_⟩
  change (Ideal.Quotient.mk (Ideal.span {F}) (X i)) ^ l *
    Ideal.Quotient.mk (Ideal.span {F}) p = 0
  rw [mul_comm]
  simpa only [map_mul, map_pow] using hz

/-- Dehomogenization identifies the degree-zero localization at a coordinate with
the coordinate ring of the corresponding affine hypersurface. -/
noncomputable def awayEquivChart (i : Fin (m + 1)) :
    Away (grading hF) (coord F i) ≃+* ChartRing F i :=
  RingEquiv.ofBijective (awayToAffine hF i)
    ⟨awayToAffine_injective hF i, awayToAffine_surjective hF i⟩

/-- The chart equivalence sends a homogeneous fraction to its dehomogenized numerator. -/
theorem awayEquivChart_mk (i : Fin (m + 1)) (e : ℕ)
    (p : MvPolynomial (Fin (m + 1)) R) (hp : p.IsHomogeneous e) :
    awayEquivChart hF i (Away.mk (grading hF) (coord_mem_degree_one hF i) e
      (Ideal.Quotient.mk (Ideal.span {F}) p) (by
        simpa only [Nat.nsmul_eq_mul, mul_one, grading] using
          mk_mem_quotientPiece (homogeneousSubmodule (Fin (m + 1)) R) (Ideal.span {F}) hp)) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize (R := R) i p) :=
  awayToAffine_mk hF i e p hp

/-- The standard open of each coordinate is the spectrum of the dehomogenized equation. -/
noncomputable def basicOpenIsoSpec (i : Fin (m + 1)) :
    (Proj.basicOpen (grading hF) (coord F i)).toScheme ≅ Spec (.of (ChartRing F i)) :=
  (Proj.basicOpenIsoSpec _ _ (coord_mem_degree_one hF i) Nat.one_pos).trans
    (Scheme.Spec.mapIso ((awayEquivChart hF i).toCommRingCatIso.op)).symm

private theorem awayToAffine_algebraMap (i : Fin (m + 1)) (c : R) :
    awayToAffine hF i (algebraMap R (Away (grading hF) (coord F i)) c) =
      algebraMap R (ChartRing F i) c := by
  unfold awayToAffine
  change Away.lift _ _ _ (algebraMap (grading hF 0) _
    (algebraMap R (grading hF 0) c)) = _
  rw [Away.lift_algebraMap, SetLike.GradeZero.coe_algebraMap]
  change chartQuotient i (Ideal.Quotient.mk _ (algebraMap R (MvPolynomial (Fin (m + 1)) R) c)) = _
  rw [chartQuotient_mk, AlgHom.commutes]
  rfl

private theorem awayι_comp_toSpec (i : Fin (m + 1)) :
    Proj.awayι (grading hF) (coord F i) (coord_mem_degree_one hF i) Nat.one_pos ≫ toSpec hF =
      Spec.map (CommRingCat.ofHom (algebraMap R (Away (grading hF) (coord F i)))) := by
  change Proj.awayι (grading hF) (coord F i) (coord_mem_degree_one hF i) Nat.one_pos ≫
    (Proj.toSpecZero (grading hF) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (grading hF 0)))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The inclusion of the dehomogenized hypersurface in the projective hypersurface. -/
noncomputable def affineChart (i : Fin (m + 1)) : Spec (.of (ChartRing F i)) ⟶ scheme hF :=
  (basicOpenIsoSpec hF i).inv ≫ (Proj.basicOpen (grading hF) (coord F i)).ι

/-- The affine chart inclusion factors through the homogeneous localization. -/
theorem affineChart_eq_awayι (i : Fin (m + 1)) :
    affineChart hF i =
      Spec.map (CommRingCat.ofHom (awayEquivChart hF i).toRingHom) ≫
        Proj.awayι (grading hF) (coord F i) (coord_mem_degree_one hF i) Nat.one_pos := by
  rfl

/-- Identifying the standard open with its affine equation recovers the open inclusion. -/
theorem basicOpenIsoSpec_hom_affineChart (i : Fin (m + 1)) :
    (basicOpenIsoSpec hF i).hom ≫ affineChart hF i =
      (Proj.basicOpen (grading hF) (coord F i)).ι := by
  let e := basicOpenIsoSpec hF i
  let j : (Proj.basicOpen (grading hF) (coord F i)).toScheme ⟶ scheme hF :=
    (Proj.basicOpen (grading hF) (coord F i)).ι
  change e.hom ≫ e.inv ≫ j = j
  exact Iso.hom_inv_id_assoc e j

instance (i : Fin (m + 1)) : IsOpenImmersion (affineChart hF i) := by
  change IsOpenImmersion ((basicOpenIsoSpec hF i).inv ≫
    (Proj.basicOpen (grading hF) (coord F i)).ι)
  exact IsOpenImmersion.comp _ _

/-- The affine chart map commutes with the structure morphisms to the coefficient ring. -/
theorem affineChart_comp_toSpec (i : Fin (m + 1)) :
    affineChart hF i ≫ toSpec hF =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing F i))) := by
  let f : Proj (grading hF) ⟶ Spec (.of R) := toSpec hF
  change (Spec.map (CommRingCat.ofHom (awayEquivChart hF i).toRingHom) ≫
    Proj.awayι (grading hF) (coord F i) (coord_mem_degree_one hF i) Nat.one_pos) ≫ f = _
  have hAway : Proj.awayι (grading hF) (coord F i) (coord_mem_degree_one hF i) Nat.one_pos ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (Away (grading hF) (coord F i)))) :=
    awayι_comp_toSpec hF i
  rw [Category.assoc, hAway, ← Spec.map_comp]
  congr 1
  ext c
  exact awayToAffine_algebraMap hF i c

end TinyTauDemo.ProjectiveHypersurface
