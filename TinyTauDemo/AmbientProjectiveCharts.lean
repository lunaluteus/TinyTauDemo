/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import Mathlib.RingTheory.MvPolynomial.Ideal
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Standard affine charts of projective space

See `/roadmap/index.qmd#rem-scheme-curves-recall @ ce3fed2d7209ae176aaa251ce23f48d13fd004d5`.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

namespace TinyTauDemo.ProjectiveHypersurface

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] {m : ℕ}

/-- Projective space with its usual total-degree grading. -/
@[expose]
noncomputable def ambient (R : Type u) [CommRing R] (m : ℕ) : Scheme :=
  Proj (homogeneousSubmodule (Fin (m + 1)) R)

/-- Every ambient coordinate variable has degree one. -/
theorem ambientCoord_mem_degree_one (i : Fin (m + 1)) :
    X i ∈ homogeneousSubmodule (Fin (m + 1)) R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X (R := R) i)

private theorem dehomogenize_coord (i : Fin (m + 1)) :
    TauCeti.dehomogenize (R := R) i (X i) = 1 := by
  rw [TauCeti.dehomogenize_X, Fin.insertNth_apply_same]

private noncomputable def ambientAwayToAffine (i : Fin (m + 1)) :
    Away (homogeneousSubmodule (Fin (m + 1)) R) (X i) →+* MvPolynomial (Fin m) R :=
  Away.lift (homogeneousSubmodule (Fin (m + 1)) R)
    (TauCeti.dehomogenize (R := R) i).toRingHom (dehomogenize_coord (R := R) i ▸ isUnit_one)

private theorem ambientAwayToAffine_mk (i : Fin (m + 1)) (e : ℕ)
    (f : MvPolynomial (Fin (m + 1)) R) (hf : f.IsHomogeneous e) :
    ambientAwayToAffine i (Away.mk (homogeneousSubmodule (Fin (m + 1)) R)
      (ambientCoord_mem_degree_one (R := R) i) e f
        (by simpa only [Nat.nsmul_eq_mul, mul_one, mem_homogeneousSubmodule] using hf)) =
      TauCeti.dehomogenize i f := by
  unfold ambientAwayToAffine
  have hu (h : IsUnit ((TauCeti.dehomogenize (R := R) i).toRingHom (X i))) : h.unit = 1 :=
    Units.ext ((IsUnit.unit_spec h).trans (dehomogenize_coord i))
  rw [Away.lift_mk, hu, one_pow, inv_one, Units.val_one, mul_one]
  rfl

private theorem ambientAwayToAffine_bijective (i : Fin (m + 1)) :
    Function.Bijective (ambientAwayToAffine (R := R) i) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨e, a, ha, rfl⟩ := Away.mk_surjective _ (ambientCoord_mem_degree_one (R := R) i) x
    have ha' : a.IsHomogeneous e := by
      simpa only [Nat.nsmul_eq_mul, mul_one, mem_homogeneousSubmodule] using ha
    rw [ambientAwayToAffine_mk i e a ha'] at hx
    have hzero : a = 0 :=
      TauCeti.dehomogenize_injOn i e ha' (isHomogeneous_zero _ _ _) (hx.trans (map_zero _).symm)
    apply val_injective
    rw [Away.val_mk, val_zero, hzero, Localization.mk_zero]
  · intro p
    obtain ⟨f, hf, hfp⟩ :=
      TauCeti.exists_isHomogeneous_dehomogenize_eq i (le_refl p.totalDegree)
    refine ⟨Away.mk _ (ambientCoord_mem_degree_one (R := R) i) p.totalDegree f
      (by simpa only [Nat.nsmul_eq_mul, mul_one, mem_homogeneousSubmodule] using hf), ?_⟩
    rw [ambientAwayToAffine_mk i p.totalDegree f hf, hfp]

/-- The coordinate ring of an ambient projective standard chart is a polynomial ring
in the affine coordinate ratios. -/
noncomputable def ambientAwayEquivAffine (i : Fin (m + 1)) :
    Away (homogeneousSubmodule (Fin (m + 1)) R) (X i) ≃+* MvPolynomial (Fin m) R :=
  RingEquiv.ofBijective (ambientAwayToAffine i) (ambientAwayToAffine_bijective i)

/-- On a homogeneous fraction, the equivalence evaluates the chart coordinate at one. -/
theorem ambientAwayEquivAffine_mk (i : Fin (m + 1)) (e : ℕ)
    (f : MvPolynomial (Fin (m + 1)) R) (hf : f.IsHomogeneous e) :
    ambientAwayEquivAffine i (Away.mk (homogeneousSubmodule (Fin (m + 1)) R)
      (ambientCoord_mem_degree_one (R := R) i) e f
        (by simpa only [Nat.nsmul_eq_mul, mul_one, mem_homogeneousSubmodule] using hf)) =
      TauCeti.dehomogenize i f :=
  ambientAwayToAffine_mk i e f hf

/-- Every homogeneous polynomial of positive degree belongs to the ideal of the variables. -/
theorem mem_idealOfVars_of_isHomogeneous {f : MvPolynomial (Fin (m + 1)) R} {e : ℕ}
    (he : 0 < e) (hf : f.IsHomogeneous e) :
    f ∈ idealOfVars (Fin (m + 1)) R := by
  rw [← pow_one (idealOfVars (Fin (m + 1)) R), mem_pow_idealOfVars_iff]
  intro l hl
  have hldeg : l.degree = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hl)
  rwa [hldeg]

/-- The ambient projective coordinate opens cover projective space. -/
theorem ambient_iSup_basicOpen_eq_top :
    ⨆ i : Fin (m + 1), Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) R) (X i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro e he f hf
  exact mem_idealOfVars_of_isHomogeneous he hf

/-- Each standard coordinate open of projective space is an affine-space spectrum. -/
noncomputable def ambientBasicOpenIsoSpecAffine (i : Fin (m + 1)) :
    (Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) R) (X i)).toScheme ≅
      Spec (.of (MvPolynomial (Fin m) R)) :=
  (Proj.basicOpenIsoSpec _ _ (ambientCoord_mem_degree_one (R := R) i) Nat.one_pos).trans
    (Scheme.Spec.mapIso (ambientAwayEquivAffine (R := R) i).toCommRingCatIso.op).symm

/-- The affine-space chart map into the ambient projective space. -/
noncomputable def ambientAffineChart (i : Fin (m + 1)) :
    Spec (.of (MvPolynomial (Fin m) R)) ⟶ Proj (homogeneousSubmodule (Fin (m + 1)) R) :=
  (ambientBasicOpenIsoSpecAffine i).inv ≫
    (Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) R) (X i)).ι

instance (i : Fin (m + 1)) : IsOpenImmersion (ambientAffineChart (R := R) i) := by
  unfold ambientAffineChart
  exact IsOpenImmersion.comp _ _

/-- The affine-space chart is the open on which its homogeneous coordinate is invertible. -/
theorem ambientAffineChart_opensRange (i : Fin (m + 1)) :
    (ambientAffineChart (R := R) i).opensRange =
      Proj.basicOpen (homogeneousSubmodule (Fin (m + 1)) R) (X i) := by
  unfold ambientAffineChart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- The structure morphism of the ambient projective space. -/
noncomputable def ambientToSpec (R : Type u) [CommRing R] (m : ℕ) :
    Proj (homogeneousSubmodule (Fin (m + 1)) R) ⟶ Spec (.of R) :=
  Proj.toSpecZero (homogeneousSubmodule (Fin (m + 1)) R) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule (Fin (m + 1)) R 0)))

private theorem ambientAwayEquivAffine_algebraMap (i : Fin (m + 1)) (c : R) :
    ambientAwayEquivAffine i
      (algebraMap R (Away (homogeneousSubmodule (Fin (m + 1)) R) (X i)) c) =
      algebraMap R (MvPolynomial (Fin m) R) c := by
  change ambientAwayToAffine i
    (algebraMap (homogeneousSubmodule (Fin (m + 1)) R 0) _
      (algebraMap R (homogeneousSubmodule (Fin (m + 1)) R 0) c)) = _
  unfold ambientAwayToAffine
  rw [Away.lift_algebraMap, SetLike.GradeZero.coe_algebraMap]
  exact AlgHom.commutes _ c

/-- An ambient affine chart carries its usual structure morphism over the coefficients. -/
theorem ambientAffineChart_comp_toSpec (i : Fin (m + 1)) :
    ambientAffineChart (R := R) i ≫ ambientToSpec R m =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin m) R))) := by
  let 𝒜 : ℕ → Submodule R (MvPolynomial (Fin (m + 1)) R) :=
    homogeneousSubmodule (Fin (m + 1)) R
  change (Spec.map (CommRingCat.ofHom (ambientAwayEquivAffine (R := R) i).toRingHom) ≫
    Proj.awayι 𝒜 (X i) (ambientCoord_mem_degree_one i) Nat.one_pos) ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) = _
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact ambientAwayEquivAffine_algebraMap i c

end TinyTauDemo.ProjectiveHypersurface
