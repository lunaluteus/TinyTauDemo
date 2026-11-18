/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Curves.ProjectiveLineCharts
public import TinyTauDemo.AlgebraicGeometry.Projective.ProjectiveHypersurface
public import TinyTauDemo.AlgebraicGeometry.Projective.InfinityCoordinates
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Coordinate morphisms to a projective hypersurface

The coordinate map generalizes the construction for Fermat tuples.
See `/roadmap/index.qmd#rem-scheme-curves-recall` @ `659046d7f13ad754bd0e36712b5fe02840fd1035`.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

namespace TinyTauDemo.ProjectiveHypersurface

universe u

variable {k : Type u} [CommRing k] {m d : ℕ} {F : MvPolynomial (Fin (m + 1)) k}

section SourceRing

variable {B : Type u} [CommRing B] [Algebra k B]

/-- Evaluation of the homogeneous coordinate ring at a tuple satisfying its equation. -/
noncomputable def coordinateEval (p : Fin (m + 1) → B) (hP : aeval p F = 0) :
    CoordinateRing F →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ (aeval p) (by
    intro f hf
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [map_mul, hP, zero_mul])

/-- Evaluation of the class of a polynomial is evaluation of the polynomial. -/
@[simp]
theorem coordinateEval_mk (p : Fin (m + 1) → B) (hP : aeval p F = 0)
    (g : MvPolynomial (Fin (m + 1)) k) :
    coordinateEval p hP (Ideal.Quotient.mk _ g) = aeval p g := by
  rfl

variable (hF : F.IsHomogeneous d)

private theorem coordinateEval_map_irrelevant (p : Fin (m + 1) → B) (hP : aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    (HomogeneousIdeal.irrelevant (grading hF)).toIdeal.map
        (coordinateEval p hP).toRingHom = ⊤ := by
  apply top_unique
  rw [← hp, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hh := Ideal.mem_map_of_mem (coordinateEval p hP).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading hF) one_pos (coord_mem_degree_one hF i))
  change coordinateEval p hP (Ideal.Quotient.mk _ (X i)) ∈ _ at hh
  rw [coordinateEval_mk, aeval_X] at hh
  exact hh

private noncomputable def globalCoordinates (p : Fin (m + 1) → B) (hP : aeval p F = 0) :
    CoordinateRing F →+* Γ(Spec (.of B), ⊤) :=
  (Scheme.ΓSpecIso (.of B)).inv.hom.comp (coordinateEval p hP).toRingHom

private theorem globalCoordinates_map_irrelevant (p : Fin (m + 1) → B) (hP : aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    (HomogeneousIdeal.irrelevant (grading hF)).toIdeal.map (globalCoordinates p hP) = ⊤ := by
  rw [globalCoordinates, ← Ideal.map_map, coordinateEval_map_irrelevant hF p hP hp,
    Ideal.map_top]

/-- Coordinates satisfying the homogeneous equation and generating the unit ideal define
a morphism to the projective hypersurface. -/
noncomputable def specMap (p : Fin (m + 1) → B) (hP : aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) : Spec (.of B) ⟶ scheme hF :=
  Proj.fromOfGlobalSections (grading hF) (globalCoordinates p hP)
    (globalCoordinates_map_irrelevant hF p hP hp)

/-- The coordinate morphism respects structure maps to the coefficient ring. -/
@[reassoc]
theorem specMap_toSpec (p : Fin (m + 1) → B) (hP : aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    specMap hF p hP hp ≫ toSpec hF = Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  change Proj.fromOfGlobalSections (grading hF) (globalCoordinates p hP) _ ≫
    Proj.toSpecZero (grading hF) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (grading hF 0))) = _
  rw [Proj.fromOfGlobalSections_toSpecZero_assoc]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcomp : (globalCoordinates p hP).comp
      ((algebraMap (grading hF 0) (CoordinateRing F)).comp (algebraMap k (grading hF 0))) =
      (Scheme.ΓSpecIso (.of B)).inv.hom.comp (algebraMap k B) := by
    ext r
    exact congrArg (Scheme.ΓSpecIso (.of B)).inv (AlgHom.commutes _ r)
  rw [RingHom.comp_assoc, hcomp, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    CommRingCat.ofHom_hom, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- If a homogeneous coordinate is a unit, the morphism factors through its coordinate chart. -/
theorem specMap_eq_awayLift
    (p : Fin (m + 1) → B) (hP : aeval p F = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (i : Fin (m + 1)) (hi : IsUnit (p i)) :
    specMap hF p hP hp = Spec.map (CommRingCat.ofHom
        (Away.lift (grading hF) (coordinateEval p hP).toRingHom
          (f := coord F i) (by
            change IsUnit (coordinateEval p hP (Ideal.Quotient.mk _ (X i)))
            rwa [coordinateEval_mk, aeval_X]))) ≫
      Proj.awayι (grading hF) (coord F i) (coord_mem_degree_one hF i) one_pos := by
  exact Proj.fromOfGlobalSections_Spec_eq_awayLift _ (coordinateEval_map_irrelevant hF p hP hp)
    one_pos (coord_mem_degree_one hF i) _

/-- Pulling back a coordinate chart gives the basic open of the coordinate's value. -/
theorem specMap_preimage_basicOpen (p : Fin (m + 1) → B) (hP : aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) (i : Fin (m + 1)) :
    specMap hF p hP hp ⁻¹ᵁ Proj.basicOpen (grading hF) (coord F i) =
      (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv (p i)) := by
  change Proj.fromOfGlobalSections (grading hF) (globalCoordinates p hP) _ ⁻¹ᵁ
    Proj.basicOpen (grading hF) (coord F i) = _
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (coord_mem_degree_one hF i),
    globalCoordinates, RingHom.comp_apply]
  change (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv
    (coordinateEval p hP (Ideal.Quotient.mk _ (X i)))) = _
  rw [coordinateEval_mk, aeval_X]

/-- Rescaling a homogeneous coordinate tuple by a common unit preserves its morphism. -/
theorem specMap_eq_of_unit_rescale (p q : Fin (m + 1) → B)
    (hP : aeval p F = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hQ : aeval q F = 0) (hq : Ideal.span (Set.range q) = ⊤)
    (c : Bˣ) (hc : ∀ i, q i = (c : B) * p i) :
    specMap hF p hP hp = specMap hF q hQ hq := by
  let γ := Scheme.ΓSpecIso (.of B)
  let cΓ := c.map γ.inv.hom.toMonoidHom
  unfold specMap
  symm
  apply TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling _ _ _ cΓ
  intro e a ha
  obtain ⟨g, hg, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp
    (show a ∈ TauCeti.GradedAlgebra.quotientPiece _ _ _ from ha)
  have hq' : q = (c : B) • p := funext hc
  have hg' : g.IsHomogeneous e := hg
  change γ.inv (coordinateEval q hQ (Ideal.Quotient.mk _ g)) =
    (cΓ : Γ(Spec (.of B), ⊤)) ^ e *
      γ.inv (coordinateEval p hP (Ideal.Quotient.mk _ g))
  simp only [coordinateEval_mk, hq', hg'.aeval_smul, smul_eq_mul, Units.coe_map, cΓ]
  change γ.inv.hom ((c : B) ^ e * aeval p g) = γ.inv.hom (c : B) ^ e * γ.inv.hom (aeval p g)
  rw [map_mul, map_pow]

/-- Pulling the coordinate morphism along a map of algebras evaluates all its coordinates. -/
theorem specMap_comp_SpecMap {C : Type u} [CommRing C] [Algebra k C] (φ : B →ₐ[k] C)
    (p : Fin (m + 1) → B) (hP : aeval p F = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hQ : aeval (fun i ↦ φ (p i)) F = 0) (hq : Ideal.span (Set.range fun i ↦ φ (p i)) = ⊤) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specMap hF p hP hp =
      specMap hF (fun i ↦ φ (p i)) hQ hq := by
  let f := CommRingCat.ofHom φ.toRingHom
  change Spec.map f ≫ Proj.fromOfGlobalSections (grading hF) (globalCoordinates p hP) _ =
    Proj.fromOfGlobalSections (grading hF) (globalCoordinates (fun i ↦ φ (p i)) hQ) _
  rw [Proj.fromOfGlobalSections_naturality]
  congr 1
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (Spec.map f).appTop ((Scheme.ΓSpecIso (.of B)).inv
    (coordinateEval p hP (Ideal.Quotient.mk _ a))) =
    (Scheme.ΓSpecIso (.of C)).inv (coordinateEval (fun i ↦ φ (p i)) hQ (Ideal.Quotient.mk _ a))
  rw [coordinateEval_mk, coordinateEval_mk, ← MvPolynomial.comp_aeval_apply (f := p) φ a]
  have hγ := Scheme.ΓSpecIso_inv_naturality f
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hγ.symm) _

end SourceRing

section SourceField

variable {L : Type u} [Field L] [Algebra k L] (hF : F.IsHomogeneous d)

private theorem insertNth_normalized_eq_smul (p : Fin (m + 1) → L) (i : Fin (m + 1))
    (hi : p i ≠ 0) :
    i.insertNth 1 (fun j ↦ p (i.succAbove j) / p i) = (p i)⁻¹ • p := by
  ext j
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) j <;> simp [hi, div_eq_mul_inv, mul_comm]

/-- A tuple with nonzero coordinate i gives a point of the corresponding dehomogenized equation
by dividing its other coordinates by that coordinate. -/
noncomputable def normalizedChartEval (p : Fin (m + 1) → L) (hP : aeval p F = 0)
    (i : Fin (m + 1)) (hi : p i ≠ 0) :
    ChartRing F i →ₐ[k] L :=
  Ideal.Quotient.liftₐ _ (aeval fun j ↦ p (i.succAbove j) / p i) (by
    intro g hg
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hg
    rw [map_mul, TauCeti.aeval_dehomogenize, insertNth_normalized_eq_smul p i hi,
      hF.aeval_smul, hP, smul_zero, zero_mul])

/-- Evaluation on an affine equation class uses the normalized coordinates. -/
@[simp]
theorem normalizedChartEval_mk (p : Fin (m + 1) → L) (hP : aeval p F = 0)
    (i : Fin (m + 1)) (hi : p i ≠ 0) (g : MvPolynomial (Fin m) k) :
    normalizedChartEval hF p hP i hi (Ideal.Quotient.mk _ g) =
      aeval (fun j ↦ p (i.succAbove j) / p i) g := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A projective coordinate morphism over a field is given on a nonzero coordinate chart
by evaluation at the normalized coordinates. -/
theorem specMap_eq_affineChart (p : Fin (m + 1) → L) (hP : aeval p F = 0)
    (hp : Ideal.span (Set.range p) = ⊤) (i : Fin (m + 1)) (hi : p i ≠ 0) :
    specMap hF p hP hp =
      Spec.map (CommRingCat.ofHom (normalizedChartEval hF p hP i hi).toRingHom) ≫
        affineChart hF i := by
  rw [specMap_eq_awayLift hF p hP hp i (isUnit_iff_ne_zero.mpr hi), affineChart_eq_awayι,
    ← Category.assoc, ← Spec.map_comp, cancel_mono, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro a
  obtain ⟨e, b, hb, rfl⟩ := Away.mk_surjective (grading hF) (coord_mem_degree_one hF i) a
  have hb' : b ∈ grading hF e := by simpa only [Nat.nsmul_eq_mul, mul_one] using hb
  obtain ⟨g, hg, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp
    (show b ∈ TauCeti.GradedAlgebra.quotientPiece _ _ _ from hb')
  change _ = normalizedChartEval hF p hP i hi
    (awayEquivChart hF i (Away.mk (grading hF) (coord_mem_degree_one hF i) e
      (Ideal.Quotient.mk _ g) hb))
  have hg' : g.IsHomogeneous e := hg
  rw [awayEquivChart_mk hF i e g hg, normalizedChartEval_mk,
    Away.lift_mk, TauCeti.aeval_dehomogenize, insertNth_normalized_eq_smul p i hi,
    hg'.aeval_smul, smul_eq_mul]
  change coordinateEval p hP (Ideal.Quotient.mk _ g) * _ = _
  rw [coordinateEval_mk]
  have hu (u : IsUnit (coordinateEval p hP (coord F i))) :
      (↑u.unit : L) = p i := by
    rw [u.unit_spec]
    exact (coordinateEval_mk p hP (X i)).trans (aeval_X p i)
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hu, inv_pow, mul_comm]

end SourceField

end TinyTauDemo.ProjectiveHypersurface

namespace TinyTauDemo.ProjectiveHypersurface

open Polynomial

universe u

variable {k : Type u} [Field k] {m d : ℕ} {F : MvPolynomial (Fin (m + 1)) k}
  (hF : F.IsHomogeneous d)

section Overlap

variable {L : Type u} [Field L] [Algebra k L]

private theorem evaluated_coordinates_vanish (φ : k[X] →ₐ[k] L) (p : Fin (m + 1) → k[X])
    (hP : MvPolynomial.aeval p F = 0) :
    MvPolynomial.aeval (fun i ↦ φ (p i)) F = 0 := by
  rw [← MvPolynomial.comp_aeval_apply, hP, map_zero]

private theorem evaluated_coordinates_span (φ : k[X] →ₐ[k] L) (p : Fin (m + 1) → k[X])
    (hp : Ideal.span (Set.range p) = ⊤) :
    Ideal.span (Set.range fun i ↦ φ (p i)) = ⊤ := by
  change Ideal.span (Set.range (φ ∘ p)) = ⊤
  rw [Set.range_comp, ← Ideal.map_span, hp, Ideal.map_top]

/-- Reflecting the coordinate polynomials preserves the actual projective morphism
over the overlap, where the parameter in the other chart is the reciprocal. -/
theorem specMap_reflect_overlap (p : Fin (m + 1) → k[X]) {M : ℕ}
    (hP : MvPolynomial.aeval p F = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hmax : ∃ i, p i ≠ 0 ∧ (p i).natDegree = M)
    {t : L} (ht : t ≠ 0) :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval t⁻¹).toRingHom) ≫
        specMap hF (fun i ↦ (p i).reflect M)
          (aeval_reflect_eq_zero_of_isHomogeneous p hF hdeg hP)
          (span_range_reflect_eq_top p hp hdeg hmax) =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom) ≫ specMap hF p hP hp := by
  let q := fun i ↦ (p i).reflect M
  let hQ := aeval_reflect_eq_zero_of_isHomogeneous p hF hdeg hP
  let hq := span_range_reflect_eq_top p hp hdeg hmax
  let ψ := Polynomial.aeval (R := k) t
  let ψ' := Polynomial.aeval (R := k) t⁻¹
  let c : Lˣ := Units.mk0 (t⁻¹ ^ M) (pow_ne_zero _ (inv_ne_zero ht))
  change Spec.map (CommRingCat.ofHom ψ'.toRingHom) ≫ specMap hF q hQ hq =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ specMap hF p hP hp
  rw [specMap_comp_SpecMap hF ψ' q hQ hq
      (evaluated_coordinates_vanish ψ' q hQ) (evaluated_coordinates_span ψ' q hq),
    specMap_comp_SpecMap hF ψ p hP hp
      (evaluated_coordinates_vanish ψ p hP) (evaluated_coordinates_span ψ p hp)]
  symm
  apply specMap_eq_of_unit_rescale hF _ _ _ _ _ _ c
  intro i
  let : Invertible t := invertibleOfNonzero ht
  have hi := eval₂_reflect_mul_pow (algebraMap k L) t M (p i) (hdeg i)
  rw [invOf_eq_inv, ← Polynomial.aeval_def, ← Polynomial.aeval_def] at hi
  have htM : t ^ M ≠ 0 := pow_ne_zero _ ht
  have hh := (eq_div_iff htM).mpr hi
  simpa only [q, ψ, ψ', c, Units.val_mk0, inv_pow, div_eq_mul_inv,
    mul_comm (t ^ M)⁻¹] using hh

end Overlap

open TauCeti TauCeti.AlgebraicGeometry

/-- On the infinity chart, a projective extension is the actual morphism defined by
reflecting the coordinates of its affine polynomial tuple at their maximum degree. -/
theorem projectiveLineMap_on_infinity_chart (p : Fin (m + 1) → k[X]) {M : ℕ}
    (hP : MvPolynomial.aeval p F = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hmax : ∃ i, p i ≠ 0 ∧ (p i).natDegree = M)
    (f : projectiveLine k ⟶ scheme hF)
    (hfS : f ≫ toSpec hF = (projectiveLine k ↘ Spec (.of k)))
    (hf : projectiveLinePolynomialChart k 0 ≫ f = specMap hF p hP hp) :
    projectiveLinePolynomialChart k 1 ≫ f =
      specMap hF (fun i ↦ (p i).reflect M)
        (aeval_reflect_eq_zero_of_isHomogeneous p hF hdeg hP)
        (span_range_reflect_eq_top p hp hdeg hmax) := by
  let S := Spec (.of k)
  let Y := scheme hF
  let A := Spec (.of k[X])
  let : Y.Over S := ⟨toSpec hF⟩
  let : A.Over S := ⟨Spec.map (CommRingCat.ofHom (algebraMap k k[X]))⟩
  let : IsProper (Y ↘ S) := inferInstanceAs (IsProper (toSpec hF))
  let q := fun i ↦ (p i).reflect M
  let hQ := aeval_reflect_eq_zero_of_isHomogeneous p hF hdeg hP
  let hq := span_range_reflect_eq_top p hp hdeg hmax
  let : (specMap hF q hQ hq).IsOver S := (Scheme.Hom.isOver_iff S).mpr
    (specMap_toSpec hF q hQ hq)
  let : (projectiveLinePolynomialChart k 1 ≫ f).IsOver S := by
    rw [Scheme.Hom.isOver_iff S]
    change projectiveLinePolynomialChart k 1 ≫ f ≫ toSpec hF = _
    rw [hfS, projectiveLinePolynomialChart_toSpec]
    rfl
  let t : RatFunc k := RatFunc.X
  have ht : t ≠ 0 := RatFunc.X_ne_zero
  have htrans : Transcendental k t⁻¹ := by
    rw [Transcendental, IsAlgebraic.inv_iff]
    exact RatFunc.transcendental_X
  let b := Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := k) t⁻¹).toRingHom)
  let : IsDominant b :=
    ⟨RingHom.denseRange_comap_of_injective _ (transcendental_iff_injective.mp htrans)⟩
  change projectiveLinePolynomialChart k 1 ≫ f = specMap hF q hQ hq
  apply ext_of_isDominant_of_isSeparated' S b
  dsimp only [b]
  rw [← Category.assoc, projectiveLinePolynomialChart_aeval_inv t ht, Category.assoc, hf]
  exact (specMap_reflect_overlap hF p hP hp hdeg hmax ht).symm

end TinyTauDemo.ProjectiveHypersurface
