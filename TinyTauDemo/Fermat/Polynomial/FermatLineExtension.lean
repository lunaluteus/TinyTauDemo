/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Polynomial.FermatPolynomialMap
import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.RingTheory.Spectrum.Prime.Topology
import TauCeti.Topology.KrullDimension
import TinyTauDemo.AlgebraicGeometry.Curves.DenseOpenExtension

/-!
# Extending polynomial Fermat coordinates to the projective line
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Order Polynomial
open TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k]

/-- The polynomial coordinate chart on the projective line with the indicated denominator. -/
noncomputable def projectiveLinePolynomialChart (i : Fin 2) :
    Spec (.of k[X]) ⟶ projectiveLine k :=
  Spec.map (CommRingCat.ofHom (projectiveLine.awayEquivPolynomial k i).toRingHom) ≫
    projectiveLine.awayι k i

instance (i : Fin 2) : IsOpenImmersion (projectiveLinePolynomialChart k i) := by
  unfold projectiveLinePolynomialChart
  let : IsIso (CommRingCat.ofHom (projectiveLine.awayEquivPolynomial k i).toRingHom) :=
    (projectiveLine.awayEquivPolynomial k i).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

/-- The chart morphism respects the structure map to the coefficient field. -/
@[reassoc]
theorem projectiveLinePolynomialChart_toSpec (i : Fin 2) :
    projectiveLinePolynomialChart k i ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  rw [projectiveLinePolynomialChart, Category.assoc, projectiveLine.awayι_over,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro r
  exact (projectiveLine.awayEquivPolynomial k i).commutes r

/-- The projective line over a field has Krull dimension at most one. -/
theorem projectiveLine_dim_le_one : topologicalKrullDim (projectiveLine k) ≤ 1 := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨i, q, rfl⟩ := projectiveLine.exists_eq_awayι k x
  rw [coheight_eq_of_isOpenImmersion (projectiveLine.awayι k i), ← idealHeight_eq_coheight]
  let : q.asIdeal.IsPrime := q.isPrime
  refine (Ideal.height_le_ringKrullDim_of_isPrime (I := q.asIdeal)).trans ?_
  rw [ringKrullDim_eq_of_ringEquiv (projectiveLine.awayEquivPolynomial k i).toRingEquiv]
  exact Order.KrullDimLE.krullDim_le (n := 1)

/-- A morphism from the affine-line chart into a proper scheme over the base field
extends uniquely over the projective line. -/
theorem existsUnique_projectiveLineMap_extending_polynomialChart
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (g₀ : Spec (.of k[X]) ⟶ Y)
    (hg₀ : g₀ ≫ (Y ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) :
    ∃! f : projectiveLine k ⟶ Y,
      f ≫ (Y ↘ Spec (.of k)) = (projectiveLine k ↘ Spec (.of k)) ∧
        projectiveLinePolynomialChart k 0 ≫ f = g₀ := by
  let S := Spec (.of k)
  let X := projectiveLine k
  let chart := projectiveLinePolynomialChart k 0
  let U := chart.opensRange
  let g := chart.isoOpensRange.inv ≫ g₀
  let : g.IsOver S := by
    rw [Scheme.Hom.isOver_iff]
    change (chart.isoOpensRange.inv ≫ g₀) ≫ (Y ↘ S) = U.ι ≫ (X ↘ S)
    rw [Category.assoc, hg₀, ← projectiveLinePolynomialChart_toSpec k 0,
      ← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  have hU : Dense (U : Set X) := by
    apply U.isOpen.dense
    obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (.of k[X])))
    exact ⟨chart t, ⟨t, rfl⟩⟩
  obtain ⟨f, ⟨hfS, hfU⟩, hfuniq⟩ :=
    existsUnique_hom_extending_denseOpen (S := S) (projectiveLine_dim_le_one k) U hU g
  refine ⟨f, ⟨(Scheme.Hom.isOver_iff S).mp hfS, ?_⟩, fun f' hf' ↦ ?_⟩
  · change chart ≫ f = g₀
    rw [← chart.isoOpensRange_hom_ι, Category.assoc, hfU]
    simp [g]
  · apply hfuniq
    refine ⟨(Scheme.Hom.isOver_iff S).mpr hf'.1, ?_⟩
    have hchart : chart ≫ f' = g₀ := hf'.2
    rw [← cancel_epi chart.isoOpensRange.hom, chart.isoOpensRange_hom_ι_assoc, hchart]
    simp [g]

section Transition

variable {k} {L : Type u} [Field L] [Algebra k L]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)

private noncomputable def lineParamCoordinates (i : Fin 2) (t : L) :
    _root_.SymmetricAlgebra k (Fin 2 → k) →ₐ[k] L :=
  (aeval t).comp (projectiveLine.dehomogenize k i)

private theorem lineParamCoordinates_coord_self (i : Fin 2) (t : L) :
    lineParamCoordinates i t (projectiveLine.coord k i) = 1 := by
  simp [lineParamCoordinates, projectiveLine.dehomogenize_coord_self]

private theorem lineParamCoordinates_coord_rev (i : Fin 2) (t : L) :
    lineParamCoordinates i t (projectiveLine.coord k i.rev) = t := by
  simp [lineParamCoordinates, projectiveLine.dehomogenize_coord_rev]

private theorem lineParamCoordinates_map_irrelevant (i : Fin 2) (t : L) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (lineParamCoordinates i t).toRingHom = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem : projectiveLine.coord k i ∈ HomogeneousIdeal.irrelevant 𝒜 :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 Nat.zero_lt_one (projectiveLine.coord_mem k i)
  have hm := Ideal.mem_map_of_mem (lineParamCoordinates i t).toRingHom hmem
  change lineParamCoordinates i t (projectiveLine.coord k i) ∈ _ at hm
  rw [lineParamCoordinates_coord_self] at hm
  exact hm

private noncomputable def lineParamMap (i : Fin 2) (t : L) :
    Spec (.of L) ⟶ projectiveLine k :=
  Proj.fromOfGlobalSections 𝒜
    ((Scheme.ΓSpecIso (.of L)).inv.hom.comp (lineParamCoordinates i t).toRingHom)
    (by rw [← Ideal.map_map, lineParamCoordinates_map_irrelevant, Ideal.map_top])

private theorem lineParamMap_eq_chart (i : Fin 2) (t : L) :
    lineParamMap i t =
      Spec.map (CommRingCat.ofHom (aeval t).toRingHom) ≫ projectiveLinePolynomialChart k i := by
  let f := (lineParamCoordinates (k := k) i t).toRingHom
  have hu : IsUnit (f (projectiveLine.coord k i)) := by
    change IsUnit (lineParamCoordinates (k := k) i t (projectiveLine.coord k i))
    rw [lineParamCoordinates_coord_self]
    exact isUnit_one
  rw [lineParamMap, Proj.fromOfGlobalSections_Spec_eq_awayLift f
    (lineParamCoordinates_map_irrelevant (k := k) i t) Nat.zero_lt_one
    (projectiveLine.coord_mem k i) hu, projectiveLinePolynomialChart, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (projectiveLine.coord_mem k i) z
  simp only [CommRingCat.hom_ofHom]
  rw [Away.lift_mk _ hu (projectiveLine.coord_mem k i), RingHom.comp_apply]
  change f a * ↑((hu.unit ^ m)⁻¹) = aeval t (projectiveLine.awayEquivPolynomial k i
    (Away.mk 𝒜 (projectiveLine.coord_mem k i) m a ha))
  rw [projectiveLine.awayEquivPolynomial_mk]
  have hunit : (hu.unit : L) = 1 :=
    hu.unit_spec.trans (lineParamCoordinates_coord_self i t)
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hunit, one_pow, inv_one, mul_one]
  rfl

/-- The two polynomial charts identify their nonzero parameters by inversion. -/
theorem projectiveLinePolynomialChart_aeval_inv (t : L) (ht : t ≠ 0) :
    Spec.map (CommRingCat.ofHom (aeval t⁻¹).toRingHom) ≫ projectiveLinePolynomialChart k 1 =
      Spec.map (CommRingCat.ofHom (aeval t).toRingHom) ≫ projectiveLinePolynomialChart k 0 := by
  rw [← lineParamMap_eq_chart, ← lineParamMap_eq_chart]
  let f := lineParamCoordinates (k := k) 0 t
  let g := lineParamCoordinates (k := k) 1 t⁻¹
  let γ := Scheme.ΓSpecIso (.of L)
  let c := (Units.mk0 t ht)⁻¹
  let cΓ := c.map γ.inv.hom.toMonoidHom
  unfold lineParamMap
  apply TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling _ _ _ cΓ
  intro n a ha
  have hf₀ : f (projectiveLine.coord k 0) = 1 := lineParamCoordinates_coord_self 0 t
  have hf₁ : f (projectiveLine.coord k 1) = t := lineParamCoordinates_coord_rev 0 t
  have hg₀ : g (projectiveLine.coord k 0) = t⁻¹ := lineParamCoordinates_coord_rev 1 t⁻¹
  have hg₁ : g (projectiveLine.coord k 1) = 1 := lineParamCoordinates_coord_self 1 t⁻¹
  have hscale : g a = (c : L) ^ n * f a := by
    apply AlgHom.apply_eq_pow_mul_of_forall_ι_eq f g _ _ ha
    intro m
    rw [projectiveLine.ι_eq_smul_coord_add_smul_coord k 0 m]
    change g (m 0 • projectiveLine.coord k 0 + m 1 • projectiveLine.coord k 1) = _
    simp only [show (0 : Fin 2).rev = 1 from rfl, map_add, Algebra.smul_def, map_mul,
      AlgHom.commutes, hf₀, hf₁, hg₀, hg₁, mul_one, Units.val_inv_eq_inv_val, Units.val_mk0, c]
    field_simp
  change γ.inv.hom (g a) = (cΓ : Γ(Spec (.of L), ⊤)) ^ n * γ.inv.hom (f a)
  rw [hscale, map_mul, map_pow]
  rfl

end Transition

variable {k} {n : ℕ}

/-- A polynomial-coordinate map on the affine chart extends uniquely to a morphism
from the projective line to the projective Fermat scheme. -/
theorem existsUnique_fermatProjectiveLineMap (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤) :
    ∃! f : projectiveLine k ⟶ fermatProjective k n,
      f ≫ fermatProjectiveToSpec k n = (projectiveLine k ↘ Spec (.of k)) ∧
        projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap p hF hp := by
  let : (fermatProjective k n).Over (Spec (.of k)) := ⟨fermatProjectiveToSpec k n⟩
  let : IsProper (fermatProjective k n ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (fermatProjectiveToSpec k n))
  exact existsUnique_projectiveLineMap_extending_polynomialChart k
    (fermatAffineMap p hF hp) (fermatAffineMap_toSpec p hF hp)

end TinyTauDemo

namespace TinyTauDemo.ProjectiveHypersurface

open Polynomial

universe u

variable {k : Type u} [Field k] {m d : ℕ} {F : MvPolynomial (Fin (m + 1)) k}
  (hF : F.IsHomogeneous d)

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

namespace TinyTauDemo

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- A projective extension of the affine Fermat map has the reflected polynomials as
its coordinates on the chart at infinity. -/
theorem fermatProjectiveLineMap_on_infinity_chart (p : Fin 3 → k[X]) {M : ℕ}
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hmax : ∃ i, p i ≠ 0 ∧ (p i).natDegree = M)
    (f : projectiveLine k ⟶ fermatProjective k n)
    (hfS : f ≫ fermatProjectiveToSpec k n = (projectiveLine k ↘ Spec (.of k)))
    (hf : projectiveLinePolynomialChart k 0 ≫ f = fermatAffineMap p hF hp) :
    projectiveLinePolynomialChart k 1 ≫ f =
      fermatAffineMap (fun i ↦ (p i).reflect M)
        (aeval_reflect_eq_zero_of_isHomogeneous p (fermatEquation_isHomogeneous k n) hdeg hF)
        (span_range_reflect_eq_top p hp hdeg hmax) := by
  rw [fermatAffineMap_eq_specMap] at hf ⊢
  exact ProjectiveHypersurface.projectiveLineMap_on_infinity_chart
    (fermatEquation_isHomogeneous k n) p hF hp hdeg hmax f hfS hf

end TinyTauDemo
