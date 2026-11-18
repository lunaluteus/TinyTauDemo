/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Polynomial.FermatLineExtension
public import TinyTauDemo.AlgebraicGeometry.Curves.ProjectiveLineDifferentials
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The local ring of the projective line at infinity

The valuation-defined point at infinity is the origin in the chart with
coordinate `X₀/X₁`. The stalk is the localization of the polynomial ring at `(X)`.

See `/roadmap/index.qmd#rem-scheme-curves-recall` @ `1f38df1cf9d142fa5da4d43a1b973b77a7debc0c`.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Polynomial TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k]

local notation "P₁" => projectiveLine k
local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)

/-- The origin of the polynomial coordinate chart. -/
@[expose] noncomputable def polynomialChartOrigin : PrimeSpectrum k[X] :=
  ⟨(Polynomial.idealX k).asIdeal, (Polynomial.idealX k).isPrime⟩

private theorem polynomialChartOrigin_asIdeal_isMaximal :
    (polynomialChartOrigin k).asIdeal.IsMaximal := by
  change (Ideal.span {(X : k[X])}).IsMaximal
  exact PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X

private theorem projectiveLinePolynomialChart_covers (x : P₁) :
    ∃ (i : Fin 2) (q : PrimeSpectrum k[X]), projectiveLinePolynomialChart k i q = x := by
  obtain ⟨i, q, rfl⟩ := projectiveLine.exists_eq_awayι k x
  let e := (projectiveLine.awayEquivPolynomial k i).toRingEquiv.toCommRingCatIso
  obtain ⟨z, hz⟩ := (Spec.map e.hom).homeomorph.surjective q
  refine ⟨i, z, ?_⟩
  rw [projectiveLinePolynomialChart_def]
  exact congrArg (projectiveLine.awayι k i) hz

private theorem projectiveLinePolynomialChart_one_mem_away_zero_iff
    (q : PrimeSpectrum k[X]) :
    projectiveLinePolynomialChart k 1 q ∈ (projectiveLine.awayι k 0 ''ᵁ ⊤) ↔
      Polynomial.X ∉ q.asIdeal := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  change projectiveLinePolynomialChart k 1 q ∈ (Proj.awayι 𝒜 _ _ _).opensRange ↔ _
  rw [Proj.opensRange_awayι]
  let e := (projectiveLine.awayEquivPolynomial k 1).toRingHom
  rw [projectiveLinePolynomialChart_def]
  change (Spec.map (CommRingCat.ofHom e)) q ∈
    (projectiveLine.awayι k 1 ⁻¹ᵁ Proj.basicOpen 𝒜 (projectiveLine.coord k 0)) ↔ _
  rw [Proj.awayι_preimage_basicOpen 𝒜 (projectiveLine.coord_mem k 1) Nat.one_pos
    (projectiveLine.coord_mem k 0) Nat.one_pos]
  change PrimeSpectrum.comap e q ∈ PrimeSpectrum.basicOpen
    (Away.isLocalizationElem (projectiveLine.coord_mem k 1) (projectiveLine.coord_mem k 0)) ↔ _
  rw [PrimeSpectrum.mem_basicOpen]
  change e (Away.isLocalizationElem (projectiveLine.coord_mem k 1)
    (projectiveLine.coord_mem k 0)) ∉ q.asIdeal ↔ _
  have he : e (Away.isLocalizationElem (projectiveLine.coord_mem k 1)
      (projectiveLine.coord_mem k 0)) = X := by
    change projectiveLine.awayEquivPolynomial k 1
      (Away.mk 𝒜 (projectiveLine.coord_mem k 1) 1
        (projectiveLine.coord k 0 ^ 1) _) = _
    rw [projectiveLine.awayEquivPolynomial_mk, pow_one]
    exact projectiveLine.dehomogenize_coord_rev k 1
  rw [he]

/-- The point at infinity is the origin in the chart with denominator `X₁`. -/
theorem projectiveLineInfinity_eq_polynomialChartOrigin :
    (projectiveLineInfinity k : P₁) =
      projectiveLinePolynomialChart k 1 (polynomialChartOrigin k) := by
  have hi := projectiveLineInfinity_not_mem_affineChart k
  obtain ⟨i, q, hq⟩ := projectiveLinePolynomialChart_covers k (projectiveLineInfinity k)
  fin_cases i
  · exfalso
    apply hi
    rw [← hq, Scheme.Hom.image_top_eq_opensRange]
    rw [projectiveLinePolynomialChart_def]
    exact Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
  · rw [← hq]
    congr 1
    apply PrimeSpectrum.ext
    have hX : (X : k[X]) ∈ q.asIdeal := by
      by_contra h
      exact hi (hq ▸ (projectiveLinePolynomialChart_one_mem_away_zero_iff k q).mpr h)
    symm
    apply (polynomialChartOrigin_asIdeal_isMaximal k).eq_of_le q.isPrime.ne_top
    exact q.asIdeal.span_singleton_le_iff_mem.mpr hX

/-- The local ring of the projective line at infinity is `k[s]_(s)`, where
`s = X₀/X₁` is the coordinate in the second polynomial chart. -/
noncomputable def projectiveLineInfinityStalkEquiv :
    ((P₁).presheaf.stalk (projectiveLineInfinity k : P₁)) ≃+*
      Localization.AtPrime (polynomialChartOrigin k).asIdeal := by
  let q : Spec (.of k[X]) := polynomialChartOrigin k
  let f := projectiveLinePolynomialChart k 1
  have : IsOpenImmersion f := inferInstanceAs (IsOpenImmersion (projectiveLinePolynomialChart k 1))
  let h := projectiveLineInfinity_eq_polynomialChartOrigin k
  let e := (P₁).presheaf.stalkCongr (.of_eq h) ≪≫ asIso (f.stalkMap q)
  exact (e ≪≫ Spec.stalkIso (.of k[X]) q).commRingCatIsoToRingEquiv

/-- The reciprocal polynomial coordinate generates the maximal ideal of the
stalk at infinity. -/
theorem projectiveLineInfinity_maximalIdeal :
    let e := projectiveLineInfinityStalkEquiv k
    IsLocalRing.maximalIdeal ((P₁).presheaf.stalk (projectiveLineInfinity k : P₁)) =
      Ideal.span {e.symm (algebraMap k[X] (Localization.AtPrime (polynomialChartOrigin k).asIdeal)
        (X : k[X]))} := by
  let e := projectiveLineInfinityStalkEquiv k
  change IsLocalRing.maximalIdeal _ = Ideal.span {e.symm (algebraMap k[X] _ X)}
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e.symm,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  change (((Ideal.span {(X : k[X])}).map (algebraMap k[X]
    (Localization.AtPrime (polynomialChartOrigin k).asIdeal))).map e.symm.toRingHom) = _
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

end TinyTauDemo
