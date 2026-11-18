/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatCharts
public import TinyTauDemo.Fermat.Polynomial.FermatSpecMap
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TinyTauDemo.AlgebraicGeometry.Projective.InfinityCoordinates
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# The morphism defined by polynomial coordinates on the Fermat curve

The homogeneous coordinate homomorphism sends the Fermat equation to zero and
the irrelevant ideal to the unit ideal. This gives an affine-line morphism
to the projective Fermat scheme and identifies its inverse images of the standard charts.
See `/roadmap/index.qmd#rem-scheme-curves-recall @ 1b6500902fe7ada276d02c819b982144f0c4070f`.
-/

public section

open AlgebraicGeometry CategoryTheory Polynomial TauCeti.GradedAlgebra

namespace TinyTauDemo

universe u

variable {k : Type u} [CommRing k] {n : ℕ}

/-- The affine-line morphism to the projective Fermat scheme given by polynomial coordinates
that satisfy the defining equation and generate the unit ideal. -/
noncomputable def fermatAffineMap (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    Spec (.of k[X]) ⟶ fermatProjective k n :=
  fermatSpecMap (k := k) p ((aeval_fermatEquation_eq_zero_iff_coordinates n p).mp hF) hp

/-- The polynomial-coordinate Fermat morphism agrees with the hypersurface construction. -/
theorem fermatAffineMap_eq_specMap (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    fermatAffineMap p hF hp =
      ProjectiveHypersurface.specMap (fermatEquation_isHomogeneous k n) p hF hp :=
  fermatSpecMap_eq_specMap (k := k) p
    ((aeval_fermatEquation_eq_zero_iff_coordinates n p).mp hF) hp

/-- The inverse image of a Fermat coordinate chart is the basic open on which the
corresponding polynomial coordinate does not vanish. -/
theorem fermatAffineMap_preimage_basicOpen (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (i : Fin 3) :
    fermatAffineMap p hF hp ⁻¹ᵁ
      Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) =
        (Spec (.of k[X])).basicOpen ((Scheme.ΓSpecIso (.of k[X])).inv (p i)) :=
  fermatSpecMap_preimage_basicOpen (k := k) p
    ((aeval_fermatEquation_eq_zero_iff_coordinates n p).mp hF) hp i

/-- The polynomial-coordinate morphism commutes with the structure maps to the base. -/
@[reassoc]
theorem fermatAffineMap_toSpec (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤) :
    fermatAffineMap p hF hp ≫ fermatProjectiveToSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) :=
  fermatSpecMap_toSpec (k := k) p ((aeval_fermatEquation_eq_zero_iff_coordinates n p).mp hF) hp

private theorem evaluated_coordinates_equation {B C : Type u} [CommRing B] [CommRing C]
    (φ : B →+* C) (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) :
    φ (p 0) ^ n + φ (p 1) ^ n = φ (p 2) ^ n := by
  simpa only [map_add, map_pow] using congrArg φ hF

private theorem evaluated_coordinates_span {B C : Type u} [CommRing B] [CommRing C]
    (φ : B →+* C) (p : Fin 3 → B) (hp : Ideal.span (Set.range p) = ⊤) :
    Ideal.span (Set.range fun i ↦ φ (p i)) = ⊤ := by
  change Ideal.span (Set.range (φ ∘ p)) = ⊤
  rw [Set.range_comp, ← Ideal.map_span, hp, Ideal.map_top]

/-- The coordinate morphisms from the two affine charts agree after substituting
the reciprocal parameter wherever it is nonzero. This is equality of scheme morphisms. -/
theorem fermatAffineMap_reflect_overlap {k : Type u} [Field k] {n : ℕ}
    {L : Type u} [Field L] [Algebra k L]
    (p : Fin 3 → k[X]) {M : ℕ}
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (hdeg : ∀ i, (p i).natDegree ≤ M) (hmax : ∃ i, p i ≠ 0 ∧ (p i).natDegree = M)
    {t : L} (ht : t ≠ 0) :
    Spec.map (CommRingCat.ofHom (aeval t⁻¹).toRingHom) ≫
        fermatAffineMap (fun i ↦ (p i).reflect M)
          (aeval_reflect_eq_zero_of_isHomogeneous p (fermatEquation_isHomogeneous k n) hdeg hF)
          (span_range_reflect_eq_top p hp hdeg hmax) =
      Spec.map (CommRingCat.ofHom (aeval t).toRingHom) ≫ fermatAffineMap p hF hp := by
  rw [fermatAffineMap_eq_specMap, fermatAffineMap_eq_specMap]
  exact ProjectiveHypersurface.specMap_reflect_overlap
    (fermatEquation_isHomogeneous k n) p hF hp hdeg hmax ht

open HomogeneousLocalization in
/-- Where the last coordinate is nonzero, the polynomial-coordinate morphism factors
through the last affine Fermat chart via evaluation in the two normalized coordinates. -/
theorem fermatAffineMap_comp_SpecMap_eq_lastChart
    {k L : Type u} [Field k] [CharZero k] [IsAlgClosed k] [Field L] [Algebra k L]
    {n : ℕ} (hn : 0 < n)
    (p : Fin 3 → k[X]) (hF : MvPolynomial.aeval p (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range p) = ⊤) (φ : k[X] →ₐ[k] L) (hz : φ (p 2) ≠ 0)
    (ψ : FermatAffineRing k n 2 →ₐ[k] L)
    (hψ : ∀ P : MvPolynomial (Fin 2) k, ψ (Ideal.Quotient.mk _ P) =
      MvPolynomial.aeval ![φ (p 0) / φ (p 2), φ (p 1) / φ (p 2)] P) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fermatAffineMap p hF hp =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ fermatAffineChart k hn 2 := by
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let q := fun i ↦ φ (p i)
  have hEq := (aeval_fermatEquation_eq_zero_iff_coordinates n p).mp hF
  have hqF := evaluated_coordinates_equation φ.toRingHom p hEq
  have hq := evaluated_coordinates_span φ.toRingHom p hp
  let f := (fermatCoordinateEval (k := k) q hqF).toRingHom
  let 𝒜 := fermatGrading k n
  let z := Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X 2)
  have hz' : f z = φ (p 2) := by
    simp [f, z, q]
  have huf : IsUnit (f z) := isUnit_iff_ne_zero.mpr (hz' ▸ hz)
  have hξ : z ∈ 𝒜 1 := fermatCoord_mem_degree_one 2
  have hleft : g ≫ fermatAffineMap p hF hp =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f huf)) ≫ Proj.awayι 𝒜 z hξ one_pos := by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fermatSpecMap (k := k) p hEq hp = _
    rw [fermatSpecMap_comp_SpecMap (k := k) φ p hEq hp hqF hq]
    exact fermatSpecMap_eq_awayLift (k := k) q hqF hq 2 (isUnit_iff_ne_zero.mpr hz)
  rw [hleft, fermatAffineChart_eq_awayι]
  -- Use the common Proj presentation before cancelling the chart immersion.
  change Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f huf)) ≫ Proj.awayι 𝒜 z hξ one_pos =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (fermatAwayEquivAffine k hn 2).toRingHom) ≫
        Proj.awayι 𝒜 z hξ one_pos
  rw [← Category.assoc, ← Spec.map_comp, cancel_mono, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hξ a
  have ha' : a ∈ fermatGrading k n d := by simpa only [Nat.nsmul_eq_mul, mul_one] using ha
  obtain ⟨P, hP, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha'
  change Away.lift 𝒜 f huf (Away.mk 𝒜 hξ d (Ideal.Quotient.mk _ P) ha) =
    ψ (fermatAwayEquivAffine k hn 2 (Away.mk 𝒜 hξ d (Ideal.Quotient.mk _ P) ha))
  rw [Away.lift_mk, fermatAwayEquivAffine_mk k hn 2 d P hP, hψ, TauCeti.aeval_dehomogenize]
  have huc : (↑huf.unit : L) = φ (p 2) := huf.unit_spec.trans hz'
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, huc]
  have hfP : f (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun i ↦ φ (p i)) P := by
    exact fermatCoordinateEval_mk (k := k) q hqF P
  rw [hfP]
  have hcoord : (2 : Fin 3).insertNth (1 : L)
      ![φ (p 0) / φ (p 2), φ (p 1) / φ (p 2)] =
      (φ (p 2))⁻¹ • (fun i ↦ φ (p i)) := by
    ext i
    fin_cases i
    · exact div_eq_inv_mul _ _
    · exact div_eq_inv_mul _ _
    · exact (inv_mul_cancel₀ hz).symm
  rw [hcoord, hP.aeval_smul, smul_eq_mul]
  simp only [inv_pow, mul_comm]

end TinyTauDemo
