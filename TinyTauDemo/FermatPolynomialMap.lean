/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatCharts
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TinyTauDemo.InfinityCoordinates
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
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

private noncomputable def fermatPolynomialCoordinates (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) :
    FermatCoordinateRing k n →ₐ[k] k[X] :=
  Ideal.Quotient.liftₐ (fermatIdeal k n) (MvPolynomial.aeval p) <| by
    have hker : fermatIdeal k n ≤ RingHom.ker (MvPolynomial.aeval p).toRingHom := by
      rw [fermatIdeal, Ideal.span_singleton_le_iff_mem]
      exact hF
    exact fun _ hz ↦ RingHom.mem_ker.mp (hker hz)

private theorem fermatPolynomialCoordinates_mk (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (a : MvPolynomial (Fin 3) k) :
    fermatPolynomialCoordinates p hF (Ideal.Quotient.mk (fermatIdeal k n) a) =
      MvPolynomial.aeval p a := by
  rfl

private noncomputable def fermatAffineGlobalCoordinates (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) :
    FermatCoordinateRing k n →+* Γ(Spec (.of k[X]), ⊤) :=
  (Scheme.ΓSpecIso (.of k[X])).inv.hom.comp (fermatPolynomialCoordinates p hF).toRingHom

private theorem fermatAffineGlobalCoordinates_map_irrelevant (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    (HomogeneousIdeal.irrelevant (fermatGrading k n)).toIdeal.map
        (fermatAffineGlobalCoordinates p hF) = ⊤ := by
  let f := fermatPolynomialCoordinates p hF
  have hmap : (HomogeneousIdeal.irrelevant (fermatGrading k n)).toIdeal.map f.toRingHom = ⊤ := by
    apply top_unique
    rw [← hp, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hm := Ideal.mem_map_of_mem f.toRingHom
      (HomogeneousIdeal.mem_irrelevant_of_mem (fermatGrading k n) Nat.zero_lt_one
        (fermatCoord_mem_degree_one (k := k) (n := n) i))
    change f (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) ∈ _ at hm
    rw [fermatPolynomialCoordinates_mk, MvPolynomial.aeval_X] at hm
    exact hm
  rw [fermatAffineGlobalCoordinates, ← Ideal.map_map, hmap, Ideal.map_top]

/-- The affine-line morphism to the projective Fermat scheme given by polynomial coordinates
that satisfy the defining equation and generate the unit ideal. -/
noncomputable def fermatAffineMap (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0)
    (hp : Ideal.span (Set.range p) = ⊤) :
    Spec (.of k[X]) ⟶ fermatProjective k n :=
  Proj.fromOfGlobalSections (fermatGrading k n) (fermatAffineGlobalCoordinates p hF)
    (fermatAffineGlobalCoordinates_map_irrelevant p hF hp)

/-- The inverse image of a Fermat coordinate chart is the basic open on which the
corresponding polynomial coordinate does not vanish. -/
theorem fermatAffineMap_preimage_basicOpen (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤)
    (i : Fin 3) :
    fermatAffineMap p hF hp ⁻¹ᵁ
      Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) =
        (Spec (.of k[X])).basicOpen ((Scheme.ΓSpecIso (.of k[X])).inv (p i)) := by
  change Proj.fromOfGlobalSections (fermatGrading k n) (fermatAffineGlobalCoordinates p hF)
      (fermatAffineGlobalCoordinates_map_irrelevant p hF hp) ⁻¹ᵁ
      Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) =
    _
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one
    (fermatCoord_mem_degree_one i), fermatAffineGlobalCoordinates, RingHom.comp_apply]
  change (Spec (.of k[X])).basicOpen ((Scheme.ΓSpecIso (.of k[X])).inv
    (fermatPolynomialCoordinates p hF (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)))) = _
  rw [fermatPolynomialCoordinates_mk, MvPolynomial.aeval_X]

/-- The polynomial-coordinate morphism commutes with the structure maps to the base. -/
@[reassoc]
theorem fermatAffineMap_toSpec (p : Fin 3 → k[X])
    (hF : MvPolynomial.aeval p (fermatEquation k n) = 0) (hp : Ideal.span (Set.range p) = ⊤) :
    fermatAffineMap p hF hp ≫ fermatProjectiveToSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  change Proj.fromOfGlobalSections (fermatGrading k n) (fermatAffineGlobalCoordinates p hF)
      (fermatAffineGlobalCoordinates_map_irrelevant p hF hp) ≫
      Proj.toSpecZero (fermatGrading k n) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (fermatGrading k n 0))) = _
  rw [Proj.fromOfGlobalSections_toSpecZero_assoc]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcomp :
      (fermatAffineGlobalCoordinates p hF).comp
          ((algebraMap (fermatGrading k n 0) (FermatCoordinateRing k n)).comp
            (algebraMap k (fermatGrading k n 0))) =
        (Scheme.ΓSpecIso (.of k[X])).inv.hom.comp (algebraMap k k[X]) := by
    ext r
    exact congrArg (Scheme.ΓSpecIso (.of k[X])).inv (AlgHom.commutes _ r)
  rw [RingHom.comp_assoc, hcomp, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    CommRingCat.ofHom_hom, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

section Overlap

private theorem pullback_global_affine_section
    {L : Type u} [CommRing L] [Algebra k L] (φ : k[X] →ₐ[k] L) (a : k[X]) :
    (Scheme.ΓSpecIso (.of L)).hom
        ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop ((Scheme.ΓSpecIso (.of k[X])).inv a)) =
      φ a := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom)
  rw [← ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]
  simp

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
  let q := fun i ↦ (p i).reflect M
  let hG := aeval_reflect_eq_zero_of_isHomogeneous p (fermatEquation_isHomogeneous k n) hdeg hF
  let hq := span_range_reflect_eq_top p hp hdeg hmax
  let ψ := aeval (R := k) t
  let ψ' := aeval (R := k) t⁻¹
  let g := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  let g' := Spec.map (CommRingCat.ofHom ψ'.toRingHom)
  let γ := Scheme.ΓSpecIso (.of L)
  let c : Lˣ := Units.mk0 (t⁻¹ ^ M) (pow_ne_zero _ (inv_ne_zero ht))
  let cΓ := c.map γ.inv.hom.toMonoidHom
  change g' ≫ Proj.fromOfGlobalSections (fermatGrading k n)
      (fermatAffineGlobalCoordinates q hG) (fermatAffineGlobalCoordinates_map_irrelevant q hG hq) =
    g ≫ Proj.fromOfGlobalSections (fermatGrading k n)
      (fermatAffineGlobalCoordinates p hF) (fermatAffineGlobalCoordinates_map_irrelevant p hF hp)
  rw [Proj.fromOfGlobalSections_naturality, Proj.fromOfGlobalSections_naturality]
  apply TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling _ _ _ cΓ
  intro d a ha
  obtain ⟨F, hFhom, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha
  apply γ.commRingCatIsoToRingEquiv.injective
  change γ.hom ((g'.appTop.hom.comp (fermatAffineGlobalCoordinates q hG))
    (Ideal.Quotient.mk (fermatIdeal k n) F)) =
      γ.hom (cΓ ^ d * (g.appTop.hom.comp (fermatAffineGlobalCoordinates p hF))
        (Ideal.Quotient.mk (fermatIdeal k n) F))
  have hc : γ.hom (cΓ : Γ(Spec (.of L), ⊤)) = (c : L) := by
    dsimp only [cΓ]
    rw [Units.coe_map]
    change γ.hom (γ.inv (c : L)) = (c : L)
    simp
  simp only [map_mul, map_pow, hc, RingHom.comp_apply, fermatAffineGlobalCoordinates]
  dsimp only [γ, g, g']
  rw [pullback_global_affine_section, pullback_global_affine_section]
  change ψ' (fermatPolynomialCoordinates q hG (Ideal.Quotient.mk (fermatIdeal k n) F)) =
    (c : L) ^ d * ψ (fermatPolynomialCoordinates p hF (Ideal.Quotient.mk (fermatIdeal k n) F))
  rw [fermatPolynomialCoordinates_mk, fermatPolynomialCoordinates_mk,
    MvPolynomial.comp_aeval_apply, MvPolynomial.comp_aeval_apply]
  have hcoords : (fun i ↦ ψ' (q i)) = (c : L) • fun i ↦ ψ (p i) := by
    funext i
    let : Invertible t := invertibleOfNonzero ht
    have hi := eval₂_reflect_mul_pow (algebraMap k L) t M (p i) (hdeg i)
    rw [invOf_eq_inv, ← aeval_def, ← aeval_def] at hi
    have htM : t ^ M ≠ 0 := pow_ne_zero _ ht
    have hh := (eq_div_iff htM).mpr hi
    simpa only [q, ψ, ψ', c, Units.val_mk0, Pi.smul_apply, smul_eq_mul, inv_pow,
      div_eq_mul_inv, mul_comm (t ^ M)⁻¹] using hh
  have hF' : F.IsHomogeneous d := hFhom
  rw [hcoords, hF'.aeval_smul, smul_eq_mul]

end Overlap

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
  let γ := Scheme.ΓSpecIso (.of L)
  let f := (φ.comp (fermatPolynomialCoordinates p hF)).toRingHom
  let 𝒜 := fermatGrading k n
  let z := Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X 2)
  have hz' : f z = φ (p 2) := by
    simp [f, z, fermatPolynomialCoordinates_mk]
  have huf : IsUnit (f z) := isUnit_iff_ne_zero.mpr (hz' ▸ hz)
  have hfΓ : (g.appTop.hom.comp (fermatAffineGlobalCoordinates p hF)) = γ.inv.hom.comp f := by
    apply RingHom.ext
    intro a
    apply γ.commRingCatIsoToRingEquiv.injective
    change γ.hom (g.appTop ((Scheme.ΓSpecIso (.of k[X])).inv
      (fermatPolynomialCoordinates p hF a))) = γ.hom (γ.inv (f a))
    rw [Iso.inv_hom_id_apply]
    exact pullback_global_affine_section φ _
  have hξ : z ∈ 𝒜 1 := fermatCoord_mem_degree_one 2
  have hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 Nat.zero_lt_one hξ)) huf
  have hleft : g ≫ fermatAffineMap p hF hp =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f huf)) ≫ Proj.awayι 𝒜 z hξ one_pos := by
    change g ≫ Proj.fromOfGlobalSections 𝒜 (fermatAffineGlobalCoordinates p hF) _ = _
    rw [Proj.fromOfGlobalSections_naturality]
    suffices ∀ ha, Proj.fromOfGlobalSections 𝒜
        (g.appTop.hom.comp (fermatAffineGlobalCoordinates p hF)) ha =
        Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f huf)) ≫ Proj.awayι 𝒜 z hξ one_pos by
      exact this _
    rw [hfΓ]
    intro _
    exact Proj.fromOfGlobalSections_Spec_eq_awayLift f hf one_pos hξ huf
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
    change φ (fermatPolynomialCoordinates p hF (Ideal.Quotient.mk _ P)) = _
    rw [fermatPolynomialCoordinates_mk, MvPolynomial.comp_aeval_apply]
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
