/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatProjective
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Naturality
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Morphisms defined by Fermat coordinates

A tuple of sections on an affine scheme gives a morphism to the projective Fermat
scheme when its entries generate the unit ideal and satisfy the equation. Chart
restrictions, base maps and rescaling are expressed on the same coordinate map.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TauCeti.GradedAlgebra

namespace TinyTauDemo

universe u

variable {k B : Type u} [CommRing k] [CommRing B] [Algebra k B] {n : ℕ}

/-- Evaluate the homogeneous Fermat coordinate ring at the given tuple. -/
noncomputable def fermatCoordinateEval (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) : FermatCoordinateRing k n →ₐ[k] B :=
  Ideal.Quotient.liftₐ (fermatIdeal k n) (MvPolynomial.aeval p) <| by
    have hker : fermatIdeal k n ≤ RingHom.ker (MvPolynomial.aeval p).toRingHom := by
      rw [fermatIdeal, Ideal.span_singleton_le_iff_mem]
      exact (aeval_fermatEquation_eq_zero_iff_coordinates (k := k) n p).mpr hF
    exact fun _ hz ↦ RingHom.mem_ker.mp (hker hz)

/-- Evaluation on a polynomial class agrees with evaluation of the polynomial. -/
@[simp]
theorem fermatCoordinateEval_mk (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (a : MvPolynomial (Fin 3) k) :
    fermatCoordinateEval (k := k) p hF (Ideal.Quotient.mk (fermatIdeal k n) a) =
      MvPolynomial.aeval p a := by
  rfl

private theorem fermatCoordinateEval_map_irrelevant (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤) :
    (HomogeneousIdeal.irrelevant (fermatGrading k n)).toIdeal.map
        (fermatCoordinateEval (k := k) p hF).toRingHom = ⊤ := by
  apply top_unique
  rw [← hp, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hm := Ideal.mem_map_of_mem (fermatCoordinateEval (k := k) p hF).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem (fermatGrading k n) Nat.zero_lt_one
      (fermatCoord_mem_degree_one (k := k) (n := n) i))
  change fermatCoordinateEval (k := k) p hF
    (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) ∈ _ at hm
  rw [fermatCoordinateEval_mk, MvPolynomial.aeval_X] at hm
  exact hm

private noncomputable def fermatSpecGlobalCoordinates (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) : FermatCoordinateRing k n →+* Γ(Spec (.of B), ⊤) :=
  (Scheme.ΓSpecIso (.of B)).inv.hom.comp (fermatCoordinateEval (k := k) p hF).toRingHom

private theorem fermatSpecGlobalCoordinates_map_irrelevant (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤) :
    (HomogeneousIdeal.irrelevant (fermatGrading k n)).toIdeal.map
        (fermatSpecGlobalCoordinates (k := k) p hF) = ⊤ := by
  rw [fermatSpecGlobalCoordinates, ← Ideal.map_map,
    fermatCoordinateEval_map_irrelevant (k := k) p hF hp, Ideal.map_top]

/-- A tuple generating the unit ideal defines a morphism from its spectrum to the Fermat scheme. -/
noncomputable def fermatSpecMap (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) : Spec (.of B) ⟶ fermatProjective k n :=
  Proj.fromOfGlobalSections (fermatGrading k n) (fermatSpecGlobalCoordinates (k := k) p hF)
    (fermatSpecGlobalCoordinates_map_irrelevant (k := k) p hF hp)

/-- The coordinate morphism commutes with the structure maps to the base. -/
@[reassoc]
theorem fermatSpecMap_toSpec (p : Fin 3 → B) (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) :
    fermatSpecMap (k := k) p hF hp ≫ fermatProjectiveToSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
  change Proj.fromOfGlobalSections (fermatGrading k n) (fermatSpecGlobalCoordinates (k := k) p hF)
      (fermatSpecGlobalCoordinates_map_irrelevant (k := k) p hF hp) ≫
      Proj.toSpecZero (fermatGrading k n) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (fermatGrading k n 0))) = _
  rw [Proj.fromOfGlobalSections_toSpecZero_assoc]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcomp :
      (fermatSpecGlobalCoordinates (k := k) p hF).comp
          ((algebraMap (fermatGrading k n 0) (FermatCoordinateRing k n)).comp
            (algebraMap k (fermatGrading k n 0))) =
        (Scheme.ΓSpecIso (.of B)).inv.hom.comp (algebraMap k B) := by
    ext r
    exact congrArg (Scheme.ΓSpecIso (.of B)).inv (AlgHom.commutes _ r)
  rw [RingHom.comp_assoc, hcomp, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    CommRingCat.ofHom_hom, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.id_comp]

/-- When a coordinate is a unit, the morphism lands in its degree-one chart. -/
theorem fermatSpecMap_eq_awayLift
    (p : Fin 3 → B) (hpF : p 0 ^ n + p 1 ^ n = p 2 ^ n)
    (hp : Ideal.span (Set.range p) = ⊤) (i : Fin 3) (hi : IsUnit (p i)) :
    fermatSpecMap (k := k) p hpF hp = Spec.map (CommRingCat.ofHom
      (Away.lift (fermatGrading k n) (fermatCoordinateEval (k := k) p hpF).toRingHom
        (f := Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i))
        (by
          change IsUnit
            (fermatCoordinateEval (k := k) p hpF (Ideal.Quotient.mk _ (MvPolynomial.X i)))
          rwa [fermatCoordinateEval_mk, MvPolynomial.aeval_X]))) ≫
      Proj.awayι (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i))
        (fermatCoord_mem_degree_one i) one_pos :=
  Proj.fromOfGlobalSections_Spec_eq_awayLift _
    (fermatCoordinateEval_map_irrelevant (k := k) p hpF hp)
    one_pos (fermatCoord_mem_degree_one i) _

/-- The inverse image of the coordinate chart is the basic open of that coordinate. -/
theorem fermatSpecMap_preimage_basicOpen (p : Fin 3 → B)
    (hF : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤) (i : Fin 3) :
    fermatSpecMap (k := k) p hF hp ⁻¹ᵁ
      Proj.basicOpen (fermatGrading k n) (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) =
        (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv (p i)) := by
  change Proj.fromOfGlobalSections (fermatGrading k n) (fermatSpecGlobalCoordinates (k := k) p hF)
    (fermatSpecGlobalCoordinates_map_irrelevant (k := k) p hF hp) ⁻¹ᵁ
      Proj.basicOpen (fermatGrading k n)
        (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)) = _
  rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
    (fermatCoord_mem_degree_one i), fermatSpecGlobalCoordinates, RingHom.comp_apply]
  change (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv
    (fermatCoordinateEval (k := k) p hF
      (Ideal.Quotient.mk (fermatIdeal k n) (MvPolynomial.X i)))) = _
  rw [fermatCoordinateEval_mk, MvPolynomial.aeval_X]

/-- Rescaling all homogeneous coordinates by a common unit preserves the morphism. -/
theorem fermatSpecMap_eq_of_unit_rescale (p q : Fin 3 → B)
    (hFp : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤)
    (hFq : q 0 ^ n + q 1 ^ n = q 2 ^ n) (hq : Ideal.span (Set.range q) = ⊤)
    (c : Bˣ) (hc : ∀ i, q i = (c : B) * p i) :
    fermatSpecMap (k := k) p hFp hp = fermatSpecMap (k := k) q hFq hq := by
  let γ := Scheme.ΓSpecIso (.of B)
  let cΓ := c.map γ.inv.hom.toMonoidHom
  unfold fermatSpecMap
  symm
  apply TauCeti.ProjectiveSpectrum.fromOfGlobalSections_eq_of_unit_rescaling _ _ _ cΓ
  intro d a ha
  obtain ⟨F, hF, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha
  have hq' : q = (c : B) • p := funext hc
  change γ.inv (fermatCoordinateEval (k := k) q hFq (Ideal.Quotient.mk _ F)) =
    (cΓ : Γ(Spec (.of B), ⊤)) ^ d *
      γ.inv (fermatCoordinateEval (k := k) p hFp (Ideal.Quotient.mk _ F))
  simp only [fermatCoordinateEval_mk, hq', hF.aeval_smul, smul_eq_mul, Units.coe_map, cΓ]
  change γ.inv.hom ((c : B) ^ d * MvPolynomial.aeval p F) =
    γ.inv.hom (c : B) ^ d * γ.inv.hom (MvPolynomial.aeval p F)
  rw [map_mul, map_pow]

/-- Pulling the coordinate morphism back along an algebra homomorphism evaluates its coordinates. -/
theorem fermatSpecMap_comp_SpecMap {C : Type u} [CommRing C] [Algebra k C] (φ : B →ₐ[k] C)
    (p : Fin 3 → B) (hFp : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤)
    (hFq : φ (p 0) ^ n + φ (p 1) ^ n = φ (p 2) ^ n)
    (hq : Ideal.span (Set.range fun i ↦ φ (p i)) = ⊤) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fermatSpecMap (k := k) p hFp hp =
      fermatSpecMap (k := k) (fun i ↦ φ (p i)) hFq hq := by
  let f := CommRingCat.ofHom φ.toRingHom
  change Spec.map f ≫ Proj.fromOfGlobalSections (fermatGrading k n)
      (fermatSpecGlobalCoordinates (k := k) p hFp)
      (fermatSpecGlobalCoordinates_map_irrelevant (k := k) p hFp hp) =
    Proj.fromOfGlobalSections (fermatGrading k n)
      (fermatSpecGlobalCoordinates (k := k) (fun i ↦ φ (p i)) hFq)
      (fermatSpecGlobalCoordinates_map_irrelevant (k := k) _ hFq hq)
  rw [Proj.fromOfGlobalSections_naturality]
  congr 1
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (Spec.map f).appTop ((Scheme.ΓSpecIso (.of B)).inv
    (fermatCoordinateEval (k := k) p hFp (Ideal.Quotient.mk _ a))) =
    (Scheme.ΓSpecIso (.of C)).inv
      (fermatCoordinateEval (k := k) (fun i ↦ φ (p i)) hFq (Ideal.Quotient.mk _ a))
  rw [fermatCoordinateEval_mk, fermatCoordinateEval_mk]
  have heval := MvPolynomial.comp_aeval_apply (f := p) φ a
  have hφ : φ (MvPolynomial.aeval p a) = MvPolynomial.aeval (fun i ↦ φ (p i)) a := heval
  rw [← hφ]
  have hγ := (Scheme.ΓSpecIso_inv_naturality f)
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hγ.symm) _

end TinyTauDemo
