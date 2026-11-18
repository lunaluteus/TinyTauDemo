/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.Projection.BranchLocal
public import TinyTauDemo.Fermat.Curve.FermatProjection
public import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.ClosedDifferentialLength
import Mathlib.RingTheory.Polynomial.Ideal
import TauCeti.AlgebraicGeometry.RationalPoint.Basic

/-!
# Ramification of the projective Fermat projection

The computation in the normalized affine coordinates gives the pullback
of the maximal ideal on the scheme stalk. The projection has index `n`
at the point with coordinates `[a : 0 : 1]` when `a^n = 1`.

See `/roadmap/index.qmd#prp-fermat-genus` @ `b2c9a29565e4747906e07cca00173aa6354b72f0`.
-/

public section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

private theorem map_maximalIdeal_of_iso {A B : CommRingCat.{u}}
    [IsLocalRing A] [IsLocalRing B] (e : A ≅ B) :
    (maximalIdeal A).map e.hom.hom = maximalIdeal B :=
  map_ringEquiv_maximalIdeal e.commRingCatIsoToRingEquiv

private theorem map_maximalIdeal_pow_in_commuting_square {A B C D : CommRingCat.{u}}
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [IsLocalRing D]
    (f : A ⟶ B) (g : C ⟶ D) (eA : A ≅ C) (eB : B ≅ D)
    (h : f ≫ eB.hom = eA.hom ≫ g) (n : ℕ)
    (hg : (maximalIdeal C).map g.hom = maximalIdeal D ^ n) :
    (maximalIdeal A).map f.hom = maximalIdeal B ^ n := by
  have hm : ((maximalIdeal A).map f.hom).map eB.hom.hom = maximalIdeal D ^ n := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, h, CommRingCat.hom_comp, ← Ideal.map_map,
      map_maximalIdeal_of_iso, hg]
  have he : (maximalIdeal D).map eB.inv.hom = maximalIdeal B :=
    map_maximalIdeal_of_iso eB.symm
  apply_fun Ideal.map eB.inv.hom at hm
  rw [Ideal.map_map, ← CommRingCat.hom_comp, eB.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id, Ideal.map_pow, he] at hm
  exact hm

set_option backward.isDefEq.respectTransparency false in
private theorem map_maximalIdeal_stalk_of_affine_charts {A B : CommRingCat.{u}} {X Y : Scheme.{u}}
    (i : Spec B ⟶ X) (j : Spec A ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (f : X ⟶ Y) (g : A ⟶ B) (h : i ≫ f = Spec.map g ≫ j) (p : Spec B) (n : ℕ)
    (hloc : (maximalIdeal (Localization.AtPrime (PrimeSpectrum.comap g.hom p).asIdeal)).map
        (Localization.localRingHom (PrimeSpectrum.comap g.hom p).asIdeal p.asIdeal g.hom rfl) =
          maximalIdeal (Localization.AtPrime p.asIdeal) ^ n) :
    (maximalIdeal (Y.presheaf.stalk (f (i p)))).map (f.stalkMap (i p)).hom =
      maximalIdeal (X.presheaf.stalk (i p)) ^ n := by
  let q : Spec A := (Spec.map g) p
  let c := Y.presheaf.stalkCongr (.of_eq (show f (i p) = j q from congrArg (fun m ↦ m p) h))
  let eX := asIso (i.stalkMap p) ≪≫ Spec.stalkIso B p
  let eY := c ≪≫ asIso (j.stalkMap q) ≪≫ Spec.stalkIso A q
  let g₀ := CommRingCat.ofHom (Localization.localRingHom q.asIdeal p.asIdeal g.hom rfl)
  have hc := Scheme.Hom.stalkMap_congr_hom (i ≫ f) (Spec.map g ≫ j) h (x := p)
  rw [Scheme.Hom.stalkMap_comp i f p, Scheme.Hom.stalkMap_comp (Spec.map g) j p] at hc
  have hLoc : (Spec.map g).stalkMap p ≫ (Spec.stalkIso B p).hom =
      (Spec.stalkIso A q).hom ≫ g₀ := by
    have e := Scheme.localRingHom_comp_stalkIso g (p : PrimeSpectrum B)
    change (Spec.stalkIso A q).hom ≫ g₀ ≫ (Spec.stalkIso B p).inv = _ at e
    rw [← e]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomm : f.stalkMap (i p) ≫ eX.hom = eY.hom ≫ g₀ := by
    dsimp only [eX, eY, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, show f.stalkMap (i p) ≫ i.stalkMap p =
      c.hom ≫ j.stalkMap q ≫ (Spec.map g).stalkMap p from hc]
    simp only [Category.assoc, hLoc]
  exact map_maximalIdeal_pow_in_commuting_square _ _ eY eX hcomm n hloc

section Fermat

variable (k : Type u) [Field k] {n : ℕ}

local notation "A" => FermatAffineRing k n 2
local notation "x" => Ideal.Quotient.mk _ (MvPolynomial.X (0 : Fin 2))
local notation "y" => Ideal.Quotient.mk _ (MvPolynomial.X (1 : Fin 2))

/-- The point `(a,0)` on the last Fermat chart viewed in the projective Fermat scheme. -/
noncomputable def fermatProjectionAffineBranchPoint (hn : 0 < n) {a : k} (ha : a ^ n = 1) :
    fermatProjective k n :=
  fermatAffineChart k hn 2
    (fermatLastChartPoint (a := a) (b := (0 : k)) (by simpa [zero_pow hn.ne'] using ha))

/-- The point `(a,0)` on the projective Fermat scheme is closed. -/
theorem isClosed_fermatProjectionAffineBranchPoint (hn : 0 < n) {a : k} (ha : a ^ n = 1) :
    IsClosed {fermatProjectionAffineBranchPoint k hn ha} := by
  let h : a ^ n + (0 : k) ^ n = 1 := by simpa [zero_pow hn.ne'] using ha
  let ev := fermatLastChartEval h
  let i := fermatAffineChart k hn 2
  let s := Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ i
  have hs : s ≫ (fermatProjective k n ↘ Spec (.of k)) = 𝟙 _ := by
    change (Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ fermatAffineChart k hn 2) ≫
      fermatProjectiveToSpec k n = _
    rw [Category.assoc, fermatAffineChart_comp_toSpec, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rw [show ev.toRingHom.comp (algebraMap k A) = RingHom.id k from
      RingHom.ext (fun r ↦ ev.commutes r)]
    exact Spec.map_id _
  have hp : s (closedPoint k) = fermatProjectionAffineBranchPoint k hn ha := by
    unfold fermatProjectionAffineBranchPoint
    apply congrArg i
    apply PrimeSpectrum.ext
    change (maximalIdeal k).comap ev.toRingHom = (fermatLastChartPoint h).asIdeal
    rw [fermatLastChartPoint_asIdeal, IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.ker_eq_comap_bot ev.toRingHom).symm
  rw [← hp]
  exact isClosed_singleton_of_section hs

variable [CharZero k] [IsAlgClosed k]

/-- On local rings of the actual projection, the pullback of the maximal ideal at the image
of the affine branch point `(a,0)` is the `n`th power of the point's maximal ideal. -/
theorem fermatProjection_map_maximalIdeal_at_affineBranchPoint (hn : 0 < n)
    {a : k} (ha : a ^ n = 1) :
    let p := fermatProjectionAffineBranchPoint k hn ha
    let f := fermatProjection k hn
    (maximalIdeal ((projectiveLine k).presheaf.stalk (f p))).map (f.stalkMap p).hom =
      maximalIdeal ((fermatProjective k n).presheaf.stalk p) ^ n := by
  dsimp only
  let h : a ^ n + (0 : k) ^ n = 1 := by simpa [zero_pow hn.ne'] using ha
  let p := fermatLastChartPoint h
  let x₀ : A := x
  let y₀ : A := y
  let g := Polynomial.aeval (R := k) x₀
  let q := p.comap g.toRingHom
  let i := fermatAffineChart k hn 2
  let j := projectiveLinePolynomialChart k 0
  let f := fermatProjection k hn
  have hcomm : i ≫ f = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ j := by
    rw [show i ≫ f = fermatProjectionOnLastChart k n from
      fermatAffineChart_comp_fermatProjection k hn, fermatProjectionOnLastChart_def]
  have hp : i p = fermatProjectionAffineBranchPoint k hn ha := by
    unfold fermatProjectionAffineBranchPoint
    rfl
  rw [← hp]
  refine map_maximalIdeal_stalk_of_affine_charts i j f
    (CommRingCat.ofHom g.toRingHom) hcomm p n ?_
  have hq : q.asIdeal = Ideal.span {Polynomial.X - Polynomial.C a} := by
    rw [← Polynomial.ker_evalRingHom]
    have he : (fermatLastChartEval h).comp g = Polynomial.aeval a := by
      apply Polynomial.algHom_ext
      rw [AlgHom.comp_apply, Polynomial.aeval_X, Polynomial.aeval_X]
      simpa only [x₀, Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.aeval_X, Matrix.cons_val_zero] using
        fermatLastChartEval_mk h (MvPolynomial.X 0)
    change p.asIdeal.comap g.toRingHom = _
    rw [show p.asIdeal = RingHom.ker (fermatLastChartEval h).toRingHom from
      fermatLastChartPoint_asIdeal h, RingHom.comap_ker]
    exact congrArg RingHom.ker (congrArg AlgHom.toRingHom he)
  let T := Localization.AtPrime q.asIdeal
  let L := Localization.AtPrime p.asIdeal
  let t := algebraMap k[X] T (Polynomial.X - Polynomial.C a)
  let ℓ := Localization.localRingHom q.asIdeal p.asIdeal g.toRingHom rfl
  have htarget : maximalIdeal T = Ideal.span {t} := by
    calc
      maximalIdeal T = q.asIdeal.map (algebraMap k[X] T) :=
        (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal T).symm
      _ = (Ideal.span {Polynomial.X - Polynomial.C a}).map (algebraMap k[X] T) :=
        congrArg (fun I : Ideal k[X] ↦ I.map (algebraMap k[X] T)) hq
      _ = Ideal.span {t} := by rw [Ideal.map_span, Set.image_singleton]
  obtain ⟨hsource, u, hu⟩ := fermatLastChart_branch_local_parameters hn ha
  have hsource' : maximalIdeal L = Ideal.span {algebraMap A L y₀} := hsource
  have hℓ : ℓ t = (u : L) * (algebraMap A L y₀) ^ n := by
    rw [show ℓ t = algebraMap A L (g (Polynomial.X - Polynomial.C a)) from
      Localization.localRingHom_to_map _ _ _ _ _]
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hu
  change (maximalIdeal T).map ℓ = maximalIdeal L ^ n
  rw [htarget, hsource', Ideal.map_span, Set.image_singleton, hℓ,
    Ideal.span_singleton_mul_left_unit u.isUnit, Ideal.span_singleton_pow]

/-- The ramification index of the actual Fermat projection at `(a,0)` is `n`. -/
theorem fermatProjection_ramificationIdx_at_affineBranchPoint (hn : 0 < n)
    {a : k} (ha : a ^ n = 1) :
    let p := fermatProjectionAffineBranchPoint k hn ha
    let f := fermatProjection k hn
    let R := (projectiveLine k).presheaf.stalk (f p)
    let S := (fermatProjective k n).presheaf.stalk p
    letI : Algebra R S := (f.stalkMap p).hom.toAlgebra
    (maximalIdeal S).ramificationIdx R = n := by
  dsimp only
  let p := fermatProjectionAffineBranchPoint k hn ha
  let f := fermatProjection k hn
  let R := (projectiveLine k).presheaf.stalk (f p)
  let S := (fermatProjective k n).presheaf.stalk p
  let g := (f.stalkMap p).hom
  let : Algebra R S := g.toAlgebra
  let Q := maximalIdeal S
  let L := Localization.AtPrime Q
  have : IsIntegral (fermatProjective k n) := fermatProjective_isIntegral k hn
  have : SmoothOfRelativeDimension 1 (fermatProjective k n ↘ Spec (.of k)) :=
    fermatProjective_smoothOne k hn
  have : IsDiscreteValuationRing S := isDiscreteValuationRing_stalk_of_closed_smoothCurve
    (k := k) p (isClosed_fermatProjectionAffineBranchPoint k hn ha)
  have : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
      (IsDiscreteValuationRing.not_a_field S) L
  have hmap : (maximalIdeal R).map g = Q ^ n :=
    fermatProjection_map_maximalIdeal_at_affineBranchPoint k hn ha
  have hunder : Q.under R = maximalIdeal R := maximalIdeal_comap g
  have hL : (maximalIdeal R).map (algebraMap R L) = maximalIdeal L ^ n := by
    rw [IsScalarTower.algebraMap_eq R S L, ← Ideal.map_map]
    change ((maximalIdeal R).map g).map (algebraMap S L) = _
    rw [hmap, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
  change Q.ramificationIdx R = n
  rw [Ideal.ramificationIdx_def, hunder, hL,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

end Fermat

end TinyTauDemo
