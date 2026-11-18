/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Projective.ProjectiveHypersurface
public import Mathlib.AlgebraicGeometry.Pullbacks
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Base change of projective hypersurfaces

The projective hypersurface of the coefficientwise image of a homogeneous
equation is the scheme-theoretic pullback along the map of coefficient spectra.
On each coordinate open, ordinary tensor extension of the dehomogenized
equation describes the chart, including for non-flat maps.

The proof follows Tau Ceti's `WeierstrassCurve.isPullback_projModelBaseChange`
and its chart comparison in `WeierstrassCurve.Projective.chartRingBaseChangeEquiv`,
from the dependency revision `1f9b4414105d86e487a4ac4c3d3397076a44d0d2`.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `2a0cfce18730a72e3af59be8ebaa793115ffd6d3`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open TauCeti.GradedAlgebra
open scoped TensorProduct

namespace TinyTauDemo.ProjectiveHypersurface

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {m d : ℕ}
  {F : MvPolynomial (Fin (m + 1)) R} (hF : F.IsHomogeneous d) (f : R →+* S)

local notation "F'" => MvPolynomial.map f F
local notation "hF'" => hF.map f
local notation "Q" => grading hF
local notation "Q'" => grading hF'

private noncomputable def gradedBaseChange : Q →+*ᵍ Q' where
  toRingHom := Ideal.quotientMap _ (MvPolynomial.map f) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton])
  map_mem hx := by
    obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff _ _).mp hx
    exact mk_mem_quotientPiece _ _ (hp.map f)

private theorem gradedBaseChange_mk (p : MvPolynomial (Fin (m + 1)) R) :
    gradedBaseChange hF f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

private theorem gradedBaseChange_coord (i : Fin (m + 1)) :
    gradedBaseChange hF f (coord F i) = coord F' i := by
  rw [coord, gradedBaseChange_mk, MvPolynomial.map_X]

private theorem irrelevant_le_map_gradedBaseChange :
    HomogeneousIdeal.irrelevant Q' ≤
      (HomogeneousIdeal.irrelevant Q).map (gradedBaseChange hF f) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine (irrelevant_le_span_coord hF').trans ?_
  rw [← funext (gradedBaseChange_coord hF f), Set.range_comp', ← Ideal.map_span]
  exact Ideal.map_mono <| Ideal.span_le.mpr <| Set.range_subset_iff.mpr fun i ↦
    HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (coord_mem_degree_one hF i)

/-- The projective hypersurface morphism induced by extending coefficients. -/
noncomputable def baseChangeHom : scheme hF' ⟶ scheme hF :=
  Proj.map (gradedBaseChange hF f) (irrelevant_le_map_gradedBaseChange hF f)

private noncomputable def chartRingMap (i : Fin (m + 1)) :
    ChartRing F i →+* ChartRing F' i :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton,
      TauCeti.map_dehomogenize])

private theorem chartRingMap_mk (i : Fin (m + 1)) (p : MvPolynomial (Fin m) R) :
    chartRingMap f (F := F) i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

private noncomputable def chartTensorEquiv [Algebra R S] (i : Fin (m + 1)) :
    S ⊗[R] ChartRing F i ≃ₐ[S] ChartRing (F.map (algebraMap R S)) i := by
  let A := MvPolynomial (Fin m) R
  let I : Ideal A := Ideal.span {TauCeti.dehomogenize i F}
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) R S
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S A S I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span {TauCeti.dehomogenize i (F.map (algebraMap R S))} =
    (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).map e.toRingHom
  dsimp only [I]
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 2
  change TauCeti.dehomogenize i (F.map (algebraMap R S)) = e (1 ⊗ₜ[R] TauCeti.dehomogenize i F)
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, TauCeti.map_dehomogenize]

private theorem chartTensorEquiv_tmul [Algebra R S] (i : Fin (m + 1)) (s : S)
    (x : ChartRing F i) :
    chartTensorEquiv i (s ⊗ₜ[R] x) = s • chartRingMap (algebraMap R S) i x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [chartTensorEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul, chartRingMap_mk]
  exact map_smul (Ideal.Quotient.mkₐ S _) s _

private theorem isPushout_chartRingMap (i : Fin (m + 1)) :
    IsPushout (CommRingCat.ofHom (algebraMap R (ChartRing F i))) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (chartRingMap f i))
      (CommRingCat.ofHom (algebraMap S (ChartRing F' i))) := by
  let _ : Algebra R S := f.toAlgebra
  refine (CommRingCat.isPushout_tensorProduct R S (ChartRing F i)).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (chartTensorEquiv (F := F) (S := S) i).toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    exact (chartTensorEquiv_tmul (S := S) i 1 x).trans (one_smul _ _)
  · refine CommRingCat.hom_ext (RingHom.ext fun s ↦ ?_)
    exact (chartTensorEquiv_tmul (F := F) (S := S) i s 1).trans (by
      simp [Algebra.algebraMap_eq_smul_one])

private theorem chartRingMap_awayMap (i : Fin (m + 1))
    (hh : Submonoid.powers (coord F i) ≤
      (Submonoid.powers (coord F' i)).comap (gradedBaseChange hF f))
    (z : Away Q (coord F i)) :
    awayEquivChart hF' i (HomogeneousLocalization.map (gradedBaseChange hF f) hh z) =
      chartRingMap f i (awayEquivChart hF i z) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (coord_mem_degree_one hF i) z
  obtain ⟨p, hp, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha
  have hp' : p.IsHomogeneous n := by
    simpa only [Nat.nsmul_eq_mul, mul_one, mem_homogeneousSubmodule] using hp
  have hh' : (Ideal.Quotient.mk _ p : CoordinateRing F) ∈ Q (n • 1) :=
    mk_mem_quotientPiece _ _ hp
  have hm : HomogeneousLocalization.map (gradedBaseChange hF f) hh
      (Away.mk Q (coord_mem_degree_one hF i) n (Ideal.Quotient.mk _ p) hh') =
    Away.mk Q' (coord_mem_degree_one hF' i) n
      (Ideal.Quotient.mk _ (MvPolynomial.map f p))
      (mk_mem_quotientPiece _ _ (hp.map f)) := by
    simp [Away.mk, HomogeneousLocalization.map_mk, gradedBaseChange_mk]
  rw [hm, awayEquivChart_mk hF i n p hp', awayEquivChart_mk hF' i n _ (hp'.map f),
    chartRingMap_mk, TauCeti.map_dehomogenize]

private theorem isPushout_awayMap (i : Fin (m + 1)) {s : CoordinateRing F'}
    (hs : s = coord F' i)
    (hh : Submonoid.powers (coord F i) ≤ (Submonoid.powers s).comap (gradedBaseChange hF f)) :
    IsPushout (CommRingCat.ofHom (algebraMap R (Away Q (coord F i)))) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (HomogeneousLocalization.map (gradedBaseChange hF f) hh))
      (CommRingCat.ofHom (algebraMap S (Away Q' s))) := by
  subst hs
  refine (isPushout_chartRingMap (F := F) f i).of_iso' (Iso.refl _)
    (awayEquivChart hF i).toCommRingCatIso (Iso.refl _)
    (awayEquivChart hF' i).toCommRingCatIso ?_ ?_ ?_ ?_ <;> ext z
  · exact (awayEquivChart_algebraMap hF i z).symm
  · simp
  · exact (chartRingMap_awayMap hF f i hh z).symm
  · exact (awayEquivChart_algebraMap hF' i z).symm

private theorem isPullback_awaySpec (i : Fin (m + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedBaseChange hF f) (coord F i))))
      (Spec.map (CommRingCat.ofHom (algebraMap S
        (Away Q' (gradedBaseChange hF f (coord F i))))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Away Q (coord F i)))))
      (Spec.map (CommRingCat.ofHom f)) := by
  rw [Away.map]
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_awayMap hF f i (gradedBaseChange_coord hF f i) _)

private theorem isPullback_awayι (i : Fin (m + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedBaseChange hF f) (coord F i))))
      (Proj.awayι Q' _ (GradedFunLike.map_mem _ (coord_mem_degree_one hF i)) one_pos)
      (Proj.awayι Q _ (coord_mem_degree_one hF i) one_pos) (baseChangeHom hF f) := by
  rw [baseChangeHom]
  refine IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map ..) ?_
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]

set_option backward.isDefEq.respectTransparency false in
/-- Extending the coefficients of a projective hypersurface gives its scheme-theoretic base
change, without a flatness hypothesis. -/
theorem isPullback_baseChangeHom :
    IsPullback (baseChangeHom hF f) (toSpec hF') (toSpec hF) (Spec.map (CommRingCat.ofHom f)) := by
  let 𝒰 := (Proj.affineOpenCoverOfIrrelevantLESpan Q (coord F)
    (coord_mem_degree_one hF) (fun _ ↦ one_pos) (irrelevant_le_span_coord hF)).openCover
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 fun i ↦ ?_
  change Fin (m + 1) at i
  dsimp only [𝒰, Scheme.AffineOpenCover.openCover, Scheme.AffineCover.cover,
    Proj.affineOpenCoverOfIrrelevantLESpan, Scheme.Cover.pullbackHom,
    Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  let c := (isPullback_awayι hF f i).flip
  refine (isPullback_awaySpec hF f i).of_iso c.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa only [Iso.refl_hom, Category.comp_id] using c.isoPullback_hom_snd.symm
  · rw [Iso.refl_hom, Category.comp_id, c.isoPullback_hom_fst_assoc, awayι_comp_toSpec]
  · exact (awayι_comp_toSpec hF (coord_mem_degree_one hF i) one_pos).symm
  · simp

end TinyTauDemo.ProjectiveHypersurface
