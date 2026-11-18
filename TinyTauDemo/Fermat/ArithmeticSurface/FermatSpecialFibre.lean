/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatCharts
import TinyTauDemo.Fermat.ArithmeticSurface.FermatProjectiveBaseChange
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.LinearAlgebra.SymmetricAlgebra.BasisComparison
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Tactic.Ring

/-!
# The characteristic-p Fermat special fibre

The Frobenius identity makes the degree-p equation the pth power of the linear
Fermat equation in characteristic p. The linear class has nilpotence index p.
The last standard affine chart detects nonreducedness. The linear Fermat scheme
maps into the characteristic-p model by a surjective closed immersion, identifying
the nilradical subscheme with the projective line. The coefficient-base-change
isomorphism gives both conclusions for the fibre of the integral model.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `2a0cfce18730a72e3af59be8ebaa793115ffd6d3`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open TauCeti TauCeti.AlgebraicGeometry TauCeti.GradedAlgebra

namespace TinyTauDemo

universe u

private theorem proj_map_surjective_of_isNilpotent_ker
    {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
    [AddSubgroupClass σ A] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hs : Function.Surjective f)
    (hker : ∀ a, f a = 0 → IsNilpotent a) :
    Surjective (Proj.map f (HomogeneousIdeal.irrelevant_le_map_of_surjective f hs)) := by
  constructor
  intro x
  let P := (show ProjectiveSpectrum 𝒜 from x).asHomogeneousIdeal
  have hP : P.toIdeal.IsPrime := inferInstance
  have hk : RingHom.ker f.toRingHom ≤ P.toIdeal := by
    intro a ha
    obtain ⟨n, hn⟩ := hker a ha
    exact hP.mem_of_pow_mem n (hn ▸ P.toIdeal.zero_mem)
  have hcomap : (P.map f).comap f = P := by
    apply HomogeneousIdeal.ext
    change (P.toIdeal.map f.toRingHom).comap f.toRingHom = P.toIdeal
    rw [Ideal.comap_map_of_surjective f.toRingHom hs, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hk]
  have hirr : ¬ HomogeneousIdeal.irrelevant ℬ ≤ P.map f := by
    intro h
    apply (show ProjectiveSpectrum 𝒜 from x).not_irrelevant_le
    change HomogeneousIdeal.irrelevant 𝒜 ≤ P
    rw [← hcomap]
    apply (HomogeneousIdeal.irrelevant_le 𝒜).mpr
    intro n hn a ha
    exact h (HomogeneousIdeal.mem_irrelevant_of_mem ℬ hn (f.map_mem ha))
  let y : ProjectiveSpectrum ℬ :=
    ⟨P.map f, Ideal.map_isPrime_of_surjective hs hk, hirr⟩
  refine ⟨show Proj ℬ from y, ?_⟩
  change y.comapFun f (HomogeneousIdeal.irrelevant_le_map_of_surjective f hs) = x
  exact ProjectiveSpectrum.ext hcomap

private theorem ker_eq_nilradical_of_surjective_closedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    [AlgebraicGeometry.IsReduced X] : f.ker = Y.nilradical := by
  have hrad : f.ker.radical = f.ker := by
    ext U : 2
    rw [Scheme.IdealSheafData.radical_ideal, f.ker_apply U]
    apply Ideal.radical_eq_iff.mpr
    rintro a ⟨n, ha⟩
    rw [RingHom.mem_ker, map_pow] at ha
    exact RingHom.mem_ker.mpr (eq_zero_of_pow_eq_zero ha)
  have hs : f.ker.support = ⊤ := by
    apply SetLike.coe_injective
    rw [f.support_ker, (show Function.Surjective f from Surjective.surj).range_eq, closure_univ]
    rfl
  rw [← Scheme.IdealSheafData.vanishingIdeal_top, ← hs,
    Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A surjective closed immersion from a reduced scheme identifies its source with
the subscheme defined by the target's nilradical. -/
private noncomputable def isoNilradicalSubschemeOfSurjectiveClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    [AlgebraicGeometry.IsReduced X] : X ≅ Y.nilradical.subscheme :=
  asIso f.toImage ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (ker_eq_nilradical_of_surjective_closedImmersion f))

section LinearCoordinate

variable (k : Type u) [Field k]

local notation "A" => MvPolynomial (Fin 3) k

private noncomputable def fermatLinearCoordinateMap : A →ₐ[k] A :=
  aeval ![X 0, X 1, fermatEquation k 1]

private theorem fermatLinearCoordinateMap_X_zero :
    fermatLinearCoordinateMap k (X 0) = X 0 := aeval_X _ _

private theorem fermatLinearCoordinateMap_X_one :
    fermatLinearCoordinateMap k (X 1) = X 1 := aeval_X _ _

private theorem fermatLinearCoordinateMap_X_two :
    fermatLinearCoordinateMap k (X 2) = fermatEquation k 1 := aeval_X _ _

private theorem fermatLinearCoordinateMap_equation :
    fermatLinearCoordinateMap k (fermatEquation k 1) = X 2 := by
  conv_lhs => rw [fermatEquation_def]
  simp only [pow_one, map_sub, map_add, fermatLinearCoordinateMap_X_zero,
    fermatLinearCoordinateMap_X_one, fermatLinearCoordinateMap_X_two, fermatEquation_def]
  ring

private theorem fermatLinearCoordinateMap_comp :
    (fermatLinearCoordinateMap k).comp (fermatLinearCoordinateMap k) = AlgHom.id k A := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change fermatLinearCoordinateMap k (fermatLinearCoordinateMap k (X 0)) = X 0
    rw [fermatLinearCoordinateMap_X_zero, fermatLinearCoordinateMap_X_zero]
  · change fermatLinearCoordinateMap k (fermatLinearCoordinateMap k (X 1)) = X 1
    rw [fermatLinearCoordinateMap_X_one, fermatLinearCoordinateMap_X_one]
  · change fermatLinearCoordinateMap k (fermatLinearCoordinateMap k (X 2)) = X 2
    rw [fermatLinearCoordinateMap_X_two, fermatLinearCoordinateMap_equation]

private noncomputable def fermatLinearCoordinateEquiv : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (fermatLinearCoordinateMap k) (fermatLinearCoordinateMap k)
    (fermatLinearCoordinateMap_comp k) (fermatLinearCoordinateMap_comp k)

private theorem fermatEquation_one_prime : Prime (fermatEquation k 1) := by
  rw [← fermatLinearCoordinateMap_X_two]
  change Prime (fermatLinearCoordinateEquiv k (X 2))
  exact (MulEquiv.prime_iff (fermatLinearCoordinateEquiv k)).2
    (MvPolynomial.prime_X (i := (2 : Fin 3)))

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def linearFermatElimination :
    MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0, X 1, X 0 + X 1]

private noncomputable def linearFermatCoordinates :
    FermatCoordinateRing k 1 →ₐ[k] MvPolynomial (Fin 2) k :=
  Ideal.Quotient.liftₐ _ (linearFermatElimination k) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [linearFermatElimination, fermatEquation_def])

@[simp] private theorem linearFermatCoordinates_mk (a : MvPolynomial (Fin 3) k) :
    linearFermatCoordinates k (Ideal.Quotient.mk (fermatIdeal k 1) a) =
      linearFermatElimination k a := rfl

private noncomputable def polynomialToLinearFermat :
    MvPolynomial (Fin 2) k →ₐ[k] FermatCoordinateRing k 1 :=
  (Ideal.Quotient.mkₐ k _).comp (rename Fin.castSucc)

private theorem linearFermatCoordinates_comp :
    (linearFermatCoordinates k).comp (polynomialToLinearFermat k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [polynomialToLinearFermat, linearFermatElimination]

private theorem polynomialToLinearFermat_comp :
    (polynomialToLinearFermat k).comp (linearFermatCoordinates k) = AlgHom.id k _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hline := (Ideal.Quotient.eq_zero_iff_mem (I := fermatIdeal k 1)).2
    (Ideal.mem_span_singleton_self (fermatEquation k 1))
  simp only [fermatEquation_def, pow_one, map_sub, map_add, sub_eq_zero] at hline
  fin_cases i <;>
    simp [polynomialToLinearFermat, linearFermatElimination, hline]

/-- Eliminating the third coordinate identifies the linear Fermat scheme with the projective
line. -/
noncomputable def fermatProjectiveOneIsoProjectiveLine :
    fermatProjective k 1 ≅ projectiveLine k := by
  let e := _root_.SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin 2))
  let forward :
      SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k) →+*ᵍ fermatGrading k 1 := {
    toRingHom := ((polynomialToLinearFermat k).comp e.toAlgHom).toRingHom
    map_mem := by
      intro n a ha
      apply mk_mem_quotientPiece
      exact ((_root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff
        k (Fin 2 → k) (Pi.basisFun k (Fin 2)) n a).2 ha).rename_isHomogeneous }
  let backward :
      fermatGrading k 1 →+*ᵍ SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k) := {
    toRingHom := (e.symm.toAlgHom.comp (linearFermatCoordinates k)).toRingHom
    map_mem := by
      intro n a ha
      obtain ⟨b, hb, rfl⟩ := (mem_quotientPiece_iff _ _).mp ha
      apply (_root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff
        k (Fin 2 → k) (Pi.basisFun k (Fin 2)) n _).1
      change (e (e.symm (linearFermatElimination k b))).IsHomogeneous n
      rw [AlgEquiv.apply_symm_apply]
      let v : Fin 3 → MvPolynomial (Fin 2) k := ![X 0, X 1, X 0 + X 1]
      have hv (i : Fin 3) : (v i).IsHomogeneous 1 := by
        fin_cases i
        · exact isHomogeneous_X k 0
        · exact isHomogeneous_X k 1
        · exact (isHomogeneous_X k 0).add (isHomogeneous_X k 1)
      change (aeval v b).IsHomogeneous n
      simpa only [one_mul] using ((mem_homogeneousSubmodule _ _).1 hb).aeval v hv }
  apply Proj.mapIso forward backward
  · intro a
    change polynomialToLinearFermat k (e (e.symm (linearFermatCoordinates k a))) = a
    rw [AlgEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (polynomialToLinearFermat_comp k) a
  · intro b
    change e.symm (linearFermatCoordinates k (polynomialToLinearFermat k (e b))) = b
    have he : linearFermatCoordinates k (polynomialToLinearFermat k (e b)) = e b :=
      DFunLike.congr_fun (linearFermatCoordinates_comp k) (e b)
    rw [he, e.symm_apply_apply]


private theorem fermatProjectiveOne_isReduced :
    AlgebraicGeometry.IsReduced (fermatProjective k 1) := by
  have hprime := fermatEquation_one_prime k
  let : (fermatIdeal k 1).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).2 hprime
  let : IsDomain (FermatCoordinateRing k 1) := Ideal.Quotient.isDomain _
  exact Proj.isReduced (𝒜 := fermatGrading k 1)

end LinearCoordinate

section PositiveCharacteristic

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- In characteristic `p`, the Fermat polynomial of degree `p` is a power of the linear
Fermat polynomial. -/
theorem fermatEquation_eq_linear_pow : fermatEquation k p = fermatEquation k 1 ^ p := by
  simp only [fermatEquation_def, pow_one, sub_pow_char, add_pow_char]

/-- The cone in characteristic `p` has the same radical ideal as the Fermat plane of degree one. -/
theorem radical_fermatIdeal_eq_linear : (fermatIdeal k p).radical = fermatIdeal k 1 := by
  have hprime := fermatEquation_one_prime k
  rw [fermatIdeal, fermatEquation_eq_linear_pow, ← Ideal.span_singleton_pow,
    Ideal.radical_pow _ (Fact.out : p.Prime).ne_zero]
  exact Ideal.radical_eq_iff.mpr ((Ideal.span_singleton_prime hprime.ne_zero).2 hprime).isRadical

/-- A linear change of variables identifies the coordinate ring with the ring cut out by `Z^p`. -/
noncomputable def fermatCoordinateRingEquiv_truncated :
    FermatCoordinateRing k p ≃ₐ[k]
      MvPolynomial (Fin 3) k ⧸ Ideal.span {(X 2 : MvPolynomial (Fin 3) k) ^ p} := by
  refine Ideal.quotientEquivAlg _ _ (fermatLinearCoordinateEquiv k) ?_
  rw [fermatIdeal, Ideal.map_span, Set.image_singleton, fermatEquation_eq_linear_pow, map_pow]
  congr 2
  exact congrArg (fun a : MvPolynomial (Fin 3) k ↦ a ^ p)
    (fermatLinearCoordinateMap_equation k).symm

private theorem mk_span_pow_pow_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {a : R} (ha : a ≠ 0) (hu : ¬ IsUnit a) {r m : ℕ} (hm : m < r) :
    (Ideal.Quotient.mk (Ideal.span {a ^ r}) a) ^ m ≠ 0 := by
  rw [← map_pow, ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    pow_dvd_pow_iff ha hu]
  exact Nat.not_le_of_lt hm

/-- The class of the linear polynomial in the characteristic-`p` Fermat cone has
nilpotence index exactly `p`. -/
theorem fermatCoordinateRing_linear_nilpotence :
    let a := Ideal.Quotient.mk (fermatIdeal k p) (fermatEquation k 1)
    a ^ p = 0 ∧ ∀ m < p, a ^ m ≠ 0 := by
  dsimp only
  rw [fermatIdeal, fermatEquation_eq_linear_pow]
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  · exact mk_span_pow_pow_ne_zero (fermatEquation_one_prime k).ne_zero
      (fermatEquation_one_prime k).not_isUnit hm

private theorem fermatIdeal_le_linear : fermatIdeal k p ≤ fermatIdeal k 1 :=
  (Ideal.le_radical).trans (radical_fermatIdeal_eq_linear k p).le

private noncomputable def fermatLinearQuotient : fermatGrading k p →+*ᵍ fermatGrading k 1 where
  toRingHom := Ideal.Quotient.factor (fermatIdeal_le_linear k p)
  map_mem := by
    intro n b hb
    obtain ⟨a, ha, rfl⟩ := (mem_quotientPiece_iff _ _).mp hb
    exact mk_mem_quotientPiece _ _ ha

private theorem fermatLinearQuotient_surjective : Function.Surjective (fermatLinearQuotient k p) :=
  Ideal.Quotient.factor_surjective (fermatIdeal_le_linear k p)

/-- The inclusion of the linear Fermat scheme into the characteristic-`p` Fermat scheme. -/
noncomputable def fermatSpecialFibreLinearInclusion :
    fermatProjective k 1 ⟶ fermatProjective k p :=
  Proj.map (fermatLinearQuotient k p)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ (fermatLinearQuotient_surjective k p))

set_option backward.isDefEq.respectTransparency false in
/-- The linear inclusion commutes with the structural maps to the coefficient field. -/
@[reassoc]
theorem fermatSpecialFibreLinearInclusion_comp_toSpec :
    fermatSpecialFibreLinearInclusion k p ≫ fermatProjectiveToSpec k p =
      fermatProjectiveToSpec k 1 := by
  unfold fermatSpecialFibreLinearInclusion fermatProjectiveToSpec
  rw [Proj.map_toSpecZero_assoc, ← Spec.map_comp]
  congr 2

instance : IsClosedImmersion (fermatSpecialFibreLinearInclusion k p) :=
  Proj.isClosedImmersion_map _ _ (fermatLinearQuotient_surjective k p)

instance : Surjective (fermatSpecialFibreLinearInclusion k p) := by
  apply proj_map_surjective_of_isNilpotent_ker _ (fermatLinearQuotient_surjective k p)
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change Ideal.Quotient.mk (fermatIdeal k 1) a = 0 → _
  intro h
  have ha := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [← radical_fermatIdeal_eq_linear k p] at ha
  obtain ⟨n, hn⟩ := ha
  exact ⟨n, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hn⟩

/-- The reduced subscheme of the characteristic-`p` Fermat scheme is the projective line. -/
noncomputable def fermatProjectiveNilradicalSubschemeIsoProjectiveLine :
    (fermatProjective k p).nilradical.subscheme ≅ projectiveLine k := by
  let := fermatProjectiveOne_isReduced k
  exact (isoNilradicalSubschemeOfSurjectiveClosedImmersion
    (fermatSpecialFibreLinearInclusion k p)).symm ≪≫ fermatProjectiveOneIsoProjectiveLine k


private theorem fermatAffineEquation_linear_last :
    fermatAffineEquation k 1 2 = X (0 : Fin 2) + X 1 - 1 := by
  have h0 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 0) = X 0 := by simp; rfl
  have h1 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 1) = X 1 := by simp; rfl
  have h2 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 2) = 1 := by simp
  change TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k 1) = _
  simp only [fermatEquation_def, pow_one, map_sub, map_add, h0, h1, h2]

/-- The last chart of the characteristic-`p` Fermat curve has a nonzero nilpotent. -/
theorem not_isReduced_fermatAffineRing_last : ¬ IsReduced (FermatAffineRing k p 2) := by
  change ¬ IsReduced (MvPolynomial (Fin 2) k ⧸ Ideal.span {fermatAffineEquation k p 2})
  have hEq : fermatAffineEquation k p 2 = (X (0 : Fin 2) + X 1 - 1) ^ p := by
    change TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k p) = _
    rw [fermatEquation_eq_linear_pow, map_pow, ← fermatAffineEquation_linear_last]
  rw [hEq]
  let a : MvPolynomial (Fin 2) k := X 0 + X 1 - 1
  have hne : a ≠ 0 := by
    intro h
    have he := congrArg (eval ![0, 0]) h
    simp [a] at he
  have hu : ¬ IsUnit a := by
    intro h
    have he := h.map (eval ![1, 0])
    simp [a] at he
  intro h
  let b := Ideal.Quotient.mk (Ideal.span {a ^ p}) a
  have hb : b ^ p = 0 := by
    dsimp only [b]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  exact (mk_span_pow_pow_ne_zero hne hu (Fact.out : p.Prime).one_lt)
    (by rw [pow_one]; exact eq_zero_of_pow_eq_zero hb)

/-- The projective Fermat scheme of degree `p` in characteristic `p` is nonreduced. -/
theorem not_isReduced_fermatProjective_charP :
    ¬ AlgebraicGeometry.IsReduced (fermatProjective k p) := by
  intro h
  have hP := isReduced_of_isOpenImmersion (fermatAffineChart k (Fact.out : p.Prime).pos 2)
  exact not_isReduced_fermatAffineRing_last k p ((affine_isReduced_iff _).mp hP)

end PositiveCharacteristic

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The base change of the integral Fermat scheme to a field of characteristic `p` is nonreduced. -/
theorem not_isReduced_fermatProjective_baseChange_charP :
    ¬ AlgebraicGeometry.IsReduced (pullback (fermatProjectiveToSpec ℤ p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
  intro h
  exact not_isReduced_fermatProjective_charP k p
    (isReduced_of_isOpenImmersion (fermatProjective_baseChangeIso k p).hom)

/-- The reduced subscheme of the actual characteristic-`p` fibre is the projective line. -/
noncomputable def fermatProjective_baseChange_charP_nilradicalSubschemeIsoProjectiveLine :
    (pullback (fermatProjectiveToSpec ℤ p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).nilradical.subscheme ≅ projectiveLine k := by
  let f := fermatSpecialFibreLinearInclusion k p ≫ (fermatProjective_baseChangeIso k p).hom
  let : IsClosedImmersion f := by
    dsimp only [f]
    infer_instance
  let : Surjective f := by
    dsimp only [f]
    infer_instance
  let := fermatProjectiveOne_isReduced k
  exact (isoNilradicalSubschemeOfSurjectiveClosedImmersion f).symm ≪≫
    fermatProjectiveOneIsoProjectiveLine k

end TinyTauDemo
