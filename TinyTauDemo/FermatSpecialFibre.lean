/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatCharts
import TinyTauDemo.ProjectiveHypersurface
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Tactic.Ring

/-!
# The characteristic-p Fermat special fibre

The Frobenius identity makes the degree-p equation the pth power of the linear
Fermat equation in characteristic p. The linear class has nilpotence index p.
The last standard affine chart detects nonreducedness on the projective scheme
and on the actual base change from the integral Fermat scheme.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `d6a1dfd0e33bc66f79ced5ef62990312885e3b1c`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace TinyTauDemo

universe u

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

variable (k : Type) [Field k] (p : ℕ)

private noncomputable def tensorFermatLastChartEquiv :
    k ⊗[ℤ] ProjectiveHypersurface.ChartRing (fermatEquation ℤ p) 2 ≃ₐ[k]
      FermatAffineRing k p 2 := by
  let A := MvPolynomial (Fin 2) ℤ
  let F := TauCeti.dehomogenize (R := ℤ) (2 : Fin 3) (fermatEquation ℤ p)
  let I : Ideal A := Ideal.span {F}
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) ℤ k
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := ℤ) k A k I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.span {fermatAffineEquation k p 2} =
    (I.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := k))).map e.toRingHom
  have hF : MvPolynomial.map (algebraMap ℤ k) F = fermatAffineEquation k p 2 := by
    dsimp only [F]
    rw [TauCeti.map_dehomogenize]
    congr 1
    simp only [fermatEquation_def, map_add, map_sub, map_pow, MvPolynomial.map_X]
  dsimp only [I]
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 2
  change fermatAffineEquation k p 2 = e (1 ⊗ₜ[ℤ] F)
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, hF]

variable [Fact p.Prime] [CharP k p]

set_option backward.isDefEq.respectTransparency false in
/-- The base change of the integral Fermat scheme to a field of characteristic `p` is nonreduced. -/
theorem not_isReduced_fermatProjective_baseChange_charP :
    ¬ AlgebraicGeometry.IsReduced (pullback (fermatProjectiveToSpec ℤ p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
  let R := ProjectiveHypersurface.ChartRing (fermatEquation ℤ p) 2
  let f := fermatProjectiveToSpec ℤ p
  let g := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
  let j : Spec (.of R) ⟶ fermatProjective ℤ p :=
    ProjectiveHypersurface.affineChart (fermatEquation_isHomogeneous ℤ p) 2
  have hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) :=
    ProjectiveHypersurface.affineChart_comp_toSpec (fermatEquation_isHomogeneous ℤ p) 2
  let e : pullback j (pullback.fst f g) ≅ Spec (.of (k ⊗[ℤ] R)) :=
    pullbackRightPullbackFstIso f g j ≪≫ pullbackSymmetry _ _ ≪≫
      pullback.congrHom rfl hj ≪≫ pullbackSpecIso ℤ k R
  have : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  intro h
  have := isReduced_of_isOpenImmersion (pullback.snd j (pullback.fst f g))
  have hS := isReduced_of_isOpenImmersion e.inv
  have : IsReduced (k ⊗[ℤ] R) := (affine_isReduced_iff _).mp hS
  exact not_isReduced_fermatAffineRing_last k p
    (isReduced_of_injective (tensorFermatLastChartEquiv k p).symm.toRingHom
      (tensorFermatLastChartEquiv k p).symm.injective)

end TinyTauDemo
