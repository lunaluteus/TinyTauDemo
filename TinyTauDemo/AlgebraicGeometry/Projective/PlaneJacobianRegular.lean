/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Projective.PlaneJacobianConverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
import TinyTauDemo.AlgebraicGeometry.Projective.PlaneJacobianIntegral
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.RingTheory.RegularLocalRing.Hypersurface
import Mathlib.Tactic.LinearCombination

/-!
# Regularity and the Jacobian criterion for projective plane curves

The degree-one expansion at an affine point detects membership in the square
of its maximal ideal. The regular local hypersurface criterion then gives the
Jacobian converse on the projective charts.

See `/roadmap/index.qmd#rem-scheme-curves-recall` @ `b66bcc7d88f40dba3595163ba382bdb7ff736e7b`.
-/

public section

open AlgebraicGeometry CategoryTheory MvPolynomial Ideal IsLocalRing
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable {k : Type u} [Field k]

private theorem mem_ker_aeval_sq_of_eval_pderiv_eq_zero
    {p : MvPolynomial (Fin 2) k} {a : Fin 2 → k} (ha : aeval a p = 0)
    (hD : ∀ i, aeval a (pderiv i p) = 0) :
    p ∈ (RingHom.ker (aeval a).toRingHom) ^ 2 := by
  classical
  let R := MvPolynomial (Fin 2) k
  let m : Ideal R := RingHom.ker (aeval a).toRingHom
  let q := Ideal.Quotient.mk (m ^ 2)
  let c := q.comp (C : k →+* R)
  let t (i : Fin 2) := q (X i - C (a i))
  have ht (i j : Fin 2) : t i * t j = 0 := by
    dsimp only [t]
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    apply Ideal.mul_mem_mul <;> change (aeval a) (_ - _) = 0
    all_goals
      simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hX (i : Fin 2) : q (X i) = c (a i) + t i := by
    simp [c, t]
  have he (f : R) : q f = c (aeval a f) + c (aeval a (pderiv 0 f)) * t 0 +
      c (aeval a (pderiv 1 f)) * t 1 := by
    induction f using MvPolynomial.induction_on with
    | C b => simp [c]
    | add x y hx hy =>
      simp only [map_add, hx, hy, add_mul]
      ring
    | mul_X x i hx =>
      rw [map_mul, hx, hX]
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
      rcases hi with rfl | rfl
      · simp only [Derivation.leibniz, smul_eq_mul, pderiv_X_self,
          pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one, mul_zero,
          map_add, map_mul, aeval_X, zero_add]
        linear_combination c (aeval a (pderiv 0 x)) * ht 0 0 +
          c (aeval a (pderiv 1 x)) * ht 1 0
      · simp only [Derivation.leibniz, smul_eq_mul, pderiv_X_self,
          pderiv_X_of_ne (by decide : (1 : Fin 2) ≠ 0), mul_one, mul_zero,
          map_add, map_mul, aeval_X, zero_add]
        linear_combination c (aeval a (pderiv 0 x)) * ht 0 1 +
          c (aeval a (pderiv 1 x)) * ht 1 1
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [ha, hD, map_zero, zero_mul, add_zero] using he p

/-- A regular localization of an affine plane hypersurface at a rational point
of a nonzero equation has a nonvanishing partial derivative. -/
theorem exists_aeval_pderiv_ne_zero_of_regular_localization
    {p : MvPolynomial (Fin 2) k} (hp : p ≠ 0) {a : Fin 2 → k}
    (P : Ideal (MvPolynomial (Fin 2) k ⧸ Ideal.span {p})) [P.IsPrime]
    (hP : P.comap (Ideal.Quotient.mk (Ideal.span {p})) = RingHom.ker (aeval a).toRingHom)
    [IsRegularLocalRing (Localization.AtPrime P)] :
    ∃ i, aeval a (pderiv i p) ≠ 0 := by
  by_contra! hD
  let R := MvPolynomial (Fin 2) k
  let J : Ideal R := Ideal.span {p}
  let Q := P.comap (Ideal.Quotient.mk J)
  let B := Localization.AtPrime Q
  let : Algebra.Smooth k R := inferInstance
  let : IsRegularRing R := TauCeti.IsRegularRing.of_smooth (R := k)
  let : IsRegularLocalRing B := IsRegularRing.isRegularLocalRing_localization Q
  have hpQ : p ∈ Q := by
    change Ideal.Quotient.mk J p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)]
    exact P.zero_mem
  have hpm : algebraMap R B p ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B Q p).mpr hpQ
  have hpB : algebraMap R B p ≠ 0 := fun h ↦ hp
    ((IsLocalization.injective B Q.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))
  have hspan : J.map (algebraMap R B) = Ideal.span {algebraMap R B p} := by
    simp [J, Ideal.map_span]
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ J) Q.primeCompl = P.primeCompl := by
    ext b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨fun ⟨a, ha, hab⟩ ↦ hab ▸ ha, fun hb ↦ ⟨b, hb, rfl⟩⟩
  have hloc : IsLocalization P.primeCompl (B ⧸ J.map (algebraMap R B)) := hsub ▸ inferInstance
  let e := (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv.symm.trans
    (IsLocalization.algEquiv P.primeCompl _ (Localization.AtPrime P)).toRingEquiv
  have hreg : IsRegularLocalRing (B ⧸ Ideal.span {algebraMap R B p}) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have hnot := (TauCeti.IsRegularLocalRing.quotient_span_singleton_iff hpm hpB).mp hreg
  apply hnot
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q B, ← Ideal.map_pow]
  apply Ideal.mem_map_of_mem
  have ha : aeval a p = 0 := RingHom.mem_ker.mp (hP ▸ hpQ)
  rw [show Q = RingHom.ker (aeval a).toRingHom from hP]
  exact mem_ker_aeval_sq_of_eval_pderiv_eq_zero ha hD

end TinyTauDemo

namespace TinyTauDemo.ProjectiveHypersurface


variable {k : Type u} [Field k] {d : ℕ} {F : MvPolynomial (Fin 3) k}
  (hF : F.IsHomogeneous d)

/-- Regular stalks of a projective plane hypersurface force the homogeneous
Jacobian criterion at each rational point. -/
theorem forall_exists_pderiv_ne_zero_of_regular_stalks (hF0 : F ≠ 0)
    (hreg : ∀ x : scheme hF, IsRegularLocalRing ((scheme hF).presheaf.stalk x)) :
    ∀ b : Fin 3 → k, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0 := by
  intro b hb₀ hb
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra! hz
    exact hb₀ (funext hz)
  let a : Fin 2 → k := fun j ↦ b (i.succAbove j) / b i
  let p := TauCeti.dehomogenize i F
  have hb' : eval b F = 0 := hb
  have ha : aeval a p = 0 := by
    change aeval a (TauCeti.dehomogenize i F) = 0
    rw [aeval_eq_eval, TauCeti.eval_dehomogenize_div i hF b hi, hb', mul_zero]
  have hp : p ≠ 0 := by
    intro he
    exact hF0 (TauCeti.dehomogenize_injOn i d hF (isHomogeneous_zero _ _ _)
      (by rw [← show p = TauCeti.dehomogenize i F from rfl, he, map_zero]))
  let A := ChartRing F i
  have hI : ∀ g ∈ Ideal.span {p}, aeval a g = 0 := by
    intro g hg
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hg
    rw [map_mul, ha, zero_mul]
  let pt : A →ₐ[k] k := Ideal.Quotient.liftₐ (Ideal.span {p}) (aeval a) hI
  let P := RingHom.ker pt.toRingHom
  let : P.IsPrime := RingHom.ker_isPrime _
  let x : Spec (.of A) := ⟨P, inferInstance⟩
  let : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk x) :=
    (isRegularLocalRing_stalk_iff_of_isOpenImmersion (affineChart hF i) x).mp
      (hreg (affineChart hF i x))
  let : IsRegularLocalRing (Localization.AtPrime P) :=
    IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of A) x).commRingCatIsoToRingEquiv
  have hP : P.comap (Ideal.Quotient.mk (Ideal.span {p})) = RingHom.ker (aeval a).toRingHom := by
    ext g
    change (pt.comp (Ideal.Quotient.mkₐ k (Ideal.span {p}))) g = 0 ↔ aeval a g = 0
    have he : pt.comp (Ideal.Quotient.mkₐ k (Ideal.span {p})) = aeval a :=
      Ideal.Quotient.liftₐ_comp _ _ hI
    rw [he]
  simpa only [aeval_eq_eval] using
    (TauCeti.exists_eval_pderiv_ne_zero_iff_dehomogenize_div i hF b hi hb').mpr
      (exists_aeval_pderiv_ne_zero_of_regular_localization hp P hP)

/-- Over an algebraically closed field, regularity of the projective plane
hypersurface is equivalent to the Jacobian criterion on rational points. -/
theorem regular_stalks_iff_forall_exists_pderiv_ne_zero [IsAlgClosed k] (hF0 : F ≠ 0) :
    (∀ x : scheme hF, IsRegularLocalRing ((scheme hF).presheaf.stalk x)) ↔
      ∀ b : Fin 3 → k, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0 := by
  refine ⟨forall_exists_pderiv_ne_zero_of_regular_stalks hF hF0, fun hJac ↦ ?_⟩
  let : Smooth (toSpec hF) := (smooth_iff_forall_exists_pderiv_ne_zero hF hF0).mpr hJac
  exact isRegularLocalRing_stalk_of_smooth (toSpec hF)

/-- Regularity and smoothness agree for a projective plane hypersurface over
an algebraically closed field. -/
theorem regular_stalks_iff_smooth [IsAlgClosed k] (hF0 : F ≠ 0) :
    (∀ x : scheme hF, IsRegularLocalRing ((scheme hF).presheaf.stalk x)) ↔ Smooth (toSpec hF) :=
  (regular_stalks_iff_forall_exists_pderiv_ne_zero hF hF0).trans
    (smooth_iff_forall_exists_pderiv_ne_zero hF hF0).symm

/-- A positive-degree projective plane hypersurface over an algebraically closed field
is an integral proper regular curve precisely when its homogeneous gradient is nowhere zero. -/
theorem isIntegral_isProper_regularCurve_iff_forall_exists_pderiv_ne_zero
    [IsAlgClosed k] (hd : 0 < d) (hF0 : F ≠ 0) :
    (IsIntegral (scheme hF) ∧ IsProper (toSpec hF) ∧ topologicalKrullDim (scheme hF) = 1 ∧
      ∀ x : scheme hF, IsRegularLocalRing ((scheme hF).presheaf.stalk x)) ↔
      ∀ b : Fin 3 → k, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0 := by
  refine ⟨fun h ↦ forall_exists_pderiv_ne_zero_of_regular_stalks hF hF0 h.2.2.2, fun hJac ↦ ?_⟩
  obtain ⟨hI, hP, _, hdim⟩ :=
    isIntegral_smoothOne_dim_of_forall_exists_pderiv_ne_zero hF hd hF0 hJac
  exact ⟨hI, hP, hdim, (regular_stalks_iff_forall_exists_pderiv_ne_zero hF hF0).mpr hJac⟩

end TinyTauDemo.ProjectiveHypersurface
