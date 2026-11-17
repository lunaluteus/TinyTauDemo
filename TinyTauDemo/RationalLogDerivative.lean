/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Logarithmic differentiation of rational functions

The polynomial derivative extends to the fraction field by localizing the map to dual numbers.
Dividing this derivative by a nonzero rational function yields an additive homomorphism on units.
-/

public section

open Polynomial

namespace RatFunc

variable {k : Type*} [Field k]

private noncomputable def polynomialJet : k[X] →ₐ[k] DualNumber (RatFunc k) where
  toFun p := TrivSqZeroExt.inl (algebraMap k[X] (RatFunc k) p) +
    TrivSqZeroExt.inr (algebraMap k[X] (RatFunc k) p.derivative)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' p q := by apply TrivSqZeroExt.ext <;> simp [-DualNumber.inr_eq_smul_eps]
  map_mul' p q := by
    apply TrivSqZeroExt.ext <;>
      simp [Polynomial.derivative_mul, -DualNumber.inr_eq_smul_eps, add_comm, mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, TrivSqZeroExt.algebraMap_eq_inl']
      exact (IsScalarTower.algebraMap_apply k k[X] (RatFunc k) r).symm
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

private noncomputable def rationalJet : RatFunc k →ₐ[k] DualNumber (RatFunc k) :=
  IsLocalization.liftAlgHom (f := polynomialJet) fun p : nonZeroDivisors k[X] => by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    simp [polynomialJet]

@[simp]
private theorem rationalJet_algebraMap (p : k[X]) :
    rationalJet (algebraMap k[X] (RatFunc k) p) = polynomialJet p := by
  rw [rationalJet, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  rfl

@[simp]
private theorem rationalJet_fst (f : RatFunc k) : (rationalJet f).fst = f := by
  have h : (TrivSqZeroExt.fstHom k (RatFunc k) (RatFunc k)).comp rationalJet =
      AlgHom.id k (RatFunc k) := by
    apply IsLocalization.algHom_ext (nonZeroDivisors k[X])
    apply AlgHom.ext
    intro p
    change (rationalJet (algebraMap k[X] (RatFunc k) p)).fst = algebraMap k[X] (RatFunc k) p
    simp [polynomialJet]
  exact DFunLike.congr_fun h f

/-- The derivation on the rational function field which extends polynomial differentiation. -/
noncomputable def derivative : Derivation k (RatFunc k) (RatFunc k) where
  toLinearMap :=
    { toFun f := (rationalJet f).snd
      map_add' f g := by simp
      map_smul' a f := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes]
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl'] }
  map_one_eq_zero' := by simp
  leibniz' f g := by simp [smul_eq_mul, mul_comm]

@[simp]
theorem derivative_algebraMap (p : k[X]) :
    derivative (algebraMap k[X] (RatFunc k) p) =
      algebraMap k[X] (RatFunc k) p.derivative := by
  simp [derivative, polynomialJet, -DualNumber.inr_eq_smul_eps]

/-- The logarithmic derivative is the additive homomorphism on nonzero rational functions
whose value at `f` is `f' / f`. -/
noncomputable def logDerivative : Additive (RatFunc k)ˣ →+ RatFunc k where
  toFun f := derivative (f.toMul : RatFunc k) / f.toMul
  map_zero' := by simp
  map_add' f g := by
    change derivative ((f.toMul : RatFunc k) * (g.toMul : RatFunc k)) /
      ((f.toMul : RatFunc k) * (g.toMul : RatFunc k)) =
      derivative (f.toMul : RatFunc k) / f.toMul +
        derivative (g.toMul : RatFunc k) / g.toMul
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    field_simp [Units.ne_zero f.toMul, Units.ne_zero g.toMul]
    ring

@[simp]
theorem logDerivative_algebraMap (p : k[X]) (hp : p ≠ 0) :
    logDerivative (Additive.ofMul (Units.mk0 _ (RatFunc.algebraMap_ne_zero hp))) =
      algebraMap k[X] (RatFunc k) p.derivative / algebraMap k[X] (RatFunc k) p := by
  simp [logDerivative]

end RatFunc
