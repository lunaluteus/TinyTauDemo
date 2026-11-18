/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import TinyTauDemo.Fermat.Integer.PrimitiveFermatSolution
import Mathlib.RingTheory.Coprime.Lemmas
import TinyTauDemo.Algebra.Polynomial.MasonStothers

/-!
# Polynomial Fermat's Last Theorem from Mason–Stothers

The degree bound applied to a primitive triple's powers contradicts the fact that taking
positive powers leaves the radical unchanged.
See `/roadmap/index.qmd#cor-flt-poly-mason @ 2cb275d155cd00febb336ca0c8bcdd1884eb5449`.
-/

namespace TinyTauDemo

open Polynomial UniqueFactorizationMonoid

/-- The Mason–Stothers bound excludes primitive Fermat solutions over characteristic-zero fields. -/
public theorem not_primitiveFermatSolution_polynomial {k : Type*} [Field k] [CharZero k]
    {n : ℕ} (hn : 3 ≤ n) (x y z : k[X]) :
    ¬ PrimitiveFermatSolution n x y z := by
  intro h
  classical
  let m := max x.natDegree (max y.natDegree z.natDegree)
  have hx : x.natDegree ≤ m := le_max_left _ _
  have hy : y.natDegree ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hz : z.natDegree ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm : 0 < m := by
    by_contra! hm
    have unit_of_natDegree_le_zero (p : k[X]) (hp : p ≠ 0) (hd : p.natDegree ≤ 0) :
        IsUnit p := by
      obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (Nat.eq_zero_of_le_zero hd)
      exact isUnit_C.mpr (C_ne_zero.mp hp).isUnit
    exact h.not_all_units ⟨
      unit_of_natDegree_le_zero _ h.x_ne_zero (hx.trans hm),
      unit_of_natDegree_le_zero _ h.y_ne_zero (hy.trans hm),
      unit_of_natDegree_le_zero _ h.z_ne_zero (hz.trans hm)⟩
  have hnpos : 0 < n := by omega
  have hdegrees : max (x ^ n).natDegree (max (y ^ n).natDegree (z ^ n).natDegree) = n * m := by
    simp only [natDegree_pow, ← max_mul_mul_left, m]
  have bound := masonStothers (pow_ne_zero n h.x_ne_zero) (pow_ne_zero n h.y_ne_zero)
    (pow_ne_zero n h.z_ne_zero) h.coprime_xy.pow h.eq
    (hdegrees.symm ▸ Nat.mul_pos hnpos hm)
  rw [hdegrees, ← mul_pow, ← mul_pow, radical_pow _ hnpos.ne'] at bound
  have hsum : (x * y * z).natDegree ≤ m + m + m := by
    rw [natDegree_mul (mul_ne_zero h.x_ne_zero h.y_ne_zero) h.z_ne_zero,
      natDegree_mul h.x_ne_zero h.y_ne_zero]
    exact Nat.add_le_add (Nat.add_le_add hx hy) hz
  have hle := Nat.mul_le_mul_right m hn
  have hbound := bound.trans (natDegree_radical_le.trans hsum)
  omega

end TinyTauDemo
