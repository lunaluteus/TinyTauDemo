/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import TinyTauDemo.Fermat.Integer.PrimitiveFermatSolution

/-!
# Rational coordinates of a primitive Fermat solution

Dividing by the last coordinate puts a solution on the affine chart of the Fermat curve.
Pairwise coprimality forces the first normalized coordinate to be transcendental.
See `/roadmap/index.qmd#thm-flt-geometric @ 043043ffcec6f4232273321a224bc7d77c9ec441`.
-/

open Polynomial

namespace TinyTauDemo

variable {k : Type*} [Field k] {n : ℕ} {x y z : k[X]}

/-- The normalized rational coordinates of a primitive solution satisfy the affine Fermat
equation. -/
public theorem PrimitiveFermatSolution.ratFunc_div_pow_add_div_pow
    (h : PrimitiveFermatSolution n x y z) :
    (algebraMap k[X] (RatFunc k) x / algebraMap k[X] (RatFunc k) z) ^ n +
    (algebraMap k[X] (RatFunc k) y / algebraMap k[X] (RatFunc k) z) ^ n = 1 := by
  simp only [div_pow, ← add_div, ← map_pow, ← map_add, h.eq]
  exact div_self <|
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr (pow_ne_zero n h.z_ne_zero)

/-- The first normalized rational coordinate of a primitive solution is transcendental over the
base field. -/
public theorem PrimitiveFermatSolution.transcendental_ratFunc_div
    (h : PrimitiveFermatSolution n x y z) (hn : 0 < n) :
    Transcendental k (algebraMap k[X] (RatFunc k) x / algebraMap k[X] (RatFunc k) z) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  have hz : algebraMap k[X] (RatFunc k) z ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr h.z_ne_zero
  have hx : x = C c * z := RatFunc.algebraMap_injective k (by simpa using (div_eq_iff hz).mp hc)
  have hzu : IsUnit z := h.coprime_zx.isUnit_of_dvd ⟨C c, by simpa [mul_comm] using hx⟩
  have hcu : IsUnit c := isUnit_iff_ne_zero.mpr fun hcz ↦ h.x_ne_zero (by simp [hx, hcz])
  have hxu : IsUnit x := hx.symm ▸ ((isUnit_C.mpr hcu).mul hzu)
  obtain ⟨a, ha⟩ := natDegree_eq_zero.mp (natDegree_eq_zero_of_isUnit hxu)
  obtain ⟨b, hb⟩ := natDegree_eq_zero.mp (natDegree_eq_zero_of_isUnit hzu)
  have hy : y ^ n = z ^ n - x ^ n := by rw [← h.eq, add_comm, add_sub_cancel_right]
  have hyd : (y ^ n).natDegree = 0 := by rw [hy, ← ha, ← hb]; simp [← map_pow, ← map_sub]
  have hy0 : y.natDegree = 0 := by simpa [natDegree_pow, hn.ne'] using hyd
  have hyu : IsUnit y :=
    isUnit_iff_degree_eq_zero.mpr ((degree_eq_natDegree h.y_ne_zero).trans (by simp [hy0]))
  exact h.not_all_units ⟨hxu, hyu, hzu⟩

end TinyTauDemo
