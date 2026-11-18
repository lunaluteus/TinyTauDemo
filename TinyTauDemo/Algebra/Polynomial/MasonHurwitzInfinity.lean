/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The point at infinity in the Mason–Hurwitz argument

For the pairwise coprime triple `X`, `X + 1`, `2X + 1`, the rational
function `X / (2X + 1)` has residue `1 / 2` at infinity.

See `/roadmap/index.qmd#rem-mason-hurwitz-bridge` @ `d2c4d4a566aab2eb4ba61e9bb96a4fcd4b9e7eaa`.
-/

public section

open Polynomial TauCeti

namespace TinyTauDemo

/-- In characteristic zero the source point at infinity can map to a finite value
different from zero and one in the Mason–Hurwitz construction. -/
theorem exists_masonTriple_infty_residue_one_half (k : Type*) [Field k] [CharZero k] :
    ∃ (a b c : k[X]), a + b = c ∧ IsCoprime a b ∧ IsCoprime a c ∧ IsCoprime b c ∧
      max a.natDegree (max b.natDegree c.natDegree) = 1 ∧
      let f := algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) c
      ∃ hf : f ∈ (Place.infty k).integers,
        IsLocalRing.residue (Place.infty k).integers ⟨f, hf⟩ =
          Place.inftyResidueFieldEquiv k (2 : k)⁻¹ ∧
        IsLocalRing.residue (Place.infty k).integers ⟨f, hf⟩ ≠ 0 ∧
        IsLocalRing.residue (Place.infty k).integers ⟨f, hf⟩ ≠ 1 := by
  let a : k[X] := X
  let b : k[X] := X + 1
  let c : k[X] := C 2 * X + 1
  have h₂ : (2 : k) ≠ 0 := two_ne_zero
  have hc_deg : c.natDegree = 1 := by
    have hx : (C (2 : k) * X).natDegree = 1 :=
      (natDegree_C_mul_of_isUnit h₂.isUnit X).trans natDegree_X
    dsimp only [c]
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · exact hx
    · rw [natDegree_one, hx]
      decide
  have hc : c ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hc_deg
    contradiction
  have hab : IsCoprime a b := ⟨-1, 1, by dsimp [a, b]; ring⟩
  have hac : IsCoprime a c := ⟨-C 2, 1, by dsimp [a, c]; ring⟩
  have hbc : IsCoprime b c := ⟨C 2, -1, by simp only [b, c, map_ofNat]; ring⟩
  refine ⟨a, b, c, by simp only [a, b, c, map_ofNat]; ring, hab, hac, hbc, ?_, ?_⟩
  · have hbdeg : b.natDegree = 1 := by
      change (X + (1 : k[X])).natDegree = 1
      rw [← C_1, natDegree_X_add_C]
    rw [hc_deg, hbdeg]
    simp [a]
  let i := algebraMap k[X] (RatFunc k)
  let f := i a / i c
  let P := Place.infty k
  let h := algebraMap k (RatFunc k) (2 : k)⁻¹
  have hic : i c ≠ 0 := RatFunc.algebraMap_ne_zero hc
  have hh : h ≠ 0 := (map_ne_zero_iff _ (algebraMap k (RatFunc k)).injective).mpr (inv_ne_zero h₂)
  have hm : h * i c = i a + h := by
    simp only [h, i, a, c, map_add, map_mul, map_one, RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_eq_C]
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h₂, map_one, one_mul]
  have hs : f - h = -h / i c := by
    dsimp only [f]
    apply (eq_div_iff hic).mpr
    rw [sub_mul, div_mul_cancel₀ _ hic, hm]
    ring
  have hsub : P.valuation (f - h) < 1 := by
    have hn : f - h ≠ 0 := hs ▸ div_ne_zero (neg_ne_zero.mpr hh) hic
    rw [Place.valuation_infty_lt_one_iff hn, hs, RatFunc.intDegree_div (neg_ne_zero.mpr hh) hic,
      RatFunc.intDegree_neg, RatFunc.intDegree_polynomial, hc_deg]
    simp [h, RatFunc.algebraMap_eq_C]
  have hf : f ∈ P.integers := by
    have hd : f - h ∈ P.integers := P.mem_integers_iff.mpr hsub.le
    have hz : h ∈ P.integers := P.algebraMap_mem_integers ((2 : k)⁻¹)
    exact sub_add_cancel f h ▸ P.integers.add_mem _ _ hd hz
  let y : P.integers := ⟨f, hf⟩
  let z : P.integers := algebraMap k P.integers (2 : k)⁻¹
  have hyz : IsLocalRing.residue P.integers (y - z) = 0 :=
    P.residue_eq_zero_iff_valuation_lt_one.mpr (by
      change P.valuation ((y : RatFunc k) - (z : RatFunc k)) < 1
      simpa only [Place.coe_algebraMap_constants, y, z, h] using hsub)
  have hr : IsLocalRing.residue P.integers y = Place.inftyResidueFieldEquiv k (2 : k)⁻¹ := by
    rw [Place.inftyResidueFieldEquiv_apply, Place.algebraMap_residueField]
    exact sub_eq_zero.mp (by simpa only [map_sub] using hyz)
  refine ⟨hf, hr, ?_, ?_⟩
  · intro hzero
    exact inv_ne_zero h₂ ((Place.inftyResidueFieldEquiv k).injective
      ((hr.symm.trans hzero).trans (map_zero _).symm))
  · intro hone
    exact (by norm_num : (2 : k) ≠ 1) (inv_eq_one.mp ((Place.inftyResidueFieldEquiv k).injective
      ((hr.symm.trans hone).trans (map_one _).symm)))

end TinyTauDemo
