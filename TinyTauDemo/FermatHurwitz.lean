/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatRational
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import TauCeti.FieldTheory.RatFunc.Transcendental
import TinyTauDemo.FermatGenus

/-!
# The function-field Fermat obstruction

The two normalized coordinates would generate the positive-genus function field of the Fermat
curve inside the rational function field. Tau Ceti's Riemann–Hurwitz genus comparison excludes
that inclusion.
See `/roadmap/index.qmd#thm-flt-geometric @ 043043ffcec6f4232273321a224bc7d77c9ec441`.
-/

namespace TinyTauDemo

open IntermediateField
open scoped IntermediateField

variable {k : Type*} [Field k] [CharZero k]

private theorem geometricInputs {x y : RatFunc k} (hx : Transcendental k x) {n : ℕ}
    (hxy : x ^ n + y ^ n = 1) :
    let E := k⟮x, y⟯
    let a := AdjoinPair.gen₁ k x y
    let b := AdjoinPair.gen₂ k x y
    Transcendental k a ∧ (k⟮a, b⟯ : IntermediateField k E) = ⊤ ∧ a ^ n + b ^ n = 1 ∧
      FiniteDimensional E (RatFunc k) ∧ Algebra.IsSeparable E (RatFunc k) := by
  intro E a b
  have hxa : Transcendental k a :=
    (transcendental_algebraMap_iff (algebraMap E (RatFunc k)).injective).mp hx
  have hgen : k⟮a, b⟯ = ⊤ := by
    apply IntermediateField.lift_injective E
    simp only [IntermediateField.lift_adjoin, Set.image_pair, IntermediateField.lift_top]
    rfl
  have heq : a ^ n + b ^ n = 1 := by
    apply (algebraMap E (RatFunc k)).injective
    simp only [map_add, map_pow, map_one]
    exact hxy
  have hE : E ≠ ⊥ := by
    intro hbot
    have hxmem : x ∈ E := mem_adjoin_pair_left k x y
    rw [hbot, IntermediateField.mem_bot] at hxmem
    obtain ⟨c, rfl⟩ := hxmem
    exact hx (isAlgebraic_algebraMap c)
  have hX := RatFunc.IntermediateField.isAlgebraic_X hE
  let := IntermediateField.adjoin.finiteDimensional hX.isIntegral
  let : FiniteDimensional E (RatFunc k) :=
    Module.Finite.of_surjective
      (RatFunc.IntermediateField.adjoinXEquiv E).toLinearMap
      (RatFunc.IntermediateField.adjoinXEquiv E).surjective
  exact ⟨hxa, hgen, heq, inferInstance, inferInstance⟩

/-- A point on the affine Fermat curve whose first coordinate is transcendental would generate
a positive-genus subfield of the rational function field. -/
public theorem not_ratFunc_fermat_of_transcendental {x y : RatFunc k} (hx : Transcendental k x)
    {n : ℕ} (hn : 3 ≤ n) : x ^ n + y ^ n ≠ 1 := by
  intro hxy
  let E := k⟮x, y⟯
  obtain ⟨ha, hgen, hrel, hfinite, hsep⟩ := geometricInputs hx hxy
  let : FiniteDimensional E (RatFunc k) := hfinite
  let : Algebra.IsSeparable E (RatFunc k) := hsep
  have hF : TauCeti.IsFunctionField k E :=
    (TauCeti.IsFunctionField.ratFunc k).of_isAlgebraic_top
  have hnpos : 0 < n := by omega
  have hex := isIntegrallyClosedIn_of_fermatEquation hnpos ha hgen hrel
  have hgenus := genus_eq_of_fermatEquation hnpos ha hgen hrel
  have hle := TauCeti.genus_le_genus (k' := k) hF (TauCeti.IsFunctionField.ratFunc k)
    hex inferInstance
  rw [hgenus, TauCeti.genus_ratFunc] at hle
  have hm : 2 ≤ (n - 1) * (n - 2) := Nat.mul_le_mul (by omega : 2 ≤ n - 1)
    (by omega : 1 ≤ n - 2)
  omega

open Polynomial in
/-- Riemann–Hurwitz excludes a primitive Fermat solution in the polynomial ring over a field
of characteristic zero. -/
public theorem not_primitiveFermatSolution_polynomial_of_hurwitz {n : ℕ} (hn : 3 ≤ n)
    (x y z : k[X]) : ¬ PrimitiveFermatSolution n x y z := by
  intro h
  exact not_ratFunc_fermat_of_transcendental (h.transcendental_ratFunc_div (by omega))
    hn h.ratFunc_div_pow_add_div_pow

end TinyTauDemo
