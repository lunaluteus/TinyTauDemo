/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
public import TinyTauDemo.Fermat.Integer.PrimitiveFermatSolution
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Reduction to exponent four and odd primes

See `/roadmap/index.qmd#prp-exponent-reduction @ 35cb4ed96954440f1494cafff5328e94563abb4b`.
-/

namespace TinyTauDemo

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Raising the coordinates to a positive power preserves primitivity and yields a solution
at the corresponding divisor of the original exponent. -/
public theorem PrimitiveFermatSolution.pow {m d : ℕ} {x y z : R}
    (h : PrimitiveFermatSolution (m * d) x y z) (hd : 0 < d) :
    PrimitiveFermatSolution m (x ^ d) (y ^ d) (z ^ d) where
  eq := by simpa only [Nat.mul_comm m d, pow_mul] using h.eq
  coprime_xy := h.coprime_xy.pow
  coprime_yz := h.coprime_yz.pow
  coprime_zx := h.coprime_zx.pow
  x_ne_zero := pow_ne_zero _ h.x_ne_zero
  y_ne_zero := pow_ne_zero _ h.y_ne_zero
  z_ne_zero := pow_ne_zero _ h.z_ne_zero
  not_all_units := by simpa only [isUnit_pow_iff hd.ne'] using h.not_all_units

/-- An integral domain with no primitive solutions at exponent four or any odd prime has
no primitive solutions at any exponent at least three. -/
public theorem not_primitiveFermatSolution_of_four_and_odd_primes
    (hfour : ∀ x y z : R, ¬ PrimitiveFermatSolution 4 x y z)
    (hprimes : ∀ p : ℕ, p.Prime → Odd p → ∀ x y z : R, ¬ PrimitiveFermatSolution p x y z)
    {n : ℕ} (hn : 3 ≤ n) (x y z : R) : ¬ PrimitiveFermatSolution n x y z := by
  intro h
  have reduce {m : ℕ} (hm : m ∣ n) (hno : ∀ a b c : R, ¬ PrimitiveFermatSolution m a b c) :
      False := by
    obtain ⟨d, rfl⟩ := hm
    have hd : 0 < d := Nat.pos_of_ne_zero fun hd => by simp [hd] at hn
    exact hno _ _ _ (h.pow hd)
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn with hdiv | ⟨p, hp, hdiv, hodd⟩
  · exact reduce hdiv hfour
  · exact reduce hdiv (hprimes p hp hodd)

end TinyTauDemo
