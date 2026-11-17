/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Roots of unity in the ring of integers

See `/roadmap/index.qmd#lem-kronecker-unit @ 5ad4234153507a4b6fef8ac8fd91d6c998dfc7db`.
-/

open scoped NumberField

namespace NumberField.RingOfIntegers

/-- An algebraic integer whose image under every complex embedding has norm one has
finite multiplicative order in the ring of integers. This is Mathlib's Kronecker theorem
`NumberField.Embeddings.pow_eq_one_of_norm_eq_one` transported to the integral ring. -/
public theorem isOfFinOrder_of_norm_eq_one {K : Type*} [Field K] [NumberField K] {x : 𝓞 K}
    (h : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ = 1) : IsOfFinOrder x := by
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.isIntegral_coe h
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, coe_injective (K := K) ?_⟩
  simpa only [map_pow, map_one] using hpow

end NumberField.RingOfIntegers
