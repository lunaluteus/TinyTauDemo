/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.BernoulliTeichmullerProduct
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Coefficient fields of the odd Bernoulli product

Every character modulo a prime is already defined over any field that contains
the requisite primitive root of unity. Scalar extension therefore preserves
the product of the first generalized Bernoulli numbers of the odd characters.
The p-adic realization detects prime divisibility in the scaled complex product.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9c6724bb1701e787d07354e649919213e3c27e1a`.
-/

public section

open Finset

namespace TinyTauDemo

variable {p : ℕ} [Fact p.Prime]

private theorem dirichletCharacter_card_le (F : Type*) [Field F] :
    Nat.card (DirichletCharacter F p) ≤ p - 1 := by
  classical
  let : NeZero (p - 1) := ⟨(Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'⟩
  rw [Nat.card_congr (MulChar.equiv_rootsOfUnity (ZMod p) F).toEquiv, ZMod.card_units]
  exact card_rootsOfUnity F _

private theorem dirichletCharacter_card_of_primitiveRoot (F : Type*) [Field F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p - 1)) :
    Nat.card (DirichletCharacter F p) = p - 1 := by
  classical
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  let : NeZero (p - 1) := ⟨hpos.ne'⟩
  rw [Nat.card_congr (MulChar.equiv_rootsOfUnity (ZMod p) F).toEquiv, ZMod.card_units]
  exact hζ.card_rootsOfUnity

private theorem isPrimitiveRoot_of_character_order (F : Type*) [Field F]
    {χ : DirichletCharacter F p} (hχ : orderOf χ = p - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ (p - 1) := by
  classical
  let e := MulChar.equiv_rootsOfUnity (ZMod p) F
  let ζ : (rootsOfUnity (Fintype.card (ZMod p)ˣ) F) := e χ
  have hz : orderOf ζ = p - 1 := e.orderOf_eq χ |>.trans hχ
  have hu : orderOf (ζ : Fˣ) = orderOf ζ :=
    orderOf_injective (rootsOfUnity (Fintype.card (ZMod p)ˣ) F).subtype
      Subtype.val_injective ζ
  refine ⟨((ζ : Fˣ) : F), ?_⟩
  exact IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr (hu.trans hz))

/-- The finite set of odd Dirichlet characters modulo a prime. -/
noncomputable def oddDirichletCharacters (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] :
    Finset (DirichletCharacter F p) := by
  classical
  letI := Fintype.ofFinite (DirichletCharacter F p)
  exact univ.filter DirichletCharacter.Odd

@[simp] theorem mem_oddDirichletCharacters {F : Type*} [Field F]
    {χ : DirichletCharacter F p} : χ ∈ oddDirichletCharacters p F ↔ χ.Odd := by
  classical
  simp [oddDirichletCharacters]

private theorem odd_pow_character_iff {F : Type*} [Field F] [CharZero F]
    {χ : DirichletCharacter F p} (hodd : χ.Odd) (i : ℕ) :
    (χ ^ i).Odd ↔ Odd i := by
  let u : (ZMod p)ˣ := -1
  change (χ ^ i) (u : ZMod p) = -1 ↔ _
  rw [MulChar.pow_apply_coe, show χ (u : ZMod p) = -1 from hodd]
  exact neg_one_pow_eq_neg_one_iff_odd (neg_ne_self.mpr (one_ne_zero : (1 : F) ≠ 0))

/-- A character of maximal order enumerates the odd characters by its odd powers. -/
theorem prod_oddDirichletCharacters_eq_prod_powers {F : Type*} [Field F] [CharZero F]
    {M : Type*} [CommMonoid M] {χ : DirichletCharacter F p}
    (hχ : orderOf χ = p - 1) (hodd : χ.Odd) (f : DirichletCharacter F p → M) :
    ∏ ψ ∈ oddDirichletCharacters p F, f ψ =
      ∏ i ∈ (range (p - 1)).filter Odd, f (χ ^ i) := by
  classical
  have htop : Subgroup.zpowers χ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hχ]
    exact le_antisymm (hχ ▸ (orderOf_le_card (x := χ))) (dirichletCharacter_card_le F)
  have himage :
      ((range (p - 1)).filter Odd).image (χ ^ ·) = oddDirichletCharacters p F := by
    ext ψ
    simp only [mem_image, mem_filter, mem_range, mem_oddDirichletCharacters]
    constructor
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩
      exact (odd_pow_character_iff hodd i).mpr hi
    · intro hψ
      have hmem : ψ ∈ Subgroup.zpowers χ := by simp [htop]
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hmem)
      exact ⟨i, ⟨hχ ▸ mem_range.mp hi, (odd_pow_character_iff hodd i).mp hψ⟩, rfl⟩
  rw [← himage, prod_image]
  intro a ha b hb hab
  apply pow_injOn_Iio_orderOf (x := χ) ?_ ?_ hab
  · simpa only [Set.mem_Iio, hχ] using mem_range.mp (mem_filter.mp ha).1
  · simpa only [Set.mem_Iio, hχ] using mem_range.mp (mem_filter.mp hb).1

/-- An embedding of coefficient fields carries the entire odd generalized Bernoulli product
to the target field whenever the source contains a primitive root of order p − 1. -/
theorem map_prod_oddDirichletCharacters_generalizedBernoulli {F E : Type*} [Field F] [Field E]
    [Algebra ℚ F] [Algebra ℚ E] (f : F →ₐ[ℚ] E) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (p - 1)) :
    f (∏ χ ∈ oddDirichletCharacters p F, χ.generalizedBernoulli 1) =
      ∏ χ ∈ oddDirichletCharacters p E, χ.generalizedBernoulli 1 := by
  classical
  let g : DirichletCharacter F p → DirichletCharacter E p := fun χ ↦ χ.ringHomComp f
  have hg : Function.Injective g := MulChar.injective_ringHomComp f.injective
  have hj : Function.Surjective g := ((Nat.bijective_iff_injective_and_card g).mpr
    ⟨hg, (dirichletCharacter_card_of_primitiveRoot F hζ).trans
      (dirichletCharacter_card_of_primitiveRoot E (hζ.map_of_injective f.injective)).symm⟩).2
  have hodd (χ : DirichletCharacter F p) : (g χ).Odd ↔ χ.Odd := by
    change f (χ (-1)) = -1 ↔ χ (-1) = -1
    rw [show (-1 : E) = f (-1 : F) by simp]
    exact ⟨fun h ↦ f.toRingHom.injective h, congrArg f⟩
  have himage : (oddDirichletCharacters p F).image g = oddDirichletCharacters p E := by
    ext ψ
    simp only [mem_image, mem_oddDirichletCharacters]
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      exact (hodd χ).mpr hχ
    · intro hψ
      obtain ⟨χ, rfl⟩ := hj ψ
      exact ⟨χ, (hodd χ).mp hψ, rfl⟩
  rw [map_prod, ← himage, prod_image (by exact fun _ _ _ _ h ↦ hg h)]
  exact prod_congr rfl fun χ _ ↦ χ.map_generalizedBernoulli f 1

private noncomputable def cyclotomicPrimePredAlgHom {F : Type*} [Field F] [Algebra ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ (p - 1)) : CyclotomicField (p - 1) ℚ →ₐ[ℚ] F := by
  have hn : p - 1 ≠ 0 := (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'
  letI : NeZero (p - 1) := ⟨hn⟩
  letI : NeZero ((p - 1 : ℕ) : ℚ) := ⟨by exact_mod_cast hn⟩
  letI : IsCyclotomicExtension {p - 1} ℚ (CyclotomicField (p - 1) ℚ) :=
    CyclotomicField.isCyclotomicExtension (p - 1) ℚ
  let S := IntermediateField.adjoin ℚ { x : F | ∃ n ∈ ({p - 1} : Set ℕ), n ≠ 0 ∧ x ^ n = 1 }
  letI : Algebra ℚ S := S.algebra'
  let e : CyclotomicField (p - 1) ℚ ≃ₐ[ℚ] S :=
    (IsCyclotomicExtension.nonempty_algEquiv_adjoin_of_exists_isPrimitiveRoot
      {p - 1} ℚ (CyclotomicField (p - 1) ℚ) F (fun n hn _ ↦
        ⟨ζ, (Set.mem_singleton_iff.mp hn).symm ▸ hζ⟩)).some
  exact S.val.comp e.toAlgHom

/-- The odd complex Bernoulli product and the product over odd powers of a
maximal-order p-adic character are images of a common cyclotomic element. -/
theorem exists_oddDirichletCharacters_generalizedBernoulli_common_preimage
    {χ : DirichletCharacter ℚ_[p] p} (hχ : orderOf χ = p - 1) (hodd : χ.Odd) :
    ∃ (ιC : CyclotomicField (p - 1) ℚ →ₐ[ℚ] ℂ)
      (ιp : CyclotomicField (p - 1) ℚ →ₐ[ℚ] ℚ_[p]) (b : CyclotomicField (p - 1) ℚ),
      ιC b = (∏ ψ ∈ oddDirichletCharacters p ℂ, ψ.generalizedBernoulli 1) ∧
      ιp b = ∏ i ∈ (range (p - 1)).filter Odd, (χ ^ i).generalizedBernoulli 1 := by
  let K := CyclotomicField (p - 1) ℚ
  have hn : p - 1 ≠ 0 := (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'
  let : NeZero (p - 1) := ⟨hn⟩
  let : NeZero ((p - 1 : ℕ) : ℚ) := ⟨by exact_mod_cast hn⟩
  have : IsCyclotomicExtension {p - 1} ℚ K := CyclotomicField.isCyclotomicExtension (p - 1) ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K (Set.mem_singleton _) hn
  obtain ⟨ζp, hζp⟩ := isPrimitiveRoot_of_character_order ℚ_[p] hχ
  let ιC := cyclotomicPrimePredAlgHom (Complex.isPrimitiveRoot_exp (p - 1) hn)
  let ιp := cyclotomicPrimePredAlgHom hζp
  refine ⟨ιC, ιp, ∏ ψ ∈ oddDirichletCharacters p K, ψ.generalizedBernoulli 1, ?_, ?_⟩
  · exact map_prod_oddDirichletCharacters_generalizedBernoulli ιC hζ
  · rw [map_prod_oddDirichletCharacters_generalizedBernoulli ιp hζ,
      prod_oddDirichletCharacters_eq_prod_powers hχ hodd]

/-- An integer expressed by the scaled complex odd Bernoulli product is divisible by p
exactly when a Bernoulli numerator in the irregularity range is divisible by p.
The scale may include a factor d prime to p, as in a quotient of class numbers. -/
theorem dvd_iff_bernoulli_irregular_of_complex_oddProduct_eq (hp5 : 5 ≤ p)
    {n a b d : ℕ} (hd : ¬ p ∣ d)
    (h : (2 : ℂ) ^ a * (n : ℂ) = (-1 : ℂ) ^ b * (d : ℂ) * (p : ℂ) *
      ∏ ψ ∈ oddDirichletCharacters p ℂ, ψ.generalizedBernoulli 1) :
    p ∣ n ↔ ∃ k : ℕ, 0 < k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  obtain ⟨ιC, ιp, B, hC, hp⟩ :=
    exists_oddDirichletCharacters_generalizedBernoulli_common_preimage
      (orderOf_padicTeichmullerCharacter (p := p)) (padicTeichmullerCharacter_odd (by omega))
  let K := CyclotomicField (p - 1) ℚ
  have hK : (2 : K) ^ a * (n : K) = (-1 : K) ^ b * (d : K) * (p : K) * B := by
    apply ιC.toRingHom.injective
    change ιC ((2 : K) ^ a * (n : K)) = ιC ((-1 : K) ^ b * (d : K) * (p : K) * B)
    simpa only [map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat, hC] using h
  let q : ℚ_[p] := (p : ℚ_[p]) * ∏ i ∈ (range (p - 1)).filter Odd,
    (padicTeichmullerCharacter (p := p) ^ i).generalizedBernoulli 1
  let s : ℚ_[p] := (-1 : ℚ_[p]) ^ b
  have hq : (2 : ℚ_[p]) ^ a * (n : ℚ_[p]) = s * ((d : ℚ_[p]) * q) := by
    have hh := congrArg ιp hK
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat, hp] at hh
    simpa only [mul_assoc, s, q] using hh
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  have hTwo : ((2 : ℤ_[p]) : ℚ_[p]) = (2 : ℚ_[p]) := PadicInt.coe_natCast 2
  rw [← padicTeichmuller_odd_generalizedBernoulli_product_dvd_iff hp5]
  change p ∣ n ↔ ∃ c : ℤ_[p], q = (p : ℚ_[p]) * c
  constructor
  · rintro ⟨r, rfl⟩
    have hdUnit : IsUnit (d : ℤ_[p]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast]
      exact fun hz ↦ hd ((ZMod.natCast_eq_zero_iff d p).mp hz)
    obtain ⟨u, hu⟩ := hdUnit
    let v : ℤ_[p] := (u⁻¹ : ℤ_[p]ˣ)
    have hv : (v : ℚ_[p]) * (d : ℚ_[p]) = 1 := by
      rw [← PadicInt.coe_natCast, ← hu, ← PadicInt.coe_mul]
      simp [v]
    refine ⟨(-1 : ℤ_[p]) ^ b * v * 2 ^ a * (r : ℤ_[p]), ?_⟩
    calc
      q = (s * s) * (((v : ℚ_[p]) * (d : ℚ_[p])) * q) := by rw [hs, hv, one_mul, one_mul]
      _ = (s * (v : ℚ_[p])) * (s * ((d : ℚ_[p]) * q)) := by ring
      _ = (s * (v : ℚ_[p])) * ((2 : ℚ_[p]) ^ a * (↑(p * r) : ℚ_[p])) := by rw [← hq]
      _ = _ := by
        push_cast
        dsimp only [s]
        rw [hTwo]
        ring
  · rintro ⟨c, hc⟩
    have hInt : (2 : ℤ_[p]) ^ a * (n : ℤ_[p]) =
        (-1 : ℤ_[p]) ^ b * ((d : ℤ_[p]) * ((p : ℤ_[p]) * c)) := by
      apply PadicInt.ext
      simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
        PadicInt.coe_neg, PadicInt.coe_one, hTwo, s, hc] using hq
    have hz := congrArg (PadicInt.toZMod (p := p)) hInt
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_ofNat,
      ZMod.natCast_self, zero_mul, mul_zero] at hz
    have h2 : (2 : ZMod p) ≠ 0 := by
      exact fun h ↦ Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
        ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    exact (ZMod.natCast_eq_zero_iff n p).mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero a h2))

end TinyTauDemo
