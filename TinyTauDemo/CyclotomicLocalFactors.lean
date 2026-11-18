/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Euler factors over finite abelian character groups

Evaluating characters at one group element gives each root of unity of the
appropriate order with equal multiplicity. This computes the product of the
linear Euler factors, including the Dirichlet-character specialization.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `19d05f674280fce4d59c513fd4da7aafdc84ca61`.
-/

public section

open scoped BigOperators

namespace TinyTauDemo

private theorem prod_rootsOfUnity_one_sub_mul (n : ℕ) [NeZero n] (z : ℂ) :
    ∏ᶠ u : rootsOfUnity n ℂ, (1 - (u.val : ℂ) * z) = 1 - z ^ n := by
  classical
  let ξ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hξ : IsPrimitiveRoot ξ n := Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  let a := (hξ.isUnit (NeZero.ne n)).unit
  have ha : (a : ℂ) = ξ := IsUnit.unit_spec _
  have hpa : IsPrimitiveRoot a n := (IsPrimitiveRoot.coe_units_iff.mp (ha ▸ hξ))
  let f (i : Fin n) : rootsOfUnity n ℂ :=
    ⟨a ^ (i : ℕ), (mem_rootsOfUnity _ _).mpr (by rw [pow_right_comm, hpa.pow_eq_one, one_pow])⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact hpa.pow_inj i.isLt j.isLt (congrArg Subtype.val hij)
    · intro u
      obtain ⟨i, hi, heq⟩ := hpa.eq_pow_of_mem_rootsOfUnity u.property
      exact ⟨⟨i, hi⟩, Subtype.ext heq⟩
  have hpoly := congrArg (Polynomial.eval (1 : ℂ))
    (X_pow_sub_C_eq_prod hξ (NeZero.pos n) (rfl : z ^ n = z ^ n))
  let := Fintype.ofFinite (rootsOfUnity n ℂ)
  rw [finprod_eq_prod_of_fintype, ← (Equiv.ofBijective f hf).prod_comp]
  change (∏ i : Fin n, (1 - ((a ^ (i : ℕ) : ℂˣ) : ℂ) * z)) = 1 - z ^ n
  simp only [Units.val_pow_eq_pow_val, ha]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ (1 - ξ ^ i * z)) n]
  simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, Polynomial.eval_C] using hpoly.symm

variable {G : Type*} [CommGroup G] [Finite G]

private def characterEvalRoots (g : G) : (G →* ℂˣ) →* rootsOfUnity (orderOf g) ℂ where
  toFun χ := ⟨χ g, (mem_rootsOfUnity _ _).mpr (by rw [← map_pow, pow_orderOf_eq_one, map_one])⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem characterEvalRoots_surjective (g : G) :
    Function.Surjective (characterEvalRoots g) := by
  intro u
  let a : Subgroup.zpowers g := ⟨g, Subgroup.mem_zpowers g⟩
  have ha (x : Subgroup.zpowers g) : x ∈ Subgroup.zpowers a := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, Subtype.ext hi⟩
  have hu : orderOf u.val ∣ orderOf a := by
    rw [← Subgroup.orderOf_coe, show (a : G) = g from rfl]
    exact orderOf_dvd_of_pow_eq_one ((mem_rootsOfUnity _ _).mp u.property)
  let φ := monoidHomOfForallMemZpowers ha hu
  obtain ⟨χ, hχ⟩ := MonoidHom.domRestrict_surjective ℂ (Subgroup.zpowers g) φ
  refine ⟨χ, Subtype.ext ?_⟩
  change χ g = u.val
  calc
    χ g = MonoidHom.domRestrictHom (Subgroup.zpowers g) ℂˣ χ a := rfl
    _ = u.val := by rw [hχ, monoidHomOfForallMemZpowers_apply_gen]

/-- At an unramified prime, the product of the linear factors indexed by the characters
of the finite abelian Galois group is determined by the order of its Frobenius element. -/
theorem prod_characters_one_sub_mul (g : G) (z : ℂ) :
    ∏ᶠ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z) =
      (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  classical
  let : NeZero (orderOf g) := ⟨(orderOf_pos g).ne'⟩
  let := Fintype.ofFinite (G →* ℂˣ)
  let := Fintype.ofFinite (rootsOfUnity (orderOf g) ℂ)
  let ev := characterEvalRoots g
  have hev : Function.Surjective ev := characterEvalRoots_surjective g
  have hcard := Subgroup.card_ker_mul_card_of_surjective hev
  rw [Complex.card_rootsOfUnity, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ] at hcard
  have hker : Nat.card ev.ker = Nat.card G / orderOf g := by
    rw [← hcard, Nat.mul_div_cancel _ (orderOf_pos g)]
  have hfiber (u : rootsOfUnity (orderOf g) ℂ) :
      Fintype.card { χ // ev χ = u } = Nat.card ev.ker := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hev u)
  calc
    _ = ∏ u : rootsOfUnity (orderOf g) ℂ, ∏ _χ : { χ // ev χ = u }, (1 - (u.val : ℂ) * z) := by
      rw [finprod_eq_prod_of_fintype]
      exact (Fintype.prod_fiberwise' ev (fun u ↦ 1 - (u.val : ℂ) * z)).symm
    _ = (∏ u : rootsOfUnity (orderOf g) ℂ, (1 - (u.val : ℂ) * z)) ^ (Nat.card G / orderOf g) := by
      simp only [Finset.prod_const, Finset.card_univ, hfiber, hker, Finset.prod_pow]
    _ = _ := by rw [← finprod_eq_prod_of_fintype, prod_rootsOfUnity_one_sub_mul]

/-- The product of the local Euler factors for the characters of a finite abelian
group, evaluated at one group element. -/
theorem prod_characters_localEulerFactor (g : G) (z : ℂ) :
    ∏ᶠ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)⁻¹ =
      ((1 - z ^ orderOf g) ^ (Nat.card G / orderOf g))⁻¹ := by
  rw [finprod_inv_distrib, prod_characters_one_sub_mul]

/-- The product of the Dirichlet Euler factors at a unit residue class. -/
theorem prod_dirichletCharacter_localEulerFactor {m : ℕ} [NeZero m] (u : (ZMod m)ˣ) (z : ℂ) :
    ∏ᶠ χ : DirichletCharacter ℂ m, (1 - χ u * z)⁻¹ =
      ((1 - z ^ orderOf u) ^ (m.totient / orderOf u))⁻¹ := by
  have h := prod_characters_localEulerFactor u z
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h
  rw [← h, ← finprod_comp_equiv MulChar.equivToUnitHom]
  simp only [MulChar.coe_equivToUnitHom]

end TinyTauDemo
