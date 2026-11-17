/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TinyTauDemo.PrimitiveFermatSolution
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TinyTauDemo.LinearFactorIdeals

/-!
# Polynomial Fermat's Last Theorem by infinite descent

Over an algebraic closure, each cyclotomic linear factor of a primitive solution is an
exact power. A linear relation between three such factors yields another primitive
solution of strictly smaller maximum coordinate degree.
See `/roadmap/index.qmd#thm-flt-poly-descent @ e6948e59762aefc93f2682cc4ae15df0e0811a14`.
-/

public section

open Polynomial

namespace TinyTauDemo

variable {k : Type*} [Field k] {n : ℕ}

/-- Distinct roots of unity are constant polynomials with a unit difference. -/
private theorem isUnit_sub_of_mem_nthRootsFinset {a b : k[X]} (hn : 0 < n)
    (ha : a ∈ nthRootsFinset n 1) (hb : b ∈ nthRootsFinset n 1) (hne : a ≠ b) :
    IsUnit (a - b) := by
  have unit_of_root {p : k[X]} (hp : p ∈ nthRootsFinset n 1) : IsUnit p := by
    apply (isUnit_pow_iff hn.ne').mp
    rw [(mem_nthRootsFinset hn 1).mp hp]
    exact isUnit_one
  have hua := unit_of_root ha
  have hub := unit_of_root hb
  obtain ⟨c, _, rfl⟩ := Polynomial.isUnit_iff.mp hua
  obtain ⟨d, _, rfl⟩ := Polynomial.isUnit_iff.mp hub
  rw [← map_sub]
  exact isUnit_C.mpr (sub_ne_zero.mpr fun h ↦ hne (congrArg C h)).isUnit

/-- Distinct linear factors built from coprime polynomials are coprime when their
coefficients differ by a unit. -/
private theorem isCoprime_sub_mul_of_isUnit_sub {x z a b : k[X]}
    (h : IsCoprime z x) (hu : IsUnit (a - b)) :
    IsCoprime (z - a * x) (z - b * x) := by
  apply Ideal.mem_span_pair.mp
  have hle := span_sub_le_span_linear_factors h.neg_right a b
  rw [Ideal.span_singleton_eq_top.mpr hu] at hle
  simpa only [mul_neg, ← sub_eq_add_neg] using hle (show (1 : k[X]) ∈ (⊤ : Ideal k[X]) by simp)

section

variable [IsAlgClosed k]

/-- A polynomial associated to a positive power over an algebraically closed field
is itself an exact power because the multiplying unit has a root. -/
private theorem exists_pow_of_associated_pow {p q : k[X]} (hn : 0 < n)
    (h : Associated (q ^ n) p) : ∃ r : k[X], r ^ n = p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, _, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  refine ⟨q * C d, ?_⟩
  rw [mul_pow, ← map_pow, hd, hcu, hu]

/-- In a pairwise coprime factorization of a polynomial power, every factor
is itself the same power over an algebraically closed coefficient field. -/
private theorem exists_pow_of_pairwise_coprime_prod_eq_pow {ι : Type*} {s : Finset ι}
    {f : ι → k[X]} {p : k[X]} (hn : 0 < n)
    (hcop : (s : Set ι).Pairwise (fun i j ↦ IsCoprime (f i) (f j)))
    (hprod : ∏ i ∈ s, f i = p ^ n) {i : ι} (hi : i ∈ s) :
    ∃ q : k[X], q ^ n = f i := by
  classical
  have hc : IsCoprime (f i) (∏ j ∈ s.erase i, f j) := by
    apply IsCoprime.prod_right
    intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    exact hcop hi hj hne.symm
  have heq : f i * (∏ j ∈ s.erase i, f j) = p ^ n :=
    (Finset.mul_prod_erase s f hi).trans hprod
  obtain ⟨q, hq⟩ := exists_associated_pow_of_mul_eq_pow' hc heq
  exact exists_pow_of_associated_pow hn hq

/-- The factors in the cyclotomic factorization of a difference of polynomial powers
are nonzero exact powers and are pairwise coprime. -/
theorem cyclotomic_factors_of_fermat_eq {x y z : k[X]} {ζ : k}
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (hcop : IsCoprime z x)
    (hy : y ≠ 0) (heq : x ^ n + y ^ n = z ^ n) :
    (∀ a ∈ nthRootsFinset n (1 : k[X]),
      ∃ q : k[X], q ≠ 0 ∧ q ^ n = z - a * x) ∧
    ((nthRootsFinset n (1 : k[X]) : Set k[X]).Pairwise
      (fun a b ↦ IsCoprime (z - a * x) (z - b * x))) := by
  have hζC := hζ.map_of_injective (C_injective (R := k))
  have hprod : ∏ a ∈ nthRootsFinset n (1 : k[X]), (z - a * x) = y ^ n := by
    rw [← hζC.pow_sub_pow_eq_prod_sub_mul z x hn, ← heq, add_sub_cancel_left]
  have hc : (nthRootsFinset n (1 : k[X]) : Set k[X]).Pairwise
      (fun a b ↦ IsCoprime (z - a * x) (z - b * x)) :=
    fun _ ha _ hb hne ↦ isCoprime_sub_mul_of_isUnit_sub hcop
      (isUnit_sub_of_mem_nthRootsFinset hn ha hb hne)
  refine ⟨?_, hc⟩
  intro a ha
  obtain ⟨q, hq⟩ := exists_pow_of_pairwise_coprime_prod_eq_pow hn hc hprod ha
  have hprod0 : (∏ a ∈ nthRootsFinset n (1 : k[X]), (z - a * x)) ≠ 0 := by
    rw [hprod]
    exact pow_ne_zero n hy
  have ha0 := Finset.prod_ne_zero_iff.mp hprod0 a ha
  exact ⟨q, fun hq0 ↦ ha0 (by simpa only [hq0, zero_pow hn.ne'] using hq.symm), hq⟩

end

private def solutionDegree (x y z : k[X]) : ℕ :=
  max x.natDegree (max y.natDegree z.natDegree)

private theorem isUnit_of_nonzero_natDegree_zero {p : k[X]} (hp : p ≠ 0)
    (hdeg : p.natDegree = 0) : IsUnit p :=
  isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hp, hdeg]; rfl)

private theorem solutionDegree_pos {x y z : k[X]} (h : PrimitiveFermatSolution n x y z) :
    0 < solutionDegree x y z := by
  by_contra! hdeg
  apply h.not_all_units
  unfold solutionDegree at hdeg
  exact ⟨isUnit_of_nonzero_natDegree_zero h.x_ne_zero (by omega),
    isUnit_of_nonzero_natDegree_zero h.y_ne_zero (by omega),
    isUnit_of_nonzero_natDegree_zero h.z_ne_zero (by omega)⟩

private theorem exists_pow_eq_C_mul [IsAlgClosed k] (hn : 0 < n) {c : k} (hc : c ≠ 0)
    {f q : k[X]} (hq0 : q ≠ 0) (hq : q ^ n = f) :
    ∃ r : k[X], r ≠ 0 ∧ r ^ n = C c * f := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  have hd0 : d ≠ 0 := fun hd0 ↦ hc (by simpa only [hd0, zero_pow hn.ne'] using hd.symm)
  refine ⟨C d * q, mul_ne_zero (C_ne_zero.mpr hd0) hq0, ?_⟩
  rw [mul_pow, ← map_pow, hd, hq]

private theorem isCoprime_of_scaled_powers (hn : 0 < n) {u v f g : k[X]} {a b : k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ^ n = C a * f) (hv : v ^ n = C b * g)
    (h : IsCoprime f g) : IsCoprime u v := by
  apply (IsCoprime.pow_iff hn hn).mp
  rw [hu, hv]
  exact (isCoprime_mul_units_left (isUnit_C.mpr ha.isUnit) (isUnit_C.mpr hb.isUnit) f g).mpr h

/-- Two constant linear factors of the original solution force all three coordinates
to be constant. -/
private theorem not_both_linear_factors_constant {x y z : k[X]}
    (h : PrimitiveFermatSolution n x y z) (hn : 0 < n) {a b : k} (hab : a ≠ b)
    (h₀ : (z - C a * x).natDegree = 0) (h₁ : (z - C b * x).natDegree = 0) : False := by
  have hxdeg : x.natDegree = 0 := by
    have hx : C (b - a) * x = (z - C a * x) - (z - C b * x) := by
      simp only [map_sub]
      ring
    have hxle := natDegree_sub_le (z - C a * x) (z - C b * x)
    rw [← hx, natDegree_C_mul (sub_ne_zero.mpr hab.symm), h₀, h₁] at hxle
    exact Nat.eq_zero_of_le_zero hxle
  have hzdeg : z.natDegree = 0 := by
    have hzle := natDegree_add_le (z - C a * x) (C a * x)
    have haxle := natDegree_C_mul_le a x
    rw [hxdeg] at haxle
    rw [sub_add_cancel, h₀, Nat.eq_zero_of_le_zero haxle] at hzle
    exact Nat.eq_zero_of_le_zero hzle
  have hydeg : y.natDegree = 0 := by
    have hy : y ^ n = z ^ n - x ^ n := by rw [← h.eq, add_sub_cancel_left]
    have hy_le := natDegree_sub_le (z ^ n) (x ^ n)
    simp only [← hy, natDegree_pow, hxdeg, hzdeg, mul_zero, max_self] at hy_le
    exact (Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hy_le)).resolve_left hn.ne'
  exact h.not_all_units ⟨isUnit_of_nonzero_natDegree_zero h.x_ne_zero hxdeg,
    isUnit_of_nonzero_natDegree_zero h.y_ne_zero hydeg,
    isUnit_of_nonzero_natDegree_zero h.z_ne_zero hzdeg⟩

private theorem exists_smaller_primitive_solution [IsAlgClosed k] [CharZero k]
    {x y z : k[X]} (hn : 3 ≤ n) (h : PrimitiveFermatSolution n x y z) :
    ∃ u v w : k[X], PrimitiveFermatSolution n u v w ∧
      solutionDegree u v w < solutionDegree x y z := by
  have hpos : 0 < n := by omega
  have : NeZero (n : k) := ⟨Nat.cast_ne_zero.mpr hpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k n
  let r (j : ℕ) := ζ ^ j
  have rmem (j : ℕ) : C (r j) ∈ nthRootsFinset n (1 : k[X]) := by
    apply (mem_nthRootsFinset hpos 1).2
    dsimp only [r]
    rw [← map_pow, ← pow_mul, Nat.mul_comm j n, pow_mul, hζ.pow_eq_one, one_pow, map_one]
  have rne {i j : ℕ} (hi : i < n) (hj : j < n) (hne : i ≠ j) : r i ≠ r j :=
    fun hij ↦ hne (hζ.pow_inj hi hj hij)
  let a := r 0
  let b := r 1
  let c := r 2
  have hab : a ≠ b := rne (by omega) (by omega) (by decide)
  have hbc : b ≠ c := rne (by omega) (by omega) (by decide)
  have hca : c ≠ a := rne (by omega) (by omega) (by decide)
  -- Select three different factors and absorb the coefficients of their linear dependence.
  obtain ⟨hpower, hcoprime⟩ := cyclotomic_factors_of_fermat_eq hpos hζ h.coprime_zx
    h.y_ne_zero h.eq
  obtain ⟨u₀, hu₀, hpow₀⟩ := hpower _ (rmem 0)
  obtain ⟨v₀, hv₀, hpow₁⟩ := hpower _ (rmem 1)
  obtain ⟨w₀, hw₀, hpow₂⟩ := hpower _ (rmem 2)
  obtain ⟨u, hu, hupow⟩ := exists_pow_eq_C_mul hpos (sub_ne_zero.mpr hbc) hu₀ hpow₀
  obtain ⟨v, hv, hvpow⟩ := exists_pow_eq_C_mul hpos (sub_ne_zero.mpr hca) hv₀ hpow₁
  obtain ⟨w, hw, hwpow⟩ := exists_pow_eq_C_mul hpos (sub_ne_zero.mpr hab.symm) hw₀ hpow₂
  -- Taking an nth root of each factor strictly reduces the maximum degree.
  have hsmall {q : k[X]} {d t : k} (hq : q ^ n = C d * (z - C t * x)) :
      q.natDegree < solutionDegree x y z := by
    have hle : n * q.natDegree ≤ solutionDegree x y z := by
      rw [← natDegree_pow, hq]
      apply (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans ?_)
      have hx := natDegree_C_mul_le t x
      unfold solutionDegree
      omega
    have hnq := Nat.mul_le_mul_right q.natDegree (show 2 ≤ n by omega)
    have hM := solutionDegree_pos h
    omega
  refine ⟨u, v, w, ?_, ?_⟩
  · refine {
      eq := ?_
      coprime_xy := ?_
      coprime_yz := ?_
      coprime_zx := ?_
      x_ne_zero := hu
      y_ne_zero := hv
      z_ne_zero := hw
      not_all_units := ?_ }
    · rw [hupow, hvpow, hwpow]
      simp only [map_sub]
      ring
    · exact isCoprime_of_scaled_powers hpos (sub_ne_zero.mpr hbc) (sub_ne_zero.mpr hca)
        hupow hvpow (hcoprime (rmem 0) (rmem 1) fun heq ↦ hab (C_injective heq))
    · exact isCoprime_of_scaled_powers hpos (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hab.symm)
        hvpow hwpow (hcoprime (rmem 1) (rmem 2) fun heq ↦ hbc (C_injective heq))
    · exact isCoprime_of_scaled_powers hpos (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hbc)
        hwpow hupow (hcoprime (rmem 2) (rmem 0) fun heq ↦ hca (C_injective heq))
    · rintro ⟨huunit, hvunit, _⟩
      apply not_both_linear_factors_constant h hpos hab
      · have hdeg := natDegree_eq_zero_of_isUnit (huunit.pow n)
        rwa [hupow, natDegree_C_mul (sub_ne_zero.mpr hbc)] at hdeg
      · have hdeg := natDegree_eq_zero_of_isUnit (hvunit.pow n)
        rwa [hvpow, natDegree_C_mul (sub_ne_zero.mpr hca)] at hdeg
  · exact max_lt_iff.mpr ⟨hsmall hupow, max_lt_iff.mpr ⟨hsmall hvpow, hsmall hwpow⟩⟩

private theorem not_primitiveFermatSolution_of_isAlgClosed [IsAlgClosed k] [CharZero k]
    {x y z : k[X]} (hn : 3 ≤ n) : ¬ PrimitiveFermatSolution n x y z := by
  classical
  intro h
  let p (d : ℕ) := ∃ u v w : k[X], PrimitiveFermatSolution n u v w ∧ solutionDegree u v w = d
  have hp : ∃ d, p d := ⟨solutionDegree x y z, x, y, z, h, rfl⟩
  obtain ⟨u, v, w, hu, hd⟩ := Nat.find_spec hp
  obtain ⟨a, b, c, hsmall, hlt⟩ := exists_smaller_primitive_solution hn hu
  have hmin := Nat.find_min' hp (show p (solutionDegree a b c) from ⟨a, b, c, hsmall, rfl⟩)
  exact (not_lt_of_ge hmin) (hd ▸ hlt)

/-- Cyclotomic factorization and descent on the largest coordinate degree rule out
primitive polynomial Fermat solutions in characteristic zero. -/
theorem not_primitiveFermatSolution_polynomial_descent [CharZero k]
    {x y z : k[X]} (hn : 3 ≤ n) : ¬ PrimitiveFermatSolution n x y z := by
  intro h
  let ι := algebraMap k (AlgebraicClosure k)
  apply not_primitiveFermatSolution_of_isAlgClosed hn
    (x := x.map ι) (y := y.map ι) (z := z.map ι)
  refine {
    eq := ?_
    coprime_xy := h.coprime_xy.map (mapRingHom ι)
    coprime_yz := h.coprime_yz.map (mapRingHom ι)
    coprime_zx := h.coprime_zx.map (mapRingHom ι)
    x_ne_zero := map_ne_zero h.x_ne_zero
    y_ne_zero := map_ne_zero h.y_ne_zero
    z_ne_zero := map_ne_zero h.z_ne_zero
    not_all_units := ?_ }
  · simpa only [Polynomial.map_add, Polynomial.map_pow] using congrArg (Polynomial.map ι) h.eq
  · rintro ⟨hx, hy, hz⟩
    exact h.not_all_units ⟨(isUnit_map ι).1 hx, (isUnit_map ι).1 hy, (isUnit_map ι).1 hz⟩

end TinyTauDemo
