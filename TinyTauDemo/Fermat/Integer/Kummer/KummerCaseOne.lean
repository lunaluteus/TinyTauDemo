/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.RegularPrime
public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicCongruences
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Prime
import TinyTauDemo.Fermat.Integer.Kummer.UnifiedCyclotomicCoprimality
import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicUnits

/-!
# Kummer's first case

For primes above three, reduce the cyclotomic linear factor modulo the exponent
and compare it with its conjugate. The resulting relation among at most four
powers of the primitive root forces the coordinates to agree modulo the exponent.
Use cubes modulo nine for exponent three. See `/roadmap/index.qmd#thm-kummer-case-1` @
`e35b3ba0aa8b46c5d4439d13defc2c2ec6c1a0cb`.
-/

public section

open scoped NumberField
open NumberField Polynomial UniqueFactorizationMonoid

namespace TinyTauDemo

section Coefficients

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [prime : Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

private theorem coeffs_congruent_of_dvd_sum_powers (c : ℕ → ℤ)
    (hc : (p : 𝓞 K) ∣ ∑ i ∈ Finset.range p, c i • hζ.toInteger ^ i) :
    ∀ i < p, (p : ℤ) ∣ c i - c (p - 1) := by
  have hdim : hζ.integralPowerBasis.dim = p - 1 := by
    rw [hζ.integralPowerBasis_dim, Nat.totient_prime prime.out]
  -- Eliminate the last power using the geometric sum relation.
  have hgeom : ∑ i ∈ Finset.range (p - 1), hζ.toInteger ^ i = -hζ.toInteger ^ (p - 1) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Finset.sum_range_succ (fun i => hζ.toInteger ^ i),
      Nat.sub_add_cancel prime.out.pos]
    exact hζ.toInteger_isPrimitiveRoot.geom_sum_eq_zero prime.out.one_lt
  have hsum : (p : 𝓞 K) ∣
      ∑ i ∈ Finset.range (p - 1), (c i - c (p - 1)) • hζ.toInteger ^ i := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hgeom,
      smul_neg, sub_neg_eq_add]
    simpa only [← Finset.sum_range_succ, Nat.sub_add_cancel (show 1 ≤ p from prime.out.pos)]
      using hc
  intro i hi
  by_cases hil : i < p - 1
  · have hf : (p : 𝓞 K) ∣
        ∑ j : Fin hζ.integralPowerBasis.dim, (c j - c (p - 1)) • hζ.toInteger ^ (j : ℕ) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => (c j - c (p - 1)) • hζ.toInteger ^ j), hdim]
      exact hsum
    exact (natCast_dvd_sum_smul_zeta_pow_iff hζ (fun i => c i - c (p - 1))).mp hf
      ⟨i, hdim.symm ▸ hil⟩
  · have : i = p - 1 := by omega
    rw [this, sub_self]
    exact dvd_zero _

private theorem val_finEquiv (i : Fin p) : (ZMod.finEquiv p i).val = i.val := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne p)
  rfl

private theorem dvd_coeffs_of_sparse_sum
    (c : ZMod p → ℤ) (hc : (p : 𝓞 K) ∣ ∑ i : ZMod p, c i • hζ.toInteger ^ i.val)
    (hzero : ∃ i : ZMod p, c i = 0) :
    ∀ i, (p : ℤ) ∣ c i := by
  let c' (i : ℕ) := c (i : ZMod p)
  have hsum : ∑ i : ZMod p, c i • hζ.toInteger ^ i.val =
      ∑ i ∈ Finset.range p, c' i • hζ.toInteger ^ i := by
    rw [← (ZMod.finEquiv p).toEquiv.sum_comp (fun i : ZMod p => c i • hζ.toInteger ^ i.val)]
    rw [← Fin.sum_univ_eq_sum_range (fun i => c' i • hζ.toInteger ^ i) p]
    apply Finset.sum_congr rfl
    intro i _
    have he : ZMod.finEquiv p i = (i.val : ZMod p) := by
      simpa only [val_finEquiv] using (ZMod.natCast_zmod_val (ZMod.finEquiv p i)).symm
    change c (ZMod.finEquiv p i) • hζ.toInteger ^ (ZMod.finEquiv p i).val = _
    rw [val_finEquiv, he]
  have hd := coeffs_congruent_of_dvd_sum_powers hζ c' (hsum ▸ hc)
  obtain ⟨j, hj⟩ := hzero
  have h := hd j.val (ZMod.val_lt j)
  have hlast : (p : ℤ) ∣ c' (p - 1) := by
    simpa only [c', ZMod.natCast_zmod_val, hj, zero_sub, dvd_neg] using h
  intro i
  have hi := dvd_add (hd i.val (ZMod.val_lt i)) hlast
  simpa only [sub_add_cancel, c', ZMod.natCast_zmod_val] using hi

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem root_pow_add (a b : ZMod p) :
    hζ.toInteger ^ (a + b).val = hζ.toInteger ^ a.val * hζ.toInteger ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ.toInteger_isPrimitiveRoot.pow_eq_one, pow_add]

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem root_pow_natCast (n : ℕ) :
    hζ.toInteger ^ (n : ZMod p).val = hζ.toInteger ^ n := by
  rw [ZMod.val_natCast, ← pow_eq_pow_mod n hζ.toInteger_isPrimitiveRoot.pow_eq_one]

private theorem intCast_eq_of_sparse_congruence (hp : 4 < p) {x y : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (k : ZMod p)
    (h : (p : 𝓞 K) ∣ (x : 𝓞 K) + (y : 𝓞 K) * hζ.toInteger -
      (x : 𝓞 K) * hζ.toInteger ^ k.val - (y : 𝓞 K) * hζ.toInteger ^ (k - 1).val) :
    (x : ZMod p) = (y : ZMod p) := by
  let c (i : ZMod p) := (if i = 0 then x else 0) + (if i = 1 then y else 0) -
    (if i = k then x else 0) - (if i = k - 1 then y else 0)
  let S : Finset (ZMod p) := {0, 1, k, k - 1}
  have hcard : S.card ≤ 4 := by
    calc
      S.card ≤ ({1, k, k - 1} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({k, k - 1} : Finset (ZMod p)).card + 2 := by
        have := Finset.card_insert_le (1 : ZMod p) ({k, k - 1} : Finset (ZMod p))
        omega
      _ ≤ 4 := by
        have := Finset.card_insert_le k ({k - 1} : Finset (ZMod p))
        rw [Finset.card_singleton] at this
        omega
  obtain ⟨j, -, hj⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ) (by
      rw [Finset.card_univ, ZMod.card]
      exact hcard.trans_lt hp)
  have hzero : c j = 0 := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp only [c, ite_eq_right hj.1, ite_eq_right hj.2.1, ite_eq_right hj.2.2.1,
      ite_eq_right hj.2.2.2, add_zero, sub_self]
  have : Fact (1 < p) := ⟨prime.out.one_lt⟩
  have hdvd : (p : 𝓞 K) ∣ ∑ i : ZMod p, c i • hζ.toInteger ^ i.val := by
    simpa only [c, sub_smul, add_smul, ite_smul, zero_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ZMod.val_zero,
      ZMod.val_one, pow_zero, pow_one, zsmul_eq_mul, mul_one] using h
  have hd := dvd_coeffs_of_sparse_sum hζ c hdvd ⟨j, hzero⟩
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  -- The coefficient of the zeroth power cannot be x by itself.
  have hk : k = 0 ∨ k = 1 := by
    by_contra hne
    push Not at hne
    apply hx
    have hk0 : (0 : ZMod p) ≠ k := hne.1.symm
    have hk1 : (0 : ZMod p) ≠ k - 1 := fun he => hne.2 (sub_eq_zero.mp he.symm)
    simpa only [c, ite_true, eq_self, ite_eq_right h01, ite_eq_right hk0,
      ite_eq_right hk1, add_zero, sub_zero] using hd 0
  rcases hk with rfl | rfl
  · exfalso
    apply hy
    have h2 : (2 : ZMod p) ≠ 0 := by
      exact fun hn => (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p))
        ((ZMod.natCast_eq_zero_iff 2 p).mp hn)
    have h1 : (1 : ZMod p) ≠ 0 - 1 := by
      intro he
      apply h2
      calc
        2 = (1 : ZMod p) + 1 := by ring
        _ = 0 := (congrArg (· + 1) he).trans (sub_add_cancel 0 1)
    simpa only [c, ite_eq_right h01.symm, ite_true, eq_self, ite_eq_right h1,
      zero_add, sub_zero] using hd 1
  · rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa only [c, ite_true, eq_self, ite_eq_right h01, sub_self, add_zero, sub_zero] using hd 0

end Coefficients

section PrincipalPower

private theorem exists_unit_mul_pow_linear {p : ℕ} [prime : Fact p.Prime]
    (hr : RegularPrime p) {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : ℤ} (hxy : IsCoprime x y) (hz : ¬ (p : ℤ) ∣ z)
    (heq : x ^ p + y ^ p = z ^ p) :
    ∃ (u : (𝓞 (CyclotomicField p ℚ))ˣ) (a : 𝓞 (CyclotomicField p ℚ)),
      (x : 𝓞 (CyclotomicField p ℚ)) + hζ.toInteger * y = (u : 𝓞 (CyclotomicField p ℚ)) * a ^ p := by
  classical
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  let R := 𝓞 (CyclotomicField p ℚ)
  let η : R := hζ.toInteger
  let L : R := (x : R) + η * (y : R)
  let E : Ideal R := Ideal.span {1 - η}
  let I : Ideal R := Ideal.span {L}
  have hζp : IsPrimitiveRoot η p := hζ.toInteger_isPrimitiveRoot
  have hz0 : (z : R) ≠ 0 := by
    exact_mod_cast (fun h : z = 0 => hz (h.symm ▸ dvd_zero _))
  have heqR : (x : R) ^ p + (y : R) ^ p = (z : R) ^ p := by
    exact_mod_cast heq
  have hη : η ∈ nthRootsFinset p (1 : R) :=
    (mem_nthRootsFinset prime.out.pos (1 : R)).mpr hζp.pow_eq_one
  obtain ⟨a, -, -, ha⟩ :=
    cyclotomic_ideal_decomposition hr.prime hr.odd hζp (hxy.map (Int.castRingHom R)) hz0 heqR
  have hdecomp : I = (a η) ^ p * ∏ q ∈ (factorization E).support, q ^ factorization I q :=
    ha η hη
  have hprime : Prime (1 - η) := by
    simpa only [neg_sub] using Prime.neg (hζ.zeta_sub_one_prime')
  have hnotDvd : ¬ (1 - η) ∣ L := by
    intro hd
    have hsum : 1 - η ∣ (x : R) + (y : R) := by
      convert dvd_add hd (dvd_mul_right (1 - η) (y : R)) using 1
      dsimp only [L]
      ring
    have hpow : 1 - η ∣ (z : R) ^ p := by
      rw [← heqR]
      have hdiv : (x : R) + (y : R) ∣ (x : R) ^ p + (y : R) ^ p := by
        simpa only [sub_neg_eq_add, hr.odd.neg_pow] using
          (sub_dvd_pow_sub_pow (x : R) (-(y : R)) p)
      exact hsum.trans hdiv
    apply hz
    apply (IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' p hζ).mp
    simpa only [η, neg_sub] using (neg_dvd.mpr (hprime.dvd_of_dvd_pow hpow))
  have hI0 : I ≠ 0 := fun h => hnotDvd (by rw [Ideal.span_singleton_eq_bot.mp h]; exact dvd_zero _)
  have hE0 : E ≠ 0 := by
    intro h
    exact hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have hEp : E.IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hEmax : E.IsMaximal := hEp.isMaximal hE0
  -- The factor is coprime to the sole prime above the exponent.
  have hExceptional : ∏ q ∈ (factorization E).support, q ^ factorization I q = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    rw [support_factorization, Multiset.mem_toFinset] at hq
    obtain ⟨hqp, hEq⟩ := (Ideal.mem_normalizedFactors_iff hE0).mp hq
    have hqE : q = E := (hEmax.eq_of_le hqp.ne_top hEq).symm
    subst q
    have hzero : factorization I E = 0 := by
      apply Nat.eq_zero_of_not_pos
      rw [factorization_eq_count, Multiset.count_pos, Ideal.mem_normalizedFactors_iff hI0]
      exact fun h => hnotDvd (Ideal.mem_span_singleton.mp (h.2 (Ideal.mem_span_singleton_self L)))
    rw [hzero, pow_zero]
  have hI : I = (a η) ^ p := by simpa only [hExceptional, mul_one] using hdecomp
  have hpI : ((a η) ^ p).IsPrincipal := hI ▸ (inferInstance : I.IsPrincipal)
  have : (a η).IsPrincipal :=
    Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hr.coprime_classNumber hpI
  let α := Submodule.IsPrincipal.generator (a η)
  have hspan : Ideal.span {α ^ p} = Ideal.span {L} := by
    rw [← Ideal.span_singleton_pow, Ideal.span_singleton_generator]
    exact hI.symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact ⟨u, α, hu.symm.trans (mul_comm _ _)⟩

end PrincipalPower

section Congruence

open NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [prime : Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

private theorem intCast_eq_of_unit_mul_pow (hp : 4 < p) {x y : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (u : (𝓞 K)ˣ) (a : 𝓞 K)
    (heq : (x : 𝓞 K) + hζ.toInteger * y = (u : 𝓞 K) * a ^ p) :
    (x : ZMod p) = (y : ZMod p) := by
  let R := 𝓞 K
  let η : R := hζ.toInteger
  have hp2 : 2 < p := by omega
  have : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp2⟩
  let σ : R ≃+* R := ringOfIntegersComplexConj K
  let e : Rˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  have he : (e : R) = η := IsUnit.unit_spec _
  have heRoot : IsPrimitiveRoot e p := hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)
  have heTor : e ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).mpr (heRoot.isOfFinOrder (NeZero.ne p))
  have heConj : unitsComplexConj K e = e⁻¹ := unitsComplexConj_torsion K ⟨e, heTor⟩
  have hηConj : σ η * η = 1 := by
    rw [← he]
    change ((unitsComplexConj K e : Rˣ) : R) * (e : R) = 1
    rw [heConj, ← _root_.Units.val_mul, inv_mul_cancel, _root_.Units.val_one]
  obtain ⟨⟨r, w⟩, huw, -⟩ := existsUnique_root_mul_realUnit hζ hp2 u
  let W : R := ((w : realCyclotomicIntegers hζ) : R)
  have hW : σ W = W := (mem_realCyclotomicIntegers_iff hζ hp2 W).mp
    (show W ∈ realCyclotomicIntegers hζ from (w : realCyclotomicIntegers hζ).property)
  have hu : (u : R) = η ^ r.val * W := huw
  obtain ⟨b, -, -, hab⟩ := exists_int_pow_congruent hζ a
  have hL : (p : R) ∣ (x : R) + η * (y : R) - η ^ r.val * W * (b : R) := by
    change (p : R) ∣ (x : R) + hζ.toInteger * (y : R) - η ^ r.val * W * (b : R)
    rw [heq, hu, ← mul_sub]
    exact dvd_mul_of_dvd_right hab _
  have hconjL : (p : R) ∣ (x : R) + σ η * (y : R) - (σ η) ^ r.val * W * (b : R) := by
    have hn : σ (p : R) = (p : R) := map_natCast σ p
    have hi (c : ℤ) : σ (c : R) = (c : R) := map_intCast σ c
    simpa only [hn, map_sub, map_add, hi, map_mul, map_pow, hW] using map_dvd σ hL
  let n : ℕ := r.val + r.val
  have hcancel : η ^ n * (σ η) ^ r.val = η ^ r.val := by
    dsimp only [n]
    rw [pow_add, mul_assoc, ← mul_pow, mul_comm η (σ η), hηConj, one_pow, mul_one]
  -- Multiply the conjugate congruence by the square of the root factor.
  have hdiff : (p : R) ∣ (x : R) + η * (y : R) -
      η ^ n * ((x : R) + σ η * (y : R)) := by
    have h := dvd_sub hL (dvd_mul_of_dvd_right hconjL (η ^ n))
    convert h using 1
    rw [mul_sub, ← mul_assoc (η ^ n) ((σ η) ^ r.val * W) (b : R),
      ← mul_assoc (η ^ n) ((σ η) ^ r.val) W, hcancel]
    ring
  let k : ZMod p := (n : ZMod p)
  have hk : η ^ k.val = η ^ n := root_pow_natCast hζ n
  have hkSub : η ^ (k - 1).val = η ^ n * σ η := by
    have : Fact (1 < p) := ⟨prime.out.one_lt⟩
    have hmul : η ^ (k - 1).val * η = η ^ n := by
      rw [← hk]
      change hζ.toInteger ^ (k - 1).val * hζ.toInteger = hζ.toInteger ^ k.val
      simpa only [sub_add_cancel, ZMod.val_one, pow_one]
        using (root_pow_add hζ (k - 1) 1).symm
    calc
      η ^ (k - 1).val = (η ^ (k - 1).val * η) * σ η := by
        rw [mul_assoc, mul_comm η (σ η), hηConj, mul_one]
      _ = η ^ n * σ η := by rw [hmul]
  apply intCast_eq_of_sparse_congruence hζ hp hx hy k
  change (p : R) ∣ (x : R) + (y : R) * η - (x : R) * η ^ k.val -
    (y : R) * η ^ (k - 1).val
  rw [hk, hkSub]
  convert hdiff using 1
  ring

end Congruence

private theorem intCast_eq_of_fermat_pair {p : ℕ} (hr : RegularPrime p) (hp : 4 < p)
    {x y z : ℤ} (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z)
    (heq : x ^ p + y ^ p = z ^ p) : (x : ZMod p) = (y : ZMod p) := by
  have : Fact p.Prime := ⟨hr.prime⟩
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  -- Normalize this pair by its gcd, which also divides the third coordinate.
  let d : ℤ := x.gcd y
  have hdNat : 0 < x.gcd y := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hx ((Int.gcd_eq_zero_iff.mp h).1.symm ▸ dvd_zero _)
  have hd0 : d ≠ 0 := by
    change (x.gcd y : ℤ) ≠ 0
    exact_mod_cast hdNat.ne'
  have hxd : d ∣ x := Int.gcd_dvd_left x y
  have hyd : d ∣ y := Int.gcd_dvd_right x y
  have hzd : d ∣ z := by
    apply (Int.pow_dvd_pow_iff hr.prime.ne_zero).mp
    rw [← heq]
    exact dvd_add (pow_dvd_pow_of_dvd hxd p) (pow_dvd_pow_of_dvd hyd p)
  let x' := x / d
  let y' := y / d
  let z' := z / d
  have hxq : d * x' = x := Int.mul_ediv_cancel' hxd
  have hyq : d * y' = y := Int.mul_ediv_cancel' hyd
  have hzq : d * z' = z := Int.mul_ediv_cancel' hzd
  have hqeq : x' ^ p + y' ^ p = z' ^ p := by
    apply mul_left_cancel₀ (pow_ne_zero p hd0)
    rwa [mul_add, ← mul_pow, ← mul_pow, ← mul_pow, hxq, hyq, hzq]
  have hcop : IsCoprime x' y' :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hdNat)
  have hnotDvd {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hab : d * b = a) : ¬ (p : ℤ) ∣ b := by
    intro h
    exact ha (hab ▸ dvd_mul_of_dvd_right h d)
  have hroot := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  obtain ⟨u, a, ha⟩ := exists_unit_mul_pow_linear hr hroot hcop (hnotDvd hz hzq) hqeq
  have hres := intCast_eq_of_unit_mul_pow hroot hp (hnotDvd hx hxq) (hnotDvd hy hyq) u a ha
  rw [← hxq, ← hyq, Int.cast_mul, Int.cast_mul, hres]

private theorem three_case_one_of_mod_nine {x y z : ℤ} (hndvd : ¬ (3 : ℤ) ∣ x * y * z) :
    x ^ 3 + y ^ 3 + z ^ 3 ≠ 0 := by
  have cube (a : ℤ) (ha : ¬ (3 : ℤ) ∣ a) :
      (a : ZMod 9) ^ 3 = 1 ∨ (a : ZMod 9) ^ 3 = -1 := by
    have htable : ∀ r : ZMod 9, ZMod.castHom (show 3 ∣ 9 by decide) (ZMod 3) r ≠ 0 →
        r ^ 3 = 1 ∨ r ^ 3 = -1 := by decide
    apply htable
    rwa [map_intCast, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp_rw [Int.prime_three.dvd_mul, not_or] at hndvd
  apply mt (congrArg (Int.cast : ℤ → ZMod 9))
  simp only [Int.cast_add, Int.cast_pow, Int.cast_zero]
  rcases cube x hndvd.1.1 with hx | hx <;>
    rcases cube y hndvd.1.2 with hy | hy <;>
    rcases cube z hndvd.2 with hz | hz <;>
    rw [hx, hy, hz] <;> decide

/-- At a regular prime, any integer solution of the symmetric Fermat equation has a
coordinate divisible by the exponent. -/
theorem kummer_case_I {p : ℕ} (hr : RegularPrime p) {x y z : ℤ}
    (hndvd : ¬ (p : ℤ) ∣ x * y * z) : x ^ p + y ^ p + z ^ p ≠ 0 := by
  intro h
  have hx : ¬ (p : ℤ) ∣ x := fun hx => hndvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hx _) _)
  have hy : ¬ (p : ℤ) ∣ y := fun hy => hndvd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hy _) _)
  have hz : ¬ (p : ℤ) ∣ z := fun hz => hndvd (dvd_mul_of_dvd_right hz _)
  have hxy : x ^ p + y ^ p = (-z) ^ p := by
    rw [hr.odd.neg_pow]
    exact eq_neg_of_add_eq_zero_left h
  by_cases hp3 : p = 3
  · subst p
    exact three_case_one_of_mod_nine hndvd h
  have hp : 4 < p := by
    have hge := hr.prime.odd_iff.mp hr.odd
    obtain ⟨k, hk⟩ := hr.odd
    omega
  have : Fact p.Prime := ⟨hr.prime⟩
  have hxz : x ^ p + z ^ p = (-y) ^ p := by
    rw [hr.odd.neg_pow]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_right_comm] using h)
  have hrxy := intCast_eq_of_fermat_pair hr hp hx hy (fun hd => hz (dvd_neg.mp hd)) hxy
  have hrxz := intCast_eq_of_fermat_pair hr hp hx hz (fun hd => hy (dvd_neg.mp hd)) hxz
  have hsum : (x : ZMod p) + (y : ZMod p) + (z : ZMod p) = 0 := by
    have hcast := congrArg (fun a : ℤ => (a : ZMod p)) h
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_zero, ZMod.pow_card] using hcast
  rw [← hrxy, ← hrxz] at hsum
  have hmul : (3 : ZMod p) * (x : ZMod p) = 0 := by
    convert hsum using 1
    ring
  have h3 : (3 : ZMod p) ≠ 0 :=
    fun hd => (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) (by omega : 3 < p))
      ((ZMod.natCast_eq_zero_iff 3 p).mp hd)
  exact hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp ((mul_eq_zero.mp hmul).resolve_left h3))

end TinyTauDemo
