/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.KummerBernoulliCongruence
import TinyTauDemo.BernoulliExamples
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.ZetaValues

/-!
# Infinitely many primes satisfying the Bernoulli numerator test

The auxiliary indices in Jensen's argument have denominator six and
numerator congruent to three modulo four. Kummer's congruence produces
a prime outside any prescribed finite set and reduces the index to
the range of the Bernoulli numerator test.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `60aea9909644d4d0d0ae3a81b56460003cbcd3b6`.
-/

public section

open Finset

namespace TinyTauDemo

private theorem vonStaudtPrimes_eq_two_three {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    (range (2 * q + 2)).filter (fun p ↦ p.Prime ∧ (p - 1) ∣ 2 * q) = {2, 3} := by
  ext p
  simp only [mem_filter, mem_range, mem_insert, mem_singleton]
  have hq2 := hq.two_le
  constructor
  · rintro ⟨_, hp, hdvd⟩
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · right
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
      have he : p - 1 = 2 * t := by omega
      rw [he, Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)] at hdvd
      rcases (Nat.dvd_prime hq).mp hdvd with ht1 | htq
      · omega
      · have hp3 : 3 ∣ p := by omega
        exact (hp.dvd_iff_eq (by decide : 3 ≠ 1)).mp hp3
  · rintro (rfl | rfl)
    · exact ⟨by omega, Nat.prime_two, by simp⟩
    · exact ⟨by omega, Nat.prime_three, by simp⟩

/-- Jensen's auxiliary index twice a prime congruent to one modulo three
has Bernoulli denominator exactly six. -/
theorem bernoulli_den_two_mul_prime_eq_six {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    (bernoulli (2 * q)).den = 6 := by
  obtain ⟨a, ha⟩ := Bernoulli.vonStaudt_clausen q
  rw [vonStaudtPrimes_eq_two_three hq hq3, sum_insert (by decide)] at ha
  norm_num at ha
  have he : bernoulli (2 * q) = -((5 / 6 : ℚ) - (a : ℚ)) := by linarith
  rw [he, Rat.neg_den, Rat.sub_intCast_den]
  norm_num

private local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private abbrev twoIntegrals : Subring ℚ := (Rat.padicValuation 2).integer

private theorem faulhaber_four_lower_terms_mem_twoIntegrals {k : ℕ} (hk : 1 < k) :
    (∑ i ∈ range (2 * k), bernoulli i * ((2 * k + 1).choose i) *
      (4 : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1) / 16) ∈ twoIntegrals := by
  apply Subring.sum_mem
  intro i hi
  have hi' := mem_range.mp hi
  by_cases hit : i + 1 = 2 * k
  · have ho : Odd i := ⟨k - 1, by omega⟩
    simp [bernoulli_eq_zero_of_odd ho (by omega), twoIntegrals]
  · let e := 2 * k - i - 2
    have he : 2 * k + 1 - i = e + 3 := by omega
    have hterm :
        bernoulli i * ((2 * k + 1).choose i) *
            (4 : ℚ) ^ (2 * k + 1 - i) / (2 * k + 1) / 16 =
          ((2 : ℚ) * bernoulli i) * (2 * 4 ^ e * ((2 * k + 1).choose i)) *
            ((2 * k + 1 : ℚ)⁻¹) := by
      rw [he, pow_add]
      ring
    rw [hterm]
    apply mul_mem
    · apply mul_mem (mul_bernoulli_mem_pIntegrals (p := 2) i)
      exact mul_mem (mul_mem (natCast_mem _ 2) (pow_mem (natCast_mem _ 4) _)) (natCast_mem _ _)
    · change (Rat.padicValuation 2) ((2 * k + 1 : ℚ)⁻¹) ≤ 1
      have hh : (2 * k + 1 : ℚ)⁻¹ = (((2 * k + 1 : ℕ) : ℚ))⁻¹ := by push_cast; rfl
      rw [hh, Rat.padicValuation_le_one_iff, Rat.inv_natCast_den_of_pos (by omega)]
      omega

private theorem faulhaber_four_mem_twoIntegrals {k : ℕ} (hk : 1 < k) :
    (((∑ j ∈ range 4, (j : ℚ) ^ (2 * k)) - 4 * bernoulli (2 * k)) / 16) ∈
      twoIntegrals := by
  rw [sum_range_pow, sum_range_succ, Nat.choose_succ_self_right,
    show 2 * k + 1 - 2 * k = 1 by omega]
  push_cast
  have hlast : bernoulli (2 * k) * (2 * k + 1 : ℚ) * (4 : ℚ) ^ 1 /
      (2 * k + 1 : ℚ) = 4 * bernoulli (2 * k) := by
    have hne : (2 * k + 1 : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hlast, add_sub_cancel_right, sum_div]
  exact faulhaber_four_lower_terms_mem_twoIntegrals hk

private theorem sixteen_dvd_of_div_mem_twoIntegrals (a : ℤ)
    (h : (a : ℚ) / 16 ∈ twoIntegrals) : (16 : ℤ) ∣ a := by
  change (Rat.padicValuation 2) ((a : ℚ) / 16) ≤ 1 at h
  rw [Rat.padicValuation_le_one_iff] at h
  have hd : ((a : ℚ) / 16).den ∣ 16 := by
    exact_mod_cast (show (((a : ℚ) / 16).den : ℤ) ∣ (16 : ℤ) by
      simpa [Rat.divInt_eq_div] using Rat.den_dvd a 16)
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show ((a : ℚ) / 16).den ∣ 2 ^ 4 from hd)
  have hden : ((a : ℚ) / 16).den = 1 := by
    cases e with
    | zero => simpa using he
    | succ e => exact (h (he ▸ dvd_pow_self _ (by omega))).elim
  exact (Rat.den_div_intCast_eq_one_iff a 16 (by decide)).mp hden

private theorem six_mul_powerSum_zmod_sixteen {k : ℕ} (hk : 1 < k) :
    (6 : ZMod 16) * ∑ j ∈ range 4, (j : ZMod 16) ^ (2 * k) = 12 := by
  have h2 : (2 : ZMod 16) ^ (2 * k) = 0 := by
    rw [show 2 * k = 4 + (2 * k - 4) by omega, pow_add]
    have h : (2 : ZMod 16) ^ 4 = 0 := by decide
    rw [h, zero_mul]
  have h9 : ∀ n : ℕ, (6 : ZMod 16) * 9 ^ n = 6 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih]; decide
  have h3 : (6 : ZMod 16) * (3 : ZMod 16) ^ (2 * k) = 6 := by
    rw [pow_mul]
    exact h9 k
  simp only [sum_range_succ, sum_range_zero, Nat.cast_one, one_pow, zero_add]
  norm_num only [Nat.cast_ofNat]
  rw [zero_pow (by omega : 2 * k ≠ 0), zero_add, h2, add_zero, mul_add, mul_one, h3]
  decide

/-- At the auxiliary indices used by Jensen, the numerator is three modulo four. -/
theorem bernoulli_num_two_mul_prime_mod_four {q : ℕ} (hq : q.Prime) (hq3 : q % 3 = 1) :
    (bernoulli (2 * q)).num ≡ 3 [ZMOD 4] := by
  have hq2 : 1 < q := hq.one_lt
  let B := bernoulli (2 * q)
  let N := B.num
  let S := ∑ j ∈ range 4, (j : ℤ) ^ (2 * q)
  have hB : B = (N : ℚ) / 6 := by
    rw [← Rat.num_div_den B, show B.den = 6 from bernoulli_den_two_mul_prime_eq_six hq hq3]
    rfl
  have h := mul_mem (natCast_mem twoIntegrals 6) (faulhaber_four_mem_twoIntegrals hq2)
  have hcast : ((6 * S - 4 * N : ℤ) : ℚ) / 16 ∈ twoIntegrals := by
    push_cast [S]
    change (6 * (∑ j ∈ range 4, (j : ℚ) ^ (2 * q)) - 4 * (N : ℚ)) / 16 ∈ _
    have he : (6 * (∑ j ∈ range 4, (j : ℚ) ^ (2 * q)) - 4 * (N : ℚ)) / 16 =
        6 * (((∑ j ∈ range 4, (j : ℚ) ^ (2 * q)) - 4 * B) / 16) := by
      rw [hB]
      ring
    rw [he]
    exact h
  have hdiv := sixteen_dvd_of_div_mem_twoIntegrals (6 * S - 4 * N) hcast
  have hpow : ((6 * S : ℤ) : ZMod 16) = (12 : ZMod 16) := by
    push_cast [S]
    exact six_mul_powerSum_zmod_sixteen hq2
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (6 * S) 12 16).mp hpow
  change (16 : ℤ) ∣ 12 - 6 * S at hd
  rw [Int.modEq_iff_dvd]
  change (4 : ℤ) ∣ 3 - N
  apply Int.dvd_of_mul_dvd_mul_left (by decide : (4 : ℤ) ≠ 0)
  change (16 : ℤ) ∣ 4 * (3 - N)
  have hsum := dvd_add hd hdiv
  rwa [show (12 - 6 * S) + (6 * S - 4 * N) = 4 * (3 - N) by ring] at hsum

private theorem exists_prime_mod_four_dvd {n : ℕ} (hn : n % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ p ∣ n := by
  classical
  have hn0 : n ≠ 0 := by omega
  by_contra! h
  have hpone (p : ℕ) (hp : p ∈ n.primeFactors) : (p : ZMod 4) = 1 := by
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hmod : p % 4 = 1 := by
      have ho := hpp.odd_of_ne_two hp2
      have hp3 : p % 4 ≠ 3 := fun hp3 ↦ h p hpp hp3 hpd
      rw [Nat.odd_iff] at ho
      have hmod := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4)
      omega
    apply (ZMod.natCast_eq_natCast_iff p 1 4).mpr
    exact hmod
  have hcast : (n : ZMod 4) = 1 := by
    calc
      (n : ZMod 4) = (∏ p ∈ n.primeFactors, (p : ZMod 4) ^ n.factorization p) := by
        have h := congrArg (Nat.castRingHom (ZMod 4))
          (Nat.prod_primeFactors_pow_factorization hn0)
        rwa [map_prod, Finset.prod_congr rfl (fun _ _ ↦ map_pow _ _ _)] at h
      _ = 1 := prod_eq_one fun p hp ↦ by rw [hpone p hp, one_pow]
  have hmod := (ZMod.natCast_eq_natCast_iff n 1 4).mp hcast
  change n % 4 = 1 at hmod
  omega

/-- Bernoulli irregularity is a numerator divisibility test at a positive even
index strictly below one less than the prime. -/
def BernoulliIrregular (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k : ℕ, 0 < k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num

/-- The numerator divisibility condition for Bernoulli irregularity. -/
theorem bernoulliIrregular_iff {p : ℕ} :
    BernoulliIrregular p ↔
      p.Prime ∧ ∃ k : ℕ, 0 < k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
  Iff.rfl

private theorem bernoulliIrregular_prime_ge_five {p : ℕ} (hp : BernoulliIrregular p) :
    5 ≤ p := by
  obtain ⟨hp, k, hk, hkp, _⟩ := hp
  omega

private theorem irregular_of_dvd_bernoulli_num_of_coprime_index
    {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 0 < q)
    (hpq : ¬ p ∣ 2 * q) (hd : (p : ℤ) ∣ (bernoulli (2 * q)).num) :
    BernoulliIrregular p := by
  let : Fact p.Prime := ⟨hp⟩
  have hodd := hp.odd_of_ne_two (by omega)
  obtain ⟨d, hd'⟩ := hodd
  let k := q % d
  have hdmod : p - 1 = 2 * d := by omega
  have hdpos : 0 < d := by omega
  have hk : k < d := Nat.mod_lt _ hdpos
  have hkq : k ≤ q := Nat.mod_le _ _
  have hdecomp : q = k + d * (q / d) := (Nat.mod_add_div q d).symm
  have hdvd : (p - 1) ∣ 2 * q - 2 * k := by
    use q / d
    rw [hdmod, mul_assoc]
    omega
  have hk' : ¬ (p - 1) ∣ 2 * q := fun h ↦ Bernoulli.not_dvd_num_bernoulli hq h hd
  have hk0 : 0 < k := by
    by_contra! he
    exact hk' (by simpa [Nat.eq_zero_of_le_zero he] using hdvd)
  have hkm : ¬ (p - 1) ∣ 2 * k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hkp : ¬ p ∣ 2 * k := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  refine ⟨hp, k, hk0, by omega, ?_⟩
  exact (dvd_bernoulli_num_iff_of_congruent_even_indices hp5 hk0 hkq hdvd hkm hpq hkp).mp hd

private theorem bernoulli_pos_of_odd {k : ℕ} (hk : Odd k) : 0 < bernoulli (2 * k) := by
  have hk0 : k ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd 0) hk
  have hs := hasSum_zeta_nat hk0
  have hsum := hs.summable.tsum_pos (fun n ↦ by positivity) (1 : ℕ) (by simp)
  rw [hs.tsum_eq, (show Even (k + 1) from hk.add_odd odd_one).neg_one_pow, one_mul] at hsum
  have hc : (0 : ℝ) < bernoulli (2 * k) := by
    by_contra! hc
    have h := mul_nonpos_of_nonneg_of_nonpos
      (by positivity : 0 ≤ (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) hc
    exact hsum.not_ge (div_nonpos_of_nonpos_of_nonneg h (by positivity))
  exact_mod_cast hc

private theorem prime_eq_of_prime_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ∣ q) : p = q :=
  ((Nat.dvd_prime hq).mp h).resolve_left hp.ne_one

private theorem prime_not_dvd_two_mul_prime {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : q.Prime) (hpq : p ≠ q) : ¬ p ∣ 2 * q := by
  intro hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · have := prime_eq_of_prime_dvd hp Nat.prime_two hd
    omega
  · exact hpq (prime_eq_of_prime_dvd hp hq hd)

private theorem exists_bernoulliIrregular_mod_four_not_mem
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    ∃ p, BernoulliIrregular p ∧ p % 4 = 3 ∧ p ∉ S := by
  let M := 12 * ∏ p ∈ S, p * (p - 1)
  have hM : M ≠ 0 := Nat.mul_ne_zero (by decide) (Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
    have := (hS p hp).2
    exact Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨q, hq, hqS, hqM⟩ := Nat.exists_prime_gt_modEq_one (S.sup id) hM
  have hq3 : q % 3 = 1 := hqM.of_dvd ((by decide : 3 ∣ 12).trans (dvd_mul_right _ _))
  have hq4 : q % 4 = 1 := hqM.of_dvd ((by decide : 4 ∣ 12).trans (dvd_mul_right _ _))
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hNpos := Rat.num_pos.mpr (bernoulli_pos_of_odd hqodd)
  let N := (bernoulli (2 * q)).num
  have hNabs : (N.natAbs : ℤ) = N := Int.natAbs_of_nonneg hNpos.le
  have hN4 : N.natAbs % 4 = 3 := by
    change N.natAbs ≡ 3 [MOD 4]
    rw [← Int.natCast_modEq_iff]
    change (N.natAbs : ℤ) ≡ 3 [ZMOD 4]
    rw [hNabs]
    exact bernoulli_num_two_mul_prime_mod_four hq hq3
  obtain ⟨p, hp, hp4, hpd⟩ := exists_prime_mod_four_dvd hN4
  have hpN : (p : ℤ) ∣ N := Int.natCast_dvd.mpr hpd
  have hp5 : 5 ≤ p := by
    by_contra! hsmall
    have he : p = 3 := by omega
    subst p
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Bernoulli.not_dvd_num_bernoulli hq.pos (by simp) hpN
  refine ⟨p, irregular_of_dvd_bernoulli_num_of_coprime_index hp hp5 hq.pos
    (prime_not_dvd_two_mul_prime hp hp5 hq (by omega)) hpN, hp4, ?_⟩
  intro hps
  have hpS : p ≤ S.sup id := Finset.le_sup (f := id) hps
  have hpdM : p - 1 ∣ M := by
    exact (dvd_mul_left (p - 1) p).trans
      ((Finset.dvd_prod_of_mem (fun p ↦ p * (p - 1)) hps).trans (dvd_mul_left _ _))
  have hqP : (p - 1) ∣ q - 1 :=
    (Nat.modEq_iff_dvd' hq.pos).mp (hqM.of_dvd hpdM).symm
  have h2qp : (p - 1) ∣ 2 * q - 2 := by
    rw [show 2 * q - 2 = 2 * (q - 1) by omega]
    exact dvd_mul_of_dvd_right hqP _
  have h2p : ¬ (p - 1) ∣ 2 * 1 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hdiv := (dvd_bernoulli_num_iff_of_congruent_even_indices hp5 (by decide)
    hq.pos h2qp h2p
    (prime_not_dvd_two_mul_prime hp hp5 hq (by omega))
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).mp hpN
  have hnum : (bernoulli 2).num = 1 := by rw [bernoulli_two]; exact Rat.inv_ofNat_num 6
  change (p : ℤ) ∣ (bernoulli 2).num at hdiv
  rw [hnum] at hdiv
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)

/-- Jensen's theorem. Infinitely many primes congruent to three modulo four
divide a Bernoulli numerator at an even index between two and the prime minus three. -/
theorem infinite_bernoulliIrregular_mod_four :
    {p | BernoulliIrregular p ∧ p % 4 = 3}.Infinite := by
  intro hfin
  obtain ⟨p, hp, hp4, hpnot⟩ :=
    exists_bernoulliIrregular_mod_four_not_mem hfin.toFinset (by
      intro p hp
      obtain ⟨hirr, _⟩ := hfin.mem_toFinset.mp hp
      exact ⟨hirr.1, bernoulliIrregular_prime_ge_five hirr⟩)
  exact hpnot (hfin.mem_toFinset.mpr ⟨hp, hp4⟩)

/-- Infinitely many primes satisfy the Bernoulli numerator test for irregularity. -/
theorem infinite_bernoulliIrregular : {p | BernoulliIrregular p}.Infinite := by
  refine Set.Infinite.mono ?_ infinite_bernoulliIrregular_mod_four
  exact fun _ hp ↦ hp.1

/-- The primes below 100 satisfying the Bernoulli numerator test are 37, 59 and 67. -/
theorem bernoulliIrregular_below_100_iff {p : ℕ} (hp : p < 100) :
    BernoulliIrregular p ↔ p = 37 ∨ p = 59 ∨ p = 67 := by
  constructor
  · intro h
    have hfive := bernoulliIrregular_prime_ge_five h
    have hodd := h.1.odd_of_ne_two (by omega)
    exact (bernoulli_irregular_primes_below_100 hp h.1 hodd).mp h.2
  · rintro (rfl | rfl | rfl)
    · exact ⟨by decide, 16, by decide, by decide, dvd_bernoulli_num_37⟩
    · exact ⟨by decide, 22, by decide, by decide, dvd_bernoulli_num_59⟩
    · exact ⟨by decide, 29, by decide, by decide, dvd_bernoulli_num_67⟩

end TinyTauDemo
