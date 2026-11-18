/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Perfect powers of ideals outside an exceptional set

Ideal factorization in a Dedekind domain decomposes a product of ideals into its prime
exponents. When only one factor contains a given prime outside a fixed exceptional ideal,
its exponent inherits the divisibility of the total exponent.
-/

public section

open UniqueFactorizationMonoid

namespace Ideal

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

open scoped Classical in
private theorem factorization_prod_ne_zero {ι : Type*} (s : Finset ι) (I : ι → Ideal B)
    (hI : ∀ i ∈ s, I i ≠ 0) :
    factorization (∏ i ∈ s, I i) = ∑ i ∈ s, factorization (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, factorization_one]
  | insert i s hi ih =>
      have hs (j : ι) (hj : j ∈ s) : I j ≠ 0 := hI j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        factorization_mul (hI _ (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.mpr hs),
        ih hs]

open scoped Classical in
private theorem factorization_pos_iff_ideal_le {I q : Ideal B} (hI : I ≠ 0) (hq : Prime q) :
    0 < factorization I q ↔ I ≤ q := by
  rw [factorization_eq_count, Multiset.count_pos, Ideal.mem_normalizedFactors_iff hI]
  exact and_iff_right (Ideal.isPrime_of_prime hq)

open scoped Classical in
private theorem prime_of_mem_support_factorization {I q : Ideal B}
    (hq : q ∈ (factorization I).support) : Prime q := by
  rw [support_factorization, Multiset.mem_toFinset] at hq
  exact prime_of_normalized_factor q hq

open scoped Classical in
private theorem factorization_prime_pow_product (s : Finset (Ideal B)) (e : Ideal B → ℕ)
    (hprime : ∀ q ∈ s, Prime q) (q : Ideal B) :
    factorization (∏ r ∈ s, r ^ e r) q = if q ∈ s then e q else 0 := by
  classical
  rw [factorization_prod_ne_zero s (fun r ↦ r ^ e r)
    (fun r hr ↦ pow_ne_zero _ (hprime r hr).ne_zero), Finsupp.finsetSum_apply]
  have hpow (r : Ideal B) (hr : r ∈ s) :
      factorization (r ^ e r) q = if q = r then e r else 0 := by
    rw [factorization_eq_count, normalizedFactors_of_irreducible_pow (hprime r hr).irreducible,
      normalize_eq, Multiset.count_replicate]
    rcases eq_or_ne r q with rfl | hne
    · simp
    · simp [hne, hne.symm]
  rw [Finset.sum_congr rfl hpow]
  simp

private theorem isCoprime_of_no_common_prime {I J : Ideal B} (hI : I ≠ 0)
    (h : ∀ q, Prime q → I ≤ q → ¬ J ≤ q) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (I ⊔ J) hsup
  have hq0 : q ≠ ⊥ := ne_bot_of_le_ne_bot hI (le_sup_left.trans hle)
  exact h q (Ideal.prime_of_isPrime hq0 hq.isPrime) (le_sup_left.trans hle)
    (le_sup_right.trans hle)

open scoped Classical in
/-- If a finite product of nonzero ideals is a perfect power, and each prime outside an
exceptional ideal divides at most one factor, then each factor is a power times its part
supported on exceptional primes. The resulting roots are pairwise coprime and coprime
to the exceptional ideal. -/
theorem exists_pow_mul_exceptionalFactors_of_prod_eq_pow {ι : Type*} (s : Finset ι)
    {I : ι → Ideal B} {J E : Ideal B} {n : ℕ}
    (hI : ∀ i ∈ s, I i ≠ 0) (hE : E ≠ 0) (hprod : ∏ i ∈ s, I i = J ^ n)
    (hdisj : ∀ q, Prime q → ¬ E ≤ q →
      (s : Set ι).Pairwise (fun i j ↦ ¬ (I i ≤ q ∧ I j ≤ q))) :
    ∃ a : ι → Ideal B,
      (s : Set ι).Pairwise (fun i j ↦ IsCoprime (a i) (a j)) ∧
      (∀ i ∈ s, IsCoprime (a i) E) ∧
      ∀ i ∈ s, I i = (a i) ^ n *
        ∏ q ∈ (factorization E).support, q ^ factorization (I i) q := by
  classical
  -- Split each ideal's prime exponents into the exceptional and remaining primes.
  let exceptional : Finset (Ideal B) := (factorization E).support
  let outside (i : ι) : Finset (Ideal B) := (factorization (I i)).support.filter
    (fun q ↦ q ∉ exceptional)
  let a (i : ι) : Ideal B := ∏ q ∈ outside i, q ^ (factorization (I i) q / n)
  let e (i : ι) : Ideal B := ∏ q ∈ exceptional, q ^ factorization (I i) q
  have hprimeE (q : Ideal B) (hq : q ∈ exceptional) : Prime q :=
    prime_of_mem_support_factorization hq
  have hprimeA (i : ι) (q : Ideal B) (hq : q ∈ outside i) : Prime q :=
    prime_of_mem_support_factorization (Finset.mem_filter.mp hq).1
  have ha0 (i : ι) : a i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq ↦ pow_ne_zero _ (hprimeA i q hq).ne_zero
  have he0 (i : ι) : e i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq ↦ pow_ne_zero _ (hprimeE q hq).ne_zero
  have hfacA (i : ι) (q : Ideal B) :
      factorization (a i) q =
        if q ∈ outside i then factorization (I i) q / n else 0 :=
    factorization_prime_pow_product _ _ (hprimeA i) q
  have hfacE (i : ι) (q : Ideal B) :
      factorization (e i) q = if q ∈ exceptional then factorization (I i) q else 0 :=
    factorization_prime_pow_product _ _ hprimeE q
  have hsupportE (q : Ideal B) (hq : Prime q) : q ∈ exceptional ↔ E ≤ q := by
    rw [show exceptional = (factorization E).support from rfl, Finsupp.mem_support_iff,
      ← Nat.pos_iff_ne_zero, factorization_pos_iff_ideal_le hE hq]
  have hsupportA (i : ι) (hi : i ∈ s) (q : Ideal B) (hq : Prime q)
      (hle : a i ≤ q) : I i ≤ q ∧ ¬ E ≤ q := by
    have hap := (factorization_pos_iff_ideal_le (ha0 i) hq).2 hle
    rw [hfacA i] at hap
    have hmem : q ∈ outside i := by
      by_contra hmem
      simp [hmem] at hap
    obtain ⟨hm, hnot⟩ := Finset.mem_filter.mp hmem
    exact ⟨(factorization_pos_iff_ideal_le (hI i hi) hq).1
      (Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm)), (hsupportE q hq).not.mp hnot⟩
  -- Away from the exceptional ideal, a nonzero exponent is the entire product's exponent.
  have hfactorization :
      (∑ i ∈ s, factorization (I i)) = n • factorization J := by
    rw [← factorization_prod_ne_zero s I hI, hprod, factorization_pow]
  have hdvd (i : ι) (hi : i ∈ s) (q : Ideal B) (hq : Prime q)
      (haway : ¬ E ≤ q) (hqi : I i ≤ q) : n ∣ factorization (I i) q := by
    have hsum := DFunLike.congr_fun hfactorization q
    rw [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Finset.sum_eq_single_of_mem i hi] at hsum
    · exact ⟨factorization J q, hsum⟩
    · intro j hj hji
      exact Nat.eq_zero_of_not_pos
        (fun hjq ↦ hdisj q hq haway hi hj hji.symm
          ⟨hqi, (factorization_pos_iff_ideal_le (hI j hj) hq).1 hjq⟩)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i hi j hj hne
    apply isCoprime_of_no_common_prime (ha0 i)
    intro q hq hqa hqb
    obtain ⟨hqi, haway⟩ := hsupportA i hi q hq hqa
    exact hdisj q hq haway hi hj hne ⟨hqi, (hsupportA j hj q hq hqb).1⟩
  · intro i hi
    apply isCoprime_of_no_common_prime (ha0 i)
    intro q hq hqa
    exact (hsupportA i hi q hq hqa).2
  · intro i hi
    apply associated_iff_eq.mp
    apply associated_of_factorization_eq _ _ (hI i hi)
      (mul_ne_zero (pow_ne_zero _ (ha0 i)) (he0 i))
    ext q
    rw [factorization_mul (pow_ne_zero _ (ha0 i)) (he0 i), Finsupp.add_apply,
      factorization_pow, Finsupp.smul_apply, smul_eq_mul, hfacA i q, hfacE i q]
    by_cases hqe : q ∈ exceptional
    · have hqa : q ∉ outside i := fun hqa ↦ (Finset.mem_filter.mp hqa).2 hqe
      simp [hqe, hqa]
    · by_cases hqi : q ∈ (factorization (I i)).support
      · have hqa : q ∈ outside i := Finset.mem_filter.mpr ⟨hqi, hqe⟩
        have hq := hprimeA i q hqa
        have hle := (factorization_pos_iff_ideal_le (hI i hi) hq).1
          (Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hqi))
        have hd := hdvd i hi q hq ((hsupportE q hq).not.mp hqe) hle
        simp [hqe, hqa, Nat.mul_div_cancel' hd]
      · have hqa : q ∉ outside i := fun hqa ↦ hqi (Finset.mem_filter.mp hqa).1
        simp [hqe, hqa, Finsupp.notMem_support_iff.mp hqi]

end Ideal
