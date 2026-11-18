/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicRamification
public import TinyTauDemo.Fermat.Integer.Kummer.UnifiedCyclotomicCoprimality
import Mathlib.Data.Fintype.EquivFin
import TinyTauDemo.Fermat.Integer.Kummer.ExceptionalIdealFactors
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Exact valuations of the Case II linear factors

Dividing each linear factor by the cyclotomic prime generator gives all residues
in the residue field. The quotient with zero residue determines the distinguished
factor. See `/roadmap/index.qmd#lem-case2-valuations` @
`1fb7542d166b622a63097a00bf396ccfefcce073`.
-/

public section

open NumberField Polynomial UniqueFactorizationMonoid

namespace TinyTauDemo

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {p m : ℕ} {ζ x y z : B}

open scoped Classical in
private theorem factorization_span_eq_zero_iff {a l : B}
    (ha : a ≠ 0) (hl : Prime l) :
    factorization (Ideal.span {a}) (Ideal.span {l}) = 0 ↔ ¬ l ∣ a := by
  have hI : (Ideal.span {a} : Ideal B) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  rw [← not_iff_not, not_not]
  change factorization (Ideal.span {a}) (Ideal.span {l}) ≠ 0 ↔ l ∣ a
  rw [← Nat.pos_iff_ne_zero, factorization_eq_count, Multiset.count_pos,
    Ideal.mem_normalizedFactors_iff hI,
    and_iff_right ((Ideal.span_singleton_prime hl.ne_zero).mpr hl),
    Ideal.span_singleton_le_span_singleton]

open scoped Classical in
private theorem factorization_finset_prod_apply {ι : Type*} (s : Finset ι)
    (I : ι → Ideal B) (hne : ∀ i ∈ s, I i ≠ 0) (E : Ideal B) :
    factorization (∏ i ∈ s, I i) E = ∑ i ∈ s, factorization (I i) E := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, factorization_one, Finset.sum_empty, Finsupp.zero_apply]
  | insert i s hi ih =>
      have hs (j : ι) (hj : j ∈ s) : I j ≠ 0 := hne j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        factorization_mul (hne i (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.mpr hs),
        Finsupp.add_apply, ih hs]

open scoped Classical in
/-- The exceptional linear factor has exponent `m * p - (p - 1)`. Removing
the full powers of the exceptional ideal leaves pairwise coprime `p`th powers. -/
theorem caseTwo_valuations_by_root (hp : p.Prime) (hodd : Odd p)
    (hζ : IsPrimitiveRoot ζ p) (hl : Prime (1 - ζ))
    (residue : (B ⧸ Ideal.span {1 - ζ}) ≃+* ZMod p)
    (hxy : IsCoprime x y) (hy : ¬ ((1 - ζ) ∣ y)) (hz : ¬ ((1 - ζ) ∣ z))
    (hm : 1 ≤ m) (u : Bˣ)
    (heq : x ^ p + y ^ p = (u : B) * (1 - ζ) ^ (m * p) * z ^ p) :
    let S := nthRootsFinset p (1 : B)
    let E : Ideal B := Ideal.span {1 - ζ}
    let I (η : B) : Ideal B := Ideal.span {x + η * y}
    2 ≤ m ∧ p + 1 ≤ m * p - (p - 1) ∧
    ∃ η₀ ∈ S, ∃ a : B → Ideal B,
      Set.Pairwise S (fun η θ ↦ IsCoprime (a η) (a θ)) ∧
      (∀ η ∈ S, IsCoprime (a η) E) ∧
      ∀ η ∈ S,
        let e := if η = η₀ then m * p - (p - 1) else 1
        factorization (I η) E = e ∧ I η = E ^ e * (a η) ^ p := by
  classical
  let l := 1 - ζ
  let S := nthRootsFinset p (1 : B)
  let E : Ideal B := Ideal.span {l}
  let I (η : B) : Ideal B := Ideal.span {x + η * y}
  let v (η : B) := factorization (I η) E
  have hE0 : E ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hl.ne_zero
  have hEp : Prime E :=
    Ideal.prime_of_isPrime hE0 ((Ideal.span_singleton_prime hl.ne_zero).mpr hl)
  have hEfac : normalizedFactors E = {E} := by
    rw [normalizedFactors_irreducible hEp.irreducible, normalize_eq]
  have hEone : factorization E E = 1 := by rw [factorization_eq_count, hEfac]; simp
  have hz0 : z ≠ 0 := by
    intro h
    exact hz (h.symm ▸ dvd_zero l)
  have hlinear : ∏ η ∈ S, (x + η * y) = (u : B) * l ^ (m * p) * z ^ p := by
    rw [← hζ.pow_add_pow_eq_prod_add_mul x y hodd, heq]
  have hnonzero (η : B) (hη : η ∈ S) : x + η * y ≠ 0 :=
    Finset.prod_ne_zero_iff.mp
      (hlinear.symm ▸ mul_ne_zero (mul_ne_zero (Units.ne_zero u) (pow_ne_zero _ hl.ne_zero))
        (pow_ne_zero _ hz0)) η hη
  have hI (η : B) (hη : η ∈ S) : I η ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hnonzero η hη)
  have hdvd : l ∣ ∏ η ∈ S, (x + η * y) := by
    rw [hlinear]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
      (dvd_pow_self l (Nat.mul_ne_zero (by omega) hp.ne_zero)) _) _
  obtain ⟨θ, hθ, hθdvd⟩ := (hl.dvd_finsetProd_iff _).mp hdvd
  have hdiv (η : S) : l ∣ x + η.val * y := by
    have hd : -(ζ - 1) ∣ η.val - θ := neg_dvd.mpr (hζ.sub_one_dvd_sub hp η.property hθ)
    rw [neg_sub] at hd
    have hsum := dvd_add hθdvd (dvd_mul_of_dvd_left hd y)
    rwa [show x + θ * y + (η.val - θ) * y = x + η.val * y by ring] at hsum
  choose q hq using hdiv
  let r (η : S) : ZMod p := residue (Ideal.Quotient.mk E (q η))
  have hr : Function.Injective r := by
    intro η θ he
    by_contra hne
    have hval : η.val ≠ θ.val := fun e ↦ hne (Subtype.ext e)
    obtain ⟨w, hw⟩ := (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hp η.property θ.property hval).neg_left
    rw [neg_sub] at hw
    have hc : Ideal.Quotient.mk E (q η) = Ideal.Quotient.mk E (q θ) :=
      residue.injective he
    have hd : l ∣ q η - q θ := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, hc, sub_self]
    have hqsub : q η - q θ = (w : B) * y := by
      apply mul_left_cancel₀ hl.ne_zero
      calc
        l * (q η - q θ) = (x + η.val * y) - (x + θ.val * y) := by
          rw [mul_sub, ← hq η, ← hq θ]
        _ = (η.val - θ.val) * y := by ring
        _ = l * ((w : B) * y) := by rw [← mul_assoc, hw]
    rw [hqsub, mul_comm] at hd
    exact hy (Units.dvd_mul_right.mp hd)
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have hsurj : Function.Surjective r :=
    ((Fintype.bijective_iff_injective_and_card r).mpr
      ⟨hr, by rw [Fintype.card_coe, hζ.card_nthRootsFinset, ZMod.card]⟩).2
  obtain ⟨η₀, hη₀⟩ := hsurj 0
  have hval (η : S) : v η.val = 1 + factorization (Ideal.span {q η}) E := by
    have hq0 : q η ≠ 0 := by
      intro h
      exact hnonzero _ η.property (by rw [hq η, h, mul_zero])
    dsimp only [v, I]
    rw [hq η, ← Ideal.span_singleton_mul_span_singleton,
      factorization_mul hE0 (Ideal.span_singleton_eq_bot.not.mpr hq0), Finsupp.add_apply, hEone]
  have hzero (η : S) : r η = 0 ↔ l ∣ q η := by
    change residue (Ideal.Quotient.mk E (q η)) = 0 ↔ _
    rw [← map_zero residue, EmbeddingLike.apply_eq_iff_eq,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hlarge : 2 ≤ v η₀.val := by
    have hq0 : q η₀ ≠ 0 := by
      intro h
      exact hnonzero _ η₀.property (by rw [hq η₀, h, mul_zero])
    have hn := (factorization_span_eq_zero_iff hq0 hl).not.mpr
      (not_not_intro ((hzero η₀).mp hη₀))
    change factorization (Ideal.span {q η₀}) E ≠ 0 at hn
    rw [hval]
    omega
  have hsmall (η : B) (hη : η ∈ S) (hne : η ≠ η₀.val) : v η = 1 := by
    let e : S := ⟨η, hη⟩
    have hq0 : q e ≠ 0 := by
      intro h
      exact hnonzero _ hη (by rw [hq e, h, mul_zero])
    have hn : ¬ l ∣ q e := by
      intro h
      exact hne (congrArg Subtype.val (hr (((hzero e).mpr h).trans hη₀.symm)))
    exact (hval e).trans (by rw [(factorization_span_eq_zero_iff hq0 hl).mpr hn, add_zero])
  have hprod : ∏ η ∈ S, I η = (E ^ m * Ideal.span {z}) ^ p := by
    dsimp only [I]
    rw [Ideal.prod_span_singleton, hlinear, mul_assoc, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.top_mul, pow_mul, ← mul_pow,
      ← Ideal.span_singleton_pow (l ^ m * z), ← Ideal.span_singleton_mul_span_singleton,
      ← Ideal.span_singleton_pow l]
  have hsum : ∑ η ∈ S, v η = m * p := by
    rw [show (∑ η ∈ S, v η) = factorization (∏ η ∈ S, I η) E from
      (factorization_finset_prod_apply S I hI E).symm, hprod,
      factorization_pow, Finsupp.smul_apply,
      factorization_mul (pow_ne_zero _ hE0) (Ideal.span_singleton_eq_bot.not.mpr hz0),
      Finsupp.add_apply, factorization_pow, Finsupp.smul_apply, hEone,
      (factorization_span_eq_zero_iff hz0 hl).mpr hz]
    simp [mul_comm]
  have hsplit : ∑ η ∈ S, v η = v η₀.val + (p - 1) := by
    rw [← Finset.add_sum_erase S v η₀.property]
    congr 1
    calc
      ∑ η ∈ S.erase η₀.val, v η = ∑ _η ∈ S.erase η₀.val, (1 : ℕ) :=
        Finset.sum_congr rfl fun η hη ↦
          hsmall η (Finset.mem_of_mem_erase hη) (Finset.ne_of_mem_erase hη)
      _ = p - 1 := by simp [Finset.card_erase_of_mem η₀.property, S, hζ.card_nthRootsFinset]
  have hm2 : 2 ≤ m := by
    by_contra! hn
    have : m = 1 := by omega
    rw [this, one_mul] at hsum
    omega
  have hv₀ : v η₀.val = m * p - (p - 1) := by omega
  have ht : p + 1 ≤ m * p - (p - 1) := by
    have hmp := Nat.mul_le_mul_right p hm2
    omega
  obtain ⟨a, ha, hcop, hdecomp⟩ :=
    Ideal.exists_pow_mul_exceptionalFactors_of_prod_eq_pow S hI hE0 hprod (by
      intro P _ hP
      have haway : ¬ 1 - ζ ∈ P := by
        simpa only [E, l, Ideal.span_singleton_le_iff_mem] using hP
      simpa only [I, Ideal.span_singleton_le_iff_mem] using
        cyclotomic_linear_factors_pairwise_outside hp hζ hxy haway)
  refine ⟨hm2, ht, η₀, η₀.property, a, ha, hcop, ?_⟩
  intro η hη
  have hcalc : v η = if η = η₀.val then m * p - (p - 1) else 1 := by
    by_cases he : η = η₀.val
    · simpa only [he, ite_true] using hv₀
    · simpa only [he, ite_false] using hsmall η hη he
  have h := hdecomp η hη
  rw [support_factorization, hEfac, Multiset.toFinset_singleton, Finset.prod_singleton,
    ← show v η = factorization (I η) E from rfl, hcalc, mul_comm] at h
  exact ⟨hcalc, h⟩

open scoped Classical in
/-- After twisting `y` by a power of the primitive root, the untwisted linear
factor has the exceptional exponent and the other factors have exponent one.
The displayed denominators yield integral quotients whose principal ideals
are pairwise coprime, coprime to the cyclotomic prime, and exact `p`th powers. -/
theorem caseTwo_valuations {K : Type*} [Field K] [NumberField K] {p m : ℕ}
    [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) {x y z : 𝓞 K}
    (hxy : IsCoprime x y) (hy : ¬ ((1 - hζ.toInteger) ∣ y))
    (hz : ¬ ((1 - hζ.toInteger) ∣ z)) (hm : 1 ≤ m) (u : (𝓞 K)ˣ)
    (heq : x ^ p + y ^ p = (u : 𝓞 K) * (1 - hζ.toInteger) ^ (m * p) * z ^ p) :
    let root := hζ.toInteger
    let l := 1 - root
    let E : Ideal (𝓞 K) := Ideal.span {l}
    let e := m * p - (p - 1)
    2 ≤ m ∧ p + 1 ≤ e ∧
    ∃ (j₀ : Fin p) (b : Fin p → 𝓞 K) (a : Fin p → Ideal (𝓞 K)),
      let y' := root ^ j₀.val * y
      y' ^ p = y ^ p ∧
      Pairwise (fun i j ↦ IsCoprime (Ideal.span {b i}) (Ideal.span {b j})) ∧
      ∀ j, let c := x + root ^ j.val * y'
           let d := if j.val = 0 then l ^ e else 1 - root ^ j.val
           factorization (Ideal.span {c}) E = (if j.val = 0 then e else 1) ∧
           c = d * b j ∧ Ideal.span {b j} = (a j) ^ p ∧ IsCoprime (Ideal.span {b j}) E := by
  classical
  let _ : NeZero p := ⟨hp.out.ne_zero⟩
  let root := hζ.toInteger
  let l := 1 - root
  let E : Ideal (𝓞 K) := Ideal.span {l}
  let e := m * p - (p - 1)
  let S := nthRootsFinset p (1 : 𝓞 K)
  have hroot : IsPrimitiveRoot root p := hζ.toInteger_isPrimitiveRoot
  have hl0 : l ≠ 0 := sub_ne_zero.mpr (hroot.ne_one hp.out.one_lt).symm
  have hE0 : E ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hl0
  have hl : Prime l := by
    rw [← Ideal.span_singleton_prime hl0]
    change (Ideal.span {1 - hζ.toInteger}).IsPrime
    rw [hζ.span_one_sub_eq_span_zeta_sub_one]
    exact (Ideal.span_singleton_prime hζ.zeta_sub_one_prime'.ne_zero).mpr hζ.zeta_sub_one_prime'
  obtain ⟨hm2, he, η₀, hη₀, a, ha, hcop, hdec⟩ :=
    caseTwo_valuations_by_root hp.out (hp.out.odd_of_ne_two hp2) hroot hl
      (hζ.quotientOneSubEquivZMod hp2) hxy hy hz hm u heq
  have hpows (j : ℕ) : (root ^ j) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot.pow_eq_one, one_pow]
  obtain ⟨j₀, hj₀, hηpow⟩ := hroot.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hp.out.pos 1).mp hη₀)
  have hηne : η₀ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hη₀
  let η (j : Fin p) := root ^ j.val * η₀
  have hη (j : Fin p) : η j ∈ S := by
    change root ^ j.val * η₀ ∈ nthRootsFinset p (1 : 𝓞 K)
    rw [mem_nthRootsFinset hp.out.pos, mul_pow, hpows,
      (mem_nthRootsFinset hp.out.pos 1).mp hη₀, one_mul]
  have hηinj : Function.Injective η := fun i j hij ↦
    Fin.ext (hroot.pow_inj i.isLt j.isLt (mul_right_cancel₀ hηne hij))
  have hηeq (j : Fin p) : η j = η₀ ↔ j.val = 0 := by
    have heq₀ : η ⟨0, hp.out.pos⟩ = η₀ := by simp [η]
    rw [← heq₀, hηinj.eq_iff]
    exact ⟨fun h ↦ congrArg Fin.val h, fun h ↦ Fin.ext (by exact h)⟩
  let n (j : Fin p) := if j.val = 0 then e else 1
  let d (j : Fin p) := if j.val = 0 then l ^ e else 1 - root ^ j.val
  let c (j : Fin p) := x + root ^ j.val * (root ^ j₀ * y)
  have hc (j : Fin p) : c j = x + η j * y := by
    dsimp only [c, η]
    rw [hηpow, mul_assoc]
  have hd (j : Fin p) : Ideal.span {d j} = E ^ n j := by
    by_cases hj : j.val = 0
    · simp only [d, n, hj, ite_true, E, Ideal.span_singleton_pow]
    · simp only [d, n, hj, ite_false, pow_one, E, l]
      exact span_one_sub_pow_eq_span_one_sub hp.out hroot (Nat.pos_of_ne_zero hj) j.isLt
  have hfactor (j : Fin p) :
      factorization (Ideal.span {c j}) E = n j ∧
        Ideal.span {c j} = Ideal.span {d j} * (a (η j)) ^ p := by
    rw [hc, hd]
    have h := hdec (η j) (hη j)
    dsimp only at h
    rw [hηeq j] at h
    by_cases hj : j.val = 0 <;> simpa only [E, l, n, e, hj, ite_true, ite_false] using h
  have hquot (j : Fin p) :
      ∃ q, c j = d j * q ∧ Ideal.span {q} = (a (η j)) ^ p := by
    have hle : Ideal.span {c j} ≤ Ideal.span {d j} :=
      (hfactor j).2.trans_le Ideal.mul_le_left
    obtain ⟨q, hq⟩ := Ideal.span_singleton_le_span_singleton.mp hle
    have hd0 : (Ideal.span {d j} : Ideal (𝓞 K)) ≠ 0 := (hd j).symm ▸ pow_ne_zero _ hE0
    refine ⟨q, hq, mul_left_cancel₀ hd0 ?_⟩
    rw [Ideal.span_singleton_mul_span_singleton, ← hq, (hfactor j).2]
  choose b hb using hquot
  refine ⟨hm2, he, ⟨j₀, hj₀⟩, b, a ∘ η, ?_, ?_, ?_⟩
  · rw [mul_pow, hpows, one_mul]
  · intro i j hij
    rw [(hb i).2, (hb j).2]
    exact (ha (hη i) (hη j) (fun h ↦ hij (hηinj h))).pow
  · intro j
    change factorization (Ideal.span {c j}) E = n j ∧
      c j = d j * b j ∧ Ideal.span {b j} = (a (η j)) ^ p ∧ IsCoprime (Ideal.span {b j}) E
    refine ⟨(hfactor j).1, (hb j).1, (hb j).2, ?_⟩
    rw [(hb j).2]
    exact (hcop (η j) (hη j)).pow_left

end TinyTauDemo
