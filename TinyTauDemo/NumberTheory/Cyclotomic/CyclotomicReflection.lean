/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.ClassNumberTransfer
public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicUnits
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Kummer reflection and unramified towers

A cyclic extension of degree p of a prime cyclotomic field that is unramified
at every finite place and abelian over its maximal real subfield supplies a
p-factor of the relative class-group norm kernel. Complex conjugation inverts
the Kummer radicand modulo pth powers. Its principal ideal is a pth power,
and if its root ideal is principal the cyclotomic unit decomposition forces
a primitive root of order p squared in the unramified extension.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9e49cf86a2f12f4c30fb1657d2e228b79f3a2a77`.
-/

public section

open NumberField IsDedekindDomain WithZero Function
open scoped NumberField nonZeroDivisors

namespace TinyTauDemo

section KummerAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- If an automorphism lifts to an automorphism commuting with the relative Galois
group and inverts the relevant roots of unity, the Kummer radicand is sent to
its inverse modulo powers. -/
theorem exists_pow_eq_mul_of_commuting_kummer_automorphism
    {n : ℕ} [NeZero n] {ζ a : K} {r : L} (hζ : IsPrimitiveRoot ζ n) (ha : a ≠ 0)
    (hr : r ^ n = algebraMap K L a) (σ : K ≃+* K) (τ : L ≃+* L)
    (hσ : σ ζ = ζ⁻¹) (hτ : ∀ x : K, τ (algebraMap K L x) = algebraMap K L (σ x))
    (hcomm : ∀ (g : L ≃ₐ[K] L) (x : L), g (τ x) = τ (g x)) :
    ∃ b : K, b ^ n = a * σ a := by
  have hr0 : r ≠ 0 := fun h ↦ ha ((map_eq_zero_iff _ (algebraMap K L).injective).mp
    (hr.symm.trans (by simp [h, NeZero.ne n])))
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n := hζ.map_of_injective (algebraMap K L).injective
  have hfixed (g : L ≃ₐ[K] L) : g (r * τ r) = r * τ r := by
    have hratio : (g r / r) ^ n = 1 := by
      rw [div_pow, ← map_pow, hr, AlgEquiv.commutes, div_self]
      exact (map_ne_zero (algebraMap K L)).mpr ha
    obtain ⟨j, _, hj⟩ := hζL.eq_pow_of_pow_eq_one hratio
    have hg : g r = (algebraMap K L ζ) ^ j * r := by
      apply (div_eq_iff hr0).mp
      exact hj.symm
    rw [map_mul, hcomm, hg, map_mul, map_pow, hτ, hσ, map_inv₀, inv_pow]
    calc
      _ = ((algebraMap K L ζ) ^ j * ((algebraMap K L ζ) ^ j)⁻¹) * (r * τ r) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ (hζL.ne_zero (NeZero.ne n))), one_mul]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (r * τ r)).mpr
    hfixed
  refine ⟨b, (algebraMap K L).injective ?_⟩
  rw [map_pow, hb, mul_pow, ← map_pow τ, hr, hτ, map_mul]

end KummerAction


section UnramifiedIdeal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- If a nonzero algebraic integer acquires an n-th root in an everywhere
unramified extension, its principal ideal is the n-th power of an integral ideal. -/
theorem exists_ideal_pow_eq_span_singleton_of_unramified_root
    {n : ℕ} (hn : 0 < n) {a : 𝓞 K} (ha : a ≠ 0) {r : L}
    (hr : r ^ n = algebraMap K L (a : K))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    ∃ I : Ideal (𝓞 K), I ^ n = Ideal.span {a} := by
  classical
  let S : Ideal (𝓞 K) := Ideal.span {a}
  have hS : S ≠ 0 := by simp [S, ha]
  have hr0 : r ≠ 0 := by
    intro hh
    rw [hh, zero_pow hn.ne'] at hr
    exact ha (RingOfIntegers.coe_injective (by simpa using hr.symm))
  have hrInt : IsIntegral ℤ r := IsIntegral.of_pow hn
    (hr ▸ a.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ K L))
  let b : 𝓞 L := ⟨r, hrInt⟩
  have hb : b ≠ 0 := fun h ↦ hr0 (congrArg (fun x : 𝓞 L ↦ (x : L)) h)
  let c (v : HeightOneSpectrum (𝓞 K)) := (Associates.mk v.asIdeal).count (Associates.mk S).factors
  have hd (v : HeightOneSpectrum (𝓞 K)) : n ∣ c v := by
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 L) v.asIdeal
    let w : HeightOneSpectrum (𝓞 L) :=
      ⟨Q, hQ.isPrime, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hQ.isPrime, hQv⟩⟩
    have : w.asIdeal.LiesOver v.asIdeal := hQv
    have : w.asIdeal.IsPrime := w.isPrime
    have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hunr w
    have he := Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 K)
    have hv : v.intValuation a = w.intValuation b ^ n := calc
      _ = v.valuation K (a : K) := (v.valuation_of_algebraMap a).symm
      _ = w.valuation L (algebraMap K L (a : K)) := by
        simpa only [he, pow_one] using v.valuation_liesOver L w (a : K)
      _ = _ := by rw [← hr, map_pow, show r = (b : L) by rfl, w.valuation_of_algebraMap]
    rw [v.intValuation_if_neg ha, w.intValuation_if_neg hb, ← exp_nsmul,
      exp_inj, Int.nsmul_eq_mul, mul_neg, neg_inj, ← Nat.cast_mul, Nat.cast_inj] at hv
    exact ⟨_, hv⟩
  let f (v : HeightOneSpectrum (𝓞 K)) := v.asIdeal ^ (c v / n)
  have hf : HasFiniteMulSupport f := (Ideal.hasFiniteMulSupport hS).subset (by
    intro v hv
    change f v ≠ 1 at hv
    change v.asIdeal ^ c v ≠ 1
    intro hc
    have hc0 : c v = 0 :=
      (Ideal.pow_eq_top_iff.mp (by simpa only [Ideal.one_eq_top] using hc)).resolve_left
        v.isPrime.ne_top
    exact hv (by simp [f, hc0]))
  refine ⟨∏ᶠ v, f v, ?_⟩
  change (∏ᶠ v, f v) ^ n = S
  rw [finprod_pow hf, ← Ideal.finprod_heightOneSpectrum_factorization hS]
  refine finprod_congr fun v ↦ ?_
  rw [show f v ^ n = v.asIdeal ^ (c v / n * n) from (pow_mul _ _ _).symm,
    Nat.div_mul_cancel (hd v)]
  rfl

end UnramifiedIdeal


section RamificationBound

/-- An everywhere unramified extension of the prime cyclotomic field does
not contain a primitive root of order p squared. -/
theorem not_isPrimitiveRoot_prime_sq_of_unramified {p : ℕ} [Fact p.Prime]
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsCyclotomicExtension {p} ℚ K]
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    (r : L) : ¬ IsPrimitiveRoot r (p ^ 2) := by
  intro hr
  have hp : p.Prime := Fact.out
  let : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let M := IntermediateField.adjoin ℚ {r}
  have : IsCyclotomicExtension {p ^ (1 + 1)} ℚ M :=
    hr.intermediateField_adjoin_isCyclotomicExtension ℚ
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP0 : P ≠ ⊥ := by simp [P, hp.ne_zero]
  have : P.IsPrime :=
    (Ideal.span_singleton_prime (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) P
  have : Q.IsPrime := hQ.isPrime
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) Q
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hP0 ⟨hQ.isPrime, hQP⟩
  have hW0 : W ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hQ0 ⟨hW.isPrime, hWQ⟩
  have : W.IsPrime := hW.isPrime
  have : W.LiesOver P := Ideal.LiesOver.trans W Q P
  let T := W.under (𝓞 M)
  have : T.IsPrime := Ideal.IsPrime.under _ W
  have : W.LiesOver T := inferInstanceAs (W.LiesOver (W.under (𝓞 M)))
  have : T.LiesOver P := Ideal.LiesOver.tower_bot W T P
  have : Algebra.IsUnramifiedAt (𝓞 K) W := hunr ⟨W, hW.isPrime, hW0⟩
  have hk := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p K Q
  have hm := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow p 1 M T
  have hWZ : W.ramificationIdx ℤ = p - 1 := by
    rw [Ideal.ramificationIdx_tower (R := ℤ) Q W, hk, Ideal.ramificationIdx_eq_one, mul_one]
  have hdiv : p ∣ p - 1 := by
    rw [← hWZ, Ideal.ramificationIdx_tower (R := ℤ) T W, hm, pow_one, mul_assoc]
    exact dvd_mul_right _ _
  exact (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt)
    (Nat.sub_lt hp.pos (by decide))) hdiv

end RamificationBound


section NormKernel

private theorem ideal_eq_of_pow_eq_pow {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (h : I ^ n = J ^ n) : I = J := by
  classical
  rw [← associated_iff_eq, ← Associates.mk_eq_mk_iff_associated]
  have hi := Associates.mk_ne_zero.mpr hI
  have hj := Associates.mk_ne_zero.mpr hJ
  apply Associates.eq_of_eq_counts hi hj
  intro P hP
  have he := congrArg (fun x : Ideal R ↦ P.count (Associates.mk x).factors) h
  rw [Associates.mk_pow, Associates.mk_pow, Associates.count_pow hi hP,
    Associates.count_pow hj hP] at he
  exact Nat.eq_of_mul_eq_mul_left hn.bot_lt he

variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Algebra.IsQuadraticExtension F K]

private theorem quadratic_norm_eq_mul {σ : K ≃ₐ[F] K} (hσ : σ ≠ 1) (x : K) :
    algebraMap F K (Algebra.norm F x) = x * σ x := by
  classical
  have hcard : Fintype.card (K ≃ₐ[F] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two]
  have hpair : ({1, σ} : Finset (K ≃ₐ[F] K)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hσ.symm, hcard]
  rw [Algebra.norm_eq_prod_automorphisms, ← hpair, Finset.prod_pair hσ.symm]
  rfl

/-- If the norm kernel has order prime to p, the ideal of a Kummer radicand
sent to its inverse modulo p-th powers by quadratic conjugation is principal. -/
theorem isPrincipal_of_antiInvariant_radical_ideal
    {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hker : ¬ p ∣ Nat.card (ClassGroup.relNorm (R := 𝓞 F) (S := 𝓞 K)).ker)
    {σ : K ≃ₐ[F] K} (hσ : σ ≠ 1) {a : 𝓞 K} (ha : a ≠ 0)
    {b : K} (hb : b ^ p = (a : K) * σ (a : K))
    {I : Ideal (𝓞 K)} (hI : I ^ p = Ideal.span {a}) : I.IsPrincipal := by
  have hI0 : I ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hI
    exact ha (Ideal.span_singleton_eq_bot.mp hI.symm)
  have hbin : IsIntegral ℤ b := IsIntegral.of_pow hp.pos (by
    rw [hb]
    exact a.isIntegral_coe.mul (a.isIntegral_coe.map (σ.restrictScalars ℤ)))
  let c : 𝓞 K := ⟨b, hbin⟩
  have hc0 : c ≠ 0 := by
    intro hc
    have hb0 : b = 0 := congrArg (fun x : 𝓞 K ↦ (x : K)) hc
    have hna : (a : K) ≠ 0 := fun h ↦ ha (RingOfIntegers.coe_injective h)
    exact (mul_ne_zero hna ((map_ne_zero σ).mpr hna)) (by simpa [hb0, hp.ne_zero] using hb.symm)
  let μ := Algebra.intNorm (𝓞 F) (𝓞 K)
  have hμ (x : 𝓞 K) :
      algebraMap (𝓞 F) F (μ x) = Algebra.norm F (x : K) :=
    Algebra.algebraMap_intNorm (K := F) (L := K) x
  have hnorm : μ c ^ p = μ a ^ 2 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_pow, hμ, hμ, ← map_pow]
    change Algebra.norm F (b ^ p) = _
    rw [hb, ← quadratic_norm_eq_mul hσ,
      Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two]
  let J := Ideal.relNorm (𝓞 F) I
  have hJ : J ^ p = Ideal.span {μ a} := by
    change (Ideal.relNorm (𝓞 F) I) ^ p = _
    rw [← map_pow, hI, Ideal.relNorm_singleton]
  have hJ0 : J ≠ 0 := Ideal.relNorm_eq_bot_iff.not.mpr hI0
  have hμc0 : μ c ≠ 0 := Algebra.intNorm_eq_zero.not.mpr hc0
  have hJ2 : J ^ 2 = Ideal.span {μ c} := by
    apply ideal_eq_of_pow_eq_pow (pow_ne_zero _ hJ0) (by simpa using hμc0) hp.ne_zero
    rw [← pow_mul, Nat.mul_comm 2 p, pow_mul, hJ, Ideal.span_singleton_pow,
      Ideal.span_singleton_pow, hnorm]
  let i : (Ideal (𝓞 K))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩
  let j := Ideal.relNorm0 (𝓞 F) i
  have hj : (j : Ideal (𝓞 F)) = J := Ideal.coe_relNorm0 i
  have hiPow : ClassGroup.mk0 i ^ p = 1 := by
    rw [← map_pow, ClassGroup.mk0_eq_one_iff]
    change (I ^ p).IsPrincipal
    rw [hI]
    exact ⟨⟨a, rfl⟩⟩
  have hjPow : ClassGroup.mk0 j ^ 2 = 1 := by
    rw [← map_pow, ClassGroup.mk0_eq_one_iff]
    change ((j : Ideal (𝓞 F)) ^ 2).IsPrincipal
    rw [hj, hJ2]
    exact ⟨⟨μ c, rfl⟩⟩
  let N := ClassGroup.relNorm (R := 𝓞 F) (S := 𝓞 K)
  have hjp : ClassGroup.mk0 j ^ p = 1 := by
    rw [← ClassGroup.relNorm_mk0, ← map_pow, hiPow, map_one]
  have hjOne : ClassGroup.mk0 j = 1 := by
    have horder := orderOf_dvd_of_pow_eq_one hjp
    rcases (Nat.dvd_prime hp).mp horder with h | h
    · exact orderOf_eq_one_iff.mp h
    · have hBad := h ▸ orderOf_dvd_of_pow_eq_one hjPow
      exact (Nat.not_dvd_of_pos_of_lt (by decide) hp2 hBad).elim
  let c' : N.ker := ⟨ClassGroup.mk0 i, by simpa only [MonoidHom.mem_ker,
    N, ClassGroup.relNorm_mk0, j] using hjOne⟩
  have horder : orderOf c' ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext hiPow)
  rw [← ClassGroup.mk0_eq_one_iff i.2]
  change ClassGroup.mk0 i = 1
  rcases (Nat.dvd_prime hp).mp horder with h | h
  · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
  · exact (hker (h ▸ orderOf_dvd_natCard c')).elim

end NormKernel


section CyclotomicReflection

variable {p : ℕ} [Fact p.Prime]
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem complexConj_primitiveRoot {n : ℕ} [NeZero n] [IsCMField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : IsCMField.complexConj K ζ = ζ⁻¹ := by
  obtain ⟨φ : K →+* ℂ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  let hφ := hζ.map_of_injective φ.injective
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_inv₀]
  have h := Complex.conj_rootsOfUnity hφ.toRootsOfUnity.2
  simpa only [starRingEnd_apply, Units.val_inv_eq_inv_val, hφ.val_toRootsOfUnity_coe] using h

private theorem exists_pow_eq_of_sq_of_odd {F : Type*} [Field F] {n : ℕ}
    (hn : Odd n) {x y : F} (hx : x ≠ 0) (hy : y ^ n = x ^ 2) :
    ∃ z : F, z ^ n = x := by
  obtain ⟨m, hm⟩ := hn
  refine ⟨y ^ (m + 1) / x, ?_⟩
  rw [div_pow, ← pow_mul, Nat.mul_comm, pow_mul, hy, ← pow_mul,
    show 2 * (m + 1) = n + 1 by omega, pow_succ,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hx)]

omit [NumberField L] in
private theorem isPrimitiveRoot_sq_of_pow {θ : L} (hθ : IsPrimitiveRoot (θ ^ p) p) :
    IsPrimitiveRoot θ (p ^ 2) := by
  have hp : p.Prime := Fact.out
  have hpow : θ ^ (p ^ 2) = 1 := by rw [pow_two, pow_mul, hθ.pow_eq_one]
  obtain ⟨e, he, horder⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hpow)
  have he2 : e = 2 := by
    by_contra hn
    have he1 : e ≤ 1 := by omega
    have hd : orderOf θ ∣ p := by
      rw [horder]
      simpa only [pow_one] using pow_dvd_pow p he1
    exact hθ.ne_one hp.one_lt (orderOf_dvd_iff_pow_eq_one.mp hd)
  exact IsPrimitiveRoot.iff_orderOf.mpr (he2 ▸ horder)

variable [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- An unramified nontrivial Kummer radical on which complex conjugation acts
by inversion modulo p-th powers supplies a p-factor of the relative norm kernel. -/
theorem dvd_relativeNormKernel_of_antiInvariant_unramified_radical
    (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) {a : 𝓞 K} (ha0 : a ≠ 0)
    (ha : ∀ z : K, z ^ p ≠ (a : K)) {b : K}
    (hb : b ^ p = (a : K) * IsCMField.complexConj K (a : K))
    {r : L} (hr : r ^ p = algebraMap K L (a : K))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    p ∣ Nat.card (ClassGroup.relNorm
      (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker := by
  by_contra hker
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  let c := IsCMField.complexConj K
  obtain ⟨I, hI⟩ := exists_ideal_pow_eq_span_singleton_of_unramified_root hp.pos ha0 hr hunr
  have hPI := isPrincipal_of_antiInvariant_radical_ideal hp hp2 hker
    (IsCMField.complexConj_ne_one K) ha0 hb hI
  obtain ⟨d, hd⟩ := hPI
  change I = Ideal.span {d} at hd
  have hspan : Ideal.span {d ^ p} = Ideal.span {a} := by
    rw [← Ideal.span_singleton_pow, ← hd, hI]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hd0 : (d : K) ≠ 0 := by
    intro h
    have hd' : d = 0 := RingOfIntegers.coe_injective h
    rw [hd', zero_pow hp.ne_zero, zero_mul] at hu
    exact ha0 hu.symm
  obtain ⟨⟨i, w⟩, huζ, -⟩ := existsUnique_root_mul_realUnit hζ hp2 u
  let w' : 𝓞 K := ((w : realCyclotomicIntegers hζ) : 𝓞 K)
  let v : K := w'
  have hv0 : v ≠ 0 := by
    intro hv
    exact w.ne_zero (Subtype.ext (RingOfIntegers.coe_injective hv))
  have hvfix : c v = v := by
    have hh := (mem_realCyclotomicIntegers_iff hζ hp2 w').mp
      (show w' ∈ realCyclotomicIntegers hζ from (w : realCyclotomicIntegers hζ).property)
    exact congrArg (fun x : 𝓞 K ↦ (x : K)) hh
  have huK : ((u : 𝓞 K) : K) = ζ ^ (i : ℕ) * v := by
    have hzI : algebraMap (𝓞 K) K hζ.toInteger = ζ := hζ.coe_toInteger
    have hh := congrArg (algebraMap (𝓞 K) K) huζ
    rw [map_mul, map_pow, hzI] at hh
    exact hh
  have haK : (a : K) = (d : K) ^ p * (ζ ^ (i : ℕ) * v) := by
    have h := congrArg (fun x : 𝓞 K ↦ (x : K)) hu.symm
    change (a : K) = algebraMap (𝓞 K) K (d ^ p * (u : 𝓞 K)) at h
    rw [map_mul, map_pow] at h
    exact h.trans (congrArg ((d : K) ^ p * ·) huK)
  let D : K := (d : K) * c (d : K)
  have hD : D ≠ 0 := mul_ne_zero hd0 ((map_ne_zero c).mpr hd0)
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have haProd : (a : K) * c (a : K) = D ^ p * v ^ 2 := calc
    _ = ((d : K) ^ p * (ζ ^ (i : ℕ) * v)) *
        ((c (d : K)) ^ p * ((ζ ^ (i : ℕ))⁻¹ * v)) := by
      nth_rw 1 [haK]
      rw [haK, map_mul, map_pow, map_mul, map_pow, complexConj_primitiveRoot hζ, inv_pow, hvfix]
    _ = D ^ p * (ζ ^ (i : ℕ) * (ζ ^ (i : ℕ))⁻¹) * v ^ 2 := by
      dsimp only [D]
      rw [mul_pow]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hζ0), mul_one]
  have hvPow : (b / D) ^ p = v ^ 2 := by
    rw [div_pow, hb, haProd, mul_div_cancel_left₀ _ (pow_ne_zero _ hD)]
  obtain ⟨s, hs⟩ := exists_pow_eq_of_sq_of_odd (hp.odd_of_ne_two (by omega)) hv0 hvPow
  let z : K := (d : K) * s
  have hz0 : z ≠ 0 := mul_ne_zero hd0 (fun h ↦ hv0 (by simpa [h, hp.ne_zero] using hs.symm))
  have haz : (a : K) = z ^ p * ζ ^ (i : ℕ) := by rw [haK, show z ^ p = _ from mul_pow _ _ _,
    hs, mul_assoc, mul_comm v]
  have hi0 : (i : ℕ) ≠ 0 := by
    intro hi
    exact ha z (by simpa [hi] using haz.symm)
  let θ := r / algebraMap K L z
  have hθ : θ ^ p = (algebraMap K L ζ) ^ (i : ℕ) := by
    dsimp only [θ]
    rw [div_pow, hr, haz, map_mul, map_pow, map_pow,
      mul_div_cancel_left₀ _ (pow_ne_zero _ ((map_ne_zero (algebraMap K L)).mpr hz0))]
  have hcop : (i : ℕ).Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hi0.bot_lt i.isLt)).symm
  have hprim : IsPrimitiveRoot (θ ^ p) p := hθ ▸
    (hζ.map_of_injective (algebraMap K L).injective).pow_of_coprime _ hcop
  exact not_isPrimitiveRoot_prime_sq_of_unramified hunr θ (isPrimitiveRoot_sq_of_pow hprim)

section Abelian

open scoped IsMulCommutative

variable [IsAbelianGalois (maximalRealSubfield K) L]

/-- An unramified relative extension of degree p that is abelian over the maximal real subfield
forces p to divide the relative class-group norm kernel of the prime cyclotomic field. -/
theorem dvd_relativeNormKernel_of_unramified_abelian_tower
    (hp2 : 2 < p) (hdegree : Module.finrank K L = p)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    p ∣ Nat.card (ClassGroup.relNorm
      (R := 𝓞 (maximalRealSubfield K)) (S := 𝓞 K)).ker := by
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  have : IsAbelianGalois K L := IsAbelianGalois.tower_top (maximalRealSubfield K) K L
  have : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K L).trans hdegree)
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
    (Set.mem_singleton p) hp.ne_zero
  have hζs : (primitiveRoots (Module.finrank K L) K).Nonempty := by
    rw [hdegree]
    exact ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩
  obtain ⟨r, ⟨α, hα⟩, hrgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hζs
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top hα.symm hrgen
  rw [hdegree] at hα hirr
  have hNoPower (z : K) : z ^ p ≠ α :=
    pow_ne_of_irreducible_X_pow_sub_C hirr dvd_rfl hp.ne_one z
  have hα0 : α ≠ 0 := fun h ↦ hNoPower 0 (by simp [hp.ne_zero, h])
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 K) α
  let a : 𝓞 K := x * y ^ (p - 1)
  have hy0 : (y : K) ≠ 0 :=
    RingOfIntegers.coe_eq_zero_iff.not.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hy)
  have ha : (a : K) = α * (y : K) ^ p := calc
    _ = (x : K) * (y : K) ^ (p - 1) := by change algebraMap (𝓞 K) K _ = _; simp [a]
    _ = (α * (y : K)) * (y : K) ^ (p - 1) := by
      have hxy' : (x : K) / (y : K) = α := hxy
      rw [← hxy', div_mul_cancel₀ _ hy0]
    _ = _ := by rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hp.pos]
  have ha0 : a ≠ 0 := by
    intro h
    exact mul_ne_zero hα0 (pow_ne_zero _ hy0) (by simpa [h] using ha.symm)
  have haNoPower (z : K) : z ^ p ≠ (a : K) := by
    intro h
    apply hNoPower (z / (y : K))
    rw [div_pow, h, ha, mul_div_cancel_right₀ _ (pow_ne_zero _ hy0)]
  let r' := r * algebraMap K L (y : K)
  have hr' : r' ^ p = algebraMap K L (a : K) := by
    rw [show r' ^ p = r ^ p * (algebraMap K L (y : K)) ^ p from mul_pow _ _ _,
      ← hα, ha, map_mul, map_pow]
  let σ := IsCMField.complexConj K
  let τ := σ.liftNormal L
  obtain ⟨b, hb⟩ := exists_pow_eq_mul_of_commuting_kummer_automorphism hζ
    (show (a : K) ≠ 0 from RingOfIntegers.coe_eq_zero_iff.not.mpr ha0) hr'
    σ.toRingEquiv τ.toRingEquiv (complexConj_primitiveRoot hζ)
    (AlgEquiv.liftNormal_commutes σ L) (by
      intro g z
      let g' := g.restrictScalars (maximalRealSubfield K)
      change (g' * τ) z = (τ * g') z
      rw [mul_comm])
  exact dvd_relativeNormKernel_of_antiInvariant_unramified_radical
    hp2 hζ ha0 haNoPower hb hr' hunr

end Abelian

end CyclotomicReflection

end TinyTauDemo
