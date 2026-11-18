/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.FLT.Basic
public import TinyTauDemo.RegularPrime
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TinyTauDemo.CaseTwoValuations
import TinyTauDemo.CyclotomicCongruences
import TinyTauDemo.KummerCaseOne
import TinyTauDemo.KummerUnit
public import TinyTauDemo.PrimitiveFermatSolution
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Case II descent for a regular cyclotomic prime

The three factors of indices zero, one, and two supply a smaller solution.
Kummer's unit lemma makes the unit in the new equation a `p`th power.
See `/roadmap/index.qmd#thm-kummer-case-2` @ `39a5e9289c026f947635d7044187c1ed7df34ac3`.
-/

public section

open NumberField

namespace TinyTauDemo

/-- Eliminating the two linear variables gives an equation with the exceptional
exponent lowered by one. -/
private theorem caseTwo_eliminate {B : Type*} [CommRing B] [IsDomain B]
    {p n : ℕ} {x y ζ t₀ t₁ t₂ : B} (hn : 1 - ζ ≠ 0)
    (w v u₀ u₁ u₂ : Bˣ) (hw : (w : B) = ζ) (hv : (v : B) = 1 + ζ)
    (h₀ : x + y = (1 - ζ) ^ (n + 1) * ((u₀ : B) * t₀ ^ p))
    (h₁ : x + ζ * y = (1 - ζ) * ((u₁ : B) * t₁ ^ p))
    (h₂ : x + ζ ^ 2 * y = (1 - ζ ^ 2) * ((u₂ : B) * t₂ ^ p)) :
    ∃ ε ε' : Bˣ, t₁ ^ p - (ε : B) * t₂ ^ p = (ε' : B) * (1 - ζ) ^ n * t₀ ^ p := by
  let l := 1 - ζ
  have hlinear : l * (x + ζ ^ 2 * y) - (1 - ζ ^ 2) * (x + ζ * y) +
      (ζ - ζ ^ 2) * (x + y) = 0 := by
    dsimp [l]
    ring
  have hdiff : 1 - ζ ^ 2 = l * (v : B) := by rw [hv]; dsimp [l]; ring
  have hsub : ζ - ζ ^ 2 = l * (w : B) := by rw [hw]; dsimp [l]; ring
  rw [h₂, h₁, h₀, hdiff, hsub, pow_succ] at hlinear
  have hf : l * l * ((v : B) * (u₂ : B) * t₂ ^ p - (v : B) * (u₁ : B) * t₁ ^ p +
      (w : B) * (u₀ : B) * l ^ n * t₀ ^ p) = 0 := by
    linear_combination hlinear
  have hc := (mul_eq_zero.mp hf).resolve_left (mul_ne_zero hn hn)
  have hcombined : (v : B) * (u₁ : B) * t₁ ^ p =
      (v : B) * (u₂ : B) * t₂ ^ p + (w : B) * (u₀ : B) * l ^ n * t₀ ^ p := by
    linear_combination -hc
  let scale := (v * u₁)⁻¹
  let ε := scale * (v * u₂)
  let ε' := scale * (w * u₀)
  have hscale : (scale : B) * ((v : B) * (u₁ : B)) = 1 := by
    change (↑(scale * (v * u₁)) : B) = 1
    simp [scale]
  have hres : t₁ ^ p = (ε : B) * t₂ ^ p + (ε' : B) * l ^ n * t₀ ^ p := calc
    t₁ ^ p = (scale : B) * ((v : B) * (u₁ : B) * t₁ ^ p) := by
      rw [← mul_assoc, hscale, one_mul]
    _ = (scale : B) * ((v : B) * (u₂ : B) * t₂ ^ p +
        (w : B) * (u₀ : B) * l ^ n * t₀ ^ p) := congrArg _ hcombined
    _ = _ := by simp only [ε, ε', Units.val_mul]; ring
  refine ⟨ε, ε', ?_⟩
  rw [hres]
  ring

/-- If two powers have integer representatives modulo the rational prime, then
a unit relating them has an integer representative provided the second power
is prime to the cyclotomic uniformizer. -/
private theorem exists_int_congruent_of_dvd_pow_sub_mul_pow {B : Type*} [CommRing B]
    {p : ℕ} (hp : p.Prime) {l t₁ t₂ : B} (hl : Prime l) (hlp : l ∣ (p : B))
    (ht₂ : ¬ l ∣ t₂) (ε : Bˣ) {c₁ c₂ : ℤ}
    (hc₁ : (p : B) ∣ t₁ ^ p - (c₁ : B)) (hc₂ : (p : B) ∣ t₂ ^ p - (c₂ : B))
    (hd : (p : B) ∣ t₁ ^ p - (ε : B) * t₂ ^ p) :
    ∃ c : ℤ, (p : B) ∣ (ε : B) - (c : B) := by
  have hnot : ¬ (p : ℤ) ∣ c₂ := by
    intro h
    have hcast : (p : B) ∣ (c₂ : B) := by exact_mod_cast Int.cast_dvd_cast (α := B) _ _ h
    have := dvd_add (hlp.trans hc₂) (hlp.trans hcast)
    rw [sub_add_cancel] at this
    exact ht₂ (hl.dvd_of_dvd_pow this)
  have hpz : Prime (p : ℤ) := by simpa [Int.prime_iff_natAbs_prime] using hp
  obtain ⟨a, b, hab⟩ := hpz.coprime_iff_not_dvd.mpr hnot
  have hab' : (a : B) * (p : B) + (b : B) * (c₂ : B) = 1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one] using
      congrArg (fun n : ℤ ↦ (n : B)) hab
  have hdiff : (p : B) ∣ (c₁ : B) - (ε : B) * (c₂ : B) := by
    have h := dvd_add (dvd_sub hd hc₁) (dvd_mul_of_dvd_right hc₂ (ε : B))
    convert h using 1; ring
  refine ⟨b * c₁, ?_⟩
  rw [Int.cast_mul, show (ε : B) - (b : B) * (c₁ : B) =
      (ε : B) * (a : B) * (p : B) - (b : B) * ((c₁ : B) - (ε : B) * (c₂ : B)) by
    calc
      (ε : B) - (b : B) * (c₁ : B) =
          (ε : B) * ((a : B) * (p : B) + (b : B) * (c₂ : B)) - (b : B) * (c₁ : B) := by
            rw [hab', mul_one]
      _ = _ := by ring]
  exact dvd_sub (dvd_mul_left _ _) (dvd_mul_of_dvd_right hdiff _)

open scoped Classical in
/-- One descent step, assuming Kummer's unit lemma at the given regular prime. -/
private theorem RegularPrime.caseTwo_descent_step {p m : ℕ} (hr : RegularPrime p)
    [Fact p.Prime] {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hm : 1 ≤ m) (hxy : IsCoprime x y) (hy : ¬ (1 - hζ.toInteger) ∣ y)
    (hz : ¬ (1 - hζ.toInteger) ∣ z)
    (heq : x ^ p + y ^ p = (u : 𝓞 (CyclotomicField p ℚ)) * (1 - hζ.toInteger) ^ (m * p) * z ^ p) :
    let B := 𝓞 (CyclotomicField p ℚ)
    let l := 1 - hζ.toInteger
    1 ≤ m - 1 ∧ ∃ (x' y' z' : B) (u' : Bˣ),
      IsCoprime x' y' ∧ IsCoprime x' z' ∧ IsCoprime y' z' ∧
      (¬ l ∣ x') ∧ (¬ l ∣ y') ∧ (¬ l ∣ z') ∧
      x' ^ p + y' ^ p = (u' : B) * l ^ ((m - 1) * p) * z' ^ p := by
  classical
  let _ : NeZero p := ⟨hr.prime.ne_zero⟩
  let _ : NeZero (p : ℚ) := ⟨by exact_mod_cast hr.prime.ne_zero⟩
  let _ : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let B := 𝓞 (CyclotomicField p ℚ)
  let root : B := hζ.toInteger
  let l : B := 1 - root
  have hp2 : p ≠ 2 := hr.odd.ne_two_of_dvd_nat dvd_rfl
  have hpgt : 2 < p := lt_of_le_of_ne hr.prime.two_le hp2.symm
  have hroot : IsPrimitiveRoot root p := hζ.toInteger_isPrimitiveRoot
  have hl : Prime l := by
    dsimp only [l, root]
    rw [← neg_sub]
    exact (Associated.refl _).neg_right.prime hζ.zeta_sub_one_prime'
  have hpc : (p : B) ∣ l ^ (p - 1) ∧ l ^ (p - 1) ∣ (p : B) :=
    ⟨by rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.span_singleton_pow,
        hζ.span_natCast_eq_span_one_sub_pow],
      by rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.span_singleton_pow,
        hζ.span_natCast_eq_span_one_sub_pow]⟩
  obtain ⟨hm2, _, jt, b, a, _, hpair, hfact⟩ :=
    caseTwo_valuations hζ hp2 hxy hy hz hm u heq
  have hprinc (j : Fin p) : (a j).IsPrincipal := by
    apply Ideal.IsPrincipal.of_isPrincipal_pow_of_coprime hr.coprime_classNumber
    rw [← (hfact j).2.2.1]
    exact ⟨b j, rfl⟩
  have hgen (j : Fin p) : ∃ t : B, a j = Ideal.span {t} := (hprinc j).principal
  choose t ht using hgen
  have htPow (j : Fin p) : Ideal.span {t j ^ p} = Ideal.span {b j} := by
    rw [← Ideal.span_singleton_pow, ← ht, (hfact j).2.2.1]
  have hgenPair : Pairwise (fun i j ↦ IsCoprime (t i) (t j)) := by
    intro i j hij
    apply (IsCoprime.pow_iff hr.prime.pos hr.prime.pos).mp
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [htPow, htPow]
    exact hpair hij
  have haway (j : Fin p) : ¬ l ∣ t j := by
    intro h
    apply hl.not_isUnit
    have hc : IsCoprime (t j ^ p) l := by
      apply (Ideal.isCoprime_span_singleton_iff _ _).mp
      rw [htPow]
      exact (hfact j).2.2.2
    exact ((IsCoprime.pow_left_iff hr.prime.pos).mp hc).symm.isUnit_of_dvd h
  have hassoc (j : Fin p) : ∃ v : Bˣ, b j = (v : B) * t j ^ p := by
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp (htPow j)
    exact ⟨v, hv.symm.trans (mul_comm _ _)⟩
  choose v hv using hassoc
  let j₀ : Fin p := ⟨0, hr.prime.pos⟩
  let j₁ : Fin p := ⟨1, hr.prime.one_lt⟩
  let j₂ : Fin p := ⟨2, hpgt⟩
  let y' := root ^ jt.val * y
  have hindex : m * p - (p - 1) = (m - 1) * p + 1 := by
    have hle := Nat.mul_le_mul_right p hm
    rw [one_mul] at hle
    rw [Nat.sub_mul, one_mul]
    have := hr.prime.pos
    omega
  have h₀ : x + y' = l ^ ((m - 1) * p + 1) * ((v j₀ : B) * t j₀ ^ p) := by
    simpa only [j₀, y', root, l, ite_true, pow_zero, one_mul, hindex, hv] using (hfact j₀).2.1
  have h₁ : x + root * y' = l * ((v j₁ : B) * t j₁ ^ p) := by
    simpa only [j₁, y', root, l, Nat.one_ne_zero, ite_false, pow_one, hv] using (hfact j₁).2.1
  have h₂ : x + root ^ 2 * y' = (1 - root ^ 2) * ((v j₂ : B) * t j₂ ^ p) := by
    simpa only [j₂, y', root, Nat.succ_ne_zero, ite_false, hv] using (hfact j₂).2.1
  obtain ⟨w, hw⟩ := hroot.isUnit hr.prime.ne_zero
  have hwunit : IsUnit (1 + root) := by
    have hcop := (Nat.coprime_of_lt_prime (by decide : 2 ≠ 0) hpgt hr.prime).symm
    simpa [Finset.sum_range_succ] using hroot.geom_sum_isUnit hr.prime.two_le hcop
  obtain ⟨v₂, hv₂⟩ := hwunit
  obtain ⟨ε, ε', hε⟩ :=
    caseTwo_eliminate hl.ne_zero w v₂ (v j₀) (v j₁) (v j₂) hw hv₂ h₀ h₁ h₂
  have hm' : 1 ≤ m - 1 := by omega
  have hrhs : (p : B) ∣ t j₁ ^ p - (ε : B) * t j₂ ^ p := by
    have hle : p - 1 ≤ (m - 1) * p :=
      (Nat.sub_le p 1).trans (by simpa using Nat.mul_le_mul_right p hm')
    rw [hε]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
      (hpc.1.trans (pow_dvd_pow l hle)) _) _
  obtain ⟨c₁, _, _, hc₁⟩ := exists_int_pow_congruent hζ (t j₁)
  obtain ⟨c₂, _, _, hc₂⟩ := exists_int_pow_congruent hζ (t j₂)
  have hlp : l ∣ (p : B) :=
    (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hr.prime.one_lt)).trans hpc.2
  obtain ⟨η, hη⟩ := hr.kummer_unit ε
    (exists_int_congruent_of_dvd_pow_sub_mul_pow hr.prime hl hlp (haway j₂) ε hc₁ hc₂ hrhs)
  let y'' := -(η : B) * t j₂
  have hηu : IsUnit (-(η : B)) := η.isUnit.neg
  have h₁₂ : j₁ ≠ j₂ := fun h ↦ (show (1 : ℕ) ≠ 2 by decide) (congrArg Fin.val h)
  have h₁₀ : j₁ ≠ j₀ := fun h ↦ (show (1 : ℕ) ≠ 0 by decide) (congrArg Fin.val h)
  have h₂₀ : j₂ ≠ j₀ := fun h ↦ (show (2 : ℕ) ≠ 0 by decide) (congrArg Fin.val h)
  refine ⟨hm', t j₁, y'', t j₀, ε', ?_, hgenPair h₁₀, ?_, haway j₁, ?_, haway j₀, ?_⟩
  · exact (isCoprime_mul_unit_left_right hηu _ _).mpr (hgenPair h₁₂)
  · exact (isCoprime_mul_unit_left_left hηu _ _).mpr (hgenPair h₂₀)
  · dsimp only [y'']
    rw [mul_comm, hηu.dvd_mul_right]
    exact haway j₂
  · dsimp only [y'']
    rw [mul_pow, hr.odd.neg_pow, ← Units.val_pow_eq_pow_val, hη, neg_mul, ← sub_eq_add_neg]
    exact hε

/-- The Case II equation has no solutions at a regular prime. -/
theorem RegularPrime.caseTwo_no_solution {p m : ℕ} (hr : RegularPrime p)
    [Fact p.Prime] {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hm : 1 ≤ m) (hxy : IsCoprime x y) (hy : ¬ (1 - hζ.toInteger) ∣ y)
    (hz : ¬ (1 - hζ.toInteger) ∣ z) :
    x ^ p + y ^ p ≠ (u : 𝓞 (CyclotomicField p ℚ)) * (1 - hζ.toInteger) ^ (m * p) * z ^ p := by
  induction m using Nat.strong_induction_on generalizing x y z u with
  | h m ih =>
    intro heq
    obtain ⟨hm', x', y', z', u', hxy', _, _, _, hy', hz', heq'⟩ :=
      hr.caseTwo_descent_step hζ u hm hxy hy hz heq
    exact ih (m - 1) (by omega) u' hm' hxy' hy' hz' heq'

/-- An integer Fermat solution with the prime dividing its right-hand coordinate
induces a solution of the cyclotomic Case II equation. -/
private theorem RegularPrime.not_fermat_eq_of_dvd_right {p : ℕ} (hr : RegularPrime p)
    [Fact p.Prime] {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : ℤ} (hxy : IsCoprime x y) (hyz : IsCoprime y z)
    (hz : z ≠ 0) (hd : (p : ℤ) ∣ z) : x ^ p + y ^ p ≠ z ^ p := by
  intro heq
  let _ : NeZero p := ⟨hr.prime.ne_zero⟩
  let _ : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  let B := 𝓞 (CyclotomicField p ℚ)
  let l : B := 1 - hζ.toInteger
  have hl : Prime l := by
    dsimp only [l]
    rw [← neg_sub]
    exact (Associated.refl _).neg_right.prime hζ.zeta_sub_one_prime'
  have hpdiv : l ^ (p - 1) ∣ (p : B) := by
    rw [← Ideal.span_singleton_le_span_singleton, ← Ideal.span_singleton_pow,
      hζ.span_natCast_eq_span_one_sub_pow]
  have hlz : l ∣ (z : B) := by
    have hcast : (p : B) ∣ (z : B) := by
      simpa only [Int.cast_natCast] using Int.cast_dvd_cast (α := B) _ _ hd
    exact (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hr.prime.one_lt)).trans (hpdiv.trans hcast)
  have hy : ¬ l ∣ (y : B) := fun h ↦
    hl.not_isUnit ((hyz.map (Int.castRingHom B)).isUnit_of_dvd' h hlz)
  have hz0 : (z : B) ≠ 0 := by exact_mod_cast hz
  obtain ⟨k, hk⟩ := Ideal.finiteMultiplicity
    (Ideal.span_singleton_eq_top.not.mpr hl.not_isUnit)
    (Ideal.span_singleton_eq_bot.not.mpr hz0)
  have hfin : FiniteMultiplicity l (z : B) := by
    refine ⟨k, fun h ↦ hk ?_⟩
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd]
  obtain ⟨γ, hγ, hγaway⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  let m := multiplicity l (z : B)
  have hm : 1 ≤ m := Nat.pos_of_ne_zero ((multiplicity_ne_zero hfin).mpr hlz)
  apply hr.caseTwo_no_solution hζ 1 hm (hxy.map (Int.castRingHom B)) hy hγaway
  have hcast := congrArg (fun w : ℤ ↦ (w : B)) heq
  simp only [Int.cast_add, Int.cast_pow] at hcast
  have hzpow := congrArg (fun a : B ↦ a ^ p) hγ
  change (z : B) ^ p = (l ^ m * γ) ^ p at hzpow
  rw [mul_pow, ← pow_mul] at hzpow
  simpa only [Int.coe_castRingHom, Units.val_one, one_mul, l, B] using hcast.trans hzpow

/-- Kummer's first and second cases rule out primitive integer solutions at a regular prime. -/
theorem RegularPrime.not_primitiveFermatSolution {p : ℕ} (hr : RegularPrime p)
    {x y z : ℤ} : ¬ PrimitiveFermatSolution p x y z := by
  intro h
  let _ : Fact p.Prime := ⟨hr.prime⟩
  let _ : NeZero p := ⟨hr.prime.ne_zero⟩
  let _ : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hpz : Prime (p : ℤ) := by simpa [Int.prime_iff_natAbs_prime] using hr.prime
  by_cases hdiv : (p : ℤ) ∣ x * y * z
  · rcases hpz.dvd_mul.mp hdiv with hxy | hz
    · rcases hpz.dvd_mul.mp hxy with hx | hy
      · apply hr.not_fermat_eq_of_dvd_right hζ h.coprime_yz.neg_right
          h.coprime_zx.neg_neg (neg_ne_zero.mpr h.x_ne_zero) (dvd_neg.mpr hx)
        simp only [hr.odd.neg_pow]
        linear_combination h.eq
      · apply hr.not_fermat_eq_of_dvd_right hζ h.coprime_zx.symm.neg_right
          h.coprime_yz.symm.neg_neg (neg_ne_zero.mpr h.y_ne_zero) (dvd_neg.mpr hy)
        simp only [hr.odd.neg_pow]
        linear_combination h.eq
    · exact hr.not_fermat_eq_of_dvd_right hζ h.coprime_xy h.coprime_yz
        h.z_ne_zero hz h.eq
  · have hnodvd : ¬ (p : ℤ) ∣ x * y * (-z) := by
      simpa only [mul_neg, dvd_neg] using hdiv
    apply kummer_case_I hr hnodvd
    rw [hr.odd.neg_pow, ← sub_eq_add_neg, sub_eq_zero]
    exact h.eq

/-- Fermat's last theorem over the integers at each regular prime. -/
theorem RegularPrime.fermatLastTheoremWith {p : ℕ} (hr : RegularPrime p)
    : FermatLastTheoremWith ℤ p := by
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hg heq
  have hF : a ^ p + b ^ p + (-c) ^ p = 0 := by
    rw [hr.odd.neg_pow, heq, add_neg_cancel]
  have hg' : ({a, b, -c} : Finset ℤ).gcd id = 1 := by
    simpa only [Finset.gcd_insert, Finset.gcd_singleton, id_eq, ← Int.abs_eq_normalize, abs_neg]
      using hg
  have hab := isCoprime_of_gcd_eq_one_of_FLT hg' hF
  have hset₁ : ({b, -c, a} : Finset ℤ) = {a, b, -c} := by
    ext x
    simp [or_comm, or_left_comm]
  have hbc : IsCoprime b (-c) :=
    isCoprime_of_gcd_eq_one_of_FLT (hset₁ ▸ hg')
      (by simpa only [add_comm, add_left_comm, add_assoc] using hF)
  have hset₂ : ({-c, a, b} : Finset ℤ) = {a, b, -c} := by
    ext x
    simp [or_comm, or_assoc]
  have hca : IsCoprime (-c) a :=
    isCoprime_of_gcd_eq_one_of_FLT (hset₂ ▸ hg')
      (by simpa only [add_comm, add_left_comm, add_assoc] using hF)
  refine hr.not_primitiveFermatSolution ⟨heq, hab, ?_, ?_, ha, hb, hc, ?_⟩
  · simpa only [neg_neg] using hbc.neg_right
  · simpa only [neg_neg] using hca.neg_left
  · rintro ⟨ha', hb', hc'⟩
    rcases Int.isUnit_iff.mp ha' with rfl | rfl <;>
      rcases Int.isUnit_iff.mp hb' with rfl | rfl <;>
      rcases Int.isUnit_iff.mp hc' with rfl | rfl <;>
      norm_num [hr.odd.neg_one_pow] at heq

end TinyTauDemo
