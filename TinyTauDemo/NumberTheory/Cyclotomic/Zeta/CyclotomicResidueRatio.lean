/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicRealDiscriminant
public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicUnits
public import Mathlib.NumberTheory.NumberField.DedekindZeta
import TauCeti.NumberTheory.NumberField.Units.Torsion
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# Dedekind-zeta residue ratios for CM fields

The analytic class-number formula and the regulator comparison give the
residue ratio against the maximal real subfield. In an odd-prime cyclotomic
field the real-unit index is one and the number of roots of unity is twice
the conductor.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4e4554e0be56c8c2d2c6edbca48ac7d6ed9e4f16`.
-/

public section

open NumberField NumberField.InfinitePlace IsCMField
open scoped Real NumberField

namespace TinyTauDemo

section CM

open NumberField.Units

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

local notation "K⁺" => maximalRealSubfield K

private theorem nrRealPlaces_maximalRealSubfield :
    nrRealPlaces K⁺ = nrComplexPlaces K := by
  have h := IsCMField.card_infinitePlace_eq_card_infinitePlace K
  rwa [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero K, IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero, zero_add] at h

omit [IsCMField K] in
private theorem torsionOrder_maximalRealSubfield :
    torsionOrder K⁺ = 2 := by
  let w : InfinitePlace K⁺ := Classical.choice (inferInstance : Nonempty _)
  exact TauCeti.NumberField.Units.torsionOrder_eq_two_of_isReal
    (IsTotallyReal.isReal w)

private theorem rank_eq_nrComplexPlaces_sub_one :
    rank K = nrComplexPlaces K - 1 := by
  rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero K,
    zero_add]

/-- The ratio of Dedekind-zeta residues for a CM field and its maximal real subfield,
after canceling the regulator using the real-unit index. -/
theorem cm_dedekindZeta_residue_div :
    dedekindZeta_residue K / dedekindZeta_residue K⁺ =
      (2 * π) ^ nrComplexPlaces K /
        ((IsCMField.indexRealUnits K : ℝ) * torsionOrder K) *
        (Real.sqrt |(discr K⁺ : ℝ)| / Real.sqrt |(discr K : ℝ)|) *
        ((classNumber K : ℝ) / classNumber K⁺) := by
  let r := nrComplexPlaces K
  have hr : 0 < r := by
    have hp : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
    rwa [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero K,
      zero_add] at hp
  have hR := IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv K
  rw [rank_eq_nrComplexPlaces_sub_one] at hR
  have hRpos := (regulator_pos K⁺).ne'
  have hQ : (IsCMField.indexRealUnits K : ℝ) ≠ 0 := by
    rcases IsCMField.indexRealUnits_eq_one_or_two K with h | h <;> simp [h]
  have hsK : Real.sqrt |(discr K : ℝ)| ≠ 0 :=
    (Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))).ne'
  have hsR : Real.sqrt |(discr K⁺ : ℝ)| ≠ 0 :=
    (Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K⁺)))).ne'
  have htK : (torsionOrder K : ℝ) ≠ 0 := by exact_mod_cast (torsionOrder_pos K).ne'
  have hhK : (classNumber K⁺ : ℝ) ≠ 0 := by exact_mod_cast classNumber_ne_zero K⁺
  have hpow : (2 : ℝ) ^ r = 2 ^ (r - 1) * 2 := by
    conv_lhs => rw [show r = r - 1 + 1 by omega, pow_succ]
  calc
    _ =
      ((2 * π) ^ r / 2 ^ r) * (regulator K / regulator K⁺) *
        (2 / (torsionOrder K : ℝ)) *
        (Real.sqrt |(discr K⁺ : ℝ)| / Real.sqrt |(discr K : ℝ)|) *
        ((classNumber K : ℝ) / classNumber K⁺) := by
      rw [dedekindZeta_residue_def, dedekindZeta_residue_def,
        IsTotallyComplex.nrRealPlaces_eq_zero K, IsTotallyReal.nrComplexPlaces_eq_zero K⁺,
        nrRealPlaces_maximalRealSubfield, torsionOrder_maximalRealSubfield]
      field_simp
      ring
    _ = _ := by
      change _ = (2 * π) ^ r / _ * _ * _
      rw [hR, hpow]
      field_simp
      ring

end CM

section Cyclotomic

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

private noncomputable def primeRootUnit : (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem primeRootUnit_val : (primeRootUnit hζ : 𝓞 K) = hζ.toInteger :=
  IsUnit.unit_spec _

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem primeRootUnit_coe : (primeRootUnit hζ : K) = ζ := by
  rw [← NumberField.Units.coe_coe, primeRootUnit_val]
  rfl

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem primeRootUnit_isPrimitiveRoot : IsPrimitiveRoot (primeRootUnit hζ) p :=
  hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem primeRootUnit_mem_torsion : primeRootUnit hζ ∈ NumberField.Units.torsion K :=
  (CommGroup.mem_torsion _).2 ((primeRootUnit_isPrimitiveRoot hζ).isOfFinOrder (NeZero.ne p))

include hζ in
/-- The real-unit index of a prime cyclotomic field of odd conductor is one. -/
theorem cyclotomic_indexRealUnits_eq_one (hp : 2 < p) [IsCMField K] :
    indexRealUnits K = 1 := by
  apply Subgroup.index_eq_one.mpr
  apply top_unique
  intro u _
  obtain ⟨⟨r, w⟩, hr, _⟩ := existsUnique_root_mul_realUnit hζ hp u
  let wK := _root_.Units.map (realCyclotomicIntegers hζ).val.toMonoidHom w
  have hw : wK ∈ realUnits K := by
    apply (unitsComplexConj_eq_self_iff K _).mp
    apply _root_.Units.ext
    exact (mem_realCyclotomicIntegers_iff hζ hp _).mp
      (show ((w : realCyclotomicIntegers hζ) : 𝓞 K) ∈ realCyclotomicIntegers hζ from w.val.property)
  have hu : u = (primeRootUnit hζ) ^ (r : ℕ) * wK := by
    apply _root_.Units.ext
    change (u : 𝓞 K) = ((primeRootUnit hζ ^ (r : ℕ) : (𝓞 K)ˣ) : 𝓞 K) *
      ((w : realCyclotomicIntegers hζ) : 𝓞 K)
    simpa only [_root_.Units.val_pow_eq_pow_val, primeRootUnit_val] using hr
  rw [hu]
  exact (realUnits K ⊔ NumberField.Units.torsion K).mul_mem
    ((le_sup_right : NumberField.Units.torsion K ≤ _) (pow_mem (primeRootUnit_mem_torsion hζ) _))
    ((le_sup_left : realUnits K ≤ _) hw)

include hζ in
/-- A prime cyclotomic field of odd conductor has exactly twice the conductor
roots of unity. -/
theorem cyclotomic_torsionOrder_eq_two_mul (hp : 2 < p) :
    NumberField.Units.torsionOrder K = 2 * p := by
  have hp' : p.Prime := Fact.out
  have hpo : Odd p := hp'.odd_of_ne_two (by omega)
  have h2 : 2 ∣ NumberField.Units.torsionOrder K :=
    Even.two_dvd (NumberField.Units.even_torsionOrder K)
  have hpt : p ∣ NumberField.Units.torsionOrder K := by
    rw [(primeRootUnit_isPrimitiveRoot hζ).eq_orderOf]
    exact (NumberField.Units.torsion K).orderOf_dvd_natCard (primeRootUnit_mem_torsion hζ)
  have hcop : Nat.Coprime 2 p := (hp'.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) hp)).symm
  apply Nat.dvd_antisymm _ (hcop.mul_dvd_of_dvd_of_dvd h2 hpt)
  rw [NumberField.Units.torsionOrder, ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd]
  intro u
  rw [orderOf_dvd_iff_pow_eq_one]
  apply Subtype.ext
  apply NumberField.Units.coe_injective K
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, NumberField.Units.coe_pow,
    NumberField.Units.coe_one]
  have hu : IsOfFinOrder (u.val : K) := by
    have h : IsOfFinOrder u.val := (CommGroup.mem_torsion _).1 u.property
    exact (Function.Injective.isOfFinOrder_iff
      (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (_root_.Units.coeHom (𝓞 K)))
      (NumberField.Units.coe_injective K)).2 h
  obtain ⟨r, _, he | he⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo hu
  · rw [he, show 2 * p = p * 2 by omega, pow_mul, ← pow_mul ζ, Nat.mul_comm r p,
      pow_mul, hζ.pow_eq_one, one_pow, one_pow]
  · rw [he, pow_mul, neg_sq, ← pow_mul, Nat.mul_comm 2 p, pow_mul, ← pow_mul ζ,
      Nat.mul_comm r p, pow_mul, hζ.pow_eq_one, one_pow, one_pow]


include hζ in
/-- The residue ratio for a prime cyclotomic field with odd conductor, in terms of
its class number and that of its maximal real subfield. -/
theorem cyclotomic_dedekindZeta_residue_div (hp : 2 < p) :
    dedekindZeta_residue K / dedekindZeta_residue (maximalRealSubfield K) =
      (2 * π) ^ nrComplexPlaces K / (2 * p : ℝ) *
        (Real.sqrt |(discr (maximalRealSubfield K) : ℝ)| / Real.sqrt |(discr K : ℝ)|) *
        ((classNumber K : ℝ) / classNumber (maximalRealSubfield K)) := by
  have : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  rw [cm_dedekindZeta_residue_div, cyclotomic_indexRealUnits_eq_one hζ hp,
    cyclotomic_torsionOrder_eq_two_mul hζ hp]
  push_cast
  rw [one_mul]

end Cyclotomic

section Explicit

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ K]

/-- The Dedekind-zeta residue ratio of an odd-prime cyclotomic field and its maximal
real subfield, with the coefficient written entirely in terms of the conductor. -/
theorem cyclotomic_dedekindZeta_residue_div_explicit (hp2 : p ≠ 2) :
    dedekindZeta_residue K / dedekindZeta_residue (maximalRealSubfield K) =
      (2 * π) ^ ((p - 1) / 2) / ((2 * p : ℝ) * Real.sqrt ((p : ℝ) ^ ((p - 1) / 2))) *
        ((classNumber K : ℝ) / classNumber (maximalRealSubfield K)) := by
  have hpge := hp.out.two_le
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  rw [cyclotomic_dedekindZeta_residue_div hζ (by omega),
    cyclotomic_real_sqrt_discr_div (K := K) (p := p) hp2,
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p K,
    Nat.totient_prime hp.out]
  simp only [div_mul_div_comm, mul_one]

end Explicit

end TinyTauDemo
