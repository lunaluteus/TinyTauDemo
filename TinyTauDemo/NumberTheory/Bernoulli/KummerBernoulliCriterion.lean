/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.CyclotomicReflectionBaseChange
public import TinyTauDemo.NumberTheory.ClassFieldTheory.Hilbert.Existence

/-!
# Kummer's criterion for regular primes

A prime divisor of the real cyclotomic class number gives an unramified cyclic
extension of the real field. Kummer reflection then gives the same Bernoulli
numerator obstruction as divisibility of the relative class-group norm kernel.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `e74e1464a9abce7e83e565c5ccdf1957b5935bc6`.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TinyTauDemo

/-- An odd prime divides the class number of its cyclotomic field exactly when it
is Bernoulli irregular. -/
theorem dvd_cyclotomicClassNumber_iff_bernoulliIrregular {p : ℕ} [Fact p.Prime]
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] (hp2 : 2 < p) :
    p ∣ classNumber K ↔ BernoulliIrregular p := by
  rw [dvd_cyclotomicClassNumber_iff_dvd_real_or_bernoulliIrregular K hp2]
  refine ⟨?_, Or.inr⟩
  rintro (h | h)
  · obtain ⟨L, fld, nf, alg, gal, -, hdeg, hunr⟩ :=
      exists_unramified_cyclic_extension_of_dvd_classNumber (maximalRealSubfield K)
        (Fact.out : p.Prime) h
    exact bernoulliIrregular_of_unramified_real_extension (K := K) (H := L) hp2 hdeg hunr
  · exact h

/-- An odd prime is regular exactly when it is Bernoulli regular. -/
theorem regularPrime_iff_not_bernoulliIrregular {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    RegularPrime p ↔ ¬ BernoulliIrregular p := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (ho.ne_two_of_dvd_nat dvd_rfl).symm
  have hiff := dvd_cyclotomicClassNumber_iff_bernoulliIrregular (CyclotomicField p ℚ) hp2
  exact ⟨fun h ↦ mt hiff.mpr h.not_dvd_classNumber, fun h ↦ ⟨hp, ho, mt hiff.mp h⟩⟩

/-- An odd prime `p` is regular exactly when it divides none of the numerators of
`B₂, B₄, …, Bₚ₋₃`. -/
theorem regularPrime_iff_not_dvd_bernoulli_num {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    RegularPrime p ↔ ∀ k : ℕ, 0 < k → 2 * k ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  rw [regularPrime_iff_not_bernoulliIrregular hp ho, bernoulliIrregular_iff]
  simp only [hp, true_and, not_exists, not_and]

/-- The odd primes below 100 that divide their cyclotomic class numbers are 37, 59, and 67. -/
theorem dvd_cyclotomicClassNumber_below_100_iff {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hlt : p < 100) : p ∣ classNumber (CyclotomicField p ℚ) ↔ p = 37 ∨ p = 59 ∨ p = 67 := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (ho.ne_two_of_dvd_nat dvd_rfl).symm
  exact (dvd_cyclotomicClassNumber_iff_bernoulliIrregular (CyclotomicField p ℚ)
    hp2).trans (bernoulliIrregular_below_100_iff hlt)

/-- Every odd prime below 100 is regular except 37, 59, and 67. -/
theorem regularPrime_below_100_iff {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlt : p < 100) :
    RegularPrime p ↔ p ≠ 37 ∧ p ≠ 59 ∧ p ≠ 67 := by
  rw [regularPrime_iff_not_bernoulliIrregular hp ho, bernoulliIrregular_below_100_iff hlt]
  simp only [not_or]

end TinyTauDemo
