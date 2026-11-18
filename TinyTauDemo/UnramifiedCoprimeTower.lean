/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Unramifiedness in a coprime compositum

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `9e49cf86a2f12f4c30fb1657d2e228b79f3a2a77`.
-/

public section

open NumberField IsDedekindDomain
open scoped NumberField

namespace TinyTauDemo

private theorem ramificationIdx_dvd_finrank_of_numberField_isGalois
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.ramificationIdx (𝓞 K) ∣ Module.finrank K L := by
  let v := w.asIdeal.under (𝓞 K)
  have : w.asIdeal.IsPrime := w.isPrime
  have : v.IsPrime := Ideal.IsPrime.under _ _
  let := IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hi := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v (𝓞 L) (L ≃ₐ[K] L)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v w.asIdeal (L ≃ₐ[K] L),
    IsGalois.card_aut_eq_finrank] at hi
  rw [← hi]
  exact (dvd_mul_right _ _).trans (dvd_mul_left _ _)

variable {F E H L : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  [Field H] [NumberField H] [Field L] [NumberField L]
  [Algebra F E] [Algebra F H] [Algebra F L] [Algebra E L] [Algebra H L]
  [IsScalarTower F E L] [IsScalarTower F H L] [IsGalois E L] [IsGalois H L]

/-- If the degrees of two Galois extensions in the top of a pair of towers are
coprime and one of the bottom extensions is unramified, the other top extension
is unramified. -/
theorem isUnramifiedAt_of_coprime_galois_towers
    (hcop : (Module.finrank E L).Coprime (Module.finrank H L))
    (hunr : ∀ w : HeightOneSpectrum (𝓞 H), Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal)
    (w : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal := by
  let P := w.asIdeal
  let Q := P.under (𝓞 H)
  let R := P.under (𝓞 E)
  have : P.IsPrime := w.isPrime
  have : Q.IsPrime := Ideal.IsPrime.under _ _
  have : R.IsPrime := Ideal.IsPrime.under _ _
  let q : HeightOneSpectrum (𝓞 H) := ⟨Q, inferInstance, Ideal.under_ne_bot _ w.ne_bot⟩
  have : Algebra.IsUnramifiedAt (𝓞 F) Q := hunr q
  have hQ := Ideal.ramificationIdx_eq_one Q (𝓞 F)
  have hP : P.ramificationIdx (𝓞 F) = P.ramificationIdx (𝓞 H) := by
    rw [Ideal.ramificationIdx_tower (R := 𝓞 F) Q P, hQ, one_mul]
  have hdiv : P.ramificationIdx (𝓞 E) ∣ P.ramificationIdx (𝓞 H) := by
    rw [← hP, Ideal.ramificationIdx_tower (R := 𝓞 F) R P]
    exact dvd_mul_left _ _
  have he : P.ramificationIdx (𝓞 E) = 1 :=
    Nat.dvd_one.mp ((Nat.dvd_gcd
      (ramificationIdx_dvd_finrank_of_numberField_isGalois (K := E) w)
      (hdiv.trans (ramificationIdx_dvd_finrank_of_numberField_isGalois (K := H) w))).trans
      (dvd_of_eq hcop.gcd_eq_one))
  let : Finite ((𝓞 E) ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (Ideal.under_ne_bot _ w.ne_bot)
  exact Ideal.ramificationIdx_eq_one_iff.mp he

end TinyTauDemo
