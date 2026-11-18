/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Norm
import Mathlib.NumberTheory.RamificationInertia.Galois
import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal

/-!
# The norm of a uniformizer idele

The norm of a single uniformizer idele has order equal to the residue degree at the underlying
prime. Thus a character that kills integral finite ideles reads the same value from all
uniformizer ideles at primes over the same place of a Galois base extension.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `e74e1464a9abce7e83e565c5ccdf1957b5935bc6`.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField TauCeti
open TauCeti.GlobalNumberFields
open scoped NumberField AdicCompletionExtension

namespace TinyTauDemo

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem valued_uniformizer (w : HeightOneSpectrum (𝓞 E)) {π : (w.adicCompletion E)ˣ}
    (hπ : IsUniformizer (w.adicCompletion E) π) :
    Valued.v (π : w.adicCompletion E) = WithZero.exp (-1) := by
  apply inv_injective
  rw [← w.normalizedValuationWithZero_adicCompletion (K := E), normalizedValuationWithZero_coe,
    (isUniformizer_def π).mp hπ, ← WithZero.exp_eq_coe_ofAdd, ← WithZero.exp_neg]
  norm_num

private theorem valued_normUnits_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (x : (w.adicCompletion E)ˣ) :
    Valued.v ((Algebra.normUnits (v.adicCompletion K) x : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = Valued.v (x : w.adicCompletion E) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have := finite_of_valuativeExtension (v.adicCompletion K) (w.adicCompletion E)
  simpa only [Algebra.coe_normUnits, normalizedValuationWithZero_adicCompletion,
    inertiaDegree_def, finrank_residueField_adicCompletion, inv_pow, inv_inj] using
    normalizedValuationWithZero_norm (K := v.adicCompletion K) (x : w.adicCompletion E)

open scoped Classical in
/-- The only finite place where the norm of a single uniformizer idele has nonunit valuation
is the place below its support. There its order is the residue degree. -/
theorem valued_ideleNormMap_ofAdicCompletion_uniformizer (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) {π : (w.adicCompletion E)ˣ}
    (hπ : IsUniformizer (w.adicCompletion E) π) :
    Valued.v (v.ideleFiniteCoord (ideleNormMap K E (IdeleGroup.ofAdicCompletion (𝓞 E) E w π)) :
      v.adicCompletion K) =
        if w.under (𝓞 K) = v then (WithZero.exp (-1)) ^ w.asIdeal.inertiaDeg (𝓞 K) else 1 := by
  classical
  rw [ideleFiniteCoord_ideleNormMap]
  split_ifs with h
  · subst v
    let W : {u : HeightOneSpectrum (𝓞 E) // u.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal} :=
      ⟨w, inferInstance⟩
    rw [finprod_eq_single _ W, HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self,
      valued_normUnits_adicCompletion, valued_uniformizer w hπ]
    intro u hu
    have hne : u.1 ≠ w := fun he ↦ hu (Subtype.ext he)
    rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hne, map_one]
  · have he (u : {u : HeightOneSpectrum (𝓞 E) // u.asIdeal.LiesOver v.asIdeal}) : u.1 ≠ w := by
      intro hu
      apply h
      rw [← hu]
      exact HeightOneSpectrum.ext u.2.over.symm
    simp only [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ (he _),
      map_one, finprod_one, Units.val_one]

/-- An idele-class character trivial on integral finite ideles has the same value on the
norms of single uniformizer ideles supported at any two places over the same place. -/
theorem character_norm_ofAdicCompletion_uniformizer_eq [IsGalois K E]
    {A : Type*} [Group A] (χ : IdeleClassGroup (𝓞 K) K →* A)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K,
      IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K → χ x = 1)
    {w w' : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 K) = w'.under (𝓞 K))
    {π : (w.adicCompletion E)ˣ} {π' : (w'.adicCompletion E)ˣ}
    (hπ : IsUniformizer (w.adicCompletion E) π) (hπ' : IsUniformizer (w'.adicCompletion E) π') :
    χ (ideleClassNormMap K E (IdeleGroup.ofAdicCompletion (𝓞 E) E w π)) =
      χ (ideleClassNormMap K E (IdeleGroup.ofAdicCompletion (𝓞 E) E w' π')) := by
  classical
  let x := ideleNormMap K E (IdeleGroup.ofAdicCompletion (𝓞 E) E w π)
  let y := ideleNormMap K E (IdeleGroup.ofAdicCompletion (𝓞 E) E w' π')
  let v := w.under (𝓞 K)
  let : w'.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal h⟩
  have hinertia : w.asIdeal.inertiaDeg (𝓞 K) = w'.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal (E ≃ₐ[K] E)
  have hv (t : HeightOneSpectrum (𝓞 K)) :
      Valued.v (t.ideleFiniteCoord x : t.adicCompletion K) =
        Valued.v (t.ideleFiniteCoord y : t.adicCompletion K) := by
    simp only [x, y, valued_ideleNormMap_ofAdicCompletion_uniformizer _ _ hπ,
      valued_ideleNormMap_ofAdicCompletion_uniformizer _ _ hπ', hinertia, h]
  have hz : IdeleGroup.toFiniteIdele (𝓞 K) K (x / y) ∈
      FiniteAdeleRing.integralUnits (𝓞 K) K := by
    rw [FiniteAdeleRing.mem_integralUnits_iff]
    intro t
    rw [IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord]
    have hy : Valued.v (t.ideleFiniteCoord y : t.adicCompletion K) ≠ 0 :=
      (map_ne_zero _).mpr (Units.ne_zero _)
    rw [map_div, Units.val_div_eq_div_val, map_div₀, hv, div_self hy]
  have hxy := hχ (x / y) hz
  change χ ((x : IdeleClassGroup (𝓞 K) K) / (y : IdeleClassGroup (𝓞 K) K)) = 1 at hxy
  have hxy' : χ x = χ y := by
    rw [map_div] at hxy
    exact div_eq_one.mp hxy
  simpa only [ideleClassNormMap_mk, x, y] using hxy'

end TinyTauDemo
