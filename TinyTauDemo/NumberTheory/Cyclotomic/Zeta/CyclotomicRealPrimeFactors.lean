/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.Cyclotomic.Zeta.CyclotomicPrimeFactors
public import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield
import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Euler factors of a maximal real cyclotomic subfield

Characters of the real subfield pull back to the even characters. Restricting
Frobenius computes the inertia degree away from the conductor. At the
conductor, both fields have a single factor of residue degree one.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `19d05f674280fce4d59c513fd4da7aafdc84ca61`.
-/

public section

open NumberField Ideal IntermediateField TauCeti.IsCyclotomicExtension.Rat
open scoped BigOperators NumberField IsMulCommutative

namespace TinyTauDemo

variable (K : Type*) [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ K] [IsAbelianGalois ℚ K]

local notation "eGal" => IsCyclotomicExtension.Rat.galEquivZMod p K
local notation "σc" => MulEquiv.symm (IsCyclotomicExtension.Rat.galEquivZMod p K) (-1)
local notation "H" => Subgroup.zpowers σc
local notation "F" => IntermediateField.fixedField H

private noncomputable def galCharOfRealChar (χ : Gal(F/ℚ) →* ℂˣ) : DirichletCharacter ℂ p :=
  MulChar.ofUnitHom (χ.comp ((AlgEquiv.restrictNormalHom F).comp (eGal).symm.toMonoidHom))

private theorem galCharOfRealChar_eval (χ : Gal(F/ℚ) →* ℂˣ) (u : (ZMod p)ˣ) :
    galCharOfRealChar K χ u = (χ (((eGal).symm u).restrictNormal F) : ℂ) := by
  rw [galCharOfRealChar, MulChar.ofUnitHom_coe]
  rfl

private theorem galCharOfRealChar_even (χ : Gal(F/ℚ) →* ℂˣ) :
    (galCharOfRealChar K χ).Even := by
  have : Normal ℚ F :=
    (IsGalois.of_fixedField_normal_subgroup H).to_normal
  have hk : (AlgEquiv.restrictNormalHom F).ker = H :=
    (IntermediateField.restrictNormalHom_ker (K := ℚ) (L := K) F).trans
      (fixingSubgroup_fixedField H)
  have hc : (AlgEquiv.restrictNormalHom F) σc = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hk]
    exact Subgroup.mem_zpowers _
  have hval : ((-1 : (ZMod p)ˣ) : ZMod p) = -1 := by simp
  rw [DirichletCharacter.Even, ← hval, galCharOfRealChar_eval]
  change (χ ((AlgEquiv.restrictNormalHom F) σc) : ℂ) = 1
  rw [hc, map_one, Units.val_one]

private noncomputable def evenCharacterEquiv :
    (Gal(F/ℚ) →* ℂˣ) ≃ {χ : DirichletCharacter ℂ p // χ.Even} := by
  refine Equiv.ofBijective (fun χ ↦ ⟨galCharOfRealChar K χ, galCharOfRealChar_even K χ⟩)
    ⟨?_, ?_⟩
  · intro χ ψ heq
    ext τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective K τ
    have h := congrArg (fun x : {χ : DirichletCharacter ℂ p // χ.Even} ↦
      x.val (eGal σ)) heq
    simp only [galCharOfRealChar_eval, MulEquiv.symm_apply_apply] at h
    exact h
  · intro χ
    let ψ := χ.val.toUnitHom.comp (eGal).toMonoidHom
    have hker : H ≤ ψ.ker := Subgroup.zpowers_le.mpr (by
      rw [MonoidHom.mem_ker, show ψ σc = χ.val.toUnitHom (eGal σc) from rfl,
        MulEquiv.apply_symm_apply]
      exact χ.property.toUnitHom_eval_neg_one)
    let θ := IsGalois.normalAutEquivQuotient H
    let φ := (QuotientGroup.lift H ψ hker).comp θ.symm.toMonoidHom
    refine ⟨φ, Subtype.ext ?_⟩
    apply MulChar.equivToUnitHom.injective
    ext u
    rw [MulChar.coe_equivToUnitHom, MulChar.coe_equivToUnitHom, galCharOfRealChar_eval]
    change (φ ((AlgEquiv.restrictNormalHom F) ((eGal).symm u)) : ℂ) = χ.val u
    rw [← IsGalois.normalAutEquivQuotient_apply H]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, θ,
      MulEquiv.symm_apply_apply, QuotientGroup.lift_mk, ψ, MulEquiv.apply_symm_apply,
      MulChar.coe_toUnitHom]

private theorem fixedField_dedekindLocalFactor_eq_prod_even
    (q : Nat.Primes) (hne : (q : ℕ) ≠ p) (s : ℂ) :
    dedekindLocalFactor F q s =
      ∏ᶠ χ : {χ : DirichletCharacter ℂ p // χ.Even},
        (1 - χ.val (q : ℕ) * (q : ℂ) ^ (-s))⁻¹ := by
  have : IsAbelianGalois ℚ F := IsAbelianGalois.tower_bot ℚ F K
  have : Normal ℚ F := (IsGalois.of_fixedField_normal_subgroup H).to_normal
  let qv : ℕ := q
  let : Fact qv.Prime := ⟨q.property⟩
  have hndvd : ¬ qv ∣ p := by
    intro h
    exact hne (((Nat.dvd_prime hp.out).mp h).resolve_left q.property.ne_one)
  let hcop : qv.Coprime p := q.property.coprime_iff_not_dvd.mpr hndvd
  let u := ZMod.unitOfCoprime qv hcop
  have hu : (u : ZMod p) = (qv : ZMod p) := ZMod.coe_unitOfCoprime qv hcop
  let σ := (eGal).symm u
  obtain ⟨Q⟩ := (inferInstance : Nonempty ((rationalPrimeIdeal q).primesOver (𝓞 K)))
  have : Q.1.LiesOver (Ideal.span {(qv : ℤ)}) := by
    change Q.1.LiesOver (rationalPrimeIdeal q)
    infer_instance
  let P := Q.1.under (𝓞 F)
  have : P.IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (rationalPrimeIdeal q) := ⟨by
    rw [show P.under ℤ = Q.1.under ℤ from Ideal.under_under Q.1]
    exact Q.1.over_def _⟩
  have hQ : Q.1.ramificationIdx ℤ = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd qv K Q.1 hndvd
  have hP : P.ramificationIdx ℤ = 1 :=
    Nat.dvd_one.mp (hQ ▸ Ideal.ramificationIdx_below_dvd (R := ℤ) P Q.1)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rationalPrimeIdeal_ne_bot q) P
  have : Finite ((𝓞 ℚ) ⧸ P.under (𝓞 ℚ)) :=
    Ring.HasFiniteQuotients.finiteQuotient (Ideal.under_ne_bot (𝓞 ℚ) hPne)
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) P := Ideal.ramificationIdx_eq_one_iff.mp (by
    rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int, hP])
  have hσ : IsArithFrobAt ℤ σ Q.1 :=
    (TauCeti.NumberField.isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime hcop Q.1 σ).mpr
      (MulEquiv.apply_symm_apply _ _)
  have hσRat := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff σ Q.1).mpr hσ
  have hσP : IsArithFrobAt ℤ (σ.restrictNormal F) P :=
    (Ideal.isArithFrobAt_ringOfIntegers_rat_iff (σ.restrictNormal F) P).mp
      (IsArithFrobAt.restrictNormal (K := ℚ) (L := K) (M := F) hσRat)
  have he : (rationalPrimeIdeal q).ramificationIdxIn (𝓞 F) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal q) P Gal(F/ℚ), hP]
  have hf : (rationalPrimeIdeal q).inertiaDegIn (𝓞 F) = orderOf (σ.restrictNormal F) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal q) P Gal(F/ℚ),
      Ideal.inertiaDeg_eq_orderOf P hσP]
  have hcard := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (rationalPrimeIdeal q) (𝓞 F) Gal(F/ℚ)
  rw [he, hf, one_mul] at hcard
  have hcard' : ((rationalPrimeIdeal q).primesOver (𝓞 F)).ncard =
      Nat.card Gal(F/ℚ) / orderOf (σ.restrictNormal F) := by
    rw [← hcard, Nat.mul_div_cancel _ (orderOf_pos _)]
  rw [dedekindLocalFactor_eq_of_isGalois, hf, hcard', ← prod_characters_localEulerFactor,
    ← finprod_comp_equiv (evenCharacterEquiv K)]
  congr 1
  funext χ
  change (1 - (χ (σ.restrictNormal F) : ℂ) * (q : ℂ) ^ (-s))⁻¹ =
    (1 - galCharOfRealChar K χ (qv : ZMod p) * (q : ℂ) ^ (-s))⁻¹
  rw [← hu, galCharOfRealChar_eval]

private theorem fixedField_dedekindLocalFactor_conductor (s : ℂ) :
    dedekindLocalFactor F ⟨p, hp.out⟩ s = dedekindLocalFactor K ⟨p, hp.out⟩ s := by
  let q : Nat.Primes := ⟨p, hp.out⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty ((rationalPrimeIdeal q).primesOver (𝓞 F)))
  have hKcard : ((rationalPrimeIdeal q).primesOver (𝓞 K)).ncard = 1 :=
    IsCyclotomicExtension.Rat.ncard_primesOver_of_prime p K
  have hKf : (rationalPrimeIdeal q).inertiaDegIn (𝓞 K) = 1 :=
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime p K
  have hFcard := Ideal.ncard_primesOver_mul_ncard_primesOver
    (p := rationalPrimeIdeal q) P.1 Gal(F/ℚ) (𝓞 K) Gal(K/ℚ)
  rw [hKcard] at hFcard
  have hFcard' := Nat.eq_one_of_mul_eq_one_right hFcard
  have hFf := Ideal.inertiaDegIn_mul_inertiaDegIn (rationalPrimeIdeal q) P.1 Gal(F/ℚ)
    (𝓞 K) Gal(K/ℚ) Gal(K/F)
  rw [hKf] at hFf
  have hFf' := Nat.eq_one_of_mul_eq_one_right hFf
  change dedekindLocalFactor F q s = dedekindLocalFactor K q s
  rw [dedekindLocalFactor_eq_of_isGalois, dedekindLocalFactor_eq_of_isGalois, hKcard, hKf,
    hFcard', hFf']

omit [IsAbelianGalois ℚ K] in
/-- Away from the conductor, the Euler factor of the maximal real subfield is the
product over the even Dirichlet characters. -/
theorem cyclotomic_real_dedekindLocalFactor_eq_prod_even
    (q : Nat.Primes) (hne : (q : ℕ) ≠ p) (s : ℂ) :
    dedekindLocalFactor (maximalRealSubfield K) q s =
      ∏ᶠ χ : {χ : DirichletCharacter ℂ p // χ.Even},
        (1 - χ.val (q : ℕ) * (q : ℂ) ^ (-s))⁻¹ := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {p} ℚ K
  rw [← toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one p K]
  exact fixedField_dedekindLocalFactor_eq_prod_even K q hne s

omit [IsAbelianGalois ℚ K] in
/-- The cyclotomic field and its maximal real subfield have the same Euler factor
at the conductor. -/
theorem cyclotomic_real_dedekindLocalFactor_conductor (s : ℂ) :
    dedekindLocalFactor (maximalRealSubfield K) ⟨p, hp.out⟩ s =
      dedekindLocalFactor K ⟨p, hp.out⟩ s := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {p} ℚ K
  rw [← toSubfield_fixedField_zpowers_galEquivZMod_symm_neg_one p K]
  exact fixedField_dedekindLocalFactor_conductor K s

end TinyTauDemo
