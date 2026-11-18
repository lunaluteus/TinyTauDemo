/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Hilbert.NormPullback
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import TauCeti.NumberTheory.NumberField.Kummer.Unramified
public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisAction

/-!
# Galois S-unit Kummer fields over the ground field

When the set of places is taken above a set of ground-field places, the
Galois action preserves the group of S-units and therefore the Kummer field.
Any finite set of places can be enlarged to one of this form.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `e74e1464a9abce7e83e565c5ccdf1957b5935bc6`.
-/

public section

open IntermediateField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  NumberField TauCeti TauCeti.GlobalNumberFields
open scoped AdeleGaloisAction NumberField

namespace TinyTauDemo

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]
  (E : IntermediateField K Ω) [Normal K E]

/-- The Kummer field of a Galois-stable group of radicands is normal over the
original base field. -/
private theorem normal_restrictScalars_kummerField_of_map_mem (n : ℕ) (Δ : Subgroup Eˣ)
    (hΔ : ∀ (σ : E ≃ₐ[K] E) (a : Eˣ), a ∈ Δ →
      Units.map (σ : E →* E) a ∈ Δ) :
    Normal K ((kummerField Ω n Δ).restrictScalars K) := by
  apply (normal_iff_forall_map_le' (K := (kummerField Ω n Δ).restrictScalars K)).2
  intro σ
  apply map_le_iff_le_comap.mpr
  conv_lhs => rw [kummerField_def, restrictScalars_adjoin]
  apply adjoin_le_iff.mpr
  rintro x (hx | ⟨a, ha, hax⟩)
  · change σ x ∈ (kummerField Ω n Δ).restrictScalars K
    have h := (normal_iff_forall_map_le' (K := E)).mp ‹Normal K E› σ
    have hx' : σ x ∈ E := h ⟨x, hx, rfl⟩
    exact (kummerField Ω n Δ).algebraMap_mem ⟨σ x, hx'⟩
  · change σ x ∈ kummerField Ω n Δ
    apply mem_kummerField_of_pow_eq (hΔ (σ.restrictNormal E) a ha)
    rw [← map_pow, hax]
    change σ (algebraMap E Ω (a : E)) = algebraMap E Ω (σ.restrictNormal E (a : E))
    exact (AlgEquiv.restrictNormal_commutes σ E (a : E)).symm

/-- Adjoining roots of the units outside the places lying above a set of
base-field places produces a normal extension of the base field. -/
private theorem normal_restrictScalars_kummerField_unit_primesAbove
    [NumberField K] [NumberField E] (n : ℕ)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    Normal K ((kummerField Ω n ((primesAbove (𝓞 K) (𝓞 E) S).unit E)).restrictScalars K) := by
  apply normal_restrictScalars_kummerField_of_map_mem
  intro σ a ha
  exact smul_mem_unit_primesAbove σ ha

/-- The S-unit Kummer field is Galois over the original base field when the
ambient extension is separable. -/
private theorem isGalois_kummerField_unit_primesAbove
    [NumberField K] [NumberField E] [Algebra.IsSeparable K Ω]
    (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsGalois K (kummerField Ω n ((primesAbove (𝓞 K) (𝓞 E) S).unit E)) := by
  let M := (kummerField Ω n ((primesAbove (𝓞 K) (𝓞 E) S).unit E)).restrictScalars K
  change IsGalois K M
  exact isGalois_iff.mpr
    ⟨inferInstance, normal_restrictScalars_kummerField_unit_primesAbove E n S⟩

/-- The same Galois property for a finite set presented as the places above
a set of base-field places. -/
theorem isGalois_kummerField_sUnits_of_coe_eq_primesAbove
    [NumberField K] [NumberField E] [Algebra.IsSeparable K Ω]
    (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : (T : Set _) = primesAbove (𝓞 K) (𝓞 E) S) :
    IsGalois K (kummerField Ω n ((T : Set (HeightOneSpectrum (𝓞 E))).unit E)) := by
  rw [hT]
  exact isGalois_kummerField_unit_primesAbove E n S

omit [Normal K Ω] [Normal K E] in
/-- A finite set of primes of an extension is contained in the primes above
a finite set of primes of its base. -/
theorem exists_finset_primesAbove_superset [NumberField K] [NumberField E]
    (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)),
      T ⊆ T' ∧ (T' : Set _) = primesAbove (𝓞 K) (𝓞 E) (S : Set _) := by
  classical
  let S := T.image (under (𝓞 K))
  let T' := (primesAbove_finite (𝓞 K) (𝓞 E) S.finite_toSet).toFinset
  refine ⟨S, T', ?_, Set.Finite.coe_toFinset _⟩
  intro w hw
  change w ∈ (primesAbove_finite (𝓞 K) (𝓞 E) S.finite_toSet).toFinset
  rw [← Finset.mem_coe, Set.Finite.coe_toFinset, mem_primesAbove_iff]
  exact Finset.mem_image_of_mem _ hw

/-- A number field has a cyclotomic intermediate field of degree prime to p
in its separable closure. -/
theorem exists_cyclotomic_intermediateField_of_prime (K : Type*) [Field K] [NumberField K]
    {p : ℕ} (hp : p.Prime) :
    ∃ E : IntermediateField K (SeparableClosure K), NumberField E ∧ IsGalois K E ∧
      Nonempty (HasEnoughRootsOfUnity E p) ∧ p.Coprime (Module.finrank K E) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) p
  let E := adjoin K ({ζ} : Set (SeparableClosure K))
  have : IsCyclotomicExtension {p} K E := hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : NumberField E := NumberField.of_module_finite K E
  refine ⟨E, inferInstance, IsCyclotomicExtension.isGalois {p} K E, ?_,
    (coprime_finrank_of_prime_cyclotomic (K := K) (E := E) hp).symm⟩
  exact ⟨⟨⟨IsCyclotomicExtension.zeta p K E, IsCyclotomicExtension.zeta_spec p K E⟩,
    inferInstance⟩⟩

end TinyTauDemo
