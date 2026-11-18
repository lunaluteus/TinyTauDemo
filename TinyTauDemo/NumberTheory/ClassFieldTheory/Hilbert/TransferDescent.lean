/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import TauCeti.GroupTheory.Transfer.Basic

/-!
# Transfer descent for prime-degree class fields

An invariant prime-order character on the fixing subgroup of a coprime-degree
Galois extension extends by transfer. Its fixed field has the desired prime
degree, and its compositum with the original field is the relative fixed field.
The extension is unramified if the relative character kills relative inertia.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `e74e1464a9abce7e83e565c5ccdf1957b5935bc6`.
-/

public section

open NumberField IsDedekindDomain IntermediateField
open scoped NumberField

namespace TinyTauDemo

section FieldRange

variable {K E M : Type*} [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]

local notation "E₀" => AlgHom.fieldRange (IsScalarTower.toAlgHom K E M)

/-- The Galois group of a tower over its middle field identifies with the
fixing subgroup of the image of that field in the top field. -/
private def scalarTowerFixingSubgroupEquiv : (M ≃ₐ[E] M) ≃* (E₀).fixingSubgroup where
  toFun σ := ⟨σ.restrictScalars K, by
    rintro ⟨x, a, rfl⟩
    exact σ.commutes a⟩
  invFun σ :=
    { σ.1 with commutes' := fun a ↦ σ.2 ⟨algebraMap E M a, ⟨a, rfl⟩⟩ }
  left_inv σ := AlgEquiv.ext fun _ ↦ rfl
  right_inv σ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)
  map_mul' σ τ := Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)

end FieldRange

section Character

variable {G A : Type*} [Group G] [Finite G] [CommGroup A] {H : Subgroup G} [H.Normal]

/-- Transfer on a conjugation-invariant character restricts to the power
of the original character by the index of the normal subgroup. -/
private theorem transfer_apply_of_conjugation_invariant (χ : H →* A)
    (hχ : ∀ (g : G) (x : H),
      χ ⟨g * (x : G) * g⁻¹, ‹H.Normal›.conj_mem _ x.2 g⟩ = χ x) (x : H) :
    MonoidHom.transfer χ (x : G) = χ x ^ H.index := by
  classical
  let : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  rw [MonoidHom.transfer_eq_prod_mul_out]
  calc
    _ = ∏ _ : G ⧸ H, χ x := by
      apply Finset.prod_congr rfl
      intro q _
      have hx : ((x : G) : G ⧸ H) = 1 := (QuotientGroup.eq_one_iff _).mpr x.2
      simpa only [hx, mul_one] using hχ q.out x
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.index]

/-- A conjugation-invariant character extends across a normal subgroup of
index coprime to the order of its target. -/
private theorem exists_surjective_monoidHom_extend_of_conjugation_invariant (χ : H →* A)
    (hχ : Function.Surjective χ) (hcop : (Nat.card A).Coprime H.index)
    (hconj : ∀ (g : G) (x : H),
      χ ⟨g * (x : G) * g⁻¹, ‹H.Normal›.conj_mem _ x.2 g⟩ = χ x) :
    ∃ ψ : G →* A, Function.Surjective ψ ∧ ψ.comp H.subtype = χ := by
  let e : A ≃* A :=
    MulEquiv.ofBijective (powMonoidHom H.index) (powCoprime hcop).bijective
  let ψ := e.symm.toMonoidHom.comp (MonoidHom.transfer χ)
  have hs (x : H) : ψ (x : G) = χ x := by
    change e.symm (MonoidHom.transfer χ (x : G)) = χ x
    rw [transfer_apply_of_conjugation_invariant χ hconj x, e.symm_apply_eq]
    rfl
  refine ⟨ψ, fun t ↦ ?_, MonoidHom.ext hs⟩
  obtain ⟨x, hx⟩ := hχ t
  exact ⟨(x : G), (hs x).trans hx⟩

end Character

section Field

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  (E : IntermediateField K M) [IsGalois K E]

/-- A conjugation-invariant relative character gives a Galois subfield of the
ground field with the same degree as the target of the character. The compositum
with the original intermediate field is the fixed field of the relative kernel. -/
private theorem exists_fixedField_of_invariant_relative_character {A : Type*} [CommGroup A]
    (χ : E.fixingSubgroup →* A) (hχ : Function.Surjective χ)
    (hcop : (Nat.card A).Coprime (Module.finrank K E))
    (hconj : ∀ (g : M ≃ₐ[K] M) (x : E.fixingSubgroup),
      χ ⟨g * (x : M ≃ₐ[K] M) * g⁻¹,
        (inferInstance : E.fixingSubgroup.Normal).conj_mem _ x.2 g⟩ = χ x) :
    ∃ ψ : (M ≃ₐ[K] M) →* A, Function.Surjective ψ ∧
      ψ.comp E.fixingSubgroup.subtype = χ ∧
      Module.finrank K (fixedField ψ.ker) = Nat.card A ∧
      E ⊔ fixedField ψ.ker = fixedField (χ.ker.map E.fixingSubgroup.subtype) := by
  obtain ⟨ψ, hψ, heq⟩ := exists_surjective_monoidHom_extend_of_conjugation_invariant χ hχ
    ((IntermediateField.finrank_eq_fixingSubgroup_index M E) ▸ hcop) hconj
  refine ⟨ψ, hψ, heq, ?_, ?_⟩
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField, Subgroup.index_ker,
      ψ.range_eq_top_of_surjective hψ, Subgroup.card_top]
  · have hk : χ.ker.map E.fixingSubgroup.subtype = E.fixingSubgroup ⊓ ψ.ker := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (DFunLike.congr_fun heq x).trans hx⟩
      · rintro ⟨hg, hψg⟩
        change ψ g = 1 at hψg
        refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
        exact (DFunLike.congr_fun heq ⟨g, hg⟩).symm.trans hψg
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    change (E ⊔ fixedField ψ.ker).fixingSubgroup = (fixedField _).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_fixedField, hk]

end Field

section Inertia

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (E : IntermediateField K M) [IsGalois K E]

/-- A conjugation-invariant relative character of prime order and coprime base
degree descends to an everywhere-unramified extension if the character kills
the intersection of every finite-place inertia group with the fixing subgroup. -/
private theorem exists_unramified_fixedField_of_invariant_character {p : ℕ} (hp : p.Prime)
    (χ : E.fixingSubgroup →* Multiplicative (ZMod p)) (hχ : Function.Surjective χ)
    (hcop : p.Coprime (Module.finrank K E))
    (hconj : ∀ (g : M ≃ₐ[K] M) (x : E.fixingSubgroup),
      χ ⟨g * (x : M ≃ₐ[K] M) * g⁻¹,
        (inferInstance : E.fixingSubgroup.Normal).conj_mem _ x.2 g⟩ = χ x)
    (hunr : ∀ (w : HeightOneSpectrum (𝓞 M)) (x : E.fixingSubgroup),
      (x : M ≃ₐ[K] M) ∈ w.asIdeal.inertia (M ≃ₐ[K] M) → χ x = 1) :
    ∃ L : IntermediateField K M, IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧
      Module.finrank K L = p ∧
      (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) ∧
      E ⊔ L = fixedField (χ.ker.map E.fixingSubgroup.subtype) := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
  have hcop' : (Nat.card (Multiplicative (ZMod p))).Coprime (Module.finrank K E) := by
    rwa [hc]
  obtain ⟨ψ, _, heq, hdeg, hsup⟩ :=
    exists_fixedField_of_invariant_relative_character E χ hχ hcop' hconj
  let L := fixedField ψ.ker
  have hL : Module.finrank K L = p := hdeg.trans hc
  have hGal : IsGalois K L := inferInstance
  have hCyc : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K L).trans hL)
  refine ⟨L, hGal, hCyc, hL, ?_, hsup⟩
  intro w
  let v := w.asIdeal.under (𝓞 K)
  have hv0 : v ≠ ⊥ := Ideal.under_ne_bot _ w.ne_bot
  have hv : Algebra.IsUnramifiedIn (𝓞 L) v := by
    rw [Ideal.isUnramifiedIn_iff_forall_inertia_le v L]
    intro Q hQ
    let w' : HeightOneSpectrum (𝓞 M) :=
      ⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hv0 hQ⟩
    change Q.inertia (M ≃ₐ[K] M) ≤ (fixedField ψ.ker).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_fixedField]
    intro g hg
    let x : E.fixingSubgroup := ⟨g ^ E.fixingSubgroup.index, E.fixingSubgroup.pow_index_mem g⟩
    have hx : (x : M ≃ₐ[K] M) ∈ Q.inertia (M ≃ₐ[K] M) :=
      (Q.inertia (M ≃ₐ[K] M)).pow_mem hg _
    have hpow : ψ g ^ E.fixingSubgroup.index = 1 := by
      rw [← map_pow]
      exact (DFunLike.congr_fun heq x).trans (hunr w' x hx)
    have hidx : (Nat.card (Multiplicative (ZMod p))).Coprime E.fixingSubgroup.index := by
      rw [← IntermediateField.finrank_eq_fixingSubgroup_index M E]
      exact hcop'
    change ψ g = 1
    apply (powCoprime hidx).injective
    simpa only [powCoprime_apply, one_pow] using hpow
  exact hv w.asIdeal w.isPrime (by infer_instance)

end Inertia

section Relative

variable {K E M : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  [Field M] [NumberField M] [Algebra K E] [Algebra E M] [Algebra K M]
  [IsScalarTower K E M] [IsGalois K E] [IsGalois K M] [IsGalois E M]

/-- A prime-degree cyclic extension cut out by a conjugation-invariant relative
character descends through a coprime-degree Galois extension. It remains
unramified at finite places if the relative fixed field is unramified. -/
theorem exists_unramified_cyclic_descent_of_relative_character {p : ℕ} (hp : p.Prime)
    (χ : (M ≃ₐ[E] M) →* Multiplicative (ZMod p)) (hχ : Function.Surjective χ)
    (hcop : p.Coprime (Module.finrank K E))
    (hconj : ∀ (g : M ≃ₐ[K] M) (σ τ : M ≃ₐ[E] M),
      τ.restrictScalars K = g * σ.restrictScalars K * g⁻¹ → χ τ = χ σ)
    (hunr : ∀ w : HeightOneSpectrum (𝓞 (fixedField χ.ker)),
      Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal) :
    ∃ L : IntermediateField K M, IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧
      Module.finrank K L = p ∧
      (∀ w : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) ∧
      (IsScalarTower.toAlgHom K E M).fieldRange ⊔ L = (fixedField χ.ker).restrictScalars K := by
  let E₀ := (IsScalarTower.toAlgHom K E M).fieldRange
  have : IsGalois K E₀ := IsGalois.of_algEquiv (IsScalarTower.toAlgHom K E M).equivFieldRange
  let e : (M ≃ₐ[E] M) ≃* E₀.fixingSubgroup := scalarTowerFixingSubgroupEquiv
  let φ := χ.comp e.symm.toMonoidHom
  have hcop' : p.Coprime (Module.finrank K E₀) := by
    rw [← (IsScalarTower.toAlgHom K E M).equivFieldRange.toLinearEquiv.finrank_eq]
    exact hcop
  have hconj' (g : M ≃ₐ[K] M) (σ : E₀.fixingSubgroup) :
      φ ⟨g * (σ : M ≃ₐ[K] M) * g⁻¹,
        (inferInstance : E₀.fixingSubgroup.Normal).conj_mem _ σ.2 g⟩ = φ σ := by
    apply hconj g
    rfl
  have hI (w : HeightOneSpectrum (𝓞 M)) (σ : E₀.fixingSubgroup)
      (hσ : (σ : M ≃ₐ[K] M) ∈ w.asIdeal.inertia (M ≃ₐ[K] M)) : φ σ = 1 := by
    let v := w.under (𝓞 E)
    let F := fixedField χ.ker
    have hF : Algebra.IsUnramifiedIn (𝓞 F) v.asIdeal := by
      intro Q hQ hQV
      exact hunr ⟨Q, hQ, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hQ, hQV⟩⟩
    have hle := (Ideal.isUnramifiedIn_iff_forall_inertia_le v.asIdeal F).mp hF w.asIdeal
      ⟨w.isPrime, inferInstance⟩
    rw [IntermediateField.fixingSubgroup_fixedField] at hle
    apply hle
    rw [Ideal.mem_inertia] at hσ ⊢
    exact hσ
  obtain ⟨L, hL, hc, hd, hu, hs⟩ := exists_unramified_fixedField_of_invariant_character
    E₀ hp φ (hχ.comp e.symm.surjective) hcop' hconj' hI
  refine ⟨L, hL, hc, hd, hu, hs.trans ?_⟩
  ext x
  simp only [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff,
    Subgroup.mem_map, Subgroup.coe_subtype, MonoidHom.mem_ker]
  constructor
  · intro h σ hσ
    exact h (σ.restrictScalars K) ⟨e σ, by simpa [φ] using hσ, rfl⟩
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h (e.symm σ) hσ


end Relative

end TinyTauDemo
