/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import TauCeti.NumberTheory.NumberField.Global.Places.PowerClasses

/-!
# The local index of the auxiliary Kummer idele subgroup

The group of R-ideles maps onto the local power classes at a subset S of R and at
the infinite places. Its kernel consists of local powers at those places and has
arbitrary components at the other places of R. This is the local index in
Milne, Class Field Theory, VII, Lemma 6.6.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `4b1f3f0413961ce8beedec28624e3b30bc10505f`.
-/

public section

open IsDedekindDomain NumberField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped BigOperators NumberField

namespace TinyTauDemo

variable {K : Type*} [Field K] [NumberField K]
  (S R : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)

private abbrev auxiliaryLocalPowerClasses :=
  ((v : S) → (v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range) ×
    ((w : InfinitePlace K) → w.Completionˣ ⧸ (powMonoidHom n).range)

private noncomputable def auxiliaryLocalPowerClassMap :
    kummerIdeleSubgroup R 1 →* auxiliaryLocalPowerClasses S n where
  toFun x := (fun v ↦ QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
    fun w ↦ QuotientGroup.mk (w.ideleInfiniteCoord x.1))
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [QuotientGroup.mk_mul]

private theorem auxiliaryLocalPowerClassMap_surjective (hSR : S ⊆ R) :
    Function.Surjective (auxiliaryLocalPowerClassMap S R n) := by
  classical
  rintro ⟨xf, xi⟩
  choose z hz using fun v : S ↦ QuotientGroup.mk_surjective (xf v)
  choose zi hzi using fun w : InfinitePlace K ↦ QuotientGroup.mk_surjective (xi w)
  let zf (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
    if hv : v ∈ S then z ⟨v, hv⟩ else 1
  have hzfu : ∀ᶠ v in Filter.cofinite, zf v ∈ (v.adicCompletionIntegers K).units :=
    S.eventually_cofinite_notMem.mono fun v hv ↦ by simp [zf, hv]
  let x := ideleOfUnits zi zf hzfu
  have hx : x ∈ kummerIdeleSubgroup R 1 := by
    rw [mem_kummerIdeleSubgroup_one_iff]
    intro v hv
    have hvS : v ∉ S := fun hs ↦ hv (hSR hs)
    simp [x, zf, hvS]
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Prod.ext
  · funext v
    simpa [auxiliaryLocalPowerClassMap, x, zf, v.2] using hz v
  · funext w
    simpa [auxiliaryLocalPowerClassMap, x] using hzi w

/-- The R-ideles that are local n-th powers at S and the infinite places. -/
noncomputable def auxiliaryKummerIdeleSubgroup : Subgroup (IdeleGroup (𝓞 K) K) :=
  (auxiliaryLocalPowerClassMap S R n).ker.map (kummerIdeleSubgroup R 1).subtype

/-- Membership in the auxiliary Kummer subgroup in terms of its finite and infinite
local components. -/
theorem mem_auxiliaryKummerIdeleSubgroup_iff (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S R n ↔
      (∀ v ∈ S, v.ideleFiniteCoord x ∈ (powMonoidHom n).range) ∧
      (∀ w : InfinitePlace K, w.ideleInfiniteCoord x ∈ (powMonoidHom n).range) ∧
      (∀ v ∉ R, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1) := by
  have hker (y : kummerIdeleSubgroup R 1) :
      y ∈ (auxiliaryLocalPowerClassMap S R n).ker ↔
        (∀ v ∈ S, v.ideleFiniteCoord y.val ∈ (powMonoidHom n).range) ∧
        (∀ w : InfinitePlace K, w.ideleInfiniteCoord y.val ∈ (powMonoidHom n).range) := by
    rw [MonoidHom.mem_ker]
    change (fun v : S ↦ QuotientGroup.mk (v.1.ideleFiniteCoord y.val),
      fun w : InfinitePlace K ↦ QuotientGroup.mk (w.ideleInfiniteCoord y.val)) = 1 ↔ _
    simp only [Prod.ext_iff, funext_iff, Prod.fst_one, Prod.snd_one, Pi.one_apply,
      QuotientGroup.eq_one_iff, Subtype.forall]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(hker y).mp hy |>.1, (hker y).mp hy |>.2,
      (mem_kummerIdeleSubgroup_one_iff R _).mp y.property⟩
  · rintro ⟨hf, hi, hR⟩
    let y : kummerIdeleSubgroup R 1 := ⟨x, (mem_kummerIdeleSubgroup_one_iff R _).mpr hR⟩
    exact ⟨y, (hker y).mpr ⟨hf, hi⟩, rfl⟩

/-- The index between the R-ideles and the auxiliary Kummer subgroup counts the power
classes only at the prescribed places S and the infinite places. -/
theorem relIndex_auxiliaryKummerIdeleSubgroup (hSR : S ⊆ R) :
    (auxiliaryKummerIdeleSubgroup S R n).relIndex (kummerIdeleSubgroup R 1) =
      (∏ v : S, Nat.card ((v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  rw [Subgroup.relIndex, auxiliaryKummerIdeleSubgroup, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
  calc
    _ = Nat.card (auxiliaryLocalPowerClasses S n) := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (auxiliaryLocalPowerClassMap S R n)
        (auxiliaryLocalPowerClassMap_surjective S R n hSR)).toEquiv
    _ = _ := by simp only [Nat.card_prod, Nat.card_pi, auxiliaryLocalPowerClasses]

/-- The auxiliary Kummer local index is the expected power of n, including when R
contains extra places where no power condition is imposed. -/
theorem relIndex_auxiliaryKummerIdeleSubgroup_eq_pow [NeZero n] [HasEnoughRootsOfUnity K n]
    (hSR : S ⊆ R)
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (auxiliaryKummerIdeleSubgroup S R n).relIndex (kummerIdeleSubgroup R 1) =
      n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  rw [relIndex_auxiliaryKummerIdeleSubgroup S R n hSR]
  rw [Finset.prod_coe_sort S (fun v ↦
    Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n).range))]
  exact prod_card_powerClasses n S hnS

end TinyTauDemo
