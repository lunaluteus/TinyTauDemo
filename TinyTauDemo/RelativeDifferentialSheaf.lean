/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.PullbackStalk
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Transitivity of relative differential sheaves

The cokernel of the pullback map on differential sheaves represents derivations
over the morphism. The stalk of this cokernel is the relative Kähler differential
module of the map on local rings.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `866d7919b0ef1ac3e973d5c6b7b8fc759727d68e`.
-/

public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace TinyTauDemo

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- A derivation relative to `f` is a derivation on `X` that annihilates functions
pulled back from every open of `Y`. -/
abbrev DerivationOverMorphism (M : X.Modules) :=
  {D : M.Derivation R // ∀ (U : Y.Opens) (a : Γ(Y, U)), D.d (f.app U a) = 0}

private theorem differentialPullback_comp_eq_zero_iff {M : X.Modules}
    (g : X.relativeDifferentials R ⟶ M) :
    differentialPullback R f ≫ g = 0 ↔
      ∀ (U : Y.Opens) (a : Γ(Y, U)), g.app (f ⁻¹ᵁ U)
        ((X.universalDerivation R).d (f.app U a)) = 0 := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let E := A.homEquiv (Y.relativeDifferentials R) M
  have h0 : E 0 = 0 := by
    dsimp only [E]
    rw [A.homEquiv_unit, Functor.map_zero, comp_zero]
  have heq : E (differentialPullback R f ≫ g) =
      pullbackRelativeDifferentialsHom R f ≫ (Scheme.Modules.pushforward f).map g := by
    dsimp only [E]
    rw [A.homEquiv_naturality_right]
    congr 1
    exact differentialPullback_homEquiv R f
  rw [← E.injective.eq_iff, h0, heq]
  constructor
  · intro h U a
    have h' := congrArg (fun h ↦ h.app U ((Y.universalDerivation R).d a)) h
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
      Scheme.Modules.Hom.zero_app] at h'
    -- The underlying group map applies the two section maps in succession.
    change g.app (f ⁻¹ᵁ U)
      ((pullbackRelativeDifferentialsHom R f).app U ((Y.universalDerivation R).d a)) = 0 at h'
    rwa [pullbackRelativeDifferentialsHom_app_d] at h'
  · intro h
    apply Y.relativeDifferentials_hom_ext R
    intro U a
    obtain ⟨V, rfl⟩ := Opposite.op_surjective U
    have hv := h V a
    rw [← pullbackRelativeDifferentialsHom_app_d R f V a] at hv
    exact hv

/-- The relative differential sheaf `Ω_{X/Y}` as the quotient of `Ω_{X/R}`
by the differentials of functions pulled back from `Y`. -/
noncomputable def morphismRelativeDifferentials : X.Modules :=
  cokernel (differentialPullback R f)

/-- The canonical map from the differentials over the base to `Ω_{X/Y}`. -/
noncomputable def morphismRelativeDifferentialsπ :
    X.relativeDifferentials R ⟶ morphismRelativeDifferentials R f :=
  cokernel.π (differentialPullback R f)

/-- Morphisms from `Ω_{X/Y}` correspond to derivations that kill the pulled-back
functions, by composing with the universal derivation. -/
noncomputable def morphismRelativeDifferentialsHomEquiv (M : X.Modules) :
    (morphismRelativeDifferentials R f ⟶ M) ≃ DerivationOverMorphism R f M where
  toFun g := by
    -- Use the cokernel presentation so that the projection identities apply.
    change cokernel (differentialPullback R f) ⟶ M at g
    let h := morphismRelativeDifferentialsπ R f ≫ g
    refine ⟨X.relativeDifferentialsHomEquiv R M h, fun U a ↦ ?_⟩
    have hz : differentialPullback R f ≫ h = 0 := by
      change differentialPullback R f ≫ cokernel.π (differentialPullback R f) ≫ g = 0
      rw [cokernel.condition_assoc, zero_comp]
    rw [Scheme.relativeDifferentialsHomEquiv_apply]
    exact (differentialPullback_comp_eq_zero_iff R f h).mp hz U a
  invFun d := by
    let g := (X.relativeDifferentialsHomEquiv R M).symm d.1
    refine cokernel.desc (differentialPullback R f) g ?_
    apply (differentialPullback_comp_eq_zero_iff R f g).mpr
    intro U a
    exact (congrArg (fun D ↦ D.d (f.app U a))
      (X.relativeDifferentialsHomEquiv_symm_fac R d.1)).trans (d.2 U a)
  left_inv g := by
    change cokernel (differentialPullback R f) ⟶ M at g
    apply (cancel_epi (cokernel.π (differentialPullback R f))).mp
    dsimp only [id]
    rw [cokernel.π_desc]
    exact (X.relativeDifferentialsHomEquiv R M).symm_apply_apply _
  right_inv d := by
    apply Subtype.ext
    change (X.relativeDifferentialsHomEquiv R M)
      (cokernel.π (differentialPullback R f) ≫ _) = d.1
    rw [cokernel.π_desc, Equiv.apply_symm_apply]

/-- The right-exact transitivity sequence of differential sheaves. -/
noncomputable def differentialTransitivity : ShortComplex X.Modules :=
  ShortComplex.mk (differentialPullback R f) (morphismRelativeDifferentialsπ R f)
    (cokernel.condition _)

/-- The transitivity sequence is exact at the middle sheaf. -/
theorem differentialTransitivity_exact : (differentialTransitivity R f).Exact :=
  ShortComplex.exact_cokernel (differentialPullback R f)

/-- The map onto `Ω_{X/Y}` is an epimorphism. -/
theorem differentialTransitivity_epi : Epi (differentialTransitivity R f).g := by
  change Epi (cokernel.π (differentialPullback R f))
  infer_instance

/-- An injective pullback gives the short exact transitivity sequence. -/
theorem differentialTransitivity_shortExact_of_mono [Mono (differentialPullback R f)] :
    (differentialTransitivity R f).ShortExact where
  exact := differentialTransitivity_exact R f
  mono_f := inferInstanceAs (Mono (differentialPullback R f))
  epi_g := differentialTransitivity_epi R f

section Stalk

open KaehlerDifferential

variable (x : X)

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x

attribute [local instance] algebraStalkMap

/-- The stalk of the sheaf of relative differentials is the module of Kähler
differentials of the induced homomorphism of local rings. -/
noncomputable def morphismRelativeDifferentialsStalkEquiv :
    (morphismRelativeDifferentials R f).presheaf.stalk x ≃ₗ[B] Ω[B⁄A] :=
  cokernelDifferentialPullbackStalkEquiv R f x

local instance relativeStalkScalarTower : IsScalarTower R A B :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap R f x c).symm

set_option backward.isDefEq.respectTransparency false in
/-- The projection of the differential sheaf sequence becomes the canonical
map from absolute to relative Kähler differentials at each stalk. -/
theorem morphismRelativeDifferentialsStalkEquiv_projection
    (m : (X.relativeDifferentials R).presheaf.stalk x) :
    morphismRelativeDifferentialsStalkEquiv R f x
        ((modulesStalkFunctor x).map (morphismRelativeDifferentialsπ R f) m) =
      KaehlerDifferential.map R A B B (X.relativeDifferentialsStalkEquiv R x m) :=
  cokernelDifferentialPullbackStalkEquiv_projection R f x m

/-- The length of the relative differential sheaf stalk of a tame curve map is
the ramification index of the map on local rings minus one. -/
theorem length_morphismRelativeDifferentials_stalk
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [CharZero (IsLocalRing.ResidueField B)]
    [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]]
    [Module.IsTorsionFree B Ω[B⁄R]] [Nontrivial Ω[B⁄R]]
    (hA : Subsingleton Ω[IsLocalRing.ResidueField A⁄R])
    (hB : Subsingleton Ω[IsLocalRing.ResidueField B⁄R])
    {t : A} {v : B} (ht : Irreducible t) (hv : Irreducible v) (ht₀ : f.stalkMap x t ≠ 0) :
    Module.length B ((morphismRelativeDifferentials R f).presheaf.stalk x) =
      ↑((IsLocalRing.maximalIdeal B).ramificationIdx A - 1 : ℕ) :=
  (morphismRelativeDifferentialsStalkEquiv R f x).length_eq.trans
    (length_relativeKaehlerDifferential_stalkMap R f x hA hB ht hv ht₀)

end Stalk

end TinyTauDemo
