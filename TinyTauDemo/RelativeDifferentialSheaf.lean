/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.DifferentialStalkMap
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Transitivity of relative differential sheaves

The cokernel of the pullback map on differential sheaves represents derivations
over the morphism. This gives the right-exact transitivity sequence.

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

end TinyTauDemo
