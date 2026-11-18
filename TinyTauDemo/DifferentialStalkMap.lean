/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.TameRamificationIndex
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Stalk
import TauCeti.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# The map of differential sheaves on germs

The pullback of differentials along a morphism over an affine base agrees
on germs with the Kähler differential map of the corresponding local rings.
See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `b73a2cb4cf6f8a5b848f4016cc46b4611bb200a2`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite KaehlerDifferential

namespace TinyTauDemo

universe u

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- Pullback of local functions induces the adjoint form of the map on differential sheaves. -/
noncomputable def pullbackRelativeDifferentialsHom :
    Y.relativeDifferentials R ⟶
      (Scheme.Modules.pushforward f).obj (X.relativeDifferentials R) :=
  (Y.relativeDifferentialsHomEquiv R _).symm
    (TauCeti.AlgebraicGeometry.pushforwardDerivation R f (X.universalDerivation R))

/-- The pullback of the differential of a section is the differential of its pullback. -/
theorem pullbackRelativeDifferentialsHom_app_d (U : Y.Opens) (a : Γ(Y, U)) :
    (pullbackRelativeDifferentialsHom R f).app U ((Y.universalDerivation R).d a) =
      (X.universalDerivation R).d (f.app U a) :=
  (congrArg (fun d ↦ d.d a) <| Y.relativeDifferentialsHomEquiv_symm_fac R
    (TauCeti.AlgebraicGeometry.pushforwardDerivation R f (X.universalDerivation R))).trans
      (TauCeti.AlgebraicGeometry.pushforwardDerivation_d R f (X.universalDerivation R) U a)

/-- The map on additive stalks induced by pullback of differentials. -/
noncomputable def pullbackRelativeDifferentialsStalk (x : X) :
    (Y.relativeDifferentials R).presheaf.stalk (f x) ⟶
      (X.relativeDifferentials R).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map
      ((PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        (pullbackRelativeDifferentialsHom R f).val) ≫
      (X.relativeDifferentials R).presheaf.stalkPushforward AddCommGrpCat f.base x

/-- The induced morphism on stalks is computed on a germ by pullback on the sections. -/
theorem pullbackRelativeDifferentialsStalk_germ (x : X) (U : Y.Opens) (hx : f x ∈ U)
    (a : Γ(Y.relativeDifferentials R, U)) :
    pullbackRelativeDifferentialsStalk R f x
        ((Y.relativeDifferentials R).presheaf.germ U (f x) hx a) =
      (X.relativeDifferentials R).presheaf.germ (f ⁻¹ᵁ U) x hx
        ((pullbackRelativeDifferentialsHom R f).app U a) := by
  let N := (X.relativeDifferentials R).presheaf
  let g : (Y.relativeDifferentials R).presheaf ⟶ f.base _* N :=
    (PresheafOfModules.toPresheaf (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
      (pullbackRelativeDifferentialsHom R f).val
  let c := N.stalkPushforward AddCommGrpCat f.base x
  change c ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map g
    ((Y.relativeDifferentials R).presheaf.germ U (f x) hx a)) = _
  exact (congrArg (fun m ↦ c m)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f x) hx g a)).trans
    (TopCat.Presheaf.stalkPushforward_germ_apply AddCommGrpCat f.base N U x hx
      (g.app (op U) a))

private theorem germ_baseRingToStructurePresheaf (W : Scheme.{u})
    [W.Over (Spec (.of R))] (U : W.Opens) (x : W) (hx : x ∈ U) (a : R) :
    W.presheaf.germ U x hx ((W.baseRingToStructurePresheaf R).app (op U) a) =
      algebraMap R (W.presheaf.stalk x) a := by
  rw [Scheme.algebraMap_stalk_eq_baseRingToStalk, Scheme.baseRingToStalk_apply,
    Scheme.baseRingToStructurePresheaf_app, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply, TopCat.Presheaf.germ_res_apply]

/-- The morphism of local rings at a point of a morphism over `Spec R` is an `R`-algebra map. -/
theorem stalkMap_algebraMap (x : X) (a : R) :
    f.stalkMap x (algebraMap R (Y.presheaf.stalk (f x)) a) =
      algebraMap R (X.presheaf.stalk x) a := by
  have htop : f x ∈ (⊤ : Y.Opens) := trivial
  rw [← germ_baseRingToStructurePresheaf R Y ⊤ (f x) htop a,
    f.germ_stalkMap_apply, Scheme.Modules.app_baseRingToStructurePresheaf]
  exact germ_baseRingToStructurePresheaf R X (f ⁻¹ᵁ ⊤) x htop a

/-- Pullback of a differential germ along the scheme morphism is the
Kähler differential map induced by its local ring homomorphism. -/
theorem pullbackRelativeDifferentialsHom_germ_d
    (x : X) (U : Y.Opens) (hx : f x ∈ U) (a : Γ(Y, U)) :
    let A := Y.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
    let _ : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap R f x c).symm
    X.relativeDifferentialsStalkEquiv R x
        (pullbackRelativeDifferentialsStalk R f x
          ((Y.relativeDifferentials R).presheaf.germ U (f x) hx
            ((Y.universalDerivation R).d a))) =
      KaehlerDifferential.map R R A B
        (Y.relativeDifferentialsStalkEquiv R (f x)
          ((Y.relativeDifferentials R).presheaf.germ U (f x) hx
            ((Y.universalDerivation R).d a))) := by
  dsimp only
  refine (congrArg (X.relativeDifferentialsStalkEquiv R x)
    (pullbackRelativeDifferentialsStalk_germ R f x U hx ((Y.universalDerivation R).d a))).trans ?_
  rw [pullbackRelativeDifferentialsHom_app_d,
    Scheme.relativeDifferentialsStalkEquiv_germ_d
    R X x (f ⁻¹ᵁ U) (show x ∈ f ⁻¹ᵁ U from hx),
    Scheme.relativeDifferentialsStalkEquiv_germ_d, KaehlerDifferential.map_D]
  congr 1
  exact (f.germ_stalkMap_apply U x hx a).symm

/-- The relative Kähler differentials of the actual map on curve stalks
have length equal to the ramification index minus one. -/
theorem length_relativeKaehlerDifferential_stalkMap (x : X)
    [IsDomain (Y.presheaf.stalk (f x))] [IsDomain (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [CharZero (IsLocalRing.ResidueField (X.presheaf.stalk x))]
    [Module.Finite (Y.presheaf.stalk (f x)) Ω[Y.presheaf.stalk (f x)⁄R]]
    [Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄R]]
    [Module.IsTorsionFree (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄R]]
    [Nontrivial Ω[X.presheaf.stalk x⁄R]]
    (hA : Subsingleton Ω[IsLocalRing.ResidueField (Y.presheaf.stalk (f x))⁄R])
    (hB : Subsingleton Ω[IsLocalRing.ResidueField (X.presheaf.stalk x)⁄R])
    {t : Y.presheaf.stalk (f x)} {v : X.presheaf.stalk x}
    (ht : Irreducible t) (hv : Irreducible v) (ht₀ : f.stalkMap x t ≠ 0) :
    let A := Y.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
    Module.length B Ω[B⁄A] = ↑((IsLocalRing.maximalIdeal B).ramificationIdx A - 1 : ℕ) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap R f x c).symm
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact length_relativeKaehlerDifferential_eq_ramificationIdx_sub_one hA hB ht hv ht₀

/-- The stalk map on differentials respects the scalar map on local rings. -/
theorem pullbackRelativeDifferentialsStalk_smul (x : X) (r : Y.presheaf.stalk (f x))
    (m : (Y.relativeDifferentials R).presheaf.stalk (f x)) :
    pullbackRelativeDifferentialsStalk R f x (r • m) =
      f.stalkMap x r • pullbackRelativeDifferentialsStalk R f x m := by
  obtain ⟨U, hU, r₀, rfl⟩ := Y.presheaf.exists_germ_eq r
  obtain ⟨V, hV, m₀, rfl⟩ := (Y.relativeDifferentials R).presheaf.exists_germ_eq m
  let W := U ⊓ V
  have hW : f x ∈ W := ⟨hU, hV⟩
  let iU : W ⟶ U := homOfLE inf_le_left
  let iV : W ⟶ V := homOfLE inf_le_right
  rw [← Y.presheaf.germ_res_apply iU (f x) hW r₀,
    ← (Y.relativeDifferentials R).presheaf.germ_res_apply iV (f x) hW m₀]
  let r₁ := Y.presheaf.map iU.op r₀
  let m₁ := (Y.relativeDifferentials R).presheaf.map iV.op m₀
  change pullbackRelativeDifferentialsStalk R f x
      (Y.presheaf.germ W (f x) hW r₁ • (Y.relativeDifferentials R).presheaf.germ W (f x) hW m₁) =
    f.stalkMap x (Y.presheaf.germ W (f x) hW r₁) •
      pullbackRelativeDifferentialsStalk R f x
        ((Y.relativeDifferentials R).presheaf.germ W (f x) hW m₁)
  have hs := Scheme.Modules.germ_smul (Y.relativeDifferentials R) (f x) W hW r₁ m₁
  have hm := pullbackRelativeDifferentialsStalk_germ R f x W hW m₁
  let z : Γ(X.relativeDifferentials R, f ⁻¹ᵁ W) :=
    (pullbackRelativeDifferentialsHom R f).app W m₁
  have hsmul : (pullbackRelativeDifferentialsHom R f).app W (r₁ • m₁) =
      f.app W r₁ • z :=
    ((pullbackRelativeDifferentialsHom R f).val.app (op W)).hom.map_smul r₁ m₁
  exact (congrArg (pullbackRelativeDifferentialsStalk R f x) hs.symm).trans <|
    (pullbackRelativeDifferentialsStalk_germ R f x W hW (r₁ • m₁)).trans <|
      (congrArg ((X.relativeDifferentials R).presheaf.germ (f ⁻¹ᵁ W) x hW) hsmul).trans <|
        (Scheme.Modules.germ_smul (X.relativeDifferentials R) x (f ⁻¹ᵁ W) hW
          (f.app W r₁) ((pullbackRelativeDifferentialsHom R f).app W m₁)).trans <|
          congrArg₂ (· • ·) (f.germ_stalkMap_apply W x hW r₁).symm hm.symm

/-- Under the canonical stalk identifications, the stalk map of the pullback
morphism is the Kähler differential map of the local ring homomorphism. -/
theorem pullbackRelativeDifferentialsStalk_eq_map (x : X)
    (m : (Y.relativeDifferentials R).presheaf.stalk (f x)) :
    let A := Y.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
    let _ : IsScalarTower R A B :=
      IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap R f x c).symm
    X.relativeDifferentialsStalkEquiv R x (pullbackRelativeDifferentialsStalk R f x m) =
      KaehlerDifferential.map R R A B (Y.relativeDifferentialsStalkEquiv R (f x) m) := by
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap R f x c).symm
  let E := Y.relativeDifferentialsStalkEquiv R (f x)
  let G := X.relativeDifferentialsStalkEquiv R x
  let g := pullbackRelativeDifferentialsStalk R f x
  let h := KaehlerDifferential.map R R A B
  change G (g m) = h (E m)
  suffices H : ∀ w : Ω[A⁄R], G (g (E.symm w)) = h w from by
    rw [← H (E m), E.symm_apply_apply]
  intro w
  have hw : w ∈ Submodule.span A (Set.range (D R A)) := by rw [span_range_derivation]; trivial
  refine Submodule.span_induction (p := fun w _ ↦ G (g (E.symm w)) = h w)
    ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨a, rfl⟩
    obtain ⟨U, hx, a₀, rfl⟩ := Y.presheaf.exists_germ_eq a
    have h₁ : E.symm (D R A (Y.presheaf.germ U (f x) hx a₀)) =
        (Y.relativeDifferentials R).presheaf.germ U (f x) hx
          ((Y.universalDerivation R).d a₀) :=
      Scheme.relativeDifferentialsStalkEquiv_symm_D_germ R Y (f x) U hx a₀
    have h₂ := pullbackRelativeDifferentialsHom_germ_d R f x U hx a₀
    have h₃ := Scheme.relativeDifferentialsStalkEquiv_germ_d R Y (f x) U hx a₀
    exact (congrArg (fun q ↦ G (g q)) h₁).trans (h₂.trans (congrArg h h₃))
  · simp only [map_zero]
  · intro a b _ _ ha hb
    rw [map_add, map_add, map_add, ha, hb, map_add]
  · intro r a _ ha
    rw [map_smul, pullbackRelativeDifferentialsStalk_smul R f, map_smul, ha, map_smul]
    rfl

end TinyTauDemo
