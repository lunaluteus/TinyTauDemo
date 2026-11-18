/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.DifferentialStalkMap
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Stalks of the pullback of differential sheaves

At a point of a scheme, morphisms to a skyscraper sheaf of modules describe
linear maps from the stalk. This identifies the stalk of a pullback sheaf
with the scalar extension of the original stalk. The induced pullback of
differentials becomes the first map of Kähler transitivity. Taking stalks
preserves the cokernel and identifies it with relative Kähler differentials.

See `/roadmap/index.qmd#thm-riemann-hurwitz-recall` @ `6a5e0c4054932c37eb1c977c31a738196704b232`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace TinyTauDemo

universe u

noncomputable section

private def skyscraperObj {X : Scheme.{u}} (x : X) (T : Type u) [AddCommGroup T]
    [Module (X.presheaf.stalk x) T] (U : X.Opens) :
    ModuleCat Γ(X, U) :=
  letI : ∀ _h : PLift (x ∈ U), Module Γ(X, U) T :=
    fun h ↦ Module.compHom T (X.presheaf.germ U x h.down).hom
  .of _ (PLift (x ∈ U) → T)

private theorem skyscraperObj_smul {X : Scheme.{u}} (x : X) (T : Type u) [AddCommGroup T]
    [Module (X.presheaf.stalk x) T] (U : X.Opens) (r : Γ(X, U))
    (m : skyscraperObj x T U) (h : x ∈ U) :
    (r • m) ⟨h⟩ = X.presheaf.germ U x h r • m ⟨h⟩ := rfl

private def skyscraperPresheaf {X : Scheme.{u}} (x : X) (T : Type u) [AddCommGroup T]
    [Module (X.presheaf.stalk x) T] :
    PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) where
  obj U := skyscraperObj x T U.unop
  map {U V} i := by
    refine ConcreteCategory.ofHom (C := ModuleCat Γ(X, U.unop)) ?_
    refine
      { toFun := fun m h ↦ m ⟨i.unop.le h.down⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := ?_ }
    intro r m
    funext h
    change (r • m) ⟨i.unop.le h.down⟩ = (X.presheaf.map i r •
      (show skyscraperObj x T V.unop from fun h' ↦ m ⟨i.unop.le h'.down⟩)) h
    rw [skyscraperObj_smul, skyscraperObj_smul]
    exact congrArg (fun z : X.presheaf.stalk x ↦ z • m ⟨i.unop.le h.down⟩)
      (X.presheaf.germ_res_apply i.unop x h.down r).symm
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def skyscraper {X : Scheme.{u}} (x : X) (T : Type u) [AddCommGroup T]
    [Module (X.presheaf.stalk x) T] : X.Modules where
  val := skyscraperPresheaf x T
  isSheaf := by
    classical
    apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
    intro ι U s hc
    have hindex (hx : x ∈ ⨆ i, U i) : ∃ i, x ∈ U i :=
      Opens.mem_iSup.mp hx
    let g : PLift (x ∈ ⨆ i, U i) → T :=
      fun hx ↦ s (hindex hx.down).choose ⟨(hindex hx.down).choose_spec⟩
    have compat (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j) :
        s i ⟨hi⟩ = s j ⟨hj⟩ := by
      exact congrFun (hc i j) ⟨⟨hi, hj⟩⟩
    refine ⟨g, ?_, ?_⟩
    · intro i
      funext hi
      let h : x ∈ ⨆ j, U j := Opens.mem_iSup.mpr ⟨i, hi.down⟩
      change g ⟨h⟩ = s i hi
      exact compat _ _ (hindex h).choose_spec hi.down
    · intro g' hg'
      funext h
      let i := (hindex h.down).choose
      exact congrFun (hg' i) ⟨(hindex h.down).choose_spec⟩

section pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : Y.Modules)
    (T : Type u) [AddCommGroup T] [Module (X.presheaf.stalk x) T]

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local instance stalkScalars : Module A T := Module.compHom T (f.stalkMap x).hom

set_option backward.isDefEq.respectTransparency false in
private def toPushforwardSkyscraper (L : M.presheaf.stalk (f x) →ₗ[A] T) :
    M ⟶ (Scheme.Modules.pushforward f).obj (skyscraper x T) := ⟨{
  app := fun U ↦ by
    letI : Module ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (M.val.obj U) :=
      (M.val.obj U).isModule
    refine ConcreteCategory.ofHom
      (C := ModuleCat ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)) ?_
    refine
      { toFun := fun m h ↦ L (M.presheaf.germ U.unop (f x) h.down m)
        map_add' := fun a b ↦ funext fun _ ↦ by simp only [map_add]; rfl
        map_smul' := ?_ }
    intro r m
    funext h
    have hx : f x ∈ U.unop := h.down
    let z : skyscraperObj x T (f ⁻¹ᵁ U.unop) :=
      fun h' ↦ L (M.presheaf.germ U.unop (f x) h'.down m)
    change L (M.presheaf.germ U.unop (f x) hx (r • m)) =
      (f.app U.unop r • z) ⟨hx⟩
    rw [Scheme.Modules.germ_smul, map_smul, skyscraperObj_smul]
    exact congrArg (fun c : B ↦ c • z ⟨hx⟩)
      (f.germ_stalkMap_apply U.unop x hx r)
  naturality := fun {U V} i ↦ by
    ext m
    funext h
    change L (M.presheaf.germ V.unop (f x) h.down (M.presheaf.map i m)) =
      L (M.presheaf.germ U.unop (f x) (i.unop.le h.down) m)
    exact congrArg L (M.presheaf.germ_res_apply i.unop (f x) h.down m) }⟩

set_option backward.isDefEq.respectTransparency false in
private def fromPushforwardSkyscraper
    (g : M ⟶ (Scheme.Modules.pushforward f).obj (skyscraper x T)) :
    M.presheaf.stalk (f x) →ₗ[A] T :=
  M.val.stalkLiftCommRing (S := Y.presheaf) (f x)
    (fun U hx ↦
      { toFun := fun m ↦ g.app U m ⟨hx⟩
        map_zero' := congrFun ((g.app U).hom.map_zero) ⟨hx⟩
        map_add' := fun a b ↦ congrFun ((g.app U).hom.map_add a b) ⟨hx⟩ })
    (fun i hx m ↦ by
      exact congrFun (PresheafOfModules.naturality_apply g.val i.op m) ⟨hx⟩)
    (fun U hx r m ↦ by
      have e := congrFun ((g.val.app (op U)).hom.map_smul r m) ⟨hx⟩
      change g.app U (r • m) ⟨hx⟩ =
        Y.presheaf.germ U (f x) hx r • g.app U m ⟨hx⟩
      refine e.trans ?_
      change (f.app U r • (show skyscraperObj x T (f ⁻¹ᵁ U) from g.app U m)) ⟨hx⟩ =
        f.stalkMap x (Y.presheaf.germ U (f x) hx r) • g.app U m ⟨hx⟩
      rw [skyscraperObj_smul, f.germ_stalkMap_apply])

set_option backward.isDefEq.respectTransparency false in
private theorem fromPushforwardSkyscraper_germ
    (g : M ⟶ (Scheme.Modules.pushforward f).obj (skyscraper x T))
    (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    fromPushforwardSkyscraper f x M T g (M.presheaf.germ U (f x) hx m) =
      g.app U m ⟨hx⟩ := by
  refine PresheafOfModules.stalkLiftCommRing_germ (f x) (S := Y.presheaf) M.val _ ?_ _ U hx m
  intro U V i hx m
  exact congrFun (PresheafOfModules.naturality_apply g.val i.op m) ⟨hx⟩

set_option backward.isDefEq.respectTransparency false in
private def pushforwardSkyscraperEquiv :
    (M ⟶ (Scheme.Modules.pushforward f).obj (skyscraper x T)) ≃
      (M.presheaf.stalk (f x) →ₗ[A] T) where
  toFun := fromPushforwardSkyscraper f x M T
  invFun := toPushforwardSkyscraper f x M T
  left_inv g := by
    ext U m
    funext h
    change fromPushforwardSkyscraper f x M T g
      (M.presheaf.germ U (f x) h.down m) = g.app U m h
    exact fromPushforwardSkyscraper_germ f x M T g U h.down m
  right_inv L := by
    ext m
    obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
    rw [fromPushforwardSkyscraper_germ]
    rfl

end pushforward

section stalk

variable {X : Scheme.{u}} (x : X) (M : X.Modules) (T : Type u)
    [AddCommGroup T] [Module (X.presheaf.stalk x) T]

local notation "B" => X.presheaf.stalk x

set_option backward.isDefEq.respectTransparency false in
private def toSkyscraper (L : M.presheaf.stalk x →ₗ[B] T) : M ⟶ skyscraper x T := ⟨{
  app := fun U ↦ by
    letI : Module ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (M.val.obj U) :=
      (M.val.obj U).isModule
    refine ConcreteCategory.ofHom
      (C := ModuleCat ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)) ?_
    refine
      { toFun := fun m h ↦ L (M.presheaf.germ U.unop x h.down m)
        map_add' := fun a b ↦ funext fun _ ↦ by simp only [map_add]; rfl
        map_smul' := ?_ }
    intro r m
    funext h
    let z : skyscraperObj x T U.unop := fun h' ↦ L (M.presheaf.germ U.unop x h'.down m)
    change L (M.presheaf.germ U.unop x h.down (r • m)) = (r • z) ⟨h.down⟩
    rw [Scheme.Modules.germ_smul, map_smul, skyscraperObj_smul]
  naturality := fun {U V} i ↦ by
    ext m
    funext h
    change L (M.presheaf.germ V.unop x h.down (M.presheaf.map i m)) =
      L (M.presheaf.germ U.unop x (i.unop.le h.down) m)
    exact congrArg L (M.presheaf.germ_res_apply i.unop x h.down m) }⟩

set_option backward.isDefEq.respectTransparency false in
private def fromSkyscraper (g : M ⟶ skyscraper x T) : M.presheaf.stalk x →ₗ[B] T :=
  M.val.stalkLiftCommRing (S := X.presheaf) x
    (fun U hx ↦
      { toFun := fun m ↦ g.app U m ⟨hx⟩
        map_zero' := congrFun ((g.app U).hom.map_zero) ⟨hx⟩
        map_add' := fun a b ↦ congrFun ((g.app U).hom.map_add a b) ⟨hx⟩ })
    (fun i hx m ↦ congrFun (PresheafOfModules.naturality_apply g.val i.op m) ⟨hx⟩)
    (fun U hx r m ↦ by
      have e := congrFun ((g.val.app (op U)).hom.map_smul r m) ⟨hx⟩
      exact e.trans (skyscraperObj_smul x T U r (g.app U m) hx))

set_option backward.isDefEq.respectTransparency false in
private theorem fromSkyscraper_germ (g : M ⟶ skyscraper x T)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    fromSkyscraper x M T g (M.presheaf.germ U x hx m) = g.app U m ⟨hx⟩ := by
  refine PresheafOfModules.stalkLiftCommRing_germ x (S := X.presheaf) M.val _ ?_ _ U hx m
  intro U V i hx m
  exact congrFun (PresheafOfModules.naturality_apply g.val i.op m) ⟨hx⟩

set_option backward.isDefEq.respectTransparency false in
private def stalkSkyscraperEquiv :
    (M ⟶ skyscraper x T) ≃ (M.presheaf.stalk x →ₗ[B] T) where
  toFun := fromSkyscraper x M T
  invFun := toSkyscraper x M T
  left_inv g := by
    ext U m
    funext h
    exact fromSkyscraper_germ x M T g U h.down m
  right_inv L := by
    ext m
    obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
    rw [fromSkyscraper_germ]
    rfl

private theorem stalkSkyscraperEquiv_symm_app
    (L : M.presheaf.stalk x →ₗ[B] T) (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    ((stalkSkyscraperEquiv x M T).symm L).app U m ⟨hx⟩ =
      L (M.presheaf.germ U x hx m) := rfl

end stalk

section ModuleStalkFunctor

variable {X : Scheme.{u}} (x : X)

local notation "B" => X.presheaf.stalk x

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a sheaf of modules, with its module structure over the local ring. -/
@[expose] def modulesStalkFunctor : X.Modules ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of _ (M.presheaf.stalk x)
  map φ := ModuleCat.ofHom (PresheafOfModules.stalkMapCommRing (S := X.presheaf) x φ.val)
  map_id M := by
    ext m
    obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
    exact PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x (𝟙 M.val) U hx m₀
  map_comp {M N P} φ ψ := by
    ext m
    obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
    change PresheafOfModules.stalkMapCommRing (S := X.presheaf) x (φ.val ≫ ψ.val)
        (M.presheaf.germ U x hx m₀) =
      PresheafOfModules.stalkMapCommRing (S := X.presheaf) x ψ.val
        (PresheafOfModules.stalkMapCommRing (S := X.presheaf) x φ.val
          (M.presheaf.germ U x hx m₀))
    have h := PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x (φ.val ≫ ψ.val)
      U hx m₀
    have hφ := PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x φ.val U hx m₀
    have hψ := PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x ψ.val U hx
      (φ.val.app (op U) m₀)
    exact h.trans ((congrArg (PresheafOfModules.stalkMapCommRing (S := X.presheaf) x ψ.val)
      hφ).trans hψ).symm

set_option backward.isDefEq.respectTransparency false in
/-- On germs the stalk functor applies the given morphism to the underlying section. -/
theorem modulesStalkFunctor_map_germ {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    (modulesStalkFunctor x).map φ (M.presheaf.germ U x hx m) =
      N.presheaf.germ U x hx (φ.app U m) :=
  PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x φ.val U hx m

set_option backward.isDefEq.respectTransparency false in
instance : (modulesStalkFunctor x).PreservesZeroMorphisms where
  map_zero M N := by
    ext m
    obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
    change (modulesStalkFunctor x).map (0 : M ⟶ N) (M.presheaf.germ U x hx m₀) = 0
    rw [modulesStalkFunctor_map_germ, Scheme.Modules.Hom.zero_app]
    change N.presheaf.germ U x hx (0 : Γ(N, U)) = 0
    exact (N.presheaf.germ U x hx).hom.map_zero

set_option backward.isDefEq.respectTransparency false in
private def modulesStalkRepresentable (T : ModuleCat.{u} B) :
    ((modulesStalkFunctor x).op ⋙ yoneda.obj T).RepresentableBy (skyscraper x T) where
  homEquiv {M} := (stalkSkyscraperEquiv x M T).trans
    { toFun := ModuleCat.ofHom
      invFun := ModuleCat.Hom.hom
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  homEquiv_comp {M N} φ ψ := by
    change (ModuleCat.ofHom _ : (modulesStalkFunctor x).obj M ⟶ T) =
      (modulesStalkFunctor x).map φ ≫ ModuleCat.ofHom _
    ext m
    obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
    change fromSkyscraper x M T (φ ≫ ψ) (M.presheaf.germ U x hx m₀) =
      fromSkyscraper x N T ψ ((modulesStalkFunctor x).map φ (M.presheaf.germ U x hx m₀))
    rw [modulesStalkFunctor_map_germ, fromSkyscraper_germ, fromSkyscraper_germ]
    rfl

/-- Taking the stalk of a sheaf of modules has a right adjoint, given by the
skyscraper sheaf at that point. -/
instance : (modulesStalkFunctor x).IsLeftAdjoint := by
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  ext T
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  exact (modulesStalkRepresentable x T).isRepresentable

end ModuleStalkFunctor

section PullbackStalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (M : Y.Modules)

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
set_option quotPrecheck false in
local notation "Mₓ" => ↑(M.presheaf.stalk (f x))
set_option quotPrecheck false in
local notation "P" => (Scheme.Modules.pullback f).obj M
set_option quotPrecheck false in
local notation "Pₓ" => ↑(((Scheme.Modules.pullback f).obj M).presheaf.stalk x)
set_option quotPrecheck false in
local notation "η" => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M

attribute [local instance] stalkScalars

set_option backward.isDefEq.respectTransparency false in
private def pullbackStalkHomEquiv (T : Type u) [AddCommGroup T] [Module B T] :
    (Pₓ →ₗ[B] T) ≃ (Mₓ →ₗ[A] T) :=
  (stalkSkyscraperEquiv x P T).symm.trans <|
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M (skyscraper x T)).trans <|
      pushforwardSkyscraperEquiv f x M T

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackStalkHomEquiv_germ (T : Type u) [AddCommGroup T] [Module B T]
    (L : Pₓ →ₗ[B] T) (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    pullbackStalkHomEquiv f x M T L (M.presheaf.germ U (f x) hx m) =
      L ((P).presheaf.germ (f ⁻¹ᵁ U) x hx ((η).app U m)) := by
  let g := (stalkSkyscraperEquiv x P T).symm L
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  change fromPushforwardSkyscraper f x M T (adj.homEquiv _ _ g)
    (M.presheaf.germ U (f x) hx m) = _
  rw [fromPushforwardSkyscraper_germ, adj.homEquiv_unit]
  change g.app (f ⁻¹ᵁ U) ((η).app U m) ⟨hx⟩ = _
  exact stalkSkyscraperEquiv_symm_app x P T L (f ⁻¹ᵁ U) hx ((η).app U m)

/-- The algebra on a target stalk induced by a morphism of schemes. -/
noncomputable abbrev algebraStalkMap : Algebra A B := (f.stalkMap x).hom.toAlgebra

attribute [local instance] algebraStalkMap

local instance stalkMapIsScalarTower (T : Type u) [AddCommGroup T] [Module B T] :
    IsScalarTower A B T :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

set_option backward.isDefEq.respectTransparency false in
private def unitTensor : Mₓ →ₗ[A] B ⊗[A] Mₓ where
  toFun m := 1 ⊗ₜ[A] m
  map_add' m n := TensorProduct.tmul_add 1 m n
  map_smul' a m := by
    change (1 : B) ⊗ₜ[A] (a • m) = algebraMap A B a • ((1 : B) ⊗ₜ[A] m)
    rw [TensorProduct.tmul_smul]
    exact (IsScalarTower.algebraMap_smul B a ((1 : B) ⊗ₜ[A] m)).symm

set_option backward.isDefEq.respectTransparency false in
private def tensorToPullbackStalk : B ⊗[A] Mₓ →ₗ[B] Pₓ :=
  (TensorProduct.isBaseChange A Mₓ B).lift (pullbackStalkHomEquiv f x M Pₓ LinearMap.id)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorToPullbackStalk_tmul (b : B) (m : Mₓ) :
    tensorToPullbackStalk f x M (b ⊗ₜ[A] m) =
      b • pullbackStalkHomEquiv f x M Pₓ LinearMap.id m := by
  have h : tensorToPullbackStalk f x M ((1 : B) ⊗ₜ[A] m) =
      pullbackStalkHomEquiv f x M Pₓ LinearMap.id m :=
    IsBaseChange.lift_eq (TensorProduct.isBaseChange A Mₓ B) _ _
  rw [← h, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
private def pullbackStalkToTensor : Pₓ →ₗ[B] B ⊗[A] Mₓ :=
  (pullbackStalkHomEquiv f x M (B ⊗[A] Mₓ)).symm (unitTensor f x M)

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackStalkToTensor_germ_unit (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    pullbackStalkToTensor f x M ((P).presheaf.germ (f ⁻¹ᵁ U) x hx ((η).app U m)) =
      (1 : B) ⊗ₜ[A] M.presheaf.germ U (f x) hx m := by
  rw [← pullbackStalkHomEquiv_germ, pullbackStalkToTensor, Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A pullback sheaf stalk is the scalar extension of the original stalk along the
map of local rings. -/
noncomputable def pullbackStalkEquiv : B ⊗[A] Mₓ ≃ₗ[B] Pₓ :=
  LinearEquiv.ofLinearMap (tensorToPullbackStalk f x M) (pullbackStalkToTensor f x M)
    (by
      apply (pullbackStalkHomEquiv f x M Pₓ).injective
      ext m
      obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
      simp only [pullbackStalkHomEquiv_germ, LinearMap.comp_apply, LinearMap.id_apply,
        pullbackStalkToTensor_germ_unit, tensorToPullbackStalk_tmul, one_smul])
    (by
      apply TensorProduct.AlgebraTensorModule.ext
      intro b m
      obtain ⟨U, hx, m₀, rfl⟩ := M.presheaf.exists_germ_eq m
      simp only [LinearMap.comp_apply, tensorToPullbackStalk_tmul, pullbackStalkHomEquiv_germ,
        LinearMap.id_apply, map_smul, pullbackStalkToTensor_germ_unit]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])

set_option backward.isDefEq.respectTransparency false in
/-- The comparison sends a pure tensor with a germ to the scalar multiple of the
pullback unit applied to that germ. -/
theorem pullbackStalkEquiv_tmul_germ (b : B) (U : Y.Opens) (hx : f x ∈ U) (m : Γ(M, U)) :
    pullbackStalkEquiv f x M (b ⊗ₜ[A] M.presheaf.germ U (f x) hx m) =
      b • (P).presheaf.germ (f ⁻¹ᵁ U) x hx ((η).app U m) := by
  change tensorToPullbackStalk f x M (b ⊗ₜ[A] M.presheaf.germ U (f x) hx m) = _
  rw [tensorToPullbackStalk_tmul, pullbackStalkHomEquiv_germ, LinearMap.id_apply]

end PullbackStalk

section DifferentialPullbackStalk

open KaehlerDifferential

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (x : X)

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
set_option quotPrecheck false in
local notation "M" => Y.relativeDifferentials R
set_option quotPrecheck false in
local notation "P" => (Scheme.Modules.pullback f).obj (Y.relativeDifferentials R)
set_option quotPrecheck false in
local notation "Mₓ" => ↑((Y.relativeDifferentials R).presheaf.stalk (f x))
set_option quotPrecheck false in
local notation "Pₓ" =>
  ↑(((Scheme.Modules.pullback f).obj (Y.relativeDifferentials R)).presheaf.stalk x)
set_option quotPrecheck false in
local notation "Nₓ" => ↑((X.relativeDifferentials R).presheaf.stalk x)

attribute [local instance] algebraStalkMap

local instance stalkMapAlgebraTower : IsScalarTower R A B :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (stalkMap_algebraMap R f x c).symm

set_option backward.isDefEq.respectTransparency false in
/-- The map on stalks of the adjoint pullback of differentials. -/
@[expose] noncomputable def differentialPullbackStalk : Pₓ →ₗ[B] Nₓ :=
  PresheafOfModules.stalkMapCommRing (S := X.presheaf) x (differentialPullback R f).val

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of differentials applied to a pure tensor is the scalar multiple
of the semilinear differential pullback on the original stalk. -/
theorem differentialPullbackStalk_tmul (b : B) (m : Mₓ) :
    differentialPullbackStalk R f x (pullbackStalkEquiv f x M (b ⊗ₜ[A] m)) =
      b • pullbackRelativeDifferentialsStalk R f x m := by
  obtain ⟨U, hx, m₀, rfl⟩ := (M).presheaf.exists_germ_eq m
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let h := differentialPullback R f
  have he : adj.unit.app M ≫ (Scheme.Modules.pushforward f).map h =
      pullbackRelativeDifferentialsHom R f :=
    (adj.homEquiv_unit _ _ h).symm.trans (differentialPullback_homEquiv R f)
  have hm := congrArg (fun g ↦ g.app U m₀) he
  change h.app (f ⁻¹ᵁ U) (adj.unit.app M |>.app U m₀) =
    (pullbackRelativeDifferentialsHom R f).app U m₀ at hm
  rw [pullbackStalkEquiv_tmul_germ, map_smul, pullbackRelativeDifferentialsStalk_germ]
  congr 1
  exact (PresheafOfModules.stalkMapCommRing_germ (S := X.presheaf) x h.val
    (f ⁻¹ᵁ U) hx (adj.unit.app M |>.app U m₀)).trans
    (congrArg ((X.relativeDifferentials R).presheaf.germ (f ⁻¹ᵁ U) x hx) hm)

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical comparisons for pullback and differential stalks, the
map on stalks of the differential pullback is the first map in Kähler transitivity. -/
theorem differentialPullbackStalk_eq_mapBaseChange :
    (X.relativeDifferentialsStalkEquiv R x).toLinearMap.comp
      ((differentialPullbackStalk R f x).comp (pullbackStalkEquiv f x M).toLinearMap) =
        (KaehlerDifferential.mapBaseChange R A B).comp
          ((Y.relativeDifferentialsStalkEquiv R (f x)).baseChange A B _ _).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul, differentialPullbackStalk_tmul, map_smul,
    pullbackRelativeDifferentialsStalk_eq_map R f x m]

end DifferentialPullbackStalk

section RelativeDifferentialStalk

open CategoryTheory.Limits KaehlerDifferential

variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of R))] (x : X)

local notation "A" => Y.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
set_option quotPrecheck false in
local notation "Nₓ" => ↑((X.relativeDifferentials R).presheaf.stalk x)

attribute [local instance] algebraStalkMap
attribute [local instance] stalkMapAlgebraTower

set_option backward.isDefEq.respectTransparency false in
private def quotientDifferentialStalkMap : Nₓ →ₗ[B] Ω[B⁄A] :=
  (KaehlerDifferential.map R A B B).comp (X.relativeDifferentialsStalkEquiv R x).toLinearMap

set_option backward.isDefEq.respectTransparency false in
private theorem quotientDifferentialStalkMap_exact :
    Function.Exact (differentialPullbackStalk R f x) (quotientDifferentialStalkMap R f x) := by
  let ea := (Y.relativeDifferentialsStalkEquiv R (f x)).baseChange A B _ _
  let eb := X.relativeDifferentialsStalkEquiv R x
  let ep := pullbackStalkEquiv f x (Y.relativeDifferentials R)
  let d := differentialPullbackStalk R f x
  let c := KaehlerDifferential.mapBaseChange R A B
  have hmap (m : B ⊗[A] ↑((Y.relativeDifferentials R).presheaf.stalk (f x))) :
      eb (d (ep m)) = c (ea m) :=
    congrArg (fun l ↦ l m) (differentialPullbackStalk_eq_mapBaseChange R f x)
  intro m
  change KaehlerDifferential.map R A B B (eb m) = 0 ↔ ∃ z, d z = m
  rw [KaehlerDifferential.exact_mapBaseChange_map R A B (eb m)]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨ep (ea.symm z), eb.injective ?_⟩
    change eb (d (ep (ea.symm z))) = eb m
    rw [hmap, ea.apply_symm_apply, hz]
  · rintro ⟨z, hz⟩
    refine ⟨ea (ep.symm z), ?_⟩
    rw [← hmap, ep.apply_symm_apply, hz]

set_option backward.isDefEq.respectTransparency false in
private def quotientDifferentialStalkIsCokernel :
    IsColimit (CokernelCofork.ofπ
      (f := (modulesStalkFunctor x).map (differentialPullback R f))
      (ModuleCat.ofHom (quotientDifferentialStalkMap R f x))
      (by ext; exact (quotientDifferentialStalkMap_exact R f x).apply_apply_eq_zero _)) :=
  ModuleCat.isColimitCokernelCofork _ _ (quotientDifferentialStalkMap_exact R f x)
    ((KaehlerDifferential.map_surjective R A B).comp
      (X.relativeDifferentialsStalkEquiv R x).surjective)

set_option backward.isDefEq.respectTransparency false in
/-- The stalk of the cokernel of the differential pullback is the relative
Kähler differential module of the map on local rings. -/
def cokernelDifferentialPullbackStalkEquiv :
    (cokernel (differentialPullback R f)).presheaf.stalk x ≃ₗ[B] Ω[B⁄A] :=
  (IsColimit.coconePointUniqueUpToIso
    (isColimitOfHasCokernelOfPreservesColimit (modulesStalkFunctor x) (differentialPullback R f))
    (quotientDifferentialStalkIsCokernel R f x)).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The stalk comparison identifies the cokernel projection with the canonical
map from the absolute to the relative Kähler differential module. -/
theorem cokernelDifferentialPullbackStalkEquiv_projection (m : Nₓ) :
    cokernelDifferentialPullbackStalkEquiv R f x
        ((modulesStalkFunctor x).map (cokernel.π (differentialPullback R f)) m) =
      KaehlerDifferential.map R A B B (X.relativeDifferentialsStalkEquiv R x m) := by
  let c := isColimitOfHasCokernelOfPreservesColimit (modulesStalkFunctor x)
    (differentialPullback R f)
  let d := quotientDifferentialStalkIsCokernel R f x
  exact congrArg (fun h ↦ h m)
    (IsColimit.comp_coconePointUniqueUpToIso_hom c d WalkingParallelPair.one)

end RelativeDifferentialStalk

section FiniteSkyscraper

variable {X : Scheme.{u}} (M : X.Modules) (s : Finset X)

private abbrev SectionStalkFamily (U : X.Opens) :=
  (z : s) → PLift ((z : X) ∈ U) → ↑(M.presheaf.stalk (z : X))

private def sectionStalkFamily (U : X.Opens) (r : Γ(M, U)) : SectionStalkFamily M s U :=
  fun z hz ↦ M.presheaf.germ U z hz.down r

variable (hs : ∀ z ∉ s, Subsingleton ↑(M.presheaf.stalk z))

include hs in
set_option backward.isDefEq.respectTransparency false in
private theorem sectionStalkFamily_injective (U : X.Opens) :
    Function.Injective (sectionStalkFamily M s U) := by
  classical
  intro a b hab
  apply TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
  intro x hx
  by_cases hxs : x ∈ s
  · exact congrFun (congrFun hab ⟨x, hxs⟩) ⟨hx⟩
  · exact (hs x hxs).elim _ _

variable (hc : ∀ z ∈ s, IsClosed ({z} : Set X))

include hs hc in
set_option backward.isDefEq.respectTransparency false in
private theorem sectionStalkFamily_surjective (U : X.Opens) :
    Function.Surjective (sectionStalkFamily M s U) := by
  classical
  intro m
  have hlocal (y : U) :
      ∃ (V : X.Opens) (i : V ⟶ U), (y : X) ∈ V ∧
        ∃ r : Γ(M, V), ∀ (z : s) (hz : (z : X) ∈ V),
          M.presheaf.germ V z hz r = m z ⟨i.le hz⟩ := by
    let E : Set X := ⋃ (z : X) (_ : z ∈ s.erase (y : X)), {z}
    have hE : IsClosed E :=
      (s.erase (y : X)).finite_toSet.isClosed_biUnion fun z hz ↦
        hc z (Finset.mem_of_mem_erase hz)
    let Q : X.Opens := U ⊓ ⟨Eᶜ, hE.isOpen_compl⟩
    have hy : (y : X) ∈ Q := ⟨y.property, by
      intro h
      obtain ⟨z, hz, heq⟩ := Set.mem_iUnion₂.mp h
      exact (Finset.mem_erase.mp hz).1 (Set.mem_singleton_iff.mp heq).symm⟩
    have unique (z : s) (hz : (z : X) ∈ Q) : (z : X) = (y : X) := by
      by_contra hne
      exact hz.2 (Set.mem_iUnion₂.mpr ⟨z, Finset.mem_erase.mpr ⟨hne, z.property⟩, rfl⟩)
    by_cases hys : (y : X) ∈ s
    · let a : s := ⟨y, hys⟩
      obtain ⟨V, hVQ, hyV, r, hr⟩ := M.presheaf.exists_le_germ_eq (m a ⟨y.property⟩) hy
      refine ⟨V, homOfLE (hVQ.trans inf_le_left), hyV, r, fun z hz ↦ ?_⟩
      have hza : z = a := Subtype.ext (unique z (hVQ hz))
      subst z
      exact hr
    · refine ⟨Q, homOfLE inf_le_left, hy, 0, fun z hz ↦ ?_⟩
      exact (hys ((unique z hz) ▸ z.property)).elim
  choose V iV hyV sf hsf using hlocal
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf V sf := by
    intro y z
    apply TopCat.Presheaf.section_ext (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    intro x hx
    change M.presheaf.germ (V y ⊓ V z) x hx
        (M.presheaf.map (Opens.infLELeft (V y) (V z)).op (sf y)) =
      M.presheaf.germ (V y ⊓ V z) x hx
        (M.presheaf.map (Opens.infLERight (V y) (V z)).op (sf z))
    rw [M.presheaf.germ_res_apply, M.presheaf.germ_res_apply]
    by_cases hxs : x ∈ s
    · exact (hsf y ⟨x, hxs⟩ hx.1).trans (hsf z ⟨x, hxs⟩ hx.2).symm
    · exact (hs x hxs).elim _ _
  have hcover : U ≤ ⨆ y : U, V y :=
    fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hyV ⟨x, hx⟩⟩
  obtain ⟨r, hr, -⟩ :=
    TopCat.Sheaf.existsUnique_gluing' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
      V U iV hcover sf hcompat
  refine ⟨r, ?_⟩
  funext z hz
  let y : U := ⟨z, hz.down⟩
  change M.presheaf.germ U z hz.down r = _
  rw [← M.presheaf.germ_res_apply (iV y) (z : X) (hyV y)]
  exact (congrArg (M.presheaf.germ (V y) z (hyV y)) (hr y)).trans (hsf y z (hyV y))

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/-- The skyscraper sheaf supported at `x` with coefficient module the stalk of `M`. -/
def modulesStalkSkyscraper (x : X) : X.Modules :=
  skyscraper x ↑(M.presheaf.stalk x)

set_option backward.isDefEq.respectTransparency false in
/-- A section maps to its germ in the skyscraper at the chosen point. -/
def modulesStalkSkyscraperProjection (x : X) : M ⟶ modulesStalkSkyscraper M x :=
  toSkyscraper x M ↑(M.presheaf.stalk x) LinearMap.id

private noncomputable def sectionStalkFamilyEquiv (U : X.Opens) :
    ↑Γ(M, U) ≃ SectionStalkFamily M s U :=
  Equiv.ofBijective (sectionStalkFamily M s U)
    ⟨sectionStalkFamily_injective M s hs U, sectionStalkFamily_surjective M s hs hc U⟩

variable (P : Fan (fun z : s ↦ modulesStalkSkyscraper M (z : X)))

set_option backward.isDefEq.respectTransparency false in
private def liftSkyscraperSection (U : X.Opens) (a : Γ(P.pt, U)) : Γ(M, U) :=
  (sectionStalkFamilyEquiv M s hs hc U).symm (fun z hz ↦ (P.proj z).app U a hz)

set_option backward.isDefEq.respectTransparency false in
private theorem liftSkyscraperSection_germ (U : X.Opens) (a : Γ(P.pt, U))
    (z : s) (hz : (z : X) ∈ U) :
    M.presheaf.germ U z hz (liftSkyscraperSection M s hs hc P U a) =
      (P.proj z).app U a ⟨hz⟩ :=
  congrFun (congrFun ((sectionStalkFamilyEquiv M s hs hc U).apply_symm_apply _) z) ⟨hz⟩

set_option backward.isDefEq.respectTransparency false in
private def liftStalkSkyscraperFan : P.pt ⟶ M := ⟨{
  app := fun U ↦ by
    letI : Module ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (P.pt.val.obj U) :=
      (P.pt.val.obj U).isModule
    letI : Module ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) (M.val.obj U) :=
      (M.val.obj U).isModule
    refine ConcreteCategory.ofHom
      (C := ModuleCat ((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U)) ?_
    refine
      { toFun := liftSkyscraperSection M s hs hc P U.unop
        map_add' := ?_
        map_smul' := ?_ }
    · intro a b
      apply sectionStalkFamily_injective M s hs U.unop
      funext z hz
      change M.presheaf.germ U.unop z hz.down (liftSkyscraperSection M s hs hc P U.unop (a + b)) =
        M.presheaf.germ U.unop z hz.down
          (liftSkyscraperSection M s hs hc P U.unop a + liftSkyscraperSection M s hs hc P U.unop b)
      rw [map_add, liftSkyscraperSection_germ, liftSkyscraperSection_germ,
        liftSkyscraperSection_germ, map_add]
      rfl
    · intro r a
      apply sectionStalkFamily_injective M s hs U.unop
      funext z hz
      let V := U.unop
      let r₀ : Γ(X, V) := r
      let a₀ : Γ(P.pt, V) := a
      change M.presheaf.germ V z hz.down (liftSkyscraperSection M s hs hc P V (r₀ • a₀)) =
        M.presheaf.germ V z hz.down (r₀ • liftSkyscraperSection M s hs hc P V a₀)
      rw [Scheme.Modules.germ_smul, liftSkyscraperSection_germ, liftSkyscraperSection_germ]
      have he := congrFun (((P.proj z).val.app U).hom.map_smul r a) hz
      exact he.trans (skyscraperObj_smul z _ V r₀ ((P.proj z).app V a₀) hz.down)
  naturality := fun {U V} i ↦ by
    ext a
    apply sectionStalkFamily_injective M s hs V.unop
    funext z hz
    change M.presheaf.germ V.unop z hz.down
        (liftSkyscraperSection M s hs hc P V.unop (P.pt.presheaf.map i a)) =
      M.presheaf.germ V.unop z hz.down
        (M.presheaf.map i (liftSkyscraperSection M s hs hc P U.unop a))
    have hres := M.presheaf.germ_res_apply i.unop z hz.down
      (liftSkyscraperSection M s hs hc P U.unop a)
    rw [liftSkyscraperSection_germ]
    refine (congrFun (PresheafOfModules.naturality_apply (P.proj z).val i a) hz).trans ?_
    exact (liftSkyscraperSection_germ M s hs hc P U.unop a z (i.unop.le hz.down)).symm.trans
      hres.symm }⟩

private def stalkSkyscraperFan : Fan (fun z : s ↦ modulesStalkSkyscraper M (z : X)) :=
  Fan.mk M fun z ↦ modulesStalkSkyscraperProjection M z

set_option backward.isDefEq.respectTransparency false in
private theorem stalkSkyscraperProjection_app (x : X) (U : X.Opens) (a : Γ(M, U)) (hx : x ∈ U) :
    (modulesStalkSkyscraperProjection M x).app U a ⟨hx⟩ = M.presheaf.germ U x hx a :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private def stalkSkyscraperFanIsLimit : IsLimit (stalkSkyscraperFan M s) :=
  Fan.IsLimit.mk _ (liftStalkSkyscraperFan M s hs hc)
    (fun F z ↦ by
      ext U a
      funext hz
      change (modulesStalkSkyscraperProjection M z).app U
          (liftSkyscraperSection M s hs hc F U a) ⟨hz.down⟩ =
        (F.proj z).app U a ⟨hz.down⟩
      rw [stalkSkyscraperProjection_app, liftSkyscraperSection_germ])
    (fun F g hg ↦ by
      ext U a
      apply sectionStalkFamily_injective M s hs U
      funext z hz
      change M.presheaf.germ U z hz.down (g.app U a) =
        M.presheaf.germ U z hz.down (liftSkyscraperSection M s hs hc F U a)
      rw [liftSkyscraperSection_germ, ← stalkSkyscraperProjection_app]
      have h := congrArg (fun φ ↦ φ.app U a hz) (hg z)
      exact h)

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf of modules whose stalks vanish away from finitely many closed points
is the product of the skyscraper sheaves of its stalks at those points. -/
def isoPiModulesStalkSkyscraper :
    M ≅ ∏ᶜ fun z : s ↦ modulesStalkSkyscraper M (z : X) :=
  (stalkSkyscraperFanIsLimit M s hs hc).conePointUniqueUpToIso (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The product isomorphism is induced by the canonical germ morphisms. -/
theorem isoPiModulesStalkSkyscraper_hom_π (z : s) :
    (isoPiModulesStalkSkyscraper M s hs hc).hom ≫ Pi.π _ z =
      modulesStalkSkyscraperProjection M z := by
  unfold isoPiModulesStalkSkyscraper
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (stalkSkyscraperFanIsLimit M s hs hc) (limit.isLimit _) ⟨z⟩

end FiniteSkyscraper

end

end TinyTauDemo
