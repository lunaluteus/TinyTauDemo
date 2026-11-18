/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TauCeti.AlgebraicGeometry.Birational.RationalMap
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
# Extension from a dense open of a regular curve

The generic-point restriction determines a morphism on a dense open. Properness
extends it through the valuation rings of the curve and separatedness gives uniqueness.
See `/roadmap/index.qmd#rem-scheme-curves-recall @ bfa7759fd8ba44b8e13df934ebe5c27f37f987eb`.
-/

public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

namespace TinyTauDemo

universe u

/-- A morphism over a separated base from a dense open of a regular integral curve to
a proper scheme extends uniquely over the whole curve. The curve hypotheses are stated
as a dimension bound and the discrete valuation property at codimension-one points. -/
theorem existsUnique_hom_extending_denseOpen
    {X Y S : Scheme.{u}} [X.Over S] [Y.Over S] [IsIntegral X] [S.IsSeparated]
    [IsProper (Y ↘ S)]
    [∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : Dense (U : Set X))
    (g : (U : Scheme) ⟶ Y) [g.IsOver S] :
    ∃! f : X ⟶ Y, f.IsOver S ∧ U.ι ≫ f = g := by
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU.nonempty)
  let i := U.fromSpecStalkOfMem (genericPoint X) hη
  have hi : i ≫ U.ι = X.fromSpecStalk (genericPoint X) := U.fromSpecStalkOfMem_ι _ _
  let φ := i ≫ g
  have hφ : φ ≫ Y ↘ S = X.fromSpecStalk (genericPoint X) ≫ X ↘ S := by
    dsimp only [φ]
    rw [Category.assoc, comp_over, ← Opens.ι_comp_over, ← Category.assoc, hi]
  let hval :=
    TauCeti.AlgebraicGeometry.Scheme.valuationRing_stalk_of_topologicalKrullDim_le_one hdim
  let f := homOfFunctionField hval φ hφ
  have hf : U.ι ≫ f = g := by
    let : IsDominant (i ≫ U.ι) := hi.symm ▸ inferInstance
    let : IsDominant i := IsDominant.of_comp_of_isOpenImmersion i U.ι
    apply ext_of_isDominant_of_isSeparated' S i
    rw [← Category.assoc, hi, fromSpecStalk_homOfFunctionField]
  refine ⟨f, ⟨inferInstance, hf⟩, fun f' hf' ↦ ?_⟩
  let : f'.IsOver S := hf'.1
  let : IsDominant U.ι := Opens.isDominant_ι hU
  exact ext_of_isDominant_of_isSeparated' S U.ι (hf'.2.trans hf.symm)

end TinyTauDemo
