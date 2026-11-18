/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.PrimeNormIndex
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.LocalizationKernel
import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer

/-!
# Brauer localization and the sum formula

Vanishing of first idele-class cohomology in a finite Galois splitting field gives injectivity of
Brauer localization. The sum formula follows from this injectivity.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IntermediateField TauCeti TauCeti.ClassFieldTheory

namespace TinyTauDemo

/-- Localization is injective on the Brauer group of a number field. -/
theorem brLocalization_injective
    (K : Type) [Field K] [NumberField K] : Function.Injective (brLocalization K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨E, _, _, y, rfl⟩ := exists_relBrInfl_eq x
  have : NumberField E := NumberField.of_module_finite K E
  have : IsGalois K E := {}
  let L := NormalLayer.ofOpenNormal (fixingOpenNormalSubgroup K E)
  have hE : fixedField L.top.toSubgroup = E := by
    dsimp only [L]
    rw [NormalLayer.top_ofOpenNormal, fixingOpenNormalSubgroup_toSubgroup E.val,
      IntermediateField.fieldRange_val, InfiniteGalois.fixedField_fixingSubgroup]
  have he (u : L.ground) (z : E) :
      ((layerGalEquiv E.val (u : L.Gal) z : E) : SeparableClosure K) =
        (u : AbsoluteGaloisGroup K) z := by
    rw [layerGalEquiv_mk]
    exact AlgHom.restrictNormalHom_commutes E.val _ z
  have : Subsingleton (L.H (globalFormation K) 1) := subsingleton_ideleClassLayer_H1 L
  have : Subsingleton (groupCohomology (ideleClassRep K E) 1) :=
    (L.ideleClassCohomologyEquiv hE he 1).symm.injective.subsingleton
  rw [(subsingleton_groupCohomology_one_ideleClassRep_iff E.val).1 ‹_› y hx, map_zero]

/-- The sum of the local invariants of a global Brauer class is zero. -/
theorem sumLocalInv_brLocalization_eq_zero
    (K : Type) [Field K] [NumberField K] (x : Br K) : sumLocalInv K (brLocalization K x) = 0 :=
  sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective K
    (fun E _ _ _ ↦ brLocalization_injective E) x

end TinyTauDemo
