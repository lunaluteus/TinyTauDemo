/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatSchemeFunctionField
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TinyTauDemo.SchemeHurwitz

/-!
# The genus of the projective Fermat curve

See `/roadmap/index.qmd#prp-fermat-genus` @ `fbc988a5bcd0d78cdb5b294d62d21b7c0f620a09`.
-/

public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}

/-- The projective Fermat scheme is an integral proper curve of dimension one. -/
theorem fermatProjective_isCurveOver (hn : 0 < n) : (fermatProjective k n).IsCurveOver k := by
  have hI := fermatProjective_isIntegral k hn
  have hP : IsProper (fermatProjective k n ↘ Spec (.of k)) := by
    change IsProper (fermatProjectiveToSpec k n)
    infer_instance
  have hS : SmoothOfRelativeDimension 1 (fermatProjective k n ↘ Spec (.of k)) :=
    fermatProjective_smoothOne k hn
  exact Scheme.isCurveOver_iff.mpr ⟨hI, hP, topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (fermatProjective k n ↘ Spec (.of k))⟩

/-- The local ring at every codimension-one point of the projective Fermat curve is a DVR. -/
theorem fermatProjective_isDiscreteValuationRing_stalk (hn : 0 < n) :
    haveI := fermatProjective_isIntegral k hn
    ∀ x : CodimensionOnePoint (fermatProjective k n),
      IsDiscreteValuationRing
        ((fermatProjective k n).presheaf.stalk (x : fermatProjective k n)) := by
  let X := fermatProjective k n
  have : IsIntegral X := fermatProjective_isIntegral k hn
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := fermatProjective_smoothOne k hn
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  intro x
  change IsDiscreteValuationRing (X.presheaf.stalk (x : X))
  infer_instance

/-- The projective Fermat curve of degree n has genus (n - 1)(n - 2)/2. -/
theorem fermatProjective_genus (hn : 0 < n) :
    haveI := fermatProjective_isCurveOver k hn
    haveI := fermatProjective_isDiscreteValuationRing_stalk k hn
    haveI := finiteDimensional_cohomology_one_trivial_of_isProper k
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := fermatProjective k n) k)
    (fermatProjective k n).genus k = (n - 1) * (n - 2) / 2 := by
  have := fermatProjective_isCurveOver k hn
  have := fermatProjective_isDiscreteValuationRing_stalk k hn
  rw [genus_eq_genus_of_regularProperCurve (k := k) (fermatProjective k n)]
  exact genus_fermatProjective_functionField k hn

end TinyTauDemo
