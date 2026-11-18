/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Curve.FermatSchemeGenus
public import TinyTauDemo.AlgebraicGeometry.Curves.ProjectiveLineDifferentials
import TinyTauDemo.AlgebraicGeometry.Curves.FiniteCurveMorphisms
import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.CartierRamification

/-!
# The scheme-theoretic geometric Fermat obstruction

A dominant morphism from the projective line would force the genus of the
Fermat curve to be zero by Riemann–Hurwitz. In degree at least three its
genus is positive.

See `/roadmap/index.qmd#thm-flt-geometric` @ `65b292ea5da1634b3c772334122a6faf23a1e68a`.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry

namespace TinyTauDemo

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}

/-- There is no dominant morphism over `k` from the projective line to the
projective Fermat curve of degree at least three. -/
theorem not_isDominant_fermatProjectiveLineMap (hn : 3 ≤ n)
    (f : projectiveLine k ⟶ fermatProjective k n) [f.IsOver (Spec (.of k))] :
    ¬ IsDominant f := by
  intro hdom
  let : IsDominant f := hdom
  have hn₀ : 0 < n := by omega
  let : (projectiveLine k).IsCurveOver k := projectiveLine_isCurveOver k
  let : (fermatProjective k n).IsCurveOver k := fermatProjective_isCurveOver k hn₀
  let := projectiveLine_smoothOfRelativeDimension k
  let := isDiscreteValuationRing_stalk_of_codimensionOne_smoothCurve
    (k := k) (X := projectiveLine k)
  let := fermatProjective_isDiscreteValuationRing_stalk k hn₀
  have hg := genus_le_of_dominant_regularProperCurveHom (k := k) f
  rw [projectiveLine_genus k, fermatProjective_genus k hn₀] at hg
  have hm : 2 ≤ (n - 1) * (n - 2) := Nat.mul_le_mul (by omega : 2 ≤ n - 1)
    (by omega : 1 ≤ n - 2)
  omega

/-- A morphism over `k` from the projective line to a Fermat curve of degree
at least three has constant image. -/
theorem not_nonconstant_fermatProjectiveLineMap (hn : 3 ≤ n)
    (f : projectiveLine k ⟶ fermatProjective k n) [f.IsOver (Spec (.of k))] :
    ¬ ∃ x y : projectiveLine k, f x ≠ f y := by
  intro h
  have hn₀ : 0 < n := by omega
  let : (projectiveLine k).IsCurveOver k := projectiveLine_isCurveOver k
  let : (fermatProjective k n).IsCurveOver k := fermatProjective_isCurveOver k hn₀
  exact not_isDominant_fermatProjectiveLineMap hn f
    (isDominant_of_nonconstant_properCurveHom (k := k) f h)

end TinyTauDemo
