/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Projective.HypersurfaceBaseChange
public import TinyTauDemo.AlgebraicGeometry.Dedekind.IntegerFibres
public import TinyTauDemo.Fermat.Curve.FermatProjective
import TinyTauDemo.Fermat.ArithmeticSurface.FermatArithmeticIntegrality

/-!
# Base change of the integral projective Fermat model

Scalar extension of the integer Fermat hypersurface gives the Fermat
hypersurface over the new coefficient ring, including in positive characteristic.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `cee501fadd7e1d00992825b62fa0edeae19d4e50`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace TinyTauDemo

/-- The projective Fermat model commutes with arbitrary coefficient extension from the integers. -/
noncomputable def fermatProjective_baseChangeIso (k : Type) [CommRing k] (n : ℕ) :
    fermatProjective k n ≅ pullback (fermatProjectiveToSpec ℤ n)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) := by
  have hF : (fermatEquation ℤ n).map (algebraMap ℤ k) = fermatEquation k n := by
    simp [fermatEquation_def]
  change ProjectiveHypersurface.scheme (fermatEquation_isHomogeneous k n) ≅
    pullback (ProjectiveHypersurface.toSpec (fermatEquation_isHomogeneous ℤ n))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))
  let h₁ := (fermatEquation_isHomogeneous ℤ n).map (algebraMap ℤ k)
  have h₂ : ProjectiveHypersurface.scheme h₁ =
      ProjectiveHypersurface.scheme (fermatEquation_isHomogeneous k n) := by
    let P : (F : MvPolynomial (Fin 3) k) → F.IsHomogeneous n → Scheme :=
      fun _ h ↦ ProjectiveHypersurface.scheme h
    exact congrArg (fun z : {F : MvPolynomial (Fin 3) k // F.IsHomogeneous n} ↦ P z.1 z.2)
      (show (⟨_, h₁⟩ : {F : MvPolynomial (Fin 3) k // F.IsHomogeneous n}) =
        ⟨_, fermatEquation_isHomogeneous k n⟩ from Subtype.ext hF)
  exact (eqToIso h₂.symm) ≪≫
    (ProjectiveHypersurface.isPullback_baseChangeHom (fermatEquation_isHomogeneous ℤ n)
      (algebraMap ℤ k)).isoPullback

/-- Extending the integral projective Fermat scheme to a characteristic-zero domain preserves
integrality in positive degree. -/
theorem isIntegral_fermatProjective_baseChange_of_charZero
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] {n : ℕ} (hn : 0 < n) :
    IsIntegral (pullback (fermatProjectiveToSpec ℤ n)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := by
  let := fermatProjective_isIntegral_of_charZero R hn
  exact IsIntegral.of_isIso (fermatProjective_baseChangeIso R n).hom

/-- The scheme-theoretic fibre of the integral Fermat model at the closed point `(p)`
is the Fermat model over `ZMod p`. -/
noncomputable def fermatProjective_fiberPrimeIntPointIso (n p : ℕ) [Fact p.Prime] :
    (fermatProjectiveToSpec ℤ n).fiber (primeIntPoint p) ≅ fermatProjective (ZMod p) n :=
  fiberPrimeIntPointIso (fermatProjectiveToSpec ℤ n) p ≪≫
    (fermatProjective_baseChangeIso (ZMod p) n).symm

end TinyTauDemo
