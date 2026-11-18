/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.ArithmeticSurface.FermatSpecialFibre
import TinyTauDemo.Fermat.ArithmeticSurface.FermatProjectiveBaseChange
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Good reduction of the Fermat model

The closed fibre in residue characteristic not dividing the degree is smooth
of relative dimension one. In prime degree, the fibre at the exponent is the
unique nonreduced fibre among the closed points.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `40dfab7e513657bb92e859b30e7ad8f1b8c18a2d`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace TinyTauDemo

set_option backward.isDefEq.respectTransparency false in
/-- A Fermat model has smooth reduction of relative dimension one at every rational
prime which does not divide its degree. -/
theorem fermatProjective_fiber_smoothOne_of_not_dvd (n q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ n) :
    SmoothOfRelativeDimension 1 ((fermatProjectiveToSpec ℤ n).fiberToSpecResidueField
      (primeIntPoint q)) := by
  let f := fermatProjectiveToSpec ℤ n
  let b := primeIntPoint q
  let e := fermatProjective_fiberPrimeIntPointIso n q
  let s := Scheme.Spec.mapIso (primeIntPointResidueFieldIso q).op
  let z := Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod q)))
  have : IsClosedImmersion z := IsClosedImmersion.spec_of_surjective _ ZMod.intCast_surjective
  have he : e.inv ≫ f.fiberToSpecResidueField b =
      fermatProjectiveToSpec (ZMod q) n ≫ s.hom := by
    rw [← cancel_mono s.inv, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact (cancel_mono z).mp (specZIsTerminal.hom_ext _ _)
  have hEq : f.fiberToSpecResidueField b = e.hom ≫ fermatProjectiveToSpec (ZMod q) n ≫ s.hom := by
    rw [← cancel_epi e.inv, he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have : SmoothOfRelativeDimension 1 (fermatProjectiveToSpec (ZMod q) n) :=
    fermatProjective_smoothOne_of_natCast_ne_zero (ZMod q)
      (mt (ZMod.natCast_eq_zero_iff n q).mp hq)
  rw [hEq]
  have hcomp : SmoothOfRelativeDimension 1 (fermatProjectiveToSpec (ZMod q) n ≫ s.hom) :=
    smoothOfRelativeDimension_comp (n := 1) (m := 0) _ _
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

private theorem isReduced_fermatProjective_fiber_of_smooth (n q : ℕ) [Fact q.Prime]
    (h : Smooth ((fermatProjectiveToSpec ℤ n).fiberToSpecResidueField (primeIntPoint q))) :
    AlgebraicGeometry.IsReduced ((fermatProjectiveToSpec ℤ n).fiber (primeIntPoint q)) := by
  let K := ((Spec (.of ℤ)).residueField (primeIntPoint q) : Type)
  let f := (fermatProjectiveToSpec ℤ n).fiberToSpecResidueField (primeIntPoint q)
  have : GeometricallyReduced f := inferInstance
  exact GeometricallyReduced.geometrically_isReduced (𝟙 (Spec (.of K)))
    (𝟙 _) f (IsPullback.id_horiz f)

/-- For prime degree `p`, the reduction at a rational prime `q` is smooth exactly when
`q ≠ p`. -/
theorem fermatProjective_fiber_smooth_iff (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] :
    Smooth ((fermatProjectiveToSpec ℤ p).fiberToSpecResidueField (primeIntPoint q)) ↔ q ≠ p := by
  constructor
  · intro h hEq
    subst q
    exact not_isReduced_fermatProjective_fiber_prime p
      (isReduced_fermatProjective_fiber_of_smooth p p h)
  · intro hqp
    have hndvd : ¬ q ∣ p := fun h ↦ hqp ((Nat.dvd_prime hp.out).mp h |>.resolve_left
      hq.out.ne_one)
    have := fermatProjective_fiber_smoothOne_of_not_dvd p q hndvd
    exact SmoothOfRelativeDimension.smooth 1 _

/-- The closed fibres of the prime-degree Fermat model are reduced exactly away from that prime. -/
theorem fermatProjective_fiber_isReduced_iff (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    AlgebraicGeometry.IsReduced ((fermatProjectiveToSpec ℤ p).fiber (primeIntPoint q)) ↔ q ≠ p := by
  refine ⟨fun h hpq ↦ ?_, fun h ↦ ?_⟩
  · subst q
    exact not_isReduced_fermatProjective_fiber_prime p h
  · exact isReduced_fermatProjective_fiber_of_smooth p q
      ((fermatProjective_fiber_smooth_iff p q).mpr h)

end TinyTauDemo
