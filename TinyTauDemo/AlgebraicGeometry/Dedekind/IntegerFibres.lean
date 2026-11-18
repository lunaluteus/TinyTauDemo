/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.Ideal.Int

/-!
# Fibres over rational primes

The scheme-theoretic fibre over the closed point `(p)` of the integer spectrum
is the base change to the field `ZMod p`.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `cee501fadd7e1d00992825b62fa0edeae19d4e50`.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace TinyTauDemo

/-- The closed point of the integer spectrum associated to a rational prime. -/
@[expose]
def primeIntPoint (p : ℕ) [Fact p.Prime] : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)}, (Int.ideal_span_isMaximal_of_prime p).isPrime⟩

/-- The residue field at the closed point `(p)` is `ZMod p`. -/
noncomputable def primeIntPointResidueFieldIso (p : ℕ) [Fact p.Prime] :
    (Spec (.of ℤ)).residueField (primeIntPoint p) ≅ CommRingCat.of (ZMod p) := by
  let I := (primeIntPoint p).asIdeal
  let : I.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let e : (ℤ ⧸ I) ≃ₐ[ℤ] I.ResidueField :=
    .ofBijective (IsScalarTower.toAlgHom ℤ (ℤ ⧸ I) I.ResidueField)
      (I.bijective_algebraMap_quotient_residueField)
  exact Scheme.Spec.residueFieldIso (.of ℤ) _ ≪≫
    (e.symm.toRingEquiv.trans (Int.quotientSpanNatEquivZMod p)).toCommRingCatIso

set_option backward.isDefEq.respectTransparency false in
/-- The residue-field point is induced by the reduction map on the integers. -/
theorem primeIntPoint_fromSpecResidueField (p : ℕ) [Fact p.Prime] :
    Spec.map (primeIntPointResidueFieldIso p).hom ≫
        (Spec (.of ℤ)).fromSpecResidueField (primeIntPoint p) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p))) := by
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- The fibre of a scheme over the integer spectrum at `(p)` is its base change to
`ZMod p`. -/
noncomputable def fiberPrimeIntPointIso {X : Scheme} (f : X ⟶ Spec (.of ℤ))
    (p : ℕ) [Fact p.Prime] :
    f.fiber (primeIntPoint p) ≅ pullback f (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod p)))) :=
  (asIso (pullback.map _ _ _ _ (𝟙 _) (Spec.map (primeIntPointResidueFieldIso p).hom) (𝟙 _)
    (by simp)
    (by simpa only [Category.comp_id] using (primeIntPoint_fromSpecResidueField p).symm))).symm

end TinyTauDemo
