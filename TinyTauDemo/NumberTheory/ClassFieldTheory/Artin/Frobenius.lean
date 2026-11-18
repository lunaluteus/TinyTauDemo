/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Artin.Finite
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Frobenius
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# Frobenius normalization of the finite Artin symbol

At an unramified prime the decomposition isomorphism identifies arithmetic Frobenius with the
local Frobenius. The local normalization then evaluates the symbol of a uniformizer.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti TauCeti.ClassFieldTheory
open scoped NumberField Pointwise AdicCompletionExtension

namespace TinyTauDemo

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- At an unramified prime, a completion uniformizer maps to the arithmetic Frobenius
in the abelianized global Galois group. -/
theorem finiteLocalArtinAt_uniformizer (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hw : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal)
    {π : (v.adicCompletion K)ˣ} (hπ : IsUniformizer (v.adicCompletion K) π) :
    finiteLocalArtinAt K L v π = Abelianization.of σ := by
  let : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hw
  let : IsUnramified (v.adicCompletion K) (w.adicCompletion L) :=
    isUnramified_adicCompletion_of_isUnramifiedAt v w
  let ι : w.adicCompletion L →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  apply finiteLocalArtinAt_eq_of_decompositionHom v w ι ⟨σ, hσ.mem_stabilizer⟩
  rw [decompositionHom_eq_frobeniusAlgEquiv v w hσ]
  exact localArtinMap_uniformizer _ _ ι hπ

end TinyTauDemo
