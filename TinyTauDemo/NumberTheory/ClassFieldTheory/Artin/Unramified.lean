/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.NumberTheory.ClassFieldTheory.Artin.Classes
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Unramifiedness detected by idele-class characters

When a character kills the integral finite ideles and has the kernel of an Artin map, the
finite local symbols kill the units at each place. This gives unramifiedness.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `11f797279de2c5c4d311420a804b8cd976ecbb67`.
-/

public section

open NumberField IsDedekindDomain TauCeti
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField IsMulCommutative

namespace TinyTauDemo

/-- An abelian extension is unramified at every finite prime if its Artin kernel is the kernel
of a character that kills the integral finite ideles. -/
theorem isUnramifiedAt_of_ideleClassCharacter_ker_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] {A : Type*} [Monoid A]
    (χ : IdeleClassGroup (𝓞 K) K →* A)
    (hχ : ∀ x : IdeleGroup (𝓞 K) K,
      IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K → χ x = 1)
    (hk : (ideleClassAbelianArtinMap K L).ker = χ.ker) (w : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  classical
  let v := w.under (𝓞 K)
  have : w.asIdeal.LiesOver v.asIdeal := inferInstance
  apply (isUnramifiedAt_iff_unitFiltration_le_ker_finiteLocalArtinAt v w).2
  intro u hu
  let x := IdeleGroup.ofAdicCompletion (𝓞 K) K v u
  have hx : IdeleGroup.toFiniteIdele (𝓞 K) K x ∈ FiniteAdeleRing.integralUnits (𝓞 K) K := by
    refine FiniteAdeleRing.mem_integralUnits_iff.mpr fun q ↦ ?_
    rw [IdeleGroup.coe_toFiniteIdele, ← HeightOneSpectrum.coe_ideleFiniteCoord]
    by_cases hq : q = v
    · subst q
      rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_self]
      exact (mem_unitFiltration_zero_adicCompletion_iff v).mp hu
    · rw [HeightOneSpectrum.ideleFiniteCoord_ofAdicCompletion_of_ne _ hq, Units.val_one, map_one]
  have hαx : ideleClassAbelianArtinMap K L x = 1 := by
    rw [← MonoidHom.mem_ker, hk]
    exact hχ x hx
  change finiteLocalArtinAt K L v u = 1
  rw [← ideleArtinMap_ofAdicCompletion, ← ideleClassArtinMap_mk,
    ← abelianization_of_ideleClassAbelianArtinMap, hαx, map_one]

end TinyTauDemo
