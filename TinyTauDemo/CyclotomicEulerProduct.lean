/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.CyclotomicPrimeFactors
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# Dedekind Euler products grouped by rational primes

The Dedekind Euler product can be grouped over rational primes using the
fibers of contraction. A local factorization then gives a quotient of
Dedekind zeta functions as a finite product of Dirichlet series.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `19d05f674280fce4d59c513fd4da7aafdc84ca61`.
-/

public section

open NumberField Ideal IsDedekindDomain
open scoped BigOperators NumberField

namespace TinyTauDemo

private def rationalPrimePlace (q : Nat.Primes) : HeightOneSpectrum ℤ :=
  ⟨rationalPrimeIdeal q, inferInstance, rationalPrimeIdeal_ne_bot q⟩

private noncomputable def rationalPrimePlaceEquiv : Nat.Primes ≃ HeightOneSpectrum ℤ :=
  Equiv.ofBijective rationalPrimePlace ⟨by
    intro p q h
    apply Subtype.ext
    exact (rationalPrimeIdeal_absNorm p).symm.trans
      ((congrArg (fun x : HeightOneSpectrum ℤ ↦ x.asIdeal.absNorm) h).trans
        (rationalPrimeIdeal_absNorm q)), by
    intro v
    let a := Submodule.IsPrincipal.generator v.asIdeal
    have ha : (Ideal.span {a} : Ideal ℤ) = v.asIdeal := Ideal.span_singleton_generator _
    have hne : a ≠ 0 := fun h ↦ v.ne_bot (by rw [← ha, h, Ideal.span_singleton_zero])
    have hp : Prime a := (Ideal.span_singleton_prime hne).mp (ha ▸ v.isPrime)
    refine ⟨⟨a.natAbs, Int.prime_iff_natAbs_prime.mp hp⟩, HeightOneSpectrum.ext ?_⟩
    change Ideal.span {((a.natAbs : ℕ) : ℤ)} = v.asIdeal
    exact (Int.span_natAbs a).trans ha⟩

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def groupedHeightOneSpectrumEquiv :
    (Σ q : Nat.Primes, (rationalPrimeIdeal q).primesOver (𝓞 K)) ≃ HeightOneSpectrum (𝓞 K) :=
  (Equiv.sigmaCongr rationalPrimePlaceEquiv (fun q ↦
    (HeightOneSpectrum.equivPrimesOver (𝓞 K) (rationalPrimeIdeal_ne_bot q)).symm.trans
      (Equiv.subtypeEquivRight fun w ↦ by
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal,
          ← liesOver_iff_dvd_map w.isPrime.ne_top]
        exact (Ideal.liesOver_iff w.asIdeal (rationalPrimeIdeal q)).trans eq_comm))).trans
    (Equiv.sigmaFiberEquiv (HeightOneSpectrum.under ℤ))

private theorem groupedHeightOneSpectrumEquiv_asIdeal
    (x : Σ q : Nat.Primes, (rationalPrimeIdeal q).primesOver (𝓞 K)) :
    (groupedHeightOneSpectrumEquiv K x).asIdeal = x.2.1 := by
  exact congrArg Subtype.val ((HeightOneSpectrum.equivPrimesOver (𝓞 K)
    (rationalPrimeIdeal_ne_bot x.1)).apply_symm_apply x.2)

/-- The Euler product of the Dedekind zeta function grouped by rational primes. -/
theorem dedekindZeta_hasProd_dedekindLocalFactor {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q ↦ dedekindLocalFactor K q s) (dedekindZeta K s) := by
  have h := (groupedHeightOneSpectrumEquiv K).hasProd_iff.mpr
    (TauCeti.dedekindZeta_eulerProduct_hasProd (K := K) hs)
  apply h.sigma
  intro q
  rw [dedekindLocalFactor]
  simpa only [Function.comp_apply, groupedHeightOneSpectrumEquiv_asIdeal] using
    hasProd_fintype (fun Q : (rationalPrimeIdeal q).primesOver (𝓞 K) ↦
      (1 - (Q.1.absNorm : ℂ) ^ (-s))⁻¹)

/-- A matching identity of local factors over rational primes gives the corresponding
global Dirichlet-series factorization of a Dedekind-zeta quotient. -/
theorem dedekindZeta_div_eq_prod_dirichlet_of_localFactors
    (L : Type*) [Field L] [NumberField L] {m : ℕ}
    (S : Finset (DirichletCharacter ℂ m)) {s : ℂ} (hs : 1 < s.re)
    (hlocal : ∀ q : Nat.Primes, dedekindLocalFactor K q s = dedekindLocalFactor L q s *
      ∏ χ ∈ S, (1 - χ (q : ℕ) * (q : ℂ) ^ (-s))⁻¹) :
    dedekindZeta K s / dedekindZeta L s = ∏ χ ∈ S, LSeries (χ ·) s := by
  let f (χ : DirichletCharacter ℂ m) (q : Nat.Primes) :=
    (1 - χ (q : ℕ) * (q : ℂ) ^ (-s))⁻¹
  have hχ (χ : DirichletCharacter ℂ m) : HasProd (f χ) (LSeries (χ ·) s) :=
    χ.LSeries_eulerProduct_hasProd hs
  have hS : HasProd (fun q ↦ ∏ χ ∈ S, f χ q) (∏ χ ∈ S, LSeries (χ ·) s) := by
    change Filter.Tendsto (fun T : Finset Nat.Primes ↦ ∏ q ∈ T, ∏ χ ∈ S, f χ q)
      Filter.atTop _
    simp_rw [Finset.prod_comm (t := S)]
    exact tendsto_finsetProd S (fun χ _ ↦ hχ χ)
  have hK := dedekindZeta_hasProd_dedekindLocalFactor K hs
  have hL := dedekindZeta_hasProd_dedekindLocalFactor L hs
  have heq : dedekindZeta K s = dedekindZeta L s * ∏ χ ∈ S, LSeries (χ ·) s :=
    hK.unique ((hL.mul hS).congr_fun hlocal)
  exact (div_eq_iff (TauCeti.dedekindZeta_ne_zero_of_one_lt_re (K := L) hs)).mpr
    (heq.trans (mul_comm _ _))

end TinyTauDemo
