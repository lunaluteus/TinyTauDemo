/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.PlaneJacobian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.RingTheory.MvPolynomial.CommonZero
import TauCeti.Algebra.MvPolynomial.Units
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Integrality and dimension of nonsingular projective plane curves

See `/roadmap/index.qmd#rem-scheme-curves-recall @ ce3fed2d7209ae176aaa251ce23f48d13fd004d5`.
-/

public section

open AlgebraicGeometry CategoryTheory MvPolynomial TauCeti.AlgebraicGeometry

namespace TinyTauDemo.ProjectiveHypersurface

universe u

variable {k : Type u} [Field k]

private theorem exists_min_degree_coeff_mul {a b : MvPolynomial (Fin 3) k}
    (hb : b ≠ 0) :
    ∃ l ∈ b.support, (a * b).coeff l = a.coeff 0 * b.coeff l := by
  classical
  obtain ⟨t, ht⟩ := support_nonempty.mpr hb
  have hex : ∃ n : ℕ, ∃ l ∈ b.support, (l : Fin 3 →₀ ℕ).degree = n := ⟨_, t, ht, rfl⟩
  obtain ⟨l, hl, hld⟩ := Nat.find_spec hex
  refine ⟨l, hl, ?_⟩
  rw [coeff_mul, Finset.sum_eq_single (0, l)]
  · intro p hp hp0
    have hp' : p.1 + p.2 = l := Finset.mem_antidiagonal.mp hp
    have h1 : p.1 ≠ 0 := by
      intro h
      have h2 : p.2 = l := by simpa only [h, zero_add] using hp'
      exact hp0 (Prod.ext h h2)
    have hpos : 0 < p.1.degree := Nat.pos_of_ne_zero ((Finsupp.degree_eq_zero_iff _).not.mpr h1)
    have hsum : p.1.degree + p.2.degree = l.degree :=
      (Finsupp.degree.map_add _ _).symm.trans (congrArg Finsupp.degree hp')
    have hnmem : p.2 ∉ b.support := by
      intro h
      have hmin := Nat.find_min' hex ⟨p.2, h, rfl⟩
      omega
    rw [notMem_support_iff.mp hnmem, mul_zero]
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr (zero_add l))).elim

private theorem constantCoeff_eq_zero_of_nonunit_factor
    {a b : MvPolynomial (Fin 3) k} {d : ℕ} (hab : a * b ≠ 0)
    (hh : (a * b).IsHomogeneous d) (hu : ¬ IsUnit a) :
    constantCoeff a = 0 := by
  by_contra h
  obtain ⟨l, hl, hprod⟩ := exists_min_degree_coeff_mul (a := a) (right_ne_zero_of_mul hab)
  have hcoef : (a * b).coeff l ≠ 0 :=
    hprod ▸ mul_ne_zero h (mem_support_iff.mp hl)
  have hd : l.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hh hcoef
  have hbound := le_totalDegree hl
  change l.degree ≤ b.totalDegree at hbound
  rw [hd] at hbound
  have htotal := hh.totalDegree hab
  rw [totalDegree_mul_of_isDomain (left_ne_zero_of_mul hab) (right_ne_zero_of_mul hab)] at htotal
  have hdeg : a.totalDegree = 0 := by omega
  exact hu (by
    rw [totalDegree_eq_zero_iff_eq_C.mp hdeg]
    exact (isUnit_iff_ne_zero.mpr h).map C)

variable {d : ℕ} {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous d)
  {K : Type*} [Field K] [Algebra k K] [IsAlgClosed K]

include hF in
/-- A nonzero positive-degree homogeneous plane equation with no projective
singular point over an algebraically closed extension is irreducible. -/
theorem irreducible_of_forall_exists_pderiv_ne_zero (hd : 0 < d) (hF0 : F ≠ 0)
    (hJac : ∀ b : Fin 3 → K, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0) :
    Irreducible F := by
  refine ⟨?_, fun a b hab ↦ ?_⟩
  · intro h
    have hzero := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h).2
    rw [hF.totalDegree hF0] at hzero
    exact hd.ne' hzero
  · by_contra! hu
    have hab0 : a * b ≠ 0 := hab ▸ hF0
    have hhom : (a * b).IsHomogeneous d := hab ▸ hF
    have ha := constantCoeff_eq_zero_of_nonunit_factor hab0 hhom hu.1
    have hb := constantCoeff_eq_zero_of_nonunit_factor
      (by rwa [mul_comm]) (show (b * a).IsHomogeneous d by rwa [mul_comm]) hu.2
    obtain ⟨x, hx, hxab, hderiv⟩ :=
      exists_ne_zero_aeval_mul_eq_zero_and_aeval_pderiv_eq_zero (K := K)
        (by simp) ha hb
    obtain ⟨i, hi⟩ := hJac x hx (hab.symm ▸ hxab)
    exact hi (hab.symm ▸ hderiv i)

include hF in
private theorem irrelevant_ne_bot (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
    (hd : 0 < d) :
    HomogeneousIdeal.irrelevant (grading hF) ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hvanish⟩ := exists_ne_zero_forall_aeval_eq_zero (K := K)
    (s := {F}) (by simp) (by simpa using hF.constantCoeff_eq_zero hd.ne')
  have hxF : aeval x F = 0 := hvanish F (by simp)
  let φ : CoordinateRing F →ₐ[k] K := Ideal.Quotient.liftₐ _ (aeval x) (by
    intro p hp
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.mp hp
    rw [map_mul, hxF, zero_mul])
  intro he
  apply hx
  funext i
  have hpos := HomogeneousIdeal.mem_irrelevant_of_mem (grading hF) Nat.one_pos
    (coord_mem_degree_one hF i)
  rw [he] at hpos
  have hz : coord F i = 0 := Ideal.mem_bot.mp hpos
  have hz' := congrArg φ hz
  change aeval x (X i) = φ 0 at hz'
  simpa only [aeval_X, map_zero, Pi.zero_apply] using hz'

/-- A nonsingular projective plane equation of positive degree gives an integral scheme. -/
theorem isIntegral_of_forall_exists_pderiv_ne_zero (hd : 0 < d) (hF0 : F ≠ 0)
    (hJac : ∀ b : Fin 3 → K, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0) :
    IsIntegral (scheme hF) := by
  have hprime := (irreducible_of_forall_exists_pderiv_ne_zero hF hd hF0 hJac).prime
  have : (Ideal.span {F} : Ideal _).IsPrime := (Ideal.span_singleton_prime hF0).mpr hprime
  have : IsDomain (CoordinateRing F) := Ideal.Quotient.isDomain _
  change IsIntegral (Proj (grading hF))
  exact Proj.isIntegral_of_isDomain (grading hF) (irrelevant_ne_bot hF K hd)

/-- The forward projective-plane Jacobian criterion gives an integral proper curve,
smooth of relative dimension one over the base field. -/
theorem isIntegral_smoothOne_dim_of_forall_exists_pderiv_ne_zero (hd : 0 < d) (hF0 : F ≠ 0)
    (hJac : ∀ b : Fin 3 → K, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0) :
    IsIntegral (scheme hF) ∧ IsProper (toSpec hF) ∧ SmoothOfRelativeDimension 1 (toSpec hF) ∧
      topologicalKrullDim (scheme hF) = 1 := by
  let : IsIntegral (scheme hF) := isIntegral_of_forall_exists_pderiv_ne_zero hF hd hF0 hJac
  let : SmoothOfRelativeDimension 1 (toSpec hF) := smoothOne_of_forall_exists_pderiv_ne_zero hF hJac
  exact ⟨‹_›, inferInstance, ‹_›, topologicalKrullDim_eq_of_smoothOfRelativeDimension (toSpec hF)⟩

/-- Every closed point of a smooth projective plane curve has a discrete valuation stalk. -/
theorem isDiscreteValuationRing_stalk_of_isClosed
    [IsIntegral (scheme hF)] [SmoothOfRelativeDimension 1 (toSpec hF)]
    (x : scheme hF) (hx : IsClosed {x}) :
    IsDiscreteValuationRing ((scheme hF).presheaf.stalk x) := by
  have : Smooth (toSpec hF) := SmoothOfRelativeDimension.smooth 1 (toSpec hF)
  have : IsRegularLocalRing ((scheme hF).presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (toSpec hF) x
  apply TauCeti.IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
  exact ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (toSpec hF) 1).mp
    inferInstance).2 x hx

end TinyTauDemo.ProjectiveHypersurface
