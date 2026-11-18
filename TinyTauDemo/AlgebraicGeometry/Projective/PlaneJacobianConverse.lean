/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.AlgebraicGeometry.Projective.PlaneJacobian
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The converse Jacobian criterion for plane hypersurfaces

See `/roadmap/index.qmd#rem-scheme-curves-recall @ ce3fed2d7209ae176aaa251ce23f48d13fd004d5`.
-/

public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace TinyTauDemo

universe u

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- Formal smoothness of a nonzero plane hypersurface implies that the gradient
does not vanish at any rational point. -/
theorem exists_aeval_pderiv_ne_zero_of_formallySmooth {f : MvPolynomial (Fin 2) k}
    (hf : f ≠ 0)
    (hsm : Algebra.FormallySmooth k (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}))
    {a : Fin 2 → k} (ha : aeval a f = 0) :
    ∃ i, aeval a (pderiv i f) ≠ 0 := by
  classical
  by_contra! hzero
  let R := MvPolynomial (Fin 2) k
  let I : Ideal R := Ideal.span {f}
  let A := R ⧸ I
  let q : R →ₐ[k] A := Ideal.Quotient.mkₐ k I
  let G : Algebra.Generators k A (Fin 2) :=
    Algebra.Generators.ofAlgHom q (Ideal.Quotient.mkₐ_surjective k I)
  let P := G.toExtension
  have hker : P.ker = I := by
    change G.ker = I
    rw [Algebra.Generators.ker_ofAlgHom]
    exact Ideal.Quotient.mkₐ_ker k I
  have hqalg : aeval G.val = q := by
    apply MvPolynomial.algHom_ext
    intro i
    change aeval (q ∘ X) (X i) = q (X i)
    rw [aeval_X]
    rfl
  have hq (y : P.Ring) : algebraMap P.Ring A y = q y := AlgHom.congr_fun hqalg y
  let : IsDomain P.Ring := inferInstanceAs (IsDomain R)
  have hpr : P.ker.IsPrincipal := ⟨f, hker⟩
  have hI : P.ker ≠ ⊥ := by
    intro he
    have hz : (f : P.Ring) ∈ P.ker := by
      rw [hker]
      exact Ideal.mem_span_singleton_self f
    rw [he] at hz
    exact hf (Ideal.mem_bot.mp hz)
  let A₀ := P.Ring ⧸ P.ker
  have ePow (J : Ideal P.Ring) (hJ : J = P.ker) :
      (J ⧸ (P.ker • ⊤ : Submodule P.Ring J)) ≃ₗ[P.Ring] P.ker.Cotangent := by
    subst J
    exact LinearEquiv.refl _ _
  let e' := (Ideal.quotEquivPowQuotPowSucc hpr hI 1).trans (ePow _ (pow_one _))
  let e : P.Cotangent ≃ₗ[P.Ring] A₀ := P.cotangentEquivCotangentKer.trans e'.symm
  let c := e.symm 1
  obtain ⟨y, hy⟩ := Algebra.Extension.Cotangent.mk_surjective c
  have toIdeal (p : R) (hp : p ∈ P.ker) : p ∈ I := by
    rw [← hker]
    exact hp
  let y₀ : R := y.val
  have hmem : y₀ ∈ I := toIdeal y₀ y.property
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hmem
  have hdy (i : Fin 2) : aeval a (pderiv i y₀) = 0 := by
    rw [hg, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [map_add, map_mul, ha, hzero i, zero_mul, mul_zero, add_zero]
  let pt : A₀ →ₐ[k] k := Ideal.Quotient.liftₐ P.ker (aeval a) (by
    intro p hp
    let p₀ : R := p
    have hm : p₀ ∈ I := toIdeal p₀ hp
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hm
    change aeval a p₀ = 0
    rw [hg, map_mul, ha, zero_mul])
  have hpt (p : P.Ring) : pt (algebraMap P.Ring A₀ p) = aeval a p := rfl
  let : Algebra.FormallySmooth k P.Ring := inferInstanceAs (Algebra.FormallySmooth k R)
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp hsm
  have hrepr (i : Fin 2) :
      G.cotangentSpaceBasis.repr (P.cotangentComplex c) i =
        algebraMap P.Ring A (pderiv i y₀) := by
    rw [← hy, Algebra.Extension.cotangentComplex_mk,
      Algebra.Generators.cotangentSpaceBasis_repr_one_tmul, hq]
    exact AlgHom.congr_fun hqalg _
  let D (i : Fin 2) : P.Ring := pderiv i y₀
  have hsum : P.cotangentComplex c = ∑ i, D i • G.cotangentSpaceBasis i := by
    calc
      _ = ∑ i, G.cotangentSpaceBasis.repr (P.cotangentComplex c) i •
          G.cotangentSpaceBasis i := (G.cotangentSpaceBasis.sum_repr _).symm
      _ = _ := by simp only [hrepr, ← show ∀ i, D i = pderiv i y₀ from fun _ ↦ rfl,
          algebraMap_smul]
  have hsplit : l (P.cotangentComplex c) = c := DFunLike.congr_fun hl c
  have hsuml : l (P.cotangentComplex c) = ∑ i, D i • l (G.cotangentSpaceBasis i) := by
    rw [hsum]
    change (l.restrictScalars P.Ring) (∑ i, D i • G.cotangentSpaceBasis i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      (l.restrictScalars P.Ring).map_smul (D i) (G.cotangentSpaceBasis i)
  have hlast : pt (e (∑ i, D i • l (G.cotangentSpaceBasis i))) = 1 := by
    rw [← hsuml, hsplit]
    change pt (e (e.symm 1)) = 1
    rw [e.apply_symm_apply, map_one]
  have hz (i : Fin 2) : pt (e (D i • l (G.cotangentSpaceBasis i))) = 0 := by
    rw [map_smul, Algebra.smul_def, map_mul, hpt]
    exact mul_eq_zero.mpr (Or.inl (hdy i))
  simp only [map_sum, hz, Finset.sum_const_zero] at hlast
  exact zero_ne_one hlast

namespace ProjectiveHypersurface

variable {d : ℕ} {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous d)

/-- Smoothness of a projective plane hypersurface defined by a nonzero equation
implies that the homogeneous gradient is nonzero at every rational point. -/
theorem forall_exists_pderiv_ne_zero_of_smooth (hF0 : F ≠ 0) (hsm : Smooth (toSpec hF)) :
    ∀ b : Fin 3 → k, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0 := by
  intro b hb₀ hb
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra! hz
    exact hb₀ (funext hz)
  let a : Fin 2 → k := fun j ↦ b (i.succAbove j) / b i
  have hb' : eval b F = 0 := hb
  have ha : aeval a (TauCeti.dehomogenize i F) = 0 := by
    rw [aeval_eq_eval, TauCeti.eval_dehomogenize_div i hF b hi, hb', mul_zero]
  have hg : TauCeti.dehomogenize i F ≠ 0 := by
    intro he
    exact hF0 (TauCeti.dehomogenize_injOn i d hF (isHomogeneous_zero _ _ _)
      (by rw [he, map_zero]))
  have hs : Smooth (affineChart hF i ≫ toSpec hF) := inferInstance
  rw [affineChart_comp_toSpec] at hs
  have hR : Algebra.Smooth k (ChartRing F i) := by
    rw [← RingHom.smooth_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
  have hm : Algebra.FormallySmooth k (ChartRing F i) := Algebra.Smooth.formallySmooth
  simpa only [aeval_eq_eval] using
    (TauCeti.exists_eval_pderiv_ne_zero_iff_dehomogenize_div i hF b hi hb').mpr
      (exists_aeval_pderiv_ne_zero_of_formallySmooth hg hm ha)

/-- The projective plane Jacobian criterion over an algebraically closed field. -/
theorem smooth_iff_forall_exists_pderiv_ne_zero [IsAlgClosed k] (hF0 : F ≠ 0) :
    Smooth (toSpec hF) ↔
      ∀ b : Fin 3 → k, b ≠ 0 → aeval b F = 0 → ∃ i, aeval b (pderiv i F) ≠ 0 := by
  refine ⟨forall_exists_pderiv_ne_zero_of_smooth hF hF0, fun hJac ↦ ?_⟩
  have := smoothOne_of_forall_exists_pderiv_ne_zero hF hJac
  exact SmoothOfRelativeDimension.smooth 1 (toSpec hF)

end ProjectiveHypersurface

end TinyTauDemo
