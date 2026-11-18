/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.FermatEquation
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import TauCeti.RingTheory.MvPolynomial.CommonZero
import TauCeti.Algebra.MvPolynomial.Units

/-!
# Irreducibility of the homogeneous Fermat equation

Dehomogenization preserves the degree of the Fermat polynomial. Its affine
irreducibility therefore gives homogeneous irreducibility over an algebraically
closed field of characteristic zero.
See `/roadmap/index.qmd#prp-fermat-genus` @ `37a7f8d27fa89d22d5baf9d53ec026b2f30e9aba`.
-/

public section

open MvPolynomial

namespace TinyTauDemo

variable {k : Type*} [Field k]

private theorem dehomogenize_fermatEquation_two (n : ℕ) :
    TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k n) =
      X (0 : Fin 2) ^ n + X 1 ^ n - 1 := by
  have h0 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 0) = X 0 := by simp; rfl
  have h1 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 1) = X 1 := by simp; rfl
  have h2 : TauCeti.dehomogenize (R := k) (2 : Fin 3) (X 2) = 1 := by simp
  simp only [fermatEquation_def, map_sub, map_add, map_pow, h0, h1, h2, one_pow]

private theorem totalDegree_dehomogenize_fermatEquation {n : ℕ} (hn : 0 < n) :
    (TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k n)).totalDegree = n := by
  refine le_antisymm ((TauCeti.totalDegree_dehomogenize_le _ _).trans
    (fermatEquation_isHomogeneous k n).totalDegree_le) ?_
  let d : Fin 2 →₀ ℕ := Finsupp.single 0 n
  have hd0 : (0 : Fin 2 →₀ ℕ) ≠ d := by
    intro h
    exact hn.ne' (by simpa [d] using (DFunLike.congr_fun h 0).symm)
  have hd1 : Finsupp.single (1 : Fin 2) n ≠ d := by
    intro h
    exact hn.ne' (by simpa [d] using (DFunLike.congr_fun h 0).symm)
  have hc : (TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k n)).coeff d = 1 := by
    simp only [dehomogenize_fermatEquation_two, AddMonoidAlgebra.coeff_sub,
      AddMonoidAlgebra.coeff_add, Finsupp.sub_apply, Finsupp.add_apply, coeff_X_pow, coeff_one]
    change (if d = d then 1 else 0) + (if Finsupp.single (1 : Fin 2) n = d then 1 else 0) -
      (if 0 = d then 1 else 0) = (1 : k)
    simp [hd0, hd1]
  have hne : (TauCeti.dehomogenize (R := k) (2 : Fin 3) (fermatEquation k n)).coeff d ≠ 0 :=
    hc.trans_ne one_ne_zero
  have hm := le_totalDegree (mem_support_iff.mpr hne)
  simpa only [d, Finsupp.sum_single_index] using hm

variable [CharZero k]

/-- The equation of the Fermat curve is irreducible in the homogeneous coordinates. -/
theorem fermatEquation_irreducible [IsAlgClosed k] {n : ℕ} (hn : 0 < n) :
    Irreducible (fermatEquation k n) := by
  let D := TauCeti.dehomogenize (R := k) (2 : Fin 3)
  let F := fermatEquation k n
  have hdeg : (D F).totalDegree = n := totalDegree_dehomogenize_fermatEquation hn
  have hd : ¬ IsUnit (D F) := by
    intro hu
    exact hn.ne' (hdeg.symm.trans (isUnit_iff_totalDegree_of_isReduced.mp hu).2)
  have hD : Irreducible (D F) := by
    have h := TauCeti.irreducible_map_dehomogenize (K := k) (by decide : 2 ≤ 2)
      (fermatEquation_isHomogeneous k n)
      (fun b hb _ => fermatEquation_exists_aeval_pderiv_ne_zero hn b hb) (2 : Fin 3) hd
    simpa only [Algebra.algebraMap_self, MvPolynomial.map_id] using h
  refine ⟨fun hu => hd (hu.map D), ?_⟩
  intro a b hab
  have habD : D F = D a * D b := (congrArg D hab).trans (map_mul D a b)
  have haD : D a ≠ 0 := left_ne_zero_of_mul (habD ▸ hD.ne_zero)
  have hbD : D b ≠ 0 := right_ne_zero_of_mul (habD ▸ hD.ne_zero)
  have ha : a ≠ 0 := fun h => haD (by rw [h, map_zero])
  have hb : b ≠ 0 := fun h => hbD (by rw [h, map_zero])
  have hsum : a.totalDegree + b.totalDegree ≤ n := by
    rw [← totalDegree_mul_of_isDomain ha hb, ← hab]
    exact (fermatEquation_isHomogeneous k n).totalDegree_le
  have hsumD : (D a).totalDegree + (D b).totalDegree = n := by
    rw [← totalDegree_mul_of_isDomain haD hbD, ← habD, hdeg]
  have hle (f : MvPolynomial (Fin 3) k) : (D f).totalDegree ≤ f.totalDegree :=
    TauCeti.totalDegree_dehomogenize_le _ f
  have hunit {f : MvPolynomial (Fin 3) k} (hf : f ≠ 0) (hdeg : f.totalDegree = 0) :
      IsUnit f := by
    rw [totalDegree_eq_zero_iff_eq_C] at hdeg
    rw [hdeg] at hf ⊢
    exact (Ne.isUnit (by simpa using hf)).map C
  rcases hD.isUnit_or_isUnit habD with hu | hu
  · have : (D a).totalDegree = 0 := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    exact Or.inl (hunit ha (by have := hle b; omega))
  · have : (D b).totalDegree = 0 := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    exact Or.inr (hunit hb (by have := hle a; omega))

end TinyTauDemo
