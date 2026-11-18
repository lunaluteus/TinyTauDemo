/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Radical.Basic
import TinyTauDemo.AlgebraicGeometry.Curves.RiemannHurwitz.HurwitzFibreCount
import TauCeti.FieldTheory.FunctionField.Divisor.RatFunc
import TauCeti.FieldTheory.FunctionField.Place.Map
import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# Mason–Stothers from Riemann–Hurwitz

The cover given by the reduced rational function `a / c` has degree equal to the
largest coordinate degree. The finite places over zero, one, and infinity belong
to the zero divisor of the radical of `a * b * c`. There is at most one more place.
See `/roadmap/index.qmd#rem-mason-hurwitz-bridge @ 1c4dad461408b9adac6d5698769a2b616a9cc434`.
-/

public section

open scoped IntermediateField
open Polynomial TauCeti TauCeti.AlgebraicGeometry UniqueFactorizationMonoid

namespace TinyTauDemo

variable {k : Type*} [Field k]

private noncomputable def zeroOneInfty (k : Type*) [Field k] :
    Finset (Place k (RatFunc k)) := by
  classical
  exact {Place.adicOfIrreducible (irreducible_X_sub_C (0 : k)),
    Place.adicOfIrreducible (irreducible_X_sub_C (1 : k)), Place.infty k}

private theorem card_zeroOneInfty (k : Type*) [Field k] : (zeroOneInfty k).card = 3 := by
  classical
  have h01 : Place.adicOfIrreducible (irreducible_X_sub_C (0 : k)) ≠
      Place.adicOfIrreducible (irreducible_X_sub_C (1 : k)) :=
    fun h ↦ zero_ne_one (Place.adicOfIrreducible_X_sub_C_injective h)
  have h0infty := Place.adicOfIrreducible_ne_infty (irreducible_X_sub_C (0 : k))
  have h1infty := Place.adicOfIrreducible_ne_infty (irreducible_X_sub_C (1 : k))
  unfold zeroOneInfty
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, h01, h0infty, or_false,
      not_false_eq_true]),
    Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using h1infty),
    Finset.card_singleton]

private theorem not_mem_zeroOneInfty_of_ord_eq_zero {Q : Place k (RatFunc k)}
    (hzero : Q.ord RatFunc.X = 0) (hzero1 : Q.ord (RatFunc.X - RatFunc.C (1 : k)) = 0) :
    Q ∉ zeroOneInfty k := by
  classical
  simp only [zeroOneInfty, Finset.mem_insert, Finset.mem_singleton]
  rintro (rfl | rfl | rfl)
  · have h := Place.ord_adicOfIrreducible_X_sub_C_self (0 : k)
    have he : RatFunc.X - RatFunc.C (0 : k) = RatFunc.X := by simp
    rw [he, hzero] at h
    omega
  · rw [Place.ord_adicOfIrreducible_X_sub_C_self] at hzero1
    omega
  · rw [Place.ord_infty, RatFunc.intDegree_X] at hzero
    omega

private theorem max_natDegree_num_denom_of_isCoprime
    {f : RatFunc k} {a c : k[X]} (ha : a ≠ 0) (hc : c ≠ 0) (hac : IsCoprime a c)
    (hf : f = algebraMap k[X] (RatFunc k) a / algebraMap k[X] (RatFunc k) c) :
    max f.num.natDegree f.denom.natDegree = max a.natDegree c.natDegree := by
  have hcross := (RatFunc.num_mul_eq_mul_denom_iff hc).mpr hf
  have han : a ∣ f.num := hac.dvd_of_dvd_mul_right ⟨f.denom, hcross⟩
  have hna : f.num ∣ a := (RatFunc.isCoprime_num_denom f).dvd_of_dvd_mul_right
    ⟨c, hcross.symm⟩
  have hcd : c ∣ f.denom := hac.symm.dvd_of_dvd_mul_left
    ⟨f.num, hcross.symm.trans (mul_comm f.num c)⟩
  have hdc : f.denom ∣ c := (RatFunc.isCoprime_num_denom f).symm.dvd_of_dvd_mul_left
    ⟨a, by rw [mul_comm f.denom a]; exact hcross⟩
  have hn0 : f.num ≠ 0 := RatFunc.num_ne_zero (hf ▸ div_ne_zero
    (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hc))
  have hnum : f.num.natDegree = a.natDegree :=
    le_antisymm (natDegree_le_of_dvd hna ha) (natDegree_le_of_dvd han hn0)
  have hden : f.denom.natDegree = c.natDegree :=
    le_antisymm (natDegree_le_of_dvd hdc hc)
      (natDegree_le_of_dvd hcd (RatFunc.denom_ne_zero f))
  rw [hnum, hden]

private theorem ord_algebraMap_eq_zero_of_not_dvd {q r : k[X]}
    (hq : Irreducible q) (hr : r ≠ 0) (hqr : ¬ q ∣ r) :
    (Place.adicOfIrreducible hq).ord (algebraMap k[X] (RatFunc k) r) = 0 := by
  rw [Place.ord_adicOfIrreducible_algebraMap hq hr, Nat.cast_eq_zero]
  exact (multiplicity_eq_zero (.of_not_isUnit hq.not_isUnit hr)).mpr hqr

open scoped Classical in
/-- Counting the three distinguished fibres of the cover `a / c` recovers the
Mason–Stothers degree bound over algebraically closed constants of characteristic zero. -/
theorem masonStothers_of_hurwitz [IsAlgClosed k] [CharZero k] {a b c : k[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hac : IsCoprime a c) (hsum : a + b = c)
    (hpos : 0 < max a.natDegree (max b.natDegree c.natDegree)) :
    max a.natDegree (max b.natDegree c.natDegree) + 1 ≤ (radical (a * b * c)).natDegree := by
  classical
  -- The degree of the rational cover is the degree of the reduced fraction.
  let i := algebraMap k[X] (RatFunc k)
  let f := i a / i c
  have hmax : max a.natDegree (max b.natDegree c.natDegree) =
      max a.natDegree c.natDegree := by
    have hbdeg : b.natDegree ≤ max c.natDegree a.natDegree := by
      have he : b = c - a := by rw [← hsum]; abel
      rw [he]
      exact natDegree_sub_le _ _
    omega
  have hdeg := max_natDegree_num_denom_of_isCoprime (f := f) ha hc hac rfl
  have hf : Transcendental k f := by
    apply RatFunc.transcendental_of_ne_C
    rintro ⟨r, hr⟩
    rw [hr] at hdeg
    simp at hdeg
    omega
  let F := k⟮f⟯
  let e : RatFunc k ≃ₐ[k] F := RatFunc.algEquivOfTranscendental f hf
  have hF : IsFunctionField k F := hf.isFunctionField_adjoin
  have hL : IsFunctionField k (RatFunc k) := IsFunctionField.ratFunc k
  have hFgenus : genus k F = 0 :=
    (genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv (fun r ↦ e.commutes r)).trans
      (genus_ratFunc k)
  have hfinrank : Module.finrank F (RatFunc k) = max a.natDegree c.natDegree :=
    (RatFunc.finrank_eq_max_natDegree f).trans hdeg
  let : FiniteDimensional F (RatFunc k) := Module.finite_of_finrank_pos (by omega)
  let : Algebra.IsSeparable F (RatFunc k) := inferInstance
  -- Transport the three target places and apply Riemann–Hurwitz to their fibres.
  let S : Finset (Place k F) := (zeroOneInfty k).map (Place.mapEquiv e).toEmbedding
  let D : Divisor k (RatFunc k) := Divisor.conorm k (RatFunc k) (WeilDivisor.ofFinset S)
  have hScard : S.card = 3 := by simp [S, card_zeroOneInfty]
  have hlow := card_places_above_lower_bound_of_genus_zero hF hL hFgenus (genus_ratFunc k) S
  rw [hScard, hfinrank] at hlow
  -- Every finite place in those fibres divides the squarefree radical.
  have hrad : radical (a * b * c) ≠ 0 := radical_ne_zero
  let Z := Divisor.zeros hL (Units.mk0 (i (radical (a * b * c)))
    (RatFunc.algebraMap_ne_zero hrad))
  have hle : WeilDivisor.ofFinset D.support ≤ Z + WeilDivisor.ofPoint (Place.infty k) := by
    refine WeilDivisor.le_iff.mpr fun P ↦ ?_
    rw [WeilDivisor.coeff_ofFinset, WeilDivisor.coeff_add, Divisor.coeff_zeros]
    simp only [Units.val_mk0]
    by_cases hP : P ∈ D.support
    · rw [ite_eq_left hP]
      rcases Place.eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C
           (P := P) (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hL) with hp | ⟨r, hp⟩
      · rw [hp, WeilDivisor.coeff_ofPoint_self]
        exact le_add_of_nonneg_left (le_max_right _ _)
      · let q := (X - C r : k[X])
        have hq : Irreducible q := irreducible_X_sub_C r
        have hPq : P = Place.adicOfIrreducible hq := hp
        have hdiv : q ∣ a * b * c := by
          by_contra! hnot
          have hqa : ¬ q ∣ a := fun h ↦ hnot ((h.mul_right b).mul_right c)
          have hqb : ¬ q ∣ b := fun h ↦ hnot ((h.mul_left a).mul_right c)
          have hqc : ¬ q ∣ c := fun h ↦ hnot (h.mul_left (a * b))
          have hPo {p : k[X]} (hp : p ≠ 0) (hd : ¬ q ∣ p) : P.ord (i p) = 0 :=
            hPq ▸ ord_algebraMap_eq_zero_of_not_dvd hq hp hd
          have hOrd : P.ord f = 0 := by
            dsimp only [f]
            rw [P.ord_div (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hc),
              hPo ha hqa, hPo hc hqc, sub_zero]
          have heq : f - 1 = -(i b / i c) := by
            dsimp only [f]
            rw [div_sub_one (RatFunc.algebraMap_ne_zero hc), ← map_sub, ← hsum,
              sub_add_eq_sub_sub, sub_self, zero_sub, map_neg, neg_div]
          have hOrd1 : P.ord (f - 1) = 0 := by
            rw [heq, P.ord_neg, P.ord_div (RatFunc.algebraMap_ne_zero hb)
              (RatFunc.algebraMap_ne_zero hc), hPo hb hqb, hPo hc hqc, sub_zero]
          have hPX : algebraMap F (RatFunc k) (e RatFunc.X) = f :=
            RatFunc.algEquivOfTranscendental_X f hf
          have hPX1 : algebraMap F (RatFunc k) (e (RatFunc.X - RatFunc.C (1 : k))) =
              f - 1 := by
            rw [map_sub, map_sub, hPX, map_one (RatFunc.C : k →+* RatFunc k), map_one, map_one]
          have hrestrict : P.restrict k F ∈ S := by
            simpa only [D, Divisor.mem_support_conorm_iff, WeilDivisor.support_ofFinset] using hP
          obtain ⟨Q, hQ, hQeq⟩ := Finset.mem_map.mp hrestrict
          have hQeq' : Q.map e = P.restrict k F := by
            simpa only [Equiv.toEmbedding_apply, Place.mapEquiv_apply] using hQeq
          have hu := Place.ord_algebraMap_restrict k F P (e RatFunc.X)
          rw [hPX, hOrd, ← hQeq', Place.ord_map_apply] at hu
          have hu1 := Place.ord_algebraMap_restrict k F P
            (e (RatFunc.X - RatFunc.C (1 : k)))
          rw [hPX1, hOrd1, ← hQeq', Place.ord_map_apply] at hu1
          have hnz : (Place.ramificationIdx F P : ℤ) ≠ 0 := by
            exact_mod_cast (Place.ramificationIdx_pos F P).ne'
          have hzero := (mul_eq_zero.mp hu.symm).resolve_left hnz
          have hzero1 := (mul_eq_zero.mp hu1.symm).resolve_left hnz
          exact not_mem_zeroOneInfty_of_ord_eq_zero hzero hzero1 hQ
        have hd := (dvd_radical_iff_of_irreducible hq (mul_ne_zero (mul_ne_zero ha hb) hc)).2 hdiv
        have hor : P.ord (i (radical (a * b * c))) = 1 := by
          rw [hPq, Place.ord_adicOfIrreducible_algebraMap_of_squarefree hq
            squarefree_radical, ite_eq_left hd]
        rw [hor, max_eq_left (by norm_num : (0 : ℤ) ≤ 1),
          WeilDivisor.coeff_ofPoint_of_ne (hPq ▸ Place.adicOfIrreducible_ne_infty hq), add_zero]
    · rw [ite_eq_right hP]
      exact add_nonneg (le_max_right _ _)
        ((WeilDivisor.isEffective_iff _).mp (WeilDivisor.isEffective_ofPoint _) P)
  have hh := Divisor.degree_le_of_le hle
  rw [map_add, Divisor.degree_zeros_algebraMap hrad, Divisor.degree_ofPoint, Place.degree_infty,
    Divisor.degree_eq_weilDivisorDegree_of_isAlgClosed hL, WeilDivisor.degree_ofFinset] at hh
  -- The abstract fibre count measures the support of the same conorm.
  change _ ≤ (D.support.card : ℤ) at hlow
  omega

end TinyTauDemo
