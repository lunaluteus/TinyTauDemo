/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Dirichlet L-values at zero

The logarithm series on the unit circle determines the sine zeta value at one.
Summation by parts bounds the tails uniformly for real exponents near one.
The Hurwitz functional equation gives the value at zero, and summing over residue
classes gives the first generalized Bernoulli value of a nontrivial character.

See `/roadmap/index.qmd#rem-bernoulli-regular` @ `3bebb147c3a76444954737508df190ace8972ff7`.
-/

public section

open Complex Finset Filter Set
open scoped Topology

namespace TinyTauDemo

private theorem norm_sum_geom_succ_le (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1) (n : ℕ) :
    ‖∑ i ∈ range n, z ^ (i + 1)‖ ≤ 2 / ‖z - 1‖ := by
  simp_rw [pow_succ', ← Finset.mul_sum, geom_sum_eq hne, norm_mul, hz, one_mul, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact (norm_sub_le _ _).trans_eq (by rw [norm_pow, hz, one_pow, norm_one]; norm_num)

private theorem one_sub_mem_slitPlane_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := by
  have hle := Complex.re_le_norm z
  rw [hz] at hle
  apply Complex.mem_slitPlane_iff.mpr
  left
  change 0 < 1 - z.re
  apply sub_pos.mpr
  apply lt_of_le_of_ne hle
  intro he
  have hn := Complex.normSq_eq_norm_sq z
  rw [Complex.normSq_apply, hz, he] at hn
  have him : z.im = 0 := by nlinarith
  exact hne (Complex.ext he him)

/-- The logarithm series converges in its natural order on the unit circle away from one. -/
theorem tendsto_sum_geom_div_eq_neg_log {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    Tendsto (fun n ↦ ∑ i ∈ range n, z ^ (i + 1) / ((i : ℂ) + 1))
      atTop (𝓝 (-Complex.log (1 - z))) := by
  let w (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hanti : Antitone w := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hzero : Tendsto w atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hC := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hzero
    (norm_sum_geom_succ_le z hz hne)
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hC
  have he (i : ℕ) : w i • z ^ (i + 1) = z ^ (i + 1) / ((i : ℂ) + 1) := by
    dsimp only [w]
    rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, one_div, div_eq_mul_inv, mul_comm]
  simp_rw [he] at hl
  have habel := Filter.tendsto_map'_iff.mp (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt hl)
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.continuousAt (x := 1)).continuousWithinAt.tendsto
  have hscaled := hreal.mul habel
  have hEq : (fun r : ℝ ↦ (r : ℂ) * ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) * (r : ℂ) ^ n) =ᶠ[
      𝓝[<] (1 : ℝ)] (fun r ↦ -Complex.log (1 - (r : ℂ) * z)) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)]
      with r hr1 hr0
    change r < 1 at hr1
    change 0 < r at hr0
    have hs : ‖(r : ℂ) * z‖ < 1 := by
      simpa [norm_mul, hz, Complex.norm_real, abs_of_pos hr0] using hr1
    rw [← tsum_mul_left]
    have h := (Complex.hasSum_taylorSeries_neg_log' hs).tsum_eq
    refine (tsum_congr fun n ↦ ?_).trans h
    rw [mul_pow, pow_succ (r : ℂ)]
    ring
  have h₁ := (hscaled.congr' hEq)
  have h₂ : Tendsto (fun r : ℝ ↦ -Complex.log (1 - (r : ℂ) * z)) (𝓝[<] (1 : ℝ))
      (𝓝 (-Complex.log (1 - z))) := by
    apply Tendsto.neg
    refine (continuousAt_clog (one_sub_mem_slitPlane_of_norm_eq_one hz hne)).tendsto.comp ?_
    simpa only [one_mul] using tendsto_const_nhds.sub (hreal.mul_const z)
  let := nhdsWithin_Iio_neBot (le_refl (1 : ℝ))
  have hL := tendsto_nhds_unique h₁ h₂
  simpa [← hL, one_mul] using hl

private noncomputable def dirichletWeight (s : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-s)

private noncomputable def dirichletDifference (z : ℂ) (s : ℝ) (n : ℕ) : ℂ :=
  (dirichletWeight s n - dirichletWeight s (n + 1)) • ∑ i ∈ range (n + 1), z ^ (i + 1)

private theorem norm_dirichletWeight_sub_le {s : ℝ} (hs : s ∈ Set.Icc 1 2) (n : ℕ) :
    ‖dirichletWeight s n - dirichletWeight s (n + 1)‖ ≤
      2 * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  let a : ℝ := (n : ℝ) + 1
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hb : ((n + 1 : ℕ) : ℝ) + 1 = a + 1 := by norm_num [a]
  have hdiff (x : ℝ) (hx : x ∈ Set.Icc a (a + 1)) :
      HasDerivWithinAt (fun y : ℝ ↦ y ^ (-s)) ((-s) * x ^ (-s - 1))
        (Set.Icc a (a + 1)) x :=
    (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Set.Ico a (a + 1)) :
      ‖(-s) * x ^ (-s - 1)‖ ≤ 2 * a ^ (-2 : ℝ) := by
    have hx1 : 1 ≤ x := ha.trans hx.1
    have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs0, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul hs.2
      ((Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [hs.1])).trans
        (Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by norm_num)))
      (Real.rpow_nonneg (by linarith) _) (by norm_num)
  have hr := norm_image_sub_le_of_norm_deriv_le_segment' hdiff hbound (a + 1)
    (right_mem_Icc.mpr (by linarith))
  rw [show a + 1 - a = 1 by ring, mul_one, norm_sub_rev] at hr
  simpa only [dirichletWeight, hb] using hr

private theorem norm_dirichletDifference_le {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    {s : ℝ} (hs : s ∈ Set.Icc 1 2) (n : ℕ) :
    ‖dirichletDifference z s n‖ ≤ (2 * (2 / ‖z - 1‖)) * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  rw [dirichletDifference, norm_smul]
  calc
    _ ≤ (2 * ((n : ℝ) + 1) ^ (-2 : ℝ)) * (2 / ‖z - 1‖) :=
      mul_le_mul (norm_dirichletWeight_sub_le hs n) (norm_sum_geom_succ_le z hz hne _)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem summable_dirichletDifference_bound (z : ℂ) :
    Summable (fun n : ℕ ↦ (2 * (2 / ‖z - 1‖)) * ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num))
  simpa only [Nat.cast_add, Nat.cast_one] using h.mul_left (2 * (2 / ‖z - 1‖))

private theorem tendsto_dirichletWeight_zero {s : ℝ} (hs : 1 ≤ s) :
    Tendsto (dirichletWeight s) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (fun n ↦ Real.rpow_nonneg (by positivity) _) ?_
  intro n
  change ((n : ℝ) + 1) ^ (-s) ≤ 1 / ((n : ℝ) + 1)
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)

private theorem tendsto_sum_dirichletWeight {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    {s : ℝ} (hs : s ∈ Set.Icc 1 2) :
    Tendsto (fun n ↦ ∑ i ∈ range n, dirichletWeight s i • z ^ (i + 1)) atTop
      (𝓝 (∑' n : ℕ, dirichletDifference z s n)) := by
  have hsum := ((summable_dirichletDifference_bound z).of_norm_bounded
    (norm_dirichletDifference_le hz hne hs)).hasSum.tendsto_sum_nat
  have hzero := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
    (tendsto_dirichletWeight_zero hs.1)
    ⟨2 / ‖z - 1‖, eventually_map.mpr <| Eventually.of_forall
      (fun n ↦ norm_sum_geom_succ_le z hz hne (n + 1))⟩
  change Tendsto (fun n : ℕ ↦ dirichletWeight s n • ∑ i ∈ range (n + 1), z ^ (i + 1))
    atTop (𝓝 (0 : ℂ)) at hzero
  have hparts (n : ℕ) :
      ∑ i ∈ range (n + 1), dirichletWeight s i • z ^ (i + 1) =
        dirichletWeight s n • (∑ i ∈ range (n + 1), z ^ (i + 1)) +
          ∑ i ∈ range n, dirichletDifference z s i := by
    rw [Finset.sum_range_by_parts, Nat.add_sub_cancel, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [dirichletDifference, ← neg_smul, neg_sub]
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Function.comp_apply, hparts, zero_add] using hzero.add hsum

private theorem tendsto_dirichletDifference_sum_at_one {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    Tendsto (fun s : ℝ ↦ ∑' n : ℕ, dirichletDifference z s n) (𝓝[>] (1 : ℝ))
      (𝓝 (∑' n : ℕ, dirichletDifference z 1 n)) := by
  refine tendsto_tsum_of_dominated_convergence (summable_dirichletDifference_bound z) ?_ ?_
  · intro n
    have he (m : ℕ) : ContinuousAt (fun s ↦ dirichletWeight s m) 1 := by
      exact ((Real.continuousAt_const_rpow (a := (m : ℝ) + 1)).comp
        continuous_neg.continuousAt)
    exact (((he n).sub (he (n + 1))).smul continuousAt_const).continuousWithinAt
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with s hs₁ hs₂
    exact norm_dirichletDifference_le hz hne ⟨le_of_lt hs₁, le_of_lt hs₂⟩

private theorem sinZeta_eq_dirichletDifference {a s : ℝ} (hs : s ∈ Set.Ioc 1 2)
    (hz : ‖Complex.exp ((2 * Real.pi * a : ℝ) * I)‖ = 1)
    (hne : Complex.exp ((2 * Real.pi * a : ℝ) * I) ≠ 1) :
    HurwitzZeta.sinZeta a (s : ℂ) =
      ((∑' n : ℕ, dirichletDifference (Complex.exp ((2 * Real.pi * a : ℝ) * I)) s n).im : ℂ) := by
  let z := Complex.exp ((2 * Real.pi * a : ℝ) * I)
  let f : ℕ → ℂ := fun n ↦
    (Real.sin (2 * Real.pi * a * (n : ℝ)) : ℂ) / (n : ℂ) ^ (s : ℂ)
  have hf := HurwitzZeta.hasSum_nat_sinZeta a (s := (s : ℂ)) (by simpa using hs.1)
  have hf₀ : f 0 = 0 := by simp [f]
  have hf₁ : HasSum (fun n : ℕ ↦ f (n + 1)) (HurwitzZeta.sinZeta a (s : ℂ)) :=
    (hasSum_nat_add_iff 1).mpr (by simpa only [sum_range_one, hf₀, add_zero] using hf)
  have hm : Continuous (fun x : ℂ ↦ (x.im : ℂ)) :=
    Complex.continuous_ofReal.comp Complex.imCLM.continuous
  have hx := (hm.tendsto _).comp (tendsto_sum_dirichletWeight (z := z) hz hne ⟨hs.1.le, hs.2⟩)
  have hterm (n : ℕ) : ((dirichletWeight s n • z ^ (n + 1)).im : ℂ) = f (n + 1) := by
    have hh : z ^ (n + 1) = Complex.exp
        ((2 * Real.pi * a * ((n + 1 : ℕ) : ℝ) : ℝ) * I) := by
      dsimp only [z]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hh, Complex.real_smul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    dsimp [f, dirichletWeight]
    rw [Complex.ofReal_mul, Real.rpow_neg (by positivity), Complex.ofReal_inv,
      Complex.ofReal_cpow (by positivity), div_eq_mul_inv, mul_comm]
    push_cast
    rfl
  have hsum (n : ℕ) :
      ((∑ i ∈ range n, dirichletWeight s i • z ^ (i + 1)).im : ℂ) =
        ∑ i ∈ range n, f (i + 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ, Complex.add_im, Complex.ofReal_add, ih, hterm]
  change Tendsto (fun n ↦ ((∑ i ∈ range n, dirichletWeight s i • z ^ (i + 1)).im : ℂ))
    atTop (𝓝 ((∑' n : ℕ, dirichletDifference z s n).im : ℂ)) at hx
  simp_rw [hsum] at hx
  exact tendsto_nhds_unique hf₁.tendsto_sum_nat hx

private theorem one_sub_cexp_two_mul (t : ℝ) :
    1 - Complex.exp ((2 * t : ℝ) * I) =
      ((2 * Real.sin t : ℝ) : ℂ) * Complex.exp ((t - Real.pi / 2 : ℝ) * I) := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re, Real.cos_two_mul, Real.cos_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · rw [Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, Complex.im_ofReal_mul,
      Complex.exp_ofReal_mul_I_im, Real.sin_two_mul, Real.sin_sub, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    ring

/-- The sine zeta at one equals the first Bernoulli polynomial times minus pi. -/
theorem sinZeta_one_eq {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    HurwitzZeta.sinZeta a (1 : ℂ) = ((Real.pi * (1 / 2 - a) : ℝ) : ℂ) := by
  let t := Real.pi * a
  have ht : 0 < t := mul_pos Real.pi_pos ha
  have ht' : t < Real.pi := by simpa [t] using mul_lt_mul_of_pos_left ha' Real.pi_pos
  let z := Complex.exp ((2 * Real.pi * a : ℝ) * I)
  have hfactor : 1 - z = ((2 * Real.sin t : ℝ) : ℂ) *
      Complex.exp ((t - Real.pi / 2 : ℝ) * I) := by
    dsimp [z, t]
    rw [show 2 * Real.pi * a = 2 * (Real.pi * a) by ring, one_sub_cexp_two_mul]
  have hsin : 0 < 2 * Real.sin t := mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi ht ht')
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp, Complex.mul_re]
  have hne : z ≠ 1 := by
    intro h
    rw [h, sub_self] at hfactor
    exact (mul_ne_zero (ofReal_ne_zero.mpr hsin.ne') (Complex.exp_ne_zero _)) hfactor.symm
  have hθ : t - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have him : (-Complex.log (1 - z)).im = Real.pi * (1 / 2 - a) := by
    rw [Complex.neg_im, Complex.log_im, hfactor, Complex.arg_real_mul _ hsin,
      Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hθ]
    dsimp [t]
    ring
  have hW : (∑' n : ℕ, dirichletDifference z 1 n) = -Complex.log (1 - z) := by
    apply tendsto_nhds_unique (tendsto_sum_dirichletWeight hz hne (s := 1)
      ⟨le_rfl, by norm_num⟩)
    convert tendsto_sum_geom_div_eq_neg_log hz hne using 1
    ext n
    apply sum_congr rfl
    intro i _
    simp only [dirichletWeight, Real.rpow_neg_one, Complex.real_smul, Complex.ofReal_inv,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, div_eq_mul_inv, mul_comm]
  have hcontinuity : Continuous (fun x : ℂ ↦ (x.im : ℂ)) :=
    Complex.continuous_ofReal.comp Complex.imCLM.continuous
  have hlim := (hcontinuity.tendsto _).comp (tendsto_dirichletDifference_sum_at_one hz hne)
  have heq : (fun s : ℝ ↦ ((∑' n : ℕ, dirichletDifference z s n).im : ℂ)) =ᶠ[
      𝓝[>] (1 : ℝ)] (fun s : ℝ ↦ HurwitzZeta.sinZeta a (s : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))]
      with s hs₁ hs₂
    exact (sinZeta_eq_dirichletDifference ⟨hs₁, hs₂.le⟩ hz hne).symm
  have h₁ := hlim.congr' heq
  have h₂ : Tendsto (fun s : ℝ ↦ HurwitzZeta.sinZeta a (s : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (HurwitzZeta.sinZeta a 1)) := by
    have hcont : Continuous (fun s : ℝ ↦ HurwitzZeta.sinZeta a (s : ℂ)) :=
      (HurwitzZeta.differentiableAt_sinZeta a).continuous.comp Complex.continuous_ofReal
    simpa only [Complex.ofReal_one] using
      (hcont.continuousAt (x := 1)).continuousWithinAt.tendsto
  let := nhdsWithin_Ioi_neBot (le_refl (1 : ℝ))
  simpa only [hW, him] using (tendsto_nhds_unique h₂ h₁)

/-- The Hurwitz zeta at zero for a representative strictly between zero and one. -/
theorem hurwitzZeta_zero_eq {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    HurwitzZeta.hurwitzZeta a 0 = ((1 / 2 - a : ℝ) : ℂ) := by
  have ha₀ : (a : UnitAddCircle) ≠ 0 := by
    exact fun h ↦ ha.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico
      (p := (1 : ℝ)) ⟨ha.le, ha'⟩).mp h)
  have hodd := HurwitzZeta.hurwitzZetaOdd_one_sub (a : UnitAddCircle) (s := 1)
    (fun n ↦ by
      intro he
      have h := congrArg Complex.re he
      simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at h
      linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [sub_self, Complex.cpow_neg, Complex.cpow_one, Complex.Gamma_one, mul_one, mul_one,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_sin, Real.sin_pi_div_two,
    Complex.ofReal_one, mul_one, sinZeta_one_eq ha ha'] at hodd
  rw [HurwitzZeta.hurwitzZeta, HurwitzZeta.hurwitzZetaEven_apply_zero, ite_eq_right ha₀,
    zero_add, hodd, Complex.ofReal_mul]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- A nontrivial Dirichlet L-function at zero is minus the first generalized Bernoulli number. -/
theorem dirichletLFunction_zero_eq_neg_generalizedBernoulli {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    χ.LFunction 0 = -χ.generalizedBernoulli 1 := by
  have hN : N ≠ 1 := fun h ↦ hχ (χ.level_one' h)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast NeZero.pos N
  rw [DirichletCharacter.LFunction, ZMod.LFunction, neg_zero, Complex.cpow_zero, one_mul,
    DirichletCharacter.generalizedBernoulli_one_of_ne_one hχ]
  calc
    _ = ∑ j : ZMod N, χ j * ((1 / 2 : ℂ) - (j.val : ℂ) / N) := by
      apply sum_congr rfl
      intro j _
      by_cases hj : j = 0
      · simp [hj, χ.map_zero' hN]
      · have hj0 : 0 < (j.val : ℝ) := by
          exact_mod_cast ZMod.val_pos.mpr hj
        have hjN : (j.val : ℝ) < N := by exact_mod_cast j.val_lt
        rw [ZMod.toAddCircle_apply, hurwitzZeta_zero_eq (div_pos hj0 hNpos)
            ((div_lt_one hNpos).mpr hjN), Complex.ofReal_sub, Complex.ofReal_div,
            Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
            Complex.ofReal_natCast, Complex.ofReal_natCast]
    _ = -(∑ j : ZMod N, χ j * ((j.val : ℂ) / N)) := by
      simp_rw [mul_sub]
      rw [sum_sub_distrib, ← sum_mul, MulChar.sum_eq_zero_of_ne_one hχ, zero_mul, zero_sub]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro j _
      rw [map_div₀, map_natCast, map_natCast]

end TinyTauDemo
