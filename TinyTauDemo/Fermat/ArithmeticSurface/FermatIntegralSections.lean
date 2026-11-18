/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import TinyTauDemo.Fermat.Polynomial.FermatSpecMap
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ChartEquality
import TauCeti.Data.Rat.PrimitiveDenominator
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Integral sections of the projective Fermat scheme

Primitive integer triples satisfying the Fermat equation, up to common sign,
are equivalent to sections of the projective Fermat scheme over the integers.
To recover a triple, restrict a section to the rational generic point, normalize
in a standard chart, then clear denominators primitively. Separatedness makes
the reconstructed section equal to the original.

See `/roadmap/index.qmd#rem-arithmetic-surface` @ `60c5097c3d45c49d5822159e0efd14f6846b1f9f`.
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TauCeti.GradedAlgebra

namespace TinyTauDemo

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {f : A} (hf : f ∈ 𝒜 1)

private noncomputable def componentNormalize (d : ℕ) : 𝒜 d →+ Away 𝒜 f :=
  (Away.mkLinearMap (𝒜 := 𝒜) hf d).toAddMonoidHom.comp
    (LinearEquiv.ofEq _ _ (by rw [Nat.nsmul_eq_mul, mul_one])).toAddEquiv.toAddMonoidHom

private theorem componentNormalize_apply (d : ℕ) (a : 𝒜 d) :
    componentNormalize 𝒜 hf d a =
      Away.mk 𝒜 hf d (a : A) (by simpa only [Nat.nsmul_eq_mul, mul_one] using a.2) := by
  change Away.mkLinearMap hf d ⟨a, _⟩ = _
  rw [Away.mkLinearMap_apply]

private noncomputable def normalizeChart : A →+* Away 𝒜 f :=
  (DirectSum.toSemiring (componentNormalize 𝒜 hf) (by
    rw [componentNormalize_apply]
    apply val_injective
    rw [Away.val_mk, val_one]
    change Localization.mk 1 (⟨f ^ 0, _⟩ : Submonoid.powers f) = 1
    simp
  ) (by
    intro i j ai aj
    simp only [componentNormalize_apply]
    apply val_injective
    simp only [Away.val_mk, val_mul, Localization.mk_mul, SetLike.coe_gMul]
    congr 1
    exact Subtype.ext (pow_add f i j)
  )).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

private theorem normalizeChart_apply_of_mem {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    normalizeChart 𝒜 hf a =
      Away.mk 𝒜 hf d a (by simpa only [Nat.nsmul_eq_mul, mul_one] using ha) := by
  unfold normalizeChart
  simp only [RingHom.comp_apply]
  have hdecomp : (DirectSum.decomposeRingEquiv 𝒜).toRingHom a = DirectSum.of _ d ⟨a, ha⟩ :=
    DirectSum.decompose_of_mem 𝒜 ha
  rw [hdecomp, DirectSum.toSemiring_of, componentNormalize_apply]

@[simp] private theorem normalizeChart_apply_self : normalizeChart 𝒜 hf f = 1 := by
  rw [normalizeChart_apply_of_mem 𝒜 hf hf]
  apply val_injective
  rw [Away.val_mk, val_one]
  change Localization.mk f (⟨f ^ 1, _⟩ : Submonoid.powers f) = 1
  rw [← Localization.mk_self (⟨f, Submonoid.mem_powers _⟩ : Submonoid.powers f)]
  congr 1
  exact Subtype.ext (pow_one f)

end

private theorem normalizeChart_lift {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {f : A} (hf : f ∈ 𝒜 1)
    (ψ : Away 𝒜 f →+* B) (hu : IsUnit ((ψ.comp (normalizeChart 𝒜 hf)) f)) :
    Away.lift 𝒜 (ψ.comp (normalizeChart 𝒜 hf)) hu = ψ := by
  ext z
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  have hu' : hu.unit = 1 := Units.ext (by
    rw [IsUnit.unit_spec, RingHom.comp_apply, normalizeChart_apply_self, map_one, Units.val_one])
  rw [Away.lift_mk, hu', one_pow, inv_one, Units.val_one, mul_one, RingHom.comp_apply]
  rw [normalizeChart_apply_of_mem 𝒜 hf (show a ∈ 𝒜 d by
    simpa only [Nat.nsmul_eq_mul, mul_one] using ha)]

/-- A primitive integral tuple satisfying the homogeneous Fermat equation.
Primitivity means that the coordinates generate the unit ideal. -/
structure PrimitiveIntegerFermatCoordinates (n : ℕ) where
  coord : Fin 3 → ℤ
  equation : coord 0 ^ n + coord 1 ^ n = coord 2 ^ n
  generates : Ideal.span (Set.range coord) = ⊤

/-- Sections of the structure morphism of the Fermat scheme over the integers. -/
abbrev IntegralFermatSections (n : ℕ) :=
  {s : Spec (.of ℤ) ⟶ fermatProjective ℤ n // s ≫ fermatProjectiveToSpec ℤ n = 𝟙 _}

variable {n : ℕ}

/-- A primitive tuple of integer coordinates defines a section of the integral Fermat scheme. -/
noncomputable def PrimitiveIntegerFermatCoordinates.toSection
    (p : PrimitiveIntegerFermatCoordinates n) : IntegralFermatSections n :=
  ⟨fermatSpecMap (k := ℤ) p.coord p.equation p.generates, by
    rw [fermatSpecMap_toSpec (k := ℤ)]
    change Spec.map (𝟙 (CommRingCat.of ℤ)) = 𝟙 _
    simp⟩

private noncomputable abbrev indexCoord (i : Fin 3) : FermatCoordinateRing ℤ n :=
  Ideal.Quotient.mk (fermatIdeal ℤ n) (MvPolynomial.X i)

private theorem exists_normalized_fermatRationalPoint (s : Spec (.of ℚ) ⟶ fermatProjective ℤ n) :
    ∃ (i : Fin 3) (q : Fin 3 → ℚ) (hqF : q 0 ^ n + q 1 ^ n = q 2 ^ n)
      (hq : Ideal.span (Set.range q) = ⊤), q i = 1 ∧ fermatSpecMap (k := ℤ) q hqF hq = s := by
  let x : Spec (.of ℚ) := default
  have hcov : s x ∈ ⨆ j : Fin 3, Proj.basicOpen (fermatGrading ℤ n) (indexCoord j) := by
    rw [fermatProjective_iSup_basicOpen ℤ n]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  let t : FermatCoordinateRing ℤ n := indexCoord i
  have ht : t ∈ fermatGrading ℤ n 1 := fermatCoord_mem_degree_one i
  let j := Proj.awayι (fermatGrading ℤ n) t ht one_pos
  have hrange : Set.range s ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y x]
    change s x ∈ j.opensRange
    rw [Proj.opensRange_awayι]
    exact hi
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift j s hrange)
  let ρ := ψ.hom.comp (normalizeChart (fermatGrading ℤ n) ht)
  have hρt : ρ t = 1 := by simp [ρ]
  let ρA : FermatCoordinateRing ℤ n →ₐ[ℤ] ℚ :=
    { ρ with
      commutes' := by
        intro r
        change ρ (r : FermatCoordinateRing ℤ n) = (r : ℚ)
        rw [map_intCast] }
  let q (a : Fin 3) : ℚ := ρ (indexCoord a)
  have hqi : q i = 1 := hρt
  have hq : Ideal.span (Set.range q) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (hqi ▸ isUnit_one)
  have heval : ρA.comp (Ideal.Quotient.mkₐ ℤ (fermatIdeal ℤ n)) =
      MvPolynomial.aeval q := by
    ext i
    change q i = MvPolynomial.aeval q (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X]
  have hqF : q 0 ^ n + q 1 ^ n = q 2 ^ n := by
    apply (aeval_fermatEquation_eq_zero_iff_coordinates (k := ℤ) n q).mp
    rw [← heval, AlgHom.comp_apply]
    change ρ (Ideal.Quotient.mk _ (fermatEquation ℤ n)) = 0
    have hz : Ideal.Quotient.mk (fermatIdeal ℤ n) (fermatEquation ℤ n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hz, map_zero]
  have hρ : (fermatCoordinateEval (k := ℤ) q hqF).toRingHom = ρ := by
    apply RingHom.ext
    intro a
    obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective a
    change fermatCoordinateEval (k := ℤ) q hqF (Ideal.Quotient.mk _ A) = _
    rw [fermatCoordinateEval_mk (k := ℤ), ← heval]
    rfl
  refine ⟨i, q, hqF, hq, hqi, ?_⟩
  rw [fermatSpecMap_eq_awayLift (k := ℤ) q hqF hq i (hqi ▸ isUnit_one)]
  simp_rw [hρ]
  change Spec.map (CommRingCat.ofHom
    (Away.lift (fermatGrading ℤ n) (ψ.hom.comp (normalizeChart (fermatGrading ℤ n) ht)) _)) ≫ j = s
  rw [normalizeChart_lift, CommRingCat.ofHom_hom, hψ]
  exact IsOpenImmersion.lift_fac j s hrange

private theorem exists_primitive_fermatCoordinates (q : Fin 3 → ℚ) (i : Fin 3) (hi : q i = 1)
    (hqF : q 0 ^ n + q 1 ^ n = q 2 ^ n) :
    ∃ (p : PrimitiveIntegerFermatCoordinates n) (c : ℚˣ), ∀ j, (p.coord j : ℚ) = c * q j := by
  obtain ⟨a, b, c, hb, hc, u, v, w, hbezout⟩ :=
    Rat.exists_primitive_common_denominator (q (i.succAbove 0)) (q (i.succAbove 1))
  let p : Fin 3 → ℤ := i.insertNth a (![b, c] : Fin 2 → ℤ)
  have ha : a ≠ 0 := by
    intro ha
    have hb' : b = 0 := by exact_mod_cast (by simpa [ha] using hb.symm : (b : ℚ) = 0)
    have hc' : c = 0 := by exact_mod_cast (by simpa [ha] using hc.symm : (c : ℚ) = 0)
    simp [ha, hb', hc'] at hbezout
  have hscale : ∀ j, (p j : ℚ) = (a : ℚ) * q j := by
    intro j
    induction j using i.succAboveCases with
    | x => simp [p, hi]
    | p j =>
      rw [show p (i.succAbove j) = (![b, c] : Fin 2 → ℤ) j from Fin.insertNth_apply_succAbove ..]
      fin_cases j
      · exact hb.symm
      · exact hc.symm
  have hF : p 0 ^ n + p 1 ^ n = p 2 ^ n := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    simp only [hscale, mul_pow, ← mul_add, hqF]
  have hp : Ideal.span (Set.range p) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hbezout]
    apply Ideal.add_mem _ (Ideal.add_mem _ _ _) _
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, Fin.insertNth_apply_same ..⟩)
    · exact Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨i.succAbove 0, Fin.insertNth_apply_succAbove ..⟩)
    · exact Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨i.succAbove 1, Fin.insertNth_apply_succAbove ..⟩)
  exact ⟨⟨p, hF, hp⟩, Units.mk0 a (Int.cast_ne_zero.mpr ha), hscale⟩

private theorem span_range_cast_eq_top {p : Fin 3 → ℤ} (hp : Ideal.span (Set.range p) = ⊤) :
    Ideal.span (Set.range fun i ↦ (p i : ℚ)) = ⊤ := by
  change Ideal.span (Set.range (algebraMap ℤ ℚ ∘ p)) = ⊤
  rw [Set.range_comp, ← Ideal.map_span, hp, Ideal.map_top]

private noncomputable abbrev intGenericPoint : Spec (.of ℚ) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))

private instance : IsDominant intGenericPoint := by
  constructor
  change DenseRange (PrimeSpectrum.comap (algebraMap ℤ ℚ))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).mp (Int.cast_injective (α := ℚ))]
  exact bot_le

private theorem restrict_fermatSection (p : PrimitiveIntegerFermatCoordinates n) :
    intGenericPoint ≫ p.toSection.1 = fermatSpecMap (k := ℤ) (fun i ↦ (p.coord i : ℚ))
      (by exact_mod_cast p.equation) (span_range_cast_eq_top p.generates) :=
  fermatSpecMap_comp_SpecMap (k := ℤ) (Algebra.ofId ℤ ℚ) p.coord p.equation p.generates _ _

/-- Every integral section arises from a primitive tuple of integer coordinates. -/
theorem primitiveIntegerFermatCoordinates_toSection_surjective :
    Function.Surjective (PrimitiveIntegerFermatCoordinates.toSection (n := n)) := by
  intro s
  obtain ⟨i, q, hqF, hq, hqi, hs⟩ := exists_normalized_fermatRationalPoint (intGenericPoint ≫ s.1)
  obtain ⟨p, c, hc⟩ := exists_primitive_fermatCoordinates q i hqi hqF
  refine ⟨p, Subtype.ext ?_⟩
  apply ext_of_isDominant_of_isSeparated (fermatProjectiveToSpec ℤ n)
    (p.toSection.2.trans s.2.symm) intGenericPoint
  rw [restrict_fermatSection, ← hs]
  exact (fermatSpecMap_eq_of_unit_rescale (k := ℤ) q _ hqF hq _ _ c hc).symm

private theorem cast_proportional_primitive_is_int {p q : Fin 3 → ℤ}
    (hp : Ideal.span (Set.range p) = ⊤) (c : ℚ)
    (hc : ∀ i, (q i : ℚ) = c * (p i : ℚ)) : ∃ a : ℤ, (a : ℚ) = c := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hp)
  refine ⟨∑ i, z i * q i, ?_⟩
  have hzQ : (∑ i, (z i : ℚ) * (p i : ℚ)) = 1 := by exact_mod_cast hz
  push_cast
  simp_rw [hc, mul_left_comm (↑(z _) : ℚ) c, ← Finset.mul_sum, hzQ, mul_one]

private theorem cast_proportional_primitive_eq_unit {p q : Fin 3 → ℤ}
    (hp : Ideal.span (Set.range p) = ⊤) (hq : Ideal.span (Set.range q) = ⊤)
    (c : ℚˣ) (hc : ∀ i, (q i : ℚ) = c * (p i : ℚ)) :
    ∃ u : ℤˣ, ∀ i, q i = u * p i := by
  obtain ⟨a, ha⟩ := cast_proportional_primitive_is_int hp (c : ℚ) hc
  have hc' : ∀ i, (p i : ℚ) = (↑c⁻¹ : ℚ) * (q i : ℚ) := by
    intro i
    rw [hc, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨b, hb⟩ := cast_proportional_primitive_is_int hq (↑c⁻¹ : ℚ) hc'
  have hab : a * b = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, ha, hb, Units.mul_inv, Int.cast_one]
  refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, fun i ↦ ?_⟩
  change q i = a * p i
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, ha, hc]

open HomogeneousLocalization in
private theorem fermatRationalPoint_eq_implies_unit_rescale (p q : Fin 3 → ℚ)
    (hFp : p 0 ^ n + p 1 ^ n = p 2 ^ n) (hp : Ideal.span (Set.range p) = ⊤)
    (hFq : q 0 ^ n + q 1 ^ n = q 2 ^ n) (hq : Ideal.span (Set.range q) = ⊤)
    (h : fermatSpecMap (k := ℤ) p hFp hp = fermatSpecMap (k := ℤ) q hFq hq) :
    ∃ c : ℚˣ, ∀ i, q i = c * p i := by
  have hpi : ∃ i, p i ≠ 0 := by
    by_contra! hpi
    have hzero : Ideal.span (Set.range p) ≤ (⊥ : Ideal ℚ) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp [hpi]
    rw [hp] at hzero
    exact top_ne_bot (le_antisymm hzero bot_le)
  obtain ⟨i, hi⟩ := hpi
  have hpiu := isUnit_iff_ne_zero.mpr hi
  have hqi : IsUnit (q i) := by
    apply isUnit_iff_ne_zero.mpr
    intro hqi
    have hpopen := fermatSpecMap_preimage_basicOpen (k := ℤ) p hFp hp i
    rw [h] at hpopen
    have hpre := hpopen.symm.trans (fermatSpecMap_preimage_basicOpen (k := ℤ) q hFq hq i)
    rw [(Spec (.of ℚ)).basicOpen_of_isUnit (hpiu.map (Scheme.ΓSpecIso (.of ℚ)).inv.hom)] at hpre
    change (⊤ : (Spec (.of ℚ)).Opens) =
      (Spec (.of ℚ)).basicOpen ((Scheme.ΓSpecIso (.of ℚ)).inv.hom (q i)) at hpre
    rw [hqi, map_zero, Scheme.basicOpen_zero] at hpre
    exact top_ne_bot hpre
  rw [fermatSpecMap_eq_awayLift (k := ℤ) p hFp hp i hpiu,
    fermatSpecMap_eq_awayLift (k := ℤ) q hFq hq i hqi] at h
  obtain ⟨c, hc⟩ := (Proj.SpecMap_awayLift_awayι_eq_iff _ _
    (fermatCoord_mem_degree_one (k := ℤ) (n := n) i) _ _).mp h
  refine ⟨c, fun j ↦ ?_⟩
  specialize hc 1 _ (fermatCoord_mem_degree_one j)
  change fermatCoordinateEval (k := ℤ) q hFq (Ideal.Quotient.mk _ (MvPolynomial.X j)) =
    (c : ℚ) ^ 1 * fermatCoordinateEval (k := ℤ) p hFp (Ideal.Quotient.mk _ (MvPolynomial.X j)) at hc
  simpa only [fermatCoordinateEval_mk (k := ℤ), MvPolynomial.aeval_X, pow_one] using hc

/-- Two primitive integral solutions are equivalent when their coordinates differ by
multiplication by one common integer unit, which is necessarily 1 or -1. -/
def primitiveIntegerFermatCoordinateSetoid (n : ℕ) :
    Setoid (PrimitiveIntegerFermatCoordinates n) where
  r p q := ∃ u : ℤˣ, ∀ i, q.coord i = u * p.coord i
  iseqv := ⟨fun p ↦ ⟨1, by simp⟩, by
      rintro p q ⟨u, hu⟩
      exact ⟨u⁻¹, fun i ↦ by rw [hu, ← mul_assoc, Units.inv_mul, one_mul]⟩,
    by
      rintro p q r ⟨u, hu⟩ ⟨v, hv⟩
      exact ⟨v * u, fun i ↦ by rw [hv, hu, ← mul_assoc, Units.val_mul]⟩⟩

/-- The only allowed common rescalings over the integers are the two signs. -/
theorem primitiveIntegerFermatCoordinateSetoid_iff (p q : PrimitiveIntegerFermatCoordinates n) :
    (primitiveIntegerFermatCoordinateSetoid n).r p q ↔ q.coord = p.coord ∨ q.coord = -p.coord := by
  change (∃ u : ℤˣ, ∀ i, q.coord i = u * p.coord i) ↔ _
  constructor
  · rintro ⟨u, hu⟩
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact Or.inl (funext fun i ↦ by simpa using hu i)
    · exact Or.inr (funext fun i ↦ by simpa using hu i)
  · rintro (h | h)
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩

/-- Two primitive tuples define equal sections exactly when they differ by common sign. -/
theorem primitiveIntegerFermatCoordinates_toSection_eq_iff
    (p q : PrimitiveIntegerFermatCoordinates n) :
    p.toSection = q.toSection ↔ (primitiveIntegerFermatCoordinateSetoid n).r p q := by
  constructor
  · intro h
    have hQ := congrArg (fun t : IntegralFermatSections n ↦ intGenericPoint ≫ t.1) h
    rw [restrict_fermatSection, restrict_fermatSection] at hQ
    obtain ⟨c, hc⟩ := fermatRationalPoint_eq_implies_unit_rescale _ _ _ _ _ _ hQ
    exact cast_proportional_primitive_eq_unit p.generates q.generates c hc
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    exact fermatSpecMap_eq_of_unit_rescale (k := ℤ) p.coord q.coord p.equation p.generates
      q.equation q.generates c hc

/-- Sections of the integral Fermat scheme are primitive integer solutions
up to simultaneous sign. Coordinates may vanish. -/
noncomputable def integralFermatSectionsEquiv (n : ℕ) :
    Quotient (primitiveIntegerFermatCoordinateSetoid n) ≃ IntegralFermatSections n :=
  Equiv.ofBijective
    (Quotient.lift (fun p : PrimitiveIntegerFermatCoordinates n ↦ p.toSection)
      (fun p q h ↦ (primitiveIntegerFermatCoordinates_toSection_eq_iff p q).mpr h)) <| by
    constructor
    · intro p q
      refine Quotient.inductionOn₂ p q ?_
      intro p q h
      exact Quotient.sound ((primitiveIntegerFermatCoordinates_toSection_eq_iff p q).mp h)
    · intro s
      obtain ⟨p, hp⟩ := primitiveIntegerFermatCoordinates_toSection_surjective s
      exact ⟨Quotient.mk _ p, hp⟩

/-- The equivalence sends a primitive tuple to its homogeneous-coordinate section. -/
@[simp] theorem integralFermatSectionsEquiv_apply (p : PrimitiveIntegerFermatCoordinates n) :
    integralFermatSectionsEquiv n (Quotient.mk _ p) = p.toSection := by
  unfold integralFermatSectionsEquiv
  rfl

/-- The integral section represented by `[1:0:1]` has no primitive presentation
whose second coordinate is nonzero. -/
theorem exists_integralFermatSection_only_zero_secondCoordinate {n : ℕ} (hn : 0 < n) :
    ∃ s : IntegralFermatSections n,
      ∀ p : PrimitiveIntegerFermatCoordinates n, p.toSection = s → p.coord 1 = 0 := by
  let t : PrimitiveIntegerFermatCoordinates n :=
    { coord := ![1, 0, 1]
      equation := by
        change (1 : ℤ) ^ n + 0 ^ n = 1 ^ n
        rw [zero_pow hn.ne', add_zero]
      generates := by
        rw [Ideal.eq_top_iff_one]
        exact Ideal.subset_span ⟨0, rfl⟩ }
  refine ⟨t.toSection, fun p hp ↦ ?_⟩
  have h := (primitiveIntegerFermatCoordinates_toSection_eq_iff t p).mp hp.symm
  rcases (primitiveIntegerFermatCoordinateSetoid_iff t p).mp h with h | h
  · simpa [t] using congrFun h 1
  · simpa [t] using congrFun h 1

end TinyTauDemo
