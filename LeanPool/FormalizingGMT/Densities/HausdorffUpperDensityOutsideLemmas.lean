/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic

/- Necessary basic definitions -/
public import LeanPool.FormalizingGMT.RadonMeasures.HausdorffMeasure
public import LeanPool.FormalizingGMT.Densities.Basic


/-!
# Technical lemmas for density bounds outside a set

This file contains the definitions and technical lemmas used in the proof of
`hausdorffMeasure_upperDensity_eq_zero_ae_notMem` (see
`FormalizingGMT/Densities/HausdorffUpperDensityOutside.lean`):

* the abbreviations `hsOuter` and `hsRestrict` and the sets `aSet s E t`,
* the inner approximation of `E` by closed sets (`approx_by_closed_inside`),
* the fine covers and the Vitali covering at each scale (`vitali_cover_at_scale`),
* the bound of the Hausdorff measure by scale covers (`hausdorffMeasure_le_of_scale_covers`),
* the key estimate `A_t_null`: `H^s(A_t) = 0` for every `0 < t < ∞`.
-/

@[expose] public section

open MeasureTheory Measure Metric Set Filter ENNReal
open scoped NNReal Topology



/-! ## Abbreviations -/

variable {X : Type*} [MetricSpace X]
  [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- The s-dimensional Hausdorff outer measure. -/
noncomputable abbrev hsOuter (s : ℝ) : OuterMeasure X :=
  OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ s)

/-- The s-dimensional Hausdorff outer measure restricted to E (Step a: µ = Hs|_E). -/
noncomputable abbrev hsRestrict (s : ℝ) (E : Set X) : OuterMeasure X :=
  OuterMeasure.restrict E (hsOuter s)

/-! ## aSet definition (Step c) -/

/-- The set A_t: points outside E where the upper s-density of H^s|_E exceeds t. -/
def aSet (s : ℝ) (E : Set X) (t : ℝ≥0∞) : Set X :=
  {x ∈ Eᶜ | dimensionalUpperDensity (hsRestrict s E) s x > t}

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
lemma A_set_subset_compl {s : ℝ} {E : Set X} {t : ℝ≥0∞} :
    aSet s E t ⊆ Eᶜ :=
  fun _ hx => hx.1

/-! ## Hausdorff measure equals outer measure -/

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma hausdorff_measure_eq_outer (s : ℝ) (S : Set X) :
    μH[s] S = (hsOuter (X := X) s) S := by
  change (MeasureTheory.Measure.hausdorffMeasure s).toOuterMeasure S = _
  rw [MeasureTheory.Measure.hausdorffMeasure,
    MeasureTheory.Measure.mkMetric_toOuterMeasure]

/-! ## Step (e): Inner approximation by closed sets -/

/-- Under the assumptions of Theorem 2.6, given ε > 0, there exists a closed set K ⊆ E
    such that Hs(E \ K) < ε.

The argument is carried out at the level of the *measure* `μH[s]` rather than of the outer
measure: `X` carries the Borel σ-algebra (`BorelSpace X`), which is the σ-algebra with respect to
which the `s`-dimensional Hausdorff measure is defined, and `μH[s]`, viewed as an outer measure,
agrees with `hsOuter s` on every set (`hausdorff_measure_eq_outer`).  The inner approximation is
then `closed_approx_of_isBorelRegular`, whose proof is an application of
`BorelRegularOuterMeasure.restrict_isRadon` (regularity of the restriction of a measure to a set
of finite measure).  This is why the ambient space is assumed here to be locally compact and
second countable, the hypotheses of that theorem.

The hypothesis `0 ≤ s` is part of the standard statement and is kept, but the proof does not
need it. -/
lemma approx_by_closed_inside
    {s : ℝ} (_hs : 0 ≤ s) {E : Set X}
    (hE_meas : MeasurableSet[(hsOuter (X := X) s).caratheodory] E)
    (hE_fin : (hsOuter (X := X) s) E < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set X, IsClosed K ∧ K ⊆ E ∧ (hsOuter s) (E \ K) < ε := by
  -- The Hausdorff measure, viewed as an outer measure, is exactly `hsOuter s`.
  have hOM : ∀ S : Set X, (μH[s] : Measure X).toOuterMeasure S = (hsOuter (X := X) s) S :=
    fun S => hausdorff_measure_eq_outer s S
  -- Hence `E` is Carathéodory measurable for `μH[s]` and has finite `μH[s]`-measure.
  have hE_cara : (μH[s] : Measure X).toOuterMeasure.IsCaratheodory E := by
    intro t
    simpa only [hOM] using hE_meas t
  have hE_fin' : μH[s] E < ∞ := by
    rw [show μH[s] E = (μH[s] : Measure X).toOuterMeasure E from rfl, hOM]
    exact hE_fin
  obtain ⟨K, hK_closed, hK_sub, hK_lt⟩ :=
    closed_approx_of_isBorelRegular (μH[s] : Measure X) E hE_cara hE_fin' ε hε
  refine ⟨K, hK_closed, hK_sub, ?_⟩
  rw [← hOM (E \ K)]
  exact hK_lt

/-! ## Step (g): A_t ⊆ U = X \ K -/

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
/-- A_t ⊆ X \ K whenever K ⊆ E, since A_t ⊆ X \ E ⊆ X \ K. (Step g) -/
lemma A_subset_compl_K {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {K : Set X} (hK : K ⊆ E) :
    aSet s E t ⊆ Kᶜ :=
  fun x hx => mt (@hK x) (A_set_subset_compl hx)

/-! ## Step (j): Fine cover for points in A_t -/

/-
For x ∈ A_t, there are arbitrarily small balls where the density exceeds t.
-/
omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
lemma fine_cover_of_mem_A_set
    {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {x : X} (hx : x ∈ aSet s E t) :
    ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
      (hsRestrict s E) (closedBall x ρ) >
        t * ENNReal.ofReal ((2 * ρ) ^ s) := by
  intro δ δ_pos;
  -- By contradiction, assume there's no such ρ.
  by_contra h_contra;
  convert hx.2.not_ge ?_ using 1
  generalize_proofs at *
  apply csInf_le
  · norm_num
  · norm_num
    filter_upwards [Ioo_mem_nhdsGT δ_pos] with ρ hρ using by
      rw [dimensional_density_ratio_closedBall _ _ _ hρ.1.le]
      exact ENNReal.div_le_of_le_mul <| by aesop

/-
For x ∈ A_t ⊆ U (open), we can also ensure B(x, ρ) ⊆ U. (Steps i-j)
-/
omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
lemma fine_cover_in_open
    {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {x : X} (hx : x ∈ aSet s E t)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
      closedBall x ρ ⊆ U ∧
      (hsRestrict s E) (closedBall x ρ) >
        t * ENNReal.ofReal ((2 * ρ) ^ s) := by
  obtain ⟨ δ₁, hδ₁, hδ₁' ⟩ := Metric.mem_nhds_iff.1 ( hU.mem_nhds hxU );
  intro δ hδ_pos
  obtain ⟨ ρ, hρ₁, hρ₂ ⟩ := fine_cover_of_mem_A_set hx (Min.min δ₁ δ) (lt_min hδ₁ hδ_pos)
  use ρ
  simp only [mem_Ioo, OuterMeasure.restrict_apply, gt_iff_lt]
  exact ⟨⟨hρ₁.1, hρ₁.2.trans_le (min_le_right _ _)⟩, fun y hy =>
    hδ₁' <| Metric.mem_ball.2 <| lt_of_le_of_lt (Metric.mem_closedBall.1 hy) <|
      hρ₁.2.trans_le (min_le_left _ _), by simpa [hsRestrict] using hρ₂⟩

/-! ## Countability of pairwise disjoint balls -/

/-
Pairwise disjoint closed balls with positive radii are countable in a locally compact,
second countable metric space.
-/
omit [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma countable_of_pairwise_disjoint_balls
    {ι : Type*} {s : Set ι} {x : ι → X} {r : ι → ℝ}
    (hr_pos : ∀ i ∈ s, 0 < r i)
    (hpd : s.PairwiseDisjoint (fun i => closedBall (x i) (r i))) :
    s.Countable := by
  have h_countable : Set.Countable (Set.image (fun i => closedBall (x i) (r i)) s) := by
    have h_countable : Set.Countable {B : Set X | ∃ i ∈ s, B = closedBall (x i) (r i)} := by
      have h_disjoint : Set.PairwiseDisjoint
          {B : Set X | ∃ i ∈ s, B = closedBall (x i) (r i)} (fun B => interior B) := by
        intro B hB C hC hBC;
        obtain ⟨i, hi, rfl⟩ := hB
        obtain ⟨j, hj, rfl⟩ := hC
        exact Disjoint.mono interior_subset interior_subset (hpd hi hj (by aesop))
      convert Set.PairwiseDisjoint.countable_of_nonempty_interior h_disjoint _;
      simp only [mem_ofPred_eq, interior_interior, forall_exists_index, and_imp]
      exact fun B i hi hB => hB.symm ▸
        ⟨x i, mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds _ (hr_pos i hi))⟩
    exact h_countable.mono fun B hB => by obtain ⟨ i, hi, rfl ⟩ := hB; exact ⟨ i, hi, rfl ⟩ ;
  have h_inj : Set.InjOn (fun i => closedBall (x i) (r i)) s := by
    intro i hi j hj hij
    by_contra hne
    have hdisj := hpd hi hj hne
    change Disjoint (closedBall (x i) (r i)) (closedBall (x j) (r j)) at hdisj
    rw [Set.disjoint_left] at hdisj
    have hxj : x j ∈ closedBall (x j) (r j) := by
      exact Metric.mem_closedBall.mpr (by simpa using (hr_pos j hj).le)
    exact hdisj (by simpa only [hij] using hxj) hxj
  exact countable_of_injective_of_countable_image h_inj h_countable

/-! ## Steps (k)-(l): Vitali covering and gauge bound -/

/-
At each scale k, construct a cover of A_t using the Vitali covering lemma.
    The covering gives balls of radius < 1/(k+1) with gauge sum ≤ 5^s/t · Hs(E\K).
    Steps (k)-(l) of the PDF proof.
-/
/-- Factor out 5^s from the gauge: (2 * (5 * ρ))^s = 5^s * (2 * ρ)^s -/
lemma gauge_factor_five (s : ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ENNReal.ofReal ((2 * (5 * ρ)) ^ s) =
    ENNReal.ofReal ((5 : ℝ) ^ s) * ENNReal.ofReal ((2 * ρ) ^ s) := by
  rw [← ENNReal.ofReal_mul (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity), mul_comm]
  ring_nf

/-- From the density condition t * a < b, derive a ≤ t⁻¹ * b. -/
lemma density_bound_inv {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤)
    {a b : ℝ≥0∞} (h : t * a < b) :
    a ≤ t⁻¹ * b := by
  rw [ ← ENNReal.mul_le_mul_iff_right ( show t ≠ 0 by exact ne_of_gt ht ) ( by aesop ) ];
  rw [ ← mul_assoc, ENNReal.mul_inv_cancel ht.ne' ht_top, one_mul ] ; exact le_of_lt h

/-  Helper: for pairwise disjoint balls in Kᶜ with density > t,
    the tsum of hsRestrict values is bounded by Hs(E \ K). -/
omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tsum_restrict_le_of_disjoint (s : ℝ)
    {E : Set X}
    (_hE_car : MeasurableSet[(hsOuter (X := X) s).caratheodory] E)
    {K : Set X} (_hK_sub : K ⊆ E)
    {u : Set X} (hu_count : u.Countable)
    (ρ : X → ℝ)
    (_hρ_pos : ∀ x ∈ u, 0 < ρ x)
    (hρ_ball : ∀ x ∈ u, closedBall x (ρ x) ⊆ Kᶜ)
    (hρ_disj : u.PairwiseDisjoint (fun x => closedBall x (ρ x))) :
    ∑' x : u, (hsOuter s) (E ∩ closedBall (↑x) (ρ ↑x)) ≤ (hsOuter s) (E \ K) := by
  have _ := hu_count.to_subtype
  -- Apply the measure_iUnion theorem for the restricted measure.
  have h_measure_iUnion :
      (MeasureTheory.Measure.restrict (MeasureTheory.Measure.hausdorffMeasure s) E)
        (⋃ x : u, closedBall (x : X) (ρ x)) =
      ∑' x : u, (MeasureTheory.Measure.restrict
        (MeasureTheory.Measure.hausdorffMeasure s) E) (closedBall (x : X) (ρ x)) := by
    rw [ MeasureTheory.measure_iUnion ];
    · exact fun x y hxy => hρ_disj x.2 y.2 ( Subtype.coe_injective.ne hxy );
    · exact fun x => measurableSet_closedBall;
  calc
    ∑' x : u, (hsOuter s) (E ∩ closedBall (x : X) (ρ x)) =
        ∑' x : u, (MeasureTheory.Measure.restrict
          (MeasureTheory.Measure.hausdorffMeasure s) E) (closedBall (x : X) (ρ x)) := by
      apply tsum_congr
      intro x
      rw [MeasureTheory.Measure.restrict_apply measurableSet_closedBall,
        Set.inter_comm, hausdorff_measure_eq_outer]
    _ = (MeasureTheory.Measure.restrict
          (MeasureTheory.Measure.hausdorffMeasure s) E)
          (⋃ x : u, closedBall (x : X) (ρ x)) := h_measure_iUnion.symm
    _ = MeasureTheory.Measure.hausdorffMeasure s
          ((⋃ x : u, closedBall (x : X) (ρ x)) ∩ E) := by
      rw [MeasureTheory.Measure.restrict_apply]
      exact MeasurableSet.iUnion fun x => measurableSet_closedBall
    _ ≤ MeasureTheory.Measure.hausdorffMeasure s (E \ K) := by
      apply MeasureTheory.measure_mono
      intro z hz
      refine ⟨hz.2, ?_⟩
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hz.1
      exact hρ_ball x x.2 hx
    _ = (hsOuter s) (E \ K) := hausdorff_measure_eq_outer s (E \ K)

omit [LocallyCompactSpace X] in
lemma vitali_cover_at_scale (s : ℝ) (_hs : 0 ≤ s)
    {E : Set X}
    (hE_meas : MeasurableSet[(hsOuter (X := X) s).caratheodory] E)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤)
    {K : Set X} (hK_closed : IsClosed K) (hK_sub : K ⊆ E)
    (k : ℕ) :
    ∃ (T : Set X) (_ : T.Countable) (r : X → ℝ),
      aSet s E t ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
      (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (↑k + 1))) ∧
      ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ s) ≤
        ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * (hsOuter s) (E \ K) := by
  -- Step 1: For each x ∈ aSet, choose ρ_x with density and ball-in-U properties
  have h_fine : ∀ x ∈ aSet s E t, ∃ ρ ∈ Ioo (0 : ℝ) (1 / (5 * ((k : ℝ) + 1))),
      closedBall x ρ ⊆ Kᶜ ∧
      (hsRestrict s E) (closedBall x ρ) > t * ENNReal.ofReal ((2 * ρ) ^ s) := by
    intro x hx
    exact fine_cover_in_open hx hK_closed.isOpen_compl
      (A_subset_compl_K hK_sub hx) _ (by positivity)
  choose! ρ hρ_range hρ_ball hρ_dens using h_fine
  -- Step 2: Apply Vitali covering theorem with τ = 5
  obtain ⟨u, hu_sub, hu_disj, hu_cover⟩ :=
    @Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall X X _
      (aSet s E t) id ρ (1 / (5 * ((k : ℝ) + 1)))
      (fun a ha => le_of_lt (hρ_range a ha).2) 5 (by norm_num : (3 : ℝ) < 5)
  -- Step 3: u is countable
  have hu_count : u.Countable :=
    countable_of_pairwise_disjoint_balls (fun x hx => (hρ_range x (hu_sub hx)).1) hu_disj
  -- Step 4: Output T = u, r = 5 * ρ
  refine ⟨u, hu_count, fun x => 5 * ρ x, ?_, ?_, ?_⟩
  -- Coverage: aSet ⊆ ⋃_{x∈u} B(x, 5ρ_x)
  · intro x hx
    obtain ⟨y, hy_mem, hy_sub⟩ := hu_cover x hx
    exact mem_iUnion₂.2 ⟨y, hy_mem, hy_sub (mem_closedBall_self (hρ_range x hx).1.le)⟩
  -- Radius bounds: 5ρ_x ∈ Ioo(0, 1/(k+1))
  · intro x hx
    have hρx := hρ_range x (hu_sub hx)
    exact ⟨mul_pos (by norm_num : (0:ℝ) < 5) hρx.1,
           calc 5 * ρ x < 5 * (1 / (5 * ((k : ℝ) + 1))) :=
                    mul_lt_mul_of_pos_left hρx.2 (by norm_num)
                _ = 1 / ((k : ℝ) + 1) := by field_simp⟩
  -- Gauge sum bound: ∑ (2·5ρ)^s ≤ 5^s · t⁻¹ · Hs(E\K)
  · -- Factor out 5^s
    have h_factor : ∀ x : u, ENNReal.ofReal ((2 * (5 * ρ ↑x)) ^ s) =
        ENNReal.ofReal ((5 : ℝ) ^ s) * ENNReal.ofReal ((2 * ρ ↑x) ^ s) := by
      intro x; exact gauge_factor_five s (ρ ↑x) (hρ_range ↑x (hu_sub x.2)).1
    simp_rw [h_factor]
    rw [ENNReal.tsum_mul_left]
    -- Bound ∑ (2ρ)^s ≤ t⁻¹ · ∑ Hs|_E(B(x,ρ))
    have h_dens_bound : ∑' x : u, ENNReal.ofReal ((2 * ρ ↑x) ^ s) ≤
        t⁻¹ * ∑' x : u, (hsOuter s) (E ∩ closedBall (↑x) (ρ ↑x)) := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun x =>
        density_bound_inv ht ht_top (by
          have := hρ_dens ↑x (hu_sub x.2)
          simp only [hsRestrict, OuterMeasure.restrict_apply, Set.inter_comm] at this
          exact this)
    -- Bound ∑ Hs(E ∩ B) ≤ Hs(E\K)
    have h_disj_bound : ∑' x : u, (hsOuter s) (E ∩ closedBall (↑x) (ρ ↑x)) ≤
        (hsOuter s) (E \ K) := by
      exact tsum_restrict_le_of_disjoint s hE_meas hK_sub hu_count ρ
        (fun x hx => (hρ_range x (hu_sub hx)).1) (fun x hx => hρ_ball x (hu_sub hx)) hu_disj
    -- Combine
    calc ENNReal.ofReal ((5 : ℝ) ^ s) * ∑' x : u, ENNReal.ofReal ((2 * ρ ↑x) ^ s)
        ≤ ENNReal.ofReal ((5 : ℝ) ^ s) *
          (t⁻¹ * ∑' x : u, (hsOuter s) (E ∩ closedBall (↑x) (ρ ↑x))) :=
          mul_le_mul_right h_dens_bound _
      _ ≤ ENNReal.ofReal ((5 : ℝ) ^ s) * (t⁻¹ * (hsOuter s) (E \ K)) :=
          mul_le_mul_right (mul_le_mul_right h_disj_bound _) _
      _ = ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * (hsOuter s) (E \ K) := by ring

/-! ## Hausdorff measure bound from scale covers -/

/-
The Hausdorff measure of a set is bounded by gauge sums of scale-k covers.
-/
omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma hausdorffMeasure_le_of_scale_covers {d : ℝ} (hd : 0 ≤ d)
    {S : Set X} (bound : ℝ≥0∞)
    (h : ∀ k : ℕ,
      ∃ (T : Set X) (_ : T.Countable)
        (r : X → ℝ),
        S ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
        (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (↑k + 1))) ∧
        ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ d) ≤ bound) :
    μH[d] S ≤ bound := by
  choose T hT r hr₁ hr₂ hr₃ using h
  let C : ∀ k : ℕ, T k → Set X := fun k x => closedBall x (r k x)
  let scale : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (2 / (k + 1))
  have hcount : ∀ k, Countable (T k) := fun k => (hT k).to_subtype
  let _ (k : ℕ) : Countable (T k) := hcount k
  have h_inv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h_real : Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul h_inv
  have hscale : Tendsto scale atTop (𝓝 0) := by
    simpa only [scale, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h_real
  have hdiam : ∀ᶠ k in atTop, ∀ x : T k, ediam (C k x) ≤ scale k := by
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    intro x
    change ediam (C k x) ≤ ENNReal.ofReal (2 / ((k : ℝ) + 1))
    apply Metric.ediam_le_of_forall_dist_le
    intro y hy z hz
    calc
      dist y z ≤ 2 * r k x := le_trans (dist_triangle_right _ _ _)
        (by linarith [Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz])
      _ ≤ 2 / ((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using (hr₂ k x x.2).2.le) (by norm_num)
  have hcover : ∀ᶠ k in atTop, S ⊆ ⋃ x : T k, C k x := by
    exact Filter.Eventually.of_forall fun k => by simpa [C] using hr₁ k
  refine (hausdorffMeasure_le_liminf_tsum d S scale hscale C hdiam hcover).trans ?_
  apply Filter.liminf_le_of_frequently_le'
  exact Filter.Frequently.of_forall fun k => (ENNReal.tsum_le_tsum fun x => by
    have hed : ediam (C k x) ≤ ENNReal.ofReal (2 * r k x) := by
      refine ediam_le ?_
      intro y hy z hz
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal
        (by linarith [dist_triangle_right y z x, Metric.mem_closedBall.mp hy,
          Metric.mem_closedBall.mp hz])
    calc
      ediam (C k x) ^ d ≤ ENNReal.ofReal (2 * r k x) ^ d :=
        ENNReal.rpow_le_rpow hed hd
      _ = ENNReal.ofReal ((2 * r k x) ^ d) := by
        rw [ENNReal.ofReal_rpow_of_pos (mul_pos zero_lt_two (hr₂ k x x.2).1)])
    |>.trans (hr₃ k)

/-! ## Step (m): H^s(A_t) = 0 -/

/-
Core result: H^s(A_t) = 0. The proof fixes ε > 0, gets K from approx_by_closed_inside,
    applies vitali_cover_at_scale for each scale k, bounds μH[s](A_t) ≤ 5^s/t · ε,
    then lets ε → 0. (Step m)
-/
theorem A_t_null (s : ℝ) (hs : 0 ≤ s)
    {E : Set X}
    (hE_meas : MeasurableSet[(hsOuter (X := X) s).caratheodory] E)
    (hE_fin : (hsOuter (X := X) s) E < ⊤)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤) :
    μH[s] (aSet (X := X) s E t) = 0 := by
  apply le_antisymm
  · have h_bound : ∀ ε > 0, μH[s] (aSet s E t) ≤ ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * ε := by
      intro ε ε_pos
      obtain ⟨K, hK_closed, hK_sub, hK_fin⟩ :
          ∃ K : Set X, IsClosed K ∧ K ⊆ E ∧ (hsOuter s) (E \ K) < ε := by
        exact approx_by_closed_inside hs hE_meas hE_fin ε_pos
      apply hausdorffMeasure_le_of_scale_covers hs
      intro k
      obtain ⟨T, hT_countable, r, hT_cover, hT_radius, hT_gauge⟩ :=
        vitali_cover_at_scale s hs hE_meas ht ht_top hK_closed hK_sub k
      use T, hT_countable, r
      exact ⟨hT_cover, hT_radius, by
        exact hT_gauge.trans (mul_le_mul_right hK_fin.le _)⟩;
    -- Let ε → 0.
    have h_zero : Filter.Tendsto
        (fun ε : ℝ≥0∞ => ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hconst : ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr ht.ne')
      have hid : Tendsto (fun ε : ℝ≥0∞ => ε) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
        Filter.tendsto_id.mono_left inf_le_left
      simpa using ENNReal.Tendsto.const_mul hid (Or.inr hconst)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_zero
      (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_bound ε hε)
  · exact bot_le
