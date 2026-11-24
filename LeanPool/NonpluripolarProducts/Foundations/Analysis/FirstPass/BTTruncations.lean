/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LocalPshDiscControl

/-!
# Actual extended-real PSH truncations

Truncate before taking `toReal`: at a pole the representative is `-k`, not
`max 0 (-k)`. Strict superlevel loci are Borel; they need not be ordinary open
sets. No Bedford–Taylor existence or locality theorem is imported here.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ} {Ω : Opens (ComplexModel n)} {u : ComplexModel n → EReal}

/-- The maximum is taken in the extended reals, including at poles. -/
def truncation (u : ComplexModel n → EReal) (k : ℕ) (z : ComplexModel n) : EReal :=
  max (u z) ((-(k : ℝ) : ℝ) : EReal)

/-- The real representative of the already truncated potential. -/
def truncationReal (u : ComplexModel n → EReal) (k : ℕ) (z : ComplexModel n) : ℝ :=
  (truncation u k z).toReal

/-- The strict truncation locus inside the given domain. -/
def strictTruncationLocus (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) (k : ℕ) : Set (ComplexModel n) :=
  {z | z ∈ Ω ∧ ((-(k : ℝ) : ℝ) : EReal) < u z}

theorem truncation_lower_bound (u : ComplexModel n → EReal) (k : ℕ)
    (z : ComplexModel n) : ((-(k : ℝ) : ℝ) : EReal) ≤ truncation u k z :=
  le_max_right _ _

theorem truncation_ne_bot (u : ComplexModel n → EReal) (k : ℕ)
    (z : ComplexModel n) : truncation u k z ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe _).trans_le (truncation_lower_bound u k z))

theorem truncation_ne_top (hu : PlurisubharmonicOn u Ω) (k : ℕ)
    {z : ComplexModel n} (hz : z ∈ Ω) : truncation u k z ≠ ⊤ := by
  exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hu z hz).ne_top)
    (EReal.coe_lt_top _))

theorem coe_truncationReal (hu : PlurisubharmonicOn u Ω) (k : ℕ)
    {z : ComplexModel n} (hz : z ∈ Ω) :
    (truncationReal u k z : EReal) = truncation u k z :=
  EReal.coe_toReal (truncation_ne_top hu k hz) (truncation_ne_bot u k z)

theorem truncation_plurisubharmonicOn (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    PlurisubharmonicOn (truncation u k) Ω :=
  hu.max (fun z _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) z)

theorem truncationReal_plurisubharmonicOn (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    PlurisubharmonicOn (fun z => (truncationReal u k z : EReal)) Ω := by
  intro z hz
  apply (truncation_plurisubharmonicOn hu k z hz).congr
  filter_upwards [Ω.isOpen.mem_nhds hz] with w hw
  exact (coe_truncationReal hu k hw).symm

@[simp] theorem truncation_at_pole (k : ℕ) {z : ComplexModel n} (hz : u z = ⊥) :
    truncation u k z = ((-(k : ℝ) : ℝ) : EReal) := by
  simp [truncation, hz]

theorem truncationReal_at_pole (k : ℕ) {z : ComplexModel n} (hz : u z = ⊥) :
    truncationReal u k z = -(k : ℝ) := by
  unfold truncationReal
  rw [truncation_at_pole k hz]
  exact EReal.toReal_coe _

theorem truncation_eq_on_strictLocus (k : ℕ) :
    EqOn (truncation u k) u (strictTruncationLocus Ω u k) :=
  fun _ hz => max_eq_left hz.2.le

theorem truncationReal_eq_on_strictLocus (k : ℕ) :
    EqOn (truncationReal u k) (fun z => (u z).toReal)
      (strictTruncationLocus Ω u k) :=
  fun _ hz => congrArg EReal.toReal (truncation_eq_on_strictLocus k hz)

theorem pole_not_mem_strictLocus (k : ℕ) {z : ComplexModel n} (hz : u z = ⊥) :
    z ∉ strictTruncationLocus Ω u k := by
  simp [strictTruncationLocus, hz]

theorem truncation_antitone (u : ComplexModel n → EReal) (z : ComplexModel n) :
    Antitone (fun k => truncation u k z) := by
  intro k l hkl
  apply max_le_max le_rfl
  exact EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))

theorem truncationReal_antitone (hu : PlurisubharmonicOn u Ω)
    {z : ComplexModel n} (hz : z ∈ Ω) : Antitone (fun k => truncationReal u k z) := by
  intro k l hkl
  apply EReal.coe_le_coe_iff.mp
  rw [coe_truncationReal hu l hz, coe_truncationReal hu k hz]
  exact truncation_antitone u z hkl

theorem strictTruncationLocus_mono (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) : Monotone (strictTruncationLocus Ω u) := by
  intro k l hkl z hz
  refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2⟩
  exact EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))

theorem truncation_truncation (u : ComplexModel n → EReal) {k l : ℕ}
    (hkl : k ≤ l) : truncation (truncation u l) k = truncation u k := by
  funext z
  have h : ((-(l : ℝ) : ℝ) : EReal) ≤ ((-(k : ℝ) : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))
  simp only [truncation, max_assoc, max_eq_right h]

/-- Nested truncation, expressed in the finite real representatives on Ω. -/
theorem truncationReal_nested (hu : PlurisubharmonicOn u Ω) {k l : ℕ}
    (hkl : k ≤ l) {z : ComplexModel n} (hz : z ∈ Ω) :
    max (truncationReal u l z) (-(k : ℝ)) = truncationReal u k z := by
  apply EReal.coe_injective
  have hmax (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
    · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]
  rw [hmax, coe_truncationReal hu l hz, coe_truncationReal hu k hz]
  exact congrFun (truncation_truncation u hkl) z

theorem strictLocus_eq_truncationReal_superlevel (hu : PlurisubharmonicOn u Ω)
    {k l : ℕ} (hkl : k ≤ l) :
    strictTruncationLocus Ω u k = {z | z ∈ Ω ∧ -(k : ℝ) < truncationReal u l z} := by
  ext z
  by_cases hz : z ∈ Ω
  · have h : ((-(l : ℝ) : ℝ) : EReal) ≤ ((-(k : ℝ) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkl))
    simp only [strictTruncationLocus, mem_ofPred_eq, hz, true_and]
    rw [← EReal.coe_lt_coe_iff, coe_truncationReal hu l hz]
    simp only [truncation, lt_max_iff, not_lt.mpr h, or_false]
  · simp [strictTruncationLocus, hz]

/-- Actual ordinary upper semicontinuity supplies Borel measurability of a genuine relative strict
    superlevel. -/
theorem measurableSet_psh_superlevel {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) (c : ℝ) :
    MeasurableSet {z | z ∈ Ω ∧ (c : EReal) < u z} := by
  have hsc : UpperSemicontinuousOn (fun z : Ω => u z.val) univ :=
    hu.upperSemicontinuousOn.comp continuous_subtype_val.continuousOn
      (fun z _ => z.property)
  have hm : Measurable (fun z : Ω => u z.val) :=
    (upperSemicontinuousOn_univ_iff.mp hsc).measurable
  have hs := Ω.isOpen.measurableSet.subtype_image
    (hm measurableSet_Ioi : MeasurableSet {z : Ω | (c : EReal) < u z.val})
  convert hs using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩

/-- The strict truncation locus is Borel. -/
theorem measurableSet_strictTruncationLocus (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    MeasurableSet (strictTruncationLocus Ω u k) :=
  measurableSet_psh_superlevel hu (-(k : ℝ))

/-- Compact upper bounds and the truncation floor give local absolute bounds. -/
theorem truncationReal_isLocallyBoundedPshOn (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    IsLocallyBoundedPshOn Ω (truncationReal u k) := by
  refine ⟨truncationReal_plurisubharmonicOn hu k, ?_⟩
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Ω.isOpen.mem_nhds hz)
  have hclosed : closedBall z (r / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC0, hC⟩ := hu.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z (r / 2)) hclosed
  refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    ball_subset_closedBall.trans hclosed, C + (k : ℝ), ?_⟩
  intro w hw
  have hwΩ := hclosed (ball_subset_closedBall hw)
  have hlo : -(k : ℝ) ≤ truncationReal u k w := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_truncationReal hu k hwΩ]
    exact truncation_lower_bound u k w
  have hhi : truncationReal u k w ≤ C := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_truncationReal hu k hwΩ]
    exact max_le (hC w (ball_subset_closedBall hw))
      (EReal.coe_le_coe_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
  exact abs_le.mpr ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) k]⟩

/-- The strict levels exhaust precisely the domain outside the pole set.
This order-theoretic identity also holds for arbitrary extended-real functions. -/
theorem iUnion_strictTruncationLocus (Ω : Opens (ComplexModel n))
    (u : ComplexModel n → EReal) :
    (⋃ k, strictTruncationLocus Ω u k) = {z | z ∈ Ω ∧ u z ≠ ⊥} := by
  ext z
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz
    exact ⟨hk.1, ne_of_gt ((EReal.bot_lt_coe (-(k : ℝ))).trans hk.2)⟩
  · rintro ⟨hz, hu⟩
    obtain ⟨r, _, hr⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hu)
    obtain ⟨k, hk⟩ := exists_nat_gt (-r)
    refine mem_iUnion.mpr ⟨k, hz, ?_⟩
    exact (EReal.coe_lt_coe_iff.mpr (show -(k : ℝ) < r by linarith)).trans hr

end SGPT.Foundations.Analysis.FirstPass.MongeAmpere
