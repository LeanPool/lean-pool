/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.GluingTopology

/-!
# Extended-real local plurisubharmonic functions

The submean inequality is expressed by integrating the nonnegative deficit
`C - u` below a finite upper bound on a closed complex disc. Thus a pole is
never sent to `toReal`, and no difference of two infinite integrals occurs.
The raw disc condition is only used together with upper semicontinuity and
the exclusion of positive infinity. Identically negative infinity is allowed.
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The image of a closed complex disc under a complex affine line. -/
noncomputable def affineClosedDisc (x v : E) (r : ℝ) : Set E :=
  (fun z : ℂ => x + z • v) '' closedBall 0 r

/-- Angular integral of a nonnegative extended-real deficit. -/
noncomputable def circleDeficit (u : E → EReal) (x v : E) (r C : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (2 * Real.pi),
    ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal

/-- Disc submean inequalities, tested below every real upper bound on the disc. -/
def HasDiscSubmeanOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ (x v : E) (r : ℝ), 0 < r → affineClosedDisc x v r ⊆ U →
    ∀ C : ℝ, (∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) →
      circleDeficit u x v r C ≤
        ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal

/-- The complete disc criterion; its regularity fields prevent vacuous tests. -/
structure DiscPshOn (u : E → EReal) (U : Set E) : Prop where
  ne_top : ∀ x ∈ U, u x ≠ ⊤
  upperSemicontinuousOn : UpperSemicontinuousOn u U
  submean : HasDiscSubmeanOn u U

/-- A germ satisfying the extended-real plurisubharmonic disc criterion. -/
def PlurisubharmonicAt (u : E → EReal) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ DiscPshOn u U

/-- Plurisubharmonicity is a local property; the value `⊥` is permitted.
On a nonopen set this means ambient germs at its points, not an intrinsic
notion on an arbitrary closed subset. -/
def PlurisubharmonicOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ x ∈ U, PlurisubharmonicAt u x

theorem center_mem_affineClosedDisc (x v : E) {r : ℝ} (hr : 0 ≤ r) :
    x ∈ affineClosedDisc x v r := by
  refine ⟨0, ?_, by simp⟩
  simpa using hr

theorem circle_mem_affineClosedDisc (x v : E) {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    x + circleMap 0 r t • v ∈ affineClosedDisc x v r := by
  refine ⟨circleMap 0 r t, ?_, rfl⟩
  exact sphere_subset_closedBall (circleMap_mem_sphere 0 hr t)

theorem isCompact_affineClosedDisc (x v : E) (r : ℝ) :
    IsCompact (affineClosedDisc x v r) := by
  apply (isCompact_closedBall (0 : ℂ) r).image
  fun_prop

/-- Compact discs have finite upper bounds, including discs contained in poles. -/
theorem DiscPshOn.exists_disc_upper_bound {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) :
    ∃ C : ℝ, ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal) := by
  obtain ⟨y, hy, hmax⟩ := (hu.upperSemicontinuousOn.mono hD).exists_isMaxOn
    ⟨x, center_mem_affineClosedDisc x v hr⟩ (isCompact_affineClosedDisc x v r)
  obtain ⟨C, hC, _⟩ := EReal.exists_rat_btwn_of_lt (lt_top_iff_ne_top.mpr (hu.ne_top y (hD hy)))
  exact ⟨C, fun z hz => (hmax hz).trans hC.le⟩

theorem HasDiscSubmeanOn.mono {u : E → EReal} {U V : Set E}
    (hu : HasDiscSubmeanOn u U) (hVU : V ⊆ U) : HasDiscSubmeanOn u V := by
  intro x v r hr hD C hC
  exact hu x v r hr (hD.trans hVU) C hC

theorem DiscPshOn.mono {u : E → EReal} {U V : Set E}
    (hu : DiscPshOn u U) (hVU : V ⊆ U) : DiscPshOn u V :=
  ⟨fun x hx => hu.ne_top x (hVU hx), hu.upperSemicontinuousOn.mono hVU,
    hu.submean.mono hVU⟩

/-- Larger potentials have smaller deficits, without any finiteness premise. -/
theorem circleDeficit_antitone {u w : E → EReal} (x v : E) (r C : ℝ)
    (huw : ∀ t : ℝ, u (x + circleMap 0 r t • v) ≤
      w (x + circleMap 0 r t • v)) :
    circleDeficit w x v r C ≤ circleDeficit u x v r C := by
  unfold circleDeficit
  apply lintegral_mono
  intro t
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (huw t))

theorem HasDiscSubmeanOn.max {u w : E → EReal} {U : Set E}
    (hu : HasDiscSubmeanOn u U) (hw : HasDiscSubmeanOn w U) :
    HasDiscSubmeanOn (fun x => Max.max (u x) (w x)) U := by
  intro x v r hr hD C hC
  have hCu : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal) :=
    fun y hy => (le_max_left _ _).trans (hC y hy)
  have hCw : ∀ y ∈ affineClosedDisc x v r, w y ≤ (C : EReal) :=
    fun y hy => (le_max_right _ _).trans (hC y hy)
  rcases le_total (u x) (w x) with h | h
  · have hmono := circleDeficit_antitone (u := w)
      (w := fun y => Max.max (u y) (w y)) x v r C (fun _ => le_max_right _ _)
    simpa only [max_eq_right h] using hmono.trans (hw x v r hr hD C hCw)
  · have hmono := circleDeficit_antitone (u := u)
      (w := fun y => Max.max (u y) (w y)) x v r C (fun _ => le_max_left _ _)
    simpa only [max_eq_left h] using hmono.trans (hu x v r hr hD C hCu)

theorem DiscPshOn.max {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hw : DiscPshOn w U) :
    DiscPshOn (fun x => Max.max (u x) (w x)) U := by
  refine ⟨?_, hu.upperSemicontinuousOn.sup hw.upperSemicontinuousOn,
    hu.submean.max hw.submean⟩
  intro x hx
  exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hu.ne_top x hx))
    (lt_top_iff_ne_top.mpr (hw.ne_top x hx)))

theorem DiscPshOn.plurisubharmonicOn {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (hU : IsOpen U) : PlurisubharmonicOn u U :=
  fun _ hx => ⟨U, hU, hx, hu⟩

theorem PlurisubharmonicAt.max {u w : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) (hw : PlurisubharmonicAt w x) :
    PlurisubharmonicAt (fun y => Max.max (u y) (w y)) x := by
  obtain ⟨U, hU, hxU, hu⟩ := hu
  obtain ⟨V, hV, hxV, hw⟩ := hw
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩,
    (hu.mono inter_subset_left).max (hw.mono inter_subset_right)⟩

theorem PlurisubharmonicOn.max {u w : E → EReal} {U : Set E}
    (hu : PlurisubharmonicOn u U) (hw : PlurisubharmonicOn w U) :
    PlurisubharmonicOn (fun x => Max.max (u x) (w x)) U :=
  fun x hx => (hu x hx).max (hw x hx)

theorem PlurisubharmonicOn.mono {u : E → EReal} {U V : Set E}
    (hu : PlurisubharmonicOn u U) (hVU : V ⊆ U) : PlurisubharmonicOn u V :=
  fun x hx => hu x (hVU hx)

/-- The submean condition is unchanged by equality on its domain. -/
theorem HasDiscSubmeanOn.congr {u w : E → EReal} {U : Set E}
    (hu : HasDiscSubmeanOn u U) (heq : EqOn u w U) : HasDiscSubmeanOn w U := by
  intro x v r hr hD C hC
  have hx : x ∈ U := hD (center_mem_affineClosedDisc x v hr.le)
  have hcircle : circleDeficit u x v r C = circleDeficit w x v r C := by
    apply lintegral_congr
    intro t
    rw [heq (hD (circle_mem_affineClosedDisc x v hr.le t))]
  rw [← hcircle, ← heq hx]
  exact hu x v r hr hD C (fun y hy => (heq (hD hy)).trans_le (hC y hy))

theorem DiscPshOn.congr {u w : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (heq : EqOn u w U) : DiscPshOn w U := by
  refine ⟨fun x hx => (heq hx) ▸ hu.ne_top x hx, ?_, hu.submean.congr heq⟩
  intro x hx
  apply (hu.upperSemicontinuousOn x hx).congr_of_eventuallyEq hx
  filter_upwards [self_mem_nhdsWithin] with y hy
  intro c
  rw [heq hy]

/-- Plurisubharmonicity depends on the actual germ, including pole values. -/
theorem PlurisubharmonicAt.congr {u w : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) (heq : u =ᶠ[𝓝 x] w) :
    PlurisubharmonicAt w x := by
  obtain ⟨U, hU, hxU, hu⟩ := hu
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp heq
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
  exact (hu.mono inter_subset_left).congr (fun _ hy => hVsub hy.2)

theorem PlurisubharmonicAt.ne_top {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) : u x ≠ ⊤ := by
  obtain ⟨_, _, hx, hu⟩ := hu
  exact hu.ne_top x hx

theorem PlurisubharmonicAt.upperSemicontinuousAt {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) : UpperSemicontinuousAt u x := by
  obtain ⟨U, hU, hx, hu⟩ := hu
  intro c hc
  have h := hu.upperSemicontinuousOn x hx c hc
  rwa [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] at h

/-- The circle-deficit expression has the expected value for every constant,
including negative infinity. -/
theorem circleDeficit_const (a : EReal) (x v : E) (r C : ℝ) :
    circleDeficit (fun _ => a) x v r C =
      ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - a).toENNReal := by
  simp [circleDeficit, mul_comm]

theorem discPshOn_const (a : EReal) (ha : a ≠ ⊤) (U : Set E) :
    DiscPshOn (fun _ => a) U := by
  refine ⟨fun _ _ => ha, upperSemicontinuousOn_const, ?_⟩
  intro x v r _ _ C _
  exact (circleDeficit_const a x v r C).le

theorem plurisubharmonicAt_const (a : EReal) (ha : a ≠ ⊤) (x : E) :
    PlurisubharmonicAt (fun _ => a) x :=
  ⟨univ, isOpen_univ, mem_univ x, discPshOn_const a ha univ⟩

/-- Actual PSH stability for the collar construction already used in the
topological module. This does not assert a current correspondence. -/
theorem gluedMax_plurisubharmonic {U U' : Set E} {u w : E → EReal}
    (hU : IsOpen U) (hclosure : closure U' ⊆ U)
    (hcollar : ∀ x ∈ U \ U', u x ≤ w x)
    (hu : PlurisubharmonicOn u U) (hw : PlurisubharmonicOn w univ) :
    PlurisubharmonicOn (gluedMax U u w) univ := by
  intro x _
  by_cases hx : x ∈ U
  · exact ((hu x hx).max (hw x (mem_univ x))).congr
      (gluedMax_eventually_eq_max hU hx).symm
  · exact (hw x (mem_univ x)).congr
      (gluedMax_eventually_eq_global hclosure hcollar hx).symm

/-- The angular restriction in every admissible disc is genuinely measurable. -/
theorem DiscPshOn.measurable_circle {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) :
    Measurable (fun t : ℝ => u (x + circleMap 0 r t • v)) := by
  have hsc : UpperSemicontinuousOn (fun t : ℝ => u (x + circleMap 0 r t • v)) univ :=
    hu.upperSemicontinuousOn.comp (by fun_prop)
      (fun t _ => hD (circle_mem_affineClosedDisc x v hr t))
  exact (upperSemicontinuousOn_univ_iff.mp hsc).measurable

theorem DiscPshOn.measurable_circle_deficit {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (x v : E) {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) (C : ℝ) :
    Measurable (fun t : ℝ => ((C : EReal) - u (x + circleMap 0 r t • v)).toENNReal) := by
  have hsub : Measurable (fun z : EReal => (C : EReal) - z) :=
    EReal.measurable_of_measurable_real (by
      simpa only [Pi.sub_apply, id_eq, EReal.coe_sub] using
        ((measurable_const : Measurable (fun _ : ℝ => C)).sub measurable_id).coe_real_ereal)
  exact (hsub.comp (hu.measurable_circle x v hr hD)).ereal_toENNReal

/-- Raising a finite majorant adds an ordinary finite constant to its deficit. -/
theorem finiteDeficit_add_bound (C a : ℝ) (ha : 0 ≤ a) (z : EReal)
    (hz : z ≤ (C : EReal)) :
    (((C + a : ℝ) : EReal) - z).toENNReal =
      ENNReal.ofReal a + ((C : EReal) - z).toENNReal := by
  have hn : 0 ≤ (C : EReal) - z :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).mpr hz
  have heq : ((C + a : ℝ) : EReal) - z = (a : EReal) + ((C : EReal) - z) := by
    rw [EReal.coe_add]
    simp only [sub_eq_add_neg]
    ac_rfl
  rw [heq, EReal.toENNReal_add (EReal.coe_nonneg.mpr ha) hn,
    EReal.real_coe_toENNReal]

theorem circleDeficit_add_bound {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) :
    circleDeficit u x v r (C + a) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal a + circleDeficit u x v r C := by
  unfold circleDeficit
  simp_rw [finiteDeficit_add_bound C a ha _
    (hC _ (circle_mem_affineClosedDisc x v hr _))]
  rw [lintegral_add_left measurable_const]
  simp [mul_comm]

/-- The submean test is independent of increasing the chosen finite bound. -/
theorem discSubmean_add_bound_iff {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ y ∈ affineClosedDisc x v r, u y ≤ (C : EReal)) :
    (circleDeficit u x v r (C + a) ≤ ENNReal.ofReal (2 * Real.pi) *
      (((C + a : ℝ) : EReal) - u x).toENNReal) ↔
    (circleDeficit u x v r C ≤ ENNReal.ofReal (2 * Real.pi) *
      ((C : EReal) - u x).toENNReal) := by
  rw [circleDeficit_add_bound x v hr C a ha hC,
    finiteDeficit_add_bound C a ha _ (hC x (center_mem_affineClosedDisc x v hr)), mul_add]
  exact ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)

end SGPT.Foundations.Analysis
