/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.BedfordTaylorManifold
public import LeanPool.NonpluripolarProducts.PSH.LocalManifold
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentL1Ddc

/-!
# `dd^c φ` of a psh function on a complex manifold, and currents on open subsets

Source: `chapter_pshfunctions.tex` (the current `dd^c φ` of `φ ∈ PSH(X)`, a closed positive
`(1,1)`-current), used in `chapter_npp.tex`, `prop:npp1` (2) and `def:npp:L146`
(`dd^c φ_j^U = T_j` on `U`); Xia, *Foundations of pluripotential theory*, `q02`
(a psh function `≢ -∞` is `L¹_loc` and `dd^c u` is a closed positive `(1,1)`-current).

`M` is a complex manifold of dimension `m + 1` (mathlib's holomorphic atlas); currents on `M` are
S17's chart families `SGPT.NPP.PositiveCurrent`.

* `isL1PshOn_chart` — the coordinate expressions of `φ ∈ PSH(M)` (`def:pshmfd`) are psh and
  locally integrable on the coordinate domains.
* `ddcCurrent φ hφ` — **the current `dd^c φ`**, a positive current of bidimension `(m,m)`
  (bidegree `(1,1)`) on `M` whose expression in a chart `e` is TN's `ddcL1` of `φ ∘ e⁻¹`
  (`dd^c(φ [1])` in the sense of distributions); the chart expressions are compatible by the
  naturality `LocalCurrentL1Ddc.pullback_ddcL1`; `isClosed_ddcCurrent`.
* `chartDomain e O` — the coordinate expression
  `e(e.source ∩ O)` of an open set `O ⊆ M`; `chartDomain_mono`.
* `IsDdcOn T φ O` — `T|_O = dd^c φ` on the open set `O` (in every chart `e`, the restriction of
  the chart expression of `T` to `chartDomain e O` is `dd^c (φ ∘ e⁻¹)`); psh functions on `O`
  are the project's `SGPT.PSH.VariableComplexAtlas.IsPSHOn` (`def:pshmfd` on the open manifold
  `O`, with ambient representatives), and `isL1PshOn_chartDomain` gives their coordinate
  expressions.
* `isDdcOn_ddcCurrent` — `dd^c φ` restricts to `dd^c φ` on every open set.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.NPP

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsManifold (𝓘(ℂ, ComplexModel (m + 1))) ∞ M]

/-! ### Open subsets in coordinates -/

section ChartDomain

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]

/-- The coordinate expression `e(e.source ∩ O)` is monotone in `O`. -/
theorem chartDomain_mono (e : ComplexChart n X) {O O' : Opens X} (h : O ≤ O') :
    chartDomain e O ≤ chartDomain e O' :=
  fun _ hz => ⟨hz.1, h hz.2⟩

end ChartDomain

/-! ### Coordinate expressions of psh functions -/

/-- A function that is psh on the coordinate domain and has finite values near every point
there is psh and locally integrable. -/
theorem isL1PshOn_of_exists_ne_bot {W : Opens (ComplexModel (m + 1))} {u : ComplexModel (m + 1)
    → EReal}
    (hu : SGPT.Foundations.Analysis.PlurisubharmonicOn u W)
    (hnb : ∀ O : Set (ComplexModel (m + 1)), IsOpen O → O ⊆ W → ∀ z ∈ O, ∃ y ∈ O, u y ≠ ⊥) :
    IsL1PshOn W u := by
  refine ⟨hu, fun z hz => Filter.frequently_iff.mpr fun {N} hN => ?_⟩
  obtain ⟨O, hON, hO, hzO⟩ := mem_nhds_iff.mp (inter_mem hN (W.isOpen.mem_nhds hz))
  obtain ⟨y, hyO, hy⟩ := hnb O hO (fun x hx => (hON hx).2) z hzO
  exact ⟨y, (hON hyO).1, hy⟩

/-- **The coordinate expressions of a psh function on `M` are psh and locally integrable.** -/
theorem isL1PshOn_chart {φ : M → EReal} (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ)
    (e : ComplexChart (m + 1) M) : IsL1PshOn (chartTarget e) fun z => φ (e.val.symm z) :=
  isL1PshOn_of_exists_ne_bot (hφ.chartPlurisubharmonic e) fun _ hO hOe _ hz =>
    hφ.locallyNondegenerate.exists_chart_ne_bot e hO hOe hz

/-- **The coordinate expressions of a psh function on an open set `O ⊆ M`** (`def:pshmfd` on the
open manifold `O`, `SGPT.PSH.VariableComplexAtlas.IsPSHOn`) are psh and locally integrable on the
coordinate expressions of `O`. -/
theorem isL1PshOn_chartDomain {φ : M → EReal} {O : Opens M}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn φ O)
    (e : ComplexChart (m + 1) M) : IsL1PshOn (chartDomain e O) fun z => φ (e.val.symm z) :=
  isL1PshOn_of_exists_ne_bot (hφ.chartPlurisubharmonic e) fun _ hO hOe _ hz =>
    SGPT.PSH.VariableComplexAtlas.exists_coordinate_ne_bot_of_locallyNondegenerateOn
      (A := SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M)
      (hφ.locallyNondegenerate O.isOpen) e hO hOe hz

/-- A psh function on `M` is psh on every open subset. -/
theorem isPSHOn_of_manifoldPSH {φ : M → EReal} (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ)
    (O : Opens M) : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn φ O := by
  intro x _
  obtain ⟨e, hx, V, hV, hc, hVe, hxV, hφV⟩ := hφ x
  -- shrink the connected witness to a ball inside the coordinate expression of `O`
  have hxO' : e.val x ∈ chartDomain e O := ⟨e.val.map_source hx, by
    simpa [e.val.left_inv hx] using ‹x ∈ O›⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ((chartDomain e O).isOpen.inter hV) (e.val x)
    ⟨hxO', hxV⟩
  refine ⟨e, hx, Metric.ball (e.val x) r, Metric.isOpen_ball, Metric.isConnected_ball hr,
    fun z hz => (hball hz).1, Metric.mem_ball_self hr, ?_⟩
  refine ⟨hφV.disc.mono fun z hz => (hball hz).2, ?_⟩
  exact hφ.locallyNondegenerate.exists_chart_ne_bot e Metric.isOpen_ball
    (fun z hz => (hball hz).1.1) (Metric.mem_ball_self hr)

/-! ### The current `dd^c φ` -/

/-- `ddcL1` only depends on the function on the open set. -/
theorem ddcL1_congr {W : Opens (ComplexModel (m + 1))} {u v : ComplexModel (m + 1) → EReal}
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) W volume)
    (hv : LocallyIntegrableOn (fun x => (v x).toReal) W volume)
    (h : ∀ x ∈ W, u x = v x) : ddcL1 W u = ddcL1 W v := by
  rw [ddcL1, ddcL1, l1Current_congr_ae hu hv]
  filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
  rw [h x hx]

variable (m) in
/-- **The current `dd^c φ`** of a psh function `φ` on `M`: the positive current of bidimension
`(m,m)` whose expression in a chart `e` is `dd^c (φ ∘ e⁻¹)` (TN's `ddcL1`, the distributional
`dd^c` of the locally integrable function `φ ∘ e⁻¹`). -/
def ddcCurrent (φ : M → EReal) (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ) :
    PositiveCurrent (m + 1) M m where
  inChart e := ddcL1 (chartTarget e) fun z => φ (e.val.symm z)
  isPositive e := (isL1PshOn_chart hφ e).isPositive_ddcL1
  compatible e f := by
    have hh := chartTransition_isBiholomorphicPair e f
    have hfL := isL1PshOn_chart hφ f
    have hB : IsL1PshOn (overlapTarget e f) fun z => φ (f.val.symm z) :=
      hfL.mono (overlapTarget_le e f)
    have e1 := restrict_ddcL1 (overlapTarget_le e f) hfL.locallyIntegrableOn
    rw [pullback_congr hh _ hB.isPositive_ddcL1 e1,
      pullback_ddcL1 hh hB,
      restrict_ddcL1 (overlapSource_le e f) (isL1PshOn_chart hφ e).locallyIntegrableOn]
    exact ddcL1_congr (((isL1PshOn_chart hφ e).mono (overlapSource_le e f)).locallyIntegrableOn)
      (hB.comp hh).locallyIntegrableOn (chart_comp_transition φ e f)

@[simp] theorem ddcCurrent_inChart {φ : M → EReal} (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ)
    (e : ComplexChart (m + 1) M) :
    (ddcCurrent m φ hφ).inChart e = ddcL1 (chartTarget e) fun z => φ (e.val.symm z) := rfl

/-- `dd^c φ` is closed. -/
theorem isClosed_ddcCurrent {φ : M → EReal} (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ) :
    (ddcCurrent m φ hφ).IsClosed := fun _ => isClosedAny_ddcL1 _

/-! ### `T = dd^c φ` on an open set -/

/-- **`T|_O = dd^c φ`** for a positive `(1,1)`-current `T` on `M`, an open set `O ⊆ M` and a
function `φ` (psh on `O`): in every chart `e`, the restriction of the chart expression of `T` to
the coordinate expression `chartDomain e O` of `O` is `dd^c (φ ∘ e⁻¹)`. -/
def IsDdcOn (T : PositiveCurrent (m + 1) M m) (φ : M → EReal) (O : Opens M) : Prop :=
  ∀ e : ComplexChart (m + 1) M,
    restrict (chartDomain_le e O) (T.inChart e) = ddcL1 (chartDomain e O) fun z => φ (e.val.symm z)

/-- `dd^c φ` restricts to `dd^c φ` on every open set. -/
theorem isDdcOn_ddcCurrent {φ : M → EReal} (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ)
    (O : Opens M) : IsDdcOn (ddcCurrent m φ hφ) φ O := fun e =>
  restrict_ddcL1 (chartDomain_le e O) (isL1PshOn_chart hφ e).locallyIntegrableOn

/-- Restriction of `T|_O = dd^c φ` to a smaller open set. -/
theorem IsDdcOn.mono {T : PositiveCurrent (m + 1) M m} {φ : M → EReal} {O O' : Opens M}
    (h : IsDdcOn T φ O) (hO : O' ≤ O)
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel (m + 1) M).IsPSHOn φ O) :
    IsDdcOn T φ O' := fun e => by
  have e1 := h e
  have e2 := congrArg (restrict (chartDomain_mono e hO)) e1
  rw [LocalBedfordTaylorLocality.restrict_restrict,
    restrict_ddcL1 (chartDomain_mono e hO) (isL1PshOn_chartDomain hφ e).locallyIntegrableOn] at e2
  exact e2

/-- `T = dd^c φ` globally iff `T|_O = dd^c φ` on `O = M`... in every chart. -/
theorem isDdcOn_top_iff {T : PositiveCurrent (m + 1) M m} {φ : M → EReal}
    (hφ : SGPT.PSH.ManifoldPSH (n := m + 1) φ) : IsDdcOn T φ ⊤ ↔ T = ddcCurrent m φ hφ := by
  constructor
  · intro h
    ext1 e
    apply LocalBedfordTaylorCalculus.eq_of_local
    intro z hz
    refine ⟨chartDomain e ⊤, chartDomain_le e ⊤, ⟨hz, trivial⟩, ?_⟩
    rw [h e, ddcCurrent_inChart,
      restrict_ddcL1 (chartDomain_le e ⊤) (isL1PshOn_chart hφ e).locallyIntegrableOn]
  · rintro rfl
    exact isDdcOn_ddcCurrent hφ ⊤

end SGPT.NPP
