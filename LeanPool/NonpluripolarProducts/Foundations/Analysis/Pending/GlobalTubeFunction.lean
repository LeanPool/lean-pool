/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ChartPartition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TubeSecondOrderVanishing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.KahlerPerturbation

/-!
# The global tube function of a compact submanifold

Source: Copy-4, step 6 of the proof of `prop:principalization`, where `r_W²` is
*the square of the distance to `W` with respect to a Riemannian metric on `Y`*,
and the property used is that *"the Levi form of `r_W²` is positive semidefinite
with kernel exactly `T_W`"*.

A submanifold is only *locally* biholomorphic to a coordinate plane
(`FirstPass.RegularAtDim` carries a flattening `Φ`), so a single function `r_W²`
on a neighbourhood of `W` has to be patched out of the chart tubes
`r_i² = planeDistSq ∘ Φ_i ∘ e_i` with a partition of unity.  The two ingredients
are already on disk:

* `Pending.LeviFormHolomorphicComp` — the Levi form of one chart tube
  (semipositive on the whole chart, kernel `(dF)⁻¹(ℂ^k × 0)`);
* `Pending.TubeSecondOrderVanishing` — no cross term of the patching survives
  **along `W`**, because each chart tube vanishes there to second order.

This file supplies the missing global step: extension by zero, the partition of
unity (`Pending.ChartPartition.exists_chartSmooth_partitionOfUnity`), and the
assembly.

## What is proved

`exists_chartSmooth_tube`: on a compact complex manifold, a closed set `W` all of
whose points are regular of dimension `k` carries a chart-smooth `r ≥ 0` with
`r = 0` on `W` such that, at every `w ∈ W` and in every chart `f` around `w`, the
Levi form of the chart representation of `r` is semipositive and its kernel is
contained in the tangent space `(dF)⁻¹(ℂ^k × 0)` of an explicit holomorphic
flattening `F` of `W` in that chart.

## The one-sided kernel

Step 6 uses the kernel inclusion in the direction `ker ⊆ T_W` only: the consumer
is `Pending.UniformTubePositivity.exists_isStrictlyPositive_add_smul_of_pos_on_null_atCompact`,
whose hypothesis is *`a` strictly positive on the null directions of `b`*, and the
positivity available on `W` is that of the Kähler form `A_W` on `T_W`.  A null
direction inside `T_W` is therefore enough, and that is what the patched tube
gives directly: one index of the partition with `χ_i(w) > 0` forces its own chart
tube to be null, which is the inclusion above.

The reverse inclusion `T_W ⊆ ker` would need the tangent space to be independent
of the flattening: two flattenings differ by a biholomorphism preserving the
plane, so its differential preserves the plane.  That statement is true but not
proved here, and it is NOT dispensable for every consumer — a consumer who wants
to discharge a hypothesis quantified over all flattenings needs it (see I-0356).
The two-step route below does not: it reads the flattening off the tube it just
built.  Nothing in this file assumes independence.

The flattening handed back is **nondegenerate** (`fderiv_flatChartMap_injective`):
its differential is injective, because it is a local biholomorphism composed with
a chart transition.  Without that, a "flattening" could be degenerate — replacing
the last `n - k` coordinates of `F` by their squares keeps the zero locus and
kills the whole differential — and a statement quantified over flattenings would
silently demand positivity in all directions.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalTubeFunction

open FirstPass FirstPass.HolomorphicMaps PlaneTubePositivity
  LeviFormHolomorphicComp TubeSecondOrderVanishing ChartPartition

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### Chart-smoothness over an open set -/

variable (n) in
/-- Smoothness in every holomorphic chart, tested only over an open subset `S` of
the manifold.  This is `FirstPass.ChartSmooth` relativised to `S`; a function
defined by a chart formula is only chart-smooth in this sense. -/
def ChartSmoothOn (h : M → ℝ) (S : Set M) : Prop :=
  ∀ e : ComplexChart n M,
    ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' S)

omit [IsComplexManifold n M] in
theorem ChartSmooth.chartSmoothOn {h : M → ℝ} (hh : ChartSmooth (n := n) h) (S : Set M) :
    ChartSmoothOn n h S :=
  fun e => (hh e).mono inter_subset_left

/-! ### Extension by zero of a bump times a locally defined function -/

/-- `χ · h`, extended by zero outside `S`.  When `tsupport χ ⊆ S` this is smooth
everywhere even though `h` is only defined (or only smooth) on `S`. -/
def bumpExtend (S : Set M) (χ h : M → ℝ) : M → ℝ :=
  S.indicator fun y => χ y * h y

omit [TopologicalSpace M] in
theorem bumpExtend_of_mem {S : Set M} {χ h : M → ℝ} {y : M} (hy : y ∈ S) :
    bumpExtend S χ h y = χ y * h y :=
  indicator_of_mem hy _

omit [TopologicalSpace M] in
theorem bumpExtend_of_notMem {S : Set M} {χ h : M → ℝ} {y : M} (hy : y ∉ S) :
    bumpExtend S χ h y = 0 :=
  indicator_of_notMem hy _

omit [TopologicalSpace M] in
theorem bumpExtend_nonneg {S : Set M} {χ h : M → ℝ} (hχ : ∀ y, 0 ≤ χ y)
    (hh : ∀ y, 0 ≤ h y) (y : M) : 0 ≤ bumpExtend S χ h y := by
  by_cases hy : y ∈ S
  · rw [bumpExtend_of_mem hy]; exact mul_nonneg (hχ y) (hh y)
  · rw [bumpExtend_of_notMem hy]

theorem bumpExtend_eq_zero_of_notMem_tsupport {S : Set M} {χ h : M → ℝ} {y : M}
    (hy : y ∉ tsupport χ) : bumpExtend S χ h y = 0 := by
  by_cases hyS : y ∈ S
  · rw [bumpExtend_of_mem hyS, image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · rw [bumpExtend_of_notMem hyS]

omit [IsComplexManifold n M] in
/-- **Extension by zero is chart-smooth.**  A chart-smooth bump with support
inside the open set `S`, multiplied by a function smooth only over `S`, extends by
zero to a globally chart-smooth function. -/
theorem chartSmooth_bumpExtend {S : Set M} (hS : IsOpen S) {χ h : M → ℝ}
    (hχ : ChartSmooth (n := n) χ) (hh : ChartSmoothOn n h S)
    (hsupp : tsupport χ ⊆ S) :
    ChartSmooth (n := n) (bumpExtend S χ h) := by
  intro e
  refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
  by_cases hzS : e.val.symm z ∈ S
  · refine ⟨e.val.target ∩ e.val.symm ⁻¹' S, ?_, ⟨hz, hzS⟩, ?_⟩
    · simpa using e.val.symm.isOpen_inter_preimage hS
    · refine ContDiffOn.congr
        (f := fun w => χ (e.val.symm w) * h (e.val.symm w)) ?_ ?_
      · exact ((hχ e).mono inter_subset_left).mul
          ((hh e).mono (s := e.val.target ∩ e.val.symm ⁻¹' S) inter_subset_right)
      · intro w hw
        exact bumpExtend_of_mem hw.2.2
  · have hzt : e.val.symm z ∉ tsupport χ := fun hc => hzS (hsupp hc)
    refine ⟨e.val.target ∩ e.val.symm ⁻¹' (tsupport χ)ᶜ, ?_, ⟨hz, hzt⟩, ?_⟩
    · simpa using e.val.symm.isOpen_inter_preimage (isClosed_tsupport χ).isOpen_compl
    · refine ContDiffOn.congr (f := fun _ => (0 : ℝ)) contDiffOn_const ?_
      intro w hw
      exact bumpExtend_eq_zero_of_notMem_tsupport hw.2.2

/-! ### The tube function of one flattening chart -/

variable {p : ComplexModel n}

/-- The part of the manifold on which the flattening `Φ`, read in the chart `e`,
is defined. -/
def flatDomain (e : ComplexChart n M) (Φ : LocalHolomorphicEquivAt (n := n) p) : Set M :=
  e.val.source ∩ e.val ⁻¹' Φ.source

omit [IsComplexManifold n M] in
theorem isOpen_flatDomain (e : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) : IsOpen (flatDomain e Φ) :=
  e.val.isOpen_inter_preimage Φ.isOpen_source

/-- The chart tube `r_i²`: the squared distance to the coordinate plane, read
through the flattening `Φ ∘ e`.  Outside `flatDomain e Φ` the formula still makes
sense but carries no information. -/
def flatTube (e : ComplexChart n M) (Φ : LocalHolomorphicEquivAt (n := n) p)
    (k : ℕ) : M → ℝ :=
  fun y => planeDistSq n k (Φ.toFun (e.val y))

omit [IsComplexManifold n M] in
theorem flatTube_nonneg (e : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) (k : ℕ) (y : M) :
    0 ≤ flatTube e Φ k y :=
  planeDistSq_nonneg _

/-- The holomorphic flattening of `W` read in an arbitrary chart `f`: the
flattening `Φ` of the chart `e` composed with the transition `f → e`. -/
def flatChartMap (e f : ComplexChart n M) (Φ : LocalHolomorphicEquivAt (n := n) p) :
    ComplexModel n → ComplexModel n :=
  fun z => Φ.toFun (chartTransition f e z)

/-- The open set of the chart `f` over which `flatChartMap e f Φ` is defined. -/
def flatChartDomain (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) : Set (ComplexModel n) :=
  f.val.target ∩ f.val.symm ⁻¹' flatDomain e Φ

omit [IsComplexManifold n M] in
theorem isOpen_flatChartDomain (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) : IsOpen (flatChartDomain e f Φ) := by
  simpa [flatChartDomain] using
    f.val.symm.isOpen_inter_preimage (isOpen_flatDomain e Φ)

omit [IsComplexManifold n M] in
theorem flatChartDomain_subset_target (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    flatChartDomain e f Φ ⊆ f.val.target := fun _ hz => hz.1

/-- **The chart flattening is holomorphic.** -/
theorem contDiffOn_flatChartMap (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) :
    ContDiffOn ℂ ∞ (flatChartMap e f Φ) (flatChartDomain e f Φ) := by
  have hΦ : ContDiffOn ℂ ∞ Φ.toFun Φ.source :=
    contDiffOn_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source
  intro z hz
  have hzs : z ∈ (chartTransition f e).source := ⟨hz.1, hz.2.1⟩
  have h1 : ContDiffAt ℂ ∞ (chartTransition f e) z := chartTransition_contDiffAt f e hzs
  have h2 : ContDiffAt ℂ ∞ Φ.toFun (chartTransition f e z) :=
    hΦ.contDiffAt (Φ.isOpen_source.mem_nhds hz.2.2)
  exact (h2.comp z h1).contDiffWithinAt

omit [IsComplexManifold n M] in
/-- The chart representation of the chart tube is `planeDistSq ∘ flatChartMap`. -/
theorem flatTube_comp_symm (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) (k : ℕ) :
    (fun z => flatTube e Φ k (f.val.symm z)) =
      fun z => planeDistSq n k (flatChartMap e f Φ z) := rfl

theorem chartSmoothOn_flatTube (e : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) (k : ℕ) :
    ChartSmoothOn n (flatTube e Φ k) (flatDomain e Φ) := by
  intro f
  rw [flatTube_comp_symm e f Φ k]
  exact (contDiff_planeDistSq (n := n) (k := k)).comp_contDiffOn
    ((contDiffOn_flatChartMap e f Φ).restrict_scalars ℝ)

/-- **The differential of a local biholomorphism is injective**: its local
inverse differentiates to a left inverse. -/
theorem fderiv_toFun_injective {p : ComplexModel n}
    (Φ : LocalHolomorphicEquivAt (n := n) p) {z : ComplexModel n} (hz : z ∈ Φ.source) :
    Function.Injective (fderiv ℝ Φ.toFun z) := by
  have hzt : Φ.toFun z ∈ Φ.target := Φ.mapsTo_toFun hz
  have hT : DifferentiableAt ℝ Φ.toFun z :=
    (Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hz)).restrictScalars ℝ
  have hT' : DifferentiableAt ℝ Φ.invFun (Φ.toFun z) :=
    (Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hzt)).restrictScalars ℝ
  have hev : (Φ.invFun ∘ Φ.toFun) =ᶠ[𝓝 z] id := by
    filter_upwards [Φ.isOpen_source.mem_nhds hz] with y hy
    exact Φ.left_inv y hy
  have hcomp : (fderiv ℝ Φ.invFun (Φ.toFun z)).comp (fderiv ℝ Φ.toFun z)
      = ContinuousLinearMap.id ℝ (ComplexModel n) := by
    rw [← fderiv_comp z hT' hT, hev.fderiv_eq, fderiv_id]
  intro v w hvw
  have h1 := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L v) hcomp
  have h2 := congrArg (fun L : ComplexModel n →L[ℝ] ComplexModel n => L w) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
  rw [← h1, ← h2]
  exact congrArg _ hvw

/-- **The chart flattening is nondegenerate.**  Its differential is injective: it
is a local biholomorphism composed with a chart transition.  This is what rules
out degenerate "flattenings" such as squaring the normal coordinates, which have
the same zero locus but a differential that kills every direction. -/
theorem fderiv_flatChartMap_injective (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) :
    Function.Injective (fderiv ℝ (flatChartMap e f Φ) z) := by
  have hzs : z ∈ (chartTransition f e).source := ⟨hz.1, hz.2.1⟩
  have hT : DifferentiableAt ℝ (chartTransition f e) z :=
    (chartTransition_contDiffAt_real f e hzs).differentiableAt (by simp)
  have hΦ : DifferentiableAt ℝ Φ.toFun (chartTransition f e z) :=
    (Φ.toFun_holomorphic.differentiableAt
      (Φ.isOpen_source.mem_nhds hz.2.2)).restrictScalars ℝ
  have hchain : fderiv ℝ (flatChartMap e f Φ) z
      = (fderiv ℝ Φ.toFun (chartTransition f e z)).comp
        (fderiv ℝ (chartTransition f e) z) := by
    rw [← fderiv_comp z hΦ hT]
    rfl
  rw [hchain]
  intro v w hvw
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hvw
  exact KahlerPerturbation.chartTransitionDerivative_injective f e hzs
    (fderiv_toFun_injective Φ hz.2.2 hvw)

/-- The Levi form of the chart tube is semipositive on the whole chart domain. -/
theorem leviForm_flatTube_nonneg (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) (k : ℕ) {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) (v : ComplexModel n) :
    0 ≤ leviForm (fun w => flatTube e Φ k (f.val.symm w)) z v := by
  rw [flatTube_comp_symm e f Φ k]
  exact leviForm_planeDistSq_comp_nonneg (j := k) (isOpen_flatChartDomain e f Φ)
    (contDiffOn_flatChartMap e f Φ) hz v

/-- The kernel of the Levi form of the chart tube is the tangent space of the
flattened submanifold. -/
theorem leviForm_flatTube_eq_zero_iff (e f : ComplexChart n M)
    (Φ : LocalHolomorphicEquivAt (n := n) p) (k : ℕ) {z : ComplexModel n}
    (hz : z ∈ flatChartDomain e f Φ) (v : ComplexModel n) :
    leviForm (fun w => flatTube e Φ k (f.val.symm w)) z v = 0 ↔
      fderiv ℝ (flatChartMap e f Φ) z v ∈ complexCoordinatePlane n k := by
  rw [flatTube_comp_symm e f Φ k]
  exact leviForm_planeDistSq_comp_eq_zero_iff (j := k) (isOpen_flatChartDomain e f Φ)
    (contDiffOn_flatChartMap e f Φ) hz v

/-! ### Germ invariance of the Levi form -/

/-- The Levi form depends only on the germ of the function.  (The same statement
for an open set is `Pending.HormanderPairingBound.leviForm_congr_of_eqOn`; that
module carries the Hörmander estimate and is not imported here.) -/
theorem leviForm_congr_of_eventuallyEq {F G : ComplexModel n → ℝ}
    {x : ComplexModel n} (h : F =ᶠ[𝓝 x] G) (v : ComplexModel n) :
    leviForm F x v = leviForm G x v := by
  simp only [leviForm, realHessian_eq_fderiv, h.fderiv.fderiv_eq]

/-! ### The global tube function -/

/-- **The global tube function of a compact submanifold** (Copy-4, step 6 of
`prop:principalization`).  A closed set all of whose points are regular of
dimension `k` carries a chart-smooth `r ≥ 0`, vanishing on `W`, whose Levi form at
every point of `W` is semipositive with kernel inside the tangent space of an
explicit holomorphic flattening of `W` in the ambient chart.

This is the manuscript's `r_W²`.  The distance function of a Riemannian metric is
replaced by the patched chart tubes, which is the standard construction of such a
distance up to a factor bounded above and below; only the two properties above are
used downstream. -/
theorem exists_chartSmooth_tube [CompactSpace M] {W : Set M} {k : ℕ}
    (hWclosed : IsClosed W) (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) :
    ∃ r : M → ℝ, ChartSmooth (n := n) r ∧ (∀ y, 0 ≤ r y) ∧ (∀ w ∈ W, r w = 0) ∧
      ∀ (f : ComplexChart n M) (w : M), w ∈ W → w ∈ f.val.source →
        (∀ v, 0 ≤ leviForm (fun z => r (f.val.symm z)) (f.val w) v) ∧
        ∃ (F : ComplexModel n → ComplexModel n) (D : Set (ComplexModel n)),
          IsOpen D ∧ f.val w ∈ D ∧ D ⊆ f.val.target ∧ ContDiffOn ℂ ∞ F D ∧
          Function.Injective (fderiv ℝ F (f.val w)) ∧
          (∀ z ∈ D, (f.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) ∧
          ∀ v, leviForm (fun z => r (f.val.symm z)) (f.val w) v = 0 →
            fderiv ℝ F (f.val w) v ∈ complexCoordinatePlane n k := by
  classical
  -- the flattening at every point of `W`, in its own preferred chart
  have hdata : ∀ x : {x : M // x ∈ W},
      ∃ Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x.1).val x.1),
        ∀ y : M, y ∈ (complexChartAt (n := n) x.1).val.source →
          (complexChartAt (n := n) x.1).val y ∈ Φ.source →
          (y ∈ W ↔ Φ.toFun ((complexChartAt (n := n) x.1).val y) ∈
            complexCoordinatePlane n k) := by
    rintro ⟨x, hx⟩
    obtain ⟨-, -, Φ, -, -, hflat⟩ := hWreg x hx
    exact ⟨Φ, fun _ hy hy' => hflat hy hy'⟩
  choose Φ hΦflat using hdata
  set E : {x : M // x ∈ W} → ComplexChart n M :=
    fun x => complexChartAt (n := n) x.1 with hE
  -- the cover: a flattening domain around each point of `W`, and the complement
  set Sset : Option {x : M // x ∈ W} → Set M :=
    fun i => i.elim Wᶜ (fun x => flatDomain (E x) (Φ x)) with hSset
  have hSnone : Sset none = Wᶜ := rfl
  have hSsome : ∀ x, Sset (some x) = flatDomain (E x) (Φ x) := fun _ => rfl
  have hSopen : ∀ i, IsOpen (Sset i) := by
    rintro (_ | x)
    · exact hWclosed.isOpen_compl
    · exact isOpen_flatDomain _ _
  set S : Option {x : M // x ∈ W} → Opens M := fun i => ⟨Sset i, hSopen i⟩ with hS
  have hcover : ∀ y : M, ∃ i, y ∈ S i := by
    intro y
    by_cases hy : y ∈ W
    · exact ⟨some ⟨y, hy⟩, mem_complexChartAt_source y, (Φ ⟨y, hy⟩).center_mem_source⟩
    · exact ⟨none, hy⟩
  obtain ⟨m, χ, idx, hχsm, hχnn, hχsupp, -, hχsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  -- the chart tube attached to each member of the cover
  set G : Option {x : M // x ∈ W} → M → ℝ :=
    fun i => i.elim (fun _ => 0) (fun x => flatTube (E x) (Φ x) k) with hG
  have hGnone : G none = fun _ : M => (0 : ℝ) := rfl
  have hGsome : ∀ x, G (some x) = flatTube (E x) (Φ x) k := fun _ => rfl
  have hGnn : ∀ i y, 0 ≤ G i y := by
    rintro (_ | x) y
    · exact le_rfl
    · exact flatTube_nonneg _ _ _ _
  have hGsm : ∀ i, ChartSmoothOn n (G i) (Sset i) := by
    rintro (_ | x)
    · exact ChartSmooth.chartSmoothOn (fun _ => contDiffOn_const) _
    · exact chartSmoothOn_flatTube _ _ _
  have hGzero : ∀ i, ∀ w ∈ W, w ∈ Sset i → G i w = 0 := by
    rintro (_ | x) w hw hwS
    · rfl
    · exact (planeDistSq_eq_zero_iff _).mpr ((hΦflat x w hwS.1 hwS.2).mp hw)
  -- the patched tube
  set T : Fin m → M → ℝ := fun a => bumpExtend (Sset (idx a)) (χ a) (G (idx a)) with hT
  have hTdef : ∀ a, T a = bumpExtend (Sset (idx a)) (χ a) (G (idx a)) := fun _ => rfl
  set r : M → ℝ := fun y => ∑ a, T a y with hr
  have hTsm : ∀ a, ChartSmooth (n := n) (T a) := fun a =>
    chartSmooth_bumpExtend (hSopen _) (hχsm a) (hGsm _) (hχsupp a)
  refine ⟨r, fun e => ContDiffOn.sum fun a _ => hTsm a e, fun y => ?_, fun w hw => ?_, ?_⟩
  · exact Finset.sum_nonneg fun a _ => bumpExtend_nonneg (hχnn a) (hGnn _) y
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [hTdef a]
    by_cases hwS : w ∈ Sset (idx a)
    · rw [bumpExtend_of_mem hwS, hGzero _ w hw hwS, mul_zero]
    · exact bumpExtend_of_notMem hwS
  · intro f w hwW hwf
    set z₀ : ComplexModel n := f.val w with hz₀
    have hz₀t : z₀ ∈ f.val.target := f.val.map_source hwf
    have hsymm : f.val.symm z₀ = w := f.val.left_inv hwf
    -- the local model of each summand at `w`
    set cx : Fin m → ComplexModel n → ℝ := fun a =>
      if w ∈ Sset (idx a) then (fun z => χ a (f.val.symm z)) else (fun _ => 0) with hcx
    set gx : Fin m → ComplexModel n → ℝ := fun a =>
      if w ∈ Sset (idx a) then (fun z => G (idx a) (f.val.symm z)) else (fun _ => 0) with hgx
    have hcxpos : ∀ a, w ∈ Sset (idx a) → cx a = fun z => χ a (f.val.symm z) := by
      intro a h; simp only [hcx, ite_eq_left h]
    have hcxneg : ∀ a, w ∉ Sset (idx a) → cx a = fun _ => (0 : ℝ) := by
      intro a h; simp only [hcx, ite_eq_right h]
    have hgxpos : ∀ a, w ∈ Sset (idx a) → gx a = fun z => G (idx a) (f.val.symm z) := by
      intro a h; simp only [hgx, ite_eq_left h]
    have hgxneg : ∀ a, w ∉ Sset (idx a) → gx a = fun _ => (0 : ℝ) := by
      intro a h; simp only [hgx, ite_eq_right h]
    have hEqa : ∀ a, (fun z => T a (f.val.symm z)) =ᶠ[𝓝 z₀] fun z => cx a z * gx a z := by
      intro a
      by_cases hwS : w ∈ Sset (idx a)
      · have hopen : IsOpen (f.val.target ∩ f.val.symm ⁻¹' Sset (idx a)) := by
          simpa using f.val.symm.isOpen_inter_preimage (hSopen (idx a))
        have hmem : z₀ ∈ f.val.target ∩ f.val.symm ⁻¹' Sset (idx a) :=
          ⟨hz₀t, by simp only [mem_preimage, hsymm]; exact hwS⟩
        filter_upwards [hopen.mem_nhds hmem] with z hz
        rw [hcxpos a hwS, hgxpos a hwS, hTdef a]
        exact bumpExtend_of_mem hz.2
      · have hwt : w ∉ tsupport (χ a) := fun hc => hwS (hχsupp a hc)
        have hopen : IsOpen (f.val.target ∩ f.val.symm ⁻¹' (tsupport (χ a))ᶜ) := by
          simpa using
            f.val.symm.isOpen_inter_preimage (isClosed_tsupport (χ a)).isOpen_compl
        have hmem : z₀ ∈ f.val.target ∩ f.val.symm ⁻¹' (tsupport (χ a))ᶜ :=
          ⟨hz₀t, by simp only [mem_preimage, mem_compl_iff, hsymm]; exact hwt⟩
        filter_upwards [hopen.mem_nhds hmem] with z hz
        rw [hcxneg a hwS, hTdef a, zero_mul]
        exact bumpExtend_eq_zero_of_notMem_tsupport hz.2
    have hEq : (fun z => r (f.val.symm z)) =ᶠ[𝓝 z₀] fun z => ∑ a, cx a z * gx a z := by
      have hall : ∀ᶠ z in 𝓝 z₀, ∀ a : Fin m, T a (f.val.symm z) = cx a z * gx a z :=
        Filter.eventually_all.2 hEqa
      filter_upwards [hall] with z hz
      exact Finset.sum_congr rfl fun a _ => hz a
    -- the flattening chart domain attached to an index switched on at `w`
    have hdom : ∀ (a : Fin m) (x : {x : M // x ∈ W}), idx a = some x →
        w ∈ Sset (idx a) → z₀ ∈ flatChartDomain (E x) f (Φ x) := by
      intro a x hax hwS
      rw [hax, hSsome] at hwS
      exact ⟨hz₀t, by simp only [mem_preimage, hsymm]; exact hwS⟩
    have hcxC : ∀ a, ContDiffAt ℝ 2 (cx a) z₀ := by
      intro a
      by_cases hwS : w ∈ Sset (idx a)
      · rw [hcxpos a hwS]
        exact ((hχsm a f).contDiffAt (f.val.open_target.mem_nhds hz₀t)).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      · rw [hcxneg a hwS]; exact contDiffAt_const
    have hgxC : ∀ a, ContDiffAt ℝ 2 (gx a) z₀ := by
      intro a
      by_cases hwS : w ∈ Sset (idx a)
      · rw [hgxpos a hwS]
        rcases hidx : idx a with _ | x
        · rw [hGnone]; exact contDiffAt_const
        · rw [hGsome x]
          exact ((chartSmoothOn_flatTube (E x) (Φ x) k f).contDiffAt
            ((isOpen_flatChartDomain (E x) f (Φ x)).mem_nhds (hdom a x hidx hwS))).of_le
              (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      · rw [hgxneg a hwS]; exact contDiffAt_const
    have hgxnn : ∀ a, ∀ y : ComplexModel n, 0 ≤ gx a y := by
      intro a y
      by_cases hwS : w ∈ Sset (idx a)
      · rw [hgxpos a hwS]; exact hGnn _ _
      · rw [hgxneg a hwS]
    have hgxz : ∀ a, gx a z₀ = 0 := by
      intro a
      by_cases hwS : w ∈ Sset (idx a)
      · rw [hgxpos a hwS]
        simp only [hsymm]
        exact hGzero _ w hwW hwS
      · rw [hgxneg a hwS]
    have hcxnn : ∀ a, 0 ≤ cx a z₀ := by
      intro a
      by_cases hwS : w ∈ Sset (idx a)
      · rw [hcxpos a hwS]; exact hχnn a _
      · rw [hcxneg a hwS]
    have hlev : ∀ (a : Fin m) (v : ComplexModel n), 0 ≤ leviForm (gx a) z₀ v := by
      intro a v
      by_cases hwS : w ∈ Sset (idx a)
      · rw [hgxpos a hwS]
        rcases hidx : idx a with _ | x
        · rw [hGnone, leviForm_const]
        · rw [hGsome x]
          exact leviForm_flatTube_nonneg (E x) f (Φ x) k (hdom a x hidx hwS) v
      · rw [hgxneg a hwS, leviForm_const]
    have hkey : ∀ v : ComplexModel n,
        leviForm (fun z => r (f.val.symm z)) z₀ v
          = ∑ a, cx a z₀ * leviForm (gx a) z₀ v := by
      intro v
      rw [leviForm_congr_of_eventuallyEq hEq v]
      exact leviForm_finsetSum_mul Finset.univ hcxC hgxC
        (fun i => Filter.Eventually.of_forall fun y => hgxnn i y) hgxz v
    -- an index switched on at `w`
    obtain ⟨a₀, ha₀⟩ : ∃ a : Fin m, 0 < χ a w := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hle : ∑ a, χ a w ≤ 0 := Finset.sum_nonpos fun a _ => hcon a
      rw [hχsum w] at hle
      linarith
    have ha₀S : w ∈ Sset (idx a₀) := hχsupp a₀ (subset_tsupport _ ha₀.ne')
    obtain ⟨x₀, hx₀⟩ : ∃ x, idx a₀ = some x := by
      rcases hidx : idx a₀ with _ | x
      · rw [hidx, hSnone] at ha₀S; exact absurd hwW ha₀S
      · exact ⟨x, rfl⟩
    have hz₀D : z₀ ∈ flatChartDomain (E x₀) f (Φ x₀) := hdom a₀ x₀ hx₀ ha₀S
    refine ⟨fun v => ?_, flatChartMap (E x₀) f (Φ x₀), flatChartDomain (E x₀) f (Φ x₀),
      isOpen_flatChartDomain _ _ _, hz₀D, flatChartDomain_subset_target _ _ _,
      contDiffOn_flatChartMap _ _ _, fderiv_flatChartMap_injective _ _ _ hz₀D,
      fun z hz => hΦflat x₀ _ hz.2.1 hz.2.2, fun v hv => ?_⟩
    · rw [hkey v]
      exact Finset.sum_nonneg fun a _ => mul_nonneg (hcxnn a) (hlev a v)
    · have hzero : leviForm (fun y => ∑ a, cx a y * gx a y) z₀ v = 0 := by
        rw [← leviForm_congr_of_eventuallyEq hEq v]; exact hv
      have hcx₀ : 0 < cx a₀ z₀ := by
        rw [hcxpos a₀ ha₀S]; simp only [hsymm]; exact ha₀
      have hgz : leviForm (gx a₀) z₀ v = 0 :=
        leviForm_eq_zero_of_leviForm_finsetSum_mul_eq_zero hcxC hgxC
          (fun i => Filter.Eventually.of_forall fun y => hgxnn i y) hgxz hcxnn
          (fun i => hlev i v) hzero (Finset.mem_univ a₀) hcx₀
      rw [hgxpos a₀ ha₀S, hx₀, hGsome x₀] at hgz
      exact (leviForm_flatTube_eq_zero_iff (E x₀) f (Φ x₀) k hz₀D v).mp hgz

end

end SGPT.Foundations.Analysis.Pending.GlobalTubeFunction
