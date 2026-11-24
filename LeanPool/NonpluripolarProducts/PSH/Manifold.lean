/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.PSH.HolomorphicPullback
public import LeanPool.NonpluripolarProducts.PSH.Supremum
public import LeanPool.NonpluripolarProducts.PSH.LocalL1
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicMaps
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SubgeodesicChord
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscRegularizationContinuous
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Actual holomorphic chart PSH

Use genuine atlas charts and holomorphic overlap compatibility. The ambient
manifold is not required to be second countable: the source allows uncountably
many components. Each concrete coordinate space is second countable.
-/

@[expose] public section

namespace SGPT.PSH

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Type*} [TopologicalSpace X]

/-- One genuine connected coordinate witness supplies finite points in every
actual open neighborhood of its original center. This local producer is shared
by the global atlas predicate and predicates on open manifold subsets. -/
theorem exists_ne_bot_in_open_of_coordinate_psh {u : X → EReal} {d : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) {x : X} (hx : x ∈ e.source)
    {V : Set (ComplexModel d)} (hV : IsOpen V) (hconn : IsConnected V)
    (hzV : e x ∈ V) (huV : PSHOn (u ∘ e.symm) V)
    {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) : ∃ y ∈ O, u y ≠ ⊥ := by
  obtain ⟨N, hN, hzN, hae, _⟩ :=
    (huV.disc.plurisubharmonicOn hV).subset_pshIntegrabilityLocus
      volume hconn.isPreconnected huV.nontrivial hzV
  let B := N ∩ (e.target ∩ e.symm ⁻¹' O) ∩ V
  have hB : IsOpen B := (hN.inter (e.isOpen_inter_preimage_symm hO)).inter hV
  have hxO' : e x ∈ e.symm ⁻¹' O := by
    change e.symm (e x) ∈ O
    simpa only [e.left_inv hx] using hxO
  have hzB : e x ∈ B := ⟨⟨hzN, e.map_source hx, hxO'⟩, hzV⟩
  have hpos : 0 < volume B := hB.measure_pos volume ⟨e x, hzB⟩
  have hfin : ∀ᵐ z ∂volume.restrict B, (u ∘ e.symm) z ≠ ⊤ ∧
      (u ∘ e.symm) z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset (fun _ hz ↦ hz.1.1) hae
  obtain ⟨z, hz, hzf⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' hfin
  exact ⟨e.symm z, hz.1.2.2, hzf.2⟩

/-- Actual connected local coordinate PSH witnesses produce non-bottom
points in every open neighborhood, with coordinate dimension allowed to vary. -/
theorem locallyNondegenerate_of_local_coordinate_psh {u : X → EReal}
    (hu : ∀ x : X, ∃ d : ℕ, ∃ e : OpenPartialHomeomorph X (ComplexModel d),
      x ∈ e.source ∧ ∃ V : Set (ComplexModel d), IsOpen V ∧ IsConnected V ∧
        V ⊆ e.target ∧ e x ∈ V ∧ PSHOn (u ∘ e.symm) V) :
    LocallyNondegenerate u := by
  intro x O hO hxO
  obtain ⟨d, e, hx, V, hV, hconn, _, hzV, huV⟩ := hu x
  exact exists_ne_bot_in_open_of_coordinate_psh e hx hV hconn hzV huV hO hxO

/-- Actual coordinate germ covers make the closure of the non-bottom locus
open. This common producer permits a different coordinate dimension at every
local chart and specializes the fixed-model proof below. -/
theorem isOpen_closure_nonbot_of_local_coordinate_psh {u : X → EReal}
    (hlocal : ∀ x : X, ∃ d : ℕ, ∃ e : OpenPartialHomeomorph X (ComplexModel d),
      x ∈ e.source ∧ SGPT.Foundations.Analysis.PlurisubharmonicOn (u ∘ e.symm) e.target) :
    IsOpen (closure {x | u x ≠ ⊥}) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨d, e, hxe, hpsh⟩ := hlocal x
  have hz : e x ∈ e.target := e.map_source hxe
  have hcl : e x ∈ closure
      (SGPT.Foundations.Analysis.pshIntegrabilityLocus ((u ∘ e.symm)) volume) := by
    apply mem_closure_iff.mpr
    intro O hO hzO
    have hxO : x ∈ e.source ∩ e ⁻¹' O := ⟨hxe, hzO⟩
    obtain ⟨y, hy, hfin⟩ := mem_closure_iff.mp hx
      (e.source ∩ e ⁻¹' O) (e.isOpen_inter_preimage hO) hxO
    have hyT := e.map_source hy.1
    change u y ≠ ⊥ at hfin
    have hyF : (u ∘ e.symm) (e y) ≠ ⊥ := by
      simpa only [Function.comp_apply, e.left_inv hy.1] using hfin
    exact ⟨e y, hy.2, (hpsh _ hyT).mem_pshIntegrabilityLocus volume hyF⟩
  obtain ⟨V, hV, hzV, hae, _⟩ :=
    (hpsh _ hz).mem_pshIntegrabilityLocus_of_mem_closure volume hcl
  have hA : IsOpen (e.source ∩ e ⁻¹' V) := e.isOpen_inter_preimage hV
  apply mem_of_superset (hA.mem_nhds ⟨hxe, hzV⟩)
  intro y hy
  apply mem_closure_iff.mpr
  intro O hO hyO
  let B := V ∩ (e.target ∩ e.symm ⁻¹' O)
  have hB : IsOpen B := hV.inter (e.isOpen_inter_preimage_symm hO)
  have hyO' : e y ∈ e.symm ⁻¹' O := by
    change e.symm (e y) ∈ O
    simpa only [e.left_inv hy.1] using hyO
  have hyB : e y ∈ B := ⟨hy.2, e.map_source hy.1, hyO'⟩
  have hpos : 0 < volume B := hB.measure_pos volume ⟨e y, hyB⟩
  have hfin : ∀ᵐ z ∂volume.restrict B, (u ∘ e.symm) z ≠ ⊤ ∧
      (u ∘ e.symm) z ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset (fun _ hz ↦ hz.1) hae
  obtain ⟨z, hz, hzf⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' hfin
  exact ⟨e.symm z, hz.2.2, hzf.2⟩

/-- Component non-bottom witnesses propagate through an actual variable-
dimensional coordinate germ cover to local nondegeneracy. -/
theorem locallyNondegenerate_of_component_nonbot_of_local_coordinate_psh {u : X → EReal}
    (hlocal : ∀ x : X, ∃ d : ℕ, ∃ e : OpenPartialHomeomorph X (ComplexModel d),
      x ∈ e.source ∧ SGPT.Foundations.Analysis.PlurisubharmonicOn (u ∘ e.symm) e.target)
    (hn : ∀ x : X, ∃ y ∈ connectedComponent x, u y ≠ ⊥) :
    LocallyNondegenerate u := by
  have hopen := isOpen_closure_nonbot_of_local_coordinate_psh hlocal
  intro x O hO hxO
  obtain ⟨y, hy, hyf⟩ := hn x
  have hsub : connectedComponent x ⊆ closure {z | u z ≠ ⊥} :=
    isPreconnected_connectedComponent.subset_of_closure_inter_subset hopen
      ⟨y, hy, subset_closure hyf⟩ (by simpa only [closure_closure] using
        (Set.inter_subset_left : closure {z | u z ≠ ⊥} ∩ connectedComponent x ⊆
          closure {z | u z ≠ ⊥}))
  obtain ⟨z, hzO, hzf⟩ := mem_closure_iff.mp (hsub mem_connectedComponent) O hO hxO
  exact ⟨z, hzO, hzf⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

/-- PSH germs transport across actual holomorphic atlas overlaps, without
global second countability or a chart-invariance certificate. -/
theorem plurisubharmonicAt_chart_iff (u : M → EReal) (e f : ComplexChart n M)
    (x : M) (he : x ∈ e.val.source) (hf : x ∈ f.val.source) :
    SGPT.Foundations.Analysis.PlurisubharmonicAt (chartFunction u e) (e.val x) ↔
      SGPT.Foundations.Analysis.PlurisubharmonicAt (chartFunction u f) (f.val x) := by
  have transport (a b : ComplexChart n M) (ha : x ∈ a.val.source)
      (hb : x ∈ b.val.source)
      (hu : SGPT.Foundations.Analysis.PlurisubharmonicAt (chartFunction u a) (a.val x)) :
      SGPT.Foundations.Analysis.PlurisubharmonicAt (chartFunction u b) (b.val x) := by
    let F := b.val.symm.trans a.val
    have hc : F ∈ contDiffGroupoid ∞ (𝓘(ℂ, ComplexModel n)) :=
      StructureGroupoid.compatible _ b.property a.property
    have hdiff : DifferentiableOn ℂ F F.source :=
      (contMDiffOn_of_mem_contDiffGroupoid hc).contDiffOn.differentiableOn (by simp)
    have hx : b.val x ∈ F.source := by
      refine ⟨b.val.map_source hb, ?_⟩
      change b.val.symm (b.val x) ∈ a.val.source
      simpa only [b.val.left_inv hb] using ha
    have huF : SGPT.Foundations.Analysis.PlurisubharmonicAt (chartFunction u a)
        (F (b.val x)) := by
      simpa only [F, OpenPartialHomeomorph.trans_apply, b.val.left_inv hb] using hu
    have hp :=
      SGPT.Foundations.Analysis.Pending.HolomorphicPullback.plurisubharmonicAt_comp_holomorphic
      F.open_source hdiff hx huF
    apply hp.congr
    filter_upwards [F.open_source.mem_nhds hx] with y hy
    change u (a.val.symm (a.val (b.val.symm y))) = u (b.val.symm y)
    exact congrArg u (a.val.left_inv hy.2)
  exact ⟨transport e f he hf, transport f e hf he⟩

/-- The source local PSH definition, with actual connected coordinate domains
in the holomorphic atlas. No global non-bottom witness is substituted for
local nontriviality. Empty manifolds satisfy this predicate vacuously. -/
def ManifoldPSH (u : M → EReal) : Prop :=
  ∀ x : M, ∃ e : ComplexChart n M, x ∈ e.val.source ∧
    ∃ V : Set (ComplexModel n), IsOpen V ∧ IsConnected V ∧
      V ⊆ e.val.target ∧ e.val x ∈ V ∧ PSHOn (chartFunction u e) V

/-- Source local witnesses produce PSH germs in every actual chart. -/
theorem ManifoldPSH.chartPlurisubharmonic {u : M → EReal} (hu : ManifoldPSH (n := n) u)
    (e : ComplexChart n M) :
    SGPT.Foundations.Analysis.PlurisubharmonicOn (chartFunction u e) e.val.target := by
  intro z hz
  obtain ⟨f, hf, V, hV, _, _, hzV, huV⟩ := hu (e.val.symm z)
  have he : e.val.symm z ∈ e.val.source := e.val.map_target hz
  have hp := (plurisubharmonicAt_chart_iff u f e (e.val.symm z) hf he).mp
    (huV.disc.plurisubharmonicOn hV _ hzV)
  simpa only [e.val.right_inv hz] using hp

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- The source's connected local PSH witnesses give a non-bottom point in
every actual open neighborhood. Actual positive Haar measure produces it. -/
theorem ManifoldPSH.locallyNondegenerate {u : M → EReal}
    (hu : ManifoldPSH (n := n) u) : LocallyNondegenerate u := by
  apply locallyNondegenerate_of_local_coordinate_psh
  intro x
  obtain ⟨e, hx, V, hV, hc, hVe, hz, huV⟩ := hu x
  exact ⟨n, e.val, hx, V, hV, hc, hVe, hz, huV⟩

/-- Actual chart germs and produced local nondegeneracy are equivalent to
the connected-neighborhood source definition in the fixed-dimensional atlas. -/
theorem manifoldPSH_iff_chart_and_nondegenerate {u : M → EReal} :
    ManifoldPSH (n := n) u ↔
      (∀ e : ComplexChart n M, SGPT.Foundations.Analysis.PlurisubharmonicOn
        (chartFunction u e) e.val.target) ∧ LocallyNondegenerate u := by
  constructor
  · intro hu
    exact ⟨hu.chartPlurisubharmonic, hu.locallyNondegenerate⟩
  · rintro ⟨hcharts, hnd⟩ x
    let e := complexChartAt (n := n) x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    obtain ⟨W, hW, hzW, hdisc⟩ := hcharts e (e.val x) (e.val.map_source hx)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hW.inter e.val.open_target)
      (e.val x) ⟨hzW, e.val.map_source hx⟩
    have hbe : Metric.ball (e.val x) r ⊆ e.val.target :=
      fun _ hz ↦ (hball hz).2
    have hnb := hnd.exists_chart_ne_bot e Metric.isOpen_ball hbe
      (Metric.mem_ball_self hr)
    exact ⟨e, hx, Metric.ball (e.val x) r, Metric.isOpen_ball,
      Metric.isConnected_ball hr, hbe, Metric.mem_ball_self hr,
      hdisc.mono (fun _ hz ↦ (hball hz).1), hnb⟩

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- Actual global upper bounds pull back to the actual chart target. -/
theorem locallyBounded_chartFamily {I : Type*} {u : I → M → EReal}
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range u) Set.univ) (e : ComplexChart n M) :
    LocallyUniformlyBoundedAbove (fun i ↦ chartFunction (u i) e) e.val.target := by
  intro z hz
  obtain ⟨O, hO, C, hC⟩ := hb (e.val.symm z) (Set.mem_univ _)
  rw [nhdsWithin_univ] at hO
  have hpre : e.val.symm ⁻¹' O ∈ 𝓝 z := (e.val.continuousAt_symm hz).eventually hO
  refine ⟨e.val.symm ⁻¹' O, mem_nhdsWithin_of_mem_nhds hpre, C, ?_⟩
  intro i y hy
  exact hC (u i) (Set.mem_range_self i) _ ⟨hy.1, Set.mem_univ _⟩

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- Chart representatives commute with the actual global regularized supremum. -/
theorem uscSup_chartFamily {I : Type*} (u : I → M → EReal)
    (e : ComplexChart n M) :
    EqOn (uscSup (fun i ↦ chartFunction (u i) e)) (chartFunction (uscSup u) e)
      e.val.target := by
  intro z hz
  exact SGPT.Foundations.Analysis.FirstPass.uscRegularization_chartFunction_apply
    (fun x ↦ ⨆ i, u i x) e hz

/-- The source's regularized-supremum clause on fixed-dimensional complex
manifolds, with actual local PSH witnesses and no global countability assumption. -/
theorem manifoldPSH_uscSup_of_locallyBounded {I : Type*} [Nonempty I]
    {u : I → M → EReal} (hu : ∀ i, ManifoldPSH (n := n) (u i))
    (hb : SGPT.Foundations.Analysis.FirstPass.LocallyUniformlyBoundedAbove
      (Set.range u) Set.univ) : ManifoldPSH (n := n) (uscSup u) := by
  classical
  apply manifoldPSH_iff_chart_and_nondegenerate.mpr
  constructor
  · intro e
    have hpsh : ∀ f ∈ Set.range (fun i ↦ chartFunction (u i) e),
        SGPT.Foundations.Analysis.PlurisubharmonicOn f e.val.target := by
      rintro f ⟨i, rfl⟩
      exact (hu i).chartPlurisubharmonic e
    have hr := SGPT.Foundations.Analysis.FirstPass.plurisubharmonicOn_uscRegularization_sSup
      e.val.open_target (Set.range_nonempty (fun i ↦ chartFunction (u i) e)) hpsh
      (locallyUniformlyBoundedAbove_range_iff.mpr (locallyBounded_chartFamily hb e))
    rw [sSup_range_eq] at hr
    exact (hr.discPshOn.congr (uscSup_chartFamily u e)).plurisubharmonicOn e.val.open_target
  · apply (hu (Classical.arbitrary I)).locallyNondegenerate.mono
    intro x
    exact (le_iSup (fun i ↦ u i x) (Classical.arbitrary I)).trans
      (SGPT.Foundations.Analysis.FirstPass.le_uscRegularization (fun y ↦ ⨆ i, u i y) x)

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- For actual chart PSH germs, the closure of the non-bottom locus is open.
Chart-local integrability propagates to its actual limit points, and positive
Haar measure supplies finite points in every coordinate neighborhood. -/
theorem isOpen_closure_nonbot_of_chart_psh {u : M → EReal}
    (hcharts : ∀ e : ComplexChart n M, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (chartFunction u e) e.val.target) : IsOpen (closure {x | u x ≠ ⊥}) := by
  apply isOpen_closure_nonbot_of_local_coordinate_psh
  intro x
  let e := complexChartAt (n := n) x
  exact ⟨n, e.val, mem_complexChartAt_source x, hcharts e⟩

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- The source non-bottom witness on every actual connected component
produces the local nondegeneracy needed by the source manifold definition. -/
theorem locallyNondegenerate_of_component_nonbot_of_chart_psh {u : M → EReal}
    (hcharts : ∀ e : ComplexChart n M, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (chartFunction u e) e.val.target)
    (hn : ∀ x : M, ∃ y ∈ connectedComponent x, u y ≠ ⊥) :
    LocallyNondegenerate u := by
  apply locallyNondegenerate_of_component_nonbot_of_local_coordinate_psh _ hn
  intro x
  let e := complexChartAt (n := n) x
  exact ⟨n, e.val, mem_complexChartAt_source x, hcharts e⟩

/-- Source decreasing-net stability on the actual fixed-dimensional
manifold, with precisely the original componentwise non-bottom premise. -/
theorem manifoldPSH_iInf_of_antitone {I : Type*} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] {u : I → M → EReal} (hu : ∀ i, ManifoldPSH (n := n) (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x))
    (hn : ∀ x : M, ∃ y ∈ connectedComponent x, (⨅ i, u i y) ≠ ⊥) :
    ManifoldPSH (n := n) (fun x ↦ ⨅ i, u i x) := by
  have hcharts : ∀ e : ComplexChart n M, SGPT.Foundations.Analysis.PlurisubharmonicOn
      (chartFunction (fun x ↦ ⨅ i, u i x) e) e.val.target := by
    intro e
    have hd := discPshOn_iInf_of_antitone
      (fun i ↦ ((hu i).chartPlurisubharmonic e).discPshOn)
      (fun z _ ↦ hanti (e.val.symm z))
    exact hd.plurisubharmonicOn e.val.open_target
  exact manifoldPSH_iff_chart_and_nondegenerate.mpr
    ⟨hcharts, locallyNondegenerate_of_component_nonbot_of_chart_psh hcharts hn⟩

/-- Local `L¹` convergence of the original net in every actual connected
coordinate neighborhood. The required non-bottom points are produced from
the source component premise; no local integrability certificate is assumed. -/
theorem tendsto_manifold_chartLocalL1_iInf {I : Type*} [Preorder I] [IsDirectedOrder I]
    [Nonempty I] {u : I → M → EReal} (hu : ∀ i, ManifoldPSH (n := n) (u i))
    (hanti : ∀ x, Antitone (fun i ↦ u i x))
    (hn : ∀ x : M, ∃ y ∈ connectedComponent x, (⨅ i, u i y) ≠ ⊥)
    (e : ComplexChart n M) {W K : Set (ComplexModel n)}
    (hW : IsOpen W) (hconn : IsConnected W) (hWe : W ⊆ e.val.target)
    (μ : Measure (ComplexModel n)) [μ.IsAddHaarMeasure]
    (hK : IsCompact K) (hKW : K ⊆ W) :
    Tendsto (fun i ↦ ∫ z in K, ‖(u i (e.val.symm z)).toReal -
      (⨅ j, u j (e.val.symm z)).toReal‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨z, hz⟩ := hconn.nonempty
  have hfamily (i : I) : PSHOn (chartFunction (u i) e) W :=
    ⟨((hu i).chartPlurisubharmonic e).discPshOn.mono hWe,
      (hu i).locallyNondegenerate.exists_chart_ne_bot e hW hWe hz⟩
  have hlimit := manifoldPSH_iInf_of_antitone hu hanti hn
  have hnb := hlimit.locallyNondegenerate.exists_chart_ne_bot e hW hWe hz
  exact tendsto_localL1_iInf hfamily hW hconn.isPreconnected
    (fun z _ ↦ hanti (e.val.symm z)) hnb μ hK hKW

end SGPT.PSH
