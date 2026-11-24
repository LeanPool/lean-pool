/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ManifoldPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition

/-!
# Finite unions and quasi-PSH pole sets

Finite unions of locally pluripolar sets are handled by adding local PSH
witnesses on a common ball.  Pole sets of globally nondegenerate quasi-PSH
potentials are handled by their local PSH-plus-smooth decompositions.  No
arbitrary global measure or product is assumed here.
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Foundations.Analysis.Pending

/-- Finite unions of locally pluripolar sets are locally pluripolar.  On a
common ball, the sum of the two local PSH witnesses has the required pole set.
Its nontriviality follows by choosing a point where both summands are finite,
using Haar almost-everywhere finiteness and positivity of the ball. -/
theorem manifoldLocallyPluripolar_union
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {S T : Set M}
    (hS : ManifoldLocallyPluripolar (n := n) S)
    (hT : ManifoldLocallyPluripolar (n := n) T) :
    ManifoldLocallyPluripolar (n := n) (S ∪ T) := by
  intro e z hz
  obtain ⟨V, v, hVo, hzV, hVc, hv, hvne, hvpole⟩ := hS e z hz
  obtain ⟨W, w, hWo, hzW, hWc, hw, hwne, hwpole⟩ := hT e z hz
  have hVW : V ∩ W ∈ 𝓝 z :=
    inter_mem (hVo.mem_nhds hzV) (hWo.mem_nhds hzW)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hVW
  let B : Set (ComplexModel n) := ball z r
  have hBV : B ⊆ V := fun y hy => (hrsub hy).1
  have hBW : B ⊆ W := fun y hy => (hrsub hy).2
  have hvae : ∀ᵐ y ∂volume.restrict B, v y ≠ ⊤ ∧ v y ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hBV (hv.ae_finite volume hVc hvne)
  have hwae : ∀ᵐ y ∂volume.restrict B, w y ≠ ⊤ ∧ w y ≠ ⊥ :=
    ae_restrict_of_ae_restrict_of_subset hBW (hw.ae_finite volume hWc hwne)
  obtain ⟨a, haB, hva, hwa⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (μ := volume) (Metric.measure_ball_pos volume z hr).ne' (hvae.and hwae)
  refine ⟨B, (fun y => v y + w y), isOpen_ball, mem_ball_self hr,
    (convex_ball z r).isPreconnected, (hv.mono hBV).add (hw.mono hBW),
    ⟨a, haB, EReal.add_ne_bot_iff.mpr ⟨hva.2, hwa.2⟩⟩, ?_⟩
  rintro y hyB hyST
  rcases hyST.2 with hyS | hyT
  · change v y + w y = ⊥
    rw [hvpole y (hBV hyB) ⟨hyST.1, hyS⟩]
    exact EReal.bot_add _
  · change v y + w y = ⊥
    rw [hwpole y (hBW hyB) ⟨hyST.1, hyT⟩]
    exact EReal.add_bot _

/-- Quasi-everywhere predicates are closed under conjunction. -/
theorem quasiEverywhere_and
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {P Q : M → Prop}
    (hP : QuasiEverywhere (n := n) P) (hQ : QuasiEverywhere (n := n) Q) :
    QuasiEverywhere (n := n) (fun x => P x ∧ Q x) := by
  classical
  apply (manifoldLocallyPluripolar_union hP hQ).mono
  intro x hx
  by_cases hp : P x
  · exact Or.inr (fun hq => hx ⟨hp, hq⟩)
  · exact Or.inl hp

theorem quasiEverywhereEq_trans
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {Y : Type*} {f g h : M → Y}
    (hfg : QuasiEverywhereEq (n := n) f g) (hgh : QuasiEverywhereEq (n := n) g h) :
    QuasiEverywhereEq (n := n) f h :=
  (quasiEverywhere_and hfg hgh).mono (fun _ hx => hx.1.trans hx.2)

/-- The pole set of a nondegenerate global quasi-PSH potential is locally
pluripolar.  A local quasi-PSH decomposition supplies the PSH witness, while
global local nondegeneracy gives a non-pole point after shrinking to a chart
ball. -/
theorem quasiPsh_poles_manifoldLocallyPluripolar
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) :
    ManifoldLocallyPluripolar (n := n) {x | u x = ⊥} := by
  intro e z hz
  obtain ⟨p, g, hp, _, heq⟩ := hu.1 e z hz
  obtain ⟨D, hDo, hzD, hpD⟩ := hp
  have hnbhd : {y | y ∈ D ∧ y ∈ e.val.target ∧
      chartFunction u e y = p y + (g y : EReal)} ∈ 𝓝 z := by
    filter_upwards [hDo.mem_nhds hzD, e.val.open_target.mem_nhds hz, heq]
      with y hyD hyt hyEq
    exact ⟨hyD, hyt, hyEq⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  let B : Set (ComplexModel n) := ball z r
  have hBD : B ⊆ D := fun y hy => (hrsub hy).1
  have hBtarget : B ⊆ e.val.target := fun y hy => (hrsub hy).2.1
  have hpB : PlurisubharmonicOn p B :=
    (hpD.mono hBD).plurisubharmonicOn isOpen_ball
  let O : Set M := e.val.source ∩ e.val ⁻¹' B
  have hOo : IsOpen O := e.val.isOpen_inter_preimage isOpen_ball
  have hzO : e.val.symm z ∈ O := by
    refine ⟨e.val.symm.map_source hz, ?_⟩
    change e.val (e.val.symm z) ∈ B
    rw [e.val.right_inv hz]
    exact mem_ball_self hr
  obtain ⟨x, hxO, hxne⟩ := hu.2 (e.val.symm z) O hOo hzO
  have hexne : chartFunction u e (e.val x) ≠ ⊥ := by
    simpa [chartFunction, e.val.left_inv hxO.1] using hxne
  have hpx : p (e.val x) ≠ ⊥ := by
    intro hpxbot
    apply hexne
    rw [(hrsub hxO.2).2.2, hpxbot]
    exact EReal.bot_add _
  refine ⟨B, p, isOpen_ball, mem_ball_self hr, (convex_ball z r).isPreconnected,
    hpB, ⟨e.val x, hxO.2, hpx⟩, ?_⟩
  intro y hyB hypole
  have hrawbot : chartFunction u e y = ⊥ := by
    exact hypole.2
  have hsum : p y + (g y : EReal) = ⊥ :=
    (hrsub hyB).2.2.symm.trans hrawbot
  exact (EReal.add_eq_bot_iff.mp hsum).resolve_right (EReal.coe_ne_bot _)

/-- Nondegenerate quasi-PSH potentials are finite quasi-everywhere, using their
actual pole set rather than a toReal representative. -/
theorem quasiPsh_finite_quasiEverywhere
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) :
    QuasiEverywhere (n := n) (fun x => u x ≠ ⊥ ∧ u x ≠ ⊤) := by
  have h : QuasiEverywhere (n := n) (fun x => u x ≠ ⊥) := by
    simpa only [QuasiEverywhere, not_not] using
      quasiPsh_poles_manifoldLocallyPluripolar hu
  exact h.mono (fun x hx => ⟨hx, hu.1.ne_top x⟩)

end SGPT.Foundations.Analysis.Pending
