/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceConstruction
import LeanPool.GraphMinor.GM12.Section2HitOrder
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM12.Section2Zero

/-!
# Existence of traces for every normal finite-length curve

For XII's trace definition on page 243, order the hits in one closed
real period starting at a hit. Their number is the curve length plus
one, so the construction over consecutive intervals has twice the
curve length as its number of edges. Periodicity closes the walk.
Zero-length curves use their region's radial hub.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Every normal finite-length curve has a trace in the radial drawing.
This proves trace existence in XII, page 243, including the
exact length and real-parameter conditions in `IsTrace`. -/
theorem exists_trace {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) :
    ∃ (u : S) (W : GraphWalk K.toGraph u u), IsTrace Γ K φ W := by
  by_cases hzero : curveLength Γ φ = 0
  · exact exists_trace_of_length_zero hK hφ hzero
  have hpos : 0 < curveLength Γ φ := Nat.pos_of_ne_zero hzero
  obtain ⟨z, hz⟩ := (Set.ncard_pos hφ.1).mp hpos
  obtain ⟨a, _, haz⟩ := (circle_parameter_bijOn 0).surjOn (mem_univ z)
  have haU : periodicCurve φ a ∈ Γ.U := by
    change φ (Circle.exp (2 * Real.pi * a)) ∈ Γ.U
    change Circle.exp (2 * Real.pi * a) = z at haz
    rw [haz]
    exact hz
  let H : Set ℝ := {s | s ∈ Icc a (a + 1) ∧ periodicCurve φ s ∈ Γ.U}
  obtain ⟨hH, hHcard⟩ := periodicCurve_closed_hits hφ haU
  have hperiod : periodicCurve φ (a + 1) = periodicCurve φ a := periodicCurve_periodic φ a
  have haH : a ∈ H := ⟨⟨le_rfl, by linarith⟩, haU⟩
  have hbH : a + 1 ∈ H := ⟨⟨by linarith, le_rfl⟩, hperiod.symm ▸ haU⟩
  obtain ⟨n, t, ht, ht0, htlast, htrange, hcard⟩ :=
    exists_ordered_interval_enumeration hH (fun _ hs => hs.1) haH hbH
  have hΓ : ∀ i, periodicCurve φ (t i) ∈ Γ.V := by
    intro i
    have hiH : t i ∈ H := by
      change t i ∈ {s | s ∈ Icc a (a + 1) ∧ periodicCurve φ s ∈ Γ.U}
      rw [← htrange]
      exact mem_range_self i
    exact hφ.2 ⟨mem_range_self _, hiH.2⟩
  have hcover : ∀ s ∈ Icc (t 0) (t (Fin.last n)), periodicCurve φ s ∈ Γ.U → s ∈ range t := by
    intro s hs hsU
    rw [ht0, htlast] at hs
    have hsH : s ∈ H := ⟨hs, hsU⟩
    exact htrange.symm ▸ hsH
  have hn : n = curveLength Γ φ := by omega
  have hpre : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hex := exists_traceSteps_of_enumerated_hits hS hpre hK.2.2 hE
    (periodicCurve_continuous φ) t ht hΓ hcover
  have hclosed : ∃ W : GraphWalk K.toGraph (periodicCurve φ a) (periodicCurve φ a),
      TraceSteps Γ K (periodicCurve φ) a (a + 1) W ∧ W.length = 2 * curveLength Γ φ := by
    obtain ⟨W, hW, hlen⟩ := hex
    have hlen' : W.length = 2 * curveLength Γ φ := hlen.trans (congrArg (fun n => 2 * n) hn)
    have hex' : ∃ W : GraphWalk K.toGraph (periodicCurve φ (t 0)) (periodicCurve φ (t
      (Fin.last n))),
        TraceSteps Γ K (periodicCurve φ) (t 0) (t (Fin.last n)) W ∧
          W.length = 2 * curveLength Γ φ := ⟨W, hW, hlen'⟩
    rw [ht0, htlast, hperiod] at hex'
    exact hex'
  obtain ⟨W, hW, hlength⟩ := hclosed
  exact ⟨periodicCurve φ a, W, hφ, Or.inr ⟨hpos, hlength, a, hW⟩⟩

end GraphMinor.GM12
