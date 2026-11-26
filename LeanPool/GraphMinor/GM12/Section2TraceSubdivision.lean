/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceParameters
public import LeanPool.GraphMinor.GM12.Section2HitOrder
import LeanPool.GraphMinor.GM12.Section2RegionIntervals
import LeanPool.GraphMinor.GM12.Section2PeriodicHits

/-!
# Extracting the cyclic region subdivision of a trace

For XII (2.1), Case 1, page 244, enumerate the drawing hits in the
closed real period already used by the trace. Its endpoints are hits,
and only the last repeats a circle parameter. Consecutive hits bound
normal intervals in single regions. This gives the ordered subdivision,
its length, and its region labels while retaining the original trace.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A positive-length trace supplies an ordered cyclic list of vertex
parameters and the regions of all successive intervals. -/
theorem exists_trace_subdivision
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S}
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hpos : 0 < curveLength Γ φ) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ) (r : Fin n → Set S),
      0 < n ∧ StrictMono t ∧ t (Fin.last n) = t 0 + 1 ∧ n = curveLength Γ φ ∧
      (∀ i, periodicCurve φ (t i) ∈ Γ.V) ∧
      TraceSteps Γ K (periodicCurve φ) (t 0) (t 0 + 1) W ∧
      (∀ i, r i ∈ Γ.R) ∧
      ∀ i s, s ∈ Ioo (t i.castSucc) (t i.succ) → periodicCurve φ s ∈ r i := by
  rcases hW.2 with ⟨hzero, _⟩ | ⟨_, _, a, hsteps⟩
  · exact (not_lt_of_ge hzero.le hpos).elim
  · have haU : periodicCurve φ a ∈ Γ.U :=
      Γ.V_subset_U ((traceSteps_parameters W hsteps).2.1.symm ▸ (traceSteps_parameters W
        hsteps).2.2.1)
    let H : Set ℝ := {s | s ∈ Icc a (a + 1) ∧ periodicCurve φ s ∈ Γ.U}
    obtain ⟨hH, hHcard⟩ := periodicCurve_closed_hits hW.1 haU
    have hperiod : periodicCurve φ (a + 1) = periodicCurve φ a := periodicCurve_periodic φ a
    have haH : a ∈ H := ⟨⟨le_rfl, by linarith⟩, haU⟩
    have hbH : a + 1 ∈ H := ⟨⟨by linarith, le_rfl⟩, hperiod.symm ▸ haU⟩
    obtain ⟨n, t, ht, ht0, htlast, htrange, hcard⟩ :=
      exists_ordered_interval_enumeration hH (fun _ hs => hs.1) haH hbH
    have hΓ : ∀ i, periodicCurve φ (t i) ∈ Γ.V := by
      intro i
      have hiH : t i ∈ H := htrange.subset (mem_range_self i)
      exact hW.1.2 ⟨mem_range_self _, hiH.2⟩
    have hcover : ∀ s ∈ Icc (t 0) (t (Fin.last n)), periodicCurve φ s ∈ Γ.U → s ∈ range t := by
      intro s hs hsU
      rw [ht0, htlast] at hs
      exact htrange.symm ▸ (show s ∈ H from ⟨hs, hsU⟩)
    have hregions : ∀ i : Fin n, ∃ r ∈ Γ.R,
        ∀ s ∈ Ioo (t i.castSucc) (t i.succ), periodicCurve φ s ∈ r := by
      intro i
      exact exists_region_of_open_interval (periodicCurve_continuous φ) (ht i.castSucc_lt_succ)
        (no_hit_between_consecutive_parameters t ht hcover i)
    choose r hr hfr using hregions
    have hlength : n = curveLength Γ φ := by omega
    refine ⟨n, t, r, hlength.symm ▸ hpos, ht, ?_, hlength, hΓ, ?_, hr, hfr⟩
    · rw [ht0, htlast]
    · simpa only [ht0] using hsteps

end GraphMinor.GM12
