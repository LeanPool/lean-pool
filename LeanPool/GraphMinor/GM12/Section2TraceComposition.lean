/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM12.Section2EntryEnds
public import LeanPool.GraphMinor.GM11.Walks

/-!
# Concatenating trace intervals

The trace construction in XII, page 243, appends the two radial edges
for each region interval. Trace steps concatenate whenever their real
parameter intervals meet. The proof removes the first two edges of
the first sequence and appends to its remaining sequence.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Concatenate trace steps on adjacent real parameter intervals. -/
theorem traceSteps_append {S : Type*} [TopologicalSpace S]
    {Γ K : Drawing S} {f : ℝ → S} {a b c : ℝ} {u v w : S}
    (W : GraphWalk K.toGraph u v) (W' : GraphWalk K.toGraph v w)
    (hW : TraceSteps Γ K f a b W) (hW' : TraceSteps Γ K f b c W') :
    TraceSteps Γ K f a c (W.append W') := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    have hab : a = b := hW.1
    exact hab.symm ▸ hW'
  | cons hl rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hW; exact hW.elim
    | cons hl₂ rest =>
      rw [hrestcase] at hW
      obtain ⟨d, had, hfa, hu, hfd, hwK, r, hr, hwr, hfr, hleave, henter, ht⟩ := hW
      exact ⟨d, had, hfa, hu, hfd, hwK, r, hr, hwr, hfr, hleave, henter,
        traceSteps_append rest W' ht hW'⟩
termination_by W.length
decreasing_by
  rw [hWcase, hrestcase]
  simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- Construct the two radial edges of a trace for one region interval
from the entry and exit witnesses of XII, page 243. -/
theorem exists_traceSteps_two_edges {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : GM11.PreRad (.drawing Γ) K) {f : ℝ → S} {a c : ℝ} (hac : a < c)
    {u x w : S} (hfa : f a = u) (hu : u ∈ Γ.V) (hfc : f c = x) (hx : x ∈ Γ.V)
    {r e e' : Set S} (hr : r ∈ Γ.R) (hw : w ∈ r) (hwK : w ∈ K.V)
    (hfr : ∀ t ∈ Ioo a c, f t ∈ r) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hleave : LeavesLike f a c e r u w) (henter : EntersLike f a c e' r x w) :
    ∃ W : GraphWalk K.toGraph u x,
      TraceSteps Γ K f a c W ∧ W.length = 2 ∧ W.edges = [e, e'] ∧ W.support = [u, w, x] := by
  have hl := leavesLike_isLink hS hrad hr hu hw hwK he hfa hleave
  have hl' := entersLike_isLink hS hrad hr hx hw hwK he' hfc henter
  let W : GraphWalk K.toGraph u x := .cons hl (.cons hl'.symm (.nil hl'.left_mem))
  refine ⟨W, ?_, rfl, rfl, rfl⟩
  exact ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hw, hfr, hleave, henter, rfl, hfc, hx⟩

end GraphMinor.GM12
