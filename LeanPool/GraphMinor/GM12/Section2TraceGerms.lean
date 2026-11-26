/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceParameters
import LeanPool.GraphMinor.GM12.Section2TraceReverse
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks

/-!
# The two region germs at a trace vertex parameter

For XII (2.1), pages 243--244, each parameter over a drawing vertex
has a recorded region visit on either side within the trace interval.
Locate the incoming visit by removing earlier visits. Reversing the
walk locates the outgoing visit. The endpoints of the whole interval
need only the side which lies inside that interval.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A noninitial vertex parameter has an incoming recorded region
interval and its entry edge belongs to the trace. -/
theorem traceSteps_exists_incoming_germ
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W)
    {s : ℝ} (hs : s ∈ Ioc a b) (hfs : f s ∈ Γ.V) :
    ∃ (d : ℝ) (w : S) (r e : Set S),
      a ≤ d ∧ d < s ∧ w ∈ K.V ∧ r ∈ Γ.R ∧ w ∈ r ∧ e ∈ W.edges ∧
      (∀ t ∈ Ioo d s, f t ∈ r) ∧ EntersLike f d s e r (f s) w := by
  cases hWcase : W with
  | nil hu =>
    rw [hWcase] at hW
    exact (not_lt_of_ge (hs.2.trans_eq hW.1.symm) hs.1).elim
  | cons hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hu => rw [hrestcase] at hW; exact hW.elim
    | @cons _ x _ e hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, _, henter, htail⟩ := hW
      have hcs : c ≤ s := by
        by_contra hn
        exact region_subset hr (hfr s ⟨hs.1, lt_of_not_ge hn⟩) (Γ.V_subset_U hfs)
      by_cases hsc : s = c
      · subst s
        refine ⟨a, _, r, e, le_rfl, hac, hwK, hr, hwr, ?_, hfr, ?_⟩
        · simp only [GraphWalk.edges, List.mem_cons]
          exact Or.inr (Or.inl trivial)
        · simpa only [hfc] using henter
      · obtain ⟨d, w, r, e, hcd, hds, hw, hr, hwr, he, hfr, henter⟩ :=
          traceSteps_exists_incoming_germ tail htail
            ⟨lt_of_le_of_ne hcs (Ne.symm hsc), hs.2⟩ hfs
        refine ⟨d, w, r, e, hac.le.trans hcd, hds, hw, hr, hwr, ?_, hfr, henter⟩
        simp only [GraphWalk.edges, List.mem_cons]
        exact Or.inr (Or.inr he)
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- A nonterminal vertex parameter has an outgoing recorded region
interval and its leaving edge belongs to the trace. -/
theorem traceSteps_exists_outgoing_germ
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W)
    {s : ℝ} (hs : s ∈ Ico a b) (hfs : f s ∈ Γ.V) :
    ∃ (d : ℝ) (w : S) (r e : Set S),
      d ≤ b ∧ s < d ∧ w ∈ K.V ∧ r ∈ Γ.R ∧ w ∈ r ∧ e ∈ W.edges ∧
      (∀ t ∈ Ioo s d, f t ∈ r) ∧ LeavesLike f s d e r (f s) w := by
  obtain ⟨d, w, r, e, hbd, hds, hw, hr, hwr, he, hfr, hentry⟩ :=
    traceSteps_exists_incoming_germ W.reverse (traceSteps_reverse W hW)
      (s := -s) ⟨neg_lt_neg hs.2, neg_le_neg hs.1⟩ (by simpa only [neg_neg] using hfs)
  refine ⟨-d, w, r, e, ?_, ?_, hw, hr, hwr, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · simpa only [GraphWalk.edges_reverse, List.mem_reverse] using he
  · intro t ht
    simpa only [neg_neg] using hfr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · simpa only [LeavesLike, neg_neg] using hentry

end GraphMinor.GM12
