/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2ArcHomotopy
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks

/-!
# A two-spoke region path is an arc

For Case 1 of XII (2.1), page 244, a visit with different boundary
vertices uses two different radial edges. Their closures meet only
at the region hub. Concatenating the injective spoke parameterizations
therefore gives an injective path. Its interior stays in the region
when both spokes have their positive parts there.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Concatenate two injective paths which meet only at the prescribed
joining endpoint. -/
theorem path_trans_injective_of_only_join
    {X : Type*} [TopologicalSpace X] {a b c : X} (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t, p s = q t → s = 1 ∧ t = 0) : Function.Injective (p.trans q) := by
  intro s t heq
  by_cases hs : s.val ≤ 1 / 2 <;> by_cases ht : t.val ≤ 1 / 2
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte] at heq
    have h := congrArg Subtype.val (hp heq)
    apply Subtype.ext
    dsimp only at h
    linarith
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte] at heq
    have h := congrArg Subtype.val (hcross _ _ heq).2
    change 2 * t.val - 1 = 0 at h
    exact (ht (by linarith)).elim
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte] at heq
    have h := congrArg Subtype.val (hcross _ _ heq.symm).2
    change 2 * s.val - 1 = 0 at h
    exact (hs (by linarith)).elim
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte] at heq
    have h := congrArg Subtype.val (hq heq)
    apply Subtype.ext
    dsimp only at h
    linarith

/-- Two spokes to one hub, from distinct drawing vertices, form an
injective two-edge path. Their closures can meet only at the hub. -/
theorem spoke_pair_path_injective
    {S : Type*} [TopologicalSpace S] {K : Drawing S}
    {e e' : Set S} {u v w : S} (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hends : closure e ∩ K.V = {u, w}) (hends' : closure e' ∩ K.V = {v, w})
    (huv : u ≠ v) (huw : u ≠ w)
    (p : Path u w) (q : Path v w) (hp : Function.Injective p) (hq : Function.Injective q)
    (hpr : range p = closure e) (hqr : range q = closure e') :
    Function.Injective (p.trans q.symm) := by
  have hee : e ≠ e' := by
    intro heq
    have hu : u ∈ closure e' ∩ K.V := by
      rw [← heq, hends]
      exact Or.inl rfl
    rw [hends'] at hu
    rcases hu with hu | hu
    · exact huv hu
    · exact huw hu
  have hcross : ∀ s t, p s = q t → s = 1 ∧ t = 1 := by
    intro s t heq
    have hxE : p s ∈ closure e := hpr ▸ mem_range_self s
    have hxE' : p s ∈ closure e' := heq.symm ▸ (hqr ▸ mem_range_self t)
    have hxV : p s ∈ K.V := by
      by_contra hn
      have hxe : p s ∈ e := K.closure_diff_V he ▸ ⟨hxE, hn⟩
      have hxe' : p s ∈ e' := K.closure_diff_V he' ▸ ⟨hxE', hn⟩
      exact hee (K.edge_eq_of_mem he he' hxe hxe')
    have hxw : p s = w := by
      have hx : p s ∈ ({u, w} : Set S) := hends ▸ ⟨hxE, hxV⟩
      rcases hx with hx | hx
      · have hx' : u ∈ ({v, w} : Set S) := hx ▸ (hends' ▸ ⟨hxE', hxV⟩)
        rcases hx' with h | h
        · exact (huv h).elim
        · exact (huw h).elim
      · exact hx
    exact ⟨hp (hxw.trans p.target.symm), hq (heq.symm.trans (hxw.trans q.target.symm))⟩
  have hqs : Function.Injective q.symm := by
    intro s t heq
    have h := hq heq
    have h' := congrArg unitInterval.symm h
    simpa only [unitInterval.symm_symm] using h'
  apply path_trans_injective_of_only_join p q.symm hp hqs
  intro s t heq
  obtain ⟨hs, ht⟩ := hcross s (unitInterval.symm t) heq
  refine ⟨hs, ?_⟩
  have h := congrArg unitInterval.symm ht
  simpa only [unitInterval.symm_symm, unitInterval.symm_one] using h

/-- Two distinct parallel spokes form a simple closed traversal:
its only repeated parameter pair is the initial and final endpoint.
Hence it is injective on its half-open parameter interval. -/
theorem parallel_spoke_pair_path_halfopen_injective
    {S : Type*} [TopologicalSpace S] {K : Drawing S}
    {e e' : Set S} {u w : S} (he : e ∈ K.E) (he' : e' ∈ K.E) (hee : e ≠ e')
    (hends : closure e ∩ K.V = {u, w})
    (p q : Path u w) (hp : Function.Injective p) (hq : Function.Injective q)
    (hpr : range p = closure e) (hqr : range q = closure e') :
    InjOn (p.trans q.symm) (Ico (0 : unitInterval) 1) := by
  have hcross : ∀ s t, p s = q t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t heq
    have hxE : p s ∈ closure e := hpr ▸ mem_range_self s
    have hxE' : p s ∈ closure e' := heq.symm ▸ (hqr ▸ mem_range_self t)
    have hxV : p s ∈ K.V := by
      by_contra hn
      have hxe : p s ∈ e := K.closure_diff_V he ▸ ⟨hxE, hn⟩
      have hxe' : p s ∈ e' := K.closure_diff_V he' ▸ ⟨hxE', hn⟩
      exact hee (K.edge_eq_of_mem he he' hxe hxe')
    have hx : p s ∈ ({u, w} : Set S) := hends ▸ ⟨hxE, hxV⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hp (hx.trans p.source.symm), hq (heq.symm.trans (hx.trans q.source.symm))⟩
    · exact Or.inr ⟨hp (hx.trans p.target.symm), hq (heq.symm.trans (hx.trans q.target.symm))⟩
  intro s hs t ht heq
  rcases joined_loop_eq p q hp hq hcross heq with h | h | h
  · exact h
  · exact ((ne_of_lt ht.2) h.2).elim
  · exact ((ne_of_lt hs.2) h.1).elim

/-- The interior of a two-spoke path stays in the region if the
positive part of each spoke stays there. -/
theorem spoke_pair_path_interior_subset
    {S : Type*} [TopologicalSpace S] {u v w : S} (p : Path u w) (q : Path v w)
    {r : Set S} (hp : ∀ t, 0 < t.val → p t ∈ r) (hq : ∀ t, 0 < t.val → q t ∈ r) :
    ∀ t ∈ Ioo (0 : unitInterval) 1, (p.trans q.symm) t ∈ r := by
  intro t ht
  rw [Path.trans_apply]
  split_ifs with h
  · apply hp
    change 0 < 2 * t.val
    have ht0 : 0 < t.val := ht.1
    linarith
  · apply hq
    change 0 < 1 - (2 * t.val - 1)
    have ht1 : t.val < 1 := ht.2
    linarith

end GraphMinor.GM12
