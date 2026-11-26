/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2NormalEntry
public import LeanPool.GraphMinor.GM12.Section2LeafEntryExistence

/-!
# Entry and exit edges for every normal approach

The omitted assertion in the trace definition on XII page 243 holds
at every vertex of a nondegenerate 2-cell drawing. Such a vertex has
an incident edge. If it has two or more half-edges, use its entering
sector. Otherwise it has exactly one half-edge and the proved leaf
patch applies. Reversing the real parameter gives the exit assertion.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Every continuous approach through one region has an entering
radial edge. This proves existence in the omitted lemma on XII page 243,
including the leaf case. -/
theorem exists_entersLike
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r : Set S} (hr : r ∈ Γ.R)
    {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃ e ∈ K.E, EntersLike f a c e r v w := by
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  by_cases h2 : 2 ≤ Nat.card (halfEdges Γ γ v)
  · exact exists_entersLike_of_two_halfEdges hS hrad hmax hE hγ hv h2 hr hw hwV hf hac hfc hinside
  · obtain ⟨e, he, hvcl⟩ := exists_edge_at hrad hS hE hv
    obtain ⟨b, hb⟩ := exists_end_eq hγ he hv hvcl
    let : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
    let : Nonempty (halfEdges Γ γ v) := ⟨⟨(e, b), he, hb⟩⟩
    have hpos : 0 < Nat.card (halfEdges Γ γ v) := Nat.card_pos
    have hcard : Nat.card (halfEdges Γ γ v) = 1 := by omega
    exact exists_entersLike_of_one_halfEdge hS hrad hmax hE hγ hv hcard hr hw hwV hf hac hfc hinside

/-- Reversing the real parameter gives the leaving edge in the
omitted trace-definition lemma of XII, page 243. -/
theorem exists_leavesLike
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r : Set S} (hr : r ∈ Γ.R)
    {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfa : f a = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃ e ∈ K.E, LeavesLike f a c e r v w := by
  change ∃ e ∈ K.E, EntersLike (fun t => f (-t)) (-c) (-a) e r v w
  apply exists_entersLike hS hrad hmax hE hv hr hw hwV
    (hf.comp continuous_neg) (by linarith : -c < -a)
  · simpa only [Function.comp_apply, neg_neg] using hfa
  · intro t ht
    apply hinside
    constructor <;> linarith [ht.1, ht.2]

end GraphMinor.GM12
