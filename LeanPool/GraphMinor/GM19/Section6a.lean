/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Epstein
public import LeanPool.GraphMinor.GM19.Conditional
public import LeanPool.GraphMinor.GM19.Cited
public import LeanPool.GraphMinor.GM19.Section4c
public import LeanPool.GraphMinor.GM20.Draw10
import LeanPool.GraphMinor.Surface.OpenDisc

/-!
# Graph Minors XIX, (6.4)

XIX quotes (6.4) from Graph Minors VII, (9.2), which is about digraphs and `α(G)`. This file does
the
translation. We give the edges of `H` and of `G` any direction (`exists_directed`), a minor of
digraphs is an enlargement (`isEnlargement_of_minor`), and `rep(G) ≤ α(G)` (`le_alpha_of_le_rep`).
The deductions that use later proofs are in `Section6aProved`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- The ends of an edge are the vertices in its closure. -/
theorem tilde_eq_inter_V (G : Drawing S) {e : Set S} (he : e ∈ G.E) :
    tilde e = closure e ∩ G.V := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    by_contra hV
    exact hx.2 (by rw [← G.closure_diff_V he]; exact ⟨hx.1, hV⟩)
  · intro hx
    exact ⟨hx.1, fun hxe ↦ (he.2.1 hxe).2 hx.2⟩

omit [T1Space S] in
/-- Every drawing in a nonempty space has a direction on each edge. -/
theorem exists_directed [Nonempty S] (G : Drawing S) : ∃ D : SurfaceDigraph S, D.G = G := by
  have key : ∀ e : Set S, ∃ a b : S, e ∈ G.E → a ∈ G.V ∧ b ∈ G.V ∧ ({a, b} : Set S) = tilde e := by
    intro e
    by_cases he : e ∈ G.E
    · have hE : closure e ∩ G.V ⊆ G.V := inter_subset_right
      rcases G.edge_cond e he with ⟨u, v, -, h, -⟩ | ⟨u, h, -⟩
      · refine ⟨u, v, fun _ ↦ ?_⟩
        rw [tilde_eq_inter_V G he, h]
        exact ⟨hE (by rw [h]; simp), hE (by rw [h]; simp), rfl⟩
      · refine ⟨u, u, fun _ ↦ ?_⟩
        rw [tilde_eq_inter_V G he, h]
        exact ⟨hE (by rw [h]; simp), hE (by rw [h]; simp), by simp⟩
    · exact ⟨Classical.arbitrary S, Classical.arbitrary S, fun h ↦ absurd h he⟩
  choose a b h using key
  exact ⟨⟨G, a, b, fun e he ↦ (h e he).1, fun e he ↦ (h e he).2.1, fun e he ↦ (h e he).2.2⟩, rfl⟩

omit [T1Space S] in
/-- A walk of a drawing joins its ends in the graph `adj` on the vertices of the drawing. -/
theorem reachable_of_walk (D : Drawing S) {u v : S} (W : GraphWalk D.toGraph u v) (hu : u ∈ D.V)
    (hv : v ∈ D.V) : (D.adj.induce D.V).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction W with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z e h W ih =>
    obtain ⟨he, hx, hy, hlink⟩ := h
    have hrest := ih hy hv
    by_cases hxy : x = y
    · subst hxy
      exact hrest
    · have hxe : x ∈ tilde e := by
        rw [tilde_eq_inter_V D he, hlink]
        simp
      have hye : y ∈ tilde e := by
        rw [tilde_eq_inter_V D he, hlink]
        simp
      have hadj : (D.adj.induce D.V).Adj ⟨x, hx⟩ ⟨y, hy⟩ := ⟨hxy, hx, hy, e, he, hxe, hye⟩
      exact hadj.reachable.trans hrest

omit [T1Space S] in
/-- A minor of digraphs in the sense of Graph Minors VII gives an enlargement. -/
theorem isEnlargement_of_minor {H G : SurfaceDigraph S} (h : IsDigraphMinor H G) :
    ∃ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement H.G G.G σv σe := by
  obtain ⟨-, -, φv, φe, h1, h2, h3, h4, -, h5, -⟩ := h
  refine ⟨φv, φe, ⟨h2, ?_, fun v hv ↦ (h1 v hv).1, fun v hv ↦ (h1 v hv).2.1, ?_, h3, ?_⟩⟩
  · intro e he e' he' hee
    by_contra hne
    exact h4 e he e' he' hne hee
  · intro v hv
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨W⟩ := (h1 v hv).2.2.2 a ha b hb
    exact reachable_of_walk _ W ha hb
  · intro e he v hv
    have hends := H.ends_eq e he
    have hendsG := G.ends_eq _ (h2 e he)
    constructor
    · rintro ⟨x, hxv, hx⟩
      rw [← hendsG] at hx
      rcases hx with rfl | hx
      · have : v = H.plus e := by
          by_contra hne
          exact Set.disjoint_left.1 (h3 v hv _ (H.plus_mem e he) hne) hxv (h5 e he).1
        rw [← hends, this]
        simp
      · rw [mem_singleton_iff] at hx
        subst hx
        have : v = H.minus e := by
          by_contra hne
          exact Set.disjoint_left.1 (h3 v hv _ (H.minus_mem e he) hne) hxv (h5 e he).2
        rw [← hends, this]
        simp
    · intro hv'
      rw [← hends] at hv'
      rcases hv' with rfl | hv'
      · exact ⟨_, (h5 e he).1, by rw [← hendsG]; simp⟩
      · rw [mem_singleton_iff] at hv'
        subst hv'
        exact ⟨_, (h5 e he).2, by rw [← hendsG]; simp⟩

omit [T1Space S] in
/-- A closed surface is not an open disc. -/
theorem not_isOpenDisc_univ [CompactSpace S] : ¬ IsOpenDisc (univ : Set S) := by
  rintro ⟨-, ⟨f⟩⟩
  have hc : IsCompact OpenUnitDisc := by
    have : CompactSpace OpenUnitDisc :=
      (Homeomorph.trans f (Homeomorph.Set.univ S)).symm.compactSpace
    exact isCompact_iff_compactSpace.2 this
  have hopen : IsOpen OpenUnitDisc := isOpen_lt (by fun_prop) continuous_const
  have huniv : OpenUnitDisc = univ := IsClopen.eq_univ ⟨hc.isClosed, hopen⟩ ⟨0, by simp
    [OpenUnitDisc]⟩
  have hmem : (!₂[2, 0] : EuclideanPlane) ∈ OpenUnitDisc := by
    rw [huniv]
    exact mem_univ _
  simp only [OpenUnitDisc, mem_ball_zero_iff] at hmem
  have h0 := PiLp.norm_apply_le (!₂[2, 0] : EuclideanPlane) 0
  norm_num at h0
  linarith

omit [T1Space S] in
/-- A closed connected surface that is not a sphere has a non-null-homotopic `O`-arc. -/
theorem exists_not_nullHomotopic (hS : IsSurface S)
    [ConnectedSpace S] (hbd : bd S = ∅) (hsph : ¬ IsSphere S) :
    ∃ F : Set S, IsOArc F ∧ ¬ IsNullHomotopicOArc F := by
  by_contra hno
  push Not at hno
  have hcl : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x ↦ by
    by_contra hx
    have : x ∈ bd S := hx
    rw [hbd] at this
    exact this⟩
  have hbdj : ∀ F : Set S, Disjoint F (bd S) := fun F ↦ by simp [hbd]
  have hd := open_disc S univ hcl ‹_› isConnected_univ isOpen_univ fun F _ hF ↦ by
    obtain ⟨Δ, -, h1, h2⟩ := (epstein S univ F hS ‹_› hF (subset_univ _) (hbdj F)).1 (hno F hF)
    exact ⟨Δ, subset_univ _, h1, h2⟩
  have : CompactSpace S := hS.1
  rcases hd with h | h
  · exact hsph h.1
  · exact not_isOpenDisc_univ h

omit [T1Space S] in
/-- `rep(G)` is at most the number of vertices on a `G`-normal non-null-homotopic `O`-arc. -/
theorem rep_le_of_arc (G : Drawing S) {F : Set S} (hF : IsOArc F) (hn : G.IsNormal F)
    (hnull : ¬ IsNullHomotopicOArc F) : G.rep ≤ ((F ∩ G.V).ncard : ℕ) :=
  sInf_le ⟨F, hF, hn, hnull, rfl⟩


/-- The model `Σ(0, 0, 0)` is the sphere. -/
theorem isSphere_model : IsSphere (SurfaceModel 0 0 0) := by
  have hb : modelBase (2 * 0 + 0 + 0) = univ := by
    ext p
    simp [modelBase]
  have : CompactSpace (modelBase (2 * 0 + 0 + 0)) :=
    isCompact_iff_compactSpace.1 (hb ▸ isCompact_univ)
  have : CompactSpace (SurfaceModel 0 0 0) :=
    inferInstanceAs (CompactSpace (Quot (ModelGlue 0 0 (2 * 0 + 0 + 0))))
  let f : SurfaceModel 0 0 0 → OnePoint EuclideanPlane :=
    Quot.lift Subtype.val fun _ _ h ↦ by
      cases h with
      | handle i hi => exact absurd hi (Nat.not_lt_zero i)
      | crosscap i hi => exact absurd hi (Nat.not_lt_zero i)
  have hf : Continuous f := continuous_quot_lift _ continuous_subtype_val
  have hinj : Function.Injective f := by
    rintro ⟨x⟩ ⟨y⟩ h
    exact congrArg (Quot.mk _) (Subtype.ext h)
  have hsurj : Function.Surjective f := fun p ↦ ⟨Quot.mk _ ⟨p, hb ▸ mem_univ p⟩, rfl⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hf⟩

/-- A surface homeomorphic to `Σ(a, b, c)` with no boundary has `c = 0`, since the model has at
least
`c` cuffs. -/
theorem model_c_eq_zero {S : Type u} [TopologicalSpace S] [T2Space S] {a b c : ℕ}
    (hom : S ≃ₜ SurfaceModel a b c) (hbd : bd S = ∅) : c = 0 := by
  have : T2Space (SurfaceModel a b c) := hom.symm.isEmbedding.t2Space
  have h := GM20.Draw.le_encard_cuffs (a := a) (b := b) (c := c)
  have hb : bd (SurfaceModel a b c) = ∅ := by
    rw [← image_bd hom, hbd, image_empty]
  have hc : cuffs (SurfaceModel a b c) = ∅ := by
    simp [cuffs, componentsIn, hb]
  rw [hc, encard_empty] at h
  simpa using h


end GraphMinor.GM19
