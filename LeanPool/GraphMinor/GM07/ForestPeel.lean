/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CutForest
public import LeanPool.GraphMinor.GM11.Forest
public import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.GM11.RadialBasics
public import LeanPool.GraphMinor.GM11.Walks
public import LeanPool.GraphMinor.GM06.DiscRegions
public import LeanPool.GraphMinor.GM06.Euler
public import LeanPool.GraphMinor.GM07.CuffWalk

/-!
# A forest grows one line at a time

Let `L` be a proper graph such that `U(L)` includes no `O`-arc and no `I`-arc, as in Graph Minors
VII, (4.4) (page 223). We list the closures of its edges so that each one meets what comes before
it, and `bd(Σ)`, in at most one end
(`exists_growth`). The list comes from peeling leaves. A longest path of `L` has an end off `bd(Σ)`,
since otherwise the path is an `I`-arc, and this end is a leaf, since another edge there would
extend the path or close an `O`-arc
(`exists_leaf`). Taking an edge away keeps the hypotheses, as `U(L)` shrinks.

We also count. An attached line adds one new vertex off `bd(Σ)` and a free line adds two, so the
number of free lines is the number of vertices off `bd(Σ)` less the number of edges. This gives the
bound on the cuffs of `Σ'` on page 226.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

theorem GraphWalk.length_support' {α β : Type*} {G : Graph α β} {u v : α}
  (W : GraphWalk G u v) : W.support.length = W.length + 1 := by
  induction W with
  | nil _ => rfl
  | cons _ r ih =>
    simp only [GraphWalk.support, List.length_cons, ih]
    rfl

/-- A prefix of a simple walk up to a vertex on it. -/
theorem GraphWalk.exists_prefix {α β : Type*} {G : Graph α β} {u v x : α} (W : GraphWalk G u v)
  (hW : W.IsSimple) (hx : x ∈ W.support) :
    ∃ W' : GraphWalk G u x, W'.IsSimple ∧ (∀ e ∈ W'.edges, e ∈ W.edges)
      ∧ ∀ z ∈ W'.support, z ∈ W.support := by
  classical
  induction W with
  | @nil a hv =>
    obtain rfl : x = a := by simpa [GraphWalk.support] using hx
    exact ⟨.nil hv, by simp [GraphWalk.IsSimple, GraphWalk.support], by simp [GraphWalk.edges],
      fun z hz => hz⟩
  | @cons a y b e hl r ih =>
    have hnd := List.nodup_cons.mp hW
    by_cases hxa : x = a
    · subst hxa
      exact ⟨.nil hl.left_mem, by simp [GraphWalk.IsSimple, GraphWalk.support],
        by simp [GraphWalk.edges], by simp [GraphWalk.support]⟩
    · have hxr : x ∈ r.support := (List.mem_cons.mp hx).resolve_left hxa
      obtain ⟨W', hs, he, hz⟩ := ih hnd.2 hxr
      refine ⟨.cons hl W', ?_, fun f hf => ?_, fun z hz' => ?_⟩
      · exact List.nodup_cons.mpr ⟨fun h => hnd.1 (hz _ h), hs⟩
      · rcases List.mem_cons.mp hf with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (he f h)
      · rcases List.mem_cons.mp hz' with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hz z h)

/-- `U(G)` includes no `O`-arc and no `I`-arc. -/
def NoArcs (G : Drawing S) : Prop := (∀ F ⊆ G.U, ¬ IsOArc F) ∧ ∀ F ⊆ G.U, ¬ IsIArc F

theorem NoArcs.mono {G G' : Drawing S} (h : NoArcs G) (hU : G'.U ⊆ G.U) : NoArcs G' :=
  ⟨fun F hF => h.1 F (hF.trans hU), fun F hF => h.2 F (hF.trans hU)⟩

/-- With no `O`-arc in `U(G)`, every edge has a line as its closure. -/
theorem NoArcs.edge_line {G : Drawing S} (h : NoArcs G) {e : Set S} (he : e ∈ G.E) : ∃ u v, u ≠ v
  ∧ closure e ∩ G.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  rcases G.edge_cond e he with h1 | ⟨u, -, hF⟩
  · exact h1
  · exact (h.1 _ (G.closure_subset_U he) hF).elim

theorem mem_E_of_mem_edges {G : Drawing S} {a b : S} (W : GraphWalk G.toGraph a b) {e : Set S}
  (he : e ∈ W.edges) : e ∈ G.E := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | cons hl r ih =>
    rcases List.mem_cons.mp he with rfl | h
    · exact hl.1
    · exact ih h

/-- A vertex in the closure of an edge of a walk lies on the walk. -/
theorem mem_support_of_mem_closure {G : Drawing S} {a b : S} (W : GraphWalk G.toGraph a b) {e : Set
  S} (he : e ∈ W.edges) {p : S} (hp : p ∈ closure e) (hV : p ∈ G.V) : p ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | @cons a y b f hl r ih =>
    rcases List.mem_cons.mp he with rfl | h
    · have h1 : p ∈ closure e ∩ G.V := ⟨hp, hV⟩
      rw [hl.2.2.2] at h1
      rcases h1 with rfl | h2
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_singleton_iff.mp h2 ▸ r.start_mem_support)
    · exact List.mem_cons_of_mem _ (ih h)

theorem walk_subset_U {G : Drawing S} {a b : S} (W : GraphWalk G.toGraph a b) :
  ({x | x ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, closure e) ⊆ G.U := by
  apply union_subset
  · exact fun x hx => G.V_subset_U (W.mem_vertexSet_of_mem_support hx)
  · exact iUnion₂_subset fun e he => G.closure_subset_U (mem_E_of_mem_edges W he)

/-- The first edge of a longest simple walk is a leaf at the first vertex. -/
theorem leaf_of_longest [T2Space S] {G : Drawing S} (hN : NoArcs G) {y b : S}
  (W : GraphWalk G.toGraph y b) (hW : W.IsSimple) (hlen : 1 ≤ W.length)
    (hmax : ∀ (a' b' : S) (W' : GraphWalk G.toGraph a' b'), W'.IsSimple → W'.length ≤ W.length) :
    ∃ e ∈ G.E, ∃ x, x ≠ y ∧ closure e ∩ G.V = {y, x} ∧ ∀ f ∈ G.E, f ≠ e → y ∉ closure f := by
  classical
  cases W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hlen
  | @cons _ x _ e hl r =>
    have hnd := List.nodup_cons.mp hW
    refine ⟨e, hl.1, x, fun h => hnd.1 (h ▸ r.start_mem_support), hl.2.2.2, fun f hf hne hyf => ?_⟩
    set W₀ : GraphWalk G.toGraph y b := .cons hl r with hW₀
    obtain ⟨u, v, huv, hcap, hline⟩ := hN.edge_line hf
    have hyV : y ∈ G.V := hl.2.1
    have hy' : y ∈ closure f ∩ G.V := ⟨hyf, hyV⟩
    obtain ⟨z, hzy, hcap', hline'⟩ : ∃ z, z ≠ y ∧ closure f ∩ G.V = {y, z} ∧ IsLineWithEnds
      (closure f) y z := by
      rw [hcap] at hy'
      rcases hy' with rfl | h
      · exact ⟨v, huv.symm, hcap, hline⟩
      · obtain rfl : y = v := h
        exact ⟨u, huv, by rw [hcap, pair_comm], hline.symm⟩
    have hzV : z ∈ G.V := (show z ∈ closure f ∩ G.V by rw [hcap']; exact .inr rfl).2
    by_cases hz : z ∈ W₀.support
    · obtain ⟨W', hs, he, hsup⟩ := GraphWalk.exists_prefix W₀ hW hz
      have hfW : f ∉ W₀.edges := fun h => by
        rcases List.mem_cons.mp h with h1 | h1
        · exact hne h1
        · exact hnd.1 (mem_support_of_mem_closure r h1 hyf hyV)
      have hL := walk_isLine G W' hs hzy.symm
      refine hN.1 _ (union_subset (walk_subset_U W') (G.closure_subset_U hf))
        (isOArc_union hL hline' ?_)
      rintro p ⟨hp, hpf⟩
      have hpc : p ∈ closure f ∩ G.V → p ∈ ({y, z} : Set S) := fun h => hcap' ▸ h
      rcases hp with hp | hp
      · exact hpc ⟨hpf, W'.mem_vertexSet_of_mem_support hp⟩
      · obtain ⟨g, hg, hpg⟩ := mem_iUnion₂.mp hp
        have hgE := mem_E_of_mem_edges W' hg
        by_cases hpV : p ∈ G.V
        · exact hpc ⟨hpf, hpV⟩
        · have h1 : p ∈ f := by rw [← G.closure_diff_V hf]; exact ⟨hpf, hpV⟩
          have h2 : p ∈ g := by rw [← G.closure_diff_V hgE]; exact ⟨hpg, hpV⟩
          exact (hfW (arcComponent_eq hgE hf h2 h1 ▸ he g hg)).elim
    · have hlink : G.toGraph.IsLink f z y := ⟨hf, hzV, hyV, by rw [hcap', pair_comm]⟩
      have h1 := hmax z b (.cons hlink W₀) (List.nodup_cons.mpr ⟨hz, hW⟩)
      have h2 : (GraphWalk.cons hlink W₀).length = W₀.length + 1 := rfl
      omega

/-- **A leaf off the boundary.** -/
theorem exists_leaf [T2Space S] {G : Drawing S} (hN : NoArcs G) (hE : G.E.Nonempty) :
    ∃ e ∈ G.E, ∃ y x, x ≠ y ∧ closure e ∩ G.V = {y, x} ∧ y ∉ bd S ∧ (∀ f ∈ G.E, f ≠ e
      → y ∉ closure f) ∧ IsLineWithEnds (closure e) y x := by
  classical
  let P : ℕ → Prop := fun n => ∃ (a b : S) (W : GraphWalk G.toGraph a b), W.IsSimple ∧ W.length = n
  have hbound : ∀ n, P n → n ≤ G.V.ncard := by
    rintro n ⟨a, b, W, hs, rfl⟩
    have h1 : W.support.toFinset ⊆ G.finite_V.toFinset := fun x hx =>
      G.finite_V.mem_toFinset.mpr (W.mem_vertexSet_of_mem_support (List.mem_toFinset.mp hx))
    have h2 := Finset.card_le_card h1
    rw [List.toFinset_card_of_nodup hs, GraphWalk.length_support',
      ← ncard_eq_toFinset_card _ G.finite_V] at h2
    omega
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨u, v, huv, hcap, -⟩ := hN.edge_line he₀
  have huV : u ∈ G.V := (show u ∈ closure e₀ ∩ G.V by rw [hcap]; exact .inl rfl).2
  have hvV : v ∈ G.V := (show v ∈ closure e₀ ∩ G.V by rw [hcap]; exact .inr rfl).2
  have hP1 : P 1 := ⟨u, v, .cons ⟨he₀, huV, hvV, hcap⟩ (.nil hvV), by
    simpa [GraphWalk.IsSimple, GraphWalk.support] using huv, rfl⟩
  have h1 : 1 ≤ G.V.ncard := hbound 1 hP1
  obtain ⟨a, b, W, hs, hl⟩ : P (Nat.findGreatest P G.V.ncard) := Nat.findGreatest_spec h1 hP1
  have hlen : 1 ≤ W.length := hl ▸ Nat.le_findGreatest h1 hP1
  have hmax : ∀ (a' b' : S) (W' : GraphWalk G.toGraph a' b'), W'.IsSimple → W'.length ≤ W.length
    := fun a' b' W' hs' => by
    rw [hl]
    exact Nat.le_findGreatest (hbound _ ⟨a', b', W', hs', rfl⟩) ⟨a', b', W', hs', rfl⟩
  have hab : a ≠ b := by
    cases W with
    | nil _ => simp [GraphWalk.length, GraphWalk.edges] at hlen
    | cons hl' r =>
      have hnd := List.nodup_cons.mp hs
      exact fun h => hnd.1 (h ▸ r.end_mem_support)
  have finish : ∀ {y b : S} (W : GraphWalk G.toGraph y b), W.IsSimple → 1 ≤ W.length → (∀
    (a' b' : S) (W' : GraphWalk G.toGraph a' b'), W'.IsSimple → W'.length ≤ W.length) → y ∉ bd S →
      ∃ e ∈ G.E, ∃ y x, x ≠ y ∧ closure e ∩ G.V = {y, x} ∧ y ∉ bd S ∧ (∀ f ∈ G.E, f ≠ e
        → y ∉ closure f) ∧ IsLineWithEnds (closure e) y x := by
    intro y b W hs hlen hmax hy
    obtain ⟨e, he, x, hxy, hcap, hleaf⟩ := leaf_of_longest hN W hs hlen hmax
    obtain ⟨u, v, huv, hcap', hline⟩ := hN.edge_line he
    have hy' : y ∈ ({u, v} : Set S) := hcap' ▸ (show y ∈ closure e ∩ G.V by
      rw [hcap]
      exact .inl rfl)
    have hx' : x ∈ ({u, v} : Set S) := hcap' ▸ (show x ∈ closure e ∩ G.V by
      rw [hcap]
      exact .inr rfl)
    refine ⟨e, he, y, x, hxy, hcap, hy, hleaf, ?_⟩
    rcases hy' with rfl | h
    · rcases hx' with rfl | h'
      · exact absurd rfl hxy
      · obtain rfl : x = v := h'
        exact hline
    · obtain rfl : y = v := h
      rcases hx' with rfl | h'
      · exact hline.symm
      · exact absurd h' hxy
  by_cases ha : a ∈ bd S
  · by_cases hb : b ∈ bd S
    · exact (hN.2 _ (walk_subset_U W) ⟨a, b, ha, hb, walk_isLine G W hs hab⟩).elim
    · have hlr : W.reverse.length = W.length := by
        have h2 := GraphWalk.length_support' W.reverse
        rw [GraphWalk.support_reverse, List.length_reverse, GraphWalk.length_support'] at h2
        omega
      refine finish W.reverse ?_ (hlr ▸ hlen) (fun a' b' W' hs' => hlr ▸ hmax a' b' W' hs') hb
      change W.reverse.support.Nodup
      rw [GraphWalk.support_reverse]
      exact List.nodup_reverse.mpr hs
  · exact finish W hs hlen hmax ha

omit [TopologicalSpace S] in
theorem listUnion_append {l : List (Set S)} {A : Set S} : listUnion (l ++ [A]) = listUnion l ∪ A
  := by
  ext z
  simp [listUnion, or_comm]

theorem IsGrowth.snoc_free {B A : Set S} {l : List (Set S)} {k : ℕ} (h : IsGrowth B l k)
  (hA : IsLine A) (hd : A ∩ (B ∪ listUnion l) = ∅) : IsGrowth B (l ++ [A]) (k + 1) := by
  induction h with
  | nil B => exact .free hA (by simpa using hd) (.nil _)
  | free hA' hd' _ ih =>
    rw [List.cons_append, Nat.add_right_comm]
    exact .free hA' hd' (ih (by rwa [listUnion_cons, ← union_assoc] at hd))
  | attached hA' hd' _ ih =>
    rw [List.cons_append]
    exact .attached hA' hd' (ih (by rwa [listUnion_cons, ← union_assoc] at hd))

theorem IsGrowth.snoc_attached {B A : Set S} {l : List (Set S)} {k : ℕ} {p q : S}
  (h : IsGrowth B l k) (hA : IsLineWithEnds A p q) (hd : A ∩ (B ∪ listUnion l) = {p}) : IsGrowth B
    (l ++ [A]) k := by
  induction h with
  | nil B => exact .attached hA (by simpa using hd) (.nil _)
  | free hA' hd' _ ih =>
    rw [List.cons_append]
    exact .free hA' hd' (ih (by rwa [listUnion_cons, ← union_assoc] at hd))
  | attached hA' hd' _ ih =>
    rw [List.cons_append]
    exact .attached hA' hd' (ih (by rwa [listUnion_cons, ← union_assoc] at hd))

/-- The vertices of `G` off `bd(Σ)` that lie on edges. -/
def endsOff (G : Drawing S) : Set S := {x | x ∉ bd S ∧ x ∈ G.V ∧ ∃ e ∈ G.E, x ∈ closure e}

theorem finite_endsOff (G : Drawing S) : (endsOff G).Finite := G.finite_V.subset fun _ h => h.2.1

/-- **A forest as a list of lines.** The closures of the edges of a proper graph whose point set
includes no `O`-arc and no `I`-arc grow from `bd(Σ)` one at a time, and the number of lines that
start a new tree is the number of vertices
on edges off `bd(Σ)` less the number of edges. -/
theorem exists_growth [T2Space S] (n : ℕ) : ∀ G : Drawing S, G.E.ncard = n → G.IsProper → NoArcs G →
    ∃ (l : List (Set S)) (k : ℕ), IsGrowth (bd S) l k ∧ listUnion l = (⋃ e ∈ G.E, closure e)
      ∧ k + n = (endsOff G).ncard := by
  classical
  induction n with
  | zero =>
    intro G hn _ _
    have hE : G.E = ∅ := (ncard_eq_zero G.finite_edges).mp hn
    have hoff : endsOff G = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
      obtain ⟨e, he, -⟩ := hx.2.2
      rw [hE] at he
      exact he
    exact ⟨[], 0, .nil _, by simp [hE], by simp [hoff]⟩
  | succ n ih =>
    intro G hn hG hN
    have hne : G.E.Nonempty := by
      rw [nonempty_iff_ne_empty]
      intro h
      rw [h] at hn
      simp at hn
    obtain ⟨e, he, y, x, hxy, hcap, hy, hleaf, hA⟩ := exists_leaf hN hne
    have hE' : (G.deleteEdge e).E = G.E \ {e} := deleteEdge_E G e
    have hV' : (G.deleteEdge e).V = G.V := GM06.deleteEdge_V G e
    have hU' : (G.deleteEdge e).U ⊆ G.U := by
      rw [deleteEdge_U G he]
      exact sdiff_subset
    obtain ⟨l, k, hg, hl, hc⟩ := ih (G.deleteEdge e)
      (by rw [hE', ncard_sdiff_singleton_of_mem he, hn]; rfl)
      (GM06.deleteEdge_isProper hG e) (hN.mono hU')
    let R : Set S := ⋃ f ∈ (G.deleteEdge e).E, closure f
    have hyV : y ∈ G.V := (show y ∈ closure e ∩ G.V by rw [hcap]; exact .inl rfl).2
    have hxV : x ∈ G.V := (show x ∈ closure e ∩ G.V by rw [hcap]; exact .inr rfl).2
    have hyc : y ∈ closure e := (show y ∈ closure e ∩ G.V by rw [hcap]; exact .inl rfl).1
    have hxc : x ∈ closure e := (show x ∈ closure e ∩ G.V by rw [hcap]; exact .inr rfl).1
    have hyR : y ∉ R := fun h => by
      obtain ⟨f, hf, hyf⟩ := mem_iUnion₂.mp h
      rw [hE'] at hf
      exact hleaf f hf.1 hf.2 hyf
    have hcapR : closure e ∩ (bd S ∪ R) ⊆ {x} := by
      rintro p ⟨hp, hpB⟩
      by_cases hpV : p ∈ G.V
      · have h1 : p ∈ closure e ∩ G.V := ⟨hp, hpV⟩
        rw [hcap] at h1
        rcases h1 with rfl | h1
        · rcases hpB with h2 | h2
          · exact (hy h2).elim
          · exact (hyR h2).elim
        · exact h1
      · have hpe : p ∈ e := by rw [← G.closure_diff_V he]; exact ⟨hp, hpV⟩
        rcases hpB with h2 | h2
        · exact (hpV (hG ⟨h2, G.closure_subset_U he hp⟩)).elim
        · obtain ⟨f, hf, hpf⟩ := mem_iUnion₂.mp h2
          rw [hE'] at hf
          have hpf' : p ∈ f := by rw [← G.closure_diff_V hf.1]; exact ⟨hpf, hpV⟩
          exact (hf.2 (mem_singleton_iff.mpr (arcComponent_eq hf.1 he hpf' hpe))).elim
    have hun : (⋃ f ∈ G.E, closure f) = R ∪ closure e := by
      ext z
      simp only [mem_iUnion₂, mem_union, R, hE', mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨f, hf, hz⟩
        by_cases hfe : f = e
        · exact .inr (hfe ▸ hz)
        · exact .inl ⟨f, ⟨hf, hfe⟩, hz⟩
      · rintro (⟨f, hf, hz⟩ | hz)
        · exact ⟨f, hf.1, hz⟩
        · exact ⟨e, he, hz⟩
    have hyoff : y ∉ endsOff (G.deleteEdge e) := fun h => by
      obtain ⟨f, hf, hyf⟩ := h.2.2
      exact hyR (mem_iUnion₂.mpr ⟨f, hf, hyf⟩)
    have hsubE : ∀ {z : S}, z ∈ endsOff (G.deleteEdge e) → z ∈ endsOff G := fun {z} h => by
      obtain ⟨hz, hzV, f, hf, hzf⟩ := h
      rw [hE'] at hf
      exact ⟨hz, hV' ▸ hzV, f, hf.1, hzf⟩
    have hsplit : ∀ {z : S}, z ∈ endsOff G → z = y ∨ z = x ∨ z ∈ endsOff (G.deleteEdge e)
      := fun {z} h => by
      obtain ⟨hz, hzV, f, hf, hzf⟩ := h
      by_cases hfe : f = e
      · subst hfe
        have h1 : z ∈ closure f ∩ G.V := ⟨hzf, hzV⟩
        rw [hcap] at h1
        rcases h1 with h1 | h1
        · exact .inl h1
        · exact .inr (.inl h1)
      · exact .inr (.inr ⟨hz, hV'.symm ▸ hzV, f, by rw [hE']; exact ⟨hf, hfe⟩, hzf⟩)
    by_cases hx : x ∈ bd S ∪ R
    · have hcapx : closure e ∩ (bd S ∪ listUnion l) = {x} := by
        rw [hl]
        exact Subset.antisymm hcapR (singleton_subset_iff.mpr ⟨hxc, hx⟩)
      refine ⟨l ++ [closure e], k, hg.snoc_attached hA.symm hcapx, by rw [listUnion_append, hl,
        hun], ?_⟩
      have hoff : endsOff G = insert y (endsOff (G.deleteEdge e)) := by
        ext z
        constructor
        · intro h
          rcases hsplit h with rfl | rfl | h1
          · exact .inl rfl
          · refine .inr ⟨h.1, hV'.symm ▸ h.2.1, ?_⟩
            rcases hx with h2 | h2
            · exact (h.1 h2).elim
            · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp h2
              exact ⟨f, hf, hzf⟩
          · exact .inr h1
        · rintro (rfl | h)
          · exact ⟨hy, hyV, e, he, hyc⟩
          · exact hsubE h
      rw [hoff, ncard_insert_of_notMem hyoff (finite_endsOff _), ← hc]
      omega
    · have hcapx : closure e ∩ (bd S ∪ listUnion l) = ∅ := by
        rw [hl]
        refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
        obtain rfl : p = x := hcapR hp
        exact hx hp.2
      have hlin : IsLine (closure e) := by
        obtain ⟨f, -, -⟩ := hA
        exact ⟨f⟩
      refine ⟨l ++ [closure e], k + 1, hg.snoc_free hlin hcapx, by rw [listUnion_append, hl,
        hun], ?_⟩
      have hxoff : x ∉ endsOff (G.deleteEdge e) := fun h => by
        obtain ⟨f, hf, hxf⟩ := h.2.2
        exact hx (.inr (mem_iUnion₂.mpr ⟨f, hf, hxf⟩))
      have hxb : x ∉ bd S := fun h => hx (.inl h)
      have hoff : endsOff G = insert y (insert x (endsOff (G.deleteEdge e))) := by
        ext z
        constructor
        · intro h
          rcases hsplit h with h1 | h1 | h1
          · exact .inl h1
          · exact .inr (.inl h1)
          · exact .inr (.inr h1)
        · rintro (rfl | rfl | h)
          · exact ⟨hy, hyV, e, he, hyc⟩
          · exact ⟨hxb, hxV, e, he, hxc⟩
          · exact hsubE h
      have hynot : y ∉ insert x (endsOff (G.deleteEdge e)) := by
        rintro (h | h)
        · exact hxy h.symm
        · exact hyoff h
      rw [hoff, ncard_insert_of_notMem hynot ((finite_endsOff _).insert _),
        ncard_insert_of_notMem hxoff (finite_endsOff _), ← hc]
      omega

theorem U_eq_biUnion_closure {G : Drawing S} (hn : HasNoIsolatedVertices G) : G.U
  = ⋃ e ∈ G.E, closure e := by
  refine Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun e he => G.closure_subset_U he)
  by_cases hzV : z ∈ G.V
  · obtain ⟨e, he, hi⟩ := hn z hzV
    exact mem_iUnion₂.mpr ⟨e, he, hi.2.2⟩
  · have hzc : z ∈ G.U \ G.V := ⟨hz, hzV⟩
    have hmem : pathComponentIn (G.U \ G.V) z ∈ G.E :=
      GraphMinor.Surface.mem_arcComponentsIn_of_mem hzc
    exact mem_iUnion₂.mpr ⟨_, hmem, subset_closure (mem_pathComponentIn_self hzc)⟩

/-- **Cutting along a forest.** For a proper graph `L` with no isolated vertices, whose point set
includes no `O`-arc and no `I`-arc, the cut along `U(L)` exists, and it has the model of (4.6) (page
226). -/
theorem exists_isCutAlongGraph (hS : IsSurface S) {a b c : ℕ} (hm : Nonempty
  (S ≃ₜ SurfaceModel a b c)) {L : Drawing S} (hL : L.IsProper) (hn : HasNoIsolatedVertices L)
    (hN : NoArcs L) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (θ : Y → S) (k : ℕ), IsCutAlongGraph L Y θ ∧ Nonempty
      (Y ≃ₜ SurfaceModel a b (c + k)) ∧ k + L.E.ncard = (endsOff L).ncard := by
  have : T2Space S := hS.2.1
  obtain ⟨l, k, hg, hl, hc⟩ := exists_growth _ L rfl hL hN
  obtain ⟨Y, tY, θ, hcut, hmY⟩ := exists_cut_growth _ hS hm rfl hg
  rw [hl, ← U_eq_biUnion_closure hn] at hcut
  exact ⟨Y, tY, θ, k, hcut.isCutAlongGraph hL hn, hmY, hc⟩

end GraphMinor.GM07
