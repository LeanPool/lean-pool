/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Disc
public import LeanPool.GraphMinor.GM19.Section6a

/-!
# Deleting a vertex lowers `rep` by at most one

In the proof of (6.6) of Graph Minors XIX (page 341), the paper says `rep(H) ≥ k` for `H = G \ v`,
since `rep(G) > k`. Here is the reason. Let `F` be a non-null-homotopic `H`-normal O-arc. We put the
edges at `v` back one at a time. Each edge `e` has a thin disc `D` around it that meets the rest
only at its ends (`exists_edge_lens`). We reroute `F` around `D` along the boundary of `D`, by
`exists_reroute`, on the side that misses the other end of `e`. The only new vertex the curve can
meet is `v`. So `rep(G) ≤ rep(H) + 1` (`lt_rep_delete`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GM11

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- **Putting one edge back.** See the module docstring. -/
theorem exists_curve_add_line (hT : IsClosedSurface S) {Z L : Set S} {u v : S}
  (hL : IsLineWithEnds L u v) (huv : u ≠ v) (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v})
    (hu : u ∈ Z) {F : Set S} (hF : IsOArc F)
    (hnn : ¬ IsNullHomotopicOArc F) : ∃ F', IsOArc F' ∧ ¬ IsNullHomotopicOArc F' ∧ F' ∩ (Z ∪ L) ⊆
      (F ∩ Z) ∪ {v} := by
  classical
  obtain ⟨D, -, -, hD, hLD, hDZ, -, -, hbL, -⟩ := exists_edge_lens hT hL huv hZ hLZ
  by_cases hm : (F ∩ D).Nonempty
  swap
  · refine ⟨F, hF, hnn, ?_⟩
    rintro x ⟨hxF, hx | hx⟩
    · exact .inl ⟨hxF, hx⟩
    · exact absurd ⟨x, hxF, hLD hx⟩ hm
  have hO := hD.isOArc_discBd
  have hch : ∀ a b, ∃ P : Set S, a ∈ discBd D → b ∈ discBd D → P ⊆ discBd D ∧ (a ≠ b
    → IsLineWithEnds P a b) ∧ (a = b → P = {a}) ∧ (u ∈ P → u = a ∨ u = b) := fun a b => by
    by_cases ha : a ∈ discBd D
    swap
    · exact ⟨∅, fun h => absurd h ha⟩
    by_cases hb : b ∈ discBd D
    swap
    · exact ⟨∅, fun _ h => absurd h hb⟩
    by_cases hab : a = b
    · refine ⟨{a}, fun _ _ => ⟨singleton_subset_iff.mpr ha, fun h => absurd hab h, fun _ => rfl,
        fun h => .inl h⟩⟩
    obtain ⟨A, B, hA, hB, hAB, hi⟩ := hO.lines ha hb hab
    by_cases huA : u ∈ A ∧ u ≠ a ∧ u ≠ b
    · refine ⟨B, fun _ _ => ⟨hAB ▸ subset_union_right, fun _ => hB, fun h => absurd h hab,
        fun h => ?_⟩⟩
      have : u ∈ A ∩ B := ⟨huA.1, h⟩
      rw [hi] at this
      exact this
    · refine ⟨A, fun _ _ => ⟨hAB ▸ subset_union_left, fun _ => hA, fun h => absurd h hab,
        fun h => ?_⟩⟩
      by_contra hn
      push Not at hn
      exact huA ⟨h, hn.1, hn.2⟩
  choose P hP using hch
  obtain ⟨C, a, b, hC, hCnn, haF, hbF, -, hCs⟩ := exists_reroute hT hD hF hnn hm P fun a ha b hb
    => by
    obtain ⟨h1, h2, h3, -⟩ := hP a b ha hb
    exact ⟨h1.trans (Surface.discBd_subset D), h2, h3⟩
  refine ⟨C, hC, hCnn, ?_⟩
  obtain ⟨h1, -, -, h4⟩ := hP a b haF.2 hbF.2
  rintro x ⟨hxC, hxZ⟩
  rcases hCs hxC with hx | hx
  · rcases hxZ with hxZ | hxZ
    · exact .inl ⟨hx.1, hxZ⟩
    · exact absurd (hLD hxZ) hx.2
  · have hxbd := h1 hx
    have hxuv : x = u ∨ x = v := by
      rcases hxZ with hxZ | hxZ
      · exact hDZ ⟨Surface.discBd_subset D hxbd, hxZ⟩
      · exact hbL ⟨hxbd, hxZ⟩
    rcases hxuv with rfl | rfl
    · left
      rcases h4 hx with h | h
      · exact ⟨h ▸ haF.1, hu⟩
      · exact ⟨h ▸ hbF.1, hu⟩
    · exact .inr rfl

/-- `G` with the vertices of `X` deleted, with all their edges. -/
noncomputable def delete (G : Drawing S) (X : Set S) : Drawing S :=
  G.span (G.V \ X) {e | e ∈ G.E ∧ Disjoint (tilde e) X}

theorem delete_E (G : Drawing S) (X : Set S) : (delete G X).E = {e | e ∈ G.E ∧ Disjoint
  (tilde e) X} := by
  rw [delete, Drawing.span_E]
  exact inter_eq_left.mpr fun _ h => h.1

theorem delete_V (G : Drawing S) (X : Set S) : (delete G X).V = G.V \ X := by
  rw [delete, Drawing.span_V]
  apply Subset.antisymm
  · refine union_subset (inter_subset_left.trans (Subset.refl _) |>.trans ?_) ?_
    · exact fun _ h => h
    · refine iUnion₂_subset fun e he => ?_
      rintro y ⟨hy, hyV⟩
      have hyt : y ∈ tilde e := GM19.tilde_eq_inter_V G he.2 ▸ ⟨hy, hyV⟩
      exact ⟨hyV, fun h => Set.disjoint_left.mp he.1.2 hyt h⟩
  · exact fun y hy => .inl ⟨hy, hy.1⟩

theorem delete_U (G : Drawing S) (X : Set S) : (delete G X).U = (G.V \ X) ∪ ⋃ e ∈ {e | e ∈ G.E
  ∧ Disjoint (tilde e) X}, closure e := by
  have h1 : (delete G X).U = (delete G X).V ∪ ⋃ e ∈ (delete G X).E, closure e := by
    rw [U_eq, sUnion_image]
  rw [h1, delete_V, delete_E]

theorem delete_subdrawing (G : Drawing S) (X : Set S) : (delete G X).IsSubdrawing G :=
  ⟨by rw [delete_V]; exact sdiff_subset, by rw [delete_E]; exact fun _ h => h.1⟩

/-- **`rep` falls by at most one when a vertex goes.** See the module docstring. -/
theorem lt_rep_delete (hT : IsClosedSurface S) (G : Drawing S) (hl : LoopFree G) {v : S}
  (hv : v ∈ G.V) {k : ℕ} (hk : (k : ℕ∞) < G.rep) : (k : ℕ∞) ≤ (delete G {v}).rep := by
  classical
  refine le_sInf ?_
  rintro _ ⟨F, hF, hn, hnull, rfl⟩
  let H := delete G {v}
  have hE : ∀ e ∈ G.E, e ∉ H.E → v ∈ tilde e := fun e he hne => by
    by_contra hv'
    exact hne (by rw [delete_E]; exact ⟨he, Set.disjoint_singleton_right.mpr hv'⟩)
  have hfinE : ∀ A : Finset (Set S), (∀ e ∈ A, e ∈ G.E ∧ e ∉ H.E) → ∃ F', IsOArc F'
    ∧ ¬ IsNullHomotopicOArc F' ∧ F' ∩ (H.U ∪ {v} ∪ ⋃ e ∈ A, closure e) ⊆ (F ∩ H.U) ∪ {v} := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨F, hF, hnull, ?_⟩
      rintro x ⟨hxF, (hx | hx) | hx⟩
      · exact .inl ⟨hxF, hx⟩
      · exact .inr hx
      · simp at hx
    | insert e A heA ih =>
      intro hA
      obtain ⟨F₁, hF₁, hn₁, hsub⟩ := ih fun f hf => hA f (Finset.mem_insert_of_mem hf)
      obtain ⟨he, heH⟩ := hA e (Finset.mem_insert_self _ _)
      obtain ⟨a, b, hab, hti, hline⟩ := hl e he
      have hve : v ∈ tilde e := hE e he heH
      obtain ⟨u, huv, hL, hti'⟩ : ∃ u, u ≠ v ∧ IsLineWithEnds (closure e) u v ∧ tilde e = {u, v}
        := by
        rw [hti] at hve
        rcases hve with rfl | hve
        · exact ⟨b, hab.symm, GraphMinor.GM11.IsLineWithEnds.symm hline, by rw [hti, pair_comm]⟩
        · rw [mem_singleton_iff.mp hve]
          exact ⟨a, hab, mem_singleton_iff.mp hve ▸ hline, hti⟩
      have hhU : ∀ {x}, x ∈ H.U → x ∉ G.V → ∃ f ∈ H.E, x ∈ closure f := fun {x} hx hxV => by
        rw [U_eq] at hx
        rcases hx with hx | hx
        · exact absurd ((delete_subdrawing G {v}).1 hx) hxV
        · obtain ⟨_, ⟨f, hf, rfl⟩, hxf⟩ := hx
          exact ⟨f, hf, hxf⟩
      let Z : Set S := H.U ∪ {v} ∪ ⋃ f ∈ A, closure f
      have hZ : IsClosed Z := (H.isClosed_U.union isClosed_singleton).union
        (A.finite_toSet.isClosed_biUnion fun _ _ => isClosed_closure)
      have hLZ : closure e ∩ Z ⊆ {u, v} := by
        rintro x ⟨hxe, hxZ⟩
        by_cases hxV : x ∈ G.V
        · rw [← hti', GM19.tilde_eq_inter_V G he]
          exact ⟨hxe, hxV⟩
        rcases hxZ with (hx | hx) | hx
        · obtain ⟨f, hf, hxf⟩ := hhU hx hxV
          have hfG := (delete_subdrawing G {v}).2 hf
          exact absurd (edge_eq_of_mem G he hfG hxe hxf hxV ▸ hf) heH
        · exact absurd (mem_singleton_iff.mp hx ▸ hv) hxV
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          exact absurd (edge_eq_of_mem G he (hA f (Finset.mem_insert_of_mem hf)).1 hxe hxf hxV ▸
            hf) heA
      have huU : u ∈ Z := by
        have hutilde : u ∈ tilde e := by rw [hti']; exact .inl rfl
        have huV : u ∈ G.V := (GM19.tilde_eq_inter_V G he ▸ hutilde).2
        refine .inl (.inl (H.V_subset_U ?_))
        change u ∈ (delete G {v}).V
        rw [delete_V]
        exact ⟨huV, huv⟩
      obtain ⟨F₂, hF₂, hn₂, hsub₂⟩ := exists_curve_add_line hT hL huv hZ hLZ huU hF₁ hn₁
      refine ⟨F₂, hF₂, hn₂, ?_⟩
      rintro x ⟨hxF, hxZ⟩
      have hxZ' : x ∈ Z ∪ closure e := by
        rcases hxZ with (hx | hx) | hx
        · exact .inl (.inl (.inl hx))
        · exact .inl (.inl (.inr hx))
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact .inr hxf
          · exact .inl (.inr (mem_iUnion₂.mpr ⟨f, hf, hxf⟩))
      rcases hsub₂ ⟨hxF, hxZ'⟩ with h | h
      · exact hsub ⟨h.1, h.2⟩
      · exact .inr h
  have hfin : (G.E \ H.E).Finite := G.finite_edges.subset sdiff_subset
  obtain ⟨F', hF', hn', hsub⟩ :=
    hfinE hfin.toFinset (fun e he => hfin.mem_toFinset.mp he)
  have hGU : G.U ⊆ H.U ∪ {v} ∪ ⋃ e ∈ hfin.toFinset, closure e := fun x hx => by
    by_cases hxV : x ∈ G.V
    · by_cases hxv : x = v
      · exact .inl (.inr hxv)
      · refine .inl (.inl (H.V_subset_U ?_))
        change x ∈ (delete G {v}).V
        rw [delete_V]
        exact ⟨hxV, hxv⟩
    obtain ⟨e, he, hxe⟩ := exists_edge_of_mem G hx hxV
    by_cases heH : e ∈ H.E
    · exact .inl (.inl (H.closure_subset_U heH (subset_closure hxe)))
    · exact .inr (mem_iUnion₂.mpr ⟨e, hfin.mem_toFinset.mpr ⟨he, heH⟩, subset_closure hxe⟩)
  have hHV : H.V ⊆ G.V := (delete_subdrawing G {v}).1
  have hnF : ∀ {x}, x ∈ F' → x ∈ G.U → (x ∈ F ∩ H.V) ∨ x = v := fun {x} hxF hxU => by
    rcases hsub ⟨hxF, hGU hxU⟩ with h | h
    · exact .inl ⟨h.1, hn h⟩
    · exact .inr h
  have hnormal : G.IsNormal F' := fun x hx => by
    rcases hnF hx.1 hx.2 with h | h
    · exact hHV h.2
    · exact h ▸ hv
  have hrep := rep_le_of_arc G hF' hnormal hn'
  have hcard : (F' ∩ G.V).ncard ≤ (F ∩ H.V).ncard + 1 := by
    have hsub' : F' ∩ G.V ⊆ insert v (F ∩ H.V) := fun x hx => by
      rcases hnF hx.1 (G.V_subset_U hx.2) with h | h
      · exact .inr h
      · exact .inl h
    have hf : (F ∩ H.V).Finite := H.finite_V.subset inter_subset_right
    calc _ ≤ (insert v (F ∩ H.V)).ncard := ncard_le_ncard hsub' (hf.insert v)
      _ ≤ _ := ncard_insert_le _ _
  have h1 : (k : ℕ∞) < (((F ∩ H.V).ncard + 1 : ℕ) : ℕ∞) := lt_of_lt_of_le hk (hrep.trans
    (by exact_mod_cast hcard))
  have h2 : k < (F ∩ H.V).ncard + 1 := by exact_mod_cast h1
  have h3 : k ≤ (F ∩ H.V).ncard := by omega
  exact_mod_cast h3

end GraphMinor.GM19
