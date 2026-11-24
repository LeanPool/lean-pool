/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffForest
public import LeanPool.GraphMinor.GM11.Ties
public import LeanPool.GraphMinor.Surface.ModelCriterion

/-!
# The step of (6.1)

Graph Minors VII, (6.1), page 237. We take a cuff `C` with at most one vertex, the disc `Δ` of `Σ +
CHat` around it from `exists_two_vertex_disc`, and shift `C` onto the boundary `A` of `Δ`. The new
surface is `Σ` itself. It stands for the part of `Σ` outside `A`, which the shift `h` covers.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] {T : Type u} [TopologicalSpace T] {C : Set S} {j : S
  → T} {D : Set T}

/-- A vertex on the closure of an edge of a walk is on the walk. -/
theorem walk_closure_vertex {G : Drawing S} {u v : S} (W : GraphWalk G.toGraph u v) : ∀ e ∈
  W.edges, ∀ x ∈ closure e, x ∈ G.V → x ∈ W.support := by
  induction W with
  | nil _ => simp [GraphWalk.edges]
  | cons hl rest ih =>
    intro e he x hx hxV
    rcases List.mem_cons.mp he with rfl | he
    · have h1 : x ∈ closure e ∩ G.V := ⟨hx, hxV⟩
      rw [hl.2.2.2] at h1
      rcases h1 with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ rest.start_mem_support
    · exact List.mem_cons_of_mem _ (ih e he x hx hxV)

/-- The part of `G` off an open set whose frontier is `G`-normal. -/
theorem exists_outside_drawing [T1Space S] {G : Drawing S} {Z : Set S} (hZ : IsOpen Z)
  (hedge : ∀ e ∈ G.E, (∃ y ∈ e, y ∉ Z) → Disjoint e Z) :
    ∃ G₁ : Drawing S, G₁.IsSubdrawing G ∧ G₁.U = G.U ∩ Zᶜ ∧ G₁.V = G.V ∩ Zᶜ := by
  classical
  let G₁ := G.span Zᶜ {e | Disjoint e Z}
  have hsub : G₁.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hE : ∀ e ∈ ({e | Disjoint e Z} ∩ G.E : Set (Set S)), closure e ⊆ Zᶜ := fun e he =>
    (Disjoint.closure_left he.1 hZ).le_compl_right
  have hV : G₁.V ⊆ Zᶜ := by
    rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact hE e he hxe.1
  refine ⟨G₁, hsub, subset_antisymm (subset_inter hsub.U_subset ?_) ?_,
    subset_antisymm (subset_inter hsub.1 hV) ?_⟩
  · rintro x (hx | hx)
    · exact hV hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact hE e he hxe
  · rintro x ⟨hxU, hxZ⟩
    by_cases hxV : x ∈ G.V
    · exact .inl (.inl ⟨hxZ, hxV⟩)
    · obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hxU hxV
      exact .inr (mem_iUnion₂.mpr ⟨e, ⟨hedge e he ⟨x, hxe, hxZ⟩, he⟩, subset_closure hxe⟩)
  · rintro x ⟨hxV, hxZ⟩
    exact .inl ⟨hxZ, hxV⟩

/-- **The data of the arc.** Two vertices of the boundary of `Δ`, a point `x₀` of `C`, a path `Q`
from `x₀` to the first vertex, and a walk of `G` to the first vertex that is `Q` if `x₀` is a
vertex. -/
theorem exists_pendant_walk [T1Space S] (hS : IsSurface S) [ConnectedSpace S] (hC : C ∈ cuffs S)
  (hc : IsCappedCuff C T j D) (hns : ¬ IsSphere T) {G : Drawing S} (hbl : IsBoundaryLinked G) {Δ Y
    : Set T} (hΔ : IsClosedDisc Δ) (hDΔ : D ⊆ Δ) (hn : G.IsNormal (j ⁻¹' discBd Δ))
    (hint : ∀ x ∈ discBd Δ, IsInteriorPoint x) (hsmall : (G.V ∩ C).ncard ≤ 1) (h2 :
      (G.V ∩ j ⁻¹' discBd Δ).ncard = 2) (hY : IsClosedDisc Y) (hΔY : Δ ⊆ Y \ discBd Y) :
    ∃ (a₁ a₂ x₀ x₁ : S) (W : GraphWalk G.toGraph x₁ a₁) (Q : Path x₀ a₁), a₁ ≠ a₂
      ∧ G.V ∩ j ⁻¹' discBd Δ = {a₁, a₂} ∧ x₀ ∈ C ∧ (∀ t, j (Q t) ∈ Y) ∧ (∀ x ∈
        (walkDrawing G W).U, x = a₁ ∨ j x ∈ discInt Δ) ∧ (∀ X, IsOArc X → ¬ X ⊆
          (walkDrawing G W).U) ∧
      (∀ s ∈ G.V ∩ C, s = x₀ ∧ x₁ = x₀) ∧ (x₀ ∈ G.V → ∀ t, Q t ∈ (walkDrawing G W).U) := by
  classical
  have hT := hc.isSurface
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : T2Space T := hT.2.1
  have hcj : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  have hnilU : ∀ {a : S} (ha : a ∈ G.V), (walkDrawing G (GraphWalk.nil (G := G.toGraph) ha)).U
    = {a} := fun {a} ha => by
    ext x
    rw [mem_walkDrawing_U]
    simp [GraphWalk.support, GraphWalk.edges]
  have hnilO : ∀ {a : S} (ha : a ∈ G.V) (X : Set S), IsOArc X → ¬ X ⊆ (walkDrawing G (GraphWalk.nil
    (G := G.toGraph) ha)).U := fun {a} ha X hX hs => by
    rw [hnilU ha] at hs
    obtain ⟨y, hy, hne⟩ := IsOArc.exists_ne hX a
    exact hne (hs hy)
  obtain ⟨p, q, hpq, hset⟩ := ncard_eq_two.mp h2
  have hbdV : ∀ {x : S}, x ∈ ({p, q} : Set S) → x ∈ G.V ∧ j x ∈ discBd Δ := fun {x} hx => by
    rw [← hset] at hx
    exact hx
  rcases (ncard_le_one_iff_eq (G.finite_V.subset inter_subset_left)).mp hsmall with hemp | ⟨c₀,
    hone⟩
  · -- no vertex on the cuff
    obtain ⟨x₀, hx₀⟩ := (isConnected_of_isOArc ((cuff_statement.{u} S hS).2.2 C hC)).nonempty
    obtain ⟨Q, hQ⟩ := exists_path_in_collar hc hΔ hDΔ hY hΔY hx₀ (hbdV (.inl rfl)).2
    have ha := (hbdV (x := p) (.inl rfl)).1
    refine ⟨p, q, x₀, p, .nil ha, Q, hpq, hset, hx₀, hQ, fun x hx => ?_, hnilO ha,
      fun s hs => ?_, fun h => ?_⟩
    · rw [hnilU ha] at hx
      exact .inl hx
    · exact absurd (hemp ▸ hs) (notMem_empty s)
    · exact absurd (hemp ▸ (⟨h, hx₀⟩ : x₀ ∈ G.V ∩ C)) (notMem_empty x₀)
  · have hc₀ : c₀ ∈ G.V ∩ C := by
      rw [hone]
      exact rfl
    obtain ⟨a₁, ha₁, hab, W₀, hs₀, hin₀, hed₀⟩ := exists_walk_to_arc hS hC hc hns hbl hΔ hDΔ hn
      hint hone
    have ha₁m : a₁ ∈ ({p, q} : Set S) := hset ▸ (⟨ha₁, hab⟩ : a₁ ∈ G.V ∩ j ⁻¹' discBd Δ)
    obtain ⟨a₂, hne₂, hset₂⟩ : ∃ a₂, a₁ ≠ a₂ ∧ G.V ∩ j ⁻¹' discBd Δ = {a₁, a₂} := by
      rcases ha₁m with rfl | rfl
      · exact ⟨q, hpq, hset⟩
      · exact ⟨p, hpq.symm, hset.trans (pair_comm _ _)⟩
    have hsC : ∀ s ∈ G.V ∩ C, s = c₀ := fun s hs => by
      rw [hone] at hs
      exact hs
    by_cases heq : c₀ = a₁
    · subst heq
      refine ⟨c₀, a₂, c₀, c₀, .nil ha₁, Path.refl _, hne₂, hset₂, hc₀.2, fun _ => ?_,
        fun x hx => ?_, hnilO ha₁, fun s hs => ⟨hsC s hs, rfl⟩, fun _ t => ?_⟩
      · exact (hΔY (hDΔ (Surface.discBd_subset D (by
          rw [hc.discBd_eq]
          exact mem_image_of_mem j hc₀.2)))).1
      · rw [hnilU ha₁] at hx
        exact .inl hx
      · rw [hnilU ha₁]
        exact rfl
    · let W : GraphWalk G.toGraph c₀ a₁ := W₀.reverse
      have hsW : W.IsSimple := by
        unfold GraphWalk.IsSimple
        rw [GraphWalk.support_reverse]
        exact List.nodup_reverse.mpr hs₀
      have hsupp : ∀ v, v ∈ W.support ↔ v ∈ W₀.support := fun v => by
        rw [GraphWalk.support_reverse, List.mem_reverse]
      have hedg : ∀ e, e ∈ W.edges ↔ e ∈ W₀.edges := fun e => by
        rw [GraphWalk.edges_reverse, List.mem_reverse]
      have hL : IsLineWithEnds (walkDrawing G W).U c₀ a₁ := isLine_of_isPathBetween
        (walkDrawing_isPathBetween G hsW) heq
      have hLint : ∀ x ∈ (walkDrawing G W).U, x = a₁ ∨ j x ∈ discInt Δ := fun x hx => by
        by_cases hxa : x = a₁
        · exact .inl hxa
        refine .inr ?_
        rcases (mem_walkDrawing_U G W).mp hx with h | ⟨e, he, hxe⟩
        · exact hin₀ x ((hsupp x).mp h) hxa
        · by_cases hxV : x ∈ G.V
          · exact hin₀ x ((hsupp x).mp (walk_closure_vertex W e he x hxe hxV)) hxa
          · have heE : e ∈ G.E := mem_E_of_mem_edges W he
            have : x ∈ e := by
              rw [← GM09.closure_edge_diff_V_eq G heE]
              exact ⟨hxe, hxV⟩
            exact hed₀ e ((hedg e).mp he) (mem_image_of_mem j this)
      obtain ⟨f, hf0, hf1⟩ := id hL
      let Q : Path c₀ a₁ := ⟨⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩, hf0, hf1⟩
      have hQL : ∀ t, Q t ∈ (walkDrawing G W).U := fun t => (f t).2
      refine ⟨a₁, a₂, c₀, c₀, W, Q, hne₂, hset₂, hc₀.2, fun t => ?_, hLint, fun X hX hs
        => not_isOArc_of_subset_line (IsLineWithEnds.isLine hL) hX hs, fun s hs
          => ⟨hsC s hs, rfl⟩, fun _ => hQL⟩
      have hj : j (Q t) ∈ Δ := by
        rcases hLint _ (hQL t) with h | h
        · rw [h]
          exact Surface.discBd_subset Δ hab
        · exact h.1
      exact (hΔY hj).1

/-- For any surface `S ≃ₜ SurfaceModel a b c`, the number of cuffs is `c`. -/
theorem ncard_cuffs_of_homeomorph_surfaceModel {a b c : ℕ} (he : Nonempty
  (S ≃ₜ SurfaceModel a b c)) : (cuffs S).ncard = c := by
  rcases he with ⟨e⟩
  obtain ⟨ht, f, hf⟩ := presents_ew a b c
  have : T2Space (SurfaceModel a b c) := ht
  rw [ncard_cuffs_congr e, ncard_cuffs hf]

theorem two_mul_le_vSurface {a b c : ℕ} (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (k : ℕ) : 2 * k
  ≤ vSurface S k :=
  le_csInf ⟨_, a, b, c, hm, rfl⟩ (by
    rintro _ ⟨_, _, _, _, rfl⟩
    exact Nat.le_add_left _ _)

/-- Adding isolated vertices keeps a forest. -/
theorem IsSurfaceForest.addIsolated [T1Space S] (hS : IsSurface S) [ConnectedSpace S] {H : Drawing
  S} (hH : IsSurfaceForest H) {B : Set S} (hf : B.Finite) (hB : Disjoint B H.U) : IsSurfaceForest
    (GM07.addIsolated H B hf hB) := by
  have : T2Space S := hS.2.1
  refine ⟨?_, isForest_of_noOArc fun X hX hs => ?_⟩
  · rintro x ⟨hb, hx | hx⟩
    · exact .inl (hH.1 ⟨hb, hx⟩)
    · exact .inr hx
  · have hpre := (isConnected_of_isOArc hX).isPreconnected
    by_cases h1 : (X ∩ H.U).Nonempty
    · by_cases h2 : (X ∩ B).Nonempty
      · obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp hpre _ _ H.isClosed_U hf.isClosed
          hs h1 h2
        exact disjoint_left.mp hB hz2 hz1
      · refine noOArc_of_forest hH.2 hX fun z hz => ?_
        rcases hs hz with h3 | h3
        · exact h3
        · exact absurd ⟨z, hz, h3⟩ h2
    · have hXB : X ⊆ B := fun z hz => by
        rcases hs hz with h3 | h3
        · exact absurd ⟨z, hz, h3⟩ h1
        · exact h3
      obtain ⟨y, hy⟩ := (isConnected_of_isOArc hX).nonempty
      obtain ⟨y', hy', hne⟩ := IsOArc.exists_ne hX y
      exact hpre.infinite_of_nontrivial ⟨y', hy', y, hy, hne⟩ (hf.subset hXB)

private theorem pulled_vertices_on_shifted_cuff
    (S : Type u)
    [TopologicalSpace S]
    [T1Space S]
    (G : Drawing S)
    (C : Set S)
    (T : Type u)
    [TopologicalSpace T]
    (j : S → T)
    (Δ : Set T)
    (Y : Set T)
    (a₁ : S)
    (a₂ : S)
    (x₀ : S)
    (x₁ : S)
    (W : GraphWalk G.toGraph x₁ a₁)
    (Q : Path x₀ a₁)
    (hset : G.V ∩ j ⁻¹' discBd Δ = {a₁, a₂})
    (hx₀C : x₀ ∈ C)
    (hQY : ∀ (t : ↑unitInterval), j (Q t) ∈ Y)
    (hsC : ∀ s ∈ G.V ∩ C, s = x₀ ∧ x₁ = x₀)
    (hQL : x₀ ∈ G.V → ∀ (t : ↑unitInterval), Q t ∈ (walkDrawing G W).U)
    (h : S → S)
    (Φ : ↑unitInterval × S → S)
    (hhi : Injective h)
    (hh0 : h x₀ = a₁)
    (P : Path x₀ a₁)
    (hP : ∀ (t : ↑unitInterval), P t = Φ (t, x₀))
    (hPQ : P.Homotopic Q)
    (c₂ : S)
    (hc₂C : c₂ ∈ C)
    (hc₂ : h c₂ = a₂)
    (G' : Drawing S)
    (hG'V : G'.V = h ⁻¹' G.V)
    (hCA : ∀ x ∈ C, j (h x) ∈ discBd Δ)
    (hx₀V : x₀ ∈ G'.V)
    (hc₂V : c₂ ∈ G'.V)
    (hx₀c₂ : x₀ ≠ c₂) :
    G'.V ∩ C = {x₀, c₂} := by
  apply subset_antisymm
  · rintro x ⟨hxV, hxC⟩
    rw [hG'V] at hxV
    have h1 : h x ∈ G.V ∩ j ⁻¹' discBd Δ := ⟨hxV, hCA x hxC⟩
    rw [hset] at h1
    rcases h1 with h2 | h2
    · exact .inl (hhi (h2.trans hh0.symm))
    · exact .inr (hhi (h2.trans hc₂.symm))
  · rintro x (rfl | rfl)
    · exact ⟨hx₀V, hx₀C⟩
    · exact ⟨hc₂V, hc₂C⟩

private theorem one_fewer_small_cuff
    (S : Type u)
    [TopologicalSpace S]
    (g₀ : ℕ)
    (G : Drawing S)
    (hcount : {C | C ∈ cuffs S ∧ (G.V ∩ C).ncard ≤ 1}.ncard = g₀ + 1)
    (C : Set S)
    (hC : C ∈ cuffs S)
    (hsmall : (G.V ∩ C).ncard ≤ 1)
    (G' : Drawing S)
    (hG'C2 : (G'.V ∩ C).ncard = 2)
    (hother : ∀ C' ∈ cuffs S, C' ≠ C → G'.V ∩ C' = G.V ∩ C') :
    {C' | C' ∈ cuffs S ∧ (G'.V ∩ C').ncard ≤ 1}.ncard = g₀ := by
  have heq : {C' ∈ cuffs S | (G'.V ∩ C').ncard ≤ 1} = {C' ∈ cuffs S | (G.V ∩ C').ncard ≤ 1} \ {C}
    := by
    ext C'
    constructor
    · rintro ⟨h1, h2⟩
      have hne' : C' ≠ C := fun e => by
        rw [e, hG'C2] at h2
        omega
      exact ⟨⟨h1, hother C' h1 hne' ▸ h2⟩, hne'⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (hother C' h1 h3).symm ▸ h2⟩
  have hmem : C ∈ {C' ∈ cuffs S | (G.V ∩ C').ncard ≤ 1} := ⟨hC, hsmall⟩
  rw [heq, ncard_sdiff_singleton_of_mem hmem, hcount]
  rfl

private theorem isolated_vertices_restore_boundary_agreement
    (S : Type u)
    [TopologicalSpace S]
    [T1Space S]
    (G : Drawing S)
    (H : Drawing S)
    (hVeq : G.V ∩ bd S = H.V ∩ bd S)
    (C : Set S)
    (T : Type u)
    (j : S → T)
    (Y : Set T)
    (a₁ : S)
    (a₂ : S)
    (x₀ : S)
    (x₁ : S)
    (W : GraphWalk G.toGraph x₁ a₁)
    (Q : Path x₀ a₁)
    (hx₀C : x₀ ∈ C)
    (hQY : ∀ (t : ↑unitInterval), j (Q t) ∈ Y)
    (hsC : ∀ s ∈ G.V ∩ C, s = x₀ ∧ x₁ = x₀)
    (hQL : x₀ ∈ G.V → ∀ (t : ↑unitInterval), Q t ∈ (walkDrawing G W).U)
    (h : S → S)
    (Φ : ↑unitInterval × S → S)
    (hh0 : h x₀ = a₁)
    (P : Path x₀ a₁)
    (hP : ∀ (t : ↑unitInterval), P t = Φ (t, x₀))
    (hPQ : P.Homotopic Q)
    (hs : IsCuffShift C h Φ)
    (c₂ : S)
    (hc₂C : c₂ ∈ C)
    (hc₂ : h c₂ = a₂)
    (G' : Drawing S)
    (hG'V : G'.V = h ⁻¹' G.V)
    (hx₀V : x₀ ∈ G'.V)
    (hc₂V : c₂ ∈ G'.V)
    (hx₀c₂ : x₀ ≠ c₂)
    (hG'C : G'.V ∩ C = {x₀, c₂}) :
    let B : Set S := {x₀, c₂} \ H.V
    ∀ (hBf : B.Finite),
    ∀ (hB : Disjoint B H.U),
    (IsSurfaceForest (addIsolated H B hBf hB)) →
    ((addIsolated H B hBf hB).V = H.V ∪ B) →
    (addIsolated H B hBf hB).V ∩ bd S = G'.V ∩ bd S := by
  intro B hBf hB hHf' hH'V
  rw [hH'V]
  ext x
  constructor
  · rintro ⟨hx | hx, hb⟩
    · refine ⟨?_, hb⟩
      have hxG : x ∈ G.V ∩ bd S := hVeq.symm ▸ (⟨hx, hb⟩ : x ∈ H.V ∩ bd S)
      by_cases hxC : x ∈ C
      · rw [(hsC x ⟨hxG.1, hxC⟩).1]
        exact hx₀V
      · rw [hG'V, mem_preimage, (hs.fix x hb hxC).1]
        exact hxG.1
    · rcases hx.1 with rfl | rfl
      · exact ⟨hx₀V, hb⟩
      · exact ⟨hc₂V, hb⟩
  · rintro ⟨hx, hb⟩
    refine ⟨?_, hb⟩
    by_cases hxC : x ∈ C
    · have h1 : x ∈ ({x₀, c₂} : Set S) := hG'C ▸ (⟨hx, hxC⟩ : x ∈ G'.V ∩ C)
      by_cases h2 : x ∈ H.V
      · exact .inl h2
      · exact .inr ⟨h1, h2⟩
    · rw [hG'V, mem_preimage, (hs.fix x hb hxC).1] at hx
      have : x ∈ H.V ∩ bd S := hVeq ▸ (⟨hx, hb⟩ : x ∈ G.V ∩ bd S)
      exact .inl this.1

/-- Graph Minors VII, Section 6, inductive step in the proof of (6.1) (pages 237–238):
When `g = {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard = g₀ + 1`, choosing a cuff `C` with
`|V(G) ∩ C| ≤ 1` and cutting along the surrounding `O`-arc `A` with `|V(G) ∩ A| = 2` yields a
surface `S' ≃ₜ S`, a boundary-linked proper graph `G'` in `S'`, and a forest `H'` in `S'` with
`g₀` cuffs containing `≤ 1` vertex of `G'`, such that `IsGFeasible G' H'` implies
`IsGFeasible G H`. The bound `g₀ + 1 ≤ k` says that `2k - 2g` is not negative, as it is in the
paper: subtraction here is cut off at `0`, and
the conclusion fails for `k = 0`. -/
theorem smallCuffReductionStep (S : Type u) [TopologicalSpace S] [T1Space S] (hS : IsSurface S)
  (a b c : ℕ) (hc2 : 2 ≤ c) (hne : (a, b, c) ≠ (0, 0, 2)) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (k g₀ : ℕ) (G H : Drawing S) (hk : g₀ + 1 ≤ k) (hbl : IsBoundaryLinked G)
      (hcount : {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.ncard = g₀ + 1) (hbdc : (G.V ∩ bd S).ncard
        ≤ 2 * k - 2 * (g₀ + 1))
    (hα : 9 * k * vSurface S k < alpha G) (hHf : IsSurfaceForest H) (hVeq : G.V ∩ bd S
      = H.V ∩ bd S) :
    ∃ (S' : Type u) (_ : TopologicalSpace S') (_ : T1Space S') (G' H' : Drawing S'),
      IsSurface S' ∧ Nonempty (S' ≃ₜ SurfaceModel a b c) ∧
      IsBoundaryLinked G' ∧
      {C' ∈ cuffs S' | (G'.V ∩ C').ncard ≤ 1}.ncard = g₀ ∧
      (G'.V ∩ bd S').ncard ≤ 2 * k - 2 * g₀ ∧
      9 * k * vSurface S' k < alpha G' ∧
      IsSurfaceForest H' ∧ G'.V ∩ bd S' = H'.V ∩ bd S' ∧
      (IsGFeasible G' H' → IsGFeasible G H) := by
  classical
  have : ConnectedSpace S := connectedSpace_of_model hm
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have habc : 3 ≤ 3 * a + 3 * b + c := by
    by_contra hlt
    have h1 : a = 0 := by omega
    have h2 : b = 0 := by omega
    have h3 : c = 2 := by omega
    exact hne (by rw [h1, h2, h3])
  have hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2) := not_cylinder_of_model habc hm
  have hG := hbl.1
  have hnsS : ¬ IsSphere S := not_isSphere_of_model hm (by omega)
  obtain ⟨C, hC, hsmall⟩ : {C ∈ cuffs S | (G.V ∩ C).ncard ≤ 1}.Nonempty :=
    nonempty_of_ncard_ne_zero (by rw [hcount]; omega)
  have hfinC : (cuffs S).Finite := (cuff_statement.{u} S hS).2.1
  have hnc := ncard_cuffs_of_homeomorph_surfaceModel hm
  obtain ⟨C₁, hC₁, hC₁ne⟩ := exists_ne_of_one_lt_ncard (s := cuffs S) (by rw [hnc]; omega) C
  have hCsub : ∀ {C' : Set S}, C' ∈ cuffs S → C' ⊆ bd S := fun hC' =>
    connectedComponentIn_subset_of_cuff hC'
  obtain ⟨T, tT, j, D, hcap, hbT⟩ := exists_cappedCuff hS hC
  have hT := hcap.isSurface
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hcj : IsClosedEmbedding j := hcap.isEmbedding.continuous.isClosedEmbedding
    hcap.isEmbedding.injective
  have hii := hcj.injective
  have hns : ¬ IsSphere T := not_isSphere_cap hS habc hm hcap
  have hv := two_mul_le_vSurface hm k
  have hk1 : 1 ≤ k := by omega
  have hbig : 2 * k + 9 ≤ 9 * k * vSurface S k := by
    have h1 : 9 * k * (2 * k) ≤ 9 * k * vSurface S k := Nat.mul_le_mul_left _ hv
    nlinarith
  have hα₂ : ∀ C' ∈ cuffs S, C' ≠ C → 2 + (G.V ∩ C').ncard < alpha G := fun C' h1 _ => by
    have h2 : (G.V ∩ C').ncard ≤ (G.V ∩ bd S).ncard := ncard_le_ncard (inter_subset_inter_right _
      (hCsub h1)) (G.finite_V.subset inter_subset_left)
    omega
  obtain ⟨Δ, hd, h2v, hoffT, hmaxF⟩ := exists_two_vertex_disc hS habc hm hcyl hG hC hcap hbT hsmall
    (by omega) hα₂ hC₁ hC₁ne
  obtain ⟨hΔ, hDΔ, hn, -⟩ := hd
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := fun x hx => by
    by_contra h
    exact disjoint_left.mp hoffT (Surface.discBd_subset Δ hx) h
  obtain ⟨Y, hY, hΔY, hYW⟩ := exists_disc_around hman hΔ hint (isClosed_bd T).isOpen_compl
    (fun x hx hb => disjoint_left.mp hoffT (Surface.discBd_subset Δ hx) hb)
  have hYoff : ∀ x, x ∈ Y → x ∉ bd T := fun x hx hb => by
    rcases hYW hx with h | h
    · exact disjoint_left.mp hoffT h hb
    · exact h hb
  obtain ⟨a₁, a₂, x₀, x₁, W, Q, hne₁₂, hset, hx₀C, hQY, hLint, hLO, hsC, hQL⟩
    := exists_pendant_walk hS hC hcap hns hbl hΔ hDΔ hn hint hsmall h2v hY hΔY
  have ha₁ : a₁ ∈ G.V ∩ j ⁻¹' discBd Δ := hset ▸ mem_insert _ _
  have ha₂ : a₂ ∈ G.V ∩ j ⁻¹' discBd Δ := hset ▸ mem_insert_of_mem _ rfl
  obtain ⟨h, Φ, hhc, hΦc, hhi, hfix, hzero, hone, hrange, himC, hh0, P, hP, hPQ⟩
    := exists_capped_push hcap hΔ hDΔ hY hΔY (discBd_subset_range hcap hDΔ) hx₀C ha₁.2 Q hQY
  have hs : IsCuffShift C h Φ := ⟨hhc, hΦc, hhi, hzero, hone, fun x hb hx => hfix x fun hi
    => hYoff _ hi.1 (hbT ▸ mem_image_of_mem j ⟨hb, hx⟩)⟩
  have hcl := hs.isClosedEmbedding
  obtain ⟨c₂, hc₂C, hc₂⟩ : ∃ c₂ ∈ C, h c₂ = a₂ := by
    have : a₂ ∈ h '' C := himC ▸ ha₂.2
    exact this
  -- the part of `G` outside `A`
  let Z : Set S := j ⁻¹' discInt Δ
  have hZo : IsOpen Z := (hΔ.isOpen_discInt hman).preimage hcj.continuous
  have hrZ : ∀ x, h x ∉ Z := fun x hx => by
    have : h x ∈ j ⁻¹' (discInt Δ)ᶜ := hrange ▸ mem_range_self x
    exact this hx
  have hedge : ∀ e ∈ G.E, (∃ y ∈ e, y ∉ Z) → Disjoint e Z := by
    rintro e he ⟨y, hye, hyZ⟩
    have hpc : IsPreconnected (j '' e) := he.2.2.1.isConnected.isPreconnected.image _
      hcj.continuous.continuousOn
    have hdb : Disjoint (j '' e) (discBd Δ) := by
      rw [disjoint_left]
      rintro _ ⟨z, hz, rfl⟩ hzb
      have hzU := he.2.1 hz
      exact hzU.2 (hn ⟨hzb, hzU.1⟩)
    rcases inside_or_off hpc hΔ.isClosed (hdb.mono_right (frontier_disc_subset hman hΔ)) with h1 |
      h1
    · exact absurd (⟨interior_subset (h1 (mem_image_of_mem j hye)),
        disjoint_left.mp hdb (mem_image_of_mem j hye)⟩ : j y ∈ discInt Δ) hyZ
    · rw [disjoint_left]
      exact fun z hz hzZ => h1 (mem_image_of_mem j hz) hzZ.1
  obtain ⟨G₁, hG₁, hG₁U, hG₁V⟩ := exists_outside_drawing hZo hedge
  have hrU : G₁.U ⊆ range h := fun x hx => by
    rw [hrange]
    rw [hG₁U] at hx
    exact hx.2
  have : Nonempty S := ⟨x₀⟩
  obtain ⟨G', hG'U₁, hG'V₁, hmat⟩ := exists_pull_drawing hcl G₁ hrU
  have hG'U : G'.U = h ⁻¹' G.U := by
    rw [hG'U₁, hG₁U]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hrZ x⟩⟩
  have hG'V : G'.V = h ⁻¹' G.V := by
    rw [hG'V₁, hG₁V]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, hrZ x⟩⟩
  have hCA : ∀ x ∈ C, j (h x) ∈ discBd Δ := fun x hx => by
    have : h x ∈ j ⁻¹' discBd Δ := himC ▸ mem_image_of_mem h hx
    exact this
  have hG'p : G'.IsProper := by
    rintro x ⟨hb, hxU⟩
    rw [hG'U] at hxU
    rw [hG'V]
    by_cases hxC : x ∈ C
    · exact hn ⟨hCA x hxC, hxU⟩
    · have h1 := (hs.fix x hb hxC).1
      change h x ∈ G.V
      rw [h1]
      rw [mem_preimage, h1] at hxU
      exact hG ⟨hb, hxU⟩
  have hx₀V : x₀ ∈ G'.V := by
    rw [hG'V]
    change h x₀ ∈ G.V
    rw [hh0]
    exact ha₁.1
  have hc₂V : c₂ ∈ G'.V := by
    rw [hG'V]
    change h c₂ ∈ G.V
    rw [hc₂]
    exact ha₂.1
  have hx₀c₂ : x₀ ≠ c₂ := fun e => hne₁₂ (by rw [← hh0, e, hc₂])
  have hG'C : G'.V ∩ C = {x₀, c₂} := by
    exact pulled_vertices_on_shifted_cuff S G C T j Δ Y a₁ a₂ x₀ x₁ W Q hset hx₀C hQY hsC hQL h Φ
      hhi hh0 P hP hPQ c₂ hc₂C hc₂ G' hG'V hCA hx₀V hc₂V hx₀c₂
  have hG'C2 : (G'.V ∩ C).ncard = 2 := by
    rw [hG'C]
    exact ncard_pair hx₀c₂
  have hbl' : IsBoundaryLinked G' := boundaryLinked_of_shift hS hs habc hm hnsS hG'U hG'V hG'p hbl
    hC fun F h1 h2 h3 h4 => by
    rw [hG'C2]
    refine hmaxF F h1 h2 h3 ?_
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hi
    obtain ⟨z, rfl⟩ := h4 hy
    exact hrZ z hi
  have hαle : alpha G ≤ alpha G' := alpha_le_of_shift hS hs habc hm hnsS hG'U hG'V
    (exists_alphaCandidate hS habc hm hcyl hG'p hC hC₁ hC₁ne.symm)
  have hother : ∀ C' ∈ cuffs S, C' ≠ C → G'.V ∩ C' = G.V ∩ C' := fun C' h1 h2 => by
    ext x
    refine and_congr_left fun hx => ?_
    have hxC : x ∉ C := fun h3 => disjoint_left.mp (cuffs_disjoint h1 hC h2) hx h3
    have h3 := (hs.fix x (hCsub h1 hx) hxC).1
    rw [hG'V, mem_preimage, h3]
  have hcount' : {C' ∈ cuffs S | (G'.V ∩ C').ncard ≤ 1}.ncard = g₀ := by
    exact one_fewer_small_cuff S g₀ G hcount C hC hsmall G' hG'C2 hother
  have hbdsub : G'.V ∩ bd S ⊆ (G'.V ∩ C) ∪ (G.V ∩ bd S) := by
    rintro x ⟨hxV, hb⟩
    by_cases hxC : x ∈ C
    · exact .inl ⟨hxV, hxC⟩
    · refine .inr ⟨?_, hb⟩
      rw [hG'V, mem_preimage, (hs.fix x hb hxC).1] at hxV
      exact hxV
  have hbdc' : (G'.V ∩ bd S).ncard ≤ 2 * k - 2 * g₀ := by
    have h1 := ncard_le_ncard hbdsub ((G'.finite_V.subset inter_subset_left).union
      (G.finite_V.subset inter_subset_left))
    have h2 := ncard_union_le (G'.V ∩ C) (G.V ∩ bd S)
    omega
  -- the forest with the two new vertices
  let B : Set S := ({x₀, c₂} : Set S) \ H.V
  have hBf : B.Finite := (toFinite ({x₀, c₂} : Set S)).subset sdiff_subset
  have hB : Disjoint B H.U := by
    rw [disjoint_left]
    rintro x ⟨hx, hxV⟩ hxU
    have hxC : x ∈ C := by
      rcases hx with rfl | rfl
      · exact hx₀C
      · exact hc₂C
    exact hxV (hHf.1 ⟨hCsub hC hxC, hxU⟩)
  have hHf' : IsSurfaceForest (addIsolated H B hBf hB) := hHf.addIsolated hS hBf hB
  have hH'V : (addIsolated H B hBf hB).V = H.V ∪ B := rfl
  have hVb' : (addIsolated H B hBf hB).V ∩ bd S = G'.V ∩ bd S := by
    exact isolated_vertices_restore_boundary_agreement S G H hVeq C T j Y a₁ a₂ x₀ x₁ W Q hx₀C hQY
      hsC hQL h Φ hh0 P hP hPQ hs c₂ hc₂C hc₂ G' hG'V hx₀V hc₂V hx₀c₂ hG'C  hBf hB hHf' hH'V
  have hLm : (walkDrawing G W).U ∩ h '' G'.U ⊆ {a₁} := by
    rintro x ⟨hx, y, -, rfl⟩
    rcases hLint _ hx with h1 | h1
    · exact h1
    · exact absurd h1 (hrZ y)
  have hWb : ∀ v ∈ W.support, v ∈ bd S → v ∈ C := fun v hv hb => by
    by_contra hvC
    have h1 := hLint v ((mem_walkDrawing_U G W).mpr (.inl hv))
    have h2 : j v ∈ Δ := by
      rcases h1 with h3 | h3
      · rw [h3]
        exact Surface.discBd_subset Δ ha₁.2
      · exact h3.1
    exact disjoint_left.mp hoffT h2 (hbT ▸ mem_image_of_mem j ⟨hb, hvC⟩)
  have hHC : ∀ s ∈ H.V ∩ bd S, s ∈ C → s = x₀ ∧ x₁ = x₀ := fun s hs' hsC' => by
    have : s ∈ G.V ∩ bd S := hVeq.symm ▸ hs'
    exact hsC s ⟨this.1, hsC'⟩
  have hQ' : x₀ ∈ H.V → ∀ t, Q t ∈ (walkDrawing G W).U := fun hx => by
    have : x₀ ∈ G.V ∩ bd S := hVeq.symm ▸ (⟨hx, hCsub hC hx₀C⟩ : x₀ ∈ H.V ∩ bd S)
    exact hQL this.1
  refine ⟨S, inferInstance, inferInstance, G', addIsolated H B hBf hB, hS, hm, hbl', hcount',
    hbdc', lt_of_lt_of_le hα hαle, hHf', hVb'.symm, ?_⟩
  exact fun hfe => isGFeasible_of_shift hS hs hG hHf hVeq hmat hG₁ hVb' hh0 ⟨hx₀V,
    hCsub hC hx₀C⟩ W hLm hLO hWb hHC P Q hP hPQ hQ' hfe

end GraphMinor.GM07
