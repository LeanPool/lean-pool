/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Delete
public import LeanPool.GraphMinor.GM19.Section6Path
public import LeanPool.GraphMinor.GM19.Section6Max
public import LeanPool.GraphMinor.GM19.Section6Five

/-!
# Theorem (6.6) of Graph Minors XIX

We follow the proof on pages 341-342. Let `σ'` be a largest enlargement, from
`exists_full_enlargement`. Let `r` be a region of `G'`, let `a, b` be vertices of `σ'(v)` in the
closure of `r`. Take a path `Q` of `σ'(v)` from `a` to `b`, and a line `L` from `a` to `b` through
`r`. By (6.5), the O-arc `F = U(Q) ∪ L` bounds a disc `Δ`. Claim (1) of the paper is
`mem_of_closed_adj`. Since `G` is a block, all branch sets other than `σ'(v)` lie on one side of
`F`. If they lie outside `Δ` we use claim (1). If they lie inside, then the surface is a sphere by
(6.5), since `exists_curve_off_disc` gives a non-null-homotopic O-arc off the inside of `Δ`, and we
use claim (1) for the other disc.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GM11

section

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem IsEnlargement.restrict {G G' H H' : Drawing S} {σv : S → Drawing S} {σe : Set S → Set S}
  (hσ : IsEnlargement G G' σv σe) (hH : H.IsSubdrawing G)
    (hτ : ∀ u ∈ H.V, (σv u).IsSubdrawing H') (he : ∀ e ∈ H.E, σe e ∈ H'.E) : IsEnlargement H H' σv
      σe :=
  ⟨he, hσ.edge_injOn.mono hH.2, hτ, fun v hv => hσ.vertex_nonempty v (hH.1 hv), fun v hv
    => hσ.vertex_connected v (hH.1 hv),
    fun a ha b hb => hσ.vertex_disjoint a (hH.1 ha) b (hH.1 hb), fun e he v hv => hσ.ends_iff e
      (hH.2 he) v (hH.1 hv)⟩

/-- Deleting `v` from `G`, and from `G'` a set that misses the other branch sets. -/
theorem IsEnlargement.delete {G G' : Drawing S} (hl : LoopFree G) (hl' : LoopFree G') {σv : S
  → Drawing S} {σe : Set S → Set S} (hσ : IsEnlargement G G' σv σe) {v : S} {X : Set S}
    (hX : ∀ u ∈ G.V, u ≠ v → Disjoint (σv u).V X) : IsEnlargement (delete G {v})
      (delete G' X) σv σe := by
  refine hσ.restrict (delete_subdrawing G {v}) (fun u hu => ?_) fun e he => ?_
  · rw [delete_V] at hu
    have hu' : u ≠ v := fun h => hu.2 h
    have hsub := hσ.vertex_subdrawing u hu.1
    refine ⟨?_, ?_⟩
    · rw [delete_V]
      exact fun x hx => ⟨hsub.1 hx, fun h => Set.disjoint_left.mp (hX u hu.1 hu') hx h⟩
    · rw [delete_E]
      exact fun e he => ⟨hsub.2 he, Set.disjoint_left.mpr fun x hx h => Set.disjoint_left.mp
        (hX u hu.1 hu') (tilde_subset_V _ he hx) h⟩
  · rw [delete_E] at he ⊢
    refine ⟨hσ.edge_mem e he.1, Set.disjoint_left.mpr fun x hx h => ?_⟩
    obtain ⟨u, hu, hue, hxu⟩ := hσ.end_mem hl hl' he.1 hx
    have huv : u ≠ v := fun h' => Set.disjoint_left.mp he.2 hue h'
    exact Set.disjoint_left.mp (hX u hu huv) hxu h

omit [T2Space S] in
theorem Drawing.IsGM19Drawing.sub {H G : Drawing S} (hG : G.IsGM19Drawing)
  (h : H.IsSubdrawing G) : H.IsGM19Drawing :=
  ⟨fun e he => hG.no_loops e (h.2 he), fun e he => hG.border_or_disjoint e (h.2 he)⟩

/-- A connected set off the boundary of a disc is inside it or outside it. -/
theorem side_const (hT : IsClosedSurface S) {Δ C : Set S} (hΔ : IsClosedDisc Δ)
  (hC : IsPreconnected C) (hd : Disjoint C (discBd Δ)) {x y : S} (hx : x ∈ C) (hy : y ∈ C)
    (hxΔ : x ∈ Δ) : y ∈ Δ := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  by_contra hyΔ
  obtain ⟨w, -, hw1, hw2⟩ := hC _ _ (hΔ.isOpen_discInt hman) hΔ.isClosed.isOpen_compl (fun w hw
    => by
    by_cases h' : w ∈ Δ
    · exact .inl ⟨h', Set.disjoint_left.mp hd hw⟩
    · exact .inr h') ⟨x, hx, hxΔ, Set.disjoint_left.mp hd hx⟩ ⟨y, hy, hyΔ⟩
  exact hw2 hw1.1

/-- In a surface that is not a sphere, there is a non-null-homotopic O-arc off the inside of a given
disc. It comes from `exists_reroute`. -/
theorem exists_curve_off_disc (hT : IsClosedSurface S) {Δ F : Set S} (hΔ : IsClosedDisc Δ)
  (hF : IsOArc F) (hnn : ¬ IsNullHomotopicOArc F) :
    ∃ C, IsOArc C ∧ ¬ IsNullHomotopicOArc C ∧ Disjoint C (discInt Δ) := by
  classical
  by_cases hm : (F ∩ Δ).Nonempty
  swap
  · exact ⟨F, hF, hnn, Set.disjoint_left.mpr fun x hx hxI => hm ⟨x, hx, hxI.1⟩⟩
  have hO := hΔ.isOArc_discBd
  have hch : ∀ a b, ∃ P : Set S, a ∈ discBd Δ → b ∈ discBd Δ → P ⊆ discBd Δ ∧ (a ≠ b
    → IsLineWithEnds P a b) ∧ (a = b → P = {a}) := fun a b => by
    by_cases ha : a ∈ discBd Δ
    swap
    · exact ⟨∅, fun h => absurd h ha⟩
    by_cases hb : b ∈ discBd Δ
    swap
    · exact ⟨∅, fun _ h => absurd h hb⟩
    by_cases hab : a = b
    · exact ⟨{a}, fun _ _ => ⟨singleton_subset_iff.mpr ha, fun h => absurd hab h, fun _ => rfl⟩⟩
    obtain ⟨A, B, hA, hB, hAB, hi⟩ := hO.lines ha hb hab
    exact ⟨A, fun _ _ => ⟨hAB ▸ subset_union_left, fun _ => hA, fun h => absurd h hab⟩⟩
  choose P hP using hch
  obtain ⟨C, a, b, hC, hCnn, haF, hbF, -, hCs⟩ := exists_reroute hT hΔ hF hnn hm P fun a ha b hb
    => by
    obtain ⟨h1, h2, h3⟩ := hP a b ha hb
    exact ⟨h1.trans (Surface.discBd_subset Δ), h2, h3⟩
  refine ⟨C, hC, hCnn, Set.disjoint_left.mpr fun x hx hxI => ?_⟩
  rcases hCs hx with h | h
  · exact h.2 hxI.1
  · exact hxI.2 ((hP a b haF.2 hbF.2).1 h)

omit [T2Space S] in
theorem exists_edge_at_vertex {G : Drawing S} (hc : (G.adj.induce G.V).Preconnected) {a b : S}
  (ha : a ∈ G.V) (hb : b ∈ G.V) (hab : a ≠ b) : ∃ e ∈ G.E, a ∈ tilde e := by
  by_contra hno
  have hY := (preconnected_iff_connIn G G.V).mp hc {a} (singleton_subset_iff.mpr ha) ⟨a, rfl⟩ fun x
    hx y _ hxy => by
    obtain ⟨-, -, -, e, he, h1, -⟩ := hxy
    exact absurd ⟨e, he, mem_singleton_iff.mp hx ▸ h1⟩ hno
  exact hab (mem_singleton_iff.mp (hY ▸ hb)).symm

private theorem adjacent_vertices_stay_on_same_disc_side
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    (hT : IsClosedSurface S)
    {G' : Drawing S}
    (hl' : LoopFree G')
    (F : Set S)
    (hedge : ∀ e ∈ Drawing.E G', (e ∩ F).Nonempty → e ⊆ F)
    (hFcl : IsClosed F)
    (hclF : ∀ e ∈ Drawing.E G', (closure e ∩ F).Nonempty → (e ∩ F).Nonempty ∨ (tilde e ∩
      F).Nonempty)
    (Δ : Set S)
    (hΔ : IsClosedDisc Δ)
    (hΔF : discBd Δ = F)
    {x : S}
    {y : S}
    (hxF : x ∉ F)
    (hyF : y ∉ F)
    (hxy : G'.adj.Adj x y)
    (hxΔ : x ∈ Δ) :
    y ∈ Δ := by
  obtain ⟨hne, -, -, e, he, h1, h2⟩ := hxy
  obtain ⟨p, q, -, hti, hLn⟩ := hl' e he
  have hd : Disjoint (closure e) (discBd Δ) := by
    rw [hΔF]
    refine Set.disjoint_left.mpr fun z hz hzF => ?_
    rcases hclF e he ⟨z, hz, hzF⟩ with h3 | ⟨w, hw, hwF⟩
    · exact hxF (closure_minimal (hedge e he h3) hFcl h1.1)
    · rw [hti] at hw h1 h2
      have hcases : w = x ∨ w = y := by
        rcases hw with rfl | hw <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hne
        · exact .inl h1.symm
        · exact .inr h2.symm
        · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) hne
        · exact absurd (h1.trans h2.symm) hne
        · exact .inr ((mem_singleton_iff.mp hw).trans (mem_singleton_iff.mp h2).symm)
        · exact .inl ((mem_singleton_iff.mp hw).trans (mem_singleton_iff.mp h1).symm)
        · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) hne
      rcases hcases with rfl | rfl
      · exact hxF hwF
      · exact hyF hwF
  exact side_const hT hΔ hLn.isPreconnected_self hd h1.1 h2.1 hxΔ

private theorem represented_vertex_stays_on_same_disc_side
    {S : Type}
    [TopologicalSpace S]
    {G : Drawing S}
    {G' : Drawing S}
    {τ : S → Drawing S}
    {σe : Set S → Set S}
    (hτ : IsEnlargement G G' τ σe)
    {v : S}
    (F : Set S)
    (hbdV : ∀ u ∈ G.V, u ≠ v → ∀ x ∈ (τ u).V, x ∉ F)
    (Δ : Set S)
    (hsideadj : ∀ {x y : S}, x ∉ F → y ∉ F → G'.adj.Adj x y → x ∈ Δ → y ∈ Δ) :
    let W : Set S := {u | (u ∈ G.V ∧ u ≠ v) ∧ ∃ x ∈ (τ u).V, x ∈ Δ}
    ∀ (u : S),
    (u ∈ W) →
    ∀ (x : S),
    (x ∈ (τ u).V) →
    x ∈ Δ := by
  intro W u hu x hx
  obtain ⟨⟨huV, huv⟩, x₀, hx₀, hx₀Δ⟩ := hu
  have h1 := (preconnected_iff_connIn _ _).mp (hτ.vertex_connected u huV) {z | z ∈ (τ u).V
    ∧ z ∈ Δ} (fun z hz => hz.1) ⟨x₀, hx₀, hx₀Δ⟩ fun p hp q hq hpq =>
    ⟨hq, hsideadj (hbdV u huV huv p hp.1) (hbdV u huV huv q hq) (adj_mono
      (hτ.vertex_subdrawing u huV) hpq) hp.2⟩
  have h2 : x ∈ {z | z ∈ (τ u).V ∧ z ∈ Δ} := by rw [h1]; exact hx
  exact h2.2

private theorem remaining_minor_drawing_lies_inside_disc
    {S : Type}
    [TopologicalSpace S]
    [T2Space S]
    (hT : IsClosedSurface S)
    {G' : Drawing S}
    (hl' : LoopFree G')
    (F : Set S)
    (hedge : ∀ e ∈ Drawing.E G', (e ∩ F).Nonempty → e ⊆ F)
    (hFcl : IsClosed F)
    (hclF : ∀ e ∈ Drawing.E G', (closure e ∩ F).Nonempty → (e ∩ F).Nonempty ∨ (tilde e ∩
      F).Nonempty)
    (Δ : Set S)
    (hΔ : IsClosedDisc Δ)
    (hΔF : discBd Δ = F) :
    let X : Set S := (discInt Δ)ᶜ
    ∀ (x : S),
    (x ∈ (delete G' X).U) →
    x ∈ discInt Δ := by
  intro X x hx
  rw [delete_U] at hx
  rcases hx with hx | hx
  · by_contra hn
    exact hx.2 hn
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    obtain ⟨p, q, -, hti, hLn⟩ := hl' e he.1
    have hp : p ∈ tilde e := by rw [hti]; exact .inl rfl
    have hq : q ∈ tilde e := by rw [hti]; exact .inr rfl
    have hpI : p ∈ discInt Δ := by
      by_contra hn
      exact Set.disjoint_left.mp he.2 hp hn
    have hqI : q ∈ discInt Δ := by
      by_contra hn
      exact Set.disjoint_left.mp he.2 hq hn
    have hd : Disjoint (closure e) (discBd Δ) := by
      rw [hΔF]
      refine Set.disjoint_left.mpr fun z hz hzF => ?_
      rcases hclF e he.1 ⟨z, hz, hzF⟩ with h3 | ⟨w, hw, hwF⟩
      · exact hpI.2 (hΔF ▸ closure_minimal (hedge e he.1 h3) hFcl hp.1)
      · rw [hti] at hw
        rcases hw with rfl | hw
        · exact hpI.2 (hΔF ▸ hwF)
        · rw [mem_singleton_iff.mp hw] at hwF
          exact hqI.2 (hΔF ▸ hwF)
    exact ⟨side_const hT hΔ hLn.isPreconnected_self hd hp.1 hxe hpI.1,
      Set.disjoint_left.mp hd hxe⟩

/-- **The third statement of (6.6).** See the module docstring. The hypothesis `hrep` is what (6.5)
gives for a surface that is not a sphere. -/
theorem region_part (hT : IsClosedSurface S) [ConnectedSpace S] {G G' : Drawing S}
  (hG : G.IsGM19Drawing) (hG' : G'.IsGM19Drawing) (hb₁ : G.IsBlock) (hb₂ : G'.IsBlock) {τ : S
    → Drawing S} {σe : Set S → Set S}
    (hτ : IsEnlargement G G' τ σe) (hcov : branchV G τ = G'.V) (hind : ∀ v ∈ G.V, ∀ e ∈ G'.E, tilde
      e ⊆ (τ v).V → e ∈ (τ v).E)
    (hrep : ¬ IsSphere S → ∀ v ∈ G.V, ∀ G'' : Drawing S, G''.IsGM19Drawing → ∀ (σv' : S
      → Drawing S) (σe' : Set S → Set S), IsEnlargement (delete G {v}) G'' σv' σe' → 1 ≤ G''.rep)
    {r : Set S} (hr : r ∈ G'.regions) {v : S} (hv : v ∈ G.V) : ConnIn ((τ v).interSet (closure r))
      ((τ v).interSet (closure r)).V := by
  classical
  have hNe : Nonempty S := ‹ConnectedSpace S›.toNonempty
  have hl := loopFree_of_gm19 hG
  have hl' := loopFree_of_gm19 hG'
  let D := τ v
  let I := D.interSet (closure r)
  have hsubD : D.IsSubdrawing G' := hτ.vertex_subdrawing v hv
  have hclr : IsClosed (closure r) := isClosed_closure
  have hIV : ∀ {x}, x ∈ I.V → x ∈ D.V ∧ x ∈ closure r := fun {x} hx => by
    rcases hx with hx | hx
    · exact hx.1
    · obtain ⟨e, he, hxe, hxV⟩ := mem_iUnion₂.mp hx
      exact ⟨hxV, closure_minimal he.1.2 hclr hxe⟩
  have hIV' : ∀ {x}, x ∈ D.V → x ∈ closure r → x ∈ I.V := fun hx hx' => .inl ⟨⟨hx, hx'⟩, hx⟩
  have hIE : ∀ {e}, e ∈ D.E → e ⊆ closure r → e ∈ I.E := fun {e} he he' => by
    change e ∈ (D.span _ _).E
    rw [Drawing.span_E]
    exact ⟨⟨he, he'⟩, he⟩
  rintro Y hY ⟨a, ha⟩ hc
  refine Subset.antisymm hY fun b hb => ?_
  by_cases hab : a = b
  · exact hab ▸ ha
  obtain ⟨haD, har⟩ := hIV (hY ha)
  obtain ⟨hbD, hbr⟩ := hIV hb
  have haV := hsubD.1 haD
  have hbV := hsubD.1 hbD
  obtain ⟨Vq, Eq, hVq, hEq, haq, hbq, htq, hQ⟩ := exists_line_of_connected D (fun e he => hl' e
    (hsubD.2 he)) (Subset.refl _) (hτ.vertex_connected v hv) haD hbD hab
  obtain ⟨L, hLine, hLr⟩ := exists_line_in_region hT G' hr haV hbV hab
    (exists_edge_at_vertex hb₂.connected haV hbV hab) (exists_edge_at_vertex hb₂.connected hbV haV
      (Ne.symm hab)) har hbr
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨hro, -, -, hrU, -, -⟩ := region_props G' hr
  have hrU' : ∀ {y}, y ∈ r → y ∉ G'.U := fun hy hyU => Set.disjoint_left.mp hrU hy hyU
  have hEqG : Eq ⊆ G'.E := hEq.trans hsubD.2
  have hVqV : Vq ⊆ G'.V := hVq.trans hsubD.1
  have hUqU : Vq ∪ ⋃₀ Eq ⊆ G'.U := union_subset (hVqV.trans G'.V_subset_U) (sUnion_subset fun e he
    => subset_closure.trans (G'.closure_subset_U (hEqG he)))
  have hLab : ∀ {x}, x ∈ L → x ∉ r → x = a ∨ x = b := fun {x} hx hxr => by
    by_contra hn
    exact hxr (hLr ⟨hx, hn⟩)
  have hi : (Vq ∪ ⋃₀ Eq) ∩ L = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxL⟩
      exact hLab hxL fun h => hrU' h (hUqU hx)
    · rintro x (rfl | hx)
      · exact ⟨.inl haq, hLine.left_mem⟩
      · rw [mem_singleton_iff.mp hx]
        exact ⟨.inl hbq, hLine.right_mem⟩
  let F : Set S := (Vq ∪ ⋃₀ Eq) ∪ L
  have hFO : IsOArc F := oArc_of_lines hQ hLine hi
  have hFV : ∀ x ∈ F, x ∈ G'.V → x ∈ Vq := fun x hx hxV => by
    rcases hx with (hx | ⟨f, hf, hxf⟩) | hx
    · exact hx
    · exact absurd hxV ((hEqG hf).2.1 hxf).2
    · by_cases hxr : x ∈ r
      · exact absurd (G'.V_subset_U hxV) (hrU' hxr)
      · rcases hLab hx hxr with rfl | rfl
        · exact haq
        · exact hbq
  have hedge : ∀ e ∈ G'.E, (e ∩ F).Nonempty → e ⊆ F := fun e he ⟨x, hxe, hxF⟩ => by
    have hxV : x ∉ G'.V := (he.2.1 hxe).2
    have hxU : x ∈ G'.U := G'.closure_subset_U he (subset_closure hxe)
    rcases hxF with (hx | ⟨f, hf, hxf⟩) | hx
    · exact absurd (hVqV hx) hxV
    · have := arcComp_eq_of_mem he (hEqG hf) hxe hxf
      subst this
      exact fun y hy => .inl (.inr ⟨e, hf, hy⟩)
    · by_cases hxr : x ∈ r
      · exact absurd hxU (hrU' hxr)
      · rcases hLab hx hxr with rfl | rfl
        · exact absurd haV hxV
        · exact absurd hbV hxV
  have hFcl : IsClosed F := hFO.isCompact.isClosed
  have hclF : ∀ e ∈ G'.E, (closure e ∩ F).Nonempty → (e ∩ F).Nonempty ∨ (tilde e ∩ F).Nonempty
    := fun e he ⟨x, hx, hxF⟩ => by
    by_cases hxe : x ∈ e
    · exact .inl ⟨x, hxe, hxF⟩
    · exact .inr ⟨x, ⟨hx, hxe⟩, hxF⟩
  have hdisjV : ∀ u ∈ G.V, u ≠ v → Disjoint (τ u).V Vq := fun u hu huv =>
    (hτ.vertex_disjoint u hu v hv huv).mono_right hVq
  have hbdV : ∀ u ∈ G.V, u ≠ v → ∀ x ∈ (τ u).V, x ∉ F := fun u hu huv x hx hxF =>
    Set.disjoint_left.mp (hdisjV u hu huv) hx (hFV x hxF ((hτ.vertex_subdrawing u hu).1 hx))
  /- `F` bounds a disc. -/
  obtain ⟨Δ, hΔ, hΔF, hsph'⟩ : ∃ Δ, IsClosedDisc Δ ∧ discBd Δ = F ∧ (IsSphere S
    → ∃ Δ', IsClosedDisc Δ' ∧ discBd Δ' = F ∧ Δ ∩ Δ' ⊆ F) := by
    by_cases hsph : IsSphere S
    · obtain ⟨Δ₁, Δ₂, -, h₁, h₂, hb₁', hb₂', -, hcap, -, -⟩ := sphere_disc S hsph F hFO
      exact ⟨Δ₁, h₁, hb₁', fun _ => ⟨Δ₂, h₂, hb₂', hcap.subset⟩⟩
    · have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hT.2.2 x)
      have hpos := hrep hsph v hv (delete G' Vq) (hG'.sub (delete_subdrawing G' Vq)) τ σe
        (hτ.delete hl hl' hdisjV)
      have hnull : IsNullHomotopicOArc F := by
        by_contra hnn
        have hdis : ∀ x ∈ F, x ∉ (delete G' Vq).U := fun x hxF hxU => by
          rw [delete_U] at hxU
          rcases hxU with hx | hx
          · exact hx.2 (hFV x hxF hx.1)
          · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
            by_cases hxV : x ∈ G'.V
            · exact Set.disjoint_left.mp he.2 (GM19.tilde_eq_inter_V G' he.1 ▸ ⟨hxe,
                hxV⟩) (hFV x hxF hxV)
            · have hxe' : x ∈ e := G'.closure_diff_V he.1 ▸ ⟨hxe, hxV⟩
              have hsub := hedge e he.1 ⟨x, hxe', hxF⟩
              obtain ⟨p, q, -, hti, -⟩ := hl' e he.1
              have hp : p ∈ tilde e := by rw [hti]; exact .inl rfl
              have hpF : p ∈ F := closure_minimal hsub hFcl hp.1
              exact Set.disjoint_left.mp he.2 hp (hFV p hpF (tilde_subset_V G' he.1 hp))
        have h0 := rep_le_of_arc (delete G' Vq) hFO (fun x hx => absurd hx.2 (hdis x hx.1)) hnn
        have h1 : F ∩ (delete G' Vq).V = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx
          => hdis x hx.1 ((delete G' Vq).V_subset_U hx.2)
        rw [h1, ncard_empty] at h0
        exact absurd (hpos.trans h0) (by simp)
      obtain ⟨Δ, -, h1, h2⟩ :=
        (epstein S univ F hT.isSurface ‹_› hFO (subset_univ _) (by simp [hbd])).1 hnull
      exact ⟨Δ, h1, h2, fun h => absurd h hsph⟩
  /- Claim (1). -/
  have hone : ∀ Δ₀, IsClosedDisc Δ₀ → discBd Δ₀ = F → (∀ x ∈ G'.V, x ∈ Δ₀ → x ∈ D.V) → b ∈ Y
    := fun Δ₀ h₀ hF₀ hin => by
    refine mem_of_closed_adj hT G' hl' hr h₀ hab hLine hLr (hF₀ ▸ subset_union_right)
      (hF₀ ▸ union_subset_union_left _ hUqU) (fun e he hn => ?_) haV hbV ha fun e he hsub x hx y hy
        hxY => ?_
    · rw [hF₀] at hn ⊢
      exact hedge e he hn
    · have hcl : closure e ⊆ closure r ∩ Δ₀ := closure_minimal hsub (hclr.inter h₀.isClosed)
      have hend : tilde e ⊆ D.V := fun z hz => hin z (tilde_subset_V G' he hz) (hcl hz.1).2
      have heD : e ∈ D.E := hind v hv e he hend
      have hyI : y ∈ I.V := hIV' (hend hy) (hcl hy.1).1
      by_cases hxy : x = y
      · exact hxy ▸ hxY
      · exact hc x hxY y hyI ⟨hxy, hY hxY, hyI, e, hIE heD fun z hz => (hsub hz).1, hx, hy⟩
  have hsideadj : ∀ {x y}, x ∉ F → y ∉ F → G'.adj.Adj x y → x ∈ Δ → y ∈ Δ
    := fun {x y} hxF hyF hxy hxΔ => by
    exact adjacent_vertices_stay_on_same_disc_side (S := S) hT (G' := G') hl' F hedge hFcl hclF Δ
      hΔ hΔF (x := x) (y := y) hxF hyF hxy hxΔ
  /- The sides of the branch sets. -/
  let W : Set S := {u | (u ∈ G.V ∧ u ≠ v) ∧ ∃ x ∈ (τ u).V, x ∈ Δ}
  have hWall : ∀ u ∈ W, ∀ x ∈ (τ u).V, x ∈ Δ := fun u hu x hx => by
    exact represented_vertex_stays_on_same_disc_side (S := S) (G := G) (G' := G') (τ := τ) (σe :=
      σe) hτ (v := v) F hbdV Δ hsideadj  u hu x hx
  have hcov' : ∀ x ∈ G'.V, ∃ u ∈ G.V, x ∈ (τ u).V := fun x hx => by
    rw [← hcov] at hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    exact ⟨u, hu, hxu⟩
  by_cases hWn : W.Nonempty
  swap
  · refine hone Δ hΔ hΔF fun x hx hxΔ => ?_
    obtain ⟨u, hu, hxu⟩ := hcov' x hx
    by_cases huv : u = v
    · change x ∈ (τ v).V
      rw [← huv]
      exact hxu
    · exact absurd ⟨u, ⟨hu, huv⟩, x, hxu, hxΔ⟩ hWn
  have hWeq : W = G.V \ {v} := (preconnected_iff_connIn G _).mp (hb₁.biconnected v hv) W (fun u hu
    => ⟨hu.1.1, hu.1.2⟩) hWn fun u hu u' hu' huu' => by
    obtain ⟨hne, -, -, e, he, h1, h2⟩ := huu'
    obtain ⟨y, hy, hyt⟩ := (hτ.ends_iff e he u hu.1.1).mpr h1
    obtain ⟨y', hy', hyt'⟩ := (hτ.ends_iff e he u' hu'.1).mpr h2
    have hyy : y ≠ y' := fun h => Set.disjoint_left.mp (hτ.vertex_disjoint u hu.1.1 u' hu'.1 hne)
      hy (h ▸ hy')
    have hyΔ := hWall u hu y hy
    have hadj : G'.adj.Adj y y' := ⟨hyy, (hτ.vertex_subdrawing u hu.1.1).1 hy,
      (hτ.vertex_subdrawing u' hu'.1).1 hy', _, hτ.edge_mem e he, hyt, hyt'⟩
    exact ⟨⟨hu'.1, hu'.2⟩, y', hy', hsideadj (hbdV u hu.1.1 hu.1.2 y hy)
      (hbdV u' hu'.1 hu'.2 y' hy') hadj hyΔ⟩
  have hinall : ∀ u ∈ G.V, u ≠ v → ∀ x ∈ (τ u).V, x ∈ Δ := fun u hu huv x hx => hWall u
    (hWeq ▸ ⟨hu, huv⟩) x hx
  by_cases hsph : IsSphere S
  · obtain ⟨Δ', hΔ', hF', hcap⟩ := hsph' hsph
    refine hone Δ' hΔ' hF' fun x hx hxΔ => ?_
    obtain ⟨u, hu, hxu⟩ := hcov' x hx
    by_cases huv : u = v
    · change x ∈ (τ v).V
      rw [← huv]
      exact hxu
    · exact hVq (hFV x (hcap ⟨hinall u hu huv x hxu, hxΔ⟩) hx)
  /- Inside `Δ`: impossible when the surface is not a sphere. -/
  exfalso
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hT.2.2 x)
  obtain ⟨C₀, hC₀, hC₀n⟩ := exists_not_nullHomotopic hT.isSurface hbd hsph
  obtain ⟨C, hC, hCn, hCd⟩ := exists_curve_off_disc hT hΔ hC₀ hC₀n
  let X : Set S := (discInt Δ)ᶜ
  have hint : ∀ u ∈ G.V, u ≠ v → Disjoint (τ u).V X := fun u hu huv => Set.disjoint_left.mpr fun x
    hx hxX => hxX ⟨hinall u hu huv x hx, by
    rw [hΔF]
    exact hbdV u hu huv x hx⟩
  have hpos := hrep hsph v hv (delete G' X) (hG'.sub (delete_subdrawing G' X)) τ σe
    (hτ.delete hl hl' hint)
  have hUI : (delete G' X).U ⊆ discInt Δ := fun x hx => by
    exact remaining_minor_drawing_lies_inside_disc (S := S) hT (G' := G') hl' F hedge hFcl hclF Δ
      hΔ hΔF  x hx
  have hdC : ∀ x ∈ C, x ∉ (delete G' X).U := fun x hx hxU => Set.disjoint_left.mp hCd hx (hUI hxU)
  have h0 := rep_le_of_arc (delete G' X) hC (fun x hx => absurd hx.2 (hdC x hx.1)) hCn
  have h1 : C ∩ (delete G' X).V = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hdC x hx.1
    ((delete G' X).V_subset_U hx.2)
  rw [h1, ncard_empty] at h0
  exact absurd (hpos.trans h0) (by simp)

end

/-- **(6.6) of Graph Minors XIX, page 341.** The set `σ'(v) ∩ rBar` is the subdrawing `(σ'
v).interSet (closure r)`. -/
def Theorem66Statement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [T2Space S], IsSurface S → ConnectedSpace S → bd S = ∅ →
    ∃ k : ℕ, ∀ G G' : Drawing S, G.IsGM19Drawing → G'.IsGM19Drawing → G.IsBlock → G'.IsBlock →
      (k : ℕ∞) < G.rep →
      ∀ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement G G' σv σe →
        ∃ σv' : S → Drawing S, IsEnlargement G G' σv' σe ∧ (∀ v ∈ G.V, (σv v).IsSubdrawing (σv' v))
          ∧
          (⋃ v ∈ G.V, (σv' v).V) = G'.V ∧ (∀ v ∈ G.V, ∀ e ∈ G'.E, tilde e ⊆ (σv' v).V → e ∈
            (σv' v).E) ∧
          ∀ r ∈ G'.regions, ∀ v ∈ G.V, ((GM19.Drawing.adj ((σv' v).interSet (closure r))).induce
            ((σv' v).interSet (closure r)).V).Preconnected

/-- **(6.6) of Graph Minors XIX** follows from (6.5). -/
theorem theorem_6_6_proof : Theorem66Statement := by
  intro S _ _ hS hconn hb
  have hT : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x => by
    by_contra hx
    have : x ∈ bd S := hx
    rw [hb] at this
    exact this⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ¬ IsSphere S → ∀ G : Drawing S, G.IsGM19Drawing → (k : ℕ∞) ≤ G.rep
    → ∀ G' : Drawing S, G'.IsGM19Drawing →
      ∀ (σv : S → Drawing S) (σe : Set S → Set S), IsEnlargement G G' σv σe → 1 ≤ G'.rep := by
    by_cases hsph : IsSphere S
    · exact ⟨0, fun h => absurd hsph h⟩
    · obtain ⟨k, hk⟩ := GraphMinor.GM19.theorem_6_5_proof S hS hconn hb hsph
      exact ⟨k, fun _ => hk⟩
  refine ⟨k, fun G G' hG hG' hb₁ hb₂ hrep σv σe hσ => ?_⟩
  obtain ⟨τ, h1, h2, h3, h4⟩ := exists_full_enlargement (loopFree_of_gm19 hG)
    (loopFree_of_gm19 hG') ((preconnected_iff_connIn G' G'.V).mp hb₂.connected) hb₁.nonempty_V hσ
  refine ⟨τ, h1, h2, h3, h4, fun r hr v hv => (preconnected_iff_connIn _ _).mpr ?_⟩
  exact region_part hT hG hG' hb₁ hb₂ h1 h3 h4 (fun hsph u hu G'' hG'' σ₁ σ₂ hσ₁ =>
    hk hsph _ (hG.sub (delete_subdrawing G {u})) (lt_rep_delete hT G (loopFree_of_gm19 hG) hu hrep)
      G'' hG'' σ₁ σ₂ hσ₁) hr hv

end GraphMinor.GM19
