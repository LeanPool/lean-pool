/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12d
public import LeanPool.GraphMinor.GM19.Section10d

import LeanPool.GraphMinor.GM07.Bridge

/-!
# Graph Minors XIX, Section 12: (12.1), the wheel around a hub

From the ring of `Section12d` we get a circuit of `Γ*` around the zone. Among all circuits of `Γ*`
in the closed disc of
(7.1), around the zone, with all vertices of `Γ` near, we take one with a maximal disc. As in the
paper, the maximality
gives the second condition in the definition of a wheel.

The paper states (12.1) for `ρ ≥ 2`, and its last step asks for a circuit `F` with `U(F) ∩ V(Γ) ⊆
V(C_{ρ/2})` that bounds
a disc. Such a circuit need not exist, and (12.1) as printed fails for `ρ = 2`: let `H = {r*}`,
where `r` is a region
with `rBar ∩ V(Γ) = {a, b}` that shares a side with a triangle `abc`. Then the only vertices of `Γ`
near `H` are `a, b`,
and a circuit around them must pass `c`. So `TangleDatum.exists_wheel` asks for `ρ ≥ 3` and for the
set `Y` of
`Section12d`, and its bound on `rep(𝒯)` is `5ρ + 14`. The paper uses (12.1) only with `ρ ≥ 8`, in
(12.4).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- **A chord of a circuit bounding a disc.** Let `F` be a circuit of `G` bounding a disc `W ⊆ Δ`,
and let `P` be a path of
`G` in `Δ` between two vertices of `F`, that meets `W` only in its ends. Then a circuit in `P ∪ F`
bounds a bigger disc
in `Δ`. -/
theorem exists_larger_circuit {T : Type} [TopologicalSpace T] [T2Space T]
  (hT : IsClosedSurface T) {G F P : Drawing T}
    {Δ W : Set T} {u v : T} (hΔ : IsClosedDisc Δ) (hW : IsClosedDisc W) (hWΔ : W ⊆ Δ)
      (hF : F.IsCircuitOf G)
    (hbd : discBd W = F.U) (hu : u ∈ F.V) (hv : v ∈ F.V) (huv : u ≠ v) (hP : P.IsPathOf G u v)
      (hPΔ : P.U ⊆ Δ)
    (hPW : P.U ∩ W = {u, v}) :
    ∃ (F' : Drawing T) (W' : Set T), F'.IsCircuitOf G ∧ W' ⊆ Δ ∧ IsClosedDisc W' ∧ W ⊂ W'
      ∧ discBd W' = F'.U ∧
      F'.U ⊆ P.U ∪ F.U ∧ F'.V ⊆ P.V ∪ F.V := by
  obtain ⟨F₁, F₂, hF₁, hF₂, hs₁, hs₂, hp₁, hp₂, hV₁₂, hE₁₂, hsup⟩ := hF.2.exists_two_paths hu hv huv
  have hFW : F.U ⊆ W := hbd ▸ Surface.discBd_subset W
  have hsplit : TwoPaths G F F₁ F₂ P u v := by
    refine ⟨huv, hF.1, ⟨hs₁, hF₁⟩, ⟨hs₂, hF₂⟩, ?_, ?_, hV₁₂.le, hE₁₂, hP, ?_, ?_⟩
    · have := Drawing.sup_V hs₁ hs₂
      rwa [hsup] at this
    · have := Drawing.sup_E hs₁ hs₂
      rwa [hsup] at this
    · rintro x ⟨hxP, hxF⟩
      rw [← hPW]
      exact ⟨P.V_subset_U hxP, hFW (F.V_subset_U hxF)⟩
    · refine disjoint_left.mpr fun e heP heF ↦ ?_
      obtain ⟨x, hx⟩ := (hP.1.2 heP).1
      have hxP : x ∈ P.U ∩ W := by
        refine ⟨?_, hFW ?_⟩
        · rw [P.U_eq]
          exact .inr (mem_iUnion₂.mpr ⟨e, heP, subset_closure hx⟩)
        · rw [F.U_eq]
          exact .inr (mem_iUnion₂.mpr ⟨e, heF, subset_closure hx⟩)
      rw [hPW] at hxP
      have hxV : x ∈ G.V := by
        rcases hxP with rfl | rfl
        · exact hF.1.1 hu
        · exact hF.1.1 hv
      exact ((hP.1.2 heP).2.1 hx).2 hxV
  have hL := isLine_of_isPathBetween hP.2 huv
  have hA := isLine_of_isPathBetween hF₁ huv
  have hB := isLine_of_isPathBetween hF₂ huv
  have hAB : F₁.U ∪ F₂.U = discBd W := by rw [hbd, hsplit.U_eq]
  have hAB' : F₁.U ∩ F₂.U = {u, v} := by
    rw [U_inter_of_disjoint hs₁ hs₂ hE₁₂, hV₁₂]
  obtain ⟨W', hW'Δ, hW', hlt, hb⟩ := exists_larger_disc hT hΔ hW hWΔ hPΔ hA hB hL hAB hAB' hPW
  rcases hb with hb | hb
  · refine ⟨G.sup P F₁, W', ⟨Drawing.sup_isSubdrawing _ _ _, hsplit.swap.left_circuit⟩, hW'Δ,
      hW', hlt, ?_, ?_, ?_⟩
    · rw [hsplit.swap.U_right, hb]
    · rw [hsplit.swap.U_right]
      exact union_subset_union_right _ (hsplit.U_eq ▸ subset_union_left)
    · rw [Drawing.sup_V hP.1 hsplit.sub₁]
      exact union_subset_union_right _ hs₁.1
  · refine ⟨G.sup P F₂, W', ⟨Drawing.sup_isSubdrawing _ _ _, hsplit.left_circuit⟩, hW'Δ, hW',
      hlt, ?_, ?_, ?_⟩
    · rw [hsplit.U_right, hb]
    · rw [hsplit.U_right]
      exact union_subset_union_right _ (hsplit.U_eq ▸ subset_union_right)
    · rw [Drawing.sup_V hP.1 hsplit.sub₂]
      exact union_subset_union_right _ hs₂.1

namespace TangleDatum

variable {D : TangleDatum cap χ} {H : Drawing Shat} {k : ℕ} {Y : Set Shat} {x : Shat}

omit [T2Space S] [T2Space Shat] in
/-- The first step of a walk from a vertex to `V(H)`. -/
theorem IsNear.exists_next (h : D.IsNear H (k + 1) x) :
    x ∈ H.V ∨ ∃ (g : Set Shat) (t : Shat), D.rad.G.toGraph.IsLink g x t ∧ D.IsNear H k t := by
  obtain ⟨h, hh, W, hW⟩ := h
  cases W with
  | nil _ => exact .inl hh
  | @cons _ u _ e hl r =>
    rw [GraphWalk.length_cons] at hW
    exact .inr ⟨e, u, hl, h, hh, r, by omega⟩

omit [T2Space Shat] in
/-- The zone includes `U(H)`. -/
theorem subset_nearZone (hH : H.IsSubdrawing D.rad.G) : H.U ⊆ nearZone D H k := by
  have hV : ∀ x ∈ H.V, x ∈ nearZone D H k := fun x hx ↦ by
    by_cases hxV : x ∈ D.P.Γ.hatV cap
    · exact .inl ⟨hxV, (isNear_self hH hx).mono (by omega)⟩
    · have hw : x ∈ D.rad.Rstar := ⟨hH.1 hx, hxV⟩
      exact .inr (mem_iUnion₂.mpr ⟨x, ⟨hw, (isNear_self hH hx).mono (by omega)⟩,
        (D.rad.regionOf_mem hw).2⟩)
  intro x hx
  by_cases hxV : x ∈ H.V
  · exact hV x hxV
  obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hx hxV
  obtain ⟨_, -, t, ht, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e (hH.2 he)
  have hm : t ∈ closure e ∩ D.rad.G.V := by
    rw [hcap]
    exact .inr rfl
  have hc : t ∈ closure e ∩ H.V := (hH.closure_inter_V he).symm ▸ hm
  exact .inr (mem_iUnion₂.mpr ⟨t, ⟨ht, (isNear_self hH hc.2).mono (by omega)⟩,
    edge_subset_regionOf D ht (hH.2 he) hm.1 hxe⟩)

/-- The ends of an edge of `Γ*` are the points of `eTilde`. -/
theorem closure_inter_V_eq_tilde {T : Type} [TopologicalSpace T] [T2Space T] {G : Drawing T} {e :
  Set T} (he : e ∈ G.E) :
    closure e ∩ G.V = tilde e := by
  ext y
  constructor
  · rintro ⟨hy, hV⟩
    exact ⟨hy, fun h ↦ (he.2.1 h).2 hV⟩
  · rintro ⟨hy, hn⟩
    refine ⟨hy, ?_⟩
    rcases closure_edge_subset he hy with h | h
    · exact absurd h hn
    · exact h

omit [T2Space S] [T2Space Shat] in
/-- The end of an edge of `Γ*` other than a vertex of `Γ` lies in `R*`. -/
theorem other_end_mem_Rstar (D : TangleDatum cap χ) {g : Set Shat} (hg : g ∈ D.rad.G.E) {p q : Shat}
    (hcap : closure g ∩ D.rad.G.V = {p, q}) (hp : p ∈ D.P.Γ.hatV cap) : q ∈ D.rad.Rstar := by
  obtain ⟨a, ha, t, ht, hcap'⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg
  rw [hcap] at hcap'
  have h₁ : t ∈ ({p, q} : Set Shat) := hcap'.symm ▸ mem_insert_of_mem _ rfl
  rcases h₁ with rfl | rfl
  · exact absurd hp ht.2
  · exact ht

omit [T2Space S] [T2Space Shat] in
/-- The atom of a vertex of `R*`. -/
theorem atomOf_Rstar (D : TangleDatum cap χ) {w : Shat} (hw : w ∈ D.rad.Rstar) : D.rad.atomOf w
  = D.rad.regionOf w := by
  classical
  unfold RadialDrawing.atomOf
  rw [ite_eq_right hw.2]

/-- The vertices of a circuit in a disc around the zone. -/
structure IsRingDisc (D : TangleDatum cap χ) (H : Drawing Shat) (k : ℕ) (Y Δ W : Set Shat)
  (F : Drawing Shat) : Prop where
  circuit : F.IsCircuitOf D.rad.G
  disc : IsClosedDisc W
  sub : W ⊆ Δ
  bd : discBd W = F.U
  zone : nearZone D H k ∪ Y ⊆ W \ F.U
  near : ∀ x ∈ F.V, x ∈ D.P.Γ.hatV cap → D.IsNear H (k + 3) x

private theorem two_boundary_neighbors_force_vertex_inside_wheel
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {α : Type w}
    {cap : IsCappedSurface S Shat}
    {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    {H : Drawing Shat}
    {k : ℕ}
    {Y : Set Shat}
    (Δ : Set Shat)
    (W : Set Shat)
    (F : Drawing Shat)
    (hF : D.IsRingDisc H k Y Δ W F)
    (hgrow : ∀ {P : Drawing Shat} {u v : Shat}, u ∈ F.V → v ∈ F.V → u ≠ v → P.IsPathOf (D.rad.G) u
      v → P.U ⊆ Δ → P.U ∩ W = {u, v} → (∀ x ∈ P.V, x ∈ Painting.hatV cap D.P.Γ → x ∈ F.V) → False)
    (hside : ∀ g ∈ Drawing.E (D.rad.G), g ⊆ W ∨ Disjoint g W)
    (hmemF : ∀ {x : Shat}, x ∈ discBd W → x ∈ (D.rad.G).V → x ∈ F.V)
    (hedgeΔ : ∀ {g : Set Shat} {p t : Shat}, g ∈ Drawing.E (D.rad.G) → closure g ∩ (D.rad.G).V =
      {p, t} → p ∈ F.V → p ∈ Painting.hatV cap D.P.Γ → closure g ⊆ Δ)
    (hTV : ∀ {g : Set Shat} {a b : Shat}, g ∈ Drawing.E (D.rad.G) → tilde g = {a, b} → closure g ∩
      (D.rad.G).V = {a, b}) :
    ∀ x ∈ D.rad.G.V, ∀ v₁ ∈ cap.emb '' D.Γ.V ∩ discBd W, ∀ v₂ ∈ cap.emb '' D.Γ.V ∩ discBd
      W, v₁ ≠ v₂ → (∃ e₁ ∈ Drawing.E D.rad.G, tilde e₁ = {x, v₁}) → (∃ e₂ ∈ Drawing.E
      D.rad.G, tilde e₂ = {x, v₂}) → x ∈ W := by
  classical
  let G := D.rad.G
  -- a vertex of `Γ*` with two neighbours in `V(Γ) ∩ bd(W)` lies in `W`
  rintro x hx v₁ ⟨hv₁V, hv₁b⟩ v₂ ⟨hv₂V, hv₂b⟩ hne ⟨e₁, he₁, ht₁⟩ ⟨e₂, he₂, ht₂⟩
  by_contra hxW
  have hc₁ : closure e₁ ∩ G.V = {x, v₁} := hTV he₁ ht₁
  have hc₂ : closure e₂ ∩ G.V = {x, v₂} := hTV he₂ ht₂
  have hxv₁ : x ≠ v₁ := fun h ↦ hxW (h ▸ Surface.discBd_subset W hv₁b)
  have hxv₂ : x ≠ v₂ := fun h ↦ hxW (h ▸ Surface.discBd_subset W hv₂b)
  have hF₁ := hmemF hv₁b (D.rad.isPreRadial.2.1 hv₁V)
  have hF₂ := hmemF hv₂b (D.rad.isPreRadial.2.1 hv₂V)
  have hc₁' : closure e₁ ∩ G.V = {v₁, x} := by rw [hc₁, pair_comm]
  have hc₂' : closure e₂ ∩ G.V = {v₂, x} := by rw [hc₂, pair_comm]
  have hxmem : x ∈ closure e₁ := by
    have : x ∈ closure e₁ ∩ G.V := by
      rw [hc₁]
      exact .inl rfl
    exact this.1
  have hxmem₂ : x ∈ closure e₂ := by
    have : x ∈ closure e₂ ∩ G.V := by
      rw [hc₂]
      exact .inl rfl
    exact this.1
  have hedge : ∀ {e : Set Shat}, e ∈ G.E → x ∈ closure e → Disjoint e W := fun {e} he hm ↦ by
    rcases hside e he with h | h
    · exact absurd (closure_minimal h hF.disc.isClosed hm) hxW
    · exact h
  let Q : GraphWalk G.toGraph v₁ v₂ :=
    .cons (e := e₁) ⟨he₁, D.rad.isPreRadial.2.1 hv₁V, hx, hc₁'⟩
      (.cons (e := e₂) ⟨he₂, hx, D.rad.isPreRadial.2.1 hv₂V, hc₂⟩ (.nil
        (D.rad.isPreRadial.2.1 hv₂V)))
  have hQs : Q.IsSimple := by
    change [v₁, x, v₂].Nodup
    simp [hne, hxv₁.symm, hxv₂]
  have hQU : (walkDrawing G Q).U = closure e₁ ∪ closure e₂ := by
    ext y
    rw [mem_walkDrawing_U]
    change (y ∈ [v₁, x, v₂] ∨ ∃ e ∈ [e₁, e₂], y ∈ closure e) ↔ _
    have hv₁c : v₁ ∈ closure e₁ := by
      have : v₁ ∈ closure e₁ ∩ G.V := by
        rw [hc₁]
        exact .inr rfl
      exact this.1
    have hv₂c : v₂ ∈ closure e₂ := by
      have : v₂ ∈ closure e₂ ∩ G.V := by
        rw [hc₂]
        exact .inr rfl
      exact this.1
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    constructor
    · rintro ((rfl | rfl | rfl) | h)
      · exact .inl hv₁c
      · exact .inl hxmem
      · exact .inr hv₂c
      · exact h
    · exact .inr
  refine hgrow (P := walkDrawing G Q) hF₁ hF₂ hne ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hQs⟩ ?_ ?_ ?_
  · rw [hQU]
    exact union_subset (hedgeΔ he₁ hc₁' hF₁ hv₁V) (hedgeΔ he₂ hc₂' hF₂ hv₂V)
  · rw [hQU]
    have hpart : ∀ {e : Set Shat} {v : Shat}, e ∈ G.E → closure e ∩ G.V = {x, v} → x ∈ closure e →
        ∀ y ∈ closure e, y ∈ W → y = v := fun {e v} he hc hm y hy hyW ↦ by
      rcases closure_edge_subset he hy with h | h
      · exact absurd hyW (disjoint_left.mp (hedge he hm) h)
      · have : y ∈ closure e ∩ G.V := ⟨hy, h⟩
        rw [hc] at this
        rcases this with rfl | rfl
        · exact absurd hyW hxW
        · rfl
    ext y
    constructor
    · rintro ⟨h | h, hyW⟩
      · exact .inl (hpart he₁ hc₁ hxmem y h hyW)
      · exact .inr (hpart he₂ hc₂ hxmem₂ y h hyW)
    · rintro (rfl | rfl)
      · have : y ∈ closure e₁ ∩ G.V := by
          rw [hc₁]
          exact .inr rfl
        exact ⟨.inl this.1, Surface.discBd_subset W hv₁b⟩
      · have : y ∈ closure e₂ ∩ G.V := by
          rw [hc₂]
          exact .inr rfl
        exact ⟨.inr this.1, Surface.discBd_subset W hv₂b⟩
  · intro y hy hyV
    rw [walkDrawing_V] at hy
    change y ∈ [v₁, x, v₂] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact hF₁
    · exact absurd hyV (other_end_mem_Rstar D he₁ hc₁' hv₁V).2
    · exact hF₂

private theorem edge_with_both_ends_on_wheel_boundary_lies_inside
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {α : Type w}
    {cap : IsCappedSurface S Shat}
    {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    (Δ : Set Shat)
    (W : Set Shat)
    (F : Drawing Shat)
    (hgrow : ∀ {P : Drawing Shat} {u v : Shat}, u ∈ F.V → v ∈ F.V → u ≠ v → P.IsPathOf (D.rad.G) u
      v → P.U ⊆ Δ → P.U ∩ W = {u, v} → (∀ x ∈ P.V, x ∈ Painting.hatV cap D.P.Γ → x ∈ F.V) → False)
    (hside : ∀ g ∈ Drawing.E (D.rad.G), g ⊆ W ∨ Disjoint g W)
    (hmemF : ∀ {x : Shat}, x ∈ discBd W → x ∈ (D.rad.G).V → x ∈ F.V)
    (hedgeΔ : ∀ {g : Set Shat} {p t : Shat}, g ∈ Drawing.E (D.rad.G) → closure g ∩ (D.rad.G).V =
      {p, t} → p ∈ F.V → p ∈ Painting.hatV cap D.P.Γ → closure g ⊆ Δ) :
    ∀ e ∈ Drawing.E D.rad.G, tilde e ⊆ discBd W → e ⊆ W := by
  classical
  let G := D.rad.G
  -- `W` includes each edge of `Γ*` with both ends in `bd(W)`
  intro g hg htg
  rcases hside g hg with h | hdis
  · exact h
  exfalso
  obtain ⟨_, ⟨v, hv, rfl⟩, t, ht, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 g hg
  have hvV : cap.emb v ∈ D.P.Γ.hatV cap := mem_image_of_mem _ hv
  have hmem₁ : cap.emb v ∈ closure g ∩ G.V := by
    rw [hcap]
    exact .inl rfl
  have hmem₂ : t ∈ closure g ∩ G.V := by
    rw [hcap]
    exact .inr rfl
  have hb₁ : cap.emb v ∈ discBd W := htg (closure_inter_V_eq_tilde hg ▸ hmem₁)
  have hb₂ : t ∈ discBd W := htg (closure_inter_V_eq_tilde hg ▸ hmem₂)
  have hne : cap.emb v ≠ t := fun h ↦ ht.2 (h ▸ hvV)
  let Q : GraphWalk G.toGraph (cap.emb v) t :=
    .cons (e := g) ⟨hg, hmem₁.2, hmem₂.2, hcap⟩ (.nil hmem₂.2)
  have hQs : Q.IsSimple := by
    change [cap.emb v, t].Nodup
    simp [hne]
  have hQU : (walkDrawing G Q).U = closure g := by
    ext y
    rw [mem_walkDrawing_U]
    change (y ∈ [cap.emb v, t] ∨ ∃ e ∈ [g], y ∈ closure e) ↔ _
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_left]
    constructor
    · rintro ((rfl | rfl) | h)
      · exact hmem₁.1
      · exact hmem₂.1
      · exact h
    · exact .inr
  have hF₁ := hmemF hb₁ hmem₁.2
  refine hgrow (P := walkDrawing G Q) hF₁ (hmemF hb₂ hmem₂.2) hne ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hQs⟩ ?_ ?_ ?_
  · rw [hQU]
    exact hedgeΔ hg hcap hF₁ hvV
  · rw [hQU]
    ext y
    constructor
    · rintro ⟨hy, hyW⟩
      rcases closure_edge_subset hg hy with h | h
      · exact absurd hyW (disjoint_left.mp hdis h)
      · rw [← hcap]
        exact ⟨hy, h⟩
    · rintro (rfl | rfl)
      · exact ⟨hmem₁.1, Surface.discBd_subset W hb₁⟩
      · exact ⟨hmem₂.1, Surface.discBd_subset W hb₂⟩
  · intro y hy hyV
    rw [walkDrawing_V] at hy
    change y ∈ [cap.emb v, t] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hF₁
    · exact absurd hyV ht.2

private theorem wheel_contains_near_vertices
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [T2Space S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {α : Type w}
    {cap : IsCappedSurface S Shat}
    {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    {H : Drawing Shat}
    {k : ℕ}
    {Y : Set Shat}
    (Δ : Set Shat)
    (W : Set Shat)
    (F : Drawing Shat)
    (hF : D.IsRingDisc H k Y Δ W F)
    (hint : (D.nearZone H k ∪ Y) ⊆ W \ discBd W)
    (hHint : H.U ⊆ W \ discBd W) :
    ∀ v ∈ cap.emb '' D.Γ.V, (∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf D.rad.G v h ∧
      (Drawing.E P).ncard ≤ k + 3) → v ∈ W := by
  classical
  let G := D.rad.G
  let Z := D.nearZone H k ∪ Y
  -- `W` contains the vertices of `Γ` within `ρ` steps of `H`
  rintro v hv ⟨P, h, hh, hP, hle⟩
  have hN : D.IsNear H (k + 3) v := isNear_iff_exists_path.mpr ⟨P, h, hh, hP, hle⟩
  rcases IsNear.exists_next (k := k + 2) hN with hm | ⟨g, t, hl, hNt⟩
  · exact (hHint (H.V_subset_U hm)).1
  · have ht : t ∈ D.rad.Rstar := other_end_mem_Rstar D hl.1 hl.2.2.2 hv
    have hvg : v ∈ closure g := by
      have : v ∈ closure g ∩ G.V := by
        rw [hl.2.2.2]
        exact .inl rfl
      exact this.1
    have htg : t ∈ closure g := by
      have : t ∈ closure g ∩ G.V := by
        rw [hl.2.2.2]
        exact .inr rfl
      exact this.1
    have hsub : D.rad.regionOf t ⊆ W := fun y hy ↦
      (hint (.inl (.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, hNt⟩, hy⟩)))).1
    exact closure_minimal ((edge_subset_regionOf D ht hl.1 htg).trans hsub) hF.disc.isClosed hvg

private theorem wheel_boundary_path_bounds
    {S : Type}
    {Shat : Type}
    [TopologicalSpace S]
    [TopologicalSpace Shat]
    [T2Space Shat]
    {α : Type w}
    {cap : IsCappedSurface S Shat}
    {χ : ColourScheme S α}
    {D : TangleDatum cap χ}
    {H : Drawing Shat}
    {k : ℕ}
    {Y : Set Shat}
    (Δ : Set Shat)
    (W : Set Shat)
    (F : Drawing Shat)
    (hF : D.IsRingDisc H k Y Δ W F)
    (hmemF : ∀ {x : Shat}, x ∈ discBd W → x ∈ (D.rad.G).V → x ∈ F.V)
    (hint : (D.nearZone H k ∪ Y) ⊆ W \ discBd W) :
    ∀ v ∈ cap.emb '' D.Γ.V ∩ discBd W, (∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf D.rad.G
      v h ∧ (Drawing.E P).ncard ≤ k + 3) ∧ ¬∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf
      D.rad.G v h ∧ (Drawing.E P).ncard + 2 ≤ k + 3 := by
  classical
  let G := D.rad.G
  let Z := D.nearZone H k ∪ Y
  -- the vertices of `Γ` on `bd(W)` are about `ρ` steps from `H`
  rintro v ⟨hvV, hvb⟩
  have hvF := hmemF hvb (D.rad.isPreRadial.2.1 hvV)
  refine ⟨isNear_iff_exists_path.mp (hF.near v hvF hvV), ?_⟩
  rintro ⟨P, h, hh, hP, hle⟩
  have hN : D.IsNear H (k + 1) v := isNear_iff_exists_path.mpr ⟨P, h, hh, hP, by omega⟩
  exact (hint (.inl (.inl ⟨hvV, hN⟩))).2 hvb

/-- The strengthened form of XIX (12.1) (page 362). Let `ρ = k + 3` and
`rep(𝒯) ≥ 5ρ + 14`, and let `H` be a nonempty subdrawing of `Γ*`
satisfying the third
condition in the definition of a wheel, with any two vertices at distance at most `2ρ + 2`. Let `Y`
be as in `IsZoneSet`,
at distance at most `3ρ + 4`. Then there is a wheel `W` with `W`-hub `H` of radius `ρ`, and with the
zone and `Y` in
its interior. -/
theorem exists_wheel (hrep : 5 * (k + 3) + 14 ≤ D.rep)
    (hH : H.IsSubdrawing D.rad.G) {z : Shat} (hz : z ∈ H.V)
    (hY : IsZoneSet D H k Y) (hconn : IsPreconnected (nearZone D H k ∪ Y))
    (hdiam : ∀ h ∈ H.V, D.dist (D.rad.atomOf z) (D.rad.atomOf h) ≤ 2 * (k + 3) + 2)
    (hYd : ∀ a ∈ D.P.Γ.atoms cap, (a ∩ Y).Nonempty → D.dist (D.rad.atomOf z) a ≤ 3 * (k + 3) + 4)
    (hhub : (H.V.ncard = 1 ∧ H.E = ∅ ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H'.E.ncard ≤ 4 * (k + 3) + 4 →
        ¬ (H.V ⊆ D.ins H' \ H'.U)) ∨
      (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * (k + 3) + 4 ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * (k + 3) + 4 →
        ¬ (H.U ⊆ D.ins H'))) :
    ∃ W, D.IsWheelHubOfRadius W H (k + 3) ∧ nearZone D H k ∪ Y ⊆ W \ discBd W ∧
      ∀ p ∈ W, ∃ a ∈ D.P.Γ.atoms cap, p ∈ a ∧ D.dist (D.rad.atomOf z) a ≤ 3 * (k + 3) + 11 := by
  classical
  have hT := cap.isClosedSurface
  have hS := χ.isSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  set G := D.rad.G with hGdef
  have hr4 : 4 ≤ D.rep := by omega
  have hzG : z ∈ G.V := hH.1 hz
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  obtain ⟨C₀, Λ, -, -, -, hΛc, hsb, hdiff, -, hfar, -, hclose, hins⟩ :=
    theorem_7_1_proof D (D.atomOf_mem hzG) (κ := 3 * (k + 3) + 6) (by omega) (by omega) hSk
  have hclose' : ∀ x ∈ D.P.Γ.atoms cap, D.dist (D.rad.atomOf z) x ≤ 3 * (k + 3) + 4 → x ⊆ Λ
    := fun x hx hd ↦
    hclose x hx (by omega)
  -- the metric bound for near vertices
  have hd : ∀ {j : ℕ} {x : Shat}, j ≤ k + 4 → D.IsNear H j x → D.dist (D.rad.atomOf z)
    (D.rad.atomOf x) ≤ 2 * (k + 3) + 2 + j := by
    rintro j x hj ⟨h, hh, W, hW⟩
    have h₁ := D.dist_atomOf_le_of_walk W (by omega)
    have h₂ := hdiam h hh
    have h₃ := D.dist_triangle hr4 (a := D.rad.atomOf z) (c := D.rad.atomOf x) (D.atomOf_mem
      (hH.1 hh))
    rw [D.dist_comm (D.rad.atomOf h) (D.rad.atomOf x)] at h₃
    omega
  have hNΛ : ∀ {j : ℕ} {x : Shat}, j ≤ k + 4 → D.IsNear H j x → D.rad.atomOf x ⊆ Λ := fun hj hN ↦
    hclose' _ (D.atomOf_mem (hN.mem_V)) ((hd hj hN).trans (by omega))
  have hYΛ : Y ⊆ Λ := fun y hy ↦ by
    obtain ⟨a, ha, hya⟩ := exists_atom_mem D y
    exact hclose' a ha (hYd a ha ⟨y, hya, hy⟩) hya
  have hzoneΛ : nearZone D H k ⊆ Λ := by
    rintro x (⟨hxV, hN⟩ | hx)
    · have hm := D.mem_atomOf (hN.mem_V)
      exact hNΛ (by omega) hN hm
    · obtain ⟨w, ⟨hw, hN⟩, hxw⟩ := mem_iUnion₂.mp hx
      have := hNΛ (by omega) hN
      rw [atomOf_Rstar D hw] at this
      exact this hxw
  have hgood : ∀ q ∈ G.R, IsGood D H k Y q → closure q ⊆ Λ := fun q hq hg ↦ by
    refine IsGood.closure_subset (b := 3 * (k + 3) + 1) D hr4 hY.closed hYΛ
      (fun x hx hdx ↦ hclose' x hx (by omega)) (fun w hw hN ↦ ?_) hq hg
    have := hd (by omega) hN
    rw [atomOf_Rstar D hw] at this
    omega
  have hsubΛ : Λ = closure Λ \ subBd (closure Λ) := by rw [hsb, hdiff]
  have hzZ : z ∈ nearZone D H k ∪ Y := .inl (subset_nearZone hH (H.V_subset_U hz))
  obtain ⟨C₁, Λ₁, hC₁s, hC₁, -, -, hΛ₁, hΛ₁c, -, hsb₁, hdiff₁, hZ₁, -⟩ :=
    GM14.theorem_5_2_full hT (ring D H k Y) hΛc ⟨z, hzZ⟩ hconn fun r hr hm ↦ by
      rw [← hsubΛ]
      exact hY.ring_region_subset hH hgood hr hm
  set Z := nearZone D H k ∪ Y with hZdef
  set Δ := closure Λ with hΔdef
  have hC₁G : Drawing.IsCircuitOf C₁ G := ⟨hC₁s.trans (Drawing.span_isSubdrawing _ _ _), hC₁⟩
  have hbd₁ : discBd (closure Λ₁) = C₁.U := by
    rw [← IsClosedDisc.frontier_eq_discBd hT hΛ₁c, subBd_eq_frontier', hsb₁]
  have hfirst : IsRingDisc D H k Y Δ (closure Λ₁) C₁ := by
    refine ⟨hC₁G, hΛ₁c, hΛ₁, hbd₁, ?_, ?_⟩
    · rw [hdiff₁]
      exact hZ₁
    · intro x hx hxV
      have hxr : x ∈ (ring D H k Y).U := (ring D H k Y).V_subset_U (hC₁s.1 hx)
      obtain ⟨g, ⟨hg, v, hv, t, ht, hcap, hN, -, -⟩, hxg⟩ := mem_ring_U.mp hxr
      have hm : x ∈ closure g ∩ G.V := ⟨hxg, D.rad.isPreRadial.2.1 hxV⟩
      rw [hcap] at hm
      rcases hm with rfl | rfl
      · exact hN
      · exact absurd hxV ht.2
  have huniq : ∀ {A B : Set Shat}, A ⊆ Δ → B ⊆ Δ → IsClosedDisc A → IsClosedDisc B → discBd A
    = discBd B → A = B := by
    intro A B hA hB hAd hBd he
    have hsub : discBd A ⊆ Δ := (Surface.discBd_subset A).trans hA
    obtain ⟨Δ₀, -, hu⟩ := disc_oArc Δ (discBd A) hΛc hsub hAd.isOArc_discBd
    rw [hu A hA hAd rfl, hu B hB hBd he.symm]
  let 𝓕 : Set (Set Shat) := {W | ∃ F, IsRingDisc D H k Y Δ W F}
  have hfin : 𝓕.Finite := by
    refine Set.Finite.of_finite_image (f := discBd) ?_ ?_
    · refine ((finite_circuits G).image fun C ↦ C.U).subset ?_
      rintro _ ⟨W, ⟨F, hF⟩, rfl⟩
      exact ⟨F, ⟨hF.circuit.2, hF.circuit.1⟩, hF.bd.symm⟩
    · rintro W ⟨F, hF⟩ W' ⟨F', hF'⟩ he
      exact huniq hF.sub hF'.sub hF.disc hF'.disc he
  obtain ⟨W, ⟨F, hF⟩, hWmax⟩ := hfin.exists_maximal ⟨_, C₁, hfirst⟩
  have hFW : F.U ⊆ W := hF.bd ▸ Surface.discBd_subset W
  have hgrow : ∀ {P : Drawing Shat} {u v : Shat}, u ∈ F.V → v ∈ F.V → u ≠ v → P.IsPathOf G u v
    → P.U ⊆ Δ →
      P.U ∩ W = {u, v} → (∀ x ∈ P.V, x ∈ D.P.Γ.hatV cap → x ∈ F.V) → False := by
    intro P u v hu hv huv hP hPΔ hPW hPV
    obtain ⟨F', W', hF', hW'Δ, hW', hlt, hbd', hU', hV'⟩ :=
      exists_larger_circuit hT hΛc hF.disc hF.sub hF.circuit hF.bd hu hv huv hP hPΔ hPW
    have hmem : IsRingDisc D H k Y Δ W' F' := by
      refine ⟨hF', hW', hW'Δ, hbd', fun x hx ↦ ?_, fun x hx hxV ↦ ?_⟩
      · obtain ⟨hxW, hxF⟩ := hF.zone hx
        refine ⟨hlt.1 hxW, fun hxF' ↦ ?_⟩
        rcases hU' hxF' with h | h
        · have hm : x ∈ P.U ∩ W := ⟨h, hxW⟩
          rw [hPW] at hm
          rcases hm with rfl | rfl
          · exact hxF (F.V_subset_U hu)
          · exact hxF (F.V_subset_U hv)
        · exact hxF h
      · rcases hV' hx with h | h
        · exact hF.near x (hPV x h hxV) hxV
        · exact hF.near x h hxV
    exact hlt.2 (hWmax ⟨F', hmem⟩ hlt.1)
  have hside : ∀ g ∈ G.E, g ⊆ W ∨ Disjoint g W := by
    intro g hg
    by_cases hgF : g ∈ F.E
    · refine .inl (subset_closure.trans (Subset.trans ?_ hFW))
      intro x hx
      rw [F.U_eq]
      exact .inr (mem_iUnion₂.mpr ⟨g, hgF, hx⟩)
    have hdis : Disjoint g (discBd W) := by
      rw [hF.bd, disjoint_left]
      intro x hx hxF
      have hxV : x ∉ F.V := fun h ↦ (hg.2.1 hx).2 (hF.circuit.1.1 h)
      obtain ⟨f, hf, hxf⟩ := F.exists_edge_of_mem hxF hxV
      exact hgF (G.edge_eq_of_mem hg (hF.circuit.1.2 hf) hx hxf ▸ hf)
    rcases hF.disc.side hman hg.2.2.1.isConnected.isPreconnected hdis with h | h
    · exact .inl (h.trans sdiff_subset)
    · exact .inr h
  have hmemF : ∀ {x : Shat}, x ∈ discBd W → x ∈ G.V → x ∈ F.V := fun hx hV ↦
    mem_V_of_mem_U hF.circuit.1 (hF.bd ▸ hx) hV
  -- an edge of `Γ*` at a vertex of `Γ` on `F` lies in `Δ`
  have hedgeΔ : ∀ {g : Set Shat} {p t : Shat}, g ∈ G.E → closure g ∩ G.V = {p, t} → p ∈ F.V
    → p ∈ D.P.Γ.hatV cap →
      closure g ⊆ Δ := by
    intro g p t hg hcap hp hpV
    have ht : t ∈ D.rad.Rstar := other_end_mem_Rstar D hg hcap hpV
    have hcap' : closure g ∩ G.V = {t, p} := by rw [hcap, pair_comm]
    have hN : D.IsNear H (k + 4) t := (hF.near p hp hpV).step ⟨hg, ht.1, hF.circuit.1.1 hp, hcap'⟩
    have hsub := hNΛ le_rfl hN
    rw [atomOf_Rstar D ht] at hsub
    have htg : t ∈ closure g := by
      have : t ∈ closure g ∩ G.V := by
        rw [hcap]
        exact .inr rfl
      exact this.1
    exact closure_mono ((edge_subset_regionOf D ht hg htg).trans hsub)
  have hint : Z ⊆ W \ discBd W := by
    rw [hF.bd]
    exact hF.zone
  have hHint : H.U ⊆ W \ discBd W := fun x hx ↦ hint (.inl (subset_nearZone hH hx))
  have hTV : ∀ {g : Set Shat} {a b : Shat}, g ∈ G.E → tilde g = {a, b} → closure g ∩ G.V = {a, b}
    := fun hg h ↦ by
    rw [closure_inter_V_eq_tilde hg, h]
  have hfarW : ∀ p ∈ W, ∃ a ∈ D.P.Γ.atoms cap, p ∈ a ∧ D.dist (D.rad.atomOf z) a ≤ 3 * (k + 3) + 11
    := fun p hp ↦ by
    obtain ⟨a, ha, hpa⟩ := exists_atom_mem D p
    exact ⟨a, ha, hpa, hfar a ha ⟨p, hpa, hF.sub hp⟩⟩
  refine ⟨W, ?_, hint, hfarW⟩
  refine ⟨by omega, by omega, hF.disc, ?_, hH, hHint, ?_, ?_, ?_, hhub, ?_, ?_⟩
  · rw [hF.bd]
    exact hF.circuit.1.U_subset
  · -- `W` includes the inside of each short circuit in it
    intro F' hF' hle hsub
    have hlt : F'.E.ncard < 2 * D.rep := by omega
    have hi := D.ins_spec hF' hlt
    have hiΔ : D.ins F' ⊆ Δ := hins F' hF' (hsub.trans hF.sub) (by omega)
    have hO : IsOArc F'.U := hi.2.2.2.1 ▸ hi.2.2.1.isOArc_discBd
    obtain ⟨Δ₀, ⟨h₁, h₂, h₃, -⟩, -⟩ := disc_oArc W F'.U hF.disc hsub hO
    have := huniq hiΔ (h₁.trans hF.sub) hi.2.2.1 h₂ (hi.2.2.2.1.trans h₃.symm)
    rw [this]
    exact h₁
  · exact two_boundary_neighbors_force_vertex_inside_wheel (S := S) (Shat := Shat) (α := α) (cap
      := cap) (χ := χ) (D := D) (H := H) (k := k) (Y := Y) Δ W F hF hgrow hside hmemF hedgeΔ hTV
  · exact edge_with_both_ends_on_wheel_boundary_lies_inside (S := S) (Shat := Shat) (α := α) (cap
      := cap) (χ := χ) (D := D) Δ W F hgrow hside hmemF hedgeΔ
  · exact wheel_contains_near_vertices (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ) (D
      := D) (H := H) (k := k) (Y := Y) Δ W F hF hint hHint
  · exact wheel_boundary_path_bounds (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ) (D :=
      D) (H := H) (k := k) (Y := Y) Δ W F hF hmemF hint
end TangleDatum

end GraphMinor.GM19
