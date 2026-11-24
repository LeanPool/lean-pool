/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FreeData
public import LeanPool.GraphMinor.GM19.CuffAngle
import LeanPool.GraphMinor.GM19.Section6Cuff

/-!
# The shape of a bite

A bite `F` at a pole `r*` runs through `r*` along two spokes `β`, a chord of the cuff disc `E`. One
side of the chord lies in `ins(F)` and the other
misses it, apart from vertices of `F` on the cuff (`exists_bite_shape`). So `I(F)` is the arc of the
cuff on the first side (`IsBiteShape.biteArc_eq`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


/-- A line in an `O`-arc that holds the two ends of a line `L₁` of that `O`-arc is `L₁`, or it holds
all of the `O`-arc off `L₁`. -/
theorem line_of_oArc {T : Type} [TopologicalSpace T] [T2Space T] {c L₁ I : Set T} {a b : T}
  (hc : IsOArc c) (hl : IsLineWithEnds L₁ a b) (hLc : L₁ ⊆ c)
    {u v : T} (hI : IsLineWithEnds I u v) (hIc : I ⊆ c) (huv : ({u, v} : Set T) = {a, b}) : I = L₁
      ∨ c \ L₁ ⊆ I := by
  have ha : a ∈ I := by
    have : a ∈ ({u, v} : Set T) := huv ▸ mem_insert _ _
    rcases this with rfl | h
    · exact (ends_of_line hI).1
    · exact (mem_singleton_iff.1 h) ▸ (ends_of_line hI).2.1
  have hb : b ∈ I := by
    have : b ∈ ({u, v} : Set T) := huv ▸ mem_insert_of_mem _ rfl
    rcases this with rfl | h
    · exact (ends_of_line hI).1
    · exact (mem_singleton_iff.1 h) ▸ (ends_of_line hI).2.1
  obtain ⟨f, h0, hpi, himg⟩ := exists_angle_of_line hc hl hLc
  have hpos := Real.pi_pos
  have hcover : c ⊆ cuffPoint f '' Icc 0 Real.pi ∪ cuffPoint f '' Icc Real.pi (0 + 2 * Real.pi)
    := fun z hz ↦ by
    obtain ⟨t, ht, rfl⟩ := exists_cuffAngle_eq f 0 hz
    by_cases h : t ≤ Real.pi
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨(not_le.1 h).le, ht.2.le⟩, rfl⟩
  rcases arc_of_preconnected f (isPreconnected_of_line hI) hIc (x₁ := 0) (x₂ := Real.pi) hpos.le
    (by linarith) (by rwa [h0]) (by rwa [hpi]) with h | h
  · left
    have hsub : L₁ ⊆ I := by
      rw [← himg]
      rintro _ ⟨t, ht, rfl⟩
      exact h t ht
    obtain ⟨g, g0, g1⟩ := hI
    apply Subset.antisymm _ hsub
    -- The line `L₁` holds both ends of `I`, so its preimage is all of `[0, 1]`.
    have hconn : IsPreconnected (g ⁻¹' (Subtype.val ⁻¹' L₁)) := by
      have hL' : IsPreconnected (Subtype.val ⁻¹' L₁ : Set I) := by
        refine Topology.IsInducing.subtypeVal.isPreconnected_image.1 ?_
        rw [Subtype.image_preimage_coe]
        have : I ∩ L₁ = L₁ := inter_eq_right.2 hsub
        rw [this]
        exact isPreconnected_of_line hl
      have := hL'.image g.symm g.symm.continuous.continuousOn
      rwa [Homeomorph.image_symm] at this
    have hconv := (isPreconnected_iff_ordConnected.1 hconn)
    have hu : u ∈ L₁ := by
      have : u ∈ ({a, b} : Set T) := huv ▸ mem_insert _ _
      rcases this with rfl | h'
      · exact (ends_of_line hl).1
      · exact (mem_singleton_iff.1 h') ▸ (ends_of_line hl).2.1
    have hv : v ∈ L₁ := by
      have : v ∈ ({a, b} : Set T) := huv ▸ mem_insert_of_mem _ rfl
      rcases this with rfl | h'
      · exact (ends_of_line hl).1
      · exact (mem_singleton_iff.1 h') ▸ (ends_of_line hl).2.1
    intro z hz
    have h₀ : (0 : unitInterval) ∈ g ⁻¹' (Subtype.val ⁻¹' L₁) := by
      change (g 0).1 ∈ L₁
      rw [g0]
      exact hu
    have h₁ : (1 : unitInterval) ∈ g ⁻¹' (Subtype.val ⁻¹' L₁) := by
      change (g 1).1 ∈ L₁
      rw [g1]
      exact hv
    have hm := hconv.out h₀ h₁ (show g.symm ⟨z, hz⟩ ∈ Icc 0 1 from ⟨bot_le, le_top⟩)
    simpa using hm
  · right
    rintro z ⟨hzc, hzL⟩
    rcases hcover hzc with h' | ⟨t, ht, rfl⟩
    · exact absurd (himg ▸ h') hzL
    · exact h t ht

namespace TangleDatum

variable {D : TangleDatum cap χ}

/-- The shape of a bite `F` at `r`. Here `β` is the path of `F` through `r`, `L` is the rest of `F`,
and `E` is the closed cuff disc. `Di` and `Do` are the two
sides of `β` in `E`, with cuff arcs `A` and `A'`, and `Di` lies inside `F`. -/
structure IsBiteShape (D : TangleDatum cap χ) (r : Shat) (Θ : Set S) (F : Drawing Shat) (v₁ v₂ : S)
  (Β L A A' Di Do : Set Shat) : Prop where
  circuit : F.IsCircuitOf D.rad.G
  lt : F.E.ncard < 2 * D.rep
  pole : r ∈ D.rad.poles
  cuff : Θ ∈ cuffs S
  reg : D.rad.regionOf r = cap.cuffDisc Θ
  r_mem : r ∈ F.V
  r_Β : r ∈ Β
  v₁_mem : v₁ ∈ D.P.Γ.V
  v₂_mem : v₂ ∈ D.P.Γ.V
  v₁_cuff : v₁ ∈ Θ
  v₂_cuff : v₂ ∈ Θ
  ne : v₁ ≠ v₂
  line : IsLineWithEnds Β (cap.emb v₁) (cap.emb v₂)
  Β_F : Β ⊆ F.U
  Β_E : Β ⊆ closure (cap.cuffDisc Θ)
  meet : Β ∩ cap.emb '' Θ = {cap.emb v₁, cap.emb v₂}
  F_disc : ∀ x ∈ F.U, x ∈ cap.cuffDisc Θ → x ∈ Β
  nbrs : {x | ∃ e ∈ F.E, closure e ∩ F.V = {r, x}} = {cap.emb v₁, cap.emb v₂}
  L_line : IsLineWithEnds L (cap.emb v₁) (cap.emb v₂)
  F_eq : F.U = Β ∪ L
  Β_L : Β ∩ L = {cap.emb v₁, cap.emb v₂}
  L_range : L ⊆ range cap.emb
  di : IsClosedDisc Di
  do_ : IsClosedDisc Do
  union : Di ∪ Do = closure (cap.cuffDisc Θ)
  inter : Di ∩ Do = Β
  bd_i : discBd Di = A ∪ Β
  bd_o : discBd Do = A' ∪ Β
  A_sub : A ⊆ cap.emb '' Θ \ {cap.emb v₁, cap.emb v₂}
  A'_sub : A' ⊆ cap.emb '' Θ \ {cap.emb v₁, cap.emb v₂}
  cover : cap.emb '' Θ \ {cap.emb v₁, cap.emb v₂} ⊆ A ∪ A'
  A'_conn : IsPreconnected A'
  in_ins : discInt Di ⊆ discInt (D.ins F)
  out_ins : Disjoint (discInt Do) (D.ins F)
  in_E : discInt Di ⊆ discInt (closure (cap.cuffDisc Θ)) \ Β

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- **Every bite that meets no other pole has its shape.** -/
theorem exists_bite_shape {r : Shat} {F : Drawing Shat} (hFc : F.IsCircuitOf D.rad.G)
  (hlt : F.E.ncard < 2 * D.rep) (hr : r ∈ D.rad.poles) {Θ : Set S}
    (hΘ : Θ ∈ cuffs S) (hreg : D.rad.regionOf r = cap.cuffDisc Θ) (hrF : r ∈ F.V)
      (hone : ∀ p ∈ D.rad.poles, p ∈ F.V → p = r) :
    ∃ v₁ v₂ Β L A A' Di Do, D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have : ConnectedSpace Shat := cap.connected
  have hi := D.ins_spec hFc hlt
  have hdisc := hi.2.2.1
  have hbd : discBd (D.ins F) = F.U := hi.2.2.2.1
  have hE := cap.cuffDisc_closedDisc Θ hΘ
  have hrd : r ∈ cap.cuffDisc Θ := hreg ▸ (D.rad.regionOf_mem hr.1).2
  have hcover := U_subset_of_one_pole hFc.1 hreg hrd hone
  obtain ⟨e₁, e₂, v₁, v₂, he₁, he₂, hv₁, hv₂, hne, hs₁, hs₂, hedges⟩ := D.rad.circuit_edges hS h3
    hFc hrF hr.1
  obtain ⟨hd₁, hvΘ₁⟩ := D.rad.pole_edge hS (hFc.1.2 he₁) hr hΘ hreg hs₁
  obtain ⟨hd₂, hvΘ₂⟩ := D.rad.pole_edge hS (hFc.1.2 he₂) hr hΘ hreg hs₂
  set G := D.rad.G with hG
  have hrnr := D.pole_notMem_range hS hr
  have hvG : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ∈ G.V := fun hv ↦ D.rad.isPreRadial.2.1
    (mem_image_of_mem _ hv)
  have hvp : ∀ {v}, v ∈ D.P.Γ.V → cap.emb v ≠ r := fun hv h ↦ hr.1.2 (h ▸ mem_image_of_mem _ hv)
  have hsne : cap.emb v₁ ≠ cap.emb v₂ := fun h ↦ hne (cap.isEmbedding.injective h)
  have hclE : ∀ {e x}, e ∈ G.E → closure e ∩ G.V = {x, r} → closure e ⊆ closure (cap.cuffDisc Θ)
    := fun he hs ↦
    closure_mono (hreg ▸ D.rad.edge_subset_region he hr.1 (by rw [hs]))
  set Β : Set Shat := closure e₁ ∪ closure e₂ with hΒ
  have hm₁ : cap.emb v₁ ∈ closure e₁ := (hs₁ ▸ mem_insert _ _ : cap.emb v₁ ∈ closure e₁ ∩ G.V).1
  have hm₂ : cap.emb v₂ ∈ closure e₂ := (hs₂ ▸ mem_insert _ _ : cap.emb v₂ ∈ closure e₂ ∩ G.V).1
  have hr₁ : r ∈ closure e₁ := (hs₁ ▸ mem_insert_of_mem _ rfl : r ∈ closure e₁ ∩ G.V).1
  have hr₂ : r ∈ closure e₂ := (hs₂ ▸ mem_insert_of_mem _ rfl : r ∈ closure e₂ ∩ G.V).1
  have hΒF : Β ⊆ F.U := union_subset (F.closure_subset_U he₁) (F.closure_subset_U he₂)
  have hΒline : IsLineWithEnds Β (cap.emb v₁) (cap.emb v₂) := by
    have hl₁ : G.toGraph.IsLink e₁ (cap.emb v₁) r := ⟨hFc.1.2 he₁, hvG hv₁, hr.1.1, hs₁⟩
    have hl₂ : G.toGraph.IsLink e₂ r (cap.emb v₂) := ⟨hFc.1.2 he₂, hr.1.1, hvG hv₂, by rw [hs₂,
      pair_comm]⟩
    let W : GraphWalk G.toGraph (cap.emb v₁) (cap.emb v₂) := .cons hl₁ (.cons hl₂ (.nil (hvG hv₂)))
    have hWs : W.IsSimple := by
      simp [GraphWalk.IsSimple, W, GraphWalk.support, hvp hv₁, hsne, (hvp hv₂).symm]
    have := walk_isLine G W hWs hsne
    have heq : ({x | x ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, closure e) = Β := by
      apply Subset.antisymm
      · rintro x (hx | hx)
        · simp only [W, GraphWalk.support, mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
            or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact Or.inl hm₁
          · exact Or.inl hr₁
          · exact Or.inr hm₂
        · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.1 hx
          simp only [W, GraphWalk.edges, mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false]
            at hf
          rcases hf with rfl | rfl
          · exact Or.inl hxf
          · exact Or.inr hxf
      · rintro x (h | h)
        · exact Or.inr (mem_biUnion (by simp [W, GraphWalk.edges]) h)
        · exact Or.inr (mem_biUnion (by simp [W, GraphWalk.edges]) h)
    rwa [heq] at this
  have hΒr : ∀ {x}, x ∈ Β → x ∈ range cap.emb → x = cap.emb v₁ ∨ x = cap.emb v₂ := by
    have key : ∀ {e : Set Shat} {v : S} {x}, e ∈ G.E → closure e ∩ G.V = {cap.emb v, r}
      → Disjoint e (range cap.emb) → x ∈ closure e →
        x ∈ range cap.emb → x = cap.emb v := by
      intro e v x he hs hdj hx hxr
      by_cases hxe : x ∈ e
      · exact absurd hxr (disjoint_left.1 hdj hxe)
      · have hxG : x ∈ G.V := by
          by_contra hn
          have : x ∈ closure e \ G.V := ⟨hx, hn⟩
          rw [G.closure_diff_V he] at this
          exact hxe this
        have hm : x ∈ ({cap.emb v, r} : Set Shat) := hs ▸ ⟨hx, hxG⟩
        rcases hm with h | h
        · exact h
        · exact absurd (h ▸ hxr) hrnr
    rintro x (h | h) hxr
    · exact Or.inl (key (hFc.1.2 he₁) hs₁ hd₁ h hxr)
    · exact Or.inr (key (hFc.1.2 he₂) hs₂ hd₂ h hxr)
  obtain ⟨u, w, h2a, hru, hu0, hu1, hun⟩ := exists_arcs_of_line (IsCircuit.isOArc_U hFc.2) hΒline
    hΒF
  set L : Set Shat := range w with hL
  have hLline : IsLineWithEnds L (cap.emb v₁) (cap.emb v₂) := by
    have := h2a.arc_right.isLineWithEnds
    rwa [h2a.zero, h2a.one, hu0, hu1] at this
  have hΒL : Β ∩ L = {cap.emb v₁, cap.emb v₂} := by
    have := h2a.inter
    rwa [hru, hu0, hu1] at this
  have hFL : F.U = Β ∪ L := by rw [← hun, hru]
  have hFcd : ∀ x ∈ F.U, x ∈ cap.cuffDisc Θ → x ∈ Β := by
    intro x hxF hxd
    have hxr : x ∉ range cap.emb := cap.notMem_range hΘ hxd
    by_cases hxV : x ∈ F.V
    · have hxh : x ∉ D.P.Γ.hatV cap := fun ⟨v, _, hv⟩ ↦ hxr ⟨v, hv⟩
      have hw : x ∈ D.rad.Rstar := ⟨hFc.1.1 hxV, hxh⟩
      by_cases hp : x ∈ D.rad.poles
      · rw [hone x hp hxV]
        exact Or.inl hr₁
      · exact absurd (D.rad.region_subset_range hw hp (D.rad.regionOf_mem hw).2) hxr
    · obtain ⟨f, hf, hxf⟩ := F.exists_edge_of_mem hxF hxV
      obtain ⟨v, -, w', hw', hset⟩ := D.rad.edge_ends (hFc.1.2 hf)
      have hwm : w' ∈ closure f ∩ G.V := by rw [hset]; exact Or.inr rfl
      have hwF : w' ∈ F.V := mem_V_of_mem_U hFc.1 (F.closure_subset_U hf hwm.1) hwm.2
      by_cases hp : w' ∈ D.rad.poles
      · have hwr := hone w' hp hwF
        rw [hwr] at hwm
        rcases hedges f hf hwm.1 with rfl | rfl
        · exact Or.inl (subset_closure hxf)
        · exact Or.inr (subset_closure hxf)
      · exact absurd (D.rad.edge_subset_range (hFc.1.2 hf) hw' hp hset hxf) hxr
  have hLr : L ⊆ range cap.emb := fun x hx ↦ by
    have hxF : x ∈ F.U := hFL ▸ Or.inr hx
    rcases hcover hxF with h | h
    · exact h
    · have : x ∈ Β ∩ L := ⟨hFcd x hxF h, hx⟩
      rw [hΒL] at this
      rcases this with h' | h'
      · exact ⟨_, h'.symm⟩
      · exact ⟨_, (mem_singleton_iff.1 h').symm⟩
  have hEb : discBd (closure (cap.cuffDisc Θ)) = cap.emb '' Θ := cap.cuffDisc_bd Θ hΘ
  have hdE : cap.cuffDisc Θ = discInt (closure (cap.cuffDisc Θ)) := cap.cuffDisc_eq_discInt hS hΘ
  have hΒE : Β ⊆ closure (cap.cuffDisc Θ) := union_subset (hclE (hFc.1.2 he₁) hs₁) (hclE
    (hFc.1.2 he₂) hs₂)
  have hmeet : Β ∩ cap.emb '' Θ = {cap.emb v₁, cap.emb v₂} := by
    apply Subset.antisymm
    · rintro x ⟨hx, y, -, rfl⟩
      exact hΒr hx (mem_range_self y)
    · rintro _ (rfl | h)
      · exact ⟨Or.inl hm₁, mem_image_of_mem _ hvΘ₁⟩
      · rw [mem_singleton_iff.1 h]
        exact ⟨Or.inr hm₂, mem_image_of_mem _ hvΘ₂⟩
  have hoff : discInt (closure (cap.cuffDisc Θ)) ∩ discBd (D.ins F) ⊆ Β := by
    rw [← hdE, hbd]
    exact fun x hx ↦ hFcd x hx.2 hx.1
  have hnbrs : {x | ∃ e ∈ F.E, closure e ∩ F.V = {r, x}} = {cap.emb v₁, cap.emb v₂} := by
    have hinter : ∀ {e x}, e ∈ F.E → closure e ∩ G.V = {x, r} → closure e ∩ F.V = {r, x}
      := fun {e x} he hs ↦ by
      rw [hFc.1.closure_inter_V he, hs, pair_comm]
    apply Subset.antisymm
    · rintro x ⟨e, he, hs⟩
      have hre : r ∈ closure e := (hs ▸ mem_insert _ _ : r ∈ closure e ∩ F.V).1
      rcases hedges e he hre with rfl | rfl
      · rw [hinter he hs₁] at hs
        have hne' := hvp hv₁
        have := (Set.pair_eq_pair_iff.1 hs)
        rcases this with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inl h.symm
        · exact absurd h hne'
      · rw [hinter he hs₂] at hs
        have hne' := hvp hv₂
        have := (Set.pair_eq_pair_iff.1 hs)
        rcases this with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inr h.symm
        · exact absurd h hne'
    · rintro x (rfl | h)
      · exact ⟨e₁, he₁, hinter he₁ hs₁⟩
      · rw [mem_singleton_iff.1 h]
        exact ⟨e₂, he₂, hinter he₂ hs₂⟩
  obtain ⟨A, A', Di, Do, hD, hD', hun', hint, hbd', hbd'', hAs, hAs', hcov, hApc, hin, hout, hi₁,
    -, -⟩ :=
    exists_chord_side hT hdisc hE hsne hΒline (hbd ▸ hΒF) hΒE (by rw [hEb]; exact hmeet) hoff
  rw [hEb] at hAs hAs' hcov
  exact ⟨v₁, v₂, Β, L, A, A', Di, Do, hFc, hlt, hr, hΘ, hreg, hrF, Or.inl hr₁, hv₁, hv₂, hvΘ₁,
    hvΘ₂, hne, hΒline, hΒF, hΒE, hmeet, hFcd, hnbrs, hLline,
    hFL, hΒL, hLr, hD, hD', hun', hint, hbd', hbd'', hAs, hAs', hcov, hApc, hin, hout, hi₁⟩

omit hS h3 in
omit [T2Space S] in
/-- The inner arc lies inside `F`. -/
theorem IsBiteShape.A_ins {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di
  Do) : A ⊆ D.ins F := by
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  have hi := D.ins_spec h.circuit h.lt
  have hDΔ : Di ⊆ D.ins F := by
    rw [← closure_discInt h.di]
    exact closure_minimal (h.in_ins.trans (discInt_subset _)) hi.2.2.1.isClosed
  exact fun x hx ↦ hDΔ (Surface.discBd_subset _ (h.bd_i ▸ Or.inl hx))

omit hS h3 in
omit [T2Space S] in
/-- A point of the outer arc inside `F` lies on `F`. -/
theorem IsBiteShape.A'_inter {r Θ F v₁ v₂ Β L A A' Di Do} (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A'
  Di Do) {x : Shat} (hx : x ∈ A') (hxi : x ∈ D.ins F) : x ∈ F.U := by
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := fun x ↦ (hT.2.2 x).isManifoldPoint
  have hi := D.ins_spec h.circuit h.lt
  by_contra hn
  have hxint : x ∈ discInt (D.ins F) := ⟨hxi, fun hb ↦ hn (hi.2.2.2.1 ▸ hb)⟩
  have hxcl : x ∈ closure (discInt Do) := (closure_discInt h.do_).symm ▸ Surface.discBd_subset _
    (h.bd_o ▸ Or.inl hx)
  obtain ⟨w, hwi, hw⟩ := _root_.mem_closure_iff.1 hxcl _ (hi.2.2.1.isOpen_discInt hman) hxint
  exact disjoint_left.1 h.out_ins hw (discInt_subset _ hwi)

omit hS h3 in
/-- A line of infinitely many points. -/
theorem infinite_of_line {T : Type} [TopologicalSpace T] {L : Set T} {a b : T}
  (hl : IsLineWithEnds L a b) : L.Infinite := by
  obtain ⟨f, -, -⟩ := hl
  have : Infinite unitInterval := (Set.Icc_infinite (zero_lt_one' ℝ)).to_subtype
  exact Set.infinite_coe_iff.1 (Infinite.of_injective _ f.injective)

omit hS h3 in
/-- The part of the boundary of a disc off a line in that boundary, with the two ends, is a line. -/
theorem line_of_discBd {T : Type} [TopologicalSpace T] [T2Space T] {Di A Β : Set T} {s t : T}
  (hD : IsClosedDisc Di) (hbd : discBd Di = A ∪ Β) (hl : IsLineWithEnds Β s t)
    (hdis : Disjoint A Β) (_hst : s ≠ t) : IsLineWithEnds (A ∪ {s, t}) s t := by
  have hO : IsOArc (discBd Di) := hD.isOArc_discBd
  obtain ⟨u, v, h2, hru, hu0, hu1, hun⟩ := exists_arcs_of_line hO hl (hbd ▸ subset_union_right)
  have hline : IsLineWithEnds (range v) s t := by
    have := h2.arc_right.isLineWithEnds
    rwa [h2.zero, h2.one, hu0, hu1] at this
  have hint : Β ∩ range v = {s, t} := by
    have := h2.inter
    rwa [hru, hu0, hu1] at this
  have heq : A ∪ {s, t} = range v := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · have : x ∈ range u ∪ range v := by
          rw [hun, hbd]
          exact Or.inl hx
        rcases this with h | h
        · exact absurd (hru ▸ h) (disjoint_left.1 hdis hx)
        · exact h
      · rw [← hint] at hx
        exact hx.2
    · intro x hx
      have hxO : x ∈ A ∪ Β := by
        rw [← hbd, ← hun]
        exact Or.inr hx
      rcases hxO with h | h
      · exact Or.inl h
      · exact Or.inr (hint ▸ ⟨h, hx⟩)
  rwa [heq]

omit hS h3 in
omit [T2Space S] in
/-- **`I(F)` is the arc of the cuff on the inner side of the chord.** -/
theorem IsBiteShape.biteArc_eq (hS : IsSurface S) {r Θ F v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) :
    D.biteArc r F = A ∪ {cap.emb v₁, cap.emb v₂} := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hne : cap.emb v₁ ≠ cap.emb v₂ := fun he ↦ h.ne (cap.isEmbedding.injective he)
  have hΒΘ : ∀ {B}, B ⊆ cap.emb '' Θ \ {cap.emb v₁, cap.emb v₂} → Disjoint B Β
    := fun hB ↦ disjoint_left.2 fun x hx hxΒ ↦
    (hB hx).2 (h.meet ▸ ⟨hxΒ, (hB hx).1⟩)
  have hlA := line_of_discBd h.di h.bd_i h.line (hΒΘ h.A_sub) hne
  have hlA' := line_of_discBd h.do_ h.bd_o h.line (hΒΘ h.A'_sub) hne
  have hE := cap.cuffDisc_closedDisc Θ h.cuff
  have hO : IsOArc (cap.emb '' Θ) := cap.cuffDisc_bd Θ h.cuff ▸ hE.isOArc_discBd
  have hs : cap.emb v₁ ∈ cap.emb '' Θ := mem_image_of_mem _ h.v₁_cuff
  have ht : cap.emb v₂ ∈ cap.emb '' Θ := mem_image_of_mem _ h.v₂_cuff
  have hAc : A ∪ {cap.emb v₁, cap.emb v₂} ⊆ cap.emb '' Θ := union_subset (fun x hx ↦
    (h.A_sub hx).1) (by
    rintro x (rfl | hx)
    · exact hs
    · exact (mem_singleton_iff.1 hx) ▸ ht)
  have hins : ∀ {x}, x ∈ F.U → x ∈ D.ins F := fun hx ↦ D.U_subset_ins h.circuit h.lt hx
  have hAi : A ∪ {cap.emb v₁, cap.emb v₂} ⊆ D.ins F := union_subset h.A_ins (by
    have hb₁ : cap.emb v₁ ∈ Β := (h.meet ▸ mem_insert _ _ : cap.emb v₁ ∈ Β ∩ cap.emb '' Θ).1
    have hb₂ : cap.emb v₂ ∈ Β := (h.meet ▸ mem_insert_of_mem _ rfl : cap.emb v₂ ∈ Β ∩ cap.emb ''
      Θ).1
    rintro x (rfl | hx)
    · exact hins (h.Β_F hb₁)
    · exact (mem_singleton_iff.1 hx) ▸ hins (h.Β_F hb₂))
  have hcl : closure (D.rad.regionOf r) \ D.rad.regionOf r = cap.emb '' Θ := by
    rw [h.reg, cap.closure_cuffDisc hS h.cuff]
    ext x
    constructor
    · rintro ⟨hx | hx, hn⟩
      · exact absurd hx hn
      · exact hx
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Or.inr (mem_image_of_mem _ hy), fun hd ↦ cap.notMem_range h.cuff hd (mem_range_self y)⟩
  have hmem : D.IsBiteArc r F (A ∪ {cap.emb v₁, cap.emb v₂}) := by
    refine ⟨fun x hx ↦ ⟨hAi hx, hcl ▸ hAc hx⟩, cap.emb v₁, cap.emb v₂, h.nbrs, Or.inr ⟨hne, hlA⟩⟩
  have huniq : ∀ I, D.IsBiteArc r F I → I = A ∪ {cap.emb v₁, cap.emb v₂} := by
    rintro I ⟨hsub, u, v, hset, hcase⟩
    rw [h.nbrs] at hset
    have hIc : I ⊆ cap.emb '' Θ := fun x hx ↦ hcl ▸ (hsub hx).2
    rcases hcase with ⟨rfl, -⟩ | ⟨-, hI⟩
    · exfalso
      have h₁ : cap.emb v₁ ∈ ({u, u} : Set Shat) := hset ▸ mem_insert _ _
      have h₂ : cap.emb v₂ ∈ ({u, u} : Set Shat) := hset ▸ mem_insert_of_mem _ rfl
      simp only [pair_eq_singleton, mem_singleton_iff] at h₁ h₂
      exact hne (h₁.trans h₂.symm)
    · rcases line_of_oArc hO hlA hAc hI hIc hset.symm with h' | h'
      · exact h'
      · exfalso
        have hsubA : cap.emb '' Θ \ (A ∪ {cap.emb v₁, cap.emb v₂}) ⊆ F.V := by
          rintro x ⟨hxΘ, hxn⟩
          have hxI := h' ⟨hxΘ, hxn⟩
          have hxst : x ∉ ({cap.emb v₁, cap.emb v₂} : Set Shat) := fun he ↦ hxn (Or.inr he)
          rcases h.cover ⟨hxΘ, hxst⟩ with h₁ | h₁
          · exact absurd (Or.inl h₁) hxn
          · obtain ⟨y, hy, rfl⟩ := hxΘ
            have hyF := h.A'_inter h₁ (hsub hxI).1
            exact (D.rad.bd_point h.circuit.1 (cuff_subset_bd ⟨Θ, h.cuff⟩ hy) hyF).2.1
        refine (infinite_of_line hlA').mono ?_ (F.finite_V.union (toFinite {cap.emb v₁,
          cap.emb v₂}))
        rintro x (hx | hx)
        · by_cases hxA : x ∈ A
          · exfalso
            have h₁ : x ∈ Di := Surface.discBd_subset _ (h.bd_i ▸ Or.inl hxA)
            have h₂ : x ∈ Do := Surface.discBd_subset _ (h.bd_o ▸ Or.inl hx)
            exact disjoint_left.1 (hΒΘ h.A_sub) hxA (h.inter ▸ ⟨h₁, h₂⟩)
          · exact Or.inl (hsubA ⟨(h.A'_sub hx).1, fun hc ↦ hc.elim hxA (h.A'_sub hx).2⟩)
        · exact Or.inr hx
  apply Subset.antisymm
  · rintro x ⟨I, hI, hx⟩
    exact huniq I hI ▸ hx
  · exact fun x hx ↦ ⟨_, hmem, hx⟩

omit hS h3 in
omit [T2Space S] in
/-- An edge of `Γ` on the cuff inside `F` lies on the arc `I(F)`. -/
theorem IsBiteShape.edge_subset (hS : IsSurface S) {r Θ F v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) {e : Set S} (he : e ∈ D.P.Γ.E) (heΘ : e ⊆ Θ)
    (hi : cap.emb '' e ⊆ D.ins F) : cap.emb '' e ⊆ D.biteArc r F := by
  rw [h.biteArc_eq hS]
  rintro _ ⟨x, hx, rfl⟩
  have hoff : cap.emb x ∉ F.U := disjoint_left.1 (disc_edge_disjoint D.rad h.circuit.1 he)
    (mem_image_of_mem _ hx)
  have hst : cap.emb x ∉ ({cap.emb v₁, cap.emb v₂} : Set Shat) := fun hm ↦ hoff (h.Β_F
    (h.meet ▸ hm : cap.emb x ∈ Β ∩ cap.emb '' Θ).1)
  rcases h.cover ⟨mem_image_of_mem _ (heΘ hx), hst⟩ with h₁ | h₁
  · exact Or.inl h₁
  · exact absurd (h.A'_inter h₁ (hi (mem_image_of_mem _ hx))) hoff

omit hS h3 in
omit [T2Space S] in
/-- The arc `I(F)` lies inside `F` and on the cuff. -/
theorem IsBiteShape.biteArc_subset (hS : IsSurface S) {r Θ F v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) :
    D.biteArc r F ⊆ D.ins F ∩ cap.emb '' Θ := by
  have : ConnectedSpace Shat := cap.connected
  rw [h.biteArc_eq hS]
  have hb₁ : cap.emb v₁ ∈ Β := (h.meet ▸ mem_insert _ _ : cap.emb v₁ ∈ Β ∩ cap.emb '' Θ).1
  have hb₂ : cap.emb v₂ ∈ Β := (h.meet ▸ mem_insert_of_mem _ rfl : cap.emb v₂ ∈ Β ∩ cap.emb '' Θ).1
  rintro x (hx | rfl | hx)
  · exact ⟨h.A_ins hx, (h.A_sub hx).1⟩
  · exact ⟨D.U_subset_ins h.circuit h.lt (h.Β_F hb₁), mem_image_of_mem _ h.v₁_cuff⟩
  · rw [mem_singleton_iff.1 hx]
    exact ⟨D.U_subset_ins h.circuit h.lt (h.Β_F hb₂), mem_image_of_mem _ h.v₂_cuff⟩

omit hS h3 in
omit [T2Space S] in
/-- The arc `I(F)` read in `Σ` is connected. -/
theorem IsBiteShape.isPreconnected_biteArc (hS : IsSurface S) {r Θ F v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) :
    IsPreconnected (cap.emb ⁻¹' D.biteArc r F) := by
  have hne : cap.emb v₁ ≠ cap.emb v₂ := fun he ↦ h.ne (cap.isEmbedding.injective he)
  have hdis : Disjoint A Β := disjoint_left.2 fun x hx hxΒ ↦ (h.A_sub hx).2 (h.meet ▸ ⟨hxΒ,
    (h.A_sub hx).1⟩)
  have hl := line_of_discBd h.di h.bd_i h.line hdis hne
  rw [← h.biteArc_eq hS] at hl
  rw [← cap.isEmbedding.isInducing.isPreconnected_image, image_preimage_eq_of_subset fun x hx ↦ by
    obtain ⟨y, -, rfl⟩ := (h.biteArc_subset hS hx).2
    exact mem_range_self y]
  exact isPreconnected_of_line hl

omit hS h3 in
omit [T2Space S] in
/-- The arc `I(F)` is a line. -/
theorem IsBiteShape.isLine_biteArc (hS : IsSurface S) {r Θ F v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) :
    IsLineWithEnds (D.biteArc r F) (cap.emb v₁) (cap.emb v₂) := by
  have hne : cap.emb v₁ ≠ cap.emb v₂ := fun he ↦ h.ne (cap.isEmbedding.injective he)
  have hdis : Disjoint A Β := disjoint_left.2 fun x hx hxΒ ↦ (h.A_sub hx).2 (h.meet ▸ ⟨hxΒ,
    (h.A_sub hx).1⟩)
  rw [h.biteArc_eq hS]
  exact line_of_discBd h.di h.bd_i h.line hdis hne

omit hS h3 in
omit [T2Space S] in
/-- A point of the cuff inside `F` is on the arc `I(F)` or is a vertex of `F`. -/
theorem IsBiteShape.mem_biteArc_or (hS : IsSurface S) {r Θ F v₁ v₂ Β L A A' Di Do}
  (h : D.IsBiteShape r Θ F v₁ v₂ Β L A A' Di Do) {x : Shat} (hxΘ : x ∈ cap.emb '' Θ)
    (hxi : x ∈ D.ins F) :
    x ∈ D.biteArc r F ∨ x ∈ F.V ∧ x ∈ A' := by
  rw [h.biteArc_eq hS]
  by_cases hst : x ∈ ({cap.emb v₁, cap.emb v₂} : Set Shat)
  · exact Or.inl (Or.inr hst)
  rcases h.cover ⟨hxΘ, hst⟩ with h₁ | h₁
  · exact Or.inl (Or.inl h₁)
  · right
    obtain ⟨y, hy, rfl⟩ := hxΘ
    exact ⟨(D.rad.bd_point h.circuit.1 (cuff_subset_bd ⟨Θ, h.cuff⟩ hy) (h.A'_inter h₁ hxi)).2.1, h₁⟩

omit hS h3 in
/-- A line is the closure of what is left after we take away finitely many points. -/
theorem line_subset_closure_diff {T : Type} [TopologicalSpace T] {L Z : Set T} {a b :
  T} (hl : IsLineWithEnds L a b) (hZ : Z.Finite) : L ⊆ closure (L \ Z) := by
  obtain ⟨f, -, -⟩ := hl
  let g : unitInterval → T := fun t ↦ (f t : T)
  have hZ' : (g ⁻¹' Z).Finite := hZ.preimage fun x _ y _ he ↦ f.injective (Subtype.ext he)
  have hd := dense_univ.sdiff_finite hZ'
  have hc : Continuous g := continuous_subtype_val.comp f.continuous
  intro x hx
  obtain ⟨t, ht⟩ := f.surjective ⟨x, hx⟩
  have hx' : x = g t := by simp [g, ht]
  rw [hx']
  refine map_mem_closure hc (hd t) ?_
  rintro s ⟨-, hs⟩
  exact ⟨(f s).2, hs⟩

omit hS h3 in
omit [T2Space S] in
/-- **A bite inside another has its arc inside the arc of the other.** -/
theorem IsBiteShape.biteArc_mono (hS : IsSurface S) {r Θ F₁ F₂ v₁ v₂ Β L A A' Di Do w₁ w₂ Β' L' B
  B' Ei Eo} (h₁ : D.IsBiteShape r Θ F₁ v₁ v₂ Β L A A' Di Do)
    (h₂ : D.IsBiteShape r Θ F₂ w₁ w₂ Β' L' B B' Ei Eo) (hsub : D.ins F₁ ⊆ D.ins F₂) : D.biteArc r
      F₁ ⊆ D.biteArc r F₂ := by
  have hT₂ : IsClosed (D.biteArc r F₂) := isClosed_of_cuffLine (h₂.isLine_biteArc hS)
  refine (line_subset_closure_diff (h₁.isLine_biteArc hS) F₂.finite_V).trans
    (closure_minimal ?_ hT₂)
  rintro x ⟨hx, hxV⟩
  have hm := h₁.biteArc_subset hS hx
  rcases h₂.mem_biteArc_or hS hm.2 (hsub hm.1) with h' | h'
  · exact h'
  · exact absurd h'.1 hxV

end TangleDatum

end GraphMinor.GM19
