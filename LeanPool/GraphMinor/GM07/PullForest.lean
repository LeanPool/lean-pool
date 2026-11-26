/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.ForestPeel

/-!
# Moving forests across a cut

This file holds the first steps of (4.5) of Graph Minors VII (pages 223 and 224). A homeomorphism of
the cut surface that fixes its boundary comes down to a homeomorphism `β` of the surface
(`exists_descend`). This is the map `β` of the paper.
The preimage of a graph `H` for which `U(J)` is `H`-normal is again a graph (`exists_pullback`), and
its edges are the lifts of the edges of `H`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

theorem IsCutAlongGraph.toSet {J : Drawing S} {φ : S' → S} (h : IsCutAlongGraph J S' φ) :
  IsCutAlongSet J.U φ :=
  ⟨h.isSurface, h.quotientMap, h.preimage_bd_union_U, h.interior_inj, h.finite_fiber⟩

/-- **The map `β` of (4.5)** (pages 223 and 224). A homeomorphism of the cut surface that fixes the
boundary comes down to the surface, because two points in one fiber are equal or on the boundary,
and the boundary is fixed. -/
theorem exists_descend {J : Drawing S} {φ : S' → S} (h : IsCutAlongGraph J S' φ) (α : S' ≃ₜ S')
  (hα : ∀ x ∈ bd S', α x = x) :
    ∃ β : S ≃ₜ S, (∀ x ∈ bd S, β x = x) ∧ ∀ y, β (φ y) = φ (α y) := by
  classical
  have hq := h.quotientMap
  have hfix : ∀ (γ : S' ≃ₜ S'), (∀ x ∈ bd S', γ x = x) → ∀ a b, φ a = φ b → φ (γ a) = φ (γ b)
    := fun γ hγ a b he => by
    by_cases ha : a ∈ bd S'
    · have hb : b ∈ bd S' := by
        rw [← h.preimage_bd_union_U] at ha ⊢
        rw [mem_preimage] at ha ⊢
        rwa [← he]
      rw [hγ a ha, hγ b hb, he]
    · rw [h.interior_inj a ha b he]
  have hαs : ∀ x ∈ bd S', α.symm x = x := fun x hx => by
    rw [Homeomorph.symm_apply_eq]
    exact (hα x hx).symm
  let f : S → S := fun x => φ (α (Function.surjInv hq.surjective x))
  let g : S → S := fun x => φ (α.symm (Function.surjInv hq.surjective x))
  have hf : ∀ y, f (φ y) = φ (α y) := fun y => hfix α hα _ _ (Function.surjInv_eq hq.surjective
    (φ y))
  have hg : ∀ y, g (φ y) = φ (α.symm y) := fun y => hfix α.symm hαs _ _
    (Function.surjInv_eq hq.surjective (φ y))
  have hfc : Continuous f := hq.continuous_iff.mpr (by
    have : f ∘ φ = φ ∘ α := funext hf
    rw [this]
    exact hq.continuous.comp α.continuous)
  have hgc : Continuous g := hq.continuous_iff.mpr (by
    have : g ∘ φ = φ ∘ α.symm := funext hg
    rw [this]
    exact hq.continuous.comp α.symm.continuous)
  let β : S ≃ₜ S :=
    { toFun := f
      invFun := g
      left_inv := fun x => by
        obtain ⟨y, rfl⟩ := hq.surjective x
        rw [hf, hg, Homeomorph.symm_apply_apply]
      right_inv := fun x => by
        obtain ⟨y, rfl⟩ := hq.surjective x
        rw [hg, hf, Homeomorph.apply_symm_apply]
      continuous_toFun := hfc
      continuous_invFun := hgc }
  refine ⟨β, fun x hx => ?_, hf⟩
  obtain ⟨y, rfl⟩ := hq.surjective x
  have hy : y ∈ bd S' := by
    rw [← h.preimage_bd_union_U]
    exact .inl hx
  change f (φ y) = φ y
  rw [hf, hα y hy]

/-- Every point of `U(G)` off `V(G)` lies on an edge. -/
theorem exists_edge_of_mem {G : Drawing S} {z : S} (hz : z ∈ G.U) (hzV : z ∉ G.V) : ∃ e ∈ G.E, z ∈
  e := by
  have hzc : z ∈ G.U \ G.V := ⟨hz, hzV⟩
  refine ⟨pathComponentIn (G.U \ G.V) z, ⟨⟨z, mem_pathComponentIn_self hzc⟩,
    pathComponentIn_subset, isPathConnected_pathComponentIn hzc, fun D hD hc hsub
      => ?_⟩, mem_pathComponentIn_self hzc⟩
  exact Subset.antisymm (hc.subset_pathComponentIn (hsub (mem_pathComponentIn_self hzc)) hD) hsub

/-- An edge of a forest has a line as its closure, since a loop is a circuit. -/
theorem IsSurfaceForest.edge_line {H : Drawing S} (hH : IsSurfaceForest H) {e : Set S}
  (he : e ∈ H.E) : ∃ u v, u ≠ v ∧ closure e ∩ H.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  rcases H.edge_cond e he with h1 | ⟨u, hcap, -⟩
  · exact h1
  · exfalso
    have huV : u ∈ H.V := (show u ∈ closure e ∩ H.V by rw [hcap]; rfl).2
    have hl : H.toGraph.IsLink e u u := ⟨he, huV, huV, by rw [hcap, pair_eq_singleton]⟩
    have h0 := hH.2 u (.cons hl (.nil huV)) (by simp [GraphWalk.IsSimpleClosed, GraphWalk.support,
      GraphWalk.edges])
    simp [GraphWalk.length, GraphWalk.edges] at h0

/-- The lift of a closed edge whose ends may both lie on the set `B` that is cut. -/
theorem exists_lift_closed_edge [CompactSpace S'] [T2Space S'] [T2Space S] {B : Set S} {φ : S' → S}
  (hφ : GM19.IsCutMap φ B) (hB : IsClosed B) {A : Set S} {u v : S}
    (hA : IsLineWithEnds A u v) (hAB : A ∩ B ⊆ {u, v}) :
    ∃ (L : Set S') (u' v' : S'), IsLineWithEnds L u' v' ∧ φ u' = u ∧ φ v' = v ∧ φ '' L = A
      ∧ InjOn φ L ∧ ∀ z, φ z ∈ A \ {u, v} → z ∈ L := by
  classical
  obtain ⟨α, hα, hr, h0, h1⟩ := hA.exists_arc
  obtain ⟨t, ht0, ht1⟩ := exists_between (show (0 : unitInterval) < 1 from zero_lt_one)
  have hmA : α t ∈ A := hr ▸ mem_range_self t
  have hmu : α t ≠ u := fun h => ht0.ne' (hα.2 (h.trans h0.symm))
  have hmv : α t ≠ v := fun h => ht1.ne (hα.2 (h.trans h1.symm))
  obtain ⟨A₁, A₂, hA₁, hA₂, hun, hin⟩ := hA.split hmA hmu hmv
  have hA₁A : A₁ ⊆ A := hun ▸ subset_union_left
  have hA₂A : A₂ ⊆ A := hun ▸ subset_union_right
  have hmB : α t ∉ B := fun h => by
    rcases hAB ⟨hmA, h⟩ with h' | h'
    · exact hmu h'
    · exact hmv h'
  have huA₂ : u ∉ A₂ := fun h => by
    have : u ∈ A₁ ∩ A₂ := ⟨hA₁.left_mem, h⟩
    rw [hin] at this
    exact hmu this.symm
  have hvA₁ : v ∉ A₁ := fun h => by
    have : v ∈ A₁ ∩ A₂ := ⟨h, hA₂.right_mem⟩
    rw [hin] at this
    exact hmv this.symm
  obtain ⟨L₁, u', m₁, hL₁, hu', hm₁, him₁, hinj₁, -⟩ := exists_lift_line hφ hB hA₁ (fun z hz => by
    rcases hAB ⟨hA₁A hz.1, hz.2⟩ with h | h
    · exact h
    · exact (hvA₁ (mem_singleton_iff.mp h ▸ hz.1)).elim)
  obtain ⟨L₂, v', m₂, hL₂, hv', hm₂, him₂, hinj₂, -⟩ := exists_lift_line hφ hB hA₂.symm (fun z hz
    => by
    rcases hAB ⟨hA₂A hz.1, hz.2⟩ with h | h
    · exact (huA₂ (h ▸ hz.1)).elim
    · exact h)
  have hoff : ∀ {x y : S'}, φ x = α t → φ y = α t → x = y := fun {x y} hx hy =>
    hφ.2.2.1 (show φ x ∈ Bᶜ by rwa [hx])
      (show φ y ∈ Bᶜ by rwa [hy]) (hx.trans hy.symm)
  obtain rfl : m₁ = m₂ := hoff hm₁ hm₂
  have hint : L₁ ∩ L₂ = {m₁} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      have : φ z ∈ A₁ ∩ A₂ := ⟨him₁ ▸ mem_image_of_mem φ h1, him₂ ▸ mem_image_of_mem φ h2⟩
      rw [hin] at this
      exact hoff this hm₁
    · rintro rfl
      exact ⟨hL₁.right_mem, hL₂.right_mem⟩
  have him : φ '' (L₁ ∪ L₂) = A := by rw [image_union, him₁, him₂, hun]
  have hinj : InjOn φ (L₁ ∪ L₂) := by
    have cross : ∀ {x y}, x ∈ L₁ → y ∈ L₂ → φ x = φ y → x = y := fun {x y} hx hy he => by
      have hm : φ x ∈ A₁ ∩ A₂ := ⟨him₁ ▸ mem_image_of_mem φ hx, he ▸ him₂ ▸ mem_image_of_mem φ hy⟩
      rw [hin] at hm
      exact (hoff hm hm₁).trans (hoff (he ▸ hm) hm₁).symm
    rintro x (hx | hx) y (hy | hy) he
    · exact hinj₁ hx hy he
    · exact cross hx hy he
    · exact (cross hy hx he.symm).symm
    · exact hinj₂ hx hy he
  refine ⟨L₁ ∪ L₂, u', v', hL₁.union hL₂.symm hint, hu', hv', him, hinj, fun z hz => ?_⟩
  obtain ⟨w, hw, hwz⟩ : φ z ∈ φ '' (L₁ ∪ L₂) := him ▸ hz.1
  have hzB : φ z ∉ B := fun h => hz.2 (hAB ⟨hz.1, h⟩)
  have : w = z := hφ.2.2.1 (show φ w ∈ Bᶜ by rw [hwz]; exact hzB) hzB hwz
  exact this ▸ hw

/-- **The pullback of a forest** (first sentence of the proof of (4.5), page 223). When `U(J)` is
`H`-normal, `φ⁻¹(H)` is a proper graph. Each of its edges is the full preimage of an edge of `H`,
and `φ` is one to one on its closure. -/
theorem exists_pullback {J H : Drawing S} {φ : S' → S} (hS : IsSurface S)
  (hJ : IsCutAlongGraph J S' φ) (hH : IsSurfaceForest H) (hN : H.IsNormal J.U) :
    ∃ H' : Drawing S', IsPullbackDrawing φ H H' ∧ H'.IsProper ∧ ∀ e' ∈ H'.E, ∃ e ∈ H.E, e'
      = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ (closure e') := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hY := hJ.isSurface
  have : CompactSpace S' := hY.1
  have : T2Space S' := hY.2.1
  have hcut := hJ.toSet
  have hφ := hcut.isCutMap
  have hB : IsClosed (bd S ∪ J.U) := (isClosed_bd S).union J.isClosed_U
  have hH' : IsSurfaceForest H := hH
  have hUB : ∀ z ∈ H.U, z ∈ bd S ∪ J.U → z ∈ H.V := fun z hz hb => by
    rcases hb with h | h
    · exact hH.1 ⟨h, hz⟩
    · exact hN ⟨h, hz⟩
  have hedge : ∀ e ∈ H.E, ∃ (L : Set S') (u v : S) (u' v' : S'), u ≠ v ∧ closure e ∩ H.V = {u, v}
    ∧ IsLineWithEnds L u' v' ∧ φ u' = u ∧ φ v' = v ∧ φ '' L = closure e ∧ InjOn φ L ∧ ∀ z, φ z ∈ e
      → z ∈ L := fun e he => by
    obtain ⟨u, v, hne, hcap, hl⟩ := hH.edge_line he
    obtain ⟨L, u', v', hL, hu, hv, him, hinj, hmem⟩ := exists_lift_closed_edge hφ hB hl
      (fun z hz => by
      have : z ∈ closure e ∩ H.V := ⟨hz.1, hUB z (H.closure_subset_U he hz.1) hz.2⟩
      rwa [hcap] at this)
    refine ⟨L, u, v, u', v', hne, hcap, hL, hu, hv, him, hinj, fun z hz
      => hmem z ⟨subset_closure hz, fun hc => ?_⟩⟩
    have hV : φ z ∈ closure e ∩ H.V := by
      rw [hcap]
      exact hc
    exact (he.2.1 hz).2 hV.2
  choose L u v u' v' hne hcap hL hu hv him hinj hmem using fun e : H.E => hedge e.1 e.2
  have hVf : (φ ⁻¹' H.V).Finite := by
    have : φ ⁻¹' H.V = ⋃ x ∈ H.V, φ ⁻¹' {x} := by
      ext z
      simp
    rw [this]
    exact H.finite_V.biUnion fun x _ => hcut.finite_fiber x
  have hends : ∀ e : H.E, L e ∩ φ ⁻¹' H.V = {u' e, v' e} := fun e => by
    ext z
    constructor
    · rintro ⟨hz, hzV⟩
      have h1 : φ z ∈ closure e.1 ∩ H.V := ⟨him e ▸ mem_image_of_mem φ hz, hzV⟩
      rw [hcap e] at h1
      rcases h1 with h1 | h1
      · exact .inl (hinj e hz (hL e).left_mem (h1.trans (hu e).symm))
      · exact .inr (hinj e hz (hL e).right_mem ((mem_singleton_iff.mp h1).trans (hv e).symm))
    · have hc : ∀ {w}, w ∈ ({u e, v e} : Set S) → w ∈ H.V := fun {w} hw =>
        (show w ∈ closure e.1 ∩ H.V by rwa [hcap e]).2
      rintro (rfl | h)
      · exact ⟨(hL e).left_mem, show φ _ ∈ H.V by rw [hu e]; exact hc (.inl rfl)⟩
      · obtain rfl : z = v' e := h
        exact ⟨(hL e).right_mem, show φ _ ∈ H.V by rw [hv e]; exact hc (.inr rfl)⟩
  have hdiff : ∀ e ∈ H.E, ∀ z ∈ closure e, z ∉ H.V → z ∈ e := fun e he z hz hzV => by
    rw [← H.closure_diff_V he]
    exact ⟨hz, hzV⟩
  have : Finite H.E := H.finite_edges.to_subtype
  obtain ⟨H', hU', hV', hE'⟩ := GM12.exists_drawing_of_finite_lines hVf (E :=
    (univ : Set H.E)) finite_univ L u' v' (fun e _ => hL e) (fun e _ h => hne e
      (by rw [← hu e, h, hv e])) (fun e _ => hends e) (fun e _ f _ hef z hz => by
    by_contra hzV
    have h1 : φ z ∈ closure e.1 := him e ▸ mem_image_of_mem φ hz.1
    have h2 : φ z ∈ closure f.1 := him f ▸ mem_image_of_mem φ hz.2
    exact hef (Subtype.ext (GM11.arcComponent_eq e.2 f.2 (hdiff e.1 e.2 _ h1 hzV)
      (hdiff f.1 f.2 _ h2 hzV))))
  have hUeq : H'.U = φ ⁻¹' H.U := by
    rw [hU']
    ext z
    constructor
    · rintro (h | h)
      · exact H.V_subset_U h
      · obtain ⟨e, -, hz⟩ := mem_iUnion₂.mp h
        exact H.closure_subset_U e.2 (him e ▸ mem_image_of_mem φ hz)
    · intro hz
      by_cases hzV : φ z ∈ H.V
      · exact .inl hzV
      · obtain ⟨e, he, hze⟩ := exists_edge_of_mem hz hzV
        exact .inr (mem_iUnion₂.mpr ⟨⟨e, he⟩, mem_univ _, hmem ⟨e, he⟩ z hze⟩)
  refine ⟨H', ⟨hUeq, hV'⟩, ?_, ?_⟩
  · rintro z ⟨hzb, hzU⟩
    rw [hV']
    rw [hUeq] at hzU
    rw [← hJ.preimage_bd_union_U] at hzb
    exact hUB _ hzU hzb
  · intro e' he'
    rw [hE'] at he'
    obtain ⟨e, -, rfl⟩ := he'
    have hcl : closure (L e \ {u' e, v' e}) = L e :=
      Subset.antisymm (closure_minimal sdiff_subset (hL e).isCompact.isClosed)
        (hL e).subset_closure_diff
    refine ⟨e.1, e.2, ?_, by rw [hcl]; exact him e, by rw [hcl]; exact hinj e⟩
    ext z
    constructor
    · rintro ⟨hz, hzn⟩
      have h1 : φ z ∈ closure e.1 := him e ▸ mem_image_of_mem φ hz
      refine hdiff e.1 e.2 _ h1 fun hzV => hzn ?_
      have : z ∈ L e ∩ φ ⁻¹' H.V := ⟨hz, hzV⟩
      rwa [hends e] at this
    · intro hz
      refine ⟨hmem e z hz, fun hzn => ?_⟩
      have : z ∈ L e ∩ φ ⁻¹' H.V := by
        rw [hends e]
        exact hzn
      exact (e.2.2.1 hz).2 this.2

/-- A prefix of a walk up to a vertex on it. -/
theorem GraphWalk.exists_prefix_sublist {α β : Type*} {G : Graph α β} {u v x : α}
  (W : GraphWalk G u v) (hx : x ∈ W.support) : ∃ W' : GraphWalk G u x, W'.edges.Sublist W.edges
    := by
  classical
  induction W with
  | @nil a hv =>
    obtain rfl : x = a := by simpa [GraphWalk.support] using hx
    exact ⟨.nil hv, List.Sublist.refl _⟩
  | @cons a y b e hl r ih =>
    by_cases hxa : x = a
    · subst hxa
      exact ⟨.nil hl.left_mem, List.nil_sublist _⟩
    · obtain ⟨W', hW'⟩ := ih ((List.mem_cons.mp hx).resolve_left hxa)
      exact ⟨.cons hl W', hW'.cons_cons _⟩

/-- A walk with a repeated vertex holds a closed walk of positive length. -/
theorem GraphWalk.exists_closed_of_not_nodup {α β : Type*} {G : Graph α β} {u v : α}
  (W : GraphWalk G u v) (h : ¬ W.support.Nodup) : ∃ (x : α) (C : GraphWalk G x x), 0 < C.length
    ∧ C.edges.Sublist W.edges := by
  classical
  induction W with
  | nil _ => simp [GraphWalk.support] at h
  | @cons a y b e hl r ih =>
    by_cases ha : a ∈ r.support
    · obtain ⟨P, hP⟩ := GraphWalk.exists_prefix_sublist r ha
      exact ⟨a, .cons hl P, by simp [GraphWalk.length, GraphWalk.edges], hP.cons_cons _⟩
    · have h' : ¬ r.support.Nodup := fun hn => h (List.nodup_cons.mpr ⟨ha, hn⟩)
      obtain ⟨x, C, hC, hs⟩ := ih h'
      exact ⟨x, C, hC, hs.cons _⟩

/-- **A forest has no closed trail.** A closed walk of a forest with distinct edges has length zero.
-/
theorem length_eq_zero_of_trail {α β : Type*} {G : Graph α β} (hG : IsGraphForest G) (n : ℕ) : ∀
  (u : α) (W : GraphWalk G u u), W.length = n → W.edges.Nodup → W.length = 0 := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u W hn hE
    cases W with
    | nil _ => rfl
    | @cons _ y _ e hl r =>
      by_cases hr : r.support.Nodup
      · exact hG u (.cons hl r) ⟨hr, hE⟩
      · obtain ⟨x, C, hC, hs⟩ := GraphWalk.exists_closed_of_not_nodup r hr
        have hlt : C.length < n := by
          have h1 : C.length ≤ r.length := hs.length_le
          have h2 : (GraphWalk.cons hl r).length = r.length + 1 := rfl
          omega
        have hnd : C.edges.Nodup := hs.nodup (List.nodup_cons.mp hE).2
        have h0 := ih C.length hlt x C rfl hnd
        omega

/-- An edge of `φ⁻¹(H)` maps to an edge of `H` with the images of its ends. -/
theorem pull_link {H : Drawing S} {H' : Drawing S'} {φ : S' → S} (hs : Function.Surjective φ)
  (hV : H'.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ H'.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ
      (closure e')) {e' : Set S'} {x y : S'} (hl : H'.toGraph.IsLink e' x y) : H.toGraph.IsLink
        (φ '' e') (φ x) (φ y) := by
  have hVm : ∀ {z : S'}, z ∈ H'.V → φ z ∈ H.V := fun {z} h => by
    rw [hV] at h
    exact h
  obtain ⟨he', hx, hy, hcap⟩ := hl
  obtain ⟨e, he, rfl, him, -⟩ := hE e' he'
  rw [image_preimage_eq _ hs]
  refine ⟨he, hVm hx, hVm hy, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzV⟩
    obtain ⟨w, hw, rfl⟩ : z ∈ φ '' closure (φ ⁻¹' e) := him ▸ hz
    have : w ∈ closure (φ ⁻¹' e) ∩ H'.V := ⟨hw, by rw [hV]; exact hzV⟩
    rw [hcap] at this
    rcases this with rfl | h
    · exact .inl rfl
    · exact .inr (congrArg φ (mem_singleton_iff.mp h))
  · have hxc : x ∈ closure (φ ⁻¹' e) ∩ H'.V := by rw [hcap]; exact .inl rfl
    have hyc : y ∈ closure (φ ⁻¹' e) ∩ H'.V := by rw [hcap]; exact .inr rfl
    rintro (rfl | h)
    · exact ⟨him ▸ mem_image_of_mem φ hxc.1, hVm hxc.2⟩
    · obtain rfl : z = φ y := h
      exact ⟨him ▸ mem_image_of_mem φ hyc.1, hVm hyc.2⟩

/-- A walk of `φ⁻¹(H)` maps to a walk of `H`, and distinct edges stay distinct. -/
theorem pull_walk {H : Drawing S} {H' : Drawing S'} {φ : S' → S} (hs : Function.Surjective φ)
  (hV : H'.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ H'.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ
      (closure e')) {a b : S'} (W : GraphWalk H'.toGraph a b) :
    ∃ W₀ : GraphWalk H.toGraph (φ a) (φ b), W₀.edges = W.edges.map (φ '' ·) ∧ (W.edges.Nodup
      → W₀.edges.Nodup) := by
  have hmap : ∀ {a b : S'} (W : GraphWalk H'.toGraph a b), ∃ W₀ : GraphWalk H.toGraph (φ a)
    (φ b), W₀.edges = W.edges.map (φ '' ·) := by
    intro a b W
    induction W with
    | @nil v h =>
      have h' : v ∈ H'.V := h
      rw [hV] at h'
      exact ⟨.nil h', rfl⟩
    | cons hl r ih =>
      obtain ⟨W₀, hW₀⟩ := ih
      exact ⟨.cons (pull_link hs hV hE hl) W₀, by simp [GraphWalk.edges, hW₀]⟩
  have hedge : ∀ {a b : S'} (W : GraphWalk H'.toGraph a b), ∀ e ∈ W.edges, e ∈ H'.E := by
    intro a b W e he
    induction W with
    | nil _ => simp [GraphWalk.edges] at he
    | cons hl r ih =>
      rcases List.mem_cons.mp he with rfl | h
      · exact hl.1
      · exact ih h
  obtain ⟨W₀, hW₀⟩ := hmap W
  refine ⟨W₀, hW₀, fun hnd => ?_⟩
  rw [hW₀]
  refine List.Nodup.map_on (fun a ha b hb he => ?_) hnd
  obtain ⟨e, -, rfl, -, -⟩ := hE a (hedge W a ha)
  obtain ⟨f, -, rfl, -, -⟩ := hE b (hedge W b hb)
  rw [image_preimage_eq _ hs, image_preimage_eq _ hs] at he
  rw [he]

/-- `φ⁻¹(H)` is a forest (first sentence of the proof of (4.5), page 223): a circuit of it would map
to a closed walk of `H` with distinct edges. -/
theorem isGraphForest_pullback {H : Drawing S} {H' : Drawing S'} {φ : S' → S}
  (hs : Function.Surjective φ) (hH : IsGraphForest H.toGraph) (hV : H'.V = φ ⁻¹' H.V)
    (hE : ∀ e' ∈ H'.E, ∃ e ∈ H.E, e' = φ ⁻¹' e ∧ φ '' closure e' = closure e ∧ InjOn φ
      (closure e')) : IsGraphForest H'.toGraph := by
  intro u W hW
  obtain ⟨W₀, hW₀, hnd⟩ := pull_walk hs hV hE W
  have h0 := length_eq_zero_of_trail hH _ _ W₀ rfl (hnd hW.2)
  have hlen : W₀.length = W.length := by
    change W₀.edges.length = W.edges.length
    rw [hW₀, List.length_map]
  omega

/-- **The first statement of (4.5)** (page 223): `φ⁻¹(H)` is a forest. -/
theorem exists_pull_forest {J H : Drawing S} {φ : S' → S} (hS : IsSurface S)
  (hJ : IsCutAlongGraph J S' φ) (hH : IsSurfaceForest H) (hN : H.IsNormal J.U) :
    ∃ H' : Drawing S', IsPullbackDrawing φ H H' ∧ IsSurfaceForest H' := by
  obtain ⟨H', hp, hprop, hE⟩ := exists_pullback hS hJ hH hN
  exact ⟨H', hp, hprop, isGraphForest_pullback hJ.quotientMap.surjective hH.2 hp.2 hE⟩

end GraphMinor.GM07
