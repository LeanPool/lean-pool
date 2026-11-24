/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13t

/-!
# Graph Minors XIX, Section 13: step (11) of (13.6)

Let `F₁` be an outer arc from `r*` to a vertex `b` on `A₁`, that cannot be pushed into `Δ_v` in `Δ₀
\ {h}`, and let `P₁` be the path of `D_v` from `r*` to `b` through `v₁`.
The disc in `Δ₀` bounded by `P₁ ∪ F₁` contains `h`, hence `ins(H)` and `Δ_v`, and then `ins(F)`. So
this disc is `Δ`, and `C = P₁ ∪ F₁`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- A connected set that meets the interior of a disc and misses its boundary lies in the interior.
-/
theorem subset_discInt_of_connected {T : Type} [TopologicalSpace T] [T2Space T] {Δ' Y : Set T}
  (hman : ∀ x : T, IsManifoldPoint x) (hΔ' : IsClosedDisc Δ') (hY : IsPreconnected Y)
    (hb : Disjoint Y (discBd Δ')) (hne : (Y ∩ discInt Δ').Nonempty) : Y ⊆ discInt Δ' := by
  refine IsPreconnected.subset_left_of_subset_union (hΔ'.isOpen_discInt hman)
    hΔ'.isClosed.isOpen_compl ?_ ?_ hne hY
  · exact disjoint_left.mpr fun x h₁ h₂ ↦ h₂ (discInt_subset _ h₁)
  · intro x hx
    by_cases hm : x ∈ Δ'
    · exact .inl ⟨hm, disjoint_left.mp hb hx⟩
    · exact .inr hm

/-- A walk along a drawing has its points in a larger walk, if vertices and edges are. -/
theorem walkU_subset {G : Drawing Shat} {a b c d : Shat} {K : GraphWalk G.toGraph a b} {K' :
  GraphWalk G.toGraph c d} (hV : ∀ x ∈ K.support, x ∈ K'.support)
    (hE : ∀ e ∈ K.edges, e ∈ K'.edges) : (walkDrawing G K).U ⊆ (walkDrawing G K').U := fun x hx ↦ by
  rcases (mem_walkDrawing_U _ _).mp hx with h | ⟨e, he, hxe⟩
  · exact (mem_walkDrawing_U _ _).mpr (.inl (hV x h))
  · exact (mem_walkDrawing_U _ _).mpr (.inr ⟨e, hE e he, hxe⟩)

omit [T2Space Shat] in
/-- A vertex of a walk with distinct ends is on an edge of the walk. -/
theorem GraphWalk.exists_edge_of_support {G : Drawing Shat} {a b x : Shat}
  (K : GraphWalk G.toGraph a b) (hab : a ≠ b) (hx : x ∈ K.support) : ∃ e ∈ K.edges, x ∈ closure e
    := by
  by_cases hax : a = x
  · subst hax
    exact GraphWalk.exists_edge_at_start K hab
  · obtain ⟨L, M, rfl⟩ := K.exists_append_of_mem hx
    obtain ⟨e, he, hc⟩ := GraphWalk.exists_edge_at_end L hax
    exact ⟨e, by rw [GraphWalk.edges_append]; exact List.mem_append_left _ he, hc⟩

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H : Drawing Shat} {ρ : ℕ} {r : Shat} {Δv : Set
  Shat} {Dv F : Drawing Shat}
  {ord' : ℕ} {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {Δ₀ Δ : Set Shat} {C :
    Drawing Shat} {h : Shat}

/-- A connected set that joins the hub to `Δ_v` and stays off the arcs and off the upper part of
`D_v`. In the fan form this is the common tail, and otherwise an inner point of
an edge of `D_v ∩ H`. -/
structure IsAnchor (D : TangleDatum cap χ) (H : Drawing Shat) (ρ : ℕ) (Δv : Set Shat)
  (Dv F : Drawing Shat) (h : Shat) {v₁ v₂ c₁ c₂ : Shat} (f₁ f₂ : Set Shat)
    (A₁ : GraphWalk D.rad.G.toGraph v₁ c₁) (A₂ : GraphWalk D.rad.G.toGraph v₂ c₂)
      (Y : Set Shat) : Prop where
  pre : IsPreconnected Y
  meets : (Y ∩ Δv).Nonempty
  hub : ∃ y ∈ Y, y = h ∨ (y ∈ H.U ∧ IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4
    ∧ h ∈ discInt (D.ins H))
  off_arc : ∀ {a b : Shat} {Q : GraphWalk D.rad.G.toGraph a b}, IsArcOn D.rad.G Dv F Q → Disjoint Y
    (walkDrawing D.rad.G Q).U
  off_f₁ : Disjoint Y (closure f₁)
  off_f₂ : Disjoint Y (closure f₂)
  off_A₁ : ∀ y ∈ Y, y ∈ (walkDrawing D.rad.G A₁).U → y = c₁
  off_A₂ : ∀ y ∈ Y, y ∈ (walkDrawing D.rad.G A₂).U → y = c₂

variable {v₁ v₂ c₁ c₂ h₁ h₂ : Shat} {f₁ f₂ : Set Shat} {A₁ : GraphWalk D.rad.G.toGraph v₁ c₁} {A₂ :
  GraphWalk D.rad.G.toGraph v₂ c₂} {T₁ : GraphWalk D.rad.G.toGraph c₁ h₁}
  {T₂ : GraphWalk D.rad.G.toGraph c₂ h₂} {Y : Set Shat}

omit [T2Space S] in
theorem IsAnchor.swap (ha : D.IsAnchor H ρ Δv Dv F h f₁ f₂ A₁ A₂ Y) : D.IsAnchor H ρ Δv Dv F h f₂
  f₁ A₂ A₁ Y :=
  ⟨ha.pre, ha.meets, ha.hub, ha.off_arc, ha.off_f₂, ha.off_f₁, ha.off_A₂, ha.off_A₁⟩

namespace IsFar

omit [T2Space S] in
/-- If `h` is not in a disc of `Δ₀` bounded by an arc and a path of `Δ_v`, then the arc can be
pushed across the disc into `Δ_v`. -/
theorem mem_disc_of_blocked {a b : Shat} {Q N :
  GraphWalk D.rad.G.toGraph a b} (hab : a ≠ b) (hN : N.IsSimple)
    (hNv : (walkDrawing D.rad.G N).U ⊆ Δv) {Δ' : Set Shat} (hΔ' : IsClosedDisc Δ') (hs' : Δ' ⊆ Δ₀)
      (hb' : discBd Δ' = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U)
    (hnp : ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q).U a b) : h ∈ Δ' := by
  have : ConnectedSpace Shat := cap.connected
  by_contra hh
  apply hnp
  intro ha₀ hb₀ p hp
  have hZ : Δ' ⊆ Δ₀ \ {h} := fun x hx ↦ ⟨hs' hx, fun h' ↦ hh (h' ▸ hx)⟩
  have hin : ∀ {x : Shat}, x ∈ discBd Δ' → x ∈ Δ' := fun hx ↦ Surface.discBd_subset _ hx
  have hNin : (walkDrawing D.rad.G N).U ⊆ Δ' := fun x hx ↦ hin (hb' ▸ .inr hx)
  obtain ⟨n, hn⟩ := (isLine_of_isPathBetween (walkDrawing_isPathBetween D.rad.G hN) hab).exists_path
  obtain ⟨q, hq⟩ := exists_path_in (hNin.trans hZ) hn ha₀ hb₀
  have haN : a ∈ Δ' := hNin ((mem_walkDrawing_U _ _).mpr (.inl N.start_mem_support))
  have hbN : b ∈ Δ' := hNin ((mem_walkDrawing_U _ _).mpr (.inl N.end_mem_support))
  refine ⟨q, fun t ↦ ⟨?_, ?_⟩, homotopic_of_mem hΔ'.isSimplyConnectedSet hZ p q haN hbN
    (fun t ↦ hin (hb' ▸ .inl (hp t))) fun t ↦ ?_⟩
  · rw [hq]; exact hNv (hn t)
  · rw [hq]; exact fun h' ↦ hh (h' ▸ hNin (hn t))
  · rw [hq]; exact hNin (hn t)

private theorem enclave_inside_outer_circuit
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
    {W : Set Shat}
    {H : Drawing Shat}
    {ρ : ℕ}
    {r : Shat}
    {Δv : Set Shat}
    {Dv : Drawing Shat}
    {F : Drawing Shat}
    {ord' : ℕ}
    {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {Δ₀ : Set Shat}
    {Δ : Set Shat}
    {C : Drawing Shat}
    {h : Shat}
    {v₁ : Shat}
    {v₂ : Shat}
    {c₁ : Shat}
    {c₂ : Shat}
    {h₁ : Shat}
    {h₂ : Shat}
    {f₁ : Set Shat}
    {f₂ : Set Shat}
    {A₁ : GraphWalk (Drawing.toGraph D.rad.G) v₁ c₁}
    {A₂ : GraphWalk (Drawing.toGraph D.rad.G) v₂ c₂}
    {T₁ : GraphWalk (Drawing.toGraph D.rad.G) c₁ h₁}
    {T₂ : GraphWalk (Drawing.toGraph D.rad.G) c₂ h₂}
    (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
    (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂)
    {b : Shat}
    {Q : GraphWalk (Drawing.toGraph D.rad.G) r b}
    {X : GraphWalk (Drawing.toGraph D.rad.G) v₁ b}
    (hQ : IsArcOn D.rad.G Dv F Q)
    (ho : ∀ e ∈ Q.edges, Disjoint e Δv)
    (hnp : ¬PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q).U r b)
    (hT : IsClosedSurface Shat)
    (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F)
    (hFc : F.IsCircuitOf D.rad.G)
    (hFs : Drawing.IsSubdrawing F D.rad.G)
    (hE : IsEnclave D.tb D.ord D.𝒯 F)
    (hDv : Dv.IsCircuitOf D.rad.G)
    (hΔv : IsClosedDisc Δv)
    (hbv : discBd Δv = Dv.U)
    (hXA : ∀ y ∈ X.support, y ∈ A₁.support)
    (hrnot : r ∉ (A₁.append T₁).support)
    (hrA₂ : r ∉ (A₂.append T₂).support)
    (hrX : r ∉ X.support)
    (N : GraphWalk (Drawing.toGraph D.rad.G) r b)
    (hNdef : N = GraphWalk.cons s.link₁ X)
    (hNs : N.IsSimple)
    (hNsup : ∀ (y : Shat), y ∈ N.support ↔ y = r ∨ y ∈ X.support)
    (hNe : ∀ (e : Set Shat), e ∈ N.edges ↔ e = f₁ ∨ e ∈ X.edges)
    (hrD : r ∈ Dv.V)
    (hNV : ∀ y ∈ N.support, y ∈ Dv.V)
    (hNE : ∀ e ∈ N.edges, e ∈ Drawing.E Dv)
    (hNU : (walkDrawing D.rad.G N).U ⊆ Dv.U)
    (hNcases : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G N).U → y ∈ closure f₁ ∨ y ∈ (walkDrawing
      D.rad.G X).U)
    (hQU : (walkDrawing D.rad.G Q).U ⊆ F.U)
    (hbA : b ∈ A₁.support)
    (hbF' : b ∈ F.V)
    (hQs : (walkDrawing D.rad.G Q).IsSubdrawing D.rad.G)
    (hNs' : (walkDrawing D.rad.G N).IsSubdrawing D.rad.G)
    (hQp : (walkDrawing D.rad.G Q).IsPathBetween r b)
    (hNp : (walkDrawing D.rad.G N).IsPathBetween r b)
    (C' : Surface.Drawing Shat)
    (hC' : C' = Drawing.sup D.rad.G (walkDrawing D.rad.G Q) (walkDrawing D.rad.G N))
    (hC'sub : C'.IsSubdrawing D.rad.G)
    (hC'V : ∀ (y : Shat), y ∈ C'.V ↔ y ∈ Q.support ∨ y ∈ N.support)
    (hC'E : ∀ (e : Set Shat), e ∈ C'.E ↔ e ∈ Q.edges ∨ e ∈ N.edges)
    (hC'U : C'.U = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U)
    (hNΔ : (walkDrawing D.rad.G N).U ⊆ Δv)
    (Δ' : Set Shat)
    (hd' : IsClosedDisc Δ')
    (hb' : discBd Δ' = C'.U)
    (hbd : discBd Δ' = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U)
    (hinbd : ∀ {y : Shat}, y ∈ discBd Δ' → y ∈ Δ')
    (hΔvΔ' : Δv ⊆ Δ')
    (hDvΔ' : Dv.U ⊆ Δ')
    (hNin : ∀ c ∈ C'.V, c ∈ Dv.V → c ∈ N.support) :
    F.U ⊆ Δ' := by
  refine U_of_edges hFc.2 hd'.isClosed fun g hgF ↦ ?_
  by_contra hn
  have hgG : g ∈ D.rad.G.E := hFs.2 hgF
  have hgD : g ∉ Dv.E := fun h' ↦ hn (subset_closure.trans ((Dv.closure_subset_U h').trans hDvΔ'))
  have hgQ : g ∉ Q.edges := fun h' ↦ hn fun y hy ↦ hinbd (hbd ▸ .inl ((mem_walkDrawing_U _ _).mpr
    (.inr ⟨g, h', subset_closure hy⟩)))
  have hgC : g ∉ C'.E := fun h' ↦ by
    rcases (hC'E g).mp h' with h₀ | h₀
    · exact hgQ h₀
    · exact hgD (hNE g h₀)
  have hoff : Disjoint g Δ' := by
    rcases edge_inside_or_off hT hC'sub hd' hb' hgG hgC with h₀ | h₀
    · exact absurd (h₀.trans (discInt_subset _)) hn
    · exact h₀
  obtain ⟨a₀, b₀, P₀, hP₀, hgP₀⟩ := hf.exists_arc_through hgF hgD
  have hP₀o : ∀ e ∈ P₀.edges, Disjoint e Δv := by
    rcases IsArcOn.side (D := D) hP₀ hDv.1 hΔv hbv with h₀ | h₀
    · obtain ⟨p, hp⟩ := hgG.1
      exact absurd (hΔvΔ' (discInt_subset _ (h₀ g hgP₀ hp))) (disjoint_left.mp hoff hp)
    · exact h₀
  obtain ⟨a', b', P, hP, hPE, -, -, n⟩ := hf.normal_form s hP₀ hP₀o
  have hPo : ∀ e ∈ P.edges, Disjoint e Δv := fun e he ↦ hP₀o e ((hPE e).mp he)
  have hgP : g ∈ P.edges := (hPE g).mpr hgP₀
  have endC : ∀ {c d : Shat} (L : GraphWalk D.rad.G.toGraph c d), IsArcOn D.rad.G Dv F L
    → g ∈ L.edges → c ∈ C'.V := by
    intro c d L hL hgL
    by_contra hcn
    have hdis : ∀ e ∈ L.edges, e ∉ Q.edges := fun e he he' ↦ hgQ (IsArcOn.edges_of_share hFc hL
      hQ he he' g hgL)
    have hLC : ∀ e ∈ L.edges, e ∉ C'.E := fun e he h' ↦ by
      rcases (hC'E e).mp h' with h₀ | h₀
      · exact hdis e he h₀
      · exact hL.off e he (hNE e h₀)
    have hmid : ∀ z ∈ L.support, z ≠ d → z ∉ C'.V := fun z hz hzd hzC ↦ by
      by_cases hzc : z = c
      · exact hcn (hzc ▸ hzC)
      rcases (hC'V z).mp hzC with h₀ | h₀
      · obtain ⟨L₁, L₂, hL₁₂⟩ := L.exists_append_of_mem hz
        obtain ⟨e₁, he₁, hc₁⟩ := GraphWalk.exists_edge_at_end L₁ (Ne.symm hzc)
        obtain ⟨e₂, he₂, hc₂⟩ := GraphWalk.exists_edge_at_start L₂ hzd
        obtain ⟨e₃, he₃, hc₃⟩ := GraphWalk.exists_edge_of_support Q hQ.ne h₀
        have hm₁ : e₁ ∈ L.edges := by
          rw [hL₁₂, GraphWalk.edges_append]
          exact List.mem_append_left _ he₁
        have hm₂ : e₂ ∈ L.edges := by
          rw [hL₁₂, GraphWalk.edges_append]
          exact List.mem_append_right _ he₂
        have hzF : z ∈ F.V := hL.mem_F hFs z hz
        exact no_three_edges hFc D.edge_two_ends hzF (hL.inF _ hm₁) (hL.inF _ hm₂)
          (hQ.inF _ he₃) hc₁ hc₂ hc₃ (fun h' ↦ Splits.append_edge (hL₁₂ ▸ hL.simple) he₁ (h' ▸ he₂))
          (fun h' ↦ hdis _ hm₁ (h' ▸ he₃)) (fun h' ↦ hdis _ hm₂ (h' ▸ he₃))
      · have hzD := hNV z h₀
        rcases hL.inner z hz hzD with h' | h'
        · exact hzc h'
        · exact hzd h'
    have hcint : c ∈ discInt Δ' := by
      refine ⟨hDvΔ' (Dv.V_subset_U hL.left), fun hb₀ ↦ hcn ?_⟩
      exact mem_V_of_mem_U hC'sub (hb' ▸ hb₀) (hDv.1.1 hL.left)
    have := (side_of_walk (D := D) hC'sub hd' hb' L hL.simple hmid hLC).1 hcint g hgL
    obtain ⟨p, hp⟩ := hgG.1
    exact disjoint_left.mp hoff hp (discInt_subset _ (this hp))
  have ha'C := endC P hP hgP
  have hb'C := endC P.reverse (IsArcOn.reverse hP) (by rwa [GraphWalk.edges_reverse,
    List.mem_reverse])
  have ha'N := hNin a' ha'C hP.left
  have hb'N := hNin b' hb'C hP.right
  have hdisPQ : ∀ e ∈ P.edges, e ∉ Q.edges := fun e he he' ↦ hgQ (IsArcOn.edges_of_share hFc hP
    hQ he he' g hgP)
  rcases n with ⟨rfl, -⟩ | ⟨h₀, h₁'⟩
  · have hb'X : b' ∈ X.support := ((hNsup b').mp hb'N).resolve_left hP.ne.symm
    obtain ⟨Sg, -, hSg, -⟩ := s.exists_seg hE hbA (hXA b' hb'X) hbF'
      (hP.mem_F hFs _ P.end_mem_support)
    have hJ : ∀ e, e ∈ (Sg.append P.reverse).edges → e ∈ Sg.edges ∨ e ∈ P.edges := fun e he ↦ by
      rwa [GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse,
        List.mem_reverse] at he
    refine hf.closing hQ.ne hQ.simple hQ.inF (J := Sg.append P.reverse) (fun e he ↦ ?_)
      (fun e he hq ↦ ?_) ?_
    · rcases hJ e he with h' | h'
      · exact (hSg e h').2
      · exact hP.inF e h'
    · rcases hJ e he with h' | h'
      · exact hQ.off e hq (s.edge₁ e (hSg e h').1)
      · exact hdisPQ e h' hq
    · rintro e (he | he)
      · exact .inr (ho e he)
      · rcases hJ e he with h' | h'
        · exact .inl (s.edge₁ e (hSg e h').1)
        · exact .inr (hPo e h')
  · rcases (hNsup b').mp hb'N with rfl | h₂'
    · exact hrA₂ ((GraphWalk.mem_support_append _ _).mpr (.inl h₁'))
    · exact hf.not_both s hP hPo h₀ (hXA b' h₂')

private theorem sector_inside_outer_circuit
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
    {ρ : ℕ}
    {r : Shat}
    {Δv : Set Shat}
    {Dv : Drawing Shat}
    {F : Drawing Shat}
    {h : Shat}
    {v₁ : Shat}
    {v₂ : Shat}
    {c₁ : Shat}
    {c₂ : Shat}
    {f₁ : Set Shat}
    {f₂ : Set Shat}
    {A₁ : GraphWalk (Drawing.toGraph D.rad.G) v₁ c₁}
    {A₂ : GraphWalk (Drawing.toGraph D.rad.G) v₂ c₂}
    {Y : Set Shat}
    (ha : D.IsAnchor H ρ Δv Dv F h f₁ f₂ A₁ A₂ Y)
    {b : Shat}
    {Q : GraphWalk (Drawing.toGraph D.rad.G) r b}
    (hQ : IsArcOn D.rad.G Dv F Q)
    (ho : ∀ e ∈ Q.edges, Disjoint e Δv)
    (hman : ∀ (x : Shat), IsManifoldPoint x)
    (hΔv : IsClosedDisc Δv)
    (hbv : discBd Δv = Dv.U)
    (N : GraphWalk (Drawing.toGraph D.rad.G) r b)
    (hNU : (walkDrawing D.rad.G N).U ⊆ Dv.U)
    (Δ' : Set Shat)
    (hd' : IsClosedDisc Δ')
    (hbd : discBd Δ' = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U)
    (hYint : Y ⊆ discInt Δ') :
    Δv ⊆ Δ' := by
  obtain ⟨z, hzY, hzΔ⟩ := ha.meets
  have hzi := hYint hzY
  have hzc : z ∈ closure (discInt Δv) := by rw [closure_discInt hΔv]; exact hzΔ
  obtain ⟨w, hw₁, hw₂⟩ := mem_closure_iff.mp hzc _ (hd'.isOpen_discInt hman) hzi
  have hsub := subset_discInt_of_connected hman hd' hΔv.isPreconnected_discInt
    (disjoint_left.mpr fun x hi' hb₀ ↦ by
    rw [hbd] at hb₀
    rcases hb₀ with hq | hn
    · have hxe : ∃ e ∈ Q.edges, x ∈ closure e := by
        rcases (mem_walkDrawing_U _ _).mp hq with h' | ⟨e, he, hye⟩
        · exact GraphWalk.exists_edge_of_support Q hQ.ne h'
        · exact ⟨e, he, hye⟩
      obtain ⟨e, he, hxe⟩ := hxe
      obtain ⟨z', hz₁, hz₂⟩ := mem_closure_iff.mp hxe _ (hΔv.isOpen_discInt hman) hi'
      exact disjoint_left.mp (ho e he) hz₂ (discInt_subset _ hz₁)
    · exact hi'.2 (hbv ▸ hNU hn)) ⟨w, hw₂, hw₁⟩
  rw [← closure_discInt hΔv, ← closure_discInt hd']
  exact closure_mono hsub

private theorem hub_inside_outer_circuit
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
    {W : Set Shat}
    {H : Drawing Shat}
    {ρ : ℕ}
    {r : Shat}
    {Δv : Set Shat}
    {Dv : Drawing Shat}
    {F : Drawing Shat}
    {ord' : ℕ}
    {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {h : Shat}
    {v₁ : Shat}
    {v₂ : Shat}
    {c₁ : Shat}
    {c₂ : Shat}
    {h₁ : Shat}
    {h₂ : Shat}
    {f₁ : Set Shat}
    {f₂ : Set Shat}
    {A₁ : GraphWalk (Drawing.toGraph D.rad.G) v₁ c₁}
    {A₂ : GraphWalk (Drawing.toGraph D.rad.G) v₂ c₂}
    {T₁ : GraphWalk (Drawing.toGraph D.rad.G) c₁ h₁}
    {T₂ : GraphWalk (Drawing.toGraph D.rad.G) c₂ h₂}
    (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂)
    {b : Shat}
    {Q : GraphWalk (Drawing.toGraph D.rad.G) r b}
    {X : GraphWalk (Drawing.toGraph D.rad.G) v₁ b}
    (hman : ∀ (x : Shat), IsManifoldPoint x)
    (hx : D.IsSectorEnclave W H ρ r Δv Dv ord' 𝒯' F)
    (hW : D.IsWheelHubOfRadius W H ρ)
    (hUF : F.U ⊆ D.ins F)
    (hclbd : ∀ {f : Set Shat}, f ⊆ discBd W → closure f ⊆ discBd W)
    (hXK : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G X).U → y ∈ (walkDrawing D.rad.G (A₁.append
      T₁)).U)
    (N : GraphWalk (Drawing.toGraph D.rad.G) r b)
    (hNcases : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G N).U → y ∈ closure f₁ ∨ y ∈ (walkDrawing
      D.rad.G X).U)
    (hQU : (walkDrawing D.rad.G Q).U ⊆ F.U)
    (Δ' : Set Shat)
    (hd' : IsClosedDisc Δ')
    (hbd : discBd Δ' = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U)
    (hhint : h ∈ discInt Δ')
    {y : Shat}
    (hy : y ∈ H.U)
    (hEn : IsEnclave D.tb D.ord D.𝒯 H)
    (hle : (Drawing.E H).ncard ≤ 4 * ρ + 4)
    (hi : h ∈ discInt (D.ins H)) :
    y ∈ Δ' := by
  obtain ⟨-, -, -, hHc, hHlt, -⟩ := id hEn
  have hHi := D.ins_spec hHc (by have := hW.rep_ge; omega)
  have hΔH := hHi.2.2.1
  have hsub := subset_discInt_of_connected hman hd' hΔH.isPreconnected_discInt
    (disjoint_left.mpr fun x hi' hb₀ ↦ by
    rw [hbd] at hb₀
    rcases hb₀ with hq | hn
    · have hm : x ∈ D.ins F ∩ D.ins H := ⟨hUF (hQU hq), discInt_subset _ hi'⟩
      rw [hx.hub_circuit hEn] at hm
      exact hi'.2 (hHi.2.2.2.1 ▸ hm.2)
    · rcases hNcases hn with hc | hc
      · exact disjoint_left.mp (hW.ins_off_bd hHc hle) (discInt_subset _ hi') (hclbd s.bd₁ hc)
      · exact disjoint_left.mp (IsSpokeWalk.off_ins_hub hW hEn hle s.spoke₁) (hXK hc) hi') ⟨h,
          hi, hhint⟩
  have hcl : D.ins H ⊆ Δ' := by
    rw [← closure_discInt hΔH, ← closure_discInt hd']
    exact closure_mono hsub
  exact hcl (Surface.discBd_subset _ (hHi.2.2.2.1 ▸ hy))

private theorem hub_point_off_outer_disc_boundary
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
    {W : Set Shat}
    {H : Drawing Shat}
    {ρ : ℕ}
    {r : Shat}
    {Δv : Set Shat}
    {Dv : Drawing Shat}
    {F : Drawing Shat}
    {ord' : ℕ}
    {𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {Δ₀ : Set Shat}
    {Δ : Set Shat}
    {C : Drawing Shat}
    {h : Shat}
    {v₁ : Shat}
    {v₂ : Shat}
    {c₁ : Shat}
    {c₂ : Shat}
    {h₁ : Shat}
    {h₂ : Shat}
    {f₁ : Set Shat}
    {f₂ : Set Shat}
    {A₁ : GraphWalk (Drawing.toGraph D.rad.G) v₁ c₁}
    {A₂ : GraphWalk (Drawing.toGraph D.rad.G) v₂ c₂}
    {T₁ : GraphWalk (Drawing.toGraph D.rad.G) c₁ h₁}
    {T₂ : GraphWalk (Drawing.toGraph D.rad.G) c₂ h₂}
    (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
    (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂)
    {b : Shat}
    {Q : GraphWalk (Drawing.toGraph D.rad.G) r b}
    {X : GraphWalk (Drawing.toGraph D.rad.G) v₁ b}
    {Z : GraphWalk (Drawing.toGraph D.rad.G) b c₁}
    (hW : D.IsWheelHubOfRadius W H ρ)
    (hnotF : h ∉ F.U)
    (hclbd : ∀ {f : Set Shat}, f ⊆ discBd W → closure f ⊆ discBd W)
    (hXK : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G X).U → y ∈ (walkDrawing D.rad.G (A₁.append
      T₁)).U)
    (N : GraphWalk (Drawing.toGraph D.rad.G) r b)
    (hNcases : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G N).U → y ∈ closure f₁ ∨ y ∈ (walkDrawing
      D.rad.G X).U)
    (hQU : (walkDrawing D.rad.G Q).U ⊆ F.U)
    (Δ' : Set Shat)
    (hbd : discBd Δ' = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U)
    (hmeetX : ∀ {y : Shat}, y ∈ X.support → y ∈ (Z.append T₁).support → y = b) :
    h ∉ discBd Δ' := by
  rw [hbd]
  rintro (hq | hn)
  · exact hnotF (hQU hq)
  · rcases hf.hub with ⟨hV, -⟩ | ⟨hEn, hle, hi⟩
    · have hhV : h ∈ H.V := by rw [hV]; rfl
      rcases hNcases hn with hc | hc
      · exact (hW.H_in_int (H.V_subset_U hhV)).2 (hclbd s.bd₁ hc)
      · have e₁ := IsSpokeWalk.U_inter_hub hW s.spoke₁ (hXK hc) (H.V_subset_U hhV)
        have hsup : h ∈ X.support := by
          have := mem_V_of_mem_U (walkDrawing_isSubdrawing D.rad.G X) hc (hW.H_sub.1 hhV)
          rw [walkDrawing_V] at this
          exact this
        have hend : h ∈ (Z.append T₁).support := by
          rw [e₁]
          exact (Z.append T₁).end_mem_support
        exact hnotF (hQU (by
          rw [hmeetX hsup hend]
          exact (mem_walkDrawing_U _ _).mpr (.inl Q.end_mem_support)))
    · obtain ⟨-, -, -, hHc, hHlt, -⟩ := id hEn
      rcases hNcases hn with hc | hc
      · exact disjoint_left.mp (hW.ins_off_bd hHc hle) (discInt_subset _ hi) (hclbd s.bd₁ hc)
      · exact disjoint_left.mp (IsSpokeWalk.off_ins_hub hW hEn hle s.spoke₁) (hXK hc) hi

/-- Step (11) of the proof of (13.6): an outer arc from `r*` to `b` on `A₁` that cannot be pushed
into `Δ_v`, with the path of `D_v` from `r*` to `b` through `v₁`, makes up `C`. -/
theorem outer_circuit (hf : D.IsFar W H ρ r Δv Dv ord' 𝒯' F Δ₀ C Δ h)
  (s : D.IsShape W H r Δv Dv F f₁ f₂ A₁ A₂ T₁ T₂) (ha : D.IsAnchor H ρ Δv Dv F h f₁ f₂ A₁ A₂ Y) {b
    : Shat}
    {Q : GraphWalk D.rad.G.toGraph r b} {X : GraphWalk D.rad.G.toGraph v₁ b} {Z : GraphWalk
      D.rad.G.toGraph b c₁} (hQ : IsArcOn D.rad.G Dv F Q) (ho : ∀ e ∈ Q.edges, Disjoint e Δv)
    (hA : A₁ = X.append Z) (hnp : ¬ PushesInto (Δ₀ \ {h}) (Δv \ {h}) (walkDrawing D.rad.G Q).U r b)
      : ∀ e, e ∈ C.E ↔ e ∈ Q.edges ∨ e ∈ (GraphWalk.cons s.link₁ X).edges := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hx := hf.enc
  have hW := hx.wheel
  have hFi := hx.isInsOf_F
  have hFc := hFi.1
  have hFs := hFc.1
  have hE := hx.isEnclave
  have hDv := hx.sector.Dv_circuit
  have hΔv := hx.sector.is_disc
  have hbv := hx.sector.Dv_U.symm
  have hΔF := hFi.2.2.1
  have hbF := hFi.2.2.2.1
  have hnotF : h ∉ F.U := fun hu ↦ hf.notMem_ins_F (Surface.discBd_subset _ (hbF ▸ hu))
  have hUvΔ : Dv.U ⊆ Δv := fun x hx' ↦ Surface.discBd_subset _ (hbv ▸ hx')
  have hUF : F.U ⊆ D.ins F := fun x hx' ↦ Surface.discBd_subset _ (hbF ▸ hx')
  have hclbd : ∀ {f : Set Shat}, f ⊆ discBd W → closure f ⊆ discBd W := fun hf' ↦ closure_minimal
    hf' (by
    rw [← IsClosedDisc.frontier_eq_discBd hT hW.is_disc]; exact isClosed_frontier)
  have hK : (X.append (Z.append T₁)).IsSimple := by
    have := s.spoke₁.1
    rwa [hA, GraphWalk.append_assoc'] at this
  have hXA : ∀ y ∈ X.support, y ∈ A₁.support := fun y hy ↦ by
    rw [hA, GraphWalk.mem_support_append]
    exact .inl hy
  have hXAe : ∀ e ∈ X.edges, e ∈ A₁.edges := fun e he ↦ by
    rw [hA, GraphWalk.edges_append]
    exact List.mem_append_left _ he
  have hXK : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G X).U → y ∈ (walkDrawing D.rad.G
    (A₁.append T₁)).U := fun hy ↦
    walkU_subset (K := X) (fun y hy ↦ (GraphWalk.mem_support_append _ _).mpr (.inl (hXA y hy)))
      (fun e he ↦ by
      rw [GraphWalk.edges_append]; exact List.mem_append_left _ (hXAe e he)) hy
  have hXA' : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G X).U → y ∈ (walkDrawing D.rad.G A₁).U
    := fun hy ↦ walkU_subset (K := X) hXA hXAe hy
  have hrnot : r ∉ (A₁.append T₁).support := IsWheelHubOfRadius.r_notMem_spoke hW hx.hbdS hx.hin
    hx.sector.rstar_mem s.spoke₁
  have hrA₂ : r ∉ (A₂.append T₂).support := IsWheelHubOfRadius.r_notMem_spoke hW hx.hbdS hx.hin
    hx.sector.rstar_mem s.spoke₂
  have hrX : r ∉ X.support := fun h' ↦ hrnot ((GraphWalk.mem_support_append _ _).mpr (.inl
    (hXA r h')))
  -- The path `P₁`, called `N` here.
  set N : GraphWalk D.rad.G.toGraph r b := GraphWalk.cons s.link₁ X with hNdef
  have hNs : N.IsSimple := List.nodup_cons.mpr ⟨hrX, (isSimple_of_append hK).1⟩
  have hNsup : ∀ y, y ∈ N.support ↔ y = r ∨ y ∈ X.support := fun y ↦ by
    rw [hNdef, GraphWalk.support_cons, List.mem_cons]
  have hNe : ∀ e, e ∈ N.edges ↔ e = f₁ ∨ e ∈ X.edges := fun e ↦ by
    rw [hNdef, GraphWalk.edges_cons, List.mem_cons]
  have hrD : r ∈ Dv.V := (Drawing.IsLink.mem_V_of_sub hDv.1 s.link₁ s.f₁_mem).1
  have hNV : ∀ y ∈ N.support, y ∈ Dv.V := fun y hy ↦ by
    rcases (hNsup y).mp hy with rfl | hy
    · exact hrD
    · exact s.mem₁ y (hXA y hy)
  have hNE : ∀ e ∈ N.edges, e ∈ Dv.E := fun e he ↦ by
    rcases (hNe e).mp he with rfl | he
    · exact s.f₁_mem
    · exact s.edge₁ e (hXAe e he)
  have hNU : (walkDrawing D.rad.G N).U ⊆ Dv.U := fun y hy ↦ by
    rcases (mem_walkDrawing_U _ _).mp hy with h' | ⟨e, he, hye⟩
    · exact Dv.V_subset_U (hNV y h')
    · exact Dv.closure_subset_U (hNE e he) hye
  have hNcases : ∀ {y : Shat}, y ∈ (walkDrawing D.rad.G N).U → y ∈ closure f₁ ∨ y ∈
    (walkDrawing D.rad.G X).U := fun {y} hy ↦ by
    rcases (mem_walkDrawing_U _ _).mp hy with h' | ⟨e, he, hye⟩
    · rcases (hNsup y).mp h' with rfl | h'
      · exact .inl (IsLink.left_mem_closure s.link₁)
      · exact .inr ((mem_walkDrawing_U _ _).mpr (.inl h'))
    · rcases (hNe e).mp he with rfl | he
      · exact .inl hye
      · exact .inr ((mem_walkDrawing_U _ _).mpr (.inr ⟨e, he, hye⟩))
  have hQU : (walkDrawing D.rad.G Q).U ⊆ F.U := fun y hy ↦ by
    rcases (mem_walkDrawing_U _ _).mp hy with h' | ⟨e, he, hye⟩
    · exact F.V_subset_U (hQ.mem_F hFs y h')
    · exact F.closure_subset_U (hQ.inF e he) hye
  have hbA : b ∈ A₁.support := hXA b X.end_mem_support
  have hbF' : b ∈ F.V := hQ.mem_F hFs _ Q.end_mem_support
  -- The circuit `P₁ ∪ F₁`, and its disc in `Δ₀`.
  have hQs := walkDrawing_isSubdrawing D.rad.G Q
  have hNs' := walkDrawing_isSubdrawing D.rad.G N
  have hQp := walkDrawing_isPathBetween D.rad.G hQ.simple
  have hNp := walkDrawing_isPathBetween D.rad.G hNs
  have hcircuit : (D.rad.G.sup (walkDrawing D.rad.G Q) (walkDrawing D.rad.G N)).IsCircuit := by
    refine circuit_sup hQs hNs' hQp hNp hQ.ne ?_ ?_
    · rintro y ⟨h₀, h₁'⟩
      rw [walkDrawing_V] at h₀ h₁'
      exact hQ.inner y h₀ (hNV y h₁')
    · refine disjoint_left.mpr fun e h₀ h₁' ↦ ?_
      rw [walkDrawing_E] at h₀ h₁'
      exact hQ.off e h₀ (hNE e h₁')
  set C' := D.rad.G.sup (walkDrawing D.rad.G Q) (walkDrawing D.rad.G N) with hC'
  have hC'sub : C'.IsSubdrawing D.rad.G := D.rad.G.sup_isSubdrawing _ _
  have hC'V : ∀ y, y ∈ C'.V ↔ y ∈ Q.support ∨ y ∈ N.support := fun y ↦ by
    rw [hC', Drawing.sup_V hQs hNs', walkDrawing_V, walkDrawing_V]
    rfl
  have hC'E : ∀ e, e ∈ C'.E ↔ e ∈ Q.edges ∨ e ∈ N.edges := fun e ↦ by
    rw [hC', Drawing.sup_E hQs hNs', walkDrawing_E, walkDrawing_E]
    rfl
  have hC'U : C'.U = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U := U_union
    (Drawing.sup_V hQs hNs') (Drawing.sup_E hQs hNs')
  have hNΔ : (walkDrawing D.rad.G N).U ⊆ Δv := hNU.trans hUvΔ
  have hC'Δ₀ : C'.U ⊆ Δ₀ := by
    rw [hC'U]
    exact union_subset (hQU.trans (hUF.trans hf.amb.ins_F)) (hNΔ.trans (hf.v_sub.trans hf.sub))
  obtain ⟨Δ', ⟨hs', hd', hb', -⟩, -⟩ := disc_oArc Δ₀ C'.U hf.amb.disc hC'Δ₀
    (GM14.isOArc_of_isCircuit hcircuit)
  have hbd : discBd Δ' = (walkDrawing D.rad.G Q).U ∪ (walkDrawing D.rad.G N).U := hb'.trans hC'U
  have hhΔ' : h ∈ Δ' := IsFar.mem_disc_of_blocked (D := D) hQ.ne hNs hNΔ hd' hs' hbd hnp
  have hinbd : ∀ {y : Shat}, y ∈ discBd Δ' → y ∈ Δ' := fun hy ↦ Surface.discBd_subset _ hy
  have hmeetX : ∀ {y : Shat}, y ∈ X.support → y ∈ (Z.append T₁).support → y = b
    := fun h₁' h₂' ↦ Splits.append_meet hK h₁' h₂'
  -- `h` is not on the boundary of the disc.
  have hhb : h ∉ discBd Δ' := by
    exact hub_point_off_outer_disc_boundary (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ)
      (D := D) (W := W) (H := H) (ρ := ρ) (r := r) (Δv := Δv) (Dv := Dv) (F := F) (ord' := ord')
      (𝒯' := 𝒯') (Δ₀ := Δ₀) (Δ := Δ) (C := C) (h := h) (v₁ := v₁) (v₂ := v₂) (c₁ := c₁) (c₂ := c₂)
      (h₁ := h₁) (h₂ := h₂) (f₁ := f₁) (f₂ := f₂) (A₁ := A₁) (A₂ := A₂) (T₁ := T₁) (T₂ := T₂) hf s
      (b := b) (Q := Q) (X := X) (Z := Z) hW hnotF hclbd hXK N hNcases hQU Δ' hbd hmeetX
  have hhint : h ∈ discInt Δ' := ⟨hhΔ', hhb⟩
  -- The hub is in the disc.
  have hHin : ∀ {y : Shat}, y ∈ H.U → IsEnclave D.tb D.ord D.𝒯 H → H.E.ncard ≤ 4 * ρ + 4
    → h ∈ discInt (D.ins H) → y ∈ Δ' := fun {y} hy hEn hle hi ↦ by
    exact hub_inside_outer_circuit (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ) (D := D)
      (W := W) (H := H) (ρ := ρ) (r := r) (Δv := Δv) (Dv := Dv) (F := F) (ord' := ord') (𝒯' := 𝒯')
      (h := h) (v₁ := v₁) (v₂ := v₂) (c₁ := c₁) (c₂ := c₂) (h₁ := h₁) (h₂ := h₂) (f₁ := f₁) (f₂ :=
      f₂) (A₁ := A₁) (A₂ := A₂) (T₁ := T₁) (T₂ := T₂) s (b := b) (Q := Q) (X := X) hman hx hW hUF
      hclbd hXK N hNcases hQU Δ' hd' hbd hhint (y := y) hy hEn hle hi
  -- The anchor is inside the disc.
  have hYb : Disjoint Y (discBd Δ') := disjoint_left.mpr fun y hy hb₀ ↦ by
    rw [hbd] at hb₀
    rcases hb₀ with hq | hn
    · exact disjoint_left.mp (ha.off_arc hQ) hy hq
    · rcases hNcases hn with hc | hc
      · exact disjoint_left.mp ha.off_f₁ hy hc
      · have e₁ := ha.off_A₁ y hy (hXA' hc)
        have hsup : y ∈ X.support := by
          have := mem_V_of_mem_U (walkDrawing_isSubdrawing D.rad.G X) hc (by
            rw [e₁]
            exact A₁.mem_vertexSet_of_mem_support A₁.end_mem_support)
          rw [walkDrawing_V] at this
          exact this
        have hend : y ∈ Z.support := by rw [e₁]; exact Z.end_mem_support
        have e₂ := Splits.append_meet (hA ▸ (isSimple_of_append s.spoke₁.1).1) hsup hend
        exact disjoint_left.mp (ha.off_arc hQ) hy (by
          rw [e₂]
          exact (mem_walkDrawing_U _ _).mpr (.inl Q.end_mem_support))
  obtain ⟨y, hyY, hyh⟩ := ha.hub
  have hyΔ' : y ∈ Δ' := by
    rcases hyh with rfl | ⟨h₀, h₁', h₂', h₃'⟩
    · exact hhΔ'
    · exact hHin h₀ h₁' h₂' h₃'
  have hYint : Y ⊆ discInt Δ' := subset_discInt_of_connected hman hd' ha.pre hYb ⟨y, hyY, hyΔ',
    disjoint_left.mp hYb hyY⟩
  -- Hence `Δ_v` is in the disc.
  have hΔvΔ' : Δv ⊆ Δ' := by
    exact sector_inside_outer_circuit (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ) (D :=
      D) (H := H) (ρ := ρ) (r := r) (Δv := Δv) (Dv := Dv) (F := F) (h := h) (v₁ := v₁) (v₂ := v₂)
      (c₁ := c₁) (c₂ := c₂) (f₁ := f₁) (f₂ := f₂) (A₁ := A₁) (A₂ := A₂) (Y := Y) ha (b := b) (Q :=
      Q) hQ ho hman hΔv hbv N hNU Δ' hd' hbd hYint
  have hDvΔ' : Dv.U ⊆ Δ' := hUvΔ.trans hΔvΔ'
  -- All of `F` is in the disc.
  have hNin : ∀ c, c ∈ C'.V → c ∈ Dv.V → c ∈ N.support := fun c hc hcD ↦ by
    rcases (hC'V c).mp hc with h' | h'
    · rcases hQ.inner c h' hcD with rfl | rfl
      · exact N.start_mem_support
      · exact N.end_mem_support
    · exact h'
  have hFΔ' : F.U ⊆ Δ' := by
    exact enclave_inside_outer_circuit (S := S) (Shat := Shat) (α := α) (cap := cap) (χ := χ) (D
      := D) (W := W) (H := H) (ρ := ρ) (r := r) (Δv := Δv) (Dv := Dv) (F := F) (ord' := ord') (𝒯'
      := 𝒯') (Δ₀ := Δ₀) (Δ := Δ) (C := C) (h := h) (v₁ := v₁) (v₂ := v₂) (c₁ := c₁) (c₂ := c₂) (h₁
      := h₁) (h₂ := h₂) (f₁ := f₁) (f₂ := f₂) (A₁ := A₁) (A₂ := A₂) (T₁ := T₁) (T₂ := T₂) hf s (b
      := b) (Q := Q) (X := X) hQ ho hnp hT hx hFc hFs hE hDv hΔv hbv hXA hrnot hrA₂ hrX N hNdef
      hNs hNsup hNe hrD hNV hNE hNU hNcases hQU hbA hbF' hQs hNs' hQp hNp C' hC' hC'sub
      hC'V hC'E hC'U hNΔ Δ' hd' hb' hbd hinbd hΔvΔ' hDvΔ' hNin
  -- So the disc is `Δ`.
  have hFiΔ' : D.ins F ⊆ Δ' := disc_subset_of_bd hT hf.amb.disc hΔF hd' hf.amb.ins_F hs' (by
    rw [hbF]
    exact hFΔ')
  have h₁' : Δ' ⊆ Δ := disc_subset_of_bd hT hf.amb.disc hd' hf.disc hs' hf.sub (by
    rw [hbd]
    exact union_subset (hQU.trans (hUF.trans hf.F_sub)) (hNΔ.trans hf.v_sub))
  have h₂' : Δ ⊆ Δ' := disc_subset_of_bd hT hf.amb.disc hf.disc hd' hf.sub hs' (by
    rw [hf.bd]
    refine U_of_edges hf.circuit.2 hd'.isClosed fun e he ↦ ?_
    rcases hf.edges e he with h₀ | h₀
    · exact subset_closure.trans ((F.closure_subset_U h₀).trans hFΔ')
    · exact subset_closure.trans ((Dv.closure_subset_U h₀).trans hDvΔ'))
  have hUeq : C.U = C'.U := by
    rw [← hf.bd, ← hb', Subset.antisymm h₁' h₂']
  intro e
  rw [← hC'E]
  constructor
  · intro he
    by_contra hn
    have heG := hf.circuit.1.2 he
    obtain ⟨p, hp⟩ := heG.1
    exact disjoint_left.mp (edge_disjoint_U hC'sub heG hn) hp (hUeq ▸ C.closure_subset_U he
      (subset_closure hp))
  · intro he
    by_contra hn
    have heG := hC'sub.2 he
    obtain ⟨p, hp⟩ := heG.1
    exact disjoint_left.mp (edge_disjoint_U hf.circuit.1 heG hn) hp (hUeq ▸ C'.closure_subset_U he
      (subset_closure hp))

end IsFar

end TangleDatum

end GraphMinor.GM19
