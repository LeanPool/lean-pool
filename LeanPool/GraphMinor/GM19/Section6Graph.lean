/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Minor
public import LeanPool.GraphMinor.GM19.RadialExists
public import LeanPool.GraphMinor.Surface.TriGraph
public import LeanPool.GraphMinor.Surface.Fan

/-!
# Drawings as graphs in a surface

A drawing without loops is a graph in the sense of `GraphMinor.Surface.IsGraph`
(`isGraph_of_loopFree`), and a graph gives a drawing (`IsGraph.toDrawing`). If no vertex cuts the
graph of a drawing with at least three vertices, then no point cuts its underlying set
(`twoConn_U`). This is what we need to extend a drawing to a triangulation of the surface, for the
count in Graph Minors XIX, (6.5) (page 341).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- The set `X` of vertices is connected in the graph of `D`: a nonempty part of `X` closed under
adjacency in `X` is all of `X`. -/
def ConnIn (D : Drawing S) (X : Set S) : Prop :=
  ∀ Y ⊆ X, Y.Nonempty → (∀ a ∈ Y, ∀ b ∈ X, D.adj.Adj a b → b ∈ Y) → Y = X

variable [T2Space S]

omit [T2Space S] in
theorem exists_edge_of_mem (D : Drawing S) {x : S} (hx : x ∈ D.U) (hV : x ∉ D.V) : ∃ e ∈ D.E, x ∈ e
  := by
  obtain ⟨c, hc, hxc⟩ := exists_arcComp_superset (F := D.U \ D.V) (C := {x})
    (isPathConnected_singleton x)
    (singleton_subset_iff.mpr ⟨hx, hV⟩)
  exact ⟨c, hc, hxc rfl⟩

omit [T2Space S] in
theorem edge_eq_of_mem (D : Drawing S) {e f : Set S} (he : e ∈ D.E) (hf : f ∈ D.E) {x : S}
  (hxe : x ∈ closure e) (hxf : x ∈ closure f)
    (hV : x ∉ D.V) : e = f := by
  have h1 : x ∈ e := D.closure_diff_V he ▸ ⟨hxe, hV⟩
  have h2 : x ∈ f := D.closure_diff_V hf ▸ ⟨hxf, hV⟩
  exact arcComp_eq_of_mem he hf h1 h2

omit [T2Space S] in
theorem exists_end (D : Drawing S) (hl : LoopFree D) {e : Set S} (he : e ∈ D.E) :
    ∃ u v, u ≠ v ∧ tilde e = {u, v} ∧ IsLineWithEnds (closure e) u v ∧ closure e ∩ D.V = {u, v}
      := by
  obtain ⟨u, v, huv, ht, hL⟩ := hl e he
  exact ⟨u, v, huv, ht, hL, by rw [← GraphMinor.GM19.tilde_eq_inter_V D he, ht]⟩

omit [T2Space S] in
/-- A drawing without loops is a graph. -/
theorem isGraph_of_loopFree (D : Drawing S) (hl : LoopFree D) : IsGraph D.V (closure '' D.E) := by
  refine ⟨D.finite_V, D.finite_edges.image _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨u, v, huv, -, hL, hi⟩ := exists_end D hl he
    exact ⟨u, v, huv, hL, hi⟩
  · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hne x hx
    by_contra hV
    exact hne (congrArg closure (edge_eq_of_mem D he hf hx.1 hx.2 hV))

omit [T2Space S] in
theorem U_eq (D : Drawing S) : D.U = D.V ∪ ⋃₀ (closure '' D.E) := by
  refine Subset.antisymm (fun x hx => ?_) (union_subset D.V_subset_U (sUnion_subset ?_))
  · by_cases hV : x ∈ D.V
    · exact .inl hV
    · obtain ⟨e, he, hxe⟩ := exists_edge_of_mem D hx hV
      exact .inr ⟨_, ⟨e, he, rfl⟩, subset_closure hxe⟩
  · rintro _ ⟨e, he, rfl⟩
    exact D.closure_subset_U he

omit [T2Space S] in
theorem exists_adj (D : Drawing S) (h3 : 3 ≤ D.V.ncard) (hc : ∀ v ∈ D.V, ConnIn D
    (D.V \ {v})) : ∀ a ∈ D.V, ∀ c ∈ D.V, a ≠ c → ∃ b, b ≠ c ∧ D.adj.Adj a b := by
  intro a ha c hc' hac
  by_contra hno
  push Not at hno
  have h1 := hc c hc' {a} (singleton_subset_iff.mpr ⟨ha, hac⟩) (singleton_nonempty a)
    (fun x hx b hb hadj => absurd hadj (by
    have : x = a := hx
    subst this
    exact hno b hb.2))
  have h2 : D.V ⊆ {a, c} := fun y hy => by
    by_cases hyc : y = c
    · exact .inr hyc
    · have : y ∈ ({a} : Set S) := h1 ▸ ⟨hy, hyc⟩
      exact .inl this
  have h4 := ncard_le_ncard h2 (toFinite _)
  have h5 := ncard_pair hac
  omega

omit [T2Space S] in
/-- If no vertex cuts the graph of a drawing with at least three vertices, then no point cuts its
underlying set. -/
theorem twoConn_U (D : Drawing S) (hl : LoopFree D) (h3 : 3 ≤ D.V.ncard) (hc : ∀ v ∈ D.V, ConnIn D
  (D.V \ {v})) : TwoConn D.U := by
  have hnbr := exists_adj D h3 hc
  have hclosure : ∀ e ∈ D.E, IsPreconnected (closure e) := fun e he => by
    obtain ⟨u, v, -, -, hL, -⟩ := exists_end D hl he
    exact hL.isPreconnected_self
  have hjoin : ∀ {C P : Set S} {x y : S}, IsPreconnected P → P ⊆ C → x ∈ P → y ∈ P
    → ∀ {z}, x ∈ connectedComponentIn C z → y ∈ connectedComponentIn C z :=
    fun {C P x y} hP hPC hx hy {z} hxz => by
      have h1 := hP.subset_connectedComponentIn hx hPC
      rw [connectedComponentIn_eq hxz]
      exact h1 hy
  intro p
  have hV3 : 1 < D.V.ncard := by omega
  by_cases hp : p ∈ D.V
  · obtain ⟨x₀, hx₀⟩ : (D.V \ {p}).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hne
      have h1 := ncard_le_ncard hne (toFinite _)
      rw [ncard_singleton] at h1
      omega
    have hx₀C : x₀ ∈ D.U \ {p} := ⟨D.V_subset_U hx₀.1, hx₀.2⟩
    have hoff : ∀ e ∈ D.E, p ∉ closure e → closure e ⊆ D.U \ {p} := fun e he hpe y hy =>
      ⟨D.closure_subset_U he hy, fun h => hpe (h ▸ hy)⟩
    have hY := hc p hp (D.V \ {p} ∩ connectedComponentIn (D.U \ {p}) x₀) inter_subset_left ⟨x₀,
      hx₀, mem_connectedComponentIn hx₀C⟩ (by
      rintro a ⟨ha, haC⟩ b hb ⟨hab, -, -, e, he, hae, hbe⟩
      refine ⟨hb, ?_⟩
      obtain ⟨u, v, -, ht, -, hi⟩ := exists_end D hl he
      have hpe : p ∉ closure e := fun hpe => by
        have h1 : p ∈ ({u, v} : Set S) := hi ▸ ⟨hpe, hp⟩
        rw [ht] at hae hbe
        rcases h1 with rfl | rfl <;> rcases hae with rfl | rfl <;>
          first
          | exact ha.2 rfl
          | rcases hbe with rfl | rfl <;> first | exact hb.2 rfl | exact hab rfl
      exact hjoin (hclosure e he) (hoff e he hpe) hae.1 hbe.1 haC)
    have hall : D.U \ {p} ⊆ connectedComponentIn (D.U \ {p}) x₀ := fun y hy => by
      by_cases hyV : y ∈ D.V
      · have : y ∈ D.V \ {p} := ⟨hyV, hy.2⟩
        rw [← hY] at this
        exact this.2
      obtain ⟨e, he, hye⟩ := exists_edge_of_mem D hy.1 hyV
      obtain ⟨u, v, huv, ht, hL, hi⟩ := exists_end D hl he
      have huV : u ∈ closure e ∩ D.V := hi ▸ Or.inl rfl
      have hvV : v ∈ closure e ∩ D.V := hi ▸ Or.inr rfl
      have hend : ∀ w ∈ closure e ∩ D.V, w ≠ p → w ∈ connectedComponentIn (D.U \ {p}) x₀
        := fun w hw hwp => by
        have : w ∈ D.V \ {p} := ⟨hw.2, hwp⟩
        rw [← hY] at this
        exact this.2
      by_cases hpe : p ∈ closure e
      · have h1 : p ∈ ({u, v} : Set S) := hi ▸ ⟨hpe, hp⟩
        rcases h1 with rfl | rfl
        · have hP : IsPreconnected (closure e \ {p}) := hL.isPreconnected_diff_left
          exact hjoin (C := D.U \ {p}) hP (fun z hz => ⟨D.closure_subset_U he hz.1,
            hz.2⟩) ⟨hvV.1, huv.symm⟩ ⟨subset_closure hye, hy.2⟩ (hend v hvV huv.symm)
        · have hP : IsPreconnected (closure e \ {p}) := hL.isPreconnected_diff_right
          exact hjoin (C := D.U \ {p}) hP (fun z hz => ⟨D.closure_subset_U he hz.1,
            hz.2⟩) ⟨huV.1, huv⟩ ⟨subset_closure hye, hy.2⟩ (hend u huV huv)
      · exact hjoin (hclosure e he) (hoff e he hpe) huV.1 (subset_closure hye) (hend u huV fun h
        => hpe (h ▸ huV.1))
    have he : D.U \ {p} = connectedComponentIn (D.U \ {p}) x₀ := Subset.antisymm hall
      (connectedComponentIn_subset _ _)
    rw [he]
    exact isPreconnected_connectedComponentIn
  · obtain ⟨u, v, huv, huV, hvV, hspec⟩ : ∃ u v, u ≠ v ∧ u ∈ D.V ∧ v ∈ D.V
    ∧ ∀ e ∈ D.E, p ∈ closure e → tilde e = {u, v} := by
      by_cases he₀ : ∃ e ∈ D.E, p ∈ closure e
      · obtain ⟨e, he, hpe⟩ := he₀
        obtain ⟨u, v, huv, ht, -, hi⟩ := exists_end D hl he
        have huV : u ∈ closure e ∩ D.V := hi ▸ Or.inl rfl
        have hvV : v ∈ closure e ∩ D.V := hi ▸ Or.inr rfl
        refine ⟨u, v, huv, huV.2, hvV.2, fun f hf hpf => ?_⟩
        rw [← edge_eq_of_mem D he hf hpe hpf hp, ht]
      · obtain ⟨u, hu, v, hv, huv⟩ := (one_lt_ncard D.finite_V).mp hV3
        exact ⟨u, v, huv, hu, hv, fun e he hpe => absurd ⟨e, he, hpe⟩ he₀⟩
    have hv₀ : v ∈ D.U \ {p} := ⟨D.V_subset_U hvV, fun h => hp (h ▸ hvV)⟩
    have hoff : ∀ e ∈ D.E, tilde e ≠ {u, v} → closure e ⊆ D.U \ {p} := fun e he hne y hy =>
      ⟨D.closure_subset_U he hy, fun h => hne (hspec e he (h ▸ hy))⟩
    have hY := hc u huV (D.V \ {u} ∩ connectedComponentIn (D.U \ {p}) v) inter_subset_left
      ⟨v, ⟨hvV, huv.symm⟩, mem_connectedComponentIn hv₀⟩ (by
      rintro a ⟨ha, haC⟩ b hb ⟨hab, -, -, e, he, hae, hbe⟩
      refine ⟨hb, hjoin (hclosure e he) (hoff e he fun hte => ?_) hae.1 hbe.1 haC⟩
      rw [hte] at hae hbe
      rcases hae with rfl | rfl
      · exact ha.2 rfl
      rcases hbe with rfl | rfl
      · exact hb.2 rfl
      · exact hab rfl)
    have hmem : ∀ w ∈ D.V, w ≠ u → w ∈ connectedComponentIn (D.U \ {p}) v := fun w hw hwu => by
      have : w ∈ D.V \ {u} := ⟨hw, hwu⟩
      rw [← hY] at this
      exact this.2
    have hVC : ∀ w ∈ D.V, w ∈ connectedComponentIn (D.U \ {p}) v := fun w hw => by
      by_cases hwu : w = u
      · subst hwu
        obtain ⟨b, hbv, hab, -, hb, e, he, hae, hbe⟩ := hnbr w hw v hvV huv
        refine hjoin (hclosure e he) (hoff e he fun hte => ?_) hbe.1 hae.1 (hmem b hb hab.symm)
        rw [hte] at hbe
        rcases hbe with h | h
        · exact hab h.symm
        · exact hbv h
      · exact hmem w hw hwu
    have hall : D.U \ {p} ⊆ connectedComponentIn (D.U \ {p}) v := fun y hy => by
      by_cases hyV : y ∈ D.V
      · exact hVC y hyV
      obtain ⟨e, he, hye⟩ := exists_edge_of_mem D hy.1 hyV
      obtain ⟨u', v', huv', -, hL, hi⟩ := exists_end D hl he
      have hu'V : u' ∈ closure e ∩ D.V := hi ▸ Or.inl rfl
      have hv'V : v' ∈ closure e ∩ D.V := hi ▸ Or.inr rfl
      by_cases hpe : p ∈ closure e
      · obtain ⟨a, ha, hr, h0, h1⟩ := hL.exists_arc
        obtain ⟨t, rfl⟩ : p ∈ range a := hr ▸ hpe
        obtain ⟨s, rfl⟩ : y ∈ range a := hr ▸ subset_closure hye
        have hst : s ≠ t := fun h => hy.2 (h ▸ rfl)
        have hsub : ∀ Q : Set unitInterval, t ∉ Q → a '' Q ⊆ D.U \ {a t} := fun Q hQ => by
          rintro _ ⟨r, hrQ, rfl⟩
          exact ⟨D.closure_subset_U he (hr ▸ mem_range_self r), fun h => hQ (ha.2 h ▸ hrQ)⟩
        rcases lt_or_gt_of_ne hst with hlt | hlt
        · have hP : IsPreconnected (a '' Iio t) :=
            ordConnected_Iio.isPreconnected.image _ ha.1.continuousOn
          have h0t : (0 : unitInterval) < t := lt_of_le_of_lt bot_le hlt
          exact hjoin hP (hsub _ (by simp)) ⟨0, h0t, rfl⟩ ⟨s, hlt, rfl⟩ (h0 ▸ hVC u' hu'V.2)
        · have hP : IsPreconnected (a '' Ioi t) :=
            ordConnected_Ioi.isPreconnected.image _ ha.1.continuousOn
          have h1t : t < (1 : unitInterval) := lt_of_lt_of_le hlt le_top
          exact hjoin hP (hsub _ (by simp)) ⟨1, h1t, rfl⟩ ⟨s, hlt, rfl⟩ (h1 ▸ hVC v' hv'V.2)
      · have hs : closure e ⊆ D.U \ {p} := fun z hz => ⟨D.closure_subset_U he hz, fun h => hpe
        (h ▸ hz)⟩
        exact hjoin (hclosure e he) hs hu'V.1 (subset_closure hye) (hVC u' hu'V.2)
    have he : D.U \ {p} = connectedComponentIn (D.U \ {p}) v := Subset.antisymm hall
      (connectedComponentIn_subset _ _)
    rw [he]
    exact isPreconnected_connectedComponentIn

omit [T2Space S] in
/-- Each vertex lies on a closed edge. -/
theorem V_subset_edges (D : Drawing S) (h3 : 3 ≤ D.V.ncard) (hc : ∀ v ∈ D.V, ConnIn D
  (D.V \ {v})) : D.V ⊆ ⋃₀ (closure '' D.E) := fun a ha => by
  obtain ⟨c, hc', hac⟩ : ∃ c ∈ D.V, a ≠ c := by
    by_contra hno
    push Not at hno
    have h1 : D.V ⊆ {a} := fun y hy => (hno y hy).symm
    have h2 := ncard_le_ncard h1 (toFinite _)
    rw [ncard_singleton] at h2
    omega
  obtain ⟨b, -, -, -, -, e, he, hae, -⟩ := exists_adj D h3 hc a ha c hc' hac
  exact ⟨_, ⟨e, he, rfl⟩, hae.1⟩

variable {T : Type} [TopologicalSpace T] [T2Space T]

omit [T2Space S] in
/-- The image of a graph under a map that is injective and continuous on a set that holds the graph.
-/
theorem isGraph_image {V : Set S} {E : Set (Set S)} (h : IsGraph V E) {ι : S → T} {Z : Set S}
  (hZ : gr V E ⊆ Z) (hc : ContinuousOn ι Z) (hi : InjOn ι Z) :
    IsGraph (ι '' V) ((fun e => ι '' e) '' E) := by
  have hE : ∀ e ∈ E, e ⊆ Z := fun e he x hx => hZ (.inr ⟨e, he, hx⟩)
  have hVZ : V ⊆ Z := fun x hx => hZ (.inl hx)
  refine ⟨h.fin.image _, h.fine.image _, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨u, v, huv, hl, hin⟩ := h.edge e he
    have hmu : u ∈ e ∩ V := hin ▸ Or.inl rfl
    have hmv : v ∈ e ∩ V := hin ▸ Or.inr rfl
    obtain ⟨a, ha, hr, h0, h1⟩ := hl.exists_arc
    have harc : IsArcMap (ι ∘ a) := ⟨hc.comp_continuous ha.1 fun t => hE e he
      (hr ▸ mem_range_self t), fun s t hst =>
      ha.2 (hi (hE e he (hr ▸ mem_range_self s)) (hE e he (hr ▸ mem_range_self t)) hst)⟩
    have hrr : range (ι ∘ a) = ι '' e := by rw [range_comp, hr]
    have hL := harc.isLineWithEnds
    rw [hrr] at hL
    simp only [Function.comp, h0, h1] at hL
    refine ⟨ι u, ι v, fun he' => huv (hi (hVZ hmu.2) (hVZ hmv.2) he'), hL, ?_⟩
    rw [← (hi.mono (union_subset (hE e he) hVZ)).image_inter subset_union_left subset_union_right,
      hin, image_pair]
  · rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hne _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h1 : y = x := hi (hE f hf hy) (hE e he hx) hxy
    subst h1
    have hef : e ≠ f := fun h' => hne (by rw [h'])
    exact mem_image_of_mem _ (h.disj e he f hf hef ⟨hx, hy⟩)

end GraphMinor.GM19
