/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.VortexAxioms

/-!
# The portrayal in XVII (13.1)

Last step of the construction in the proof of XVII (13.1), pages 203-204. From a segregation with a
proper arrangement in a closed surface we get a portrayal of the graph in the surface
with the polygons removed (`exists_portrayal_of_arrangement`). Its warp is at most `ρ + 1`, it has
at most `κ` cuffs, and each cell graph lies in a society of the segregation.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface GM09 GM14 GM15 GM16 Graph

universe u v

variable {α : Type u} [Nonempty α] {β : Type v} {S : Type} [TopologicalSpace S] [T2Space S] {G :
  Graph α β} {Seg : Set (Society α β)} {D : Society α β → Set S} {ν : α → S} {ρ : ℕ}
  {V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ}

theorem IsLineWithEnds.isPreconnected {T : Type*} [TopologicalSpace T] {L : Set T} {u v : T}
  (h : IsLineWithEnds L u v) : IsPreconnected L := by
  obtain ⟨f, -, -⟩ := h
  have : L = range (fun t => (f t).1) := by
    ext x
    constructor
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨t, rfl⟩
      exact (f t).2
  rw [this]
  exact isPreconnected_range (continuous_subtype_val.comp f.continuous)

variable (harr : IsProperArrangement Seg D ν) (hS : IsClosedSurface S) (hfin : Seg.Finite)
include harr hS hfin

/-- (P7). -/
theorem p7_aux [ConnectedSpace S] (m : Maj Seg) {n₁ n₂ n₃ n₄ : ↥(Cut V)} {Θ : Set ↥(Cut V)} (hΘ : Θ
  = Subtype.val ⁻¹' discBd (V m).P)
    (h₁ : n₁ ∈ NT V ∩ Θ) (h₂ : n₂ ∈ NT V ∩ Θ) (h₃ : n₃ ∈ NT V ∩ Θ) (h₄ : n₄ ∈ NT V ∩ Θ)
      (ho : GM19.InOrderOn Θ n₁ n₂ n₃ n₄) {v : α}
    (hv₁ : v ∈ bt V n₁.1 ∨ (n₁ ∈ NT V ∧ v = nv Seg ν n₁.1)) (hv₃ : v ∈ bt V n₃.1 ∨ (n₃ ∈ NT V ∧ v
      = nv Seg ν n₃.1)) :
    (v ∈ bt V n₂.1 ∨ (n₂ ∈ NT V ∧ v = nv Seg ν n₂.1)) ∨ (v ∈ bt V n₄.1 ∨ (n₄ ∈ NT V ∧ v
      = nv Seg ν n₄.1)) := by
  obtain ⟨-, h2, -, -, -⟩ := cut_surface (V := V) harr hS hfin
  have : T2Space ↥(Cut V) := h2.2.1
  have hLm : ∀ j, ν ((V m).t j) ∈ (V m).L j := fun j => ((V m).node_mem j j).mpr (Or.inl rfl)
  let nd : Fin (V m).k → ↥(Cut V) := fun j => ⟨ν ((V m).t j), Ds_sub_Cut harr (.inr ⟨m, j⟩) (hLm j)⟩
  have hnd : ∀ n ∈ NT V ∩ Θ, ∃ j, nd j = n := by
    rintro n ⟨hn, hb⟩
    obtain ⟨w, hw, he⟩ := hn
    rw [hΘ] at hb
    have hb' : ν w ∈ discBd (V m).P := by
      rw [he]
      exact hb
    obtain ⟨j, rfl⟩ := exists_t_eq (V := V) (mem_bar_of_mem_disc harr m.2.1 hw ((V m).P_sub
      (discBd_subset _ hb')))
    exact ⟨j, Subtype.ext he⟩
  obtain ⟨a, rfl⟩ := hnd _ h₁
  obtain ⟨b, rfl⟩ := hnd _ h₂
  obtain ⟨c, rfl⟩ := hnd _ h₃
  obtain ⟨d, rfl⟩ := hnd _ h₄
  have hinj : Function.Injective nd := fun x y he => by
    have := congrArg Subtype.val he
    have h3 := harr.1.injOn_pts (bar_sub_verts m.2.1 (t_mem_bar m x)) (bar_sub_verts m.2.1
      (t_mem_bar m y)) this
    exact (V m).dec.injective_t h3
  let I : Set (Fin (V m).k) := {j | v ∈ bt V (nd j).1 ∨ (nd j ∈ NT V ∧ v = nv Seg ν (nd j).1)}
  have hmem : ∀ j ∈ I, v ∈ V((V m).X j) := by
    rintro j (⟨m', i, j', h1, -, -, h4, -⟩ | ⟨-, h1⟩)
    · obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.mp (node_unique harr h1)
      obtain rfl := eq_of_heq hi
      exact h4
    · have : v = (V m).t j := by rw [h1]; exact nv_t harr m j
      rw [this]
      exact (V m).dec.mem_vertexSet j
  have hI : ∀ x y z, x < y → y < z → x ∈ I → z ∈ I → y ∈ I := fun x y z hxy hyz hx hz => by
    have h0 : x.1 < y.1 := hxy
    let y' : Fin (V m).k := ⟨y.1 - 1, by omega⟩
    have hv' := (V m).mem_between (a := x) (b := y') (c := z)
      (Fin.le_def.mpr (by simp only [y']; omega))
      (Fin.le_def.mpr (by have : y.1 < z.1 := hyz; simp only [y']; omega))
      (hmem x hx) (hmem z hz)
    have hvy := (V m).mem_between (a := x) (b := y) (c := z) hxy.le hyz.le (hmem x hx) (hmem z hz)
    by_cases he : v = (V m).t y
    · exact Or.inr ⟨pt_mem_Nd m.2.1 (t_mem_bar m y), by rw [he]; exact (nv_t harr m y).symm⟩
    · exact Or.inl ⟨m, y, y', rfl, by simp only [y']; omega, hv', hvy, he⟩
  have hF : ∀ i, IsPreconnected (Subtype.val ⁻¹' (V m).F i : Set ↥(Cut V)) ∧ (Subtype.val ⁻¹'
    (V m).F i : Set ↥(Cut V)) ⊆ Θ ∧ nd i ∈ (Subtype.val ⁻¹' (V m).F i : Set ↥(Cut V)) ∧
      nd ((V m).nx i) ∈ (Subtype.val ⁻¹' (V m).F i : Set ↥(Cut V)) ∧ ∀ j, nd j ∈ (Subtype.val ⁻¹'
        (V m).F i : Set ↥(Cut V)) → j = i ∨ j = (V m).nx i := fun i => by
    obtain ⟨u, w, -, -, -, -, -, hl⟩ := lune_ends (V := V) harr hS hfin m i
    refine ⟨IsLineWithEnds.isPreconnected hl, ?_, ((V m).F_line i).left_mem,
      ((V m).F_line i).right_mem, fun j hj => ?_⟩
    · rw [hΘ]
      intro x hx
      change x.1 ∈ discBd (V m).P
      rw [(V m).bd_P]
      exact mem_iUnion.2 ⟨i, hx⟩
    · apply ((V m).node_mem i j).mp
      have h3 : ν ((V m).t j) ∈ (V m).F i := hj
      rw [← (V m).L_inter i] at h3
      exact h3.1
  exact mem_of_inOrderOn hinj (V m).hnx hF hI ho hv₁ hv₃

omit harr hS hfin [Nonempty α] [TopologicalSpace S] [T2Space S] in
theorem Portrayal.warp_le_of_cellWarpLE {H : Hypergraph α β} (π : Portrayal H) {p : ℕ} (hp : 1 ≤ p)
  (h : ∀ c ∈ π.Γ.C, π.CellWarpLE c p) : π.warp ≤ p := by
  classical
  unfold Portrayal.warp
  split_ifs
  · refine max_le hp (csSup_le' ?_)
    rintro _ ⟨Θ, -, rfl⟩
    refine csSup_le' ?_
    rintro _ ⟨c, hc, -, rfl⟩
    exact Nat.sInf_le (h c hc)
  · exact hp

omit harr hS hfin

/-- **The portrayal of a proper arrangement.** A segregation of type `(ρ, κ)` with a proper
arrangement in a connected closed surface gives a portrayal of the graph in the surface with
the polygons removed. This is the construction in the proof of XVII (13.1), pages 202-204. -/
theorem exists_portrayal_of_arrangement [ConnectedSpace S] (hS : IsClosedSurface S)
  (hV : V(G).Finite) (hE : E(G).Finite) {κ : ℕ} (hseg : GM16.IsSegregationOfType G ρ κ Seg)
    (harr : IsProperArrangement Seg D ν) :
    ∃ π : Portrayal (Hypergraph.ofGraph G hV hE), (∃ j : π.S → S, IsEmbedding j) ∧ π.warp ≤ ρ + 1 ∧
      (cuffs π.S).encard ≤ κ ∧
      ∀ c ∈ π.Γ.C, ∃ s ∈ Seg, SubhypergraphInGraph (π.cellGraph c) s.G := by
  classical
  have hsg := hseg.isSegregation
  have hfin := hsg.finite
  have hex : ∀ m : Maj Seg, Nonempty (VortexCut m.1 (D m.1) ν ρ) := fun m
    => exists_vortexCut hS harr m.2.1 m.2.2 (hseg.is_rho_vortex m.2.1 m.2.2)
  let V : ∀ m : Maj Seg, VortexCut m.1 (D m.1) ν ρ := fun m => Classical.choice (hex m)
  obtain ⟨hcl, hsurf, hbd, hcon, hcuffs⟩ := cut_surface (V := V) harr hS hfin
  obtain ⟨Γ, hU, hN, hC, hct⟩ := exists_cut_painting (V := V) harr hS hfin
  have : T2Space ↥(Cut V) := hsurf.2.1
  let cl : Idx V → Set ↥(Cut V) := fun i => dT V i \ NT V
  have hcC : ∀ i, cl i ∈ Γ.C := fun i => hC ▸ mem_range_self i
  have hcinj : Function.Injective cl := fun i j he => by
    by_contra hij
    obtain ⟨x, hx⟩ := arcComponentsIn_nonempty (hcC i)
    have h1 : x ∈ dT V j := (he ▸ hx : x ∈ cl j).1
    exact hx.2 (inter_sub_Nd harr hij ⟨hx.1, h1⟩)
  let cg : Set ↥(Cut V) → Hypergraph α β := Function.extend cl (gr V) (fun _ => ⊥)
  have hcg : ∀ i, cg (cl i) = gr V i := fun i => hcinj.extend_apply _ _ i
  have htl : ∀ i, tilde (cl i) = NT V ∩ dT V i := fun i => (hct i).2
  have hbL : ∀ a, ¬ (cl (.inl a) ∩ bd ↥(Cut V)).Nonempty := by
    rintro a ⟨x, hx, hb⟩
    rw [hbd] at hb
    exact hx.2 (mnr_inter_bd harr a ⟨hx.1, hb⟩)
  have hbR : ∀ m a, (cl (.inr ⟨m, a⟩) ∩ bd ↥(Cut V)).Nonempty := by
    intro m a
    obtain ⟨u, w, hne, -, -, h4, h5, f, h0, h1⟩ := lune_ends (V := V) harr hS hfin m a
    let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
    have ht0 : (f t).1 ≠ u := fun he => by
      have h3 : f t = f 0 := Subtype.ext (he.trans h0.symm)
      have := congrArg Subtype.val (f.injective h3)
      norm_num [t] at this
    have ht1 : (f t).1 ≠ w := fun he => by
      have h3 : f t = f 1 := Subtype.ext (he.trans h1.symm)
      have := congrArg Subtype.val (f.injective h3)
      norm_num [t] at this
    have hm : (f t).1 ∈ dT V (.inr ⟨m, a⟩) ∩ bd ↥(Cut V) := by
      rw [h5]
      exact (f t).2
    refine ⟨(f t).1, ⟨hm.1, fun hn => ?_⟩, hm.2⟩
    have : (f t).1 ∈ NT V ∩ dT V (.inr ⟨m, a⟩) := ⟨hn, hm.1⟩
    rw [h4] at this
    rcases this with h | h
    · exact ht0 h
    · exact ht1 h
  have hNmem : ∀ n : ↥(Cut V), n ∈ NT V → n.1 ∈ Nd Seg ν := fun _ h => h
  have hcuffm : ∀ Θ ∈ cuffs ↥(Cut V), ∃ m, Θ = Subtype.val ⁻¹' discBd (V m).P := fun Θ hΘ => by
    rw [hcuffs] at hΘ
    obtain ⟨m, rfl⟩ := hΘ
    exact ⟨m, rfl⟩
  have hbtV : ∀ x, bt V x ⊆ V(G) := fun x v hv => by
    obtain ⟨m, -, -, hg⟩ := bt_mem_graph hv
    exact (hsg.le _ m.2.1).vertexSet_mono hg
  let π : Portrayal (Hypergraph.ofGraph G hV hE) :=
    { S := ↥(Cut V)
      isSurface := hsurf
      connected := hcon
      Γ := Γ
      cellGraph := cg
      borderSet := fun x => bt V x.1
      domγ := NT V
      nodeVertex := fun x => nv Seg ν x.1
      cellGraph_le := fun c hc => by
        obtain ⟨i, rfl⟩ := hC ▸ hc
        change cg (cl i) ≤ _
        rw [hcg]
        exact gr_le hsg hV hE i
      borderSet_subset := fun n _ => hbtV n.1
      domγ_subset := hN.ge
      nodeVertex_mem := fun n hn => by
        obtain ⟨w, hw, he⟩ := hNmem n hn
        change nv Seg ν n.1 ∈ V(G)
        rw [← he, nv_eq harr hw]
        obtain ⟨s, hs, hv'⟩ : ∃ s ∈ Seg, w ∈ s.Ω.bar := by simpa [segregationVertices] using hw
        exact (hsg.le _ hs).vertexSet_mono (s.bar_subset hv')
      nodeVertex_injOn := fun x hx y hy he => by
        obtain ⟨w, hw, he₁⟩ := hNmem x hx
        obtain ⟨w', hw', he₂⟩ := hNmem y hy
        have h' : nv Seg ν x.1 = nv Seg ν y.1 := he
        rw [← he₁, ← he₂, nv_eq harr hw, nv_eq harr hw'] at h'
        exact Subtype.ext (by rw [← he₁, ← he₂, h'])
      p1_vertex := fun v hv => by
        obtain ⟨i, hi⟩ := cover_vertex (V := V) hsg hv
        exact ⟨cl i, hcC i, by rw [hcg]; exact hi⟩
      p1_edge := fun e he => by
        obtain ⟨i, hi⟩ := cover_edge (V := V) hsg he
        exact ⟨cl i, hcC i, by rw [hcg]; exact hi⟩
      p1_disjoint := fun c hc c' hc' hne => by
        obtain ⟨i, rfl⟩ := hC ▸ hc
        obtain ⟨j, rfl⟩ := hC ▸ hc'
        change Disjoint (cg (cl i)).edgeSet (cg (cl j)).edgeSet
        rw [hcg, hcg]
        exact gr_edge_disjoint hsg (fun h => hne (h ▸ rfl))
      p2 := fun c hc n hn => by
        obtain ⟨i, rfl⟩ := hC ▸ hc
        change nv Seg ν n.1 ∈ (cg (cl i)).vertexSet
        rw [hcg]
        have h1 : n ∈ NT V ∩ dT V i := htl i ▸ hn.1
        exact nv_mem_gr harr i h1
      p3_notMem := fun n hn => nv_notMem_bt harr hn.1
      p3_subset := fun c hc hb n hn => by
        obtain ⟨i, rfl⟩ := hC ▸ hc
        rcases i with a | ⟨m, a⟩
        · exact absurd hb (hbL a)
        · change bt V n.1 ⊆ (cg (cl _)).vertexSet
          rw [hcg]
          have h1 : n ∈ NT V ∩ dT V (.inr ⟨m, a⟩) := htl _ ▸ hn
          exact bt_sub_gr harr h1
      p4_disjoint := fun Θ₁ hΘ₁ Θ₂ hΘ₂ hne n₁ hn₁ n₂ hn₂ => by
        obtain ⟨m₁, rfl⟩ := hcuffm Θ₁ hΘ₁
        obtain ⟨m₂, rfl⟩ := hcuffm Θ₂ hΘ₂
        have hm : m₁ ≠ m₂ := fun h => hne (h ▸ rfl)
        exact bt_disjoint harr hsg hm ((V m₁).P_sub (discBd_subset _ hn₁.2)) ((V m₂).P_sub
          (discBd_subset _ hn₂.2))
      p4_notMem := fun Θ hΘ n₁ hn₁ n₂ hn₂ hoff => by
        obtain ⟨m, rfl⟩ := hcuffm Θ hΘ
        exact nv_notMem_bt_of_off harr hsg ((V m).P_sub (discBd_subset _ hn₁.2)) hn₂ hoff
      p5 := fun c hc hb v hv ho => by
        obtain ⟨i, rfl⟩ := hC ▸ hc
        rcases i with a | ⟨m, a⟩
        · obtain ⟨c', hc', hne, hvc⟩ := ho
          obtain ⟨j, rfl⟩ := hC ▸ hc'
          have hv₁ : v ∈ (gr V (.inl a)).vertexSet := hcg (.inl a) ▸ hv
          have hv₂ : v ∈ (gr V j).vertexSet := hcg j ▸ hvc
          obtain ⟨h1, h2⟩ := p5_aux harr hsg a hv₁ (fun h => hne (h ▸ rfl)) hv₂
          have hmem : ν v ∈ Cut V := Ds_sub_Cut harr (.inl a) h1.2
          refine ⟨⟨ν v, hmem⟩, ⟨?_, h1.1⟩, h2⟩
          rw [htl]
          exact ⟨h1.1, h1.2⟩
        · exact absurd (hbR m a) hb
      p6 := fun c hc hb v hv ho => by
        obtain ⟨i, rfl⟩ := hC ▸ hc
        rcases i with a | ⟨m, a⟩
        · exact absurd hb (hbL a)
        · obtain ⟨c', hc', hne, hvc⟩ := ho
          obtain ⟨j, rfl⟩ := hC ▸ hc'
          have hv₁ : v ∈ (gr V (.inr ⟨m, a⟩)).vertexSet := hcg _ ▸ hv
          have hv₂ : v ∈ (gr V j).vertexSet := hcg j ▸ hvc
          obtain ⟨n, hn, h1⟩ := p6_aux harr hsg hv₁ (fun h => hne (h ▸ rfl)) hv₂
          have hmem : n ∈ Cut V := Ds_sub_Cut harr (.inr ⟨m, a⟩) hn.2
          refine ⟨⟨n, hmem⟩, ?_, h1⟩
          rw [htl]
          exact hn
      p7 := fun Θ hΘ n₁ hn₁ n₂ hn₂ n₃ hn₃ n₄ hn₄ ho v hv₁ hv₃ => by
        obtain ⟨m, rfl⟩ := hcuffm Θ hΘ
        rw [hN] at hn₁ hn₂ hn₃ hn₄
        exact p7_aux harr hS hfin m rfl hn₁ hn₂ hn₃ hn₄ ho hv₁ hv₃ }
  refine ⟨π, ⟨Subtype.val, IsEmbedding.subtypeVal⟩, ?_, ?_, ?_⟩
  · refine Portrayal.warp_le_of_cellWarpLE π (by omega) fun c _ n₁ _ n₂ _ _ => ?_
    have hle : ∀ n : ↥(Cut V), (bt V n.1).ncard ≤ ρ := fun n => ncard_bt_le harr n.1
    have hplus : ∀ n : ↥(Cut V), (π.borderPlus n).ncard ≤ ρ + 1 := fun n => by
      have hsub : π.borderPlus n ⊆ insert (nv Seg ν n.1) (bt V n.1) := by
        rintro v (hv | ⟨-, hv⟩)
        · exact Or.inr hv
        · exact Or.inl hv
      have hfinb : (bt V n.1).Finite := hV.subset (hbtV n.1)
      exact (Set.ncard_le_ncard hsub (hfinb.insert _)).trans ((Set.ncard_insert_le _ _).trans
        (by have := hle n; omega))
    refine ⟨(hle n₁).trans (by omega), (hle n₂).trans (by omega), fun h => ?_⟩
    have := hplus n₁
    omega
  · have := finite_Maj hfin
    change (cuffs ↥(Cut V)).encard ≤ κ
    rw [hcuffs, ← image_univ]
    refine (Set.encard_image_le _ _).trans ?_
    rw [Set.encard_univ, ENat.card_coe_set_eq]
    have hf : {s ∈ Seg | 3 < s.Ω.bar.ncard}.Finite := hfin.subset (sep_subset _ _)
    rw [← hf.cast_ncard_eq]
    exact_mod_cast hseg.vortex_count_le
  · intro c hc
    obtain ⟨i, rfl⟩ := hC ▸ hc
    refine ⟨soc V i, soc_mem V i, ?_⟩
    change SubhypergraphInGraph (cg (cl i)) _
    rw [hcg]
    exact ⟨gr_vertex_sub i, gr_edge_sub i⟩

end GraphMinor.GM17
