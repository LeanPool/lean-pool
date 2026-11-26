/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.RootedCut
import LeanPool.GraphMinor.GM06.Section3Dual
import LeanPool.GraphMinor.GM19.Section6a
import LeanPool.GraphMinor.GM07.ArcPlace

/-!
# Step 2 of (9.1)

See page 243. We cut along edges `e₁, ..., e_r` of `G`, one for each edge `f_i` of `H`, by (7.4).
The paper then takes "a homeomorphism of
$\Sigma$ which fixes every point of $bd(\Sigma)$ and maps the middle third of $f_i$ onto the whole
of $e_i$" (`exists_line_family_placement`), and
replaces `H` by its image. "Let $H' = (U(H) - Y, V(H) \cup Z)$ where $Y = e_1 \cup \dots \cup e_r$
and $Z$ is the set of all ends of
$e_1, \dots, e_r$." Before the homeomorphism, this is the drawing obtained from `H` by removing the
open middle third of each edge
(`exists_split_middle`), which is a forest. Its image under the homeomorphism meets each `ē_i` in
the two ends of `e_i` only, so it lifts to the
cut surface `Σ_r`.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The first end of the middle third of the unit interval. -/
@[expose] noncomputable def third₁ : I := ⟨1 / 3, by norm_num, by norm_num⟩
/-- The second end of the middle third of the unit interval. -/
@[expose] noncomputable def third₂ : I := ⟨2 / 3, by norm_num, by norm_num⟩

theorem third₁_pos : (0 : I) < third₁ := by
  rw [← Subtype.coe_lt_coe]
  norm_num [third₁]

theorem third_lt : third₁ < third₂ := by
  rw [← Subtype.coe_lt_coe]
  norm_num [third₁, third₂]

theorem third₂_lt : third₂ < 1 := by
  rw [← Subtype.coe_lt_coe]
  norm_num [third₂]

/-- The part of an edge between two inner parameters is a line. -/
theorem EdgeParam.middle_line {H : Drawing S} {f : Set S} {γ : I → S}
  (hγ : EdgeParam H f γ) {t t' : I} (h0 : 0 < t) (htt : t < t')
    (h1 : t' < 1) : IsLineWithEnds (γ '' Icc t t') (γ t) (γ t') := by
  have hIcc : Icc t t' ⊆ Ioo (0 : I) 1 := fun y hy => ⟨h0.trans_le hy.1, hy.2.trans_lt h1⟩
  have hinj : InjOn γ (Icc t t') := hγ.inj.mono hIcc
  have hmaps : ∀ z, lerpI t t' z ∈ Icc t t' := fun z => by
    rw [← range_lerpI htt.le]
    exact mem_range_self z
  have ha : IsArcMap (subArc γ t t') := ⟨hγ.cont.comp (continuous_lerpI _ _), fun x y he
    => lerpI_injective htt.ne (hinj (hmaps x) (hmaps y) he)⟩
  have hL := isLineWithEnds_range_of_arc ha
  rwa [range_subArc _ htt.le, subArc_zero, subArc_one] at hL

omit [T2Space S] in
/-- The middle third of an edge lies in the edge. -/
theorem EdgeParam.middle_subset {H : Drawing S} {f : Set S} {γ : I → S}
  (hγ : EdgeParam H f γ) : γ '' Icc third₁ third₂ ⊆ f := by
  rintro _ ⟨y, hy, rfl⟩
  exact hγ.mem_edge (third₁_pos.trans_le hy.1) (hy.2.trans_lt third₂_lt)

/-- Removing the middle third of each edge of `H`. The marks of the split are the ends of the middle
thirds, and the new drawing meets each
middle third in its two ends only. -/
theorem exists_split_middle [Nonempty S] (Hd : SurfaceDigraph S) :
    ∃ (γ : Set S → I → S) (β : Set S × Bool → I → S) (τ : Set S × Bool → I) (hs : IsSplit Hd.G β τ),
      (∀ f ∈ Hd.G.E, EdgeParam Hd.G f (γ f) ∧ γ f 0 = Hd.plus f ∧ γ f 1 = Hd.minus f) ∧
      (∀ f ∈ Hd.G.E, β (f, false) 0 = Hd.plus f ∧ β (f, true) 0 = Hd.minus f) ∧
      (∀ f ∈ Hd.G.E, β (f, false) (τ (f, false)) = γ f third₁ ∧ β (f, true) (τ (f, true))
        = γ f third₂) ∧
      ∀ f ∈ Hd.G.E, hs.drawing.U ∩ γ f '' Icc third₁ third₂ = {γ f third₁, γ f third₂} := by
  classical
  set H := Hd.G with hHd
  have hor : ∀ f, f ∈ H.E → ∃ γ : I → S, EdgeParam H f γ ∧ γ 0 = Hd.plus f ∧ γ 1 = Hd.minus f
    := fun f hf =>
    exists_oriented_param hf (Hd.ends_eq f hf)
  choose! γ hγ hγ0 hγ1 using hor
  have h0 := third₁_pos
  have h1 := third_lt
  have h2 := third₂_lt
  let β : Set S × Bool → I → S := fun q => cond q.2 (γ q.1 ∘ σ) (γ q.1)
  let τ : Set S × Bool → I := fun q => cond q.2 (σ third₂) third₁
  have hsym1 : ∀ {u : I}, u < 1 → 0 < σ u := fun {u} hu => by
    rw [← unitInterval.symm_one, unitInterval.symm_lt_symm]
    exact hu
  have hsym0 : ∀ {u : I}, 0 < u → σ u < 1 := fun {u} hu => by
    rw [← unitInterval.symm_zero, unitInterval.symm_lt_symm]
    exact hu
  have hrev : ∀ {u v : I}, v ≤ σ u → u ≤ σ v := fun {u v} huv => by
    have := unitInterval.symm_le_symm.mpr huv
    rwa [unitInterval.symm_symm] at this
  have hs : IsSplit H β τ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨f, b⟩ hf
      cases b
      · exact hγ f hf
      · exact (hγ f hf).rev
    · rintro ⟨f, b⟩ hf
      cases b
      · exact h0
      · exact hsym1 h2
    · rintro ⟨f, b⟩ hf
      cases b
      · exact h1.trans h2
      · exact hsym0 (h0.trans h1)
    · intro f hf
      rw [disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ ⟨u, hu, he⟩
      change γ f (σ u) = γ f y at he
      have hu1 : σ u ∈ Ioo (0 : I) 1 := ⟨hsym1 (hu.2.trans_lt (hsym0 (h0.trans h1))), hsym0 hu.1⟩
      have hy1 : y ∈ Ioo (0 : I) 1 := ⟨hy.1, (show y ≤ third₁ from hy.2).trans_lt (h1.trans h2)⟩
      have heq := (hγ f hf).inj hu1 hy1 he
      have h9 : third₂ ≤ σ u := hrev hu.2
      have h10 : y ≤ third₁ := hy.2
      exact absurd (h1.trans_le (h9.trans (heq.le.trans h10))) (lt_irrefl _)
  have hm₂ : ∀ f, β (f, true) (τ (f, true)) = γ f third₂ := fun f => by
    change γ f (σ (σ third₂)) = _
    rw [unitInterval.symm_symm]
  refine ⟨γ, β, τ, hs, fun f hf => ⟨hγ f hf, hγ0 f hf, hγ1 f hf⟩, fun f hf => ⟨hγ0 f hf, ?_⟩,
    fun f _ => ⟨rfl, hm₂ f⟩, fun f hf => ?_⟩
  · change γ f (σ 0) = _
    rw [unitInterval.symm_zero, hγ1 f hf]
  · have hγf := hγ f hf
    have hU₃ : hs.drawing.U ⊆ H.U := by
      refine union_subset H.V_subset_U (iUnion₂_subset fun q hq => ?_)
      rintro _ ⟨y, -, rfl⟩
      exact (hs.param q hq).subset_U hq y
    have hqf : (f, false) ∈ halves H := hf
    have hqt : (f, true) ∈ halves H := hf
    apply Subset.antisymm
    · rintro x ⟨hxU, y, hy, rfl⟩
      by_cases hyt : y = third₁
      · left
        rw [hyt]
      by_cases hyt' : y = third₂
      · right
        rw [hyt']
        rfl
      exfalso
      have ht : third₁ < y := lt_of_le_of_ne hy.1 (Ne.symm hyt)
      have ht' : y < third₂ := lt_of_le_of_ne hy.2 hyt'
      have hy0 : 0 < y := h0.trans ht
      have hy1 : y < 1 := ht'.trans h2
      have hyI : y ∈ Ioo (0 : I) 1 := ⟨hy0, hy1⟩
      have hedge := hγf.mem_edge hy0 hy1
      rcases hxU with hV | hxU
      · exact hγf.not_V hf hy0 hy1 hV
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hxU
      rcases mem_closed_half hxq with h9 | h9
      · exact hγf.not_V hf hy0 hy1 (h9 ▸ (hs.param q hq).mem0)
      have hsame : q.1 = f := by
        by_contra hne
        exact disjoint_left.mp (GraphMinor.GM06.disjoint_edges_of_ne H hq hf hne)
          (hs.halfRest_subset hq h9) hedge
      obtain ⟨g, b⟩ := q
      change g = f at hsame
      subst hsame
      cases b
      · obtain ⟨u, hu, he⟩ := h9
        have hu' : u ∈ Ioo (0 : I) 1 := ⟨hu.1, (show u ≤ third₁ from hu.2).trans_lt (h1.trans h2)⟩
        have := hγf.inj hu' hyI he
        exact absurd (this ▸ hu.2 : y ≤ third₁) (not_le.mpr ht)
      · obtain ⟨u, hu, he⟩ := h9
        change γ g (σ u) = γ g y at he
        have hu' : σ u ∈ Ioo (0 : I) 1 := ⟨hsym1 (hu.2.trans_lt (hsym0 (h0.trans h1))), hsym0 hu.1⟩
        have := hγf.inj hu' hyI he
        have h10 : third₂ ≤ σ u := hrev hu.2
        exact absurd (this ▸ h10) (not_le.mpr ht')
    · rintro x (rfl | hx)
      · exact ⟨hs.drawing.V_subset_U (.inr ⟨(f, false), hqf, rfl⟩), third₁, ⟨le_rfl, h1.le⟩, rfl⟩
      · rw [mem_singleton_iff] at hx
        subst hx
        refine ⟨?_, third₂, ⟨h1.le, le_rfl⟩, rfl⟩
        rw [← hm₂]
        exact hs.drawing.V_subset_U (.inr ⟨(f, true), hqt, rfl⟩)

omit [T2Space S] in
/-- The closure of an edge that is not a loop is a line between its two ends. -/
theorem isLineWithEnds_closure_of_ends (G : Drawing S) {e : Set S} (he : e ∈ G.E) (hloop :
  (tilde e).ncard = 2) {p m : S}
    (hpm : ({p, m} : Set S) = tilde e) : IsLineWithEnds (closure e) p m := by
  rw [← hpm] at hloop
  rcases G.edge_cond e he with ⟨u, v, -, hcap, hL⟩ | ⟨u, hcap, -⟩
  · have h1 : ({p, m} : Set S) = {u, v} := by
      rw [hpm, GraphMinor.GM19.tilde_eq_inter_V G he, hcap]
    have h6 : p ∈ ({u, v} : Set S) := by rw [← h1]; simp
    have h7 : m ∈ ({u, v} : Set S) := by rw [← h1]; simp
    have h8 : u ∈ ({p, m} : Set S) := by rw [h1]; simp
    have h9 : v ∈ ({p, m} : Set S) := by rw [h1]; simp
    simp only [mem_insert_iff, mem_singleton_iff] at h6 h7 h8 h9
    by_cases hc : p = u ∧ m = v
    · rw [hc.1, hc.2]
      exact hL
    · have h10 : p = v ∧ m = u := by grind
      rw [h10.1, h10.2]
      exact hL.symm
  · rw [hpm, GraphMinor.GM19.tilde_eq_inter_V G he, hcap] at hloop
    simp at hloop

private theorem matched_forest_meets_cut_at_ends
    {S : Type u}
    [TopologicalSpace S]
    (Hd : SurfaceDigraph S)
    (Gd : SurfaceDigraph S)
    (γ : Set S → ↑I → S)
    (β : Set S × Bool → ↑I → S)
    (τ : Set S × Bool → ↑I)
    (hmk : ∀ f ∈ Hd.G.E, β (f, false) (τ (f, false)) = γ f third₁ ∧ β (f, true) (τ (f, true)) = γ
      f third₂)
    (ε : Set S → Set S)
    (e : S ≃ₜ S)
    (mk₁ : Set S → S)
    (hmk₁ : mk₁ = fun f => β (f, false) (τ (f, false)))
    (mk₂ : Set S → S)
    (hmk₂ : mk₂ = fun f => β (f, true) (τ (f, true)))
    (hplace : ∀ f ∈ Hd.G.E, ⇑e '' γ f '' Icc third₁ third₂ = closure (ε f) ∧ e (mk₁ f) = Gd.plus
      (ε f) ∧ e (mk₂ f) = Gd.minus (ε f))
    (H₃ : Drawing S)
    (hmid : ∀ f ∈ Hd.G.E, H₃.U ∩ γ f '' Icc third₁ third₂ = {γ f third₁, γ f third₂}) :
    let Hc : Drawing S := mapDrawingHomeo e H₃
    ∀ f ∈ Hd.G.E, ∀ x ∈ Hc.U, x ∈ closure (ε f) → x = Gd.plus (ε f) ∨ x = Gd.minus (ε f) := by
  intro Hc
  rintro f hf _ ⟨y, hy, rfl⟩ hx
  rw [← (hplace f hf).1] at hx
  obtain ⟨y', hy', he⟩ := hx
  have hyy := e.injective he
  subst hyy
  have h1 : y' ∈ H₃.U ∩ γ f '' Icc third₁ third₂ := ⟨hy, hy'⟩
  rw [hmid f hf] at h1
  rcases h1 with rfl | h1
  · left
    rw [← (hplace f hf).2.1, hmk₁]
    simp only
    rw [(hmk f hf).1]
  · rw [mem_singleton_iff] at h1
    subst h1
    right
    rw [← (hplace f hf).2.2, hmk₂]
    simp only
    rw [(hmk f hf).2]

private theorem matched_forest_avoids_cut_edges
    {S : Type u}
    [TopologicalSpace S]
    (Hd : SurfaceDigraph S)
    (Gd : SurfaceDigraph S)
    (S_r : Type u)
    [TopologicalSpace S_r]
    (θ : S_r → S)
    (G_r : Drawing S_r)
    (𝓔 : Set (Set S))
    (hmc : IsMultiCut Gd.G 𝓔 θ G_r)
    (ε : Set S → Set S)
    (hεs : ∀ e' ∈ 𝓔, ∃ f ∈ Hd.G.E, ε f = e')
    (Hc : Drawing S)
    (hCap : ∀ f ∈ Hd.G.E, ∀ x ∈ Hc.U, x ∈ closure (ε f) → x = Gd.plus (ε f) ∨ x = Gd.minus (ε f)) :
    ∀ x ∈ Hc.U, x ∉ ⋃₀ 𝓔 := by
  rintro x hx ⟨e', he', hxe⟩
  obtain ⟨f, hf, rfl⟩ := hεs e' he'
  have hnV : x ∉ Gd.G.V := ((hmc.sub he').2.1 hxe).2
  rcases hCap f hf x hx (subset_closure hxe) with rfl | rfl
  · exact hnV (Gd.plus_mem _ (hmc.sub he'))
  · exact hnV (Gd.minus_mem _ (hmc.sub he'))

private theorem matching_preserves_original_boundary_vertices
    {S : Type u}
    [TopologicalSpace S]
    [T2Space S]
    (Hd : SurfaceDigraph S)
    (hH : Hd.IsProper)
    (β : Set S × Bool → ↑I → S)
    (τ : Set S × Bool → ↑I)
    (hsp : IsSplit Hd.G β τ)
    (e : S ≃ₜ S)
    (hebd : ∀ x ∈ bd S, e x = x)
    (hesymm : ∀ x ∈ bd S, e.symm x = x) :
    let H₃ : Drawing S := hsp.drawing
    let Hc : Drawing S := mapDrawingHomeo e H₃
    ∀ x ∈ bd S, x ∈ Hc.V ↔ x ∈ Hd.G.V := by
  intro H₃ Hc x hx
  have hxU : x ∉ H₃.V \ Hd.G.V := by
    rintro ⟨h1 | ⟨q, hq, rfl⟩, h2⟩
    · exact h2 h1
    · exact h2 (hH ⟨hx, (hsp.param q hq).subset_U hq _⟩)
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : y = e y := by
      have h := hesymm _ hx
      rwa [e.symm_apply_apply] at h
    rw [← this] at hxU ⊢
    by_contra hn
    exact hxU ⟨hy, hn⟩
  · intro h1
    exact ⟨x, .inl h1, hebd x hx⟩

private theorem matching_preserves_cut_edge_vertices
    {S : Type u}
    [TopologicalSpace S]
    (Hd : SurfaceDigraph S)
    (Gd : SurfaceDigraph S)
    (S_r : Type u)
    [TopologicalSpace S_r]
    (θ : S_r → S)
    (G_r : Drawing S_r)
    (𝓔 : Set (Set S))
    (hmc : IsMultiCut Gd.G 𝓔 θ G_r)
    (ε : Set S → Set S)
    (hεs : ∀ e' ∈ 𝓔, ∃ f ∈ Hd.G.E, ε f = e')
    (Hc : Drawing S)
    (hpV : ∀ f ∈ Hd.G.E, Gd.plus (ε f) ∈ Hc.V)
    (hmV : ∀ f ∈ Hd.G.E, Gd.minus (ε f) ∈ Hc.V)
    (hCap : ∀ f ∈ Hd.G.E, ∀ x ∈ Hc.U, x ∈ closure (ε f) → x = Gd.plus (ε f) ∨ x = Gd.minus (ε f)) :
    ∀ e' ∈ 𝓔, ∀ x ∈ closure e', x ∈ Hc.V ↔ x ∈ Gd.G.V := by
  intro e' he' x hx
  obtain ⟨f, hf, rfl⟩ := hεs e' he'
  constructor
  · intro h1
    rcases hCap f hf x (Hc.V_subset_U h1) hx with rfl | rfl
    · exact Gd.plus_mem _ (hmc.sub he')
    · exact Gd.minus_mem _ (hmc.sub he')
  · intro h1
    have h2 : x ∈ tilde (ε f) := by
      rw [GraphMinor.GM19.tilde_eq_inter_V Gd.G (hmc.sub he')]
      exact ⟨hx, h1⟩
    rw [← Gd.ends_eq _ (hmc.sub he')] at h2
    rcases h2 with rfl | h2
    · exact hpV f hf
    · rw [mem_singleton_iff] at h2
      subst h2
      exact hmV f hf

private theorem cut_boundary_projects_to_boundary_or_cut_edge
    {S : Type u}
    [TopologicalSpace S]
    (Gd : SurfaceDigraph S)
    (S_r : Type u)
    [TopologicalSpace S_r]
    (θ : S_r → S)
    (G_r : Drawing S_r)
    (𝓔 : Set (Set S))
    (hmc : IsMultiCut Gd.G 𝓔 θ G_r)
    (x : S_r)
    (hx : x ∈ bd S_r) :
    θ x ∈ bd S ∨ ∃ e' ∈ 𝓔, θ x ∈ closure e' := by
  rw [hmc.bd_eq] at hx
  rcases hx with h1 | h1
  · exact .inl h1
  · obtain ⟨e', he', h2⟩ := mem_iUnion₂.mp h1
    exact .inr ⟨e', he', h2⟩

private theorem forest_vertices_have_boundary_representatives
    {S : Type u}
    [TopologicalSpace S]
    (Hd : SurfaceDigraph S)
    (Gd : SurfaceDigraph S)
    (S_r : Type u)
    [TopologicalSpace S_r]
    (θ : S_r → S)
    (G_r : Drawing S_r)
    (𝓔 : Set (Set S))
    (hmc : IsMultiCut Gd.G 𝓔 θ G_r)
    (hs : Surjective θ)
    (β : Set S × Bool → ↑I → S)
    (τ : Set S × Bool → ↑I)
    (hsp : IsSplit Hd.G β τ)
    (e : S ≃ₜ S)
    (hesymm : ∀ x ∈ bd S, e.symm x = x)
    (Hc : Drawing S)
    (hbdV : ∀ x ∈ bd S, x ∈ Hc.V ↔ x ∈ Hd.G.V)
    (Mid : Drawing S_r)
    (w : S_r → S)
    (hwb : ∀ s ∈ bd S_r, w s = e.symm (θ s))
    (hMidV : ∀ s ∈ bd S_r, θ s ∈ Hc.V → s ∈ Mid.V ∩ bd S_r)
    (zp : Set S → S_r)
    (hzp1 : ∀ f ∈ Hd.G.E, zp f ∈ Mid.V ∩ bd S_r)
    (hzp3 : ∀ f ∈ Hd.G.E, splitOwner Hd.G β τ (w (zp f)) = Hd.plus f)
    (zm : Set S → S_r)
    (hzm1 : ∀ f ∈ Hd.G.E, zm f ∈ Mid.V ∩ bd S_r)
    (hzm3 : ∀ f ∈ Hd.G.E, splitOwner Hd.G β τ (w (zm f)) = Hd.minus f)
    (hiso : ∀ v ∈ Hd.G.V \ bd S, ¬IsIsolatedVertex Hd.G v) :
    ∀ v ∈ Hd.G.V, ∃ s ∈ Mid.V ∩ bd S_r, splitOwner Hd.G β τ (w s) = v ∧ (v ∈ bd S → θ s = v) := by
  intro v hv
  by_cases hb : v ∈ bd S
  · obtain ⟨s, hs'⟩ := hs v
    have hsb : s ∈ bd S_r := by
      rw [hmc.bd_eq, mem_preimage, hs']
      exact .inl hb
    refine ⟨s, hMidV s hsb (by rw [hs', hbdV v hb]; exact hv), ?_, fun _ => hs'⟩
    rw [hwb s hsb, hs', hesymm v hb]
    exact hsp.owner_V hv
  · have hn := hiso v ⟨hv, hb⟩
    simp only [IsIsolatedVertex, not_and, not_forall, not_not] at hn
    obtain ⟨f, hf, hinc⟩ := hn hv
    have h1 : v ∈ tilde f := by
      rw [GraphMinor.GM19.tilde_eq_inter_V Hd.G hf]
      exact ⟨hinc.2.2, hv⟩
    rw [← Hd.ends_eq f hf] at h1
    rcases h1 with rfl | h1
    · exact ⟨zp f, hzp1 f hf, hzp3 f hf, fun h => absurd h hb⟩
    · rw [mem_singleton_iff] at h1
      subst h1
      exact ⟨zm f, hzm1 f hf, hzm3 f hf, fun h => absurd h hb⟩

private theorem lifted_cut_forest_is_proper
    {S : Type u}
    [TopologicalSpace S]
    (Hd : SurfaceDigraph S)
    (Gd : SurfaceDigraph S)
    (S_r : Type u)
    [TopologicalSpace S_r]
    (θ : S_r → S)
    (𝓔 : Set (Set S))
    (ε : Set S → Set S)
    (hεs : ∀ e' ∈ 𝓔, ∃ f ∈ Hd.G.E, ε f = e')
    (Hc : Drawing S)
    (hpV : ∀ f ∈ Hd.G.E, Gd.plus (ε f) ∈ Hc.V)
    (hmV : ∀ f ∈ Hd.G.E, Gd.minus (ε f) ∈ Hc.V)
    (hCap : ∀ f ∈ Hd.G.E, ∀ x ∈ Hc.U, x ∈ closure (ε f) → x = Gd.plus (ε f) ∨ x = Gd.minus (ε f))
    (H' : Drawing S_r)
    (hU : H'.U = θ ⁻¹' Hc.U)
    (hH'V : H'.V = θ ⁻¹' Hc.V)
    (hbdU : ∀ x ∈ bd S, x ∈ Hc.U → x ∈ Hc.V)
    (hbdcases : ∀ x ∈ bd S_r, θ x ∈ bd S ∨ ∃ e' ∈ 𝓔, θ x ∈ closure e') :
    H'.IsProper := by
  rintro x ⟨hx, hxU⟩
  rw [hU] at hxU
  rw [hH'V]
  rcases hbdcases x hx with h1 | ⟨e', he', h1⟩
  · exact hbdU _ h1 hxU
  · obtain ⟨f, hf, rfl⟩ := hεs e' he'
    rcases hCap f hf _ hxU h1 with h2 | h2
    · rw [mem_preimage, h2]
      exact hpV f hf
    · rw [mem_preimage, h2]
      exact hmV f hf

private theorem lifted_cut_forest_agrees_on_boundary
    {S : Type u}
    [TopologicalSpace S]
    (Gd : SurfaceDigraph S)
    (S_r : Type u)
    [TopologicalSpace S_r]
    (θ : S_r → S)
    (G_r : Drawing S_r)
    (𝓔 : Set (Set S))
    (hmc : IsMultiCut Gd.G 𝓔 θ G_r)
    (Hc : Drawing S)
    (H' : Drawing S_r)
    (hH'V : H'.V = θ ⁻¹' Hc.V)
    (hbdV' : ∀ x ∈ bd S_r, θ x ∈ Hc.V ↔ θ x ∈ Gd.G.V) :
    G_r.V ∩ bd S_r = H'.V ∩ bd S_r := by
  ext x
  refine and_congr_left fun hx => ?_
  rw [hH'V, hmc.preV]
  exact (hbdV' x hx).symm

private theorem endpoint_preimage_mem_cut_boundary {S S_r : Type u}
    [TopologicalSpace S] [TopologicalSpace S_r] {Gd : SurfaceDigraph S}
    {θ : S_r → S} {G_r : Drawing S_r} {𝓔 : Set (Set S)} (hmc : IsMultiCut Gd.G 𝓔 θ G_r)
    {edge : Set S} (he : edge ∈ 𝓔) {z : S_r}
    (hz : θ z = Gd.plus edge ∨ θ z = Gd.minus edge) : z ∈ bd S_r := by
  rw [hmc.bd_eq]
  have hEnd : θ z ∈ tilde edge := by
    rw [← Gd.ends_eq _ (hmc.sub he)]
    rcases hz with hz | hz <;> simp [hz]
  exact .inr (mem_iUnion₂.mpr ⟨edge, he, hEnd.1⟩)

/-- Step 2 of (9.1): cutting along one edge of `G` for each edge of `H` turns the question of a
minor into a question of feasibility of a forest. -/
theorem cutEdgesForestReduction {S : Type u} [TopologicalSpace S] [T1Space S] (hS : IsSurface S)
  (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (hm : Nonempty (S ≃ₜ SurfaceModel a b c)) (Hd : SurfaceDigraph S) (hH : Hd.IsProper)
      (hg0 : numInternalIsolatedVertices Hd.G = 0) (k c₀ : ℕ)
    (hk : 2 * k ≥ 4 * Hd.G.E.ncard + (Hd.G.V ∩ bd S).ncard + 2 * c + 2) (Gd : SurfaceDigraph S)
    (hbd_eq : Gd.G.V ∩ bd S = Hd.G.V ∩ bd S) (hBL : IsBoundaryLinked Gd.G)
    (halpha : alpha Gd.G ≥ 42 * k * 5 ^ Hd.G.E.ncard * vModel a b c₀ k) :
    ∃ (S_r : Type u) (_ : TopologicalSpace S_r) (_ : T1Space S_r) (G_r H' : Drawing S_r),
      IsSurface S_r ∧ Nonempty (S_r ≃ₜ SurfaceModel a b (c + Hd.G.E.ncard)) ∧ IsBoundaryLinked G_r
        ∧ 42 * k * vModel a b c₀ k ≤ alpha G_r ∧
      (G_r.V ∩ bd S_r).ncard + 2 * (c + Hd.G.E.ncard) + 2 ≤ 2 * k ∧ IsSurfaceForest H'
        ∧ G_r.V ∩ bd S_r = H'.V ∩ bd S_r ∧
      (IsGFeasible G_r H' → IsBoundaryRootedMinor Hd Gd) := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hConn : ConnectedSpace S := connectedSpace_of_model hm
  have hneS : Nonempty S := inferInstance
  have hM : IsSurface (SurfaceModel a b c) := (modelCriterion.1 a b c).1
  obtain ⟨hh⟩ := id hm
  have hk1 : 1 ≤ k := by omega
  have hv1 : 1 ≤ vModel a b c₀ k := by
    have := two_mul_k_le_vModel a b c₀ k
    omega
  have hcount : (Gd.G.V ∩ bd S).ncard + 2 * Hd.G.E.ncard ≤ 2 * k := by
    rw [hbd_eq]
    omega
  obtain ⟨S_r, tS_r, t1S_r, θ, G_r, 𝓔, hmc, hnc, hSr, hmr, hBLr, hαr, hcardr⟩
    := exists_multiCut hS h3 hm Gd.G hBL hk1 hv1 hcount halpha _ le_rfl
  have ht2r : T2Space S_r := hSr.2.1
  have hcr : CompactSpace S_r := hSr.1
  have hs := hmc.quot.surjective
  have hcθ := hmc.quot.continuous
  have hneR : Nonempty S_r := by
    obtain ⟨x⟩ := hneS
    obtain ⟨y, -⟩ := hs x
    exact ⟨y⟩
  obtain ⟨γ, β, τ, hsp, hγ, hor, hmk, hmid⟩ := exists_split_middle Hd
  -- Match the edges of `H` with the edges we cut along.
  have hfE : Finite Hd.G.E := Hd.G.finite_edges
  have hf𝓔 : Finite 𝓔 := hmc.finite
  have hcard : Nat.card Hd.G.E = Nat.card 𝓔 := by rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hnc]
  obtain ⟨eqv⟩ : Nonempty (Hd.G.E ≃ 𝓔) := Finite.card_eq.mp hcard
  let ε : Set S → Set S := fun f => if hf : f ∈ Hd.G.E then (eqv ⟨f, hf⟩).1 else ∅
  have hεv : ∀ i : Hd.G.E, ε i = (eqv i).1 := fun i => by
    change (if hf : i.1 ∈ Hd.G.E then (eqv ⟨i.1, hf⟩).1 else ∅) = _
    rw [dite_eq_left i.2]
  have hε : ∀ f ∈ Hd.G.E, ε f ∈ 𝓔 := fun f hf => by
    have := hεv ⟨f, hf⟩
    simp only at this
    rw [this]
    exact (eqv _).2
  have hεi : ∀ f ∈ Hd.G.E, ∀ f' ∈ Hd.G.E, f ≠ f' → ε f ≠ ε f' := fun f hf f' hf' hne he => by
    have h1 := hεv ⟨f, hf⟩
    have h2 := hεv ⟨f', hf'⟩
    simp only at h1 h2
    rw [h1, h2] at he
    exact hne (congrArg Subtype.val (eqv.injective (Subtype.ext he)))
  have hεs : ∀ e' ∈ 𝓔, ∃ f ∈ Hd.G.E, ε f = e' := fun e' he' => by
    obtain ⟨i, hi⟩ := eqv.surjective ⟨e', he'⟩
    refine ⟨i.1, i.2, ?_⟩
    rw [hεv, hi]
  -- The middle thirds of the edges of `H`, and the closures of the edges we cut along, are disjoint
  -- lines off the boundary.
  have hends : ∀ e' ∈ 𝓔, Gd.plus e' ≠ Gd.minus e' := fun e' he' hpe => by
    have h1 := hmc.not_loop e' he'
    rw [← Gd.ends_eq e' (hmc.sub he'), hpe] at h1
    simp at h1
  have hmidL : ∀ f ∈ Hd.G.E, IsLineWithEnds (γ f '' Icc third₁ third₂) (γ f third₁) (γ f third₂)
    := fun f hf =>
    (hγ f hf).1.middle_line third₁_pos third_lt third₂_lt
  have hmidD : Pairwise fun i j : Hd.G.E => Disjoint (γ i '' Icc third₁ third₂)
    (γ j '' Icc third₁ third₂) := fun i j hij =>
    (GraphMinor.GM06.disjoint_edges_of_ne Hd.G i.2 j.2 fun he => hij (Subtype.ext he)).mono
      (hγ i i.2).1.middle_subset (hγ j j.2).1.middle_subset
  have hmidb : ∀ f ∈ Hd.G.E, Disjoint (γ f '' Icc third₁ third₂) (bd S) := fun f hf => by
    rw [disjoint_left]
    intro x hx hb
    have h1 := hf.2.1 ((hγ f hf).1.middle_subset hx)
    exact h1.2 (hH ⟨hb, h1.1⟩)
  have hclL : ∀ e' ∈ 𝓔, IsLineWithEnds (closure e') (Gd.plus e') (Gd.minus e') := fun e' he' =>
    isLineWithEnds_closure_of_ends Gd.G (hmc.sub he') (hmc.not_loop e' he') (Gd.ends_eq e'
      (hmc.sub he'))
  -- A homeomorphism `ψ` of `Σ` fixing `bd(Σ)` maps the middle third of each `f` onto the whole of
  -- `ε f`, by `exists_line_family_placement`.
  obtain ⟨e, hebd, heA⟩ := exists_line_family_placement hS hM hh (fun i : Hd.G.E
    => γ i '' Icc third₁ third₂) (fun i => closure (ε i))
    (fun i => γ i third₁) (fun i => γ i third₂) (fun i => Gd.plus (ε i)) (fun i => Gd.minus (ε i))
      (fun i => hmidL i i.2)
    (fun i => hclL _ (hε i i.2)) hmidD (fun i j hij => hmc.disj _ (hε i i.2) _ (hε j j.2)
      (hεi i i.2 j j.2 fun he => hij (Subtype.ext he)))
    (fun i => hmidb i i.2) (fun i => disjoint_iff_inter_eq_empty.mpr
      (disjoint_iff_inter_eq_empty.mp (hmc.off_bd _ (hε i i.2))))
  set mk₁ : Set S → S := fun f => β (f, false) (τ (f, false)) with hmk₁
  set mk₂ : Set S → S := fun f => β (f, true) (τ (f, true)) with hmk₂
  have hplace : ∀ f ∈ Hd.G.E, e '' (γ f '' Icc third₁ third₂) = closure (ε f) ∧ e (mk₁ f) = Gd.plus
    (ε f) ∧ e (mk₂ f) = Gd.minus (ε f) :=
    fun f hf => by
      obtain ⟨h1, h2, h3⟩ := heA ⟨f, hf⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [hmk₁]
        simp only
        rw [(hmk f hf).1]
        exact h2
      · rw [hmk₂]
        simp only
        rw [(hmk f hf).2]
        exact h3
  have hesymm : ∀ x ∈ bd S, e.symm x = x := fun x hx => by
    rw [Homeomorph.symm_apply_eq, hebd x hx]
  set H₃ := hsp.drawing with hH₃
  set Hc := mapDrawingHomeo e H₃ with hHc
  have hmk₁V : ∀ f ∈ Hd.G.E, mk₁ f ∈ H₃.V := fun f hf => .inr ⟨(f, false), hf, rfl⟩
  have hmk₂V : ∀ f ∈ Hd.G.E, mk₂ f ∈ H₃.V := fun f hf => .inr ⟨(f, true), hf, rfl⟩
  have hpV : ∀ f ∈ Hd.G.E, Gd.plus (ε f) ∈ Hc.V := fun f hf => ⟨_, hmk₁V f hf, (hplace f hf).2.1⟩
  have hmV : ∀ f ∈ Hd.G.E, Gd.minus (ε f) ∈ Hc.V := fun f hf => ⟨_, hmk₂V f hf, (hplace f hf).2.2⟩
  have hHU₃ : H₃.U ⊆ Hd.G.U := by
    refine union_subset Hd.G.V_subset_U (iUnion₂_subset fun q hq => ?_)
    rintro _ ⟨y, -, rfl⟩
    exact (hsp.param q hq).subset_U hq y
  -- The drawing `Hc` meets the closure of each `ε f` in its ends only.
  have hCap : ∀ f ∈ Hd.G.E, ∀ x ∈ Hc.U, x ∈ closure (ε f) → x = Gd.plus (ε f) ∨ x = Gd.minus (ε f)
    := by
    exact matched_forest_meets_cut_at_ends (S := S) Hd Gd γ β τ hmk ε e mk₁ hmk₁ mk₂ hmk₂ hplace
      H₃ hmid
  have hoff : ∀ x ∈ Hc.U, x ∉ ⋃₀ 𝓔 := by
    exact matched_forest_avoids_cut_edges (S := S) Hd Gd S_r θ G_r 𝓔 hmc ε hεs Hc hCap
  have hi : InjOn θ (θ ⁻¹' Hc.U) := fun x hx y _ he => (hmc.inj x y he).resolve_right (hoff _ hx)
  set H' := pullDrawing Hc hcθ hs hi with hH'
  have hH'V : H'.V = θ ⁻¹' Hc.V := rfl
  have hH'U : H'.U = θ ⁻¹' Hc.U := rfl
  have hbackd : mapDrawingHomeo e.symm Hc = H₃ := by
    rw [hHc, mapDrawingHomeo_trans, e.self_trans_symm, mapDrawingHomeo_refl]
  have m₁ : IsMatched H' H₃ (e.symm ∘ θ) ∅ := by
    have := (matched_pullDrawing Hc hcθ hs hi).post e.symm
    rwa [hbackd] at this
  -- Points of the boundary.
  have hbdV : ∀ x ∈ bd S, (x ∈ Hc.V ↔ x ∈ Hd.G.V) := by
    exact matching_preserves_original_boundary_vertices (S := S) Hd hH β τ hsp e hebd hesymm
  have hbdU : ∀ x ∈ bd S, x ∈ Hc.U → x ∈ Hc.V := by
    rintro x hx ⟨y, hy, rfl⟩
    have : y = e y := by
      have h := hesymm _ hx
      rwa [e.symm_apply_apply] at h
    rw [hbdV _ hx, ← this]
    exact hH ⟨this ▸ hx, hHU₃ hy⟩
  have hclV : ∀ e' ∈ 𝓔, ∀ x ∈ closure e', (x ∈ Hc.V ↔ x ∈ Gd.G.V) := by
    exact matching_preserves_cut_edge_vertices (S := S) Hd Gd S_r θ G_r 𝓔 hmc ε hεs Hc hpV hmV
      hCap
  have hbdcases : ∀ x ∈ bd S_r, θ x ∈ bd S ∨ ∃ e' ∈ 𝓔, θ x ∈ closure e' := fun x hx => by
    exact cut_boundary_projects_to_boundary_or_cut_edge (S := S) Gd S_r θ G_r 𝓔 hmc x hx
  have hbdV' : ∀ x ∈ bd S_r, (θ x ∈ Hc.V ↔ θ x ∈ Gd.G.V) := fun x hx => by
    rcases hbdcases x hx with h1 | ⟨e', he', h1⟩
    · rw [hbdV _ h1]
      have h2 : (Gd.G.V ∩ bd S : Set S) = Hd.G.V ∩ bd S := hbd_eq
      constructor
      · intro h3
        exact (h2 ▸ (⟨h3, h1⟩ : θ x ∈ Hd.G.V ∩ bd S) : θ x ∈ Gd.G.V ∩ bd S).1
      · intro h3
        exact (h2 ▸ (⟨h3, h1⟩ : θ x ∈ Gd.G.V ∩ bd S) : θ x ∈ Hd.G.V ∩ bd S).1
    · exact hclV e' he' _ h1
  have hprop : H'.IsProper := by
    exact lifted_cut_forest_is_proper (S := S) Hd Gd S_r θ 𝓔 ε hεs Hc hpV hmV hCap H' rfl hH'V hbdU
      hbdcases
  have hforest : IsSurfaceForest H' := ⟨hprop, m₁.isGraphForest_iff.mpr hsp.isGraphForest⟩
  have hVeq : G_r.V ∩ bd S_r = H'.V ∩ bd S_r := by
    exact lifted_cut_forest_agrees_on_boundary (S := S) Gd S_r θ G_r 𝓔 hmc Hc H' hH'V hbdV'
  have hcardG : (G_r.V ∩ bd S_r).ncard + 2 * (c + Hd.G.E.ncard) + 2 ≤ 2 * k := by
    rw [hbd_eq] at hcardr
    omega
  refine ⟨S_r, tS_r, t1S_r, G_r, H', hSr, hmr, hBLr, by simpa using hαr, hcardG, hforest, hVeq, ?_⟩
  rintro ⟨H'', -, ⟨α, hα, hhom⟩, hsub⟩
  set Mid := mapDrawingHomeo α H' with hMid
  have hαs : ∀ s ∈ bd S_r, α.symm s = s := fun s hs' => by
    rw [Homeomorph.symm_apply_eq, hα s hs']
  set w : S_r → S := (e.symm ∘ θ) ∘ α.symm with hw
  have M : IsMatched Mid H₃ w ∅ := m₁.pre α
  have hwb : ∀ s ∈ bd S_r, w s = e.symm (θ s) := fun s hs' => by
    simp only [hw, comp_apply, hαs s hs']
  have hMidV : ∀ s ∈ bd S_r, θ s ∈ Hc.V → s ∈ Mid.V ∩ bd S_r := fun s hs' h1
    => ⟨⟨s, h1, hα s hs'⟩, hs'⟩
  have hzp : ∀ f, f ∈ Hd.G.E → ∃ z, z ∈ Mid.V ∩ bd S_r ∧ θ z = Gd.plus (ε f) ∧ splitOwner Hd.G β τ
    (w z) = Hd.plus f := fun f hf => by
    obtain ⟨z, hz⟩ := hs (Gd.plus (ε f))
    have hb := endpoint_preimage_mem_cut_boundary hmc (hε f hf) (.inl hz)
    refine ⟨z, hMidV z hb (hz ▸ hpV f hf), hz, ?_⟩
    rw [hwb z hb, hz, ← (hplace f hf).2.1, e.symm_apply_apply, ← (hor f hf).1]
    exact hsp.owner_mark (q := (f, false)) hf
  have hzm : ∀ f, f ∈ Hd.G.E → ∃ z, z ∈ Mid.V ∩ bd S_r ∧ θ z = Gd.minus (ε f) ∧ splitOwner Hd.G β τ
    (w z) = Hd.minus f := fun f hf => by
    obtain ⟨z, hz⟩ := hs (Gd.minus (ε f))
    have hb := endpoint_preimage_mem_cut_boundary hmc (hε f hf) (.inr hz)
    refine ⟨z, hMidV z hb (hz ▸ hmV f hf), hz, ?_⟩
    rw [hwb z hb, hz, ← (hplace f hf).2.2, e.symm_apply_apply, ← (hor f hf).2]
    exact hsp.owner_mark (q := (f, true)) hf
  choose! zp hzp1 hzp2 hzp3 using hzp
  choose! zm hzm1 hzm2 hzm3 using hzm
  have hiso : ∀ v ∈ Hd.G.V \ bd S, ¬ IsIsolatedVertex Hd.G v := fun v hv hisov => by
    have hfin : {v ∈ Hd.G.V \ bd S | IsIsolatedVertex Hd.G v}.Finite := Hd.G.finite_V.subset fun x
      hx => hx.1.1
    have := (Set.ncard_eq_zero hfin).mp hg0
    exact (this ▸ (⟨hv, hisov⟩ : v ∈ {v ∈ Hd.G.V \ bd S | IsIsolatedVertex Hd.G v}) : v ∈
      (∅ : Set S))
  have hrep : ∀ v, v ∈ Hd.G.V → ∃ s, s ∈ Mid.V ∩ bd S_r ∧ splitOwner Hd.G β τ (w s) = v ∧ (v ∈ bd S
    → θ s = v) := by
    exact forest_vertices_have_boundary_representatives (S := S) Hd Gd S_r θ G_r 𝓔 hmc hs β τ hsp
      e hesymm Hc hbdV Mid w hwb hMidV zp hzp1 hzp3 zm hzm1 hzm3 hiso
  choose! ρ hρ1 hρ2 hρ3 using hrep
  exact isBoundaryRootedMinor_of_forest (O := splitOwner Hd.G β τ) hbd_eq.symm hmc M hsub hhom
    (fun W => hsp.owner_walk W)
    (fun x hx y hy he hne => hsp.exists_simple_walk hx hy he hne) (fun v hv
      => ⟨hρ1 v hv, hρ2 v hv⟩) (fun v hv => hρ3 v hv.1 hv.2) hε hεi
    (fun f hf => ⟨hzp1 f hf, hzp2 f hf, hzp3 f hf⟩) (fun f hf => ⟨hzm1 f hf, hzm2 f hf, hzm3 f hf⟩)

end GraphMinor.GM07
