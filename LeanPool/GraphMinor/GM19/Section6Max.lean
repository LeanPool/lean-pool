/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Comp

/-!
# Growing an enlargement

The first step of the proof of (6.6) of Graph Minors XIX (page 341): choose an enlargement `σ'` that
keeps the edges of `σ` and contains its branch sets, as large as possible. If `G'` is connected then
the branch sets of `σ'` cover `V(G')`, and each is induced (`exists_full_enlargement`). We add one
edge at a time (`IsEnlargement.extend`), and count (`exists_full_aux`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GM11

variable {S : Type} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
theorem tilde_subset_V (D : Drawing S) {e : Set S} (he : e ∈ D.E) : tilde e ⊆ D.V := fun _ hx =>
  (GM19.tilde_eq_inter_V D he ▸ hx : _ ∈ closure e ∩ D.V).2

omit [T2Space S] in
/-- Each end of `σ(e)` lies in the branch set of an end of `e`. -/
theorem IsEnlargement.end_mem {G G' : Drawing S} (hl : LoopFree G) (hl' : LoopFree G') {σv : S
    → Drawing S} {σe : Set S → Set S} (hσ : IsEnlargement G G' σv σe)
    {e : Set S} (he : e ∈ G.E) {x : S}
    (hx : x ∈ tilde (σe e)) : ∃ u ∈ G.V, u ∈ tilde e ∧ x ∈ (σv u).V := by
  obtain ⟨u₁, u₂, h12, hti, -⟩ := hl e he
  have hm₁ : u₁ ∈ tilde e := by rw [hti]; exact .inl rfl
  have hm₂ : u₂ ∈ tilde e := by rw [hti]; exact .inr rfl
  have hV₁ := tilde_subset_V G he hm₁
  have hV₂ := tilde_subset_V G he hm₂
  obtain ⟨y₁, hy₁, hy₁e⟩ := (hσ.ends_iff e he u₁ hV₁).mpr hm₁
  obtain ⟨y₂, hy₂, hy₂e⟩ := (hσ.ends_iff e he u₂ hV₂).mpr hm₂
  have hne : y₁ ≠ y₂ := fun h => Set.disjoint_left.mp (hσ.vertex_disjoint _ hV₁ _ hV₂ h12) hy₁
    (h ▸ hy₂)
  obtain ⟨a, b, -, hti', -⟩ := hl' _ (hσ.edge_mem e he)
  rw [hti'] at hy₁e hy₂e hx
  have hcases : x = y₁ ∨ x = y₂ := by
    rcases hy₁e with rfl | hy₁e <;> rcases hy₂e with rfl | hy₂e <;> rcases hx with rfl | hx
    · exact absurd rfl hne
    · exact absurd rfl hne
    · exact .inl rfl
    · exact .inr (hx.trans hy₂e.symm)
    · exact .inr rfl
    · exact .inl (hx.trans hy₁e.symm)
    · exact absurd (hy₁e.trans hy₂e.symm) hne
    · exact absurd (hy₁e.trans hy₂e.symm) hne
  rcases hcases with rfl | rfl
  · exact ⟨u₁, hV₁, hm₁, hy₁⟩
  · exact ⟨u₂, hV₂, hm₂, hy₂⟩

/-- **Adding an edge to a branch set.** The edge `f` has an end `y` in the branch set of `w`, and
its other end `x` is in no other branch set. -/
theorem IsEnlargement.extend {G G' : Drawing S} (hl : LoopFree G)
    (hl' : LoopFree G') {σv : S → Drawing S} {σe : Set S → Set S}
    (hσ : IsEnlargement G G' σv σe) {w : S} (hw : w ∈ G.V) {f : Set S}
    (hf : f ∈ G'.E) {x y : S} (hy : y ∈ (σv w).V) (hti : tilde f = {y, x}) (hx : ∀ u ∈ G.V, u ≠ w
      → x ∉ (σv u).V) :
    ∃ τ : S → Drawing S, IsEnlargement G G' τ σe ∧ (∀ v ∈ G.V, (σv v).IsSubdrawing (τ v)) ∧ x ∈
      (τ w).V ∧ f ∈ (τ w).E := by
  classical
  have hsubw := hσ.vertex_subdrawing w hw
  have hxV : x ∈ G'.V := tilde_subset_V G' hf (by rw [hti]; exact .inr rfl)
  let D : Drawing S := G'.span (insert x (σv w).V) (insert f (σv w).E)
  have hDV : D.V = insert x (σv w).V := by
    apply Subset.antisymm
    · refine union_subset inter_subset_left (iUnion₂_subset fun e he => ?_)
      rintro z ⟨hz, hzV⟩
      have hzt : z ∈ tilde e := GM19.tilde_eq_inter_V G' he.2 ▸ ⟨hz, hzV⟩
      rcases he.1 with rfl | he1
      · rw [hti] at hzt
        rcases hzt with rfl | hzt
        · exact .inr hy
        · exact .inl hzt
      · exact .inr (tilde_subset_V _ he1 hzt)
    · rintro z (rfl | hz)
      · exact .inl ⟨.inl rfl, hxV⟩
      · exact .inl ⟨.inr hz, hsubw.1 hz⟩
  have hDE : D.E = insert f (σv w).E := by
    change (G'.span _ _).E = _
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (insert_subset hf hsubw.2)
  have hsubD : (σv w).IsSubdrawing D := ⟨hDV ▸ subset_insert _ _, hDE ▸ subset_insert _ _⟩
  have hDsub : D.IsSubdrawing G' := ⟨hDV ▸ insert_subset hxV hsubw.1, hDE ▸ insert_subset hf
    hsubw.2⟩
  have hyx : ∀ {z}, z = x → z ≠ y → D.adj.Adj y z := fun {z} hz hne => by
    subst hz
    exact ⟨hne.symm, hsubD.1 hy, hDV ▸ .inl rfl, f, hDE ▸ .inl rfl,
      hti ▸ .inl rfl, hti ▸ .inr rfl⟩
  let τ : S → Drawing S := fun u => if u = w then D else σv u
  have hτw : τ w = D := ite_eq_left rfl
  have hτ : ∀ u, u ≠ w → τ u = σv u := fun u hu => ite_eq_right hu
  refine ⟨τ, ⟨hσ.edge_mem, hσ.edge_injOn, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_,
    fun v₁ hv₁ v₂ hv₂ hne => ?_, fun e he v hv => ?_⟩, fun v hv => ?_,
    hτw ▸ hDV ▸ .inl rfl, hτw ▸ hDE ▸ .inl rfl⟩
  · by_cases h : v = w
    · rw [h, hτw]
      exact hDsub
    · rw [hτ v h]
      exact hσ.vertex_subdrawing v hv
  · by_cases h : v = w
    · rw [h, hτw, hDV]
      exact insert_nonempty _ _
    · rw [hτ v h]
      exact hσ.vertex_nonempty v hv
  · by_cases h : v = w
    · rw [h, hτw, preconnected_iff_connIn, hDV]
      rintro Y hY ⟨z, hz⟩ hc
      have hold := (preconnected_iff_connIn _ _).mp (hσ.vertex_connected w hw)
      have hstep : ∀ {a b}, a ∈ Y → b ∈ insert x (σv w).V → D.adj.Adj a b → b ∈ Y := fun ha hb hab
        => hc _ ha _ hb hab
      have hYold : (Y ∩ (σv w).V).Nonempty → (σv w).V ⊆ Y := fun hn => by
        have := hold (Y ∩ (σv w).V) inter_subset_right hn fun a ha b hb hab => ⟨hc a ha.1 b
          (.inr hb) (adj_mono hsubD hab), hb⟩
        rw [← this]
        exact inter_subset_left
      have hyY : y ∈ Y := by
        rcases hY hz with rfl | hzw
        · by_cases hzy : z = y
          · exact hzy ▸ hz
          · exact hc _ hz _ (.inr hy) ((hyx rfl hzy).symm)
        · exact hYold ⟨z, hz, hzw⟩ hy
      have hall := hYold ⟨y, hyY, hy⟩
      refine Subset.antisymm hY (insert_subset ?_ hall)
      by_cases hxy : x = y
      · exact hxy ▸ hyY
      · exact hc _ hyY _ (.inl rfl) (hyx rfl hxy)
    · rw [hτ v h]
      exact hσ.vertex_connected v hv
  · by_cases h1 : v₁ = w
    · subst h1
      rw [hτw, hτ v₂ hne.symm, hDV]
      exact Set.disjoint_insert_left.mpr ⟨hx v₂ hv₂ hne.symm, hσ.vertex_disjoint _ hv₁ _ hv₂ hne⟩
    · by_cases h2 : v₂ = w
      · subst h2
        rw [hτw, hτ v₁ hne, hDV]
        exact Set.disjoint_insert_right.mpr ⟨hx v₁ hv₁ hne, hσ.vertex_disjoint _ hv₁ _ hv₂ hne⟩
      · rw [hτ v₁ h1, hτ v₂ h2]
        exact hσ.vertex_disjoint _ hv₁ _ hv₂ hne
  · by_cases h : v = w
    · subst h
      rw [hτw, hDV]
      rw [← hσ.ends_iff e he v hv]
      constructor
      · rintro ⟨z, rfl | hz, hzt⟩
        · obtain ⟨u, hu, -, hzu⟩ := hσ.end_mem hl hl' he hzt
          by_cases huv : u = v
          · exact ⟨z, huv ▸ hzu, hzt⟩
          · exact absurd hzu (hx u hu huv)
        · exact ⟨z, hz, hzt⟩
      · rintro ⟨z, hz, hzt⟩
        exact ⟨z, .inr hz, hzt⟩
    · rw [hτ v h]
      exact hσ.ends_iff e he v hv
  · by_cases h : v = w
    · rw [h, hτw]
      exact hsubD
    · rw [hτ v h]
      exact ⟨Subset.refl _, Subset.refl _⟩

/-- All the vertices of the branch sets. -/
def branchV (G : Drawing S) (σv : S → Drawing S) : Set S := ⋃ v ∈ G.V, (σv v).V

/-- All the edges of the branch sets. -/
def branchE (G : Drawing S) (σv : S → Drawing S) : Set (Set S) := ⋃ v ∈ G.V, (σv v).E

theorem exists_full_aux {G G' : Drawing S} (hl : LoopFree G) (hl' : LoopFree G')
  (hconn : ConnIn G' G'.V) (hne : G.V.Nonempty) {σe : Set S → Set S} :
    ∀ (d : ℕ) (σv : S → Drawing S), IsEnlargement G G' σv σe → G'.V.ncard + G'.E.ncard ≤ d +
      ((branchV G σv).ncard + (branchE G σv).ncard) →
      ∃ τ : S → Drawing S, IsEnlargement G G' τ σe ∧ (∀ v ∈ G.V, (σv v).IsSubdrawing (τ v))
        ∧ branchV G τ = G'.V ∧ ∀ v ∈ G.V, ∀ e ∈ G'.E, tilde e ⊆ (τ v).V → e ∈ (τ v).E := by
  classical
  have hsubV : ∀ {σ : S → Drawing S}, IsEnlargement G G' σ σe → branchV G σ ⊆ G'.V := fun hσ
    => iUnion₂_subset fun v hv => (hσ.vertex_subdrawing v hv).1
  have hsubE : ∀ {σ : S → Drawing S}, IsEnlargement G G' σ σe → branchE G σ ⊆ G'.E := fun hσ
    => iUnion₂_subset fun v hv => (hσ.vertex_subdrawing v hv).2
  have hmono : ∀ {σ τ : S → Drawing S}, (∀ v ∈ G.V, (σ v).IsSubdrawing (τ v))
    → branchV G σ ⊆ branchV G τ ∧ branchE G σ ⊆ branchE G τ := fun h =>
    ⟨biUnion_mono (Subset.refl _) fun v hv => (h v hv).1, biUnion_mono (Subset.refl _) fun v hv =>
      (h v hv).2⟩
  have hgrow : ∀ {σ τ : S → Drawing S}, IsEnlargement G G' σ σe → IsEnlargement G G' τ σe →
    (∀ v ∈ G.V, (σ v).IsSubdrawing (τ v)) →
      ((∃ x ∈ branchV G τ, x ∉ branchV G σ) ∨ ∃ f ∈ branchE G τ, f ∉ branchE G σ) →
        (branchV G σ).ncard + (branchE G σ).ncard < (branchV G τ).ncard + (branchE G τ).ncard := by
    intro σ τ h1 h2 h3 h4
    obtain ⟨h5, h6⟩ := hmono h3
    have hfV := G'.finite_V.subset (hsubV h2)
    have hfE := G'.finite_edges.subset (hsubE h2)
    rcases h4 with ⟨x, hx, hx'⟩ | ⟨f, hf, hf'⟩
    · have := ncard_lt_ncard (⟨h5, fun h => hx' (h hx)⟩ : branchV G σ ⊂ branchV G τ) hfV
      have := ncard_le_ncard h6 hfE
      omega
    · have := ncard_lt_ncard (⟨h6, fun h => hf' (h hf)⟩ : branchE G σ ⊂ branchE G τ) hfE
      have := ncard_le_ncard h5 hfV
      omega
  intro d
  induction d with
  | zero =>
    intro σv hσ hd
    have h1 := ncard_le_ncard (hsubV hσ) G'.finite_V
    have h2 := ncard_le_ncard (hsubE hσ) G'.finite_edges
    have hV : branchV G σv = G'.V := eq_of_subset_of_ncard_le (hsubV hσ) (by omega) G'.finite_V
    have hE : branchE G σv = G'.E := eq_of_subset_of_ncard_le (hsubE hσ) (by omega) G'.finite_edges
    refine ⟨σv, hσ, fun v _ => ⟨Subset.refl _, Subset.refl _⟩, hV, fun v hv e he hsub => ?_⟩
    rw [← hE] at he
    obtain ⟨u, hu, heu⟩ := mem_iUnion₂.mp he
    obtain ⟨a, b, hab, hti, -⟩ := hl' e (by rw [← hE]; exact he)
    have ha : a ∈ tilde e := by rw [hti]; exact .inl rfl
    have huv : u = v := by
      by_contra hne'
      exact Set.disjoint_left.mp (hσ.vertex_disjoint _ hu _ hv hne') (tilde_subset_V _ heu ha)
        (hsub ha)
    exact huv ▸ heu
  | succ d ih =>
    intro σv hσ hd
    have hfin : ∀ {τ : S → Drawing S}, IsEnlargement G G' τ σe → (∀ v ∈ G.V, (σv v).IsSubdrawing
      (τ v)) → ((∃ x ∈ branchV G τ, x ∉ branchV G σv) ∨ ∃ f ∈ branchE G τ, f ∉ branchE G σv) →
        ∃ τ' : S → Drawing S, IsEnlargement G G' τ' σe ∧ (∀ v ∈ G.V, (σv v).IsSubdrawing (τ' v))
          ∧ branchV G τ' = G'.V ∧ ∀ v ∈ G.V, ∀ e ∈ G'.E, tilde e ⊆ (τ' v).V → e ∈ (τ' v).E := by
      intro τ hτ hs hnew
      have := hgrow hσ hτ hs hnew
      obtain ⟨τ', h1, h2, h3⟩ := ih τ hτ (by omega)
      exact ⟨τ', h1, fun v hv => (hs v hv).trans (h2 v hv), h3⟩
    by_cases hcover : branchV G σv = G'.V
    swap
    · have hbne : (branchV G σv).Nonempty := by
        obtain ⟨v, hv⟩ := hne
        obtain ⟨x, hx⟩ := hσ.vertex_nonempty v hv
        exact ⟨x, mem_iUnion₂.mpr ⟨v, hv, hx⟩⟩
      have hex : ∃ a ∈ branchV G σv, ∃ b ∈ G'.V, G'.adj.Adj a b ∧ b ∉ branchV G σv := by
        by_contra hno
        push Not at hno
        exact hcover (hconn _ (hsubV hσ) hbne fun a ha b hb hab => hno a ha b hb hab)
      obtain ⟨a, ha, b, hb, ⟨hab, -, -, f, hf, hfa, hfb⟩, hbn⟩ := hex
      obtain ⟨w, hw, haw⟩ := mem_iUnion₂.mp ha
      obtain ⟨p, q, hpq, hti, -⟩ := hl' f hf
      have hti' : tilde f = {a, b} := by
        rw [hti] at hfa hfb ⊢
        rcases hfa with rfl | hfa <;> rcases hfb with rfl | hfb
        · exact absurd rfl hab
        · rw [mem_singleton_iff.mp hfb]
        · rw [mem_singleton_iff.mp hfa, pair_comm]
        · exact absurd ((mem_singleton_iff.mp hfa).trans (mem_singleton_iff.mp hfb).symm) hab
      obtain ⟨τ, h1, h2, h3, -⟩ := hσ.extend hl hl' hw hf haw hti' fun u hu _ hbu => hbn
        (mem_iUnion₂.mpr ⟨u, hu, hbu⟩)
      exact hfin h1 h2 (.inl ⟨b, mem_iUnion₂.mpr ⟨w, hw, h3⟩, hbn⟩)
    by_cases hind : ∀ v ∈ G.V, ∀ e ∈ G'.E, tilde e ⊆ (σv v).V → e ∈ (σv v).E
    · exact ⟨σv, hσ, fun v _ => ⟨Subset.refl _, Subset.refl _⟩, hcover, hind⟩
    push Not at hind
    obtain ⟨w, hw, f, hf, hsub, hfn⟩ := hind
    obtain ⟨p, q, hpq, hti, -⟩ := hl' f hf
    have hp : p ∈ (σv w).V := hsub (by rw [hti]; exact .inl rfl)
    have hq : q ∈ (σv w).V := hsub (by rw [hti]; exact .inr rfl)
    obtain ⟨τ, h1, h2, -, h4⟩ := hσ.extend hl hl' hw hf hp hti fun u hu hne' hqu
      => Set.disjoint_left.mp (hσ.vertex_disjoint _ hu _ hw hne') hqu hq
    refine hfin h1 h2 (.inr ⟨f, mem_iUnion₂.mpr ⟨w, hw, h4⟩, fun hfb => ?_⟩)
    obtain ⟨u, hu, hfu⟩ := mem_iUnion₂.mp hfb
    have hpt : p ∈ tilde f := by rw [hti]; exact .inl rfl
    by_cases huw : u = w
    · exact hfn (huw ▸ hfu)
    · exact Set.disjoint_left.mp (hσ.vertex_disjoint _ hu _ hw huw) (tilde_subset_V _ hfu hpt) hp

/-- **A full enlargement.** See the module docstring. -/
theorem exists_full_enlargement {G G' : Drawing S} (hl : LoopFree G) (hl' : LoopFree G')
    (hconn : ConnIn G' G'.V) (hne : G.V.Nonempty) {σv : S → Drawing S}
    {σe : Set S → Set S} (hσ : IsEnlargement G G' σv σe) :
    ∃ τ : S → Drawing S, IsEnlargement G G' τ σe ∧ (∀ v ∈ G.V, (σv v).IsSubdrawing (τ v))
      ∧ branchV G τ = G'.V ∧ ∀ v ∈ G.V, ∀ e ∈ G'.E, tilde e ⊆ (τ v).V → e ∈ (τ v).E := by
  classical
  exact exists_full_aux hl hl' hconn hne _ σv hσ (Nat.le_add_right _ _)

end GraphMinor.GM19
