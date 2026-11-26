/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.CutDrawing
public import LeanPool.GraphMinor.Surface.CutGraph

/-!
# A graph in a surface, and a dissection that holds it

To cut along a set of lines we must see them as edges of a word. So we put the lines in a graph with
the cuffs
(`exists_graph_of_lines`), and extend that graph to a dissection (`exists_dissection_lines`). The
second step
is `exists_dissection_with`, for several lines in place of one.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Function GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- What we need of the sets we cut along: they are `O`-arcs, with the cuffs among them, and lines
with both
ends on the `O`-arcs. -/
structure IsCutFrame (S : Type u) [TopologicalSpace S] (𝓐 𝓛 : Set (Set S)) : Prop where
  finite_arcs : 𝓐.Finite
  finite_lines : 𝓛.Finite
  isOArc : ∀ C ∈ 𝓐, IsOArc C
  cuffs_subset : cuffs S ⊆ 𝓐
  line : ∀ L ∈ 𝓛, ∃ s t, s ≠ t ∧ IsLineWithEnds L s t ∧ s ∈ ⋃₀ 𝓐 ∧ t ∈ ⋃₀ 𝓐

omit [T2Space S] in
/-- `exists_dissection_with`, with several lines. -/
theorem exists_dissection_lines (hS : IsSurface S) [ConnectedSpace S] {V₀ : Set S} {E₀ 𝓐 𝓛 : Set
  (Set S)}
    (hg : IsGraph V₀ E₀) (hV₀ : V₀ ⊆ ⋃₀ E₀) (hF : IsCutFrame S 𝓐 𝓛) (hc : ⋃₀ E₀ = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 ∧ V₀ ⊆ V ∧ ⋃₀ E₀ ⊆ gr V E :=
  exists_dissection_with_lines hS hg hV₀ hF.finite_arcs hF.finite_lines hF.isOArc
    hF.cuffs_subset hF.line hc

/-- A graph containing the cuffs and a finite family of lines, with a uniform bound on its
edge count and the added edges lying in the boundary. -/
theorem exists_counted_line_graph (hS : IsSurface S) :
    ∃ B : ℕ, ∀ {N : Set S} {𝓔 : Set (Set S)}, N.Finite → 𝓔.Finite →
      (∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v}) →
      (∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ N) → (∀ L ∈ 𝓔, L ∩ bd S ⊆ N) → N ⊆ bd S ∪ ⋃₀ 𝓔 →
      ∃ (V : Set S) (E : Set (Set S)), N ⊆ V ∧ IsGraph V E ∧ V ⊆ ⋃₀ E ∧ ⋃₀ E = bd S ∪ ⋃₀ 𝓔 ∧ 𝓔 ⊆ E ∧
        E.ncard ≤ B + N.ncard + 𝓔.ncard ∧ (∀ e ∈ E, e ∉ 𝓔 → e ⊆ bd S) ∧ ∀ x ∈ bd S, ∃ e ∈ E, e ∉ 𝓔
          ∧ x ∈ e := by
  classical
  obtain ⟨V₁, E₁, hg, hV, hgr⟩ := exists_cuff_graph hS
  refine ⟨E₁.ncard, ?_⟩
  intro N 𝓔 hN h𝓔 hline hdisj hbd hNs
  have hgr1 : gr V₁ E₁ = bd S := by
    rw [← hgr]
    exact union_eq_right.mpr hV
  have hpts : ∀ M : Set S, M.Finite → ∃ E', IsGraph (M ∪ V₁) E' ∧ gr (M ∪ V₁) E' = M ∪ bd S
    ∧ bd S ⊆ ⋃₀ E' ∧
      E'.ncard ≤ E₁.ncard + M.ncard ∧ ∀ f ∈ E', f ⊆ bd S := by
    intro M hM
    induction M, hM using Set.Finite.induction_on with
    | empty =>
      refine ⟨E₁, by simpa using hg, by simpa using hgr1, hgr.ge, by simp, fun f hf ↦ ?_⟩
      rw [← hgr]
      exact subset_sUnion_of_mem hf
    | @insert x M hx hfin ih =>
      obtain ⟨E', h1, h2, h3, h3', h3''⟩ := ih
      obtain ⟨E'', h4, h5, h6, h7, h8⟩ := h1.add_point_counted x
      refine ⟨E'', by rwa [insert_union], ?_, h3.trans h6, ?_, fun f hf ↦ ?_⟩
      · rw [insert_union, h5, h2, insert_union]
      · rw [ncard_insert_of_notMem hx hfin]
        omega
      · obtain ⟨e, he, hfe⟩ := h8 f hf
        exact hfe.trans (h3'' e he)
  obtain ⟨E₂, hg2, hgr2, hbdE, hcard2, hE₂bd⟩ := hpts N hN
  have hE₂ : ⋃₀ E₂ ⊆ N ∪ bd S := hgr2 ▸ subset_union_right
  have harcs : ∀ 𝓔' : Set (Set S), 𝓔'.Finite → 𝓔' ⊆ 𝓔 →
      IsGraph (N ∪ V₁) (𝓔' ∪ E₂) ∧ gr (N ∪ V₁) (𝓔' ∪ E₂) = (N ∪ bd S) ∪ ⋃₀ 𝓔' := by
    intro 𝓔' h𝓔'
    induction 𝓔', h𝓔' using Set.Finite.induction_on with
    | empty =>
      intro _
      simpa [hgr2] using hg2
    | @insert L 𝓔' hL hfin ih =>
      intro hsub
      obtain ⟨h1, h2⟩ := ih ((subset_insert _ _).trans hsub)
      have hLm : L ∈ 𝓔 := hsub (mem_insert _ _)
      obtain ⟨u, v, huv, hl, hi⟩ := hline L hLm
      have hu : u ∈ L ∩ N := hi ▸ mem_insert _ _
      have hv : v ∈ L ∩ N := hi ▸ mem_insert_of_mem _ rfl
      have hcap : L ∩ gr (N ∪ V₁) (𝓔' ∪ E₂) = {u, v} := by
        rw [h2]
        apply subset_antisymm
        · rintro x ⟨hxL, (hx | hx) | ⟨L', hL', hx⟩⟩
          · exact hi ▸ ⟨hxL, hx⟩
          · exact hi ▸ ⟨hxL, hbd L hLm ⟨hxL, hx⟩⟩
          · exact hi ▸ ⟨hxL, hdisj L hLm L' (hsub (.inr hL')) (fun he => hL (he ▸ hL')) ⟨hxL, hx⟩⟩
        · rintro x (rfl | rfl)
          · exact ⟨hu.1, .inl (.inl hu.2)⟩
          · exact ⟨hv.1, .inl (.inl hv.2)⟩
      obtain ⟨h3, h4⟩ := h1.add_arc huv hl (.inl hu.2) (.inl hv.2) hcap
      rw [insert_union]
      refine ⟨h3, ?_⟩
      rw [h4, h2, sUnion_insert, union_comm L, union_assoc]
  obtain ⟨hg3, hgr3⟩ := harcs 𝓔 h𝓔 subset_rfl
  have hU : ⋃₀ (𝓔 ∪ E₂) = bd S ∪ ⋃₀ 𝓔 := by
    rw [sUnion_union]
    apply subset_antisymm
    · refine union_subset subset_union_right fun x hx ↦ ?_
      rcases hE₂ hx with h | h
      · exact hNs h
      · exact .inl h
    · exact union_subset (hbdE.trans subset_union_right) subset_union_left
  refine ⟨N ∪ V₁, 𝓔 ∪ E₂, subset_union_left, hg3, ?_, hU, subset_union_left, ?_, ?_, ?_⟩
  · rw [hU]
    refine union_subset hNs ?_
    exact (hgr ▸ hV).trans subset_union_left
  · have := ncard_union_le 𝓔 E₂
    omega
  · rintro e (he | he) hne
    · exact absurd he hne
    · exact hE₂bd e he
  · intro x hx
    obtain ⟨e, he, hxe⟩ := hbdE hx
    refine ⟨e, .inr he, fun hin ↦ ?_, hxe⟩
    obtain ⟨u, v, huv, hl, hi⟩ := hline e hin
    obtain ⟨a, ha, rfl, rfl, rfl⟩ := hl.exists_arc
    have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hm : a ⟨1 / 2, h12⟩ ∈ range a ∩ N := ⟨⟨_, rfl⟩, hbd _ hin ⟨⟨_, rfl⟩, hE₂bd _ he ⟨_, rfl⟩⟩⟩
    rw [hi] at hm
    rcases hm with h1 | h1
    · have : (1 / 2 : ℝ) = 0 := congrArg Subtype.val (ha.2 h1)
      norm_num at this
    · have : (1 / 2 : ℝ) = 1 := congrArg Subtype.val (ha.2 h1)
      norm_num at this

/-- The cuffs, a finite set `N` of points on the lines, and lines that meet only in `N`, make up a
graph. -/
theorem exists_graph_of_lines (hS : IsSurface S) {N : Set S} {𝓔 : Set (Set S)} (hN : N.Finite)
  (h𝓔 : 𝓔.Finite)
    (hline : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v})
    (hdisj : ∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ N) (hbd : ∀ L ∈ 𝓔, L ∩ bd S ⊆ N)
      (hNs : N ⊆ bd S ∪ ⋃₀ 𝓔) :
    ∃ (V : Set S) (E : Set (Set S)), N ⊆ V ∧ IsGraph V E ∧ V ⊆ ⋃₀ E ∧ ⋃₀ E = bd S ∪ ⋃₀ 𝓔 ∧ 𝓔 ⊆ E
      := by
  obtain ⟨_, h⟩ := exists_counted_line_graph hS
  obtain ⟨V, E, hNV, hg, hV, hU, hE, _, _, _⟩ := h hN h𝓔 hline hdisj hbd hNs
  exact ⟨V, E, hNV, hg, hV, hU, hE⟩

variable {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)} {A : Set S
  → unitInterval → S}
  {lab : Set S → ℕ} {D : Set (Set S)} {Y : Type u} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S}

/-- A part of an edge with lifts, with ends where the lifts are apart, has a pair of lifts. -/
theorem liftPair_of_piece (h : WordEdges W f V E A lab) {e : Set S} (he : e ∈ E) {hend : Bool
  → Prop}
    {r r' : ℝ → Y} (hL : IsEdgeLift ψ (extI (A e)) hend r r') {ι : ℝ → S} {c d : ℝ} (hcd : c < d)
    (hι : ContinuousOn ι (Icc c d)) (hinj : InjOn ι (Icc c d)) (hsub : ι '' Icc c d ⊆ e)
    (hfine : ∀ x ∈ Icc c d, ∀ τ, ι x = extI (A e) (eo τ) → hend τ) :
    ∃ X X', LiftPair ψ (ι '' Icc c d) (ι c) (ι d) X X' := by
  obtain ⟨hrc, hrc', hr, -, hf⟩ := hL
  have ha := h.arc e he
  have hec := continuous_extI ha.1.1
  have hei := extI_injOn ha.1.2
  have hre : extI (A e) '' Icc 0 1 = e := by rw [image_extI, ha.2.1]
  obtain ⟨ρ, hρ, hl⟩ := exists_inv_of_compactOn (isCompact_Icc (a := (0 : ℝ)) (b
    := 1)) hec.continuousOn hei
  have hθ : ∀ x ∈ Icc c d, ρ (ι x) ∈ Icc (0 : ℝ) 1 ∧ extI (A e) (ρ (ι x)) = ι x := fun x hx ↦ by
    have hm : ι x ∈ extI (A e) '' Icc 0 1 := by
      rw [hre]
      exact hsub (mem_image_of_mem ι hx)
    obtain ⟨s, hs, hse⟩ := hm
    rw [← hse, hl hs]
    exact ⟨hs, rfl⟩
  have hδ : 0 < d - c := sub_pos.mpr hcd
  let u : ℝ → ℝ := fun s ↦ c + s * (d - c)
  have huc : Continuous u := by fun_prop
  have huI : ∀ s ∈ Icc (0 : ℝ) 1, u s ∈ Icc c d := fun s hs ↦
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have huo : ∀ x ∈ Icc c d, (x - c) / (d - c) ∈ Icc (0 : ℝ) 1 ∧ u ((x - c) / (d - c)) = x
    := fun x hx ↦ by
    refine ⟨⟨div_nonneg (by linarith [hx.1]) hδ.le, ?_⟩, ?_⟩
    · rw [div_le_one hδ]
      linarith [hx.2]
    · simp only [u]
      field_simp
      ring
  have hb : ContinuousOn (fun s ↦ ρ (ι (u s))) (Icc 0 1) := by
    refine hρ.comp (hι.comp huc.continuousOn huI) fun s hs ↦ ?_
    rw [hre]
    exact hsub (mem_image_of_mem ι (huI s hs))
  have himg : (fun s ↦ ι (u s)) '' Icc 0 1 = ι '' Icc c d := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_image_of_mem ι (huI s hs)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, (huo x hx).1, by simp only [(huo x hx).2]⟩
  have hfineθ : ∀ s ∈ Icc (0 : ℝ) 1, ρ (ι (u s)) ∈ Ioo (0 : ℝ) 1 ∨ ∃ τ, eo τ = ρ (ι (u s)) ∧ hend τ
    := fun s hs ↦ by
    obtain ⟨h1, h2⟩ := hθ _ (huI s hs)
    by_cases h0 : ρ (ι (u s)) = 0
    · refine .inr ⟨false, by simp [eo, h0], hfine _ (huI s hs) false ?_⟩
      rw [← h2, h0]
      simp [eo]
    by_cases h3 : ρ (ι (u s)) = 1
    · refine .inr ⟨true, by simp [eo, h3], hfine _ (huI s hs) true ?_⟩
      rw [← h2, h3]
      simp [eo]
    exact .inl ⟨lt_of_le_of_ne h1.1 (Ne.symm h0), lt_of_le_of_ne h1.2 h3⟩
  have hpair := liftPair_of_maps (ψ := ψ) (a := fun s ↦ ι (u s)) (r := fun s ↦ r (ρ (ι (u s))))
    (r' := fun s ↦ r' (ρ (ι (u s))))
    (hrc.comp hb fun s hs ↦ (hθ _ (huI s hs)).1) (hrc'.comp hb fun s hs ↦ (hθ _ (huI s hs)).1)
    (fun s hs ↦ by
      rw [(hr _ (hθ _ (huI s hs)).1).1, (hθ _ (huI s hs)).2])
    (fun s hs ↦ by
      rw [(hr _ (hθ _ (huI s hs)).1).2, (hθ _ (huI s hs)).2])
    (fun s hs s' hs' he' ↦ by
      have := hinj (huI s hs) (huI s' hs') he'
      have h5 : (s - s') * (d - c) = 0 := by
        simp only [u] at this
        linear_combination this
      rcases mul_eq_zero.mp h5 with h6 | h6
      · linarith
      · linarith)
    (fun s hs ↦ (hf _ (hθ _ (huI s hs)).1 (hfineθ s hs)).1)
    (by
      rintro z ⟨s, hs, hz⟩
      have hzt : ψ z = extI (A e) (ρ (ι (u s))) := by rw [(hθ _ (huI s hs)).2]; exact hz.symm
      rcases (hf _ (hθ _ (huI s hs)).1 (hfineθ s hs)).2 z hzt with rfl | rfl
      · exact .inl ⟨s, hs, rfl⟩
      · exact .inr ⟨s, hs, rfl⟩)
  rw [himg] at hpair
  have e0 : u 0 = c := by simp [u]
  have e1 : u 1 = d := by simp [u]
  simp only [e0, e1] at hpair
  exact ⟨_, _, hpair⟩

omit [T2Space S] in
/-- At a vertex inside a chain of edges that holds all the edges of `D` ending there, the edges of
`D` look
like a line. -/
theorem endFine_of_chain {ι : ℝ → S} {m : ℕ} {t : ℕ → ℝ} {ss : ℕ → Set S} {ε : ℕ → Bool}
    (hex : ∀ p < m, ∀ τ, extI (A (ss p)) (eo τ) = ι (t (chainAt ε p τ)))
    (hinj : ∀ k ≤ m, ∀ k' ≤ m, ι (t k) = ι (t k') → k = k') (hsne : ∀ p < m, ∀ q < m, p ≠ q
      → ss p ≠ ss q)
    (hmem : ∀ p < m, ss p ∈ D) {p : ℕ} (hp : p < m) {τ : Bool} (h0 : 0 < chainAt ε p τ)
      (h1 : chainAt ε p τ < m)
    (hb : ι (t (chainAt ε p τ)) ∉ bd S)
    (hall : ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = ι (t (chainAt ε p τ)) → ∃ q < m, e'' = ss q) :
    EndFine A D (ss p) τ := by
  have hat : ∀ {q τ'}, q < m → chainAt ε q τ' ≤ m := fun {q τ'} hq ↦ by
    unfold chainAt
    split_ifs <;> omega
  obtain ⟨k, hk⟩ : ∃ k, chainAt ε p τ = k := ⟨_, rfl⟩
  have hsplit := chainAt_split hk
  rw [hk] at h0 h1 hb hall
  have hup : chainAt ε k (!ε k) = k := by
    unfold chainAt
    cases ε k <;> simp
  have hdn : chainAt ε (k - 1) (ε (k - 1)) = k := by
    unfold chainAt
    simp
    omega
  refine .inl ?_
  have hval : extI (A (ss p)) (eo τ) = ι (t k) := hk ▸ hex p hp τ
  have huniq : ∀ e'' ∈ D, ∀ τ'', extI (A e'') (eo τ'') = extI (A (ss p)) (eo τ) →
      (e'' = ss k ∧ τ'' = !ε k) ∨ (e'' = ss (k - 1) ∧ τ'' = ε (k - 1)) := by
    intro e'' he'' τ'' he
    obtain ⟨q, hq, rfl⟩ := hall e'' he'' τ'' (he.trans hval)
    have h3 := hinj _ (hat hq) k h1.le (by rw [← hex q hq τ'', he, hval])
    rcases chainAt_split h3 with ⟨rfl, rfl⟩ | ⟨h5, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · obtain rfl : q = k - 1 := by omega
      exact .inr ⟨rfl, rfl⟩
  rcases hsplit with ⟨hpk, rfl⟩ | ⟨hpk, rfl⟩
  · subst hpk
    refine ⟨ss (p - 1), hmem _ (by omega), ε (p - 1), hsne _ (by omega) _ hp (by omega), ?_, ?_, ?_⟩
    · rw [hval, hex _ (by omega), hdn]
    · rw [hval]
      exact hb
    · intro e'' he'' τ'' he
      exact huniq e'' he'' τ'' he
  · obtain rfl : p = k - 1 := by omega
    refine ⟨ss k, hmem _ h1, !ε k, hsne _ h1 _ hp (by omega), ?_, ?_, ?_⟩
    · rw [hval, hex _ h1, hup]
    · rw [hval]
      exact hb
    · intro e'' he'' τ'' he
      exact (huniq e'' he'' τ'' he).symm

end GraphMinor.GM19
