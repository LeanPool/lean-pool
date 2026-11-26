/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.DrawingOps
public import LeanPool.GraphMinor.GM11.Rotation

/-!
# Splitting each edge at a new vertex

`exists_split` adds one new vertex in each edge of a drawing. An edge `e` splits at its new vertex
`m e`
into two edges `A e` and `B e` of the new drawing, none of which is a loop, and these are all the
edges of
the new drawing. The point set does not change, and so neither do the regions.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- The piece of a curve over an open interval of parameters is path connected. -/
theorem isPathConnected_image_Ioo {γ : I → S} (hγ : Continuous γ) {a b : I} (hab : a < b) :
    IsPathConnected (γ '' Ioo a b) := by
  let g : ℝ → S := fun x => γ (projIcc 0 1 zero_le_one x)
  have hg : Continuous g := hγ.comp continuous_projIcc
  have heq : γ '' Ioo a b = g '' Ioo a.1 b.1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.1, ⟨ht.1, ht.2⟩, by simp [g]⟩
    · rintro ⟨t, ht, rfl⟩
      have hm : t ∈ Icc (0 : ℝ) 1 := ⟨a.2.1.trans ht.1.le, ht.2.le.trans b.2.2⟩
      refine ⟨⟨t, hm⟩, ⟨ht.1, ht.2⟩, ?_⟩
      simp only [g, projIcc_of_mem zero_le_one hm]
  rw [heq]
  exact ((convex_Ioo a.1 b.1).isPathConnected (nonempty_Ioo.mpr hab)).image hg

/-- The closure of the piece of a curve over an open interval is the piece over the closed interval.
-/
theorem closure_image_Ioo {γ : I → S} (hγ : Continuous γ) {a b : I} (hab : a < b) :
    closure (γ '' Ioo a b) = γ '' Icc a b := by
  have hcl : IsClosed (γ '' Icc a b) := (isCompact_Icc.image hγ).isClosed
  apply subset_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) hcl
  · rw [← closure_Ioo hab.ne]
    exact image_closure_subset_closure_image hγ

variable {D D₂ : Drawing S}

/-- One half of an edge is an edge of the new drawing. -/
private theorem piece_mem {m : Set S → S} (hm : ∀ e ∈ D.E, m e ∈ e) (hU : D₂.U = D.U)
    (hV : D₂.V = D.V ∪ m '' D.E) {e : Set S} (he : e ∈ D.E) {γ : I → S} (hγ : Continuous γ)
    (h0 : γ 0 ∈ D.V) (h1 : γ 1 ∈ D.V) (hi : InjOn γ (Ioo 0 1)) (him : γ '' Ioo 0 1 = e)
    {t₀ : I} (ht₀ : t₀ ∈ Ioo (0 : I) 1) (hγt : γ t₀ = m e) {a b : I} (hab : a < b) (ha : 0 ≤ a)
    (hb : b ≤ 1) (hne : t₀ ∉ Ioo a b) (hend : (a = 0 ∧ b = t₀) ∨ (a = t₀ ∧ b = 1)) :
    γ '' Ioo a b ∈ D₂.E := by
  have hsub : Ioo a b ⊆ Ioo (0 : I) 1 := Ioo_subset_Ioo ha hb
  have hoff : ∀ s ∈ Ioo (0 : I) 1, s ≠ t₀ → γ s ∈ D₂.U \ D₂.V := by
    intro s hs hst
    have hse : γ s ∈ e := him ▸ mem_image_of_mem γ hs
    have hsU : γ s ∈ D.U \ D.V := he.2.1 hse
    rw [hU, hV]
    refine ⟨hsU.1, ?_⟩
    rintro (h | ⟨f, hf, hfe⟩)
    · exact hsU.2 h
    · have hee : f = e := D.edge_eq_of_mem hf he (hfe ▸ hm f hf) hse
      subst hee
      exact hst (hi hs ht₀ (hfe.symm.trans hγt.symm))
  have hsubF : γ '' Ioo a b ⊆ D₂.U \ D₂.V := by
    rintro _ ⟨s, hs, rfl⟩
    exact hoff s (hsub hs) fun h => hne (h ▸ hs)
  refine ⟨(nonempty_Ioo.mpr hab).image γ, hsubF, isPathConnected_image_Ioo hγ hab, ?_⟩
  intro C hCF hCp hsubC
  obtain ⟨s₀, hs₀⟩ := nonempty_Ioo.mpr hab
  have hs₀e : γ s₀ ∈ e := him ▸ mem_image_of_mem γ (hsub hs₀)
  have hF : D₂.U \ D₂.V ⊆ D.U \ D.V := by
    rw [hU, hV]
    exact fun x hx => ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
  have hCe : C ⊆ e := by
    have hunion : IsPathConnected (e ∪ C) :=
      he.2.2.1.union hCp ⟨γ s₀, hs₀e, hsubC (mem_image_of_mem γ hs₀)⟩
    have := he.2.2.2 _ (union_subset he.2.1 (hCF.trans hF)) hunion subset_union_left
    exact this ▸ subset_union_right
  have hmC : m e ∉ C := fun h => (hCF h).2 (hV ▸ Or.inr ⟨e, he, rfl⟩)
  -- `C` lies in one of the two closed halves.
  have hcl₁ : IsClosed (γ '' Icc 0 t₀) := (isCompact_Icc.image hγ).isClosed
  have hcl₂ : IsClosed (γ '' Icc t₀ 1) := (isCompact_Icc.image hγ).isClosed
  have hcov : C ⊆ γ '' Icc 0 t₀ ∪ γ '' Icc t₀ 1 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := him ▸ hCe hx
    rcases le_total s t₀ with h | h
    · exact Or.inl ⟨s, ⟨hs.1.le, h⟩, rfl⟩
    · exact Or.inr ⟨s, ⟨h, hs.2.le⟩, rfl⟩
  have hIoo : ∀ {u : I}, γ u ∈ e → u ∈ Ioo (0 : I) 1 := by
    intro u hu
    have hnV := (he.2.1 hu).2
    refine ⟨unitInterval.pos_iff_ne_zero.mpr fun h => hnV (by rw [h]; exact h0),
      lt_of_le_of_ne (unitInterval.le_one u) fun h => hnV (by rw [h]; exact h1)⟩
  have hdisj : ∀ x ∈ C, x ∈ γ '' Icc 0 t₀ → x ∈ γ '' Icc t₀ 1 → False := by
    rintro _ hx ⟨s, hs, rfl⟩ ⟨s', hs', hss⟩
    have heq := hi (hIoo (hss ▸ hCe hx)) (hIoo (hCe hx)) hss
    have hst : s = t₀ := le_antisymm hs.2 (heq ▸ hs'.1)
    rw [hst, hγt] at hx
    exact hmC hx
  have hpre := hCp.isConnected.isPreconnected
  have hwhich : C ⊆ γ '' Icc 0 t₀ ∨ C ⊆ γ '' Icc t₀ 1 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨hn₁, hn₂⟩ := hnot
    obtain ⟨x, hxC, hx₁⟩ := not_subset.mp hn₁
    obtain ⟨y, hyC, hy₂⟩ := not_subset.mp hn₂
    have hxb : x ∈ γ '' Icc t₀ 1 := (hcov hxC).resolve_left hx₁
    have hyb : y ∈ γ '' Icc 0 t₀ := (hcov hyC).resolve_right hy₂
    obtain ⟨z, hz, hz₁, hz₂⟩ := (isPreconnected_closed_iff.mp hpre) _ _ hcl₁ hcl₂ hcov ⟨y, hyC,
      hyb⟩ ⟨x, hxC, hxb⟩
    exact hdisj z hz hz₁ hz₂
  apply subset_antisymm _ hsubC
  have hs₀C : γ s₀ ∈ C := hsubC (mem_image_of_mem γ hs₀)
  -- A point of `C` in a closed half, with parameter in `Ioo 0 1`.
  have hpar : ∀ {K : Set I} {x : S}, x ∈ C → x ∈ γ '' K → ∃ u ∈ K, u ∈ Ioo (0 : I) 1 ∧ γ u = x := by
    rintro K _ hx ⟨u, hu, rfl⟩
    exact ⟨u, hu, hIoo (hCe hx), rfl⟩
  intro x hx
  have hne' : x ≠ γ t₀ := fun h => hmC (by rw [← hγt, ← h]; exact hx)
  have hneu : ∀ u, γ u = x → u ≠ t₀ := fun u hu h => hne' (by rw [← hu, h])
  rcases hend with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hwhich with h | h
    · obtain ⟨u, hu, hu₀, rfl⟩ := hpar hx (h hx)
      exact ⟨u, ⟨hu₀.1, lt_of_le_of_ne hu.2 (hneu u rfl)⟩, rfl⟩
    · obtain ⟨u, hu, hu₀, hue⟩ := hpar hs₀C (h hs₀C)
      obtain rfl := hi hu₀ (hsub hs₀) hue
      exact (not_lt.mpr hu.1 hs₀.2).elim
  · rcases hwhich with h | h
    · obtain ⟨u, hu, hu₀, hue⟩ := hpar hs₀C (h hs₀C)
      obtain rfl := hi hu₀ (hsub hs₀) hue
      exact (not_lt.mpr hu.2 hs₀.1).elim
    · obtain ⟨u, hu, hu₀, rfl⟩ := hpar hx (h hx)
      exact ⟨u, ⟨lt_of_le_of_ne hu.1 (Ne.symm (hneu u rfl)), hu₀.2⟩, rfl⟩

/-- **Splitting each edge at a new vertex.** Each edge `e` splits into edges `A e`, `B e` at the new
vertex `m e`, and these are all the new edges. Each closure meets the new vertices in two distinct
points
`x, m e` or `m e, y`, where `x, y` are the ends of `e`. -/
theorem exists_split_at [Nonempty S] (D : Drawing S) (m : Set S → S) (hm₀ : ∀ e ∈ D.E, m e ∈ e) :
    ∃ (D₂ : Drawing S) (A B : Set S → Set S) (x y : Set S → S), D₂.U = D.U ∧ D₂.V = D.V ∪ m '' D.E ∧
      (∀ e ∈ D.E, A e ∈ D₂.E ∧ B e ∈ D₂.E ∧ m e ∈ e ∧ m e ∉ A e ∧ m e ∉ B e ∧ Disjoint (A e) (B e) ∧
        e = A e ∪ {m e} ∪ B e ∧ x e ∈ D.V ∧ y e ∈ D.V ∧ closure e ∩ D.V = {x e, y e} ∧
        closure (A e) ∩ D₂.V = {x e, m e} ∧ closure (B e) ∩ D₂.V = {m e, y e}) ∧
      ∀ g ∈ D₂.E, ∃ e ∈ D.E, g = A e ∨ g = B e := by
  classical
  have key : ∀ e ∈ D.E, ∃ (γ : I → S) (t₀ : I), Continuous γ ∧ γ 0 ∈ D.V ∧ γ 1 ∈ D.V ∧
      InjOn γ (Ioo 0 1) ∧ γ '' Ioo 0 1 = e ∧ t₀ ∈ Ioo (0 : I) 1 ∧ γ t₀ = m e := by
    intro e he
    obtain ⟨γ, hc, h0, h1, hi, him⟩ := exists_edge_param D he
    have hme : m e ∈ γ '' Ioo 0 1 := him.symm ▸ hm₀ e he
    obtain ⟨t, ht, htm⟩ := hme
    exact ⟨γ, t, hc, h0, h1, hi, him, ht, htm⟩
  choose! γ t₀ hc h0 h1 hi him ht htm using key
  have hm : ∀ e ∈ D.E, m e ∈ e := hm₀
  obtain ⟨D₂, hU, hV⟩ := exists_added_vertices D hm
  let A : Set S → Set S := fun e => γ e '' Ioo 0 (t₀ e)
  let B : Set S → Set S := fun e => γ e '' Ioo (t₀ e) 1
  have hAE : ∀ e ∈ D.E, A e ∈ D₂.E := fun e he => piece_mem hm hU hV he (hc e he) (h0 e he)
    (h1 e he)
    (hi e he) (him e he) (ht e he) (htm e he) (ht e he).1 bot_le (unitInterval.le_one _) (fun h
      => lt_irrefl _ h.2)
    (Or.inl ⟨rfl, rfl⟩)
  have hBE : ∀ e ∈ D.E, B e ∈ D₂.E := fun e he => piece_mem hm hU hV he (hc e he) (h0 e he)
    (h1 e he)
    (hi e he) (him e he) (ht e he) (htm e he) (ht e he).2 (unitInterval.nonneg _) le_rfl (fun h
      => lt_irrefl _ h.1)
    (Or.inr ⟨rfl, rfl⟩)
  have hAsub : ∀ e ∈ D.E, Ioo 0 (t₀ e) ⊆ Ioo (0 : I) 1 := fun e he => Ioo_subset_Ioo_right
    (ht e he).2.le
  have hBsub : ∀ e ∈ D.E, Ioo (t₀ e) 1 ⊆ Ioo (0 : I) 1 := fun e he => Ioo_subset_Ioo_left
    (ht e he).1.le
  have hsplit : ∀ e ∈ D.E, e = A e ∪ {m e} ∪ B e := by
    intro e he
    apply subset_antisymm
    · intro p hp
      obtain ⟨s, hs, rfl⟩ := him e he ▸ hp
      rcases lt_trichotomy s (t₀ e) with h | h | h
      · exact Or.inl (Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩)
      · exact Or.inl (Or.inr (by rw [h]; exact htm e he))
      · exact Or.inr ⟨s, ⟨h, hs.2⟩, rfl⟩
    · have hsub : ∀ s ∈ Ioo (0 : I) 1, γ e s ∈ e := fun s hs => by
        have := mem_image_of_mem (γ e) hs
        rwa [him e he] at this
      rintro _ ((⟨s, hs, rfl⟩ | rfl) | ⟨s, hs, rfl⟩)
      · exact hsub s (hAsub e he hs)
      · exact hm e he
      · exact hsub s (hBsub e he hs)
  have hmA : ∀ e ∈ D.E, m e ∉ A e := by
    rintro e he ⟨s, hs, hse⟩
    exact hs.2.ne (hi e he (hAsub e he hs) (ht e he) (hse.trans (htm e he).symm))
  have hmB : ∀ e ∈ D.E, m e ∉ B e := by
    rintro e he ⟨s, hs, hse⟩
    exact hs.1.ne' (hi e he (hBsub e he hs) (ht e he) (hse.trans (htm e he).symm))
  have hAB : ∀ e ∈ D.E, Disjoint (A e) (B e) := by
    intro e he
    refine disjoint_left.mpr ?_
    rintro _ ⟨s, hs, rfl⟩ ⟨s', hs', hse⟩
    have := hi e he (hBsub e he hs') (hAsub e he hs) hse
    exact absurd (hs.2.trans hs'.1) (by rw [this]; exact lt_irrefl _)
  have hVm : ∀ e ∈ D.E, m e ∈ D₂.V := fun e he => hV ▸ Or.inr ⟨e, he, rfl⟩
  have hclA : ∀ e ∈ D.E, closure (A e) ∩ D₂.V = {γ e 0, m e} := by
    intro e he
    have hcl := closure_image_Ioo (hc e he) (ht e he).1
    apply subset_antisymm
    · rintro p ⟨hp, hpV⟩
      rw [hcl] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      by_cases h0' : s = 0
      · simp [h0']
      by_cases h1' : s = t₀ e
      · simp [h1', htm e he]
      exact (((hAE e he).2.1 ⟨s, ⟨unitInterval.pos_iff_ne_zero.mpr h0', lt_of_le_of_ne hs.2 h1'⟩,
        rfl⟩).2
        hpV).elim
    · rw [hcl]
      rintro _ (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, (ht e he).1.le⟩, rfl⟩, hV ▸ Or.inl (h0 e he)⟩
      · exact ⟨⟨t₀ e, ⟨(ht e he).1.le, le_rfl⟩, htm e he⟩, hVm e he⟩
  have hclB : ∀ e ∈ D.E, closure (B e) ∩ D₂.V = {m e, γ e 1} := by
    intro e he
    have hcl := closure_image_Ioo (hc e he) (ht e he).2
    apply subset_antisymm
    · rintro p ⟨hp, hpV⟩
      rw [hcl] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      by_cases h0' : s = t₀ e
      · simp [h0', htm e he]
      by_cases h1' : s = 1
      · simp [h1']
      exact (((hBE e he).2.1 ⟨s, ⟨lt_of_le_of_ne hs.1 (Ne.symm h0'), lt_of_le_of_ne hs.2 h1'⟩,
        rfl⟩).2
        hpV).elim
    · rw [hcl]
      rintro _ (rfl | rfl)
      · exact ⟨⟨t₀ e, ⟨le_rfl, (ht e he).2.le⟩, htm e he⟩, hVm e he⟩
      · exact ⟨⟨1, ⟨(ht e he).2.le, le_rfl⟩, rfl⟩, hV ▸ Or.inl (h1 e he)⟩
  have hclE : ∀ e ∈ D.E, closure e ∩ D.V = {γ e 0, γ e 1} := by
    intro e he
    have hcl : closure e = γ e '' Icc 0 1 := by
      conv_lhs => rw [← him e he]
      exact closure_image_Ioo (hc e he) zero_lt_one
    apply subset_antisymm
    · rintro p ⟨hp, hpV⟩
      rw [hcl] at hp
      obtain ⟨s, hs, rfl⟩ := hp
      by_cases h0' : s = 0
      · simp [h0']
      by_cases h1' : s = 1
      · simp [h1']
      have hmem : γ e s ∈ e := by
        have := mem_image_of_mem (γ e) (show s ∈ Ioo (0 : I) 1 from
          ⟨unitInterval.pos_iff_ne_zero.mpr h0', lt_of_le_of_ne hs.2 h1'⟩)
        rwa [him e he] at this
      exact ((he.2.1 hmem).2 hpV).elim
    · rw [hcl]
      rintro _ (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, h0 e he⟩
      · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, h1 e he⟩
  refine ⟨D₂, A, B, fun e => γ e 0, fun e => γ e 1, hU, hV, fun e he => ⟨hAE e he, hBE e he,
    hm e he,
    hmA e he, hmB e he, hAB e he, hsplit e he, h0 e he, h1 e he, hclE e he, hclA e he, hclB e he⟩,
      ?_⟩
  intro g hg
  obtain ⟨z, hz⟩ := hg.1
  have hzF := hg.2.1 hz
  have hzU : z ∈ D.U := hU ▸ hzF.1
  have hzV : z ∉ D.V := fun h => hzF.2 (hV ▸ Or.inl h)
  rw [D.U_eq] at hzU
  obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp (hzU.resolve_left hzV)
  have hzee : z ∈ e := D.closure_diff_V he ▸ (⟨hze, hzV⟩ : z ∈ closure e \ D.V)
  refine ⟨e, he, ?_⟩
  rw [hsplit e he] at hzee
  rcases hzee with (h | h) | h
  · exact Or.inl (D₂.edge_eq_of_mem hg (hAE e he) hz h)
  · exact (hzF.2 (by rw [mem_singleton_iff.mp h]; exact hVm e he)).elim
  · exact Or.inr (D₂.edge_eq_of_mem hg (hBE e he) hz h)

/-- `exists_split_at`, with the point `m e` chosen freely. -/
theorem exists_split [Nonempty S] (D : Drawing S) :
    ∃ (D₂ : Drawing S) (A B : Set S → Set S) (m x y : Set S → S), D₂.U = D.U ∧ D₂.V
      = D.V ∪ m '' D.E ∧
      (∀ e ∈ D.E, A e ∈ D₂.E ∧ B e ∈ D₂.E ∧ m e ∈ e ∧ m e ∉ A e ∧ m e ∉ B e ∧ Disjoint (A e) (B e) ∧
        e = A e ∪ {m e} ∪ B e ∧ x e ∈ D.V ∧ y e ∈ D.V ∧ closure e ∩ D.V = {x e, y e} ∧
        closure (A e) ∩ D₂.V = {x e, m e} ∧ closure (B e) ∩ D₂.V = {m e, y e}) ∧
      ∀ g ∈ D₂.E, ∃ e ∈ D.E, g = A e ∨ g = B e := by
  have key : ∀ e ∈ D.E, ∃ x, x ∈ e := fun e he => he.1
  choose! m hm using key
  obtain ⟨D₂, A, B, x, y, h⟩ := exists_split_at D m hm
  exact ⟨D₂, A, B, m, x, y, h⟩

end GraphMinor.GM11
