/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.ReplaceDisc
public import LeanPool.GraphMinor.Surface.Crossing

/-!
# Marked nodes on an arc of a cuff

This file has the tools for `NormalIArcDiscRegionStatement`: a choice of a gap in a noncrossing
partition (`exists_gap`), and the circular
order of points along an arc of an `O`-arc (`inOrder_of_arc`).
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface

/-- Let `R` be an equivalence relation on a finite linear order whose classes do not cross, and let
`P` be constant on classes, true at the
least point and false at the last point. Then there is a pair of consecutive points with `P` true
and false, and no class has points on
both sides of the pair. -/
theorem exists_gap {α : Type*} [LinearOrder α] (T : Finset α) (R : α → α → Prop) (P : α → Prop)
  (hrefl : ∀ a ∈ T, R a a)
    (_hsymm : ∀ a b, R a b → R b a) (htrans : ∀ a b c, R a b → R b c → R a c)
      (hP : ∀ a ∈ T, ∀ b ∈ T, R a b → P a → P b)
    (hcross : ∀ a ∈ T, ∀ b ∈ T, ∀ a' ∈ T, ∀ b' ∈ T, a < b → b < a' → a' < b' → R a a' → R b b'
      → R a b) {t₀ t₁ : α} (h₀ : t₀ ∈ T) (h₁ : t₁ ∈ T)
    (hmin : ∀ t ∈ T, t₀ ≤ t) (hmax : ∀ t ∈ T, t ≤ t₁) (hP₀ : P t₀) (hP₁ : ¬ P t₁) :
    ∃ p ∈ T, ∃ q ∈ T, p < q ∧ P p ∧ ¬ P q ∧ (∀ t ∈ T, t ≤ p ∨ q ≤ t) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≤ p → q
      ≤ b → ¬ R a b := by
  classical
  have hclosed : ∀ s ∈ T, (∀ a ∈ T, ∀ b ∈ T, a ≤ s → s < b → R s a → False) → True := fun _ _ _
    => trivial
  have hM : ∀ s ∈ T, ∃ m ∈ T, R s m ∧ ∀ b ∈ T, R s b → b ≤ m := fun s hs => by
    have hne : (T.filter (R s)).Nonempty := ⟨s, by simp [hs, hrefl s hs]⟩
    refine ⟨(T.filter (R s)).max' hne, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).1,
      (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, fun b hb hR => ?_⟩
    exact Finset.le_max' _ _ (by simp [hb, hR])
  let Cl : α → Prop := fun s => ∀ a ∈ T, ∀ b ∈ T, a ≤ s → s < b → ¬ R a b
  obtain ⟨p₀, hp₀, hRp₀, hmaxp₀⟩ := hM t₀ h₀
  have hstep : ∀ s ∈ T, ∀ r ∈ T, s ≤ r → R s r → (∀ b ∈ T, R s b → b ≤ r) →
    (∀ a ∈ T, ∀ b ∈ T, a < s → r < b → ¬ R a b) → Cl r := by
    intro s hs r hr hsr hR hm hlow a ha b hb har hrb hab
    rcases lt_or_ge a s with h | h
    · exact hlow a ha b hb h hrb hab
    rcases eq_or_lt_of_le h with rfl | h
    · exact absurd (hm b hb hab) (not_le.mpr hrb)
    rcases eq_or_lt_of_le har with rfl | h'
    · exact absurd (hm b hb (htrans _ _ _ hR hab)) (not_le.mpr hrb)
    have h3 := hcross s hs a ha r hr b hb h h' hrb hR hab
    exact absurd (hm b hb (htrans _ _ _ h3 hab)) (not_le.mpr hrb)
  have hCp₀ : Cl p₀ := hstep t₀ h₀ p₀ hp₀ (hmin _ hp₀) hRp₀ hmaxp₀ fun a ha b hb h => absurd
    (hmin a ha) (not_le.mpr h)
  have hne : (T.filter fun s => P s ∧ Cl s).Nonempty := by
    exact ⟨p₀, Finset.mem_filter.mpr ⟨hp₀, hP _ h₀ _ hp₀ hRp₀ hP₀, hCp₀⟩⟩
  let p := (T.filter fun s => P s ∧ Cl s).max' hne
  have hpm := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  have hpT : p ∈ T := hpm.1
  have hpP : P p := hpm.2.1
  have hpC : Cl p := hpm.2.2
  have hplt : p < t₁ := lt_of_le_of_ne (hmax p hpT) fun h => hP₁ (h ▸ hpP)
  have hne2 : (T.filter fun s => p < s).Nonempty :=
    ⟨t₁, Finset.mem_filter.mpr ⟨h₁, hplt⟩⟩
  let q := (T.filter fun s => p < s).min' hne2
  have hqm := Finset.mem_filter.mp (Finset.min'_mem _ hne2)
  have hqT : q ∈ T := hqm.1
  have hpq : p < q := hqm.2
  have hgap : ∀ t ∈ T, t ≤ p ∨ q ≤ t := fun t ht => by
    rcases le_or_gt t p with h | h
    · exact .inl h
    · exact .inr (Finset.min'_le _ _ (by simp only [Finset.mem_filter]; exact ⟨ht, h⟩))
  have hPq : ¬ P q := by
    intro hq
    obtain ⟨r, hr, hRr, hmr⟩ := hM q hqT
    have hqr : q ≤ r := hmr q hqT (hrefl q hqT)
    have hCr : Cl r := hstep q hqT r hr hqr hRr hmr fun a ha b hb h hrb hab => by
      refine hpC a ha b hb ?_ (lt_of_lt_of_le hpq (hqr.trans hrb.le)) hab
      exact (hgap a ha).resolve_right (not_le.mpr h)
    have h3 : r ≤ p := Finset.le_max' _ _ (by simp only [Finset.mem_filter]; exact ⟨hr, hP _ hqT _
      hr hRr hq, hCr⟩)
    exact absurd (lt_of_lt_of_le hpq hqr) (not_lt.mpr h3)
  exact ⟨p, hpT, q, hqT, hpq, hpP, hPq, hgap, fun a ha b hb h3 h4 => hpC a ha b hb h3
    (lt_of_lt_of_le hpq h4)⟩

variable {S : Type} [TopologicalSpace S]

/-- The part of an arc between two parameters is a line. -/
theorem isLine_piece [T2Space S] {a : unitInterval → S} (ha : IsArcMap a) {s r : unitInterval}
  (h : s < r) :
    IsLineWithEnds (a '' Icc s r) (a s) (a r) := by
  have h1 := (isArcMap_pieceA ha s.2.1 (Subtype.coe_lt_coe.mpr h) r.2.2).isLineWithEnds
  rw [pieceA_zero, pieceA_one, extI_coe, extI_coe, range_pieceA a s.2.1
    (Subtype.coe_lt_coe.mpr h).le r.2.2] at h1
  convert h1 using 1
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ⟨ht.1, ht.2⟩, extI_coe a t⟩
  · rintro ⟨t, ht, rfl⟩
    have ht0 : t ∈ Icc (0 : ℝ) 1 := ⟨s.2.1.trans ht.1, ht.2.trans r.2.2⟩
    exact ⟨⟨t, ht0⟩, ⟨ht.1, ht.2⟩, (extI_of_mem a ht0).symm⟩

/-- Points along an arc of an `O`-arc are in circular order. -/
theorem inOrder_of_arc [T2Space S] {Θ : Set S} (hO : IsOArc Θ) {a : unitInterval → S}
  (ha : IsArcMap a) (hs : ∀ t, a t ∈ Θ)
    {s₁ s₂ s₃ s₄ : unitInterval} (h12 : s₁ ≤ s₂) (h23 : s₂ ≤ s₃) (h34 : s₃ ≤ s₄) : GM19.InOrderOn Θ
      (a s₁) (a s₂) (a s₃) (a s₄) := by
  rcases eq_or_lt_of_le (h12.trans h23) with h | h
  · obtain rfl : s₁ = s₂ := le_antisymm h12 (h23.trans h.ge)
    obtain rfl : s₁ = s₃ := h
    obtain ⟨f⟩ := id hO
    obtain ⟨t, -, e⟩ := exists_cuffPoint_mem_Ico f 0 (hs s₁)
    obtain ⟨t', ht', e'⟩ := exists_cuffPoint_mem_Ico f t (hs s₄)
    exact ⟨f, t, t, t, t', le_rfl, le_rfl, ht'.1, ht'.2.le, e, e, e, e'⟩
  · have hL := isLine_piece ha h
    obtain ⟨L', hL', hu, -⟩ := oarc_split hO hL (by rintro _ ⟨t, -, rfl⟩; exact hs t)
    refine inOrder_of_lines hO hL hL' hu ⟨s₂, ⟨h12, h23⟩, rfl⟩ ?_
    rcases eq_or_lt_of_le h34 with rfl | h3
    · exact hL'.right_mem
    · have h5 : a s₄ ∈ a '' Icc s₁ s₃ ∪ L' := hu ▸ hs s₄
      refine h5.resolve_left ?_
      rintro ⟨t, ht, he⟩
      have h6 := ha.2 he
      exact absurd (h6 ▸ ht.2) (not_le.mpr h3)

/-- Two points on opposite lines of a circle cross the ends of the lines. -/
theorem pairsCross_of_lines [T2Space S] {C J₁ J₂ : Set S} {x y b d : S}
  (hJ₁ : IsLineWithEnds J₁ x y) (hJ₂ : IsLineWithEnds J₂ x y) (hu : J₁ ∪ J₂ = C)
    (hi : J₁ ∩ J₂ = {x, y}) (hb : b ∈ J₁) (hd : d ∈ J₂) (hbx : b ≠ x) (hby : b ≠ y) (hdx : d ≠ x)
      (hdy : d ≠ y) : PairsCrossOn C x y b d := by
  have hbC : b ∈ C := hu ▸ .inl hb
  have hdC : d ∈ C := hu ▸ .inr hd
  have hne : b ≠ d := by
    rintro rfl
    have h3 : b ∈ J₁ ∩ J₂ := ⟨hb, hd⟩
    rw [hi] at h3
    rcases h3 with h3 | h3
    · exact hbx h3
    · exact hby h3
  refine ⟨hu ▸ .inl hJ₁.left_mem, hbC, hu ▸ .inl hJ₁.right_mem, hdC, hJ₁.ne', hne, hbx.symm,
    hdx.symm, hby.symm, hdy.symm, fun he => ?_⟩
  have hbm : b ∈ C \ {x, y} := ⟨hbC, by rintro (h | h); exacts [hbx h, hby h]⟩
  have hdm : d ∈ C \ {x, y} := ⟨hdC, by rintro (h | h); exacts [hdx h, hdy h]⟩
  have hd' : d ∈ connectedComponentIn (C \ {x, y}) b := he ▸ mem_connectedComponentIn hdm
  have hsub := connectedComponentIn_subset (C \ {x, y}) b
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn J₁
    J₂ hJ₁.isCompact.isClosed hJ₂.isCompact.isClosed
    (fun z hz => hu ▸ (hsub hz).1) ⟨b, mem_connectedComponentIn hbm, hb⟩ ⟨d, hd', hd⟩
  exact (hsub hz).2 (hi ▸ ⟨hz₁, hz₂⟩)

/-- Two nodes are linked if a chain of cells of the family `G` joins them, where `e d` is what cell
`d` joins. -/
def Linked (G : Set (Set S)) (e : Set S → Set S) : S → S → Prop :=
  Relation.EqvGen fun u v => ∃ d ∈ G, u ∈ e d ∧ v ∈ e d

/-- The nodes in `Q` linked to `x`, with the cells that link them. -/
def linkedPart (Q : Set S) (G : Set (Set S)) (e : Set S → Set S) (x : S) : Set S :=
  {y ∈ Q | Linked G e x y} ∪ ⋃₀ {d ∈ G | ∃ y ∈ e d, Linked G e x y}

section

variable {Q : Set S} {G : Set (Set S)} {e : Set S → Set S}

omit [TopologicalSpace S] in
theorem Linked.mem_iff (hQ : ∀ d ∈ G, e d ⊆ Q) {u v : S} (h : Linked G e u v) : u ∈ Q ↔ v ∈ Q := by
  induction h with
  | rel u v h =>
    obtain ⟨d, hd, hu, hv⟩ := h
    exact ⟨fun _ => hQ d hd hv, fun _ => hQ d hd hu⟩
  | refl u => rfl
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem linkedPart_isPathConnected (hQ : ∀ d ∈ G, e d ⊆ Q) (hG : ∀ d ∈ G, IsPathConnected
  (d ∪ e d)) {x : S} (hx : x ∈ Q) :
    IsPathConnected (linkedPart Q G e x) := by
  set P := linkedPart Q G e x with hP
  have hcell : ∀ d ∈ G, ∀ y ∈ e d, Linked G e x y → d ∪ e d ⊆ P := by
    intro d hd y hy hl z hz
    rcases hz with hz | hz
    · exact .inr ⟨d, ⟨hd, y, hy, hl⟩, hz⟩
    · exact .inl ⟨hQ d hd hz, hl.trans _ _ _ (.rel _ _ ⟨d, hd, hy, hz⟩)⟩
  have key : ∀ u v, Linked G e u v → Linked G e x u → JoinedIn P u v := by
    intro u v h
    induction h with
    | rel u v h =>
      intro hl
      obtain ⟨d, hd, hu, hv⟩ := h
      exact ((hG d hd).joinedIn u (.inr hu) v (.inr hv)).mono (hcell d hd u hu hl)
    | refl u =>
      intro hl
      exact JoinedIn.refl (.inl ⟨(hl.mem_iff hQ).mp hx, hl⟩)
    | symm u v h ih =>
      intro hl
      exact (ih (hl.trans _ _ _ (.symm _ _ h))).symm
    | trans u v w h _ ih₁ ih₂ =>
      intro hl
      exact (ih₁ hl).trans (ih₂ (hl.trans _ _ _ h))
  refine ⟨x, .inl ⟨hx, .refl _⟩, fun y hy => ?_⟩
  rcases hy with hy | ⟨d, ⟨hd, z, hz, hl⟩, hy⟩
  · exact key x y hy.2 (.refl _)
  · exact (key x z hl (.refl _)).trans (((hG d hd).joinedIn z (.inr hz) y (.inl hy)).mono
    (hcell d hd z hz hl))

omit [TopologicalSpace S] in
/-- Two parts meet only if they are parts of one class. -/
theorem linked_of_part (hQ : Disjoint Q (⋃₀ G)) (hdis : G.PairwiseDisjoint id) {x x' z : S}
  (hz : z ∈ linkedPart Q G e x) (hz' : z ∈ linkedPart Q G e x') :
    Linked G e x x' := by
  rcases hz with hz | ⟨d, ⟨hd, y, hy, hl⟩, hzd⟩
  · rcases hz' with hz' | ⟨d, ⟨hd, -⟩, hzd⟩
    · exact hz.2.trans _ _ _ (.symm _ _ hz'.2)
    · exact absurd (subset_sUnion_of_mem hd hzd) (disjoint_left.mp hQ hz.1)
  · rcases hz' with hz' | ⟨d', ⟨hd', y', hy', hl'⟩, hzd'⟩
    · exact absurd (subset_sUnion_of_mem hd hzd) (disjoint_left.mp hQ hz'.1)
    · have hdd : d = d' := by
        by_contra hne
        exact disjoint_left.mp (hdis hd hd' hne) hzd hzd'
      subst hdd
      exact (hl.trans _ _ _ (.rel _ _ ⟨d, hd, hy, hy'⟩)).trans _ _ _ (.symm _ _ hl')

end

/-- Two linked pairs whose endpoints alternate on a disc boundary belong to the same
linked component. -/
theorem linked_of_alternating_ends {S : Type} [TopologicalSpace S] [T2Space S]
    {Δ : Set S} (hΔ : IsClosedDisc Δ) {G : Set (Set S)} {e : Set S → Set S} {Q : Set S}
    (hQΔ : Q ⊆ Δ) (hGΔ : ∀ d ∈ G, d ⊆ Δ)
    (hGQ : ∀ d ∈ G, e d ⊆ Q) (hGpc : ∀ d ∈ G, IsPathConnected (d ∪ e d))
    (hQdis : Disjoint Q (⋃₀ G)) (hGdis : G.PairwiseDisjoint id)
    {α : unitInterval → S} (ha : IsArcMap α) (hαbd : ∀ t, α t ∈ discBd Δ)
    {T : Finset unitInterval} (hαQ : ∀ t ∈ T, α t ∈ Q) :
    ∀ a ∈ T, ∀ b ∈ T, ∀ a' ∈ T, ∀ b' ∈ T,
      a < b → b < a' → a' < b' → Linked G e (α a) (α a') →
        Linked G e (α b) (α b') → Linked G e (α a) (α b) := by
  intro a ha' b hb' a' ha'' b' hb'' hab hba hab' hla hlb
  have hJ := isLine_piece ha (hab.trans hba)
  have hO : IsOArc (discBd Δ) := hΔ.isOArc_discBd
  have hJs : α '' Icc a a' ⊆ discBd Δ := by
    rintro _ ⟨t, -, rfl⟩
    exact hαbd t
  obtain ⟨J₂, hJ₂, hJu, hJi⟩ := oarc_split hO hJ hJs
  have hb1 : α b' ∈ α '' Icc a a' ∪ J₂ := hJu ▸ hαbd b'
  have hb2 : α b' ∈ J₂ := hb1.resolve_left fun ⟨t, ht, h9⟩ => absurd (ha.2 h9 ▸ ht.2)
    (not_le.mpr hab')
  have hcr := pairsCross_of_lines hJ hJ₂ hJu hJi ⟨b, ⟨hab.le, hba.le⟩, rfl⟩ hb2 (fun h9 => hab.ne
    (ha.2 h9).symm)
    (fun h9 => hba.ne (ha.2 h9)) (fun h9 => (hab.trans (hba.trans hab')).ne (ha.2 h9).symm)
      (fun h9 => hab'.ne (ha.2 h9).symm)
  have hQa : α a ∈ Q := hαQ a ha'
  have hQb : α b ∈ Q := hαQ b hb'
  have hsubP : ∀ x ∈ Q, linkedPart Q G e x ⊆ Δ := fun x _ => by
    rintro z (hz | ⟨d, hd, hz⟩)
    · exact hQΔ hz.1
    · exact hGΔ d hd.1 hz
  obtain ⟨z, hz, hz'⟩ := disc_crossing.of_isPathConnected Δ _ _ (α a) (α a') (α b) (α b') hΔ
    (hsubP _ hQa) (hsubP _ hQb)
    (linkedPart_isPathConnected hGQ hGpc hQa) (linkedPart_isPathConnected hGQ hGpc hQb)
    (.inl ⟨hQa, .refl _⟩) (.inl ⟨hαQ a' ha'', hla⟩) (.inl ⟨hQb, .refl _⟩)
      (.inl ⟨hαQ b' hb'', hlb⟩) hcr
  exact linked_of_part hQdis hGdis hz hz'

/-- The surface part of (7.3) of Graph Minors XVII, page 179. Among the marked nodes on the arc `I`
we pick a place where marked meets unmarked,
in a gap that no linked pair spans. Linked pairs do not cross because of the crossing theorem for a
disc. -/
theorem normalIArcDiscRegion_of_boundary
    (S : Type) [TopologicalSpace S] (hS : IsSurface S)
    (Γ : Painting S) (Θ : Set S) (n₁ n₂ : S) (F Δ : Set S)
    (e : Set S → Set S) (P_mark : S → Prop)
    (hΘ : Θ ∈ cuffs S) (hn₁ : n₁ ∈ Γ.N ∩ Θ) (hn₂ : n₂ ∈ Γ.N ∩ Θ) (hne : n₁ ≠ n₂)
    (hnorm : Γ.IsNormal F) (hF : IsLineWithEnds F n₁ n₂) (hb : F ∩ bd S = {n₁, n₂})
    (hΔ : IsClosedDisc Δ) (h1 : F ⊆ discBd Δ) (h2 : discBd Δ ⊆ F ∪ Θ)
    (he : ∀ d ∈ Γ.C, d ⊆ Δ → ¬ (d ∩ bd S).Nonempty →
      e d ⊆ tilde d ∧ (e d = ∅ ∨ 2 ≤ (e d).ncard) ∧
      ∀ x ∈ e d, ∀ y ∈ e d, P_mark x → P_mark y)
    (hP₁ : P_mark n₁) (hP₂ : ¬ P_mark n₂) :
    ∃ (m₁ m₂ : S) (c I₁ I₂ N₁ N₂ : Set S),
      m₁ ∈ Γ.N ∩ (Θ ∩ discBd Δ) ∧ m₂ ∈ Γ.N ∩ (Θ ∩ discBd Δ) ∧ m₁ ≠ m₂ ∧
      P_mark m₁ ∧ ¬ P_mark m₂ ∧
      c ∈ Γ.C ∧ c ⊆ Δ ∧ (c ∩ Θ).Nonempty ∧ tilde c = {m₁, m₂} ∧
      I₁ ⊆ Θ ∩ discBd Δ ∧ I₂ ⊆ Θ ∩ discBd Δ ∧ Disjoint I₁ I₂ ∧
      n₁ ∈ I₁ ∧ m₁ ∈ I₁ ∧ m₂ ∈ I₂ ∧ n₂ ∈ I₂ ∧
      N₁ ⊆ (Γ.N ∩ Δ) \ bd S ∧ N₂ ⊆ (Γ.N ∩ Δ) \ bd S ∧ Disjoint N₁ N₂ ∧
      (∀ n ∈ I₁ ∩ Γ.N, ∀ n' ∈ I₂ ∩ Γ.N,
        (n ≠ n₁ → n ≠ m₁ → GM19.InOrderOn Θ n₁ n m₁ n') ∧
        (m₁ ≠ n₁ → n' ≠ n₂ → GM19.InOrderOn Θ n₁ m₁ n' n₂) ∧
        (n' ≠ m₂ → n' ≠ n₂ → GM19.InOrderOn Θ n m₂ n' n₂) ∧
        (n ≠ n₁ → m₂ ≠ n₂ → GM19.InOrderOn Θ n₁ n m₂ n₂)) ∧
      (∀ d ∈ Γ.C, d ⊆ Δ → (d ∩ bd S).Nonempty → d ≠ c →
        tilde d ⊆ I₁ ∨ tilde d ⊆ I₂) ∧
      (∀ d ∈ Γ.C, d ⊆ Δ → ¬ (d ∩ bd S).Nonempty →
        e d ⊆ N₁ ∪ I₁ ∨ e d ⊆ N₂ ∪ I₂) ∧
      (∃ c₁ ∈ Γ.C, c₁ ⊆ Δ ∧ (c₁ ∩ bd S).Nonempty ∧ n₁ ∈ tilde c₁) ∧
      (∃ c₂ ∈ Γ.C, c₂ ⊆ Δ ∧ (c₂ ∩ bd S).Nonempty ∧ n₂ ∈ tilde c₂) := by
  have ht2 : T2Space S := hS.2.1
  have hΘb : Θ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hΘ
    exact connectedComponentIn_subset _ _
  obtain ⟨I, I', Θ', hΘ', hI, hI', hu', hi', hu, hi, hmeet, hnb⟩ := arc_disc_data hS hF hb hΔ h1
    (h2.trans (union_subset_union_right _ hΘb))
  have hΘeq : Θ' = Θ := cuffs_disjoint_eq hΘ' hΘ (hu' ▸ .inl hI.left_mem) hn₁.2
  subst hΘeq
  have hcl := hΔ.isClosed
  have hIΘ : I ⊆ Θ' := fun z hz => hu' ▸ .inl hz
  have hbdΔ : discBd Δ ⊆ Δ := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hIbd : I ⊆ discBd Δ := fun z hz => hu ▸ .inr hz
  have hIΔ : I ⊆ Δ := hIbd.trans hbdΔ
  have hside : ∀ c ∈ Γ.C, c ⊆ Δ ∨ c ⊆ Δᶜ := fun c hc => cell_side hc hnorm hΔ hnb
  obtain ⟨c₁, hc₁, h3, h4, h5, -⟩ := exists_border_cell hI (hIΘ.trans hΘb) hIΔ hn₁.1 hside
  obtain ⟨c₂, hc₂, h6, h7, h8, -⟩ := exists_border_cell hI.symm (hIΘ.trans hΘb) hIΔ hn₂.1 hside
  let G : Set (Set S) := {d ∈ Γ.C | d ⊆ Δ ∧ ¬ (d ∩ bd S).Nonempty}
  let Q : Set S := Γ.N ∩ Δ
  have hGQ : ∀ d ∈ G, e d ⊆ Q := fun d hd x hx => by
    have h9 := (he d hd.1 hd.2.1 hd.2.2).1 hx
    exact ⟨Γ.tilde_subset_N hd.1 h9, closure_minimal hd.2.1 hcl h9.1⟩
  have hGpc : ∀ d ∈ G, IsPathConnected (d ∪ e d) := fun d hd => by
    have h9 := (he d hd.1 hd.2.1 hd.2.2).1
    refine isPathConnected_of_isClosedDisc_finite_diff (Γ.isClosedDisc_closure_cell hd.1)
      (union_subset subset_closure (h9.trans sdiff_subset)) (Γ.finite_N.subset fun x hx => ?_)
    refine Γ.tilde_subset_N hd.1 ⟨hx.1, fun h => hx.2 (.inl h)⟩
  have hQdis : Disjoint Q (⋃₀ G) := disjoint_left.mpr fun x hx ⟨d, hd, hxd⟩ =>
    (arcComponentsIn_subset hd.1 hxd).2 hx.1
  have hGdis : G.PairwiseDisjoint id := fun d hd d' hd' hne => arcComponentsIn_disjoint hd.1 hd'.1
    hne
  obtain ⟨α, ha, hr, rfl, rfl⟩ := hI.exists_arc
  have hαI : ∀ t, α t ∈ I := fun t => hr ▸ mem_range_self t
  have hTfin : (α ⁻¹' Γ.N).Finite := Γ.finite_N.preimage ha.2.injOn
  let T : Finset unitInterval := hTfin.toFinset
  have hT : ∀ {t}, t ∈ T ↔ α t ∈ Γ.N := by
    intro t
    exact hTfin.mem_toFinset
  have hPrel : ∀ u v, Linked G e u v → (P_mark u ↔ P_mark v) := by
    intro u v h
    induction h with
    | rel u v h =>
      obtain ⟨d, hd, hu, hv⟩ := h
      have h9 := (he d hd.1 hd.2.1 hd.2.2).2.2
      exact ⟨fun h => h9 u hu v hv h, fun h => h9 v hv u hu h⟩
    | refl u => rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hcross := linked_of_alternating_ends hΔ (G := G) (Q := Q) inter_subset_right
    (fun _ hd => hd.2.1) hGQ hGpc hQdis hGdis ha
    (fun t => hIbd (hαI t)) (T := T) (fun t ht => ⟨hT.mp ht, hIΔ (hαI t)⟩)
  obtain ⟨p, hp, q, hq, hpq, hPp, hPq, hgap, hnol⟩ := exists_gap T (fun s t => Linked G e (α s)
    (α t)) (fun s => P_mark (α s))
    (fun a _ => .refl _) (fun a b h => .symm _ _ h) (fun a b c h h' => .trans _ _ _ h h')
    (fun a _ b _ h => (hPrel _ _ h).mp) hcross (hT.mpr hn₁.1) (hT.mpr hn₂.1) (fun _ _
      => unitInterval.nonneg') (fun _ _ => unitInterval.le_one') hP₁ hP₂
  have hLZ := isLine_piece ha hpq
  obtain ⟨hZne, hZpc⟩ := isPathConnected_diff_ends_of_isLineWithEnds hLZ
  set Z := α '' Icc p q \ {α p, α q} with hZdef
  have hZt : ∀ z ∈ Z, ∃ t, p < t ∧ t < q ∧ α t = z := by
    rintro _ ⟨⟨t, ht, rfl⟩, h9⟩
    refine ⟨t, lt_of_le_of_ne ht.1 fun h => h9 (.inl (h ▸ rfl)), lt_of_le_of_ne ht.2 fun h => h9
      (.inr (h ▸ rfl)), rfl⟩
  have hnoN : ∀ t, p < t → t < q → α t ∉ Γ.N := fun t h9 h10 h => by
    rcases hgap t (hT.mpr h) with h11 | h11
    · exact absurd h11 (not_le.mpr h9)
    · exact absurd h11 (not_le.mpr h10)
  have hZsub : Z ⊆ Γ.U \ Γ.N := fun z hz => by
    obtain ⟨t, h9, h10, rfl⟩ := hZt z hz
    exact ⟨Γ.bd_subset (hΘb (hIΘ (hαI t))), hnoN t h9 h10⟩
  obtain ⟨z₀, hz₀⟩ := hZne
  obtain ⟨c, hc, hz₀c⟩ := exists_mem_arcComponentsIn (hZsub hz₀)
  have hZc : Z ⊆ c := subset_arcComponent_of_isPathConnected hc hZsub hZpc ⟨z₀, hz₀, hz₀c⟩
  have hz₀I : z₀ ∈ I := by
    obtain ⟨t, -, -, rfl⟩ := hZt z₀ hz₀
    exact hαI t
  have hcΔ : c ⊆ Δ := (hside c hc).resolve_right fun h => h hz₀c (hIΔ hz₀I)
  have hcb : (c ∩ bd S).Nonempty := ⟨z₀, hz₀c, hΘb (hIΘ hz₀I)⟩
  have htc : tilde c = {α p, α q} := by
    obtain ⟨u, v, huv, htilde, -, hdiff, -, -⟩ := Γ.border_cell_exists_ends hc hcb
    have hend : ∀ x ∈ α '' Icc p q, x ∈ Γ.N → x ∈ tilde c := fun x hx hxN =>
      ⟨closure_mono hZc (hLZ.subset_closure_diff hx), fun h => (arcComponentsIn_subset hc h).2 hxN⟩
    have h9 := hend _ hLZ.left_mem (hT.mp hp)
    have h10 := hend _ hLZ.right_mem (hT.mp hq)
    have hpq' : α p ≠ α q := hLZ.ne'
    rw [htilde] at h9 h10 ⊢
    rcases h9 with h9 | h9 <;> rcases h10 with h10 | h10
    · exact absurd (h9.trans h10.symm) hpq'
    · rw [h9, h10]
    · rw [h9, h10, pair_comm]
    · exact absurd (h9.trans h10.symm) hpq'
  have hIcl : ∀ s r : unitInterval, IsClosed (α '' Icc s r) := fun s r =>
    (isCompact_Icc.image ha.1).isClosed
  let I₁ : Set S := α '' Icc 0 p
  let I₂ : Set S := α '' Icc q 1
  have hI₁I : I₁ ⊆ I := by
    rintro _ ⟨t, -, rfl⟩
    exact hαI t
  have hI₂I : I₂ ⊆ I := by
    rintro _ ⟨t, -, rfl⟩
    exact hαI t
  have hI₁₂ : Disjoint I₁ I₂ := disjoint_left.mpr fun x ⟨t, ht, h9⟩ ⟨t', ht', h10⟩ => by
    have h11 := ha.2 (h9.trans h10.symm)
    exact absurd (ht.2.trans_lt (hpq.trans_le ht'.1)) (by rw [h11]; exact lt_irrefl _)
  have hnode : ∀ x ∈ Q, x ∉ bd S ∨ x ∈ I₁ ∨ x ∈ I₂ := fun x hx => by
    by_cases hxb : x ∈ bd S
    · right
      have h9 : x ∈ I := hmeet ▸ ⟨hx.2, hxb⟩
      rw [← hr] at h9
      obtain ⟨t, rfl⟩ := h9
      rcases hgap t (hT.mpr hx.1) with h10 | h10
      · exact .inl ⟨t, ⟨unitInterval.nonneg', h10⟩, rfl⟩
      · exact .inr ⟨t, ⟨h10, unitInterval.le_one'⟩, rfl⟩
    · exact .inl hxb
  have hnl : ∀ x ∈ I₁, ∀ y ∈ I₂, x ∈ Γ.N → y ∈ Γ.N → ¬ Linked G e x y := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hx hy
    exact hnol s (hT.mpr hx) t (hT.mpr hy) hs.2 ht.1
  let N₁ : Set S := {y ∈ (Γ.N ∩ Δ) \ bd S | ∃ w ∈ I₁ ∩ Γ.N, Linked G e w y}
  let N₂ : Set S := ((Γ.N ∩ Δ) \ bd S) \ N₁
  refine ⟨α p, α q, c, I₁, I₂, N₁, N₂, ⟨hT.mp hp, hIΘ (hαI p), hIbd (hαI p)⟩, ⟨hT.mp hq,
    hIΘ (hαI q), hIbd (hαI q)⟩, hLZ.ne', hPp, hPq, hc, hcΔ,
    ⟨z₀, hz₀c, hIΘ hz₀I⟩, htc, fun x hx => ⟨hIΘ (hI₁I hx), hIbd (hI₁I hx)⟩, fun x hx => ⟨hIΘ
      (hI₂I hx), hIbd (hI₂I hx)⟩, hI₁₂,
    ⟨0, ⟨le_rfl, unitInterval.nonneg'⟩, rfl⟩, ⟨p, ⟨unitInterval.nonneg', le_rfl⟩, rfl⟩, ⟨q,
      ⟨le_rfl, unitInterval.le_one'⟩, rfl⟩, ⟨1, ⟨unitInterval.le_one', le_rfl⟩, rfl⟩,
    fun x hx => hx.1, sdiff_subset, disjoint_sdiff_right, ?_, ?_, ?_, ⟨c₁, hc₁, h3, h4, h5⟩, ⟨c₂,
      hc₂, h6, h7, h8⟩⟩
  · rintro _ ⟨⟨s, hs, rfl⟩, -⟩ _ ⟨⟨t, ht, rfl⟩, -⟩
    have hO : IsOArc Θ' := (cuff_statement.{0} S hS).2.2 _ hΘ
    have hf : ∀ t, α t ∈ Θ' := fun t => hIΘ (hαI t)
    have hst : s ≤ t := hs.2.trans (hpq.le.trans ht.1)
    exact ⟨fun _ _ => inOrder_of_arc hO ha hf hs.1 hs.2 (hpq.le.trans ht.1), fun _ _
      => inOrder_of_arc hO ha hf unitInterval.nonneg' (hpq.le.trans ht.1) unitInterval.le_one',
      fun _ _ => inOrder_of_arc hO ha hf (hs.2.trans hpq.le) ht.1 unitInterval.le_one', fun _ _
        => inOrder_of_arc hO ha hf hs.1 (hs.2.trans hpq.le) unitInterval.le_one'⟩
  · intro d hd hdΔ hdb hdc
    obtain ⟨u, v, -, htilde, hL, hdiff, -, -⟩ := Γ.border_cell_exists_ends hd hdb
    have hW : (closure d ∩ bd S) \ {u, v} ⊆ I₁ ∪ I₂ := by
      intro w hw
      have hwd : w ∈ d ∩ bd S := hdiff ▸ hw
      have hwI : w ∈ I := hmeet ▸ ⟨hdΔ hwd.1, hwd.2⟩
      rw [← hr] at hwI
      obtain ⟨t, rfl⟩ := hwI
      by_cases h9 : t ≤ p
      · exact .inl ⟨t, ⟨unitInterval.nonneg', h9⟩, rfl⟩
      by_cases h10 : q ≤ t
      · exact .inr ⟨t, ⟨h10, unitInterval.le_one'⟩, rfl⟩
      have h11 : α t ∈ Z := ⟨⟨t, ⟨(not_le.mp h9).le, (not_le.mp h10).le⟩, rfl⟩, by
        rintro (h | h)
        · exact (not_le.mp h9).ne (ha.2 h).symm
        · exact (not_le.mp h10).ne (ha.2 h)⟩
      exact absurd (arcComponentsIn_eq_of_mem hd hc hwd.1 (hZc h11)) hdc
    have htl : tilde d ⊆ closure ((closure d ∩ bd S) \ {u, v}) := by
      rw [htilde]
      rintro x (rfl | rfl)
      · exact hL.subset_closure_diff hL.left_mem
      · exact hL.subset_closure_diff hL.right_mem
    by_cases hmeet₂ : ((closure d ∩ bd S) \ {u, v} ∩ I₂).Nonempty
    · right
      have h9 : (closure d ∩ bd S) \ {u, v} ⊆ I₂ := fun w hw => by
        refine (hW hw).resolve_left fun hw₁ => ?_
        obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hL.isPreconnected_diff I₁ I₂
          (hIcl _ _) (hIcl _ _) hW ⟨w, hw, hw₁⟩ hmeet₂
        exact disjoint_left.mp hI₁₂ hz₁ hz₂
      exact htl.trans (closure_minimal h9 (hIcl _ _))
    · left
      have h9 : (closure d ∩ bd S) \ {u, v} ⊆ I₁ := fun w hw =>
        (hW hw).resolve_right fun hw₂ => hmeet₂ ⟨w, hw, hw₂⟩
      exact htl.trans (closure_minimal h9 (hIcl _ _))
  · intro d hd hdΔ hdb
    have hdG : d ∈ G := ⟨hd, hdΔ, hdb⟩
    by_cases h : ∃ y ∈ e d, y ∈ N₁ ∪ I₁
    · left
      obtain ⟨y, hy, hy'⟩ := h
      have hw : ∃ w ∈ I₁ ∩ Γ.N, Linked G e w y := by
        rcases hy' with hy' | hy'
        · exact hy'.2
        · exact ⟨y, ⟨hy', (hGQ d hdG hy).1⟩, .refl _⟩
      obtain ⟨w, hw, hl⟩ := hw
      intro x hx
      have hl' : Linked G e w x := hl.trans _ _ _ (.rel _ _ ⟨d, hdG, hy, hx⟩)
      rcases hnode x (hGQ d hdG hx) with h9 | h9 | h9
      · exact .inl ⟨⟨hGQ d hdG hx, h9⟩, w, hw, hl'⟩
      · exact .inr h9
      · exact absurd hl' (hnl w hw.1 x h9 hw.2 (hGQ d hdG hx).1)
    · right
      push Not at h
      intro x hx
      have h9 := h x hx
      rcases hnode x (hGQ d hdG hx) with h10 | h10 | h10
      · exact .inl ⟨⟨hGQ d hdG hx, h10⟩, fun h11 => h9 (.inl h11)⟩
      · exact absurd (.inr h10) h9
      · exact .inr h10

/-- The marked-region partition for the two-node normal arc statement in XVII (7.3). -/
theorem normalIArcDiscRegion : NormalIArcDiscRegionStatement := by
  intro S _ hS Γ Θ n₁ n₂ F Δ e P_mark hΘ hn₁ hn₂ hne hnorm hF hb _ hΔ h1 h2 he hP₁ hP₂
  exact normalIArcDiscRegion_of_boundary S hS Γ Θ n₁ n₂ F Δ e P_mark
    hΘ hn₁ hn₂ hne hnorm hF hb hΔ h1 h2 he hP₁ hP₂

end GraphMinor.GM17
