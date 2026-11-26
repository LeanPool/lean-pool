/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffBoxes
public import LeanPool.GraphMinor.GM12.Section6Sides
public import LeanPool.GraphMinor.Surface.DiscPolygon

/-!
# Cutting an annulus into cells

Graph Minors VII, (5.9), page 235. The paths `Q_i(C)` are disjoint lines across the annulus between
the cuff `C` and the circuit `N(C)`. They cut the annulus into cells, one for each pair of
neighbouring lines.
A cell is a closed disc with its boundary in four parts: an arc of the cuff, an arc of the circuit,
and two lines. Each further line across a cell cuts it into two cells.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T]

/-- A cell of the annulus between `D` and `E`: a disc with bottom `a` on `D`, top `b` on `E`, and
sides `l` and `l'`. -/
structure IsCell (D E R a b l l' : Set T) (x x' t t' : T) : Prop where
  disc : IsClosedDisc R
  bottom : IsLineWithEnds a x x'
  top : IsLineWithEnds b t t'
  left : IsLineWithEnds l x t
  right : IsLineWithEnds l' x' t'
  bd_eq : discBd R = a ∪ l' ∪ b ∪ l
  al : a ∩ l = {x}
  ar : a ∩ l' = {x'}
  bl : b ∩ l = {t}
  br : b ∩ l' = {t'}
  ab : Disjoint a b
  ll : Disjoint l l'
  botCap : R ∩ D = a
  aBd : a ⊆ discBd D
  topCap : R ∩ discBd E = b
  subE : R ⊆ E

variable {D E R a b l l' : Set T} {x x' t t' : T}

omit [T2Space T] in
/-- The mirror image of a cell. -/
theorem IsCell.swap (h : IsCell D E R a b l l' x x' t t') : IsCell D E R a b l' l x' x t' t :=
  ⟨h.disc, h.bottom.symm, h.top.symm, h.right, h.left, by rw [h.bd_eq]; ac_rfl,
    h.ar, h.al, h.br, h.bl, h.ab, h.ll.symm, h.botCap, h.aBd, h.topCap, h.subE⟩

omit [T2Space T] in
theorem IsCell.a_sub (h : IsCell D E R a b l l' x x' t t') : a ⊆ discBd R := by
  rw [h.bd_eq]
  exact fun z hz => .inl (.inl (.inl hz))

omit [T2Space T] in
theorem IsCell.b_sub (h : IsCell D E R a b l l' x x' t t') : b ⊆ discBd R := by
  rw [h.bd_eq]
  exact fun z hz => .inl (.inr hz)

omit [T2Space T] in
theorem IsCell.l_sub (h : IsCell D E R a b l l' x x' t t') : l ⊆ discBd R := by
  rw [h.bd_eq]
  exact fun z hz => .inr hz

omit [T2Space T] in
theorem IsCell.r_sub (h : IsCell D E R a b l l' x x' t t') : l' ⊆ discBd R := by
  rw [h.bd_eq]
  exact fun z hz => .inl (.inl (.inr hz))

omit [T2Space T] in
/-- One half of a cell cut by a line `q` from `y` on the bottom to `z` on the top. -/
theorem IsCell.half (h : IsCell D E R a b l l' x x' t t') {q a₁ a₂ b₁ b₂ E₁ E₂ : Set T} {y z : T}
  (hq : IsLineWithEnds q y z) (hqb : q ∩ discBd R = {y, z}) (hxy : x ≠ y) (ht : t ≠ z)
    (ha₁ : IsLineWithEnds a₁ x y) (ha₂ : IsLineWithEnds a₂ y x') (hau : a₁ ∪ a₂ = a) (hai : a₁ ∩ a₂
      = {y}) (hb₁ : IsLineWithEnds b₁ t z) (hb₂ : IsLineWithEnds b₂ z t') (hbu : b₁ ∪ b₂ = b)
        (hbi : b₁ ∩ b₂ = {z})
    (h1 : IsClosedDisc E₁) (h2 : discBd E₁ = (a₁ ∪ l ∪ b₁) ∪ q) (h2' : discBd E₂ =
      (a₂ ∪ l' ∪ b₂) ∪ q) (h3 : E₁ ∪ E₂ = R) (h4 : E₁ ∩ E₂ = q) : IsCell D E E₁ a₁ b₁ l q x y t z
        := by
  have hyb : y ∉ b := fun hy => disjoint_left.mp h.ab (hau ▸ (Or.inr (ha₂.left_mem) : y ∈ a₁ ∪ a₂))
    hy
  have hza : z ∉ a := fun hz => disjoint_left.mp h.ab hz (hbu ▸ (Or.inr
    (hb₂.left_mem) : z ∈ b₁ ∪ b₂))
  have ha₁a : a₁ ⊆ a := hau ▸ subset_union_left
  have ha₂a : a₂ ⊆ a := hau ▸ subset_union_right
  have hb₁b : b₁ ⊆ b := hbu ▸ subset_union_left
  have hb₂b : b₂ ⊆ b := hbu ▸ subset_union_right
  have hE₁R : E₁ ⊆ R := h3 ▸ subset_union_left
  have hqe : ∀ {w}, w ∈ q → w ∈ discBd R → w = y ∨ w = z := fun {w} h5 h6 => by
    have : w ∈ q ∩ discBd R := ⟨h5, h6⟩
    rwa [hqb] at this
  refine ⟨h1, ha₁, hb₁, h.left, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE₁R.trans h.subE⟩
  · rw [h2]
    ac_rfl
  · refine subset_antisymm (fun w hw => ?_) ?_
    · have h5 : w ∈ a ∩ l := ⟨ha₁a hw.1, hw.2⟩
      rwa [h.al] at h5
    · rintro _ rfl
      exact ⟨ha₁.left_mem, h.left.left_mem⟩
  · refine subset_antisymm (fun w hw => ?_) ?_
    · rcases hqe hw.2 (h.a_sub (ha₁a hw.1)) with rfl | rfl
      · rfl
      · exact absurd (ha₁a hw.1) hza
    · rintro _ rfl
      exact ⟨ha₁.right_mem, hq.left_mem⟩
  · refine subset_antisymm (fun w hw => ?_) ?_
    · have h5 : w ∈ b ∩ l := ⟨hb₁b hw.1, hw.2⟩
      rwa [h.bl] at h5
    · rintro _ rfl
      exact ⟨hb₁.left_mem, h.left.right_mem⟩
  · refine subset_antisymm (fun w hw => ?_) ?_
    · rcases hqe hw.2 (h.b_sub (hb₁b hw.1)) with rfl | rfl
      · exact absurd (hb₁b hw.1) hyb
      · rfl
    · rintro _ rfl
      exact ⟨hb₁.right_mem, hq.right_mem⟩
  · exact h.ab.mono ha₁a hb₁b
  · rw [disjoint_left]
    intro w hw hwq
    rcases hqe hwq (h.l_sub hw) with rfl | rfl
    · have h5 : w ∈ a ∩ l := ⟨ha₂a ha₂.left_mem, hw⟩
      rw [h.al] at h5
      exact hxy h5.symm
    · have h5 : w ∈ b ∩ l := ⟨hb₂b hb₂.left_mem, hw⟩
      rw [h.bl] at h5
      exact ht h5.symm
  · refine subset_antisymm ?_ fun w hw => ?_
    · rintro w ⟨hw, hb⟩
      have hwa : w ∈ a := h.botCap ▸ (⟨hE₁R hw, hb⟩ : w ∈ R ∩ D)
      rw [← hau] at hwa
      rcases hwa with h5 | h5
      · exact h5
      · have h6 : w ∈ E₂ := Surface.discBd_subset _ (h2' ▸ .inl (.inl (.inl h5)))
        rcases hqe (h4 ▸ ⟨hw, h6⟩) (h.a_sub (ha₂a h5)) with rfl | rfl
        · exact ha₁.right_mem
        · exact absurd (ha₂a h5) hza
    · refine ⟨Surface.discBd_subset _ (h2 ▸ .inl (.inl (.inl hw))), ?_⟩
      have : w ∈ R ∩ D := h.botCap ▸ ha₁a hw
      exact this.2
  · exact ha₁a.trans h.aBd
  · refine subset_antisymm ?_ fun w hw => ?_
    · rintro w ⟨hw, hb⟩
      have hwa : w ∈ b := h.topCap ▸ (⟨hE₁R hw, hb⟩ : w ∈ R ∩ discBd E)
      rw [← hbu] at hwa
      rcases hwa with h5 | h5
      · exact h5
      · have h6 : w ∈ E₂ := Surface.discBd_subset _ (h2' ▸ .inl (.inr h5))
        rcases hqe (h4 ▸ ⟨hw, h6⟩) (h.b_sub (hb₂b h5)) with rfl | rfl
        · exact absurd (hb₂b h5) hyb
        · exact hb₁.right_mem
    · refine ⟨Surface.discBd_subset _ (h2 ▸ .inl (.inr hw)), ?_⟩
      have : w ∈ R ∩ discBd E := h.topCap ▸ hb₁b hw
      exact this.2

/-- A disc inside a disc with the same boundary is equal to it, since the part of the interior of
the large disc in the small one is open and closed. -/
theorem disc_eq_of_subset_of_bd_eq (hman : ∀ x : T, IsManifoldPoint x) {A B : Set T}
  (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ⊆ B) (hbd : discBd A = discBd B) : A = B
    := by
  refine subset_antisymm hAB ?_
  have h1 : discInt B ⊆ discInt A ∨ Disjoint (discInt B) A := hA.side hman
    hB.isPreconnected_discInt (by
    rw [hbd, disjoint_left]
    exact fun x hx => hx.2)
  rcases h1 with h1 | h1
  · intro x hx
    by_cases hb : x ∈ discBd B
    · exact Surface.discBd_subset _ (hbd ▸ hb)
    · exact discInt_subset _ (h1 ⟨hx, hb⟩)
  · obtain ⟨z, hz⟩ := hA.nonempty_discInt
    exact absurd (discInt_subset _ hz) (disjoint_left.mp h1 (discInt_mono hman hA hAB hz))

/-- The image of a line by a map that is one to one on it is a line. -/
theorem isLineWithEnds_image {X : Type*} [TopologicalSpace X] {Z : Set X} {a b : X}
  (hl : IsLineWithEnds Z a b) {g : X → T} (hc : ContinuousOn g Z) (hi : InjOn g Z) : IsLineWithEnds
    (g '' Z) (g a) (g b) := by
  obtain ⟨f, h0, h1⟩ := hl
  let e : unitInterval → T := fun t => g (f t).1
  have hec : Continuous e := hc.comp_continuous (continuous_subtype_val.comp f.continuous) fun t =>
    (f t).2
  have hei : Injective e := fun s t he => f.injective (Subtype.ext (hi (f s).2 (f t).2 he))
  have hemb := hec.isClosedEmbedding hei
  have hr : range e = g '' Z := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact mem_image_of_mem g (f t).2
    · rintro ⟨z, hz, rfl⟩
      exact ⟨f.symm ⟨z, hz⟩, by simp [e]⟩
  refine ⟨hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr), ?_, ?_⟩
  · change e 0 = g a
    simp only [e, h0]
  · change e 1 = g b
    simp only [e, h1]

/-- A chord of a disc, by a chart from the unit disc. -/
theorem exists_chord_any {D : Set T} (hD : IsClosedDisc D) {a b : T} (ha : a ∈ discBd D)
  (hb : b ∈ discBd D) (hab : a ≠ b) : ∃ F, IsLineWithEnds F a b ∧ F ⊆ D ∧ F ∩ discBd D = {a, b}
    := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hbd : ∀ x ∈ discBd D, h x ∈ sphere (0 : ℂ) 1 := fun x hx => c.bd ▸ mem_image_of_mem h hx
  have hsub := Surface.discBd_subset D
  have hne : h a ≠ h b := fun he => hab (by rw [← c.gh (hsub ha), ← c.gh (hsub hb), he])
  obtain ⟨hU, hUb⟩ := closedBall_disc (s := 1) one_pos
  have hbU : ∀ x ∈ discBd D, h x ∈ discBd (closedBall (0 : ℂ) 1) := fun x hx => hUb ▸ hbd x hx
  obtain ⟨F, hF, hFs, hFc⟩ := Surface.exists_chord hU (hbU a ha) (hbU b hb) hne
  have hg : InjOn g F := fun p hp q hq he => by
    rw [← c.hg (hFs hp), ← c.hg (hFs hq), he]
  have hl := isLineWithEnds_image hF (c.gc.mono hFs) hg
  rw [c.gh (hsub ha), c.gh (hsub hb)] at hl
  refine ⟨g '' F, hl, ?_, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact c.gm (hFs hp)
  · rintro _ ⟨⟨p, hp, rfl⟩, h1⟩
    have h2 : h (g p) ∈ discBd (closedBall (0 : ℂ) 1) := hbU _ h1
    rw [c.hg (hFs hp)] at h2
    have h3 : p ∈ F ∩ discBd (closedBall (0 : ℂ) 1) := ⟨hp, h2⟩
    rw [hFc] at h3
    rcases h3 with rfl | rfl
    · exact .inl (c.gh (hsub ha))
    · exact .inr (c.gh (hsub hb))
  · rintro _ (rfl | rfl)
    · exact ⟨hl.left_mem, ha⟩
    · exact ⟨hl.right_mem, hb⟩

/-- A line from the disc `D` to the boundary of the disc `E`. -/
structure IsCrossLine (D E q : Set T) (x t : T) : Prop where
  line : IsLineWithEnds q x t
  sub : q ⊆ E
  bot : q ∩ D = {x}
  top : q ∩ discBd E = {t}
  xbd : x ∈ discBd D

theorem exists_mem_diff_of_line {c : Set T} {x y : T} (h : IsLineWithEnds c x y) :
  (c \ {x, y}).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have h1 := h.subset_closure_diff h.left_mem
  simp [hne] at h1

/-- One side of the chord through `D` gives a cell, and the part of `D` on that side is the rest of
it. -/
theorem exists_cell_of_side (hman : ∀ x : T, IsManifoldPoint x) {D E X D₁ D₂ a A B c l r : Set T}
  {x x' t t' : T} (hD : D₁ ∪ D₂ = D) (hE : discBd E = A ∪ B) (hX : IsClosedDisc X) (hbd : discBd X
    = A ∪ (l ∪ c ∪ r))
    (hD₁ : IsClosedDisc D₁) (hbD₁ : discBd D₁ = a ∪ c) (hs : D₁ \ c ⊆ X) (hD₂ : D₂ ∩ X ⊆ c)
      (hB : X ∩ B ⊆ A) (hc : IsLineWithEnds c x x') (hac : a ∩ c = {x, x'})
        (ha : IsLineWithEnds a x x') (hA : IsLineWithEnds A t t') (hl : IsLineWithEnds l x t)
          (hr : IsLineWithEnds r x' t') (hxx : x ≠ x')
    (hll : Disjoint l r) (haBd : a ⊆ discBd D) (hXE : X ⊆ E) (hlD : l ∩ D = {x}) (hrD : r ∩ D
      = {x'}) (hlE : l ∩ discBd E = {t}) (hrE : r ∩ discBd E = {t'}) (hDE : Disjoint D (discBd E)) :
    ∃ R, IsCell D E R a A l r x x' t t' ∧ R ∪ D₁ = X := by
  have hcD₁ : c ⊆ D₁ := fun z hz => Surface.discBd_subset _ (hbD₁ ▸ .inr hz)
  have haD₁ : a ⊆ D₁ := fun z hz => Surface.discBd_subset _ (hbD₁ ▸ .inl hz)
  have hD₁D : D₁ ⊆ D := hD ▸ subset_union_left
  have hAE : A ⊆ discBd E := hE ▸ subset_union_left
  have hBX : ∀ z ∈ c, z ∈ X := fun z hz => Surface.discBd_subset _ (hbd ▸ .inr (.inl (.inr hz)))
  have haX : a ⊆ X := fun z hz => by
    by_cases h1 : z ∈ c
    · exact hBX z h1
    · exact hs ⟨haD₁ hz, h1⟩
  have hlone : ∀ {z}, z ∈ l → z ∈ D → z = x := fun {z} h1 h2 => by
    have : z ∈ l ∩ D := ⟨h1, h2⟩
    rwa [hlD] at this
  have hrone : ∀ {z}, z ∈ r → z ∈ D → z = x' := fun {z} h1 h2 => by
    have : z ∈ r ∩ D := ⟨h1, h2⟩
    rwa [hrD] at this
  have hltop : ∀ {z}, z ∈ l → z ∈ discBd E → z = t := fun {z} h1 h2 => by
    have : z ∈ l ∩ discBd E := ⟨h1, h2⟩
    rwa [hlE] at this
  have hrtop : ∀ {z}, z ∈ r → z ∈ discBd E → z = t' := fun {z} h1 h2 => by
    have : z ∈ r ∩ discBd E := ⟨h1, h2⟩
    rwa [hrE] at this
  have hxl : x ∈ l := hl.left_mem
  have htl : t ∈ l := hl.right_mem
  have hxr : x' ∈ r := hr.left_mem
  have htr : t' ∈ r := hr.right_mem
  have hxc : x ∈ c := hc.left_mem
  have hxc' : x' ∈ c := hc.right_mem
  have hxD : x ∈ D := hD₁D (hcD₁ hxc)
  have hxD' : x' ∈ D := hD₁D (hcD₁ hxc')
  have htA : t ∈ A := hA.left_mem
  have htA' : t' ∈ A := hA.right_mem
  have hAoff : ∀ {z}, z ∈ A → z ∉ D := fun {z} h1 h2 => disjoint_left.mp hDE h2 (hAE h1)
  have hl1 : l ∩ A = {t} := subset_antisymm (fun z hz => hltop hz.1 (hAE hz.2)) (by
    rintro _ rfl
    exact ⟨htl, htA⟩)
  have hr1 : r ∩ A = {t'} := subset_antisymm (fun z hz => hrtop hz.1 (hAE hz.2)) (by
    rintro _ rfl
    exact ⟨htr, htA'⟩)
  have hM1 : IsLineWithEnds (l ∪ A) x t' := hl.union hA hl1
  have hM2 : IsLineWithEnds ((l ∪ A) ∪ r) x x' := hM1.union hr.symm (by
    refine subset_antisymm ?_ ?_
    · rintro z ⟨h1 | h1, h2⟩
      · exact absurd h2 (disjoint_left.mp hll h1)
      · exact hrtop h2 (hAE h1)
    · rintro _ rfl
      exact ⟨.inr htA', htr⟩)
  have hMoff : ∀ {z}, z ∈ (l ∪ A) ∪ r → z ∈ D → z = x ∨ z = x' := fun {z} h1 h2 => by
    rcases h1 with (h1 | h1) | h1
    · exact .inl (hlone h1 h2)
    · exact absurd h2 (hAoff h1)
    · exact .inr (hrone h1 h2)
  have hmem : ∀ {M : Set T}, x ∈ M → x' ∈ M → ∀ {K : Set T}, K ⊆ D → x ∈ K → x' ∈ K
    → M ∩ D ⊆ {x, x'} → K ∩ M = {x, x'} := fun {M} h1 h2 {K} h3 h4 h5 h6 => subset_antisymm
      (fun z hz => h6 ⟨hz.2, h3 hz.1⟩) (by
    rintro _ (rfl | rfl)
    · exact ⟨h4, h1⟩
    · exact ⟨h5, h2⟩)
  have hMsub : ((l ∪ A) ∪ r) ∩ D ⊆ {x, x'} := fun z hz => hMoff hz.1 hz.2
  have hMx : x ∈ (l ∪ A) ∪ r := .inl (.inl hxl)
  have hMx' : x' ∈ (l ∪ A) ∪ r := .inr hxr
  have hcD : c ⊆ D := hcD₁.trans hD₁D
  have haD : a ⊆ D := haD₁.trans hD₁D
  have hbdX : discBd X = c ∪ ((l ∪ A) ∪ r) := by
    rw [hbd]
    ac_rfl
  obtain ⟨E₁, E₂, h1, h2, hu, hin, hb1, hb2⟩ := GM12.split_with_arcs hX ha hc hM2
    (hmem hMx hMx' hcD hxc hxc' hMsub) hac (hmem hMx hMx' haD ha.left_mem ha.right_mem hMsub) hbdX
      haX hxx
  have hE₁X : E₁ ⊆ X := hu ▸ subset_union_left
  have hE₂X : E₂ ⊆ X := hu ▸ subset_union_right
  have hce₁ : c ⊆ E₁ := fun z hz => Surface.discBd_subset _ (hb1 ▸ .inl hz)
  have hint : discInt D₁ ⊆ X := fun z hz => by
    by_cases h3 : z ∈ c
    · exact hBX z h3
    · exact hs ⟨hz.1, h3⟩
  have hsub : D₁ ⊆ E₁ := by
    have hd : Disjoint (discInt D₁) (E₁ ∩ E₂) := by
      rw [hin, disjoint_left]
      exact fun z hz h3 => hz.2 (hbD₁ ▸ .inl h3)
    rcases GM12.subset_side h1.isClosed h2.isClosed hD₁.isPreconnected_discInt
      (by rw [hu]; exact hint) hd with h3 | h3
    · exact hD₁.subset_closure_discInt.trans (closure_minimal h3 h1.isClosed)
    · exfalso
      have h4 : D₁ ⊆ E₂ := hD₁.subset_closure_discInt.trans (closure_minimal h3 h2.isClosed)
      obtain ⟨z, hz, hne⟩ := exists_mem_diff_of_line hc
      have h5 : z ∈ a := hin ▸ (⟨hce₁ hz, h4 (hcD₁ hz)⟩ : z ∈ E₁ ∩ E₂)
      exact hne (hac ▸ (⟨h5, hz⟩ : z ∈ a ∩ c))
  have heq : D₁ = E₁ := disc_eq_of_subset_of_bd_eq hman hD₁ h1 hsub
    (by rw [hbD₁, hb1]; exact union_comm _ _)
  have hE₂a : E₂ ∩ D₁ = a := by
    rw [heq, inter_comm]
    exact hin
  have hsubE : ∀ z ∈ (l ∪ A) ∪ r, z ∈ E₂ := fun z hz => Surface.discBd_subset _ (hb2 ▸ .inl hz)
  have haE₂ : a ⊆ E₂ := fun z hz => Surface.discBd_subset _ (hb2 ▸ .inr hz)
  refine ⟨E₂, ⟨h2, ha, hA, hl, hr, ?_, subset_antisymm (fun z hz => hlone hz.2
    (haD hz.1)) ?_, subset_antisymm (fun z hz => hrone hz.2 (haD hz.1)) ?_, hl1 ▸ inter_comm _ _,
      hr1 ▸ inter_comm _ _, ?_, hll, ?_, haBd, ?_, hE₂X.trans hXE⟩, ?_⟩
  · rw [hb2]
    ac_rfl
  · rintro _ rfl
    exact ⟨ha.left_mem, hxl⟩
  · rintro _ rfl
    exact ⟨ha.right_mem, hxr⟩
  · rw [disjoint_left]
    exact fun z h3 h4 => hAoff h4 (haD h3)
  · refine subset_antisymm ?_ fun z hz => ⟨haE₂ hz, haD hz⟩
    rintro z ⟨h3, h4⟩
    rw [← hD] at h4
    rcases h4 with h4 | h4
    · exact hE₂a ▸ (⟨h3, h4⟩ : z ∈ E₂ ∩ D₁)
    · have h5 := hD₂ ⟨h4, hE₂X h3⟩
      exact hE₂a ▸ (⟨h3, hcD₁ h5⟩ : z ∈ E₂ ∩ D₁)
  · refine subset_antisymm ?_ fun z hz => ⟨hsubE z (.inl (.inr hz)), hAE hz⟩
    rintro z ⟨h3, h4⟩
    rw [hE] at h4
    rcases h4 with h4 | h4
    · exact h4
    · exact hB ⟨hE₂X h3, h4⟩
  · rw [heq, union_comm]
    exact hu

omit [T2Space T] in
/-- Two points of the chord side cannot both lie on one side. -/
theorem not_both_sides {X Y D D₁ D₂ c : Set T} {z : T} (hman : ∀ x : T, IsManifoldPoint x)
  (hDd : IsClosedDisc D) (hY : IsClosedDisc Y) (hXY : X ∩ Y ⊆ discBd Y) (hz : z ∈ c)
    (hzD : z ∈ discInt D) (hcX : c ⊆ X) (hcY : c ⊆ Y) (hD : D₁ ∪ D₂ = D) (h1 : D₁ \ c ⊆ X)
      (h2 : D₂ \ c ⊆ X) : False := by
  have hzc : z ∈ closure (discInt Y) := hY.subset_closure_discInt (hcY hz)
  obtain ⟨y, hyD, hyY⟩ := mem_closure_iff.mp hzc _ (hDd.isOpen_discInt hman) hzD
  have hyX : y ∈ X := by
    by_cases h3 : y ∈ c
    · exact hcX h3
    · have h4 : y ∈ D₁ ∪ D₂ := hD ▸ hyD.1
      rcases h4 with h4 | h4
      · exact h1 ⟨h4, h3⟩
      · exact h2 ⟨h4, h3⟩
  exact hyY.2 (hXY ⟨hyX, hyY.1⟩)

/-- **The first two cells.** Two lines across the annulus between `D` and `E`, joined by a chord of
`D`, cut `E` into two discs. Each holds one half of `D` and one cell. -/
theorem exists_two_cells (hman : ∀ x : T, IsManifoldPoint x) {D E l r : Set T} {x x' t t' : T}
  (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : D ⊆ E \ discBd E) (hl : IsCrossLine D E l x t)
    (hr : IsCrossLine D E r x' t') (hll : Disjoint l r) :
    ∃ R₁ R₂ a₁ a₂ b₁ b₂, IsCell D E R₁ a₁ b₁ l r x x' t t' ∧ IsCell D E R₂ a₂ b₂ l r x x' t t'
      ∧ R₁ ∩ R₂ ⊆ l ∪ r ∧ a₁ ∪ a₂ = discBd D ∧ b₁ ∪ b₂ = discBd E ∧ R₁ ∪ R₂ ∪ D = E := by
  have hxx : x ≠ x' := fun h => disjoint_left.mp hll hl.line.left_mem (h ▸ hr.line.left_mem)
  have hxD : x ∈ D := Surface.discBd_subset _ hl.xbd
  have htE : t ∈ discBd E := (hl.top ▸ (mem_singleton t) : t ∈ l ∩ discBd E).2
  have htE' : t' ∈ discBd E := (hr.top ▸ (mem_singleton t') : t' ∈ r ∩ discBd E).2
  have htt : t ≠ t' := fun h => disjoint_left.mp hll hl.line.right_mem (h ▸ hr.line.right_mem)
  have hdis : Disjoint D (discBd E) := disjoint_left.mpr fun z hz h => (hDE hz).2 h
  obtain ⟨c, hc, hcD, hcb⟩ := exists_chord_any hD hl.xbd hr.xbd hxx
  obtain ⟨D₁, D₂, a₁, a₂, ha₁, ha₂, hau, hai, hD₁, hD₂, hDu, hDi, hbD₁, hbD₂⟩
    := GM12.split_disc hD hcD hxx hc hcb
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hE.isOArc_discBd.lines htE htE' htt
  have hcl : l ∩ c = {x} := subset_antisymm (fun z hz => hl.bot ▸ (⟨hz.1, hcD hz.2⟩ : z ∈ l ∩ D))
    (by
    rintro _ rfl
    exact ⟨hl.line.left_mem, hc.left_mem⟩)
  have hL₁ : IsLineWithEnds (l ∪ c) t x' := hl.line.symm.union hc hcl
  have hrone : ∀ {z}, z ∈ r → z ∈ D → z = x' := fun {z} h1 h2 => by
    have : z ∈ r ∩ D := ⟨h1, h2⟩
    rwa [hr.bot] at this
  have hL₂ : IsLineWithEnds (l ∪ c ∪ r) t t' := hL₁.union hr.line (by
    refine subset_antisymm ?_ ?_
    · rintro z ⟨h1 | h1, h2⟩
      · exact absurd h2 (disjoint_left.mp hll h1)
      · exact hrone h2 (hcD h1)
    · rintro _ rfl
      exact ⟨.inr hc.right_mem, hr.line.left_mem⟩)
  have hLE : ∀ z ∈ l ∪ c ∪ r, z ∈ discBd E → z = t ∨ z = t' := fun z hz h1 => by
    rcases hz with (h2 | h2) | h2
    · have h3 : z ∈ l ∩ discBd E := ⟨h2, h1⟩
      rw [hl.top] at h3
      exact .inl h3
    · exact absurd h1 (disjoint_left.mp hdis (hcD h2))
    · have h3 : z ∈ r ∩ discBd E := ⟨h2, h1⟩
      rw [hr.top] at h3
      exact .inr h3
  have hLs : ∀ {K : Set T}, K ⊆ discBd E → t ∈ K → t' ∈ K → (l ∪ c ∪ r) ∩ K = {t, t'}
    := fun {K} h1 h2 h3 => subset_antisymm (fun z hz => hLE z hz.1 (h1 hz.2)) (by
    rintro _ (rfl | rfl)
    · exact ⟨.inl (.inl hl.line.right_mem), h2⟩
    · exact ⟨.inr hr.line.right_mem, h3⟩)
  have hAE : A ⊆ discBd E := hu ▸ subset_union_left
  have hBE : B ⊆ discBd E := hu ▸ subset_union_right
  have hLsub : l ∪ c ∪ r ⊆ E := union_subset (union_subset hl.sub fun z hz => (hDE
    (hcD hz)).1) hr.sub
  obtain ⟨X, Y, hX, hY, hun, hin, hbX, hbY⟩ := GM12.split_with_arcs hE hL₂ hA hB hi
    (hLs hAE hA.left_mem hA.right_mem) (hLs hBE hB.left_mem hB.right_mem) hu.symm hLsub htt
  have hXE : X ⊆ E := hun ▸ subset_union_left
  have hYE : Y ⊆ E := hun ▸ subset_union_right
  have hLD : ∀ z ∈ l ∪ c ∪ r, z ∈ D → z ∈ c := fun z hz h1 => by
    rcases hz with (h2 | h2) | h2
    · have h3 : z ∈ l ∩ D := ⟨h2, h1⟩
      rw [hl.bot] at h3
      exact h3 ▸ hc.left_mem
    · exact h2
    · exact hrone h2 h1 ▸ hc.right_mem
  have hside : ∀ {K : Set T}, IsClosedDisc K → K ⊆ D → c ⊆ discBd K → K \ c ⊆ X ∨ K \ c ⊆ Y
    := fun {K} h1 h2 h3 => by
    refine GM12.subset_side hX.isClosed hY.isClosed ?_
      (by rw [hun]; exact fun z hz => (hDE (h2 hz.1)).1) ?_
    · refine h1.isPreconnected_discInt.subset_closure (fun z hz => ⟨hz.1,
        fun h4 => hz.2 (h3 h4)⟩) fun z hz => h1.subset_closure_discInt hz.1
    · rw [hin, disjoint_left]
      exact fun z hz h4 => hz.2 (hLD z h4 (h2 hz.1))
  have hcsub : c ⊆ l ∪ c ∪ r := fun z hz => .inl (.inr hz)
  obtain ⟨z, hz, hne⟩ := exists_mem_diff_of_line hc
  have hzD : z ∈ discInt D := ⟨hcD hz, fun h1 => hne (hcb ▸ (⟨hz, h1⟩ : z ∈ c ∩ discBd D))⟩
  have hLX : l ∪ c ∪ r ⊆ X := fun z hz => Surface.discBd_subset _ (hbX ▸ .inr hz)
  have hLY : l ∪ c ∪ r ⊆ Y := fun z hz => Surface.discBd_subset _ (hbY ▸ .inr hz)
  have hcX := hcsub.trans hLX
  have hcY := hcsub.trans hLY
  have hXYb : X ∩ Y ⊆ discBd Y := fun z hz => hbY ▸ .inr (hin ▸ hz)
  have hYXb : Y ∩ X ⊆ discBd X := fun z hz => hbX ▸ .inr (hin ▸ (inter_comm X Y) ▸ hz)
  have hD₁D : D₁ ⊆ D := hDu ▸ subset_union_left
  have hD₂D : D₂ ⊆ D := hDu ▸ subset_union_right
  have hcb₁ : c ⊆ discBd D₁ := fun z hz => hbD₁ ▸ .inr hz
  have hcb₂ : c ⊆ discBd D₂ := fun z hz => hbD₂ ▸ .inr hz
  -- The two halves of `D` lie on different sides.
  have key : ∀ {X Y A B D₁ D₂ a₁ a₂ : Set T}, IsClosedDisc X → IsClosedDisc Y → X ∩ Y = l ∪ c ∪ r
    → discBd X = A ∪ (l ∪ c ∪ r) → discBd Y = B ∪ (l ∪ c ∪ r) → IsLineWithEnds A t t'
      → IsLineWithEnds B t t' → discBd E = A ∪ B → X ∪ Y = E → IsClosedDisc D₁ → IsClosedDisc D₂
        → D₁ ∪ D₂ = D → D₁ \ c ⊆ X → D₂ \ c ⊆ Y → discBd D₁ = a₁ ∪ c → discBd D₂ = a₂ ∪ c → a₁ ∩ c
          = {x, x'} → a₂ ∩ c = {x, x'} → IsLineWithEnds a₁ x x' → IsLineWithEnds a₂ x x'
            → a₁ ⊆ discBd D → a₂ ⊆ discBd D → ∃ R₁ R₂, IsCell D E R₁ a₁ A l r x x' t t'
              ∧ IsCell D E R₂ a₂ B l r x x' t t' ∧ R₁ ∪ D₁ = X ∧ R₂ ∪ D₂ = Y := by
    intro X Y A B D₁ D₂ a₁ a₂ hX hY hin hbX hbY hA hB hE' hun hD₁ hD₂ hDu h1 h2 hbD₁ hbD₂ hac₁ hac₂
      ha₁ ha₂ haB₁ haB₂
    have hXE : X ⊆ E := hun ▸ subset_union_left
    have hYE : Y ⊆ E := hun ▸ subset_union_right
    have hXYc : ∀ w ∈ X, w ∈ Y → w ∈ l ∪ c ∪ r := fun w h3 h4 => hin ▸ ⟨h3, h4⟩
    obtain ⟨R₁, hR₁, hu₁⟩ := exists_cell_of_side hman hDu hE' hX hbX hD₁ hbD₁ h1 (fun w hw => by
      by_cases h3 : w ∈ c
      · exact h3
      · exact hLD w (hXYc w hw.2 (h2 ⟨hw.1, h3⟩)) (hDu ▸ .inr hw.1)) (fun w hw => by
      have h3 : w ∈ l ∪ c ∪ r := hXYc w hw.1 (Surface.discBd_subset _ (hbY ▸ .inl hw.2))
      have h4 := hLE w h3 (hE' ▸ .inr hw.2)
      rcases h4 with rfl | rfl
      · exact hA.left_mem
      · exact hA.right_mem) hc hac₁ ha₁ hA hl.line hr.line hxx hll haB₁ hXE hl.bot hr.bot hl.top
          hr.top hdis
    obtain ⟨R₂, hR₂, hu₂⟩ := exists_cell_of_side hman
      (by rw [union_comm]; exact hDu) (by rw [union_comm]; exact hE') hY hbY hD₂ hbD₂ h2
      (fun w hw => by
      by_cases h3 : w ∈ c
      · exact h3
      · exact hLD w (hXYc w (h1 ⟨hw.1, h3⟩) hw.2) (hDu ▸ .inl hw.1)) (fun w hw => by
      have h3 : w ∈ l ∪ c ∪ r := hXYc w (Surface.discBd_subset _ (hbX ▸ .inl hw.2)) hw.1
      have h4 := hLE w h3 (hE' ▸ .inl hw.2)
      rcases h4 with rfl | rfl
      · exact hB.left_mem
      · exact hB.right_mem) hc hac₂ ha₂ hB hl.line hr.line hxx hll haB₂ hYE hl.bot hr.bot hl.top
          hr.top hdis
    exact ⟨R₁, R₂, hR₁, hR₂, hu₁, hu₂⟩
  have hac : ∀ {M : Set T}, M ⊆ discBd D → x ∈ M → x' ∈ M → M ∩ c = {x, x'} := fun {M} h1 h2 h3
    => subset_antisymm (fun w hw => hcb ▸ (⟨hw.2, h1 hw.1⟩ : w ∈ c ∩ discBd D)) (by
    rintro _ (rfl | rfl)
    · exact ⟨h2, hc.left_mem⟩
    · exact ⟨h3, hc.right_mem⟩)
  have hac₁ := hac (hau ▸ subset_union_left) ha₁.left_mem ha₁.right_mem
  have hac₂ := hac (hau ▸ subset_union_right) ha₂.left_mem ha₂.right_mem
  have hfinal : ∀ {R₁ R₂ D₁ D₂ X Y : Set T}, R₁ ∪ D₁ = X → R₂ ∪ D₂ = Y → D₁ ∪ D₂ = D → X ∩ Y
    = l ∪ c ∪ r → X ∪ Y = E → (R₁ ∩ D = a₁ ∨ True) → R₁ ∩ D ⊆ discBd D → R₂ ∩ D ⊆ discBd D
      → R₁ ∩ R₂ ⊆ l ∪ r ∧ R₁ ∪ R₂ ∪ D = E := by
    intro R₁ R₂ D₁ D₂ X Y h1 h2 h3 h4 h5 _ h6 h7
    constructor
    · intro w hw
      have h8 : w ∈ X ∩ Y := ⟨h1 ▸ .inl hw.1, h2 ▸ .inl hw.2⟩
      rw [h4] at h8
      rcases h8 with (h9 | h9) | h9
      · exact .inl h9
      · have h10 : w ∈ c ∩ discBd D := ⟨h9, h6 ⟨hw.1, hcD h9⟩⟩
        rw [hcb] at h10
        rcases h10 with rfl | rfl
        · exact .inl hl.line.left_mem
        · exact .inr hr.line.left_mem
      · exact .inr h9
    · rw [← h5, ← h1, ← h2, ← h3]
      ac_rfl
  rcases hside hD₁ hD₁D hcb₁ with h1 | h1 <;> rcases hside hD₂ hD₂D hcb₂ with h2 | h2
  · exact (not_both_sides hman hD hY hXYb hz hzD hcX hcY hDu h1 h2).elim
  · obtain ⟨R₁, R₂, hR₁, hR₂, hu₁, hu₂⟩ := key hX hY hin hbX hbY hA hB hu.symm hun hD₁ hD₂ hDu h1
      h2 hbD₁ hbD₂ hac₁ hac₂ ha₁ ha₂ (hau ▸ subset_union_left) (hau ▸ subset_union_right)
    obtain ⟨h3, h4⟩ := hfinal hu₁ hu₂ hDu hin hun (.inr trivial) (fun w hw => hau ▸ .inl
      (hR₁.botCap ▸ hw)) (fun w hw => hau ▸ .inr (hR₂.botCap ▸ hw))
    exact ⟨R₁, R₂, a₁, a₂, A, B, hR₁, hR₂, h3, hau, hu, h4⟩
  · obtain ⟨R₁, R₂, hR₁, hR₂, hu₁, hu₂⟩ := key hX hY hin hbX hbY hA hB hu.symm hun hD₂ hD₁
      (by rw [union_comm]; exact hDu) h2 h1 hbD₂ hbD₁ hac₂ hac₁ ha₂ ha₁
      (hau ▸ subset_union_right) (hau ▸ subset_union_left)
    obtain ⟨h3, h4⟩ := hfinal hu₁ hu₂ (by rw [union_comm]; exact hDu) hin hun (.inr trivial)
      (fun w hw => hau ▸ .inr (hR₁.botCap ▸ hw)) (fun w hw => hau ▸ .inl (hR₂.botCap ▸ hw))
    exact ⟨R₁, R₂, a₂, a₁, A, B, hR₁, hR₂, h3, by rw [union_comm]; exact hau, hu, h4⟩
  · exact (not_both_sides hman hD hX hYXb hz hzD hcY hcX hDu h1 h2).elim

/-- A cell of a family: its disc, its bottom and top arcs, and the indices of its two sides. -/
structure CellRec (T : Type u) (ι : Type*) where
  /-- The closed disc of the cell. -/
  R : Set T
  /-- The bottom boundary arc on the inner disc. -/
  a : Set T
  /-- The top boundary arc on the outer disc. -/
  b : Set T
  /-- The index of the left side. -/
  i : ι
  /-- The index of the right side. -/
  i' : ι

/-- The cells of the annulus between `D` and `E` cut by the lines with index in `s`. -/
structure IsCellFamily {ι : Type*} (D E : Set T) (q : ι → Set T) (x t : ι → T) (s : Set ι) (F : Set
  (CellRec T ι)) : Prop where
  finite : F.Finite
  cell : ∀ c ∈ F, IsCell D E c.R c.a c.b (q c.i) (q c.i') (x c.i) (x c.i') (t c.i) (t c.i')
  meet : ∀ c ∈ F, ∀ c' ∈ F, c ≠ c' → ∀ w, w ∈ c.R → w ∈ c'.R → ∃ k, (k = c.i ∨ k = c.i') ∧ (k
    = c'.i ∨ k = c'.i') ∧ w ∈ q k
  cover : ∀ w ∈ E, w ∈ D ∨ ∃ c ∈ F, w ∈ c.R
  botCover : ∀ w ∈ discBd D, ∃ c ∈ F, w ∈ c.a
  topCover : ∀ w ∈ discBd E, ∃ c ∈ F, w ∈ c.b
  side : ∀ c ∈ F, c.i ∈ s ∧ c.i' ∈ s
  used : ∀ k ∈ s, ∃ c ∈ F, c.i = k ∨ c.i' = k

section Family

variable {ι : Type*} {q : ι → Set T} {x t : ι → T}

private theorem inserted_line_interior_avoids_cell_boundary
    {T : Type u}
    [TopologicalSpace T]
    {D : Set T}
    {E : Set T}
    {ι : Type*}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    {s : Set ι}
    {F : Set (CellRec T ι)}
    (h : IsCellFamily D E q x t s F)
    {j : ι}
    (hoff : ∀ k ∈ s, ∀ {w : T}, w ∈ q j → w ∉ q k)
    (hqD : ∀ {w : T}, w ∈ q j → w ∈ D → w = x j)
    (hqE : ∀ {w : T}, w ∈ q j → w ∈ discBd E → w = t j)
    (hbE : ∀ c ∈ F, ∀ {w : T}, w ∈ c.b → w ∈ discBd E)
    (haD : ∀ c ∈ F, ∀ {w : T}, w ∈ c.a → w ∈ D) :
    let Z : Set T := q j \ {x j, t j}
    ∀ (c : CellRec T ι),
    (c ∈ F) →
    Disjoint Z (discBd c.R) := by
  intro Z c hc
  rw [disjoint_left]
  rintro w ⟨h1, h2⟩ h3
  rw [(h.cell c hc).bd_eq] at h3
  rcases h3 with ((h3 | h3) | h3) | h3
  · exact h2 (.inl (hqD h1 (haD c hc h3)))
  · exact hoff _ (h.side c hc).2 h1 h3
  · exact h2 (.inr (hqE h1 (hbE c hc h3)))
  · exact hoff _ (h.side c hc).1 h1 h3

private theorem inserted_line_interior_stays_in_cell
    {T : Type u}
    [TopologicalSpace T]
    [T2Space T]
    {D : Set T}
    {E : Set T}
    {ι : Type*}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (hman : ∀ (x : T), IsManifoldPoint x)
    {s : Set ι}
    {F : Set (CellRec T ι)}
    (h : IsCellFamily D E q x t s F)
    (hq : ∀ (k : ι), IsCrossLine D E (q k) (x k) (t k))
    {j : ι}
    (hoff : ∀ k ∈ s, ∀ {w : T}, w ∈ q j → w ∉ q k)
    (hqD : ∀ {w : T}, w ∈ q j → w ∈ D → w = x j)
    (c₀ : CellRec T ι)
    (hc₀ : c₀ ∈ F)
    (hxa : x j ∈ c₀.a)
    (hcell : IsCell D E c₀.R c₀.a c₀.b (q c₀.i) (q c₀.i') (x c₀.i) (x c₀.i') (t c₀.i) (t c₀.i'))
    (hs₁ : c₀.i ∈ s)
    (hs₂ : c₀.i' ∈ s) :
    let Z : Set T := q j \ {x j, t j}
    (∀ c ∈ F, Disjoint Z (discBd c.R)) →
    Z ⊆ discInt c₀.R := by
  intro Z hZbd
  rcases hcell.disc.side hman (hq j).line.isPreconnected_diff (hZbd c₀ hc₀) with h1 | h1
  · exact h1
  · exfalso
    have hcl : IsClosed (⋃ c ∈ F \ {c₀}, c.R) := (h.finite.subset sdiff_subset).isClosed_biUnion
      fun c hc => (h.cell c hc.1).disc.isClosed
    have hsub : Z ⊆ ⋃ c ∈ F \ {c₀}, c.R := fun w hw => by
      have hwD : w ∉ D := fun h2 => hw.2 (.inl (hqD hw.1 h2))
      rcases h.cover w ((hq j).sub hw.1) with h2 | ⟨c, hc, h2⟩
      · exact absurd h2 hwD
      · refine mem_iUnion₂.mpr ⟨c, ⟨hc, ?_⟩, h2⟩
        rintro rfl
        exact disjoint_left.mp h1 hw h2
    have h2 : x j ∈ ⋃ c ∈ F \ {c₀}, c.R := closure_minimal hsub hcl
      ((hq j).line.subset_closure_diff (hq j).line.left_mem)
    obtain ⟨c, hc, h3⟩ := mem_iUnion₂.mp h2
    have hne' : c₀ ≠ c := fun he => hc.2 he.symm
    obtain ⟨k, hk, -, h4⟩ := h.meet c₀ hc₀ c hc.1 hne' _ (hcell.a_sub hxa |>
      Surface.discBd_subset _) h3
    have hks : k ∈ s := by
      rcases hk with rfl | rfl
      · exact hs₁
      · exact hs₂
    exact hoff k hks (hq j).line.left_mem h4

private theorem right_end_on_cell_top
    {T : Type u}
    [TopologicalSpace T]
    {D : Set T}
    {E : Set T}
    {ι : Type*}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    (hq : ∀ (k : ι), IsCrossLine D E (q k) (x k) (t k))
    {j : ι}
    (c₀ : CellRec T ι)
    (hcell : IsCell D E c₀.R c₀.a c₀.b (q c₀.i) (q c₀.i') (x c₀.i) (x c₀.i') (t c₀.i) (t c₀.i'))
    (hqR : q j ⊆ c₀.R) :
    t j ∈ c₀.b := by
  have h1 : t j ∈ c₀.R ∩ discBd E := ⟨hqR (hq j).line.right_mem, by
    have h2 : t j ∈ q j ∩ discBd E := by
      rw [(hq j).top]
      rfl
    exact h2.2⟩
  rwa [hcell.topCap] at h1

private theorem split_cell_arcs_meet_only_at_new_ends
    {T : Type u}
    [TopologicalSpace T]
    {ι : Type*}
    {x : ι → T}
    {t : ι → T}
    {j : ι}
    (c₀ : CellRec T ι)
    (hx₁ : x j ≠ x c₀.i)
    (hx₂ : x j ≠ x c₀.i')
    (ht₁ : t j ≠ t c₀.i)
    (ht₂ : t j ≠ t c₀.i')
    (a₁ : Set T)
    (a₂ : Set T)
    (ha₁ : IsLineWithEnds a₁ (x c₀.i) (x j))
    (ha₂ : IsLineWithEnds a₂ (x j) (x c₀.i'))
    (b₁ : Set T)
    (b₂ : Set T)
    (hb₁ : IsLineWithEnds b₁ (t c₀.i) (t j))
    (hb₂ : IsLineWithEnds b₂ (t j) (t c₀.i'))
    (ha₁s : a₁ ⊆ c₀.a)
    (ha₂s : a₂ ⊆ c₀.a)
    (hb₁s : b₁ ⊆ c₀.b)
    (hb₂s : b₂ ⊆ c₀.b)
    (l : Set T)
    (r : Set T)
    (hal : ∀ {w : T}, w ∈ c₀.a → w ∈ l → w = x c₀.i)
    (har : ∀ {w : T}, w ∈ c₀.a → w ∈ r → w = x c₀.i')
    (hbl : ∀ {w : T}, w ∈ c₀.b → w ∈ l → w = t c₀.i)
    (hbr : ∀ {w : T}, w ∈ c₀.b → w ∈ r → w = t c₀.i')
    (hab : ∀ {w : T}, w ∈ c₀.a → w ∉ c₀.b)
    (hlr : ∀ {w : T}, w ∈ l → w ∉ r)
    (ha₁₂ : ∀ {w : T}, w ∈ a₁ → w ∈ a₂ → w = x j)
    (hb₁₂ : ∀ {w : T}, w ∈ b₁ → w ∈ b₂ → w = t j) :
    (a₁ ∪ l ∪ b₁) ∩ (a₂ ∪ r ∪ b₂) = {x j, t j} := by
  refine subset_antisymm ?_ ?_
  · rintro w ⟨(h1 | h1) | h1, (h2 | h2) | h2⟩
    · exact .inl (ha₁₂ h1 h2)
    · have h3 := har (ha₁s h1) h2
      exact absurd (ha₁₂ (h3 ▸ h1) ha₂.right_mem) hx₂.symm
    · exact absurd (hb₂s h2) (hab (ha₁s h1))
    · have h3 := hal (ha₂s h2) h1
      exact absurd (ha₁₂ ha₁.left_mem (h3 ▸ h2)) hx₁.symm
    · exact absurd h2 (hlr h1)
    · have h3 := hbl (hb₂s h2) h1
      exact absurd (hb₁₂ hb₁.left_mem (h3 ▸ h2)) ht₁.symm
    · exact absurd (hb₁s h1) (hab (ha₂s h2))
    · have h3 := hbr (hb₁s h1) h2
      exact absurd (hb₁₂ (h3 ▸ h1) hb₂.right_mem) ht₂.symm
    · exact .inr (hb₁₂ h1 h2)
  · rintro _ (rfl | rfl)
    · exact ⟨.inl (.inl ha₁.right_mem), .inl (.inl ha₂.left_mem)⟩
    · exact ⟨.inr hb₁.right_mem, .inr hb₂.left_mem⟩

private theorem inserted_line_meets_boundary_route_only_at_ends
    {T : Type u}
    [TopologicalSpace T]
    {D : Set T}
    {E : Set T}
    {ι : Type*}
    {q : ι → Set T}
    {x : ι → T}
    {t : ι → T}
    {s : Set ι}
    {F : Set (CellRec T ι)}
    (hq : ∀ (k : ι), IsCrossLine D E (q k) (x k) (t k))
    {j : ι}
    (hoff : ∀ k ∈ s, ∀ {w : T}, w ∈ q j → w ∉ q k)
    (hqD : ∀ {w : T}, w ∈ q j → w ∈ D → w = x j)
    (hqE : ∀ {w : T}, w ∈ q j → w ∈ discBd E → w = t j)
    (c₀ : CellRec T ι)
    (hc₀ : c₀ ∈ F)
    (hbE : ∀ c ∈ F, ∀ {w : T}, w ∈ c.b → w ∈ discBd E)
    (haD : ∀ c ∈ F, ∀ {w : T}, w ∈ c.a → w ∈ D)
    {A₀ : Set T}
    {B₀ : Set T}
    (h1 : A₀ ⊆ c₀.a)
    (h2 : B₀ ⊆ c₀.b)
    (k : ι)
    (hk : k ∈ s)
    (h3 : x j ∈ A₀)
    (h4 : t j ∈ B₀) :
    q j ∩ (A₀ ∪ q k ∪ B₀) = {x j, t j} := by
  refine subset_antisymm ?_ ?_
  · rintro w ⟨h5, (h6 | h6) | h6⟩
    · exact .inl (hqD h5 (haD c₀ hc₀ (h1 h6)))
    · exact absurd h6 (hoff k hk h5)
    · exact .inr (hqE h5 (hbE c₀ hc₀ (h2 h6)))
  · rintro _ (rfl | rfl)
    · exact ⟨(hq j).line.left_mem, .inl (.inl h3)⟩
    · exact ⟨(hq j).line.right_mem, .inr h4⟩

/-- A further line across the annulus lies in one cell, and it cuts that cell into two. -/
theorem IsCellFamily.insert (hman : ∀ x : T, IsManifoldPoint x) {s : Set ι} {F : Set (CellRec T ι)}
  (h : IsCellFamily D E q x t s F) (hDE : Disjoint D (discBd E)) (hq : ∀ k, IsCrossLine D E (q k)
    (x k) (t k)) (hdis : ∀ k k', k ≠ k' → Disjoint (q k) (q k')) {j : ι}
      (hj : j ∉ s) : ∃ F', IsCellFamily D E q x t (insert j s) F' := by
  classical
  have hne : ∀ k ∈ s, k ≠ j := fun k hk he => hj (he ▸ hk)
  have hoff : ∀ k ∈ s, ∀ {w}, w ∈ q j → w ∉ q k := fun k hk {w} h1 h2 => disjoint_left.mp (hdis k j
    (hne k hk)) h2 h1
  have hxt : x j ≠ t j := fun he => disjoint_left.mp hDE (Surface.discBd_subset _ (hq j).xbd) (by
    have h1 : t j ∈ q j ∩ discBd E := by
      rw [(hq j).top]
      rfl
    exact he ▸ h1.2)
  have hqD : ∀ {w}, w ∈ q j → w ∈ D → w = x j := fun {w} h1 h2 => by
    have h3 : w ∈ q j ∩ D := ⟨h1, h2⟩
    rwa [(hq j).bot] at h3
  have hqE : ∀ {w}, w ∈ q j → w ∈ discBd E → w = t j := fun {w} h1 h2 => by
    have h3 : w ∈ q j ∩ discBd E := ⟨h1, h2⟩
    rwa [(hq j).top] at h3
  obtain ⟨c₀, hc₀, hxa⟩ := h.botCover _ (hq j).xbd
  have hcell := h.cell c₀ hc₀
  obtain ⟨hs₁, hs₂⟩ := h.side c₀ hc₀
  have hbE : ∀ c ∈ F, ∀ {w}, w ∈ c.b → w ∈ discBd E := fun c hc {w} h1 => by
    have h2 : w ∈ c.R ∩ discBd E := by
      rw [(h.cell c hc).topCap]
      exact h1
    exact h2.2
  have haD : ∀ c ∈ F, ∀ {w}, w ∈ c.a → w ∈ D := fun c hc {w} h1 => by
    have h2 : w ∈ c.R ∩ D := by
      rw [(h.cell c hc).botCap]
      exact h1
    exact h2.2
  set Z := q j \ {x j, t j} with hZ
  have hZbd : ∀ c ∈ F, Disjoint Z (discBd c.R) := fun c hc => by
    exact inserted_line_interior_avoids_cell_boundary (T := T) (D := D) (E := E) (ι := ι) (q := q)
      (x := x) (t := t) (s := s) (F := F) h (j := j) hoff hqD hqE hbE haD  c hc
  have hZin : Z ⊆ discInt c₀.R := by
    exact inserted_line_interior_stays_in_cell (T := T) (D := D) (E := E) (ι := ι) (q := q) (x :=
      x) (t := t) hman (s := s) (F := F) h hq (j := j) hoff hqD c₀ hc₀ hxa hcell hs₁ hs₂  hZbd
  have hqR : q j ⊆ c₀.R := fun w hw => closure_minimal (hZin.trans (discInt_subset _))
    hcell.disc.isClosed ((hq j).line.subset_closure_diff hw)
  have htb : t j ∈ c₀.b := by
    exact right_end_on_cell_top (T := T) (D := D) (E := E) (ι := ι) (q := q) (x := x) (t := t) hq
      (j := j) c₀ hcell hqR
  have hend : ∀ k ∈ s, ∀ {w}, w ∈ q k → w ∉ q j := fun k hk {w} h1 h2 => hoff k hk h2 h1
  have hx₁ : x j ≠ x c₀.i := fun he => hoff _ hs₁ (hq j).line.left_mem (he ▸ (hq _).line.left_mem)
  have hx₂ : x j ≠ x c₀.i' := fun he => hoff _ hs₂ (hq j).line.left_mem (he ▸ (hq _).line.left_mem)
  have ht₁ : t j ≠ t c₀.i := fun he => hoff _ hs₁ (hq j).line.right_mem (he ▸ (hq _).line.right_mem)
  have ht₂ : t j ≠ t c₀.i' := fun he => hoff _ hs₂ (hq j).line.right_mem (he ▸
    (hq _).line.right_mem)
  obtain ⟨a₁, a₂, ha₁, ha₂, hau, hai⟩ := hcell.bottom.split hxa hx₁ hx₂
  obtain ⟨b₁, b₂, hb₁, hb₂, hbu, hbi⟩ := hcell.top.split htb ht₁ ht₂
  have ha₁s : a₁ ⊆ c₀.a := hau ▸ subset_union_left
  have ha₂s : a₂ ⊆ c₀.a := hau ▸ subset_union_right
  have hb₁s : b₁ ⊆ c₀.b := hbu ▸ subset_union_left
  have hb₂s : b₂ ⊆ c₀.b := hbu ▸ subset_union_right
  set l := q c₀.i with hl
  set r := q c₀.i' with hr
  have hal : ∀ {w}, w ∈ c₀.a → w ∈ l → w = x c₀.i := fun {w} h1 h2 => by
    have h3 : w ∈ c₀.a ∩ l := ⟨h1, h2⟩
    rwa [hcell.al] at h3
  have har : ∀ {w}, w ∈ c₀.a → w ∈ r → w = x c₀.i' := fun {w} h1 h2 => by
    have h3 : w ∈ c₀.a ∩ r := ⟨h1, h2⟩
    rwa [hcell.ar] at h3
  have hbl : ∀ {w}, w ∈ c₀.b → w ∈ l → w = t c₀.i := fun {w} h1 h2 => by
    have h3 : w ∈ c₀.b ∩ l := ⟨h1, h2⟩
    rwa [hcell.bl] at h3
  have hbr : ∀ {w}, w ∈ c₀.b → w ∈ r → w = t c₀.i' := fun {w} h1 h2 => by
    have h3 : w ∈ c₀.b ∩ r := ⟨h1, h2⟩
    rwa [hcell.br] at h3
  have hab : ∀ {w}, w ∈ c₀.a → w ∉ c₀.b := fun {w} h1 h2 => disjoint_left.mp hcell.ab h1 h2
  have hlr : ∀ {w}, w ∈ l → w ∉ r := fun {w} h1 h2 => disjoint_left.mp hcell.ll h1 h2
  have ha₁₂ : ∀ {w}, w ∈ a₁ → w ∈ a₂ → w = x j := fun {w} h1 h2 => by
    have h3 : w ∈ a₁ ∩ a₂ := ⟨h1, h2⟩
    rwa [hai] at h3
  have hb₁₂ : ∀ {w}, w ∈ b₁ → w ∈ b₂ → w = t j := fun {w} h1 h2 => by
    have h3 : w ∈ b₁ ∩ b₂ := ⟨h1, h2⟩
    rwa [hbi] at h3
  -- The two arcs of the boundary of the cell between the ends of the line.
  have hM₁a : IsLineWithEnds (a₁ ∪ l) (x j) (t c₀.i) := ha₁.symm.union hcell.left (subset_antisymm
    (fun w hw => hal (ha₁s hw.1) hw.2) (by
    rintro _ rfl
    exact ⟨ha₁.left_mem, hcell.left.left_mem⟩))
  have hM₁ : IsLineWithEnds ((a₁ ∪ l) ∪ b₁) (x j) (t j) := hM₁a.union hb₁ (subset_antisymm (by
    rintro w ⟨h1 | h1, h2⟩
    · exact absurd (hb₁s h2) (hab (ha₁s h1))
    · exact hbl (hb₁s h2) h1) (by
    rintro _ rfl
    exact ⟨.inr hcell.left.right_mem, hb₁.left_mem⟩))
  have hM₂a : IsLineWithEnds (a₂ ∪ r) (x j) (t c₀.i') := ha₂.union hcell.right (subset_antisymm
    (fun w hw => har (ha₂s hw.1) hw.2) (by
    rintro _ rfl
    exact ⟨ha₂.right_mem, hcell.right.left_mem⟩))
  have hM₂ : IsLineWithEnds ((a₂ ∪ r) ∪ b₂) (x j) (t j) := hM₂a.union hb₂.symm (subset_antisymm (by
    rintro w ⟨h1 | h1, h2⟩
    · exact absurd (hb₂s h2) (hab (ha₂s h1))
    · exact hbr (hb₂s h2) h1) (by
    rintro _ rfl
    exact ⟨.inr hcell.right.right_mem, hb₂.right_mem⟩))
  have hM₁₂ : ((a₁ ∪ l) ∪ b₁) ∩ ((a₂ ∪ r) ∪ b₂) = {x j, t j} := by
    exact split_cell_arcs_meet_only_at_new_ends (T := T) (ι := ι) (x := x) (t := t) (j := j) c₀
      hx₁ hx₂ ht₁ ht₂ a₁ a₂ ha₁ ha₂ b₁ b₂ hb₁ hb₂ ha₁s ha₂s hb₁s hb₂s l r hal har hbl hbr hab hlr
      ha₁₂ hb₁₂
  have hqM : ∀ {A₀ B₀ : Set T}, A₀ ⊆ c₀.a → B₀ ⊆ c₀.b → ∀ k ∈ s, x j ∈ A₀ → t j ∈ B₀ → q j ∩
    ((A₀ ∪ q k) ∪ B₀) = {x j, t j} := fun {A₀ B₀} h1 h2 k hk h3 h4 => by
    exact inserted_line_meets_boundary_route_only_at_ends (T := T) (D := D) (E := E) (ι := ι) (q
      := q) (x := x) (t := t) (s := s) (F := F) hq (j := j) hoff hqD hqE c₀ hc₀ hbE haD (A₀ := A₀)
      (B₀ := B₀) h1 h2 k hk h3 h4
  have hqM₁ := hqM ha₁s hb₁s c₀.i hs₁ ha₁.right_mem hb₁.right_mem
  have hqM₂ := hqM ha₂s hb₂s c₀.i' hs₂ ha₂.left_mem hb₂.left_mem
  have hbdR : discBd c₀.R = ((a₁ ∪ l) ∪ b₁) ∪ ((a₂ ∪ r) ∪ b₂) := by
    rw [hcell.bd_eq, ← hau, ← hbu]
    ac_rfl
  obtain ⟨E₁, E₂, h1, h2, hu, hin, hb1, hb2⟩ := GM12.split_with_arcs hcell.disc
    (hq j).line hM₁ hM₂ hM₁₂ hqM₁ hqM₂ hbdR hqR hxt
  have hqb : q j ∩ discBd c₀.R = {x j, t j} := by
    rw [hbdR, inter_union_distrib_left, hqM₁, hqM₂, union_self]
  have hcell₁ : IsCell D E E₁ a₁ b₁ l (q j) (x c₀.i) (x j) (t c₀.i) (t j) := hcell.half
    (hq j).line hqb hx₁.symm ht₁.symm ha₁ ha₂ hau hai hb₁ hb₂ hbu hbi h1 hb1 hb2 hu hin
  have hcell₂ : IsCell D E E₂ a₂ b₂ (q j) r (x j) (x c₀.i') (t j) (t c₀.i') :=
    (hcell.swap.half (hq j).line hqb hx₂.symm ht₂.symm
    ha₂.symm ha₁.symm (by rw [union_comm]; exact hau) (by rw [inter_comm]; exact hai) hb₂.symm
    hb₁.symm (by rw [union_comm]; exact hbu) (by rw [inter_comm]; exact hbi) h2 hb2 hb1
    (by rw [union_comm]; exact hu) (by rw [inter_comm]; exact hin)).swap
  have hE₁R : E₁ ⊆ c₀.R := hu ▸ subset_union_left
  have hE₂R : E₂ ⊆ c₀.R := hu ▸ subset_union_right
  have hlE₁ : l ⊆ E₁ := hcell₁.l_sub.trans (Surface.discBd_subset _)
  have hrE₂ : r ⊆ E₂ := hcell₂.r_sub.trans (Surface.discBd_subset _)
  let c₁ : CellRec T ι := ⟨E₁, a₁, b₁, c₀.i, j⟩
  let c₂ : CellRec T ι := ⟨E₂, a₂, b₂, j, c₀.i'⟩
  have hin' : ∀ {w}, w ∈ E₁ → w ∈ E₂ → w ∈ q j := fun {w} h3 h4 => hin ▸ (⟨h3, h4⟩ : w ∈ E₁ ∩ E₂)
  have hc₁ : ∀ c ∈ F, c ≠ c₀ → ∀ w, w ∈ E₁ → w ∈ c.R → ∃ k, (k = c₀.i ∨ k = j) ∧ (k = c.i ∨ k
    = c.i') ∧ w ∈ q k := fun c hc hne w h3 h4 => by
    obtain ⟨k, hk, hk', hw⟩ := h.meet c₀ hc₀ c hc hne.symm w (hE₁R h3) h4
    rcases hk with rfl | rfl
    · exact ⟨_, .inl rfl, hk', hw⟩
    · exact absurd (hin' h3 (hrE₂ hw)) (hend _ hs₂ hw)
  have hc₂ : ∀ c ∈ F, c ≠ c₀ → ∀ w, w ∈ E₂ → w ∈ c.R → ∃ k, (k = j ∨ k = c₀.i') ∧ (k = c.i ∨ k
    = c.i') ∧ w ∈ q k := fun c hc hne w h3 h4 => by
    obtain ⟨k, hk, hk', hw⟩ := h.meet c₀ hc₀ c hc hne.symm w (hE₂R h3) h4
    rcases hk with rfl | rfl
    · exact absurd (hin' (hlE₁ hw) h3) (hend _ hs₁ hw)
    · exact ⟨_, .inr rfl, hk', hw⟩
  refine ⟨Insert.insert c₁ (Insert.insert c₂ (F \ {c₀})), ⟨((h.finite.subset sdiff_subset).insert
    _).insert _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro c (rfl | rfl | hc)
    · exact hcell₁
    · exact hcell₂
    · exact h.cell c hc.1
  · rintro c (rfl | rfl | hc) c' (rfl | rfl | hc') hne w h3 h4
    · exact absurd rfl hne
    · exact ⟨j, .inr rfl, .inl rfl, hin' h3 h4⟩
    · obtain ⟨k, h5, h6, h7⟩ := hc₁ c' hc'.1 hc'.2 w h3 h4
      exact ⟨k, h5, h6, h7⟩
    · exact ⟨j, .inl rfl, .inr rfl, hin' h4 h3⟩
    · exact absurd rfl hne
    · obtain ⟨k, h5, h6, h7⟩ := hc₂ c' hc'.1 hc'.2 w h3 h4
      exact ⟨k, h5, h6, h7⟩
    · obtain ⟨k, h5, h6, h7⟩ := hc₁ c hc.1 hc.2 w h4 h3
      exact ⟨k, h6, h5, h7⟩
    · obtain ⟨k, h5, h6, h7⟩ := hc₂ c hc.1 hc.2 w h4 h3
      exact ⟨k, h6, h5, h7⟩
    · exact h.meet c hc.1 c' hc'.1 hne w h3 h4
  · intro w hw
    rcases h.cover w hw with h3 | ⟨c, hc, h3⟩
    · exact .inl h3
    · by_cases he : c = c₀
      · subst he
        rw [← hu] at h3
        rcases h3 with h3 | h3
        · exact .inr ⟨c₁, .inl rfl, h3⟩
        · exact .inr ⟨c₂, .inr (.inl rfl), h3⟩
      · exact .inr ⟨c, .inr (.inr ⟨hc, he⟩), h3⟩
  · intro w hw
    obtain ⟨c, hc, h3⟩ := h.botCover w hw
    by_cases he : c = c₀
    · subst he
      rw [← hau] at h3
      rcases h3 with h3 | h3
      · exact ⟨c₁, .inl rfl, h3⟩
      · exact ⟨c₂, .inr (.inl rfl), h3⟩
    · exact ⟨c, .inr (.inr ⟨hc, he⟩), h3⟩
  · intro w hw
    obtain ⟨c, hc, h3⟩ := h.topCover w hw
    by_cases he : c = c₀
    · subst he
      rw [← hbu] at h3
      rcases h3 with h3 | h3
      · exact ⟨c₁, .inl rfl, h3⟩
      · exact ⟨c₂, .inr (.inl rfl), h3⟩
    · exact ⟨c, .inr (.inr ⟨hc, he⟩), h3⟩
  · rintro c (rfl | rfl | hc)
    · exact ⟨.inr hs₁, .inl rfl⟩
    · exact ⟨.inl rfl, .inr hs₂⟩
    · exact ⟨.inr (h.side c hc.1).1, .inr (h.side c hc.1).2⟩
  · rintro k (rfl | hk)
    · exact ⟨c₁, .inl rfl, .inr rfl⟩
    · obtain ⟨c, hc, h3⟩ := h.used k hk
      by_cases he : c = c₀
      · subst he
        rcases h3 with h3 | h3
        · exact ⟨c₁, .inl rfl, .inl h3⟩
        · exact ⟨c₂, .inr (.inl rfl), .inr h3⟩
      · exact ⟨c, .inr (.inr ⟨hc, he⟩), h3⟩

/-- **The cells of the annulus.** All the lines together cut the annulus between `D` and `E` into
cells, each with two of the lines as its sides. -/
theorem exists_cell_family [Finite ι] (hman : ∀ x : T, IsManifoldPoint x) (hD : IsClosedDisc D)
  (hE : IsClosedDisc E) (hDE : D ⊆ E \ discBd E) (hq : ∀ k, IsCrossLine D E (q k) (x k) (t k))
    (hdis : ∀ k k', k ≠ k' → Disjoint (q k) (q k')) {i₀ i₁ : ι} (hi : i₀ ≠ i₁) : ∃ F, IsCellFamily
      D E q x t univ F := by
  classical
  have := Fintype.ofFinite ι
  have hd : Disjoint D (discBd E) := disjoint_left.mpr fun z hz h => (hDE hz).2 h
  obtain ⟨R₁, R₂, a₁, a₂, b₁, b₂, h₁, h₂, hm, ha, hb, hc⟩ := exists_two_cells hman hD hE hDE
    (hq i₀) (hq i₁) (hdis _ _ hi)
  let c₁ : CellRec T ι := ⟨R₁, a₁, b₁, i₀, i₁⟩
  let c₂ : CellRec T ι := ⟨R₂, a₂, b₂, i₀, i₁⟩
  have hbase : IsCellFamily D E q x t {i₀, i₁} {c₁, c₂} := by
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro c (rfl | rfl)
      · exact h₁
      · exact h₂
    · rintro c (rfl | rfl) c' (rfl | rfl) hne w h3 h4
      · exact absurd rfl hne
      · rcases hm ⟨h3, h4⟩ with h5 | h5
        · exact ⟨i₀, .inl rfl, .inl rfl, h5⟩
        · exact ⟨i₁, .inr rfl, .inr rfl, h5⟩
      · rcases hm ⟨h4, h3⟩ with h5 | h5
        · exact ⟨i₀, .inl rfl, .inl rfl, h5⟩
        · exact ⟨i₁, .inr rfl, .inr rfl, h5⟩
      · exact absurd rfl hne
    · intro w hw
      rw [← hc] at hw
      rcases hw with (h3 | h3) | h3
      · exact .inr ⟨c₁, .inl rfl, h3⟩
      · exact .inr ⟨c₂, .inr rfl, h3⟩
      · exact .inl h3
    · intro w hw
      rw [← ha] at hw
      rcases hw with h3 | h3
      · exact ⟨c₁, .inl rfl, h3⟩
      · exact ⟨c₂, .inr rfl, h3⟩
    · intro w hw
      rw [← hb] at hw
      rcases hw with h3 | h3
      · exact ⟨c₁, .inl rfl, h3⟩
      · exact ⟨c₂, .inr rfl, h3⟩
    · rintro c (rfl | rfl)
      · exact ⟨.inl rfl, .inr rfl⟩
      · exact ⟨.inl rfl, .inr rfl⟩
    · rintro k (rfl | rfl)
      · exact ⟨c₁, .inl rfl, .inl rfl⟩
      · exact ⟨c₁, .inl rfl, .inr rfl⟩
  have hall : ∀ s : Finset ι, ∃ F, IsCellFamily D E q x t ({i₀, i₁} ∪ (s : Set ι)) F := fun s => by
    induction s using Finset.induction_on with
    | empty => exact ⟨_, by simpa using hbase⟩
    | insert j s _ ih =>
      obtain ⟨F, hF⟩ := ih
      by_cases hj : j ∈ ({i₀, i₁} ∪ (s : Set ι))
      · refine ⟨F, ?_⟩
        have : ({i₀, i₁} ∪ ((Insert.insert j s : Finset ι) : Set ι)) = {i₀, i₁} ∪ (s : Set ι) := by
          rw [Finset.coe_insert, union_insert]
          exact insert_eq_of_mem hj
        rwa [this]
      · obtain ⟨F', hF'⟩ := hF.insert hman hd hq hdis hj
        refine ⟨F', ?_⟩
        have : ({i₀, i₁} ∪ ((Insert.insert j s : Finset ι) : Set ι)) = Insert.insert j ({i₀, i₁} ∪
          (s : Set ι)) := by
          rw [Finset.coe_insert, union_insert]
        rwa [this]
  obtain ⟨F, hF⟩ := hall Finset.univ
  exact ⟨F, by simpa using hF⟩

end Family

end GraphMinor.GM07
