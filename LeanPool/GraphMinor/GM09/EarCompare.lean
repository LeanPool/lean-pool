/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.EarDisc

/-!
# Comparing two ears on a closed disc

Fix a closed disc `Δ₀` in the plane. An ear is a line with both ends on the boundary of `Δ₀` and no
other point in `Δ₀`, and `EarData` records the disc it cuts off. Here we show that two ears with
disjoint open parts have nested discs, or discs that meet only in common ends. We also show what
happens with three lines from one point. These are the facts behind (11.1) of Graph Minors IX.
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

/-- A connected set that misses the boundary of a closed disc lies inside it or outside it. -/
theorem subset_interior_or_compl {W T : Set EuclideanPlane} (hW : IsClosedDisc W)
    (hT : IsPreconnected T) (hd : Disjoint T (discBd W)) : T ⊆ interior W ∨ T ⊆ Wᶜ := by
  refine IsPreconnected.subset_or_subset isOpen_interior hW.isCompact.isClosed.isOpen_compl
    (disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx)) (fun x hx => ?_) hT
  by_cases hxW : x ∈ W
  · left
    rw [interior_eq_discInt_plane hW]
    exact ⟨hxW, disjoint_left.mp hd hx⟩
  · exact Or.inr hxW

/-- If the boundary of a closed disc lies in another closed disc, so does the whole disc. -/
theorem subset_of_discBd_subset {W W' : Set EuclideanPlane} (hW : IsClosedDisc W)
    (hW' : IsClosedDisc W') (h : discBd W' ⊆ W) : W' ⊆ W := by
  have hc := isPreconnected_compl_of_isClosedDisc hW
  have hd : Disjoint Wᶜ (discBd W') := disjoint_left.mpr fun x hx hx' => hx (h hx')
  rcases subset_interior_or_compl hW' hc hd with hs | hs
  · exfalso
    have hu : W ∪ W' = univ := by
      ext x
      simp only [mem_union, mem_univ, iff_true]
      by_cases hx : x ∈ W
      · exact Or.inl hx
      · exact Or.inr (interior_subset (hs hx))
    have hcpt : IsCompact (univ : Set EuclideanPlane) := hu ▸ hW.isCompact.union hW'.isCompact
    have : NoncompactSpace EuclideanPlane := NormedSpace.noncompactSpace ℝ _
    exact noncompact_univ _ hcpt
  · intro x hx
    by_contra hn
    exact hs hn hx

/-- Two closed discs in the plane with the same boundary are equal. -/
theorem eq_of_discBd_eq {W W' : Set EuclideanPlane} (hW : IsClosedDisc W) (hW' : IsClosedDisc W')
    (h : discBd W = discBd W') : W = W' :=
  Subset.antisymm (subset_of_discBd_subset hW' hW (h ▸ Surface.discBd_subset W'))
    (subset_of_discBd_subset hW hW' (h ▸ Surface.discBd_subset W))

theorem closure_interior_of_isClosedDisc {W : Set EuclideanPlane} (hW : IsClosedDisc W) :
    closure (interior W) = W := by
  refine Subset.antisymm (closure_minimal interior_subset hW.isCompact.isClosed) ?_
  rw [interior_eq_discInt_plane hW]
  exact hW.subset_closure_discInt

/-- A line with the same ends as two lines that meet only in those ends, and that lies in their
union, is one of the two lines. -/
theorem line_eq_or_eq_of_subset_union {R T₁ T₂ : Set EuclideanPlane}
    {m z : EuclideanPlane} (hR : IsLineWithEnds R m z) (h₁ : IsLineWithEnds T₁ m z)
    (h₂ : IsLineWithEnds T₂ m z) (hi : T₁ ∩ T₂ = {m, z}) (hs : R ⊆ T₁ ∪ T₂) :
    R = T₁ ∨ R = T₂ := by
  have hRo := hR.isPreconnected_diff
  have hsub : ∀ {T : Set EuclideanPlane}, IsLineWithEnds T m z → R \ {m, z} ⊆ T → R = T := by
    intro T hT hRT
    have hRs : R ⊆ T := by
      intro w hw
      by_cases hm : w ∈ ({m, z} : Set EuclideanPlane)
      · rcases hm with rfl | rfl
        · exact hT.left_mem
        · exact hT.right_mem
      · exact hRT ⟨hw, hm⟩
    exact hT.eq_of_subset (hR.isPreconnected_diff.subset_closure sdiff_subset
      hR.subset_closure_diff) hRs hR.left_mem hR.right_mem
  rw [isPreconnected_closed_iff] at hRo
  by_cases hn₁ : ((R \ {m, z}) ∩ T₁).Nonempty
  · by_cases hn₂ : ((R \ {m, z}) ∩ T₂).Nonempty
    · exfalso
      obtain ⟨w, hw, hw₁, hw₂⟩ := hRo T₁ T₂ h₁.isCompact.isClosed h₂.isCompact.isClosed
        (fun w hw => hs hw.1) hn₁ hn₂
      exact hw.2 (hi ▸ ⟨hw₁, hw₂⟩)
    · left
      refine hsub h₁ fun w hw => (hs hw.1).resolve_right fun h => hn₂ ⟨w, hw, h⟩
  · right
    refine hsub h₂ fun w hw => (hs hw.1).resolve_left fun h => hn₁ ⟨w, hw, h⟩

/-- The data of an ear on `Δ₀`: the line `c` with ends `a`, `b`, the disc `L` it cuts off, and the
parts `A`, `B` of the boundary of `Δ₀` under `L` and away from `L`. -/
structure EarData (Δ₀ c L A B : Set EuclideanPlane) (a b : EuclideanPlane) : Prop where
  disc₀ : IsClosedDisc Δ₀
  line : IsLineWithEnds c a b
  ne : a ≠ b
  left_mem : a ∈ discBd Δ₀
  right_mem : b ∈ discBd Δ₀
  inter_c : c ∩ Δ₀ ⊆ {a, b}
  lineA : IsLineWithEnds A a b
  lineB : IsLineWithEnds B a b
  union : A ∪ B = discBd Δ₀
  inter : A ∩ B = {a, b}
  disc : IsClosedDisc L
  bdL : discBd L = A ∪ c
  L_inter : L ∩ Δ₀ = A
  discW : IsClosedDisc (Δ₀ ∪ L)
  bdW : discBd (Δ₀ ∪ L) = B ∪ c

/-- Every line with the right ends is an ear. -/
theorem exists_earData {Δ₀ c : Set EuclideanPlane} {a b : EuclideanPlane} (h₀ : IsClosedDisc Δ₀)
    (hc : IsLineWithEnds c a b) (hab : a ≠ b) (ha : a ∈ discBd Δ₀) (hb : b ∈ discBd Δ₀)
    (hi : c ∩ Δ₀ ⊆ {a, b}) : ∃ L A B, EarData Δ₀ c L A B a b := by
  obtain ⟨A, B, L, hA, hB, hu, hin, hL, hbL, hLi, hW, hbW⟩ := exists_ear_disc h₀ hc hab ha hb hi
  exact ⟨L, A, B, ⟨h₀, hc, hab, ha, hb, hi, hA, hB, hu, hin, hL, hbL, hLi, hW, hbW⟩⟩

namespace EarData

variable {Δ₀ c L A B c' L' A' B' : Set EuclideanPlane} {a b a' b' : EuclideanPlane}

theorem c_subset_L (E : EarData Δ₀ c L A B a b) : c ⊆ L :=
  fun _ hx => Surface.discBd_subset L (E.bdL ▸ Or.inr hx)

theorem A_subset_L (E : EarData Δ₀ c L A B a b) : A ⊆ L :=
  fun _ hx => Surface.discBd_subset L (E.bdL ▸ Or.inl hx)

theorem A_subset (E : EarData Δ₀ c L A B a b) : A ⊆ discBd Δ₀ := E.union ▸ subset_union_left

theorem B_subset (E : EarData Δ₀ c L A B a b) : B ⊆ discBd Δ₀ := E.union ▸ subset_union_right

theorem left_mem_c (E : EarData Δ₀ c L A B a b) : a ∈ c := E.line.left_mem

theorem right_mem_c (E : EarData Δ₀ c L A B a b) : b ∈ c := E.line.right_mem

theorem disjoint_open (E : EarData Δ₀ c L A B a b) : Disjoint (c \ {a, b}) Δ₀ :=
  disjoint_left.mpr fun _ hx hx' => hx.2 (E.inter_c ⟨hx.1, hx'⟩)

theorem isPreconnected_open (E : EarData Δ₀ c L A B a b) : IsPreconnected (c \ {a, b}) :=
  E.line.isPreconnected_diff

theorem nonempty_open (E : EarData Δ₀ c L A B a b) : (c \ {a, b}).Nonempty :=
  E.line.nonempty_sdiff

theorem c_subset_W (E : EarData Δ₀ c L A B a b) : c ⊆ Δ₀ ∪ L :=
  fun _ hx => Or.inr (E.c_subset_L hx)

/-- The interior of the disc of an ear misses `Δ₀`. -/
theorem disjoint_interior (E : EarData Δ₀ c L A B a b) : Disjoint (interior L) Δ₀ := by
  rw [disjoint_left]
  intro x hx hx₀
  have hxA : x ∈ A := E.L_inter ▸ ⟨interior_subset hx, hx₀⟩
  have hb : x ∈ discBd L := E.bdL ▸ Or.inl hxA
  rw [interior_eq_discInt_plane E.disc] at hx
  exact hx.2 hb

/-- A point of `Δ₀ ∪ L` outside `Δ₀` is in `L`. -/
theorem mem_L_of_mem_W (_E : EarData Δ₀ c L A B a b) {x : EuclideanPlane} (hx : x ∈ Δ₀ ∪ L)
    (hn : x ∉ Δ₀) : x ∈ L := hx.resolve_left hn

theorem L_subset_of_W_subset (E : EarData Δ₀ c L A B a b) {X : Set EuclideanPlane}
    (hX : IsClosed X) (hs : Δ₀ ∪ L ⊆ Δ₀ ∪ X) : L ⊆ X := by
  rw [← closure_interior_of_isClosedDisc E.disc]
  refine closure_minimal (fun x hx => ?_) hX
  exact (hs (Or.inr (interior_subset hx))).resolve_left (disjoint_left.mp E.disjoint_interior hx)

/-- If the open part of a second ear lies in the disc of the first, so does the disc of the
second. -/
theorem subset_of_open_subset (E : EarData Δ₀ c L A B a b) (E' : EarData Δ₀ c' L' A' B' a' b')
    (h : c' \ {a', b'} ⊆ L) : L' ⊆ L := by
  refine E'.L_subset_of_W_subset E.disc.isCompact.isClosed
    (subset_of_discBd_subset E.discW E'.discW ?_)
  rw [E'.bdW]
  rintro x (hx | hx)
  · exact Or.inl (Surface.discBd_subset _ (E'.B_subset hx))
  · by_cases hm : x ∈ ({a', b'} : Set EuclideanPlane)
    · rcases hm with rfl | rfl
      · exact Or.inl (Surface.discBd_subset _ E'.left_mem)
      · exact Or.inl (Surface.discBd_subset _ E'.right_mem)
    · exact Or.inr (h ⟨hx, hm⟩)

/-- The open part of a second ear lies in the disc of the first or outside its union with `Δ₀`,
provided the two open parts are disjoint. -/
theorem open_subset_or (E : EarData Δ₀ c L A B a b) (E' : EarData Δ₀ c' L' A' B' a' b')
    (hd : Disjoint (c \ {a, b}) (c' \ {a', b'})) :
    c' \ {a', b'} ⊆ L ∨ c' \ {a', b'} ⊆ (Δ₀ ∪ L)ᶜ := by
  have hdb : Disjoint (c' \ {a', b'}) (discBd (Δ₀ ∪ L)) := by
    rw [E.bdW, disjoint_left]
    rintro x hx (hb | hc)
    · exact disjoint_left.mp E'.disjoint_open hx (Surface.discBd_subset _ (E.B_subset hb))
    · by_cases hm : x ∈ ({a, b} : Set EuclideanPlane)
      · refine disjoint_left.mp E'.disjoint_open hx ?_
        rcases hm with rfl | rfl
        · exact Surface.discBd_subset _ E.left_mem
        · exact Surface.discBd_subset _ E.right_mem
      · exact disjoint_left.mp hd ⟨hc, hm⟩ hx
  rcases subset_interior_or_compl E.discW E'.isPreconnected_open hdb with hs | hs
  · left
    intro x hx
    exact (interior_subset (hs hx)).resolve_left (disjoint_left.mp E'.disjoint_open hx)
  · exact Or.inr hs

/-- Two ears with disjoint open parts have nested discs, or discs that meet in common ends. -/
theorem nested_or_inter (E : EarData Δ₀ c L A B a b) (E' : EarData Δ₀ c' L' A' B' a' b')
    (hd : Disjoint (c \ {a, b}) (c' \ {a', b'})) :
    L' ⊆ L ∨ L ⊆ L' ∨ L ∩ L' ⊆ {a, b} ∩ {a', b'} := by
  rcases E.open_subset_or E' hd with h₁ | h₁
  · exact Or.inl (E.subset_of_open_subset E' h₁)
  rcases E'.open_subset_or E hd.symm with h₂ | h₂
  · exact Or.inr (Or.inl (E'.subset_of_open_subset E h₂))
  -- Each disc misses the interior of the other union.
  have hout : ∀ {c₁ L₁ A₁ B₁ c₂ L₂ A₂ B₂ : Set EuclideanPlane} {a₁ b₁ a₂ b₂ : EuclideanPlane},
      EarData Δ₀ c₁ L₁ A₁ B₁ a₁ b₁ → EarData Δ₀ c₂ L₂ A₂ B₂ a₂ b₂ →
      c₁ \ {a₁, b₁} ⊆ (Δ₀ ∪ L₂)ᶜ → c₂ \ {a₂, b₂} ⊆ (Δ₀ ∪ L₁)ᶜ →
      interior L₁ ⊆ (Δ₀ ∪ L₂)ᶜ := by
    intro c₁ L₁ A₁ B₁ c₂ L₂ A₂ B₂ a₁ b₁ a₂ b₂ E₁ E₂ h₁ h₂
    have hdb : Disjoint (interior L₁) (discBd (Δ₀ ∪ L₂)) := by
      rw [E₂.bdW, disjoint_left]
      intro x hx hb
      have hxL : x ∈ L₁ := interior_subset hx
      have hx₀ : x ∉ Δ₀ := disjoint_left.mp E₁.disjoint_interior hx
      rcases hb with hb | hc
      · exact hx₀ (Surface.discBd_subset _ (E₂.B_subset hb))
      · by_cases hm : x ∈ ({a₂, b₂} : Set EuclideanPlane)
        · rcases hm with rfl | rfl
          · exact hx₀ (Surface.discBd_subset _ E₂.left_mem)
          · exact hx₀ (Surface.discBd_subset _ E₂.right_mem)
        · exact h₂ ⟨hc, hm⟩ (Or.inr hxL)
    have hconn : IsPreconnected (interior L₁) := by
      rw [interior_eq_discInt_plane E₁.disc]
      exact E₁.disc.isPreconnected_discInt
    rcases subset_interior_or_compl E₂.discW hconn hdb with hs | hs
    · exfalso
      have hsub : L₁ ⊆ L₂ := E₁.L_subset_of_W_subset E₂.disc.isCompact.isClosed (by
        apply union_subset_union_right Δ₀ ?_ |>.trans (Subset.refl _)
        rw [← closure_interior_of_isClosedDisc E₁.disc]
        refine closure_minimal (fun x hx => ?_) E₂.disc.isCompact.isClosed
        exact (interior_subset (hs hx)).resolve_left (disjoint_left.mp E₁.disjoint_interior hx))
      obtain ⟨y, hy⟩ := E₁.nonempty_open
      exact h₁ hy (Or.inr (hsub (E₁.c_subset_L hy.1)))
    · exact hs
  have hi₁ := hout E E' h₂ h₁
  have hi₂ := hout E' E h₁ h₂
  right
  right
  -- A point of both discs is on the boundary of both unions.
  have hbd : ∀ {c₁ L₁ A₁ B₁ L₂ : Set EuclideanPlane} {a₁ b₁ : EuclideanPlane},
      EarData Δ₀ c₁ L₁ A₁ B₁ a₁ b₁ → IsClosedDisc L₂ → interior L₂ ⊆ (Δ₀ ∪ L₁)ᶜ →
      ∀ x ∈ L₂, x ∈ Δ₀ ∪ L₁ → x ∈ B₁ ∪ c₁ := by
    intro c₁ L₁ A₁ B₁ L₂ a₁ b₁ E₁ hL₂ hi x hx hxW
    rw [← E₁.bdW]
    by_contra hn
    have hint : x ∈ interior (Δ₀ ∪ L₁) := by
      rw [interior_eq_discInt_plane E₁.discW]
      exact ⟨hxW, hn⟩
    rw [← closure_interior_of_isClosedDisc hL₂] at hx
    obtain ⟨y, hyi, hyL⟩ := mem_closure_iff.mp hx _ isOpen_interior hint
    exact hi hyL (interior_subset hyi)
  rintro x ⟨hx, hx'⟩
  have h₁' := hbd E' E.disc hi₁ x hx (Or.inr hx')
  have h₂' := hbd E E'.disc hi₂ x hx' (Or.inr hx)
  by_cases hx₀ : x ∈ Δ₀
  · have ha₁ : x ∈ A := E.L_inter ▸ ⟨hx, hx₀⟩
    have ha₂ : x ∈ A' := E'.L_inter ▸ ⟨hx', hx₀⟩
    refine ⟨?_, ?_⟩
    · rcases h₂' with h | h
      · exact E.inter ▸ ⟨ha₁, h⟩
      · exact E.inter_c ⟨h, hx₀⟩
    · rcases h₁' with h | h
      · exact E'.inter ▸ ⟨ha₂, h⟩
      · exact E'.inter_c ⟨h, hx₀⟩
  · exfalso
    have hc₁ : x ∈ c \ {a, b} := by
      rcases h₂' with h | h
      · exact (hx₀ (Surface.discBd_subset _ (E.B_subset h))).elim
      · refine ⟨h, ?_⟩
        rintro (rfl | rfl)
        · exact hx₀ (Surface.discBd_subset _ E.left_mem)
        · exact hx₀ (Surface.discBd_subset _ E.right_mem)
    have hc₂ : x ∈ c' \ {a', b'} := by
      rcases h₁' with h | h
      · exact (hx₀ (Surface.discBd_subset _ (E'.B_subset h))).elim
      · refine ⟨h, ?_⟩
        rintro (rfl | rfl)
        · exact hx₀ (Surface.discBd_subset _ E'.left_mem)
        · exact hx₀ (Surface.discBd_subset _ E'.right_mem)
    exact disjoint_left.mp hd hc₁ hc₂

/-- A closed disc bounded by the line of an ear and a line in the boundary of `Δ₀` with the same
ends is the disc `L` of the ear or the union of `L` with `Δ₀`. -/
theorem eq_or_eq_of_discBd (E : EarData Δ₀ c L A B a b) {W T : Set EuclideanPlane}
    (hW : IsClosedDisc W) (hT : IsLineWithEnds T a b) (hTs : T ⊆ discBd Δ₀)
    (hb : discBd W = c ∪ T) : W = L ∨ W = Δ₀ ∪ L := by
  have hTu : T ⊆ A ∪ B := E.union ▸ hTs
  rcases line_eq_or_eq_of_subset_union hT E.lineA E.lineB E.inter hTu with rfl | rfl
  · left
    exact eq_of_discBd_eq hW E.disc (by rw [hb, E.bdL, union_comm])
  · right
    exact eq_of_discBd_eq hW E.discW (by rw [hb, E.bdW, union_comm])

/-- If a closed disc contains `Δ₀`, and is bounded by the line of an ear and a line in the boundary
of `Δ₀`, then it is the union of `Δ₀` with the disc of the ear. -/
theorem eq_W_of_discBd (E : EarData Δ₀ c L A B a b) {W T : Set EuclideanPlane}
    (hW : IsClosedDisc W) (hT : IsLineWithEnds T a b) (hTs : T ⊆ discBd Δ₀)
    (hb : discBd W = c ∪ T) (hsub : Δ₀ ⊆ W) : W = Δ₀ ∪ L := by
  rcases E.eq_or_eq_of_discBd hW hT hTs hb with rfl | h
  · exfalso
    obtain ⟨x, hx, hn⟩ := E.lineB.nonempty_sdiff
    have hxΔ : x ∈ Δ₀ := Surface.discBd_subset _ (E.B_subset hx)
    have hxA : x ∈ A := E.L_inter ▸ ⟨hsub hxΔ, hxΔ⟩
    exact hn (E.inter ▸ ⟨hxA, hx⟩)
  · exact h

/-- A point of the boundary of `Δ₀` that is not an end of the ear, and is a limit of points outside
`Δ₀ ∪ L`, is on the side `B` of the boundary away from `L`. -/
theorem mem_B_of_mem_closure (E : EarData Δ₀ c L A B a b) {z : EuclideanPlane}
    (hz : z ∈ discBd Δ₀) (hza : z ≠ a) (hzb : z ≠ b) (hcl : z ∈ closure (Δ₀ ∪ L)ᶜ) : z ∈ B := by
  by_contra hn
  have hzΔ : z ∈ Δ₀ := Surface.discBd_subset _ hz
  have hzA : z ∈ A := by
    have : z ∈ A ∪ B := E.union ▸ hz
    exact this.resolve_right hn
  have hzc : z ∉ c := fun h => by
    rcases E.inter_c ⟨h, hzΔ⟩ with h' | h'
    · exact hza h'
    · exact hzb h'
  have hi : z ∈ interior (Δ₀ ∪ L) := by
    rw [interior_eq_discInt_plane E.discW]
    refine ⟨Or.inl hzΔ, ?_⟩
    rw [E.bdW]
    rintro (h | h)
    · exact hn h
    · exact hzc h
  obtain ⟨y, hyi, hy⟩ := mem_closure_iff.mp hcl _ isOpen_interior hi
  exact hy (interior_subset hyi)

/-- Three lines from a point `m` outside `Δ₀` to points `x`, `y`, `z` of its boundary. If the line
to `z` leaves the union of `Δ₀` with the disc of the ear through `x` and `y`, then the line to `y`
lies in the disc of the ear through `x` and `z`, or the line to `x` lies in the disc of the ear
through `y` and `z`. -/
theorem leg_swap {ℓx ℓy ℓz L₁ A₁ B₁ L₂ A₂ B₂ L₃ A₃ B₃ : Set EuclideanPlane}
    {m x y z : EuclideanPlane} (E₁ : EarData Δ₀ (ℓx ∪ ℓy) L₁ A₁ B₁ x y)
    (E₂ : EarData Δ₀ (ℓx ∪ ℓz) L₂ A₂ B₂ x z) (E₃ : EarData Δ₀ (ℓy ∪ ℓz) L₃ A₃ B₃ y z)
    (hx : IsLineWithEnds ℓx m x) (hy : IsLineWithEnds ℓy m y) (hz : IsLineWithEnds ℓz m z)
    (hm : m ∉ Δ₀) (hzB : z ∈ B₁) (hzx : z ≠ x) (hzy : z ≠ y)
    (hxy : ℓx ∩ ℓy = {m}) (hout : ℓz \ {m, z} ⊆ (Δ₀ ∪ L₁)ᶜ) :
    ℓy \ {y} ⊆ L₂ ∨ ℓx \ {x} ⊆ L₃ := by
  have hmz : m ≠ z := fun h => hm (h ▸ Surface.discBd_subset _ E₂.right_mem)
  have hmbd : m ∈ discBd (Δ₀ ∪ L₁) := E₁.bdW ▸ Or.inr (Or.inl hx.left_mem)
  have hzbd : z ∈ discBd (Δ₀ ∪ L₁) := E₁.bdW ▸ Or.inl hzB
  have hi : ℓz ∩ (Δ₀ ∪ L₁) ⊆ {m, z} := by
    rintro w ⟨hw, hw'⟩
    by_contra hn
    exact hout ⟨hw, hn⟩ hw'
  obtain ⟨R, R', L₄, hR, hR', hRu, hRi, hL₄, -, -, hW₄, hb₄⟩ :=
    exists_ear_disc E₁.discW hz hmz hmbd hzbd hi
  obtain ⟨Bx, By, hBx, hBy, hBu, hBi⟩ := E₁.lineB.split hzB hzx hzy
  have hsBx : Bx ⊆ Δ₀ := fun w hw =>
    Surface.discBd_subset _ (E₁.B_subset (hBu ▸ Or.inl hw))
  have hsBy : By ⊆ Δ₀ := fun w hw =>
    Surface.discBd_subset _ (E₁.B_subset (hBu ▸ Or.inr hw))
  have hmx : m ≠ x := fun h => hm (h ▸ Surface.discBd_subset _ E₁.left_mem)
  have hmy : m ≠ y := fun h => hm (h ▸ Surface.discBd_subset _ E₁.right_mem)
  have hx_not : ∀ w ∈ ℓx, w ∈ Δ₀ → w = x := by
    intro w hw hw₀
    rcases E₁.inter_c ⟨Or.inl hw, hw₀⟩ with h | h
    · exact h
    · subst h
      have : w ∈ ℓx ∩ ℓy := ⟨hw, hy.right_mem⟩
      rw [hxy] at this
      exact (hmy this.symm).elim
  have hy_not : ∀ w ∈ ℓy, w ∈ Δ₀ → w = y := by
    intro w hw hw₀
    rcases E₁.inter_c ⟨Or.inr hw, hw₀⟩ with h | h
    · subst h
      have : w ∈ ℓx ∩ ℓy := ⟨hx.right_mem, hw⟩
      rw [hxy] at this
      exact (hmx this.symm).elim
    · exact h
  have hxBx : ℓx ∩ Bx = {x} := by
    ext w
    constructor
    · rintro ⟨h₁, h₂⟩
      exact hx_not w h₁ (hsBx h₂)
    · rintro rfl
      exact ⟨hx.right_mem, hBx.left_mem⟩
  have hyBy : ℓy ∩ By = {y} := by
    ext w
    constructor
    · rintro ⟨h₁, h₂⟩
      exact hy_not w h₁ (hsBy h₂)
    · rintro rfl
      exact ⟨hy.right_mem, hBy.right_mem⟩
  have hTx : IsLineWithEnds (ℓx ∪ Bx) m z := hx.union hBx hxBx
  have hTy : IsLineWithEnds (ℓy ∪ By) m z := hy.union hBy.symm hyBy
  have hTi : (ℓx ∪ Bx) ∩ (ℓy ∪ By) = {m, z} := by
    ext w
    constructor
    · rintro ⟨h₁ | h₁, h₂ | h₂⟩
      · have : w ∈ ℓx ∩ ℓy := ⟨h₁, h₂⟩
        rw [hxy] at this
        exact Or.inl this
      · exfalso
        have hwx := hx_not w h₁ (hsBy h₂)
        subst hwx
        have : w ∈ Bx ∩ By := ⟨hBx.left_mem, h₂⟩
        rw [hBi] at this
        exact hzx this.symm
      · exfalso
        have hwy := hy_not w h₂ (hsBx h₁)
        subst hwy
        have : w ∈ Bx ∩ By := ⟨h₁, hBy.right_mem⟩
        rw [hBi] at this
        exact hzy this.symm
      · have : w ∈ Bx ∩ By := ⟨h₁, h₂⟩
        rw [hBi] at this
        exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨Or.inl hx.left_mem, Or.inl hy.left_mem⟩
      · exact ⟨Or.inr hBx.right_mem, Or.inr hBy.left_mem⟩
  have hTu : (ℓx ∪ Bx) ∪ (ℓy ∪ By) = discBd (Δ₀ ∪ L₁) := by
    rw [E₁.bdW, ← hBu]
    ext w
    simp only [mem_union]
    tauto
  have hW₁₄ : Δ₀ ∪ L₁ ⊆ (Δ₀ ∪ L₁) ∪ L₄ := subset_union_left
  have hsTy : By ⊆ discBd Δ₀ := fun w hw => E₁.B_subset (hBu ▸ Or.inr hw)
  have hsTx : Bx ⊆ discBd Δ₀ := fun w hw => E₁.B_subset (hBu ▸ Or.inl hw)
  have hR'sub : R' ⊆ (ℓx ∪ Bx) ∪ (ℓy ∪ By) := by
    rw [hTu, ← hRu]
    exact subset_union_right
  rcases line_eq_or_eq_of_subset_union hR' hTx hTy hTi hR'sub with rfl | rfl
  · left
    have hWeq := E₂.eq_W_of_discBd hW₄ hBx hsTx
      (by rw [hb₄]; ext w; simp only [mem_union]; tauto)
      (subset_union_left.trans hW₁₄)
    intro w hw
    have hwW : w ∈ Δ₀ ∪ L₂ := hWeq ▸ hW₁₄ (E₁.c_subset_W (Or.inr hw.1))
    exact hwW.resolve_left fun h => hw.2 (hy_not w hw.1 h)
  · right
    have hWeq := E₃.eq_W_of_discBd hW₄ hBy.symm hsTy
      (by rw [hb₄]; ext w; simp only [mem_union]; tauto)
      (subset_union_left.trans hW₁₄)
    intro w hw
    have hwW : w ∈ Δ₀ ∪ L₃ := hWeq ▸ hW₁₄ (E₁.c_subset_W (Or.inl hw.1))
    exact hwW.resolve_left fun h => hw.2 (hx_not w hw.1 h)

/-- Three lines from a point `m` outside `Δ₀`. Either the line to `z` lies in the disc of the ear
through `x` and `y`, or that disc lies properly in the disc of one of the other two ears. -/
theorem third_leg {ℓx ℓy ℓz L₁ A₁ B₁ L₂ A₂ B₂ L₃ A₃ B₃ : Set EuclideanPlane}
    {m x y z : EuclideanPlane} (E₁ : EarData Δ₀ (ℓx ∪ ℓy) L₁ A₁ B₁ x y)
    (E₂ : EarData Δ₀ (ℓx ∪ ℓz) L₂ A₂ B₂ x z) (E₃ : EarData Δ₀ (ℓy ∪ ℓz) L₃ A₃ B₃ y z)
    (hx : IsLineWithEnds ℓx m x) (hy : IsLineWithEnds ℓy m y) (hz : IsLineWithEnds ℓz m z)
    (hm : m ∉ Δ₀) (hzx : z ≠ x) (hzy : z ≠ y) (hxy : ℓx ∩ ℓy = {m}) (hxz : ℓx ∩ ℓz = {m})
    (hyz : ℓy ∩ ℓz = {m}) :
    ℓz \ {m, z} ⊆ L₁ ∨ (L₁ ⊆ L₂ ∧ L₁ ≠ L₂) ∨ (L₁ ⊆ L₃ ∧ L₁ ≠ L₃) := by
  have hzΔ : z ∈ Δ₀ := Surface.discBd_subset _ E₂.right_mem
  have hz_not : ∀ w ∈ ℓz, w ∈ Δ₀ → w = z := by
    intro w hw hw₀
    rcases E₂.inter_c ⟨Or.inr hw, hw₀⟩ with h | h
    · subst h
      have : w ∈ ℓx ∩ ℓz := ⟨hx.right_mem, hw⟩
      rw [hxz] at this
      exact (hm (this ▸ hw₀)).elim
    · exact h
  have hd : Disjoint (ℓz \ {m, z}) (discBd (Δ₀ ∪ L₁)) := by
    rw [E₁.bdW, disjoint_left]
    rintro w ⟨hw, hn⟩ (h | h | h)
    · exact hn (Or.inr (hz_not w hw (Surface.discBd_subset _ (E₁.B_subset h))))
    · have : w ∈ ℓx ∩ ℓz := ⟨h, hw⟩
      rw [hxz] at this
      exact hn (Or.inl this)
    · have : w ∈ ℓy ∩ ℓz := ⟨h, hw⟩
      rw [hyz] at this
      exact hn (Or.inl this)
  rcases subset_interior_or_compl E₁.discW hz.isPreconnected_diff hd with hs | hs
  · left
    intro w hw
    refine (interior_subset (hs hw)).resolve_left fun h => hw.2 (Or.inr (hz_not w hw.1 h))
  right
  have hzB : z ∈ B₁ := by
    refine E₁.mem_B_of_mem_closure E₂.right_mem hzx hzy (closure_mono hs ?_)
    exact (hz.subset_closure_diff hz.right_mem)
  obtain ⟨t, ht⟩ := hz.nonempty_sdiff
  have htL : t ∉ L₁ := fun h => hs ht (Or.inr h)
  rcases E₁.leg_swap E₂ E₃ hx hy hz hm hzB hzx hzy hxy hs with h | h
  · left
    refine ⟨?_, fun heq => htL (heq ▸ E₂.c_subset_L (Or.inr ht.1))⟩
    refine E₂.subset_of_open_subset E₁ fun w hw => ?_
    rcases hw.1 with h' | h'
    · exact E₂.c_subset_L (Or.inl h')
    · exact h ⟨h', fun h'' => hw.2 (Or.inr h'')⟩
  · right
    refine ⟨?_, fun heq => htL (heq ▸ E₃.c_subset_L (Or.inr ht.1))⟩
    refine E₃.subset_of_open_subset E₁ fun w hw => ?_
    rcases hw.1 with h' | h'
    · exact h ⟨h', fun h'' => hw.2 (Or.inl h'')⟩
    · exact E₃.c_subset_L (Or.inl h')

/-- Two ears with the same disc have the same line. -/
theorem c_eq (E : EarData Δ₀ c L A B a b) (E' : EarData Δ₀ c' L A' B' a' b') :
    c = c' := by
  have key : ∀ {c₁ c₂ A₁ B₁ A₂ B₂ : Set EuclideanPlane} {a₁ b₁ a₂ b₂ : EuclideanPlane},
      EarData Δ₀ c₁ L A₁ B₁ a₁ b₁ → EarData Δ₀ c₂ L A₂ B₂ a₂ b₂ → c₂ ⊆ c₁ := by
    intro c₁ c₂ A₁ B₁ A₂ B₂ a₁ b₁ a₂ b₂ E₁ E₂
    refine E₂.line.subset_closure_diff.trans (closure_minimal ?_ E₁.line.isCompact.isClosed)
    intro x hx
    have hb : x ∈ discBd L := E₂.bdL ▸ Or.inr hx.1
    rw [E₁.bdL] at hb
    refine hb.resolve_left fun h => ?_
    exact disjoint_left.mp E₂.disjoint_open hx (Surface.discBd_subset _ (E₁.A_subset h))
  exact Subset.antisymm (key E' E) (key E E')

end EarData

end GraphMinor.GM09
