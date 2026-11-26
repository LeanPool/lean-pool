/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM17.CellPartitionEnd
public import LeanPool.GraphMinor.GM17.Section11

/-!
# (11.1) of Graph Minors XVII for paintings

`cellPartitionPainting` proves `CellPartitionPaintingStatement`, which is (11.1) of Graph Minors
XVII with Claims (1)-(4), pages 189-191, for paintings without portrayals. The route is the paper's.
Claim (4), in `triangle_of_system`, gives three faces and three nodes in a triangle. At most one of
the faces is a cuff, as cuffs are disjoint.
This is the case split at the end of the paper's proof. If all three are regions, then three chords
make an `O`-arc (`tri_regions`). If one is a cuff and the third node is not on `bd(Σ)`, then two
chords make an `I`-arc (`tri_cuff`). If one is a cuff and the third node is on `bd(Σ)`,
then each chord cuts off one cell by (8.3). These two cells are a class, so the other class has all
nodes, against the hypothesis. This is the paper's Case 3.
-/

@[expose] public section

namespace GraphMinor.GM17

open Set Topology GraphMinor.Surface Painting

attribute [local instance 2000] Classical.decEq Classical.propDecidable

variable {S : Type} [TopologicalSpace S] [T2Space S] {Γ : Painting S}

/-- The facts on arcs of a painting. -/
abbrev PSys (Γ : Painting S) : Prop := ArcSystem cellOf faceOf gapEnds (cellNodes (Γ
  := Γ)) Γ.finite_N.toFinset

/-- The changes of a class of cells of a painting. -/
abbrev Ch (I : Finset (CellT Γ)) (O : Set S) (n : S) : Prop := Chg cellOf faceOf gapEnds I O n

open Classical in
/-- The conclusion of (11.1) for a class `I`, with the shared nodes `Z`. -/
def Concl (Γ : Painting S) (I : Finset (CellT Γ)) (Z : Set S) : Prop :=
  (∃ F, IsOArc F ∧ Γ.IsNormal F ∧ Γ.N ∩ F = Z ∧ ∀ Δ, IsClosedDisc Δ → discBd Δ = F → inside Γ Δ = I
    ∨ inside Γ Δ = Iᶜ) ∨
  (∃ F n₁ n₂, IsLineWithEnds F n₁ n₂ ∧ Γ.IsNormal F ∧ F ∩ bd S = {n₁, n₂} ∧ Γ.N ∩ F = Z
    ∧ ∀ Δ, IsClosedDisc Δ → F ⊆ discBd Δ → discBd Δ ⊆ F ∪ bd S → inside Γ Δ = I ∨ inside Γ Δ = Iᶜ)

variable [ConnectedSpace S]

theorem frontier_inj (hS : IsSurface S) (h : CellHyps Γ) {r r' : Set S} (hr : r ∈ Γ.regions)
  (hr' : r' ∈ Γ.regions) (e : closure r \ r = closure r' \ r') : r = r' := by
  have hcS : CompactSpace S := hS.1
  obtain ⟨L, hL⟩ := region_side hS h hr
  obtain ⟨c, u, v, hs, hcl⟩ := id hL
  have hsub : L ⊆ closure r \ r := fun x hx => ⟨hcl hx, fun hxr => region_off_paint hr hxr
    (hs.1.subset_U hx)⟩
  exact SideOf.unique hS h.hopen hr hr' hL (side_of_frontier hS h hr' hs.1 (e ▸ hsub))

theorem region_ne_cuff (hS : IsSurface S) (h : CellHyps Γ) {r Θ : Set S} (hr : r ∈ Γ.regions)
  (hΘ : Θ ∈ cuffs S) : closure r \ r ≠ Θ := fun e => by
  obtain ⟨L, c, u, v, hs, hcl⟩ := region_side hS h hr
  obtain ⟨z, hz⟩ := line_inner_nonempty hs.1.2.1
  have hzN : z ∉ Γ.N := hs.1.not_mem_N hz.1 (fun e => hz.2 (.inl e)) (fun e => hz.2 (.inr e))
  have hzf : z ∈ closure r \ r := ⟨hcl hz.1, fun hxr => region_off_paint hr hxr
    (hs.1.subset_U hz.1)⟩
  exact side_off_bd hs hz.1 hzN (cuff_subset hΘ (e ▸ hzf))

omit [ConnectedSpace S] in
omit [T2Space S] in
theorem chord_off {r r' F C₁ C₂ Δ₁ Δ₂ : Set S} {u v w : S} (hr : r ∈ Γ.regions)
  (hr' : r' ∈ Γ.regions) (C : ChordData Γ r u v F C₁ C₂ Δ₁ Δ₂) (hw : w ∈ F) (hw' : w ∈ r') : r' = r
    := by
  by_cases hs : w ∈ ({u, v} : Set S)
  · exact (region_off_paint hr' hw' (Γ.N_subset (C.nodes.ge hs).2)).elim
  · exact region_eq hr' hr hw' (C.inner ⟨hw, hs⟩)

omit [ConnectedSpace S] in
omit [T2Space S] in
theorem chord_meet {r r' F F' C₁ C₂ Δ₁ Δ₂ C₁' C₂' Δ₁' Δ₂' : Set S} {u v u' v' w : S}
  (hr : r ∈ Γ.regions) (hr' : r' ∈ Γ.regions) (hne : r ≠ r') (C : ChordData Γ r u v F C₁ C₂ Δ₁ Δ₂)
    (C' : ChordData Γ r' u' v' F' C₁' C₂' Δ₁' Δ₂')
    (hw : w ∈ F) (hw' : w ∈ F') : w ∈ Γ.N := by
  by_cases hs : w ∈ ({u, v} : Set S)
  · exact (C.nodes.ge hs).2
  · by_cases hs' : w ∈ ({u', v'} : Set S)
    · exact (C'.nodes.ge hs').2
    · exact (hne (region_eq hr hr' (C.inner ⟨hw, hs⟩) (C'.inner ⟨hw', hs'⟩))).elim

theorem iff_chord (hS : IsSurface S) (h : CellHyps Γ) (sys : PSys Γ) {I : Finset
  (CellT Γ)} {r F₀ C₁ C₂ Δ₁ Δ₂ F Δ : Set S} {u v : S} (hr : r ∈ Γ.regions)
    (C : ChordData Γ r u v F₀ C₁ C₂ Δ₁ Δ₂) (D : DiscData Γ F Δ) (hsub : F₀ ⊆ F)
      (hrF : ∀ x ∈ F, x ∈ r → x ∈ F₀) (huN : u ∈ Γ.N) (hvN : v ∈ Γ.N) (huv : u ≠ v) (hI : ∀ n, Ch I
        (closure r \ r) n ↔ n = u ∨ n = v) (n : S) :
    Ch I (closure r \ r) n ↔ Ch (inside Γ Δ) (closure r \ r) n :=
  (hI n).trans (chord_chg hS h sys hr C D hsub hrF huN hvN huv n).symm

/-- Three regions: three chords make an `O`-arc. -/
theorem tri_regions (hS : IsSurface S) (h : CellHyps Γ) (sys : PSys Γ) (I : Finset
  (CellT Γ)) {r₁ r₂ r₃ : Set S} {x y z : S} (hr₁ : r₁ ∈ Γ.regions) (hr₂ : r₂ ∈ Γ.regions)
    (hr₃ : r₃ ∈ Γ.regions)
    (h12 : r₁ ≠ r₂) (h23 : r₂ ≠ r₃) (h13 : r₁ ≠ r₃) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
      (hxN : x ∈ Γ.N) (hyN : y ∈ Γ.N) (hzN : z ∈ Γ.N)
    (hx₁ : x ∈ closure r₁ \ r₁) (hy₁ : y ∈ closure r₁ \ r₁) (hy₂ : y ∈ closure r₂ \ r₂)
      (hz₂ : z ∈ closure r₂ \ r₂) (hx₃ : x ∈ closure r₃ \ r₃) (hz₃ : z ∈ closure r₃ \ r₃)
    (H₁ : ∀ n, Ch I (closure r₁ \ r₁) n ↔ n = x ∨ n = y) (H₂ : ∀ n, Ch I (closure r₂ \ r₂) n ↔ n
      = y ∨ n = z) (H₃ : ∀ n, Ch I (closure r₃ \ r₃) n ↔ n = x ∨ n = z)
    (Hoth : ∀ e, e ≠ closure r₁ \ r₁ → e ≠ closure r₂ \ r₂ → e ≠ closure r₃ \ r₃
      → ∀ n, ¬ Ch I e n) : Concl Γ I {x, y, z} := by
  have hman := hS.2.2
  obtain ⟨F₁, A₁, B₁, D₁, E₁, c₁⟩ := exists_chordData hS h hr₁ hx₁ hy₁ hxN hyN hxy
  obtain ⟨F₂, A₂, B₂, D₂, E₂, c₂⟩ := exists_chordData hS h hr₂ hy₂ hz₂ hyN hzN hyz
  obtain ⟨F₃, A₃, B₃, D₃, E₃, c₃⟩ := exists_chordData hS h hr₃ hx₃ hz₃ hxN hzN hxz
  have hi : F₁ ∩ F₂ = {y} := by
    ext w
    constructor
    · rintro ⟨a, b⟩
      have hN := chord_meet hr₁ hr₂ h12 c₁ c₂ a b
      have h3 : w ∈ ({x, y} : Set S) := c₁.nodes ▸ ⟨a, hN⟩
      have h4 : w ∈ ({y, z} : Set S) := c₂.nodes ▸ ⟨b, hN⟩
      rcases h3 with rfl | rfl
      · rcases h4 with e | e
        · exact (hxy e).elim
        · exact (hxz e).elim
      · rfl
    · rintro rfl
      exact ⟨c₁.chord.right_mem, c₂.chord.left_mem⟩
  have hi3 : (F₁ ∪ F₂) ∩ F₃ = {x, z} := by
    ext w
    constructor
    · rintro ⟨a | a, b⟩
      · have hN := chord_meet hr₁ hr₃ h13 c₁ c₃ a b
        have h3 : w ∈ ({x, y} : Set S) := c₁.nodes ▸ ⟨a, hN⟩
        have h4 : w ∈ ({x, z} : Set S) := c₃.nodes ▸ ⟨b, hN⟩
        rcases h3 with rfl | rfl
        · exact .inl rfl
        · exact h4
      · have hN := chord_meet hr₂ hr₃ h23 c₂ c₃ a b
        have h3 : w ∈ ({y, z} : Set S) := c₂.nodes ▸ ⟨a, hN⟩
        have h4 : w ∈ ({x, z} : Set S) := c₃.nodes ▸ ⟨b, hN⟩
        rcases h3 with rfl | rfl
        · exact h4
        · exact .inr rfl
    · rintro (rfl | rfl)
      · exact ⟨.inl c₁.chord.left_mem, c₃.chord.left_mem⟩
      · exact ⟨.inr c₂.chord.right_mem, c₃.chord.right_mem⟩
  have hsN : ∀ {a b : S}, a ∈ Γ.N → b ∈ Γ.N → ({a, b} : Set S) ⊆ Γ.N := fun {a b} ha hb w hw
    => hw.elim (fun e => e ▸ ha) fun e => e ▸ hb
  have hFU : ((F₁ ∪ F₂) ∪ F₃) ∩ Γ.U ⊆ Γ.N := by
    rintro w ⟨(a | a) | a, hU⟩
    · exact hsN hxN hyN (c₁.paint ⟨a, hU⟩)
    · exact hsN hyN hzN (c₂.paint ⟨a, hU⟩)
    · exact hsN hxN hzN (c₃.paint ⟨a, hU⟩)
  have hFN : Γ.N ∩ ((F₁ ∪ F₂) ∪ F₃) = {x, y, z} := by
    ext w
    constructor
    · rintro ⟨hN, (a | a) | a⟩
      · exact (c₁.nodes.subset ⟨a, hN⟩).elim .inl fun e => .inr (.inl e)
      · exact (c₂.nodes.subset ⟨a, hN⟩).elim (fun e => .inr (.inl e)) fun e => .inr (.inr e)
      · exact (c₃.nodes.subset ⟨a, hN⟩).elim .inl fun e => .inr (.inr e)
    · rintro (rfl | rfl | rfl)
      · exact ⟨hxN, .inl (.inl c₁.chord.left_mem)⟩
      · exact ⟨hyN, .inl (.inl c₁.chord.right_mem)⟩
      · exact ⟨hzN, .inl (.inr c₂.chord.right_mem)⟩
  have hFc : IsClosed ((F₁ ∪ F₂) ∪ F₃) := ((GM19.isClosed_of_cuffLine c₁.chord).union
    (GM19.isClosed_of_cuffLine c₂.chord)).union (GM19.isClosed_of_cuffLine c₃.chord)
  refine .inl ⟨_, oArc_of_lines (c₁.chord.union c₂.chord hi) c₃.chord hi3, hFU, hFN,
    fun Δ hΔ hb => ?_⟩
  have D : DiscData Γ ((F₁ ∪ F₂) ∪ F₃) Δ := ⟨hΔ, hFc, hFU, fun x hx => Filter.mem_of_superset
    ((hΔ.isOpen_discInt hman).mem_nhds ⟨hx.1, hb ▸ hx.2⟩) sdiff_subset, hb.ge, hb.le.trans
      subset_union_left⟩
  refine match_of_chg hS h I _ fun r hr n => ?_
  by_cases e₁ : r = r₁
  · subst e₁
    refine iff_chord hS h sys hr c₁ D (subset_union_left.trans subset_union_left) ?_ hxN hyN hxy H₁
      n
    rintro w ((a | a) | a) hw
    · exact a
    · exact (h12 (chord_off hr₂ hr c₂ a hw)).elim
    · exact (h13 (chord_off hr₃ hr c₃ a hw)).elim
  by_cases e₂ : r = r₂
  · subst e₂
    refine iff_chord hS h sys hr c₂ D (subset_union_right.trans subset_union_left) ?_ hyN hzN hyz
      H₂ n
    rintro w ((a | a) | a) hw
    · exact (h12 (chord_off hr₁ hr c₁ a hw).symm).elim
    · exact a
    · exact (h23 (chord_off hr₃ hr c₃ a hw)).elim
  by_cases e₃ : r = r₃
  · subst e₃
    refine iff_chord hS h sys hr c₃ D subset_union_right ?_ hxN hzN hxz H₃ n
    rintro w ((a | a) | a) hw
    · exact (h13 (chord_off hr₁ hr c₁ a hw).symm).elim
    · exact (h23 (chord_off hr₂ hr c₂ a hw).symm).elim
    · exact a
  have hd : Disjoint r ((F₁ ∪ F₂) ∪ F₃) := disjoint_left.mpr fun w hw ha => by
    rcases ha with (a | a) | a
    · exact e₁ (chord_off hr₁ hr c₁ a hw)
    · exact e₂ (chord_off hr₂ hr c₂ a hw)
    · exact e₃ (chord_off hr₃ hr c₃ a hw)
  exact iff_of_false (Hoth _ (fun e => e₁ (frontier_inj hS h hr hr₁ e)) (fun e => e₂
    (frontier_inj hS h hr hr₂ e)) (fun e => e₃ (frontier_inj hS h hr hr₃ e)) n)
      (off_chord_no_chg hS h sys hr D hd n)

theorem exists_gap_at (hS : IsSurface S) (h : CellHyps Γ) {O : Set S} {n m : S} (hO : Γ.IsFace O)
  (hn : n ∈ O) (hm : m ∈ O) (hnN : n ∈ Γ.N) (hmN : m ∈ Γ.N) (hnm : n ≠ m) : ∃ a : GapT Γ, faceOf a
    = O ∧ n ∈ gapEnds a := by
  have hfin : (Γ.N ∩ O).Finite := Γ.finite_N.subset inter_subset_left
  obtain ⟨-, hcov⟩ := arcOf_family (face_oarc hS h hO) hfin inter_subset_right ⟨hnN, hn⟩ ⟨hmN, hm⟩
    hnm
  have hnO : n ∈ ⋃₀ {L | IsArcOf O (Γ.N ∩ O) L} := by
    rw [hcov]
    exact hn
  obtain ⟨L, hL, hnL⟩ := hnO
  exact ⟨⟨L, arc_face_gap hS h hO hL⟩, faceOf_eq hS h hO hL.subset, mem_gapEnds.mpr ⟨hnN, hnL⟩⟩

/-- Two nodes on the frontier of a region and on `bd(Σ)` are on the same cuff, by (8.3). -/
theorem same_cuff (hS : IsSurface S) (h : CellHyps Γ) (h83 : Hyp83 Γ) {r : Set S} {x y : S}
  (hr : r ∈ Γ.regions) (hx : x ∈ closure r \ r) (hy : y ∈ closure r \ r) (hxN : x ∈ Γ.N)
    (hyN : y ∈ Γ.N) (hxy : x ≠ y) (hxb : x ∈ bd S) (hyb : y ∈ bd S) :
    ∃ Θ ∈ cuffs S, x ∈ Θ ∧ y ∈ Θ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hun, hin⟩ := (h.hreg r hr).2.lines hx hy hxy
  obtain ⟨F, -, -, Δ, hF, hFr, -, -, -, -, -, -, -, hΔ, h1, h2, -, -, -, -⟩ :=
    exists_chord_disc hS (fun r hr => (h.hreg r hr).1) (fun r hr => (h.hreg r hr).2) h83 hr hC₁ hC₂
      hun hin hxN hyN hxy hxb hyb
  have hFb : F ∩ bd S = {x, y} := by
    refine Subset.antisymm (fun w hw => by_contra fun h3 => region_off_bd hr (hFr ⟨hw.1,
      h3⟩) hw.2) ?_
    rintro w (rfl | rfl)
    · exact ⟨hF.left_mem, hxb⟩
    · exact ⟨hF.right_mem, hyb⟩
  obtain ⟨I, I', Θ, hΘ, hI, -, hU, -, -⟩ := arc_disc_data hS hF hFb hΔ h1 h2
  exact ⟨Θ, hΘ, hU ▸ .inl hI.left_mem, hU ▸ .inl hI.right_mem⟩

open Classical in
/-- The paper's Case 3: two regions and a cuff, and the third node on `bd(Σ)`. The two cells cut off
by (8.3) have the changes of `I` at each region, so they are `I` or its complement, and the other
class has all nodes. -/
theorem tri_cuff_bd (hS : IsSurface S) (h : CellHyps Γ) (h83 : Hyp83 Γ) (sys : PSys Γ) (I : Finset
  (CellT Γ)) (hI : nodesOf cellNodes I ≠ Γ.finite_N.toFinset) (hJ : nodesOf cellNodes Iᶜ ≠
    Γ.finite_N.toFinset)
    {r₁ r₂ Θ : Set S} {x y z : S} (hr₁ : r₁ ∈ Γ.regions) (hr₂ : r₂ ∈ Γ.regions) (hΘ : Θ ∈ cuffs S)
      (h12 : r₁ ≠ r₂) (hxy : x ≠ y) (hyz : y ≠ z) (hxN : x ∈ Γ.N) (hyN : y ∈ Γ.N) (hzN : z ∈ Γ.N)
    (hx₁ : x ∈ closure r₁ \ r₁) (hy₁ : y ∈ closure r₁ \ r₁) (hy₂ : y ∈ closure r₂ \ r₂)
      (hz₂ : z ∈ closure r₂ \ r₂) (hx₃ : x ∈ Θ) (hz₃ : z ∈ Θ) (hyb : y ∈ bd S)
    (H₁ : ∀ n, Ch I (closure r₁ \ r₁) n ↔ n = x ∨ n = y) (H₂ : ∀ n, Ch I (closure r₂ \ r₂) n ↔ n
      = y ∨ n = z)
    (Hoth : ∀ e, e ≠ closure r₁ \ r₁ → e ≠ closure r₂ \ r₂ → e ≠ Θ → ∀ n, ¬ Ch I e n) : False := by
  have hxb := cuff_subset hΘ hx₃
  have hneΘ : ∀ {r}, r ∈ Γ.regions → closure r \ r ≠ Θ := fun hr => region_ne_cuff hS h hr hΘ
  have hfne : closure r₁ \ r₁ ≠ closure r₂ \ r₂ := fun e => h12 (frontier_inj hS h hr₁ hr₂ e)
  obtain ⟨Θ', hΘ', hxΘ, hyΘ⟩ := same_cuff hS h h83 hr₁ hx₁ hy₁ hxN hyN hxy hxb hyb
  obtain rfl : Θ' = Θ := cuff_eq hΘ' hΘ hxΘ hx₃
  have hF₁ : Γ.IsFace (closure r₁ \ r₁) := .inl ⟨r₁, hr₁, rfl⟩
  have hF₂ : Γ.IsFace (closure r₂ \ r₂) := .inl ⟨r₂, hr₂, rfl⟩
  have hF₃ : Γ.IsFace Θ' := .inr hΘ
  have on : ∀ {O n m}, Γ.IsFace O → n ∈ O → m ∈ O → n ∈ Γ.N → m ∈ Γ.N → n ≠ m → ∃ a, faceOf a = O
    ∧ n ∈ gapEnds a := fun hO hn hm hnN hmN hnm => exists_gap_at hS h hO hn hm hnN hmN hnm
  obtain ⟨c₁, a₁, b₁, ht₁, ha₁, hb₁, hfa₁, hfb₁, hae₁, hbe₁⟩ := sys.par _ _ x y (hneΘ hr₁) hxy
    (on hF₁ hx₁ hy₁ hxN hyN hxy) (on hF₁ hy₁ hx₁ hyN hxN hxy.symm) (on hF₃ hx₃ hyΘ hxN hyN hxy)
      (on hF₃ hyΘ hx₃ hyN hxN hxy.symm)
  obtain ⟨c₂, a₂, b₂, ht₂, ha₂, hb₂, hfa₂, hfb₂, hae₂, hbe₂⟩ := sys.par _ _ y z (hneΘ hr₂) hyz
    (on hF₂ hy₂ hz₂ hyN hzN hyz) (on hF₂ hz₂ hy₂ hzN hyN hyz.symm) (on hF₃ hyΘ hz₃ hyN hzN hyz)
      (on hF₃ hz₃ hyΘ hzN hyN hyz.symm)
  have S₁ := chg_single sys ht₁ ha₁ hb₁ hfa₁ hfb₁ hae₁ hbe₁ (hneΘ hr₁)
  have S₂ := chg_single sys ht₂ ha₂ hb₂ hfa₂ hfb₂ hae₂ hbe₂ (hneΘ hr₂)
  let I₀ : Finset (CellT Γ) := symmDiff {c₁} {c₂}
  have hsd : ∀ e n, Ch I₀ e n ↔ ¬ (Ch {c₁} e n ↔ Ch {c₂} e n) := fun e n
    => chg_symmDiff cellOf faceOf gapEnds {c₁} {c₂} e n
  have hm := match_of_chg hS h I I₀ fun r hr n => by
    change Ch I _ n ↔ Ch I₀ _ n
    rw [hsd]
    change _ ↔ ¬ (Chg cellOf faceOf gapEnds {c₁} _ n ↔ Chg cellOf faceOf gapEnds {c₂} _ n)
    rw [S₁, S₂]
    by_cases e₁ : r = r₁
    · subst e₁
      simp [H₁ n, hneΘ hr, hfne]
      tauto
    by_cases e₂ : r = r₂
    · subst e₂
      simp [H₂ n, hneΘ hr, hfne.symm]
      tauto
    have n₁ : closure r \ r ≠ closure r₁ \ r₁ := fun e => e₁ (frontier_inj hS h hr hr₁ e)
    have n₂ : closure r \ r ≠ closure r₂ \ r₂ := fun e => e₂ (frontier_inj hS h hr hr₂ e)
    simp [Hoth _ n₁ n₂ (hneΘ hr) n, n₁, n₂, hneΘ hr]
  have hshared : ∀ m, m = x ∨ m = y ∨ m = z → m ∈ nodesOf cellNodes I ∩ nodesOf cellNodes Iᶜ := by
    rintro m (rfl | rfl | rfl)
    · exact chg_shared sys ((H₁ _).mpr (.inl rfl))
    · exact chg_shared sys ((H₁ _).mpr (.inr rfl))
    · exact chg_shared sys ((H₂ _).mpr (.inr rfl))
  have hsmall : ∀ c ∈ I₀, ∀ m ∈ cellNodes c, m ∈ nodesOf cellNodes I ∩ nodesOf cellNodes Iᶜ
    := fun c hc m hmc => by
    have hcc : c = c₁ ∨ c = c₂ := by
      rcases Finset.mem_symmDiff.mp hc with h3 | h3
      · exact .inl (Finset.mem_singleton.mp h3.1)
      · exact .inr (Finset.mem_singleton.mp h3.1)
    refine hshared m ?_
    rcases hcc with rfl | rfl
    · rw [ht₁] at hmc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmc
      tauto
    · rw [ht₂] at hmc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmc
      tauto
  rcases hm with e | e
  · refine hJ (Finset.Subset.antisymm (nodesOf_sub sys _) fun n hn => ?_)
    obtain ⟨c, hc⟩ := sys.cover n hn
    by_cases hcI : c ∈ I
    · exact (Finset.mem_inter.mp (hsmall c (e ▸ hcI) n hc)).2
    · exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_compl.mpr hcI, hc⟩
  · refine hI (Finset.Subset.antisymm (nodesOf_sub sys _) fun n hn => ?_)
    obtain ⟨c, hc⟩ := sys.cover n hn
    by_cases hcI : c ∈ I
    · exact Finset.mem_biUnion.mpr ⟨c, hcI, hc⟩
    · exact (Finset.mem_inter.mp (hsmall c (e ▸ Finset.mem_compl.mpr hcI) n hc)).1

open Classical in
/-- Two regions and a cuff. If the third node is off `bd(Σ)`, then two chords make an `I`-arc. The
other case is `tri_cuff_bd`. -/
theorem tri_cuff (hS : IsSurface S) (h : CellHyps Γ) (h83 : Hyp83 Γ) (sys : PSys Γ) (I : Finset
  (CellT Γ)) (hI : nodesOf cellNodes I ≠ Γ.finite_N.toFinset) (hJ : nodesOf cellNodes Iᶜ ≠
    Γ.finite_N.toFinset)
    {r₁ r₂ Θ : Set S} {x y z : S} (hr₁ : r₁ ∈ Γ.regions) (hr₂ : r₂ ∈ Γ.regions) (hΘ : Θ ∈ cuffs S)
      (h12 : r₁ ≠ r₂) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (hxN : x ∈ Γ.N) (hyN : y ∈ Γ.N)
        (hzN : z ∈ Γ.N)
    (hx₁ : x ∈ closure r₁ \ r₁) (hy₁ : y ∈ closure r₁ \ r₁) (hy₂ : y ∈ closure r₂ \ r₂)
      (hz₂ : z ∈ closure r₂ \ r₂) (hx₃ : x ∈ Θ) (hz₃ : z ∈ Θ)
    (H₁ : ∀ n, Ch I (closure r₁ \ r₁) n ↔ n = x ∨ n = y) (H₂ : ∀ n, Ch I (closure r₂ \ r₂) n ↔ n
      = y ∨ n = z)
    (Hoth : ∀ e, e ≠ closure r₁ \ r₁ → e ≠ closure r₂ \ r₂ → e ≠ Θ → ∀ n, ¬ Ch I e n) : Concl Γ I
      {x, y, z} := by
  have hxb := cuff_subset hΘ hx₃
  have hzb := cuff_subset hΘ hz₃
  have hneΘ : ∀ {r}, r ∈ Γ.regions → closure r \ r ≠ Θ := fun hr => region_ne_cuff hS h hr hΘ
  by_cases hyb : y ∈ bd S
  · exact (tri_cuff_bd hS h h83 sys I hI hJ hr₁ hr₂ hΘ h12 hxy hyz hxN hyN hzN hx₁ hy₁ hy₂ hz₂ hx₃
    hz₃ hyb H₁ H₂ Hoth).elim
  · obtain ⟨F₁, A₁, B₁, D₁, E₁, c₁⟩ := exists_chordData hS h hr₁ hx₁ hy₁ hxN hyN hxy
    obtain ⟨F₂, A₂, B₂, D₂, E₂, c₂⟩ := exists_chordData hS h hr₂ hy₂ hz₂ hyN hzN hyz
    have hi : F₁ ∩ F₂ = {y} := by
      ext w
      constructor
      · rintro ⟨a, b⟩
        have hN := chord_meet hr₁ hr₂ h12 c₁ c₂ a b
        have h3 : w ∈ ({x, y} : Set S) := c₁.nodes ▸ ⟨a, hN⟩
        have h4 : w ∈ ({y, z} : Set S) := c₂.nodes ▸ ⟨b, hN⟩
        rcases h3 with rfl | rfl
        · rcases h4 with e | e
          · exact (hxy e).elim
          · exact (hxz e).elim
        · rfl
      · rintro rfl
        exact ⟨c₁.chord.right_mem, c₂.chord.left_mem⟩
    have hline := c₁.chord.union c₂.chord hi
    have hsN : ∀ {a b : S}, a ∈ Γ.N → b ∈ Γ.N → ({a, b} : Set S) ⊆ Γ.N := fun {a b} ha hb w hw
      => hw.elim (fun e => e ▸ ha) fun e => e ▸ hb
    have hFU : (F₁ ∪ F₂) ∩ Γ.U ⊆ Γ.N := by
      rintro w ⟨a | a, hU⟩
      · exact hsN hxN hyN (c₁.paint ⟨a, hU⟩)
      · exact hsN hyN hzN (c₂.paint ⟨a, hU⟩)
    have hFb : (F₁ ∪ F₂) ∩ bd S = {x, z} := by
      ext w
      constructor
      · rintro ⟨a | a, hb⟩
        · rcases c₁.edge ⟨a, hb⟩ with rfl | rfl
          · exact .inl rfl
          · exact (hyb hb).elim
        · rcases c₂.edge ⟨a, hb⟩ with rfl | rfl
          · exact (hyb hb).elim
          · exact .inr rfl
      · rintro (rfl | rfl)
        · exact ⟨.inl c₁.chord.left_mem, hxb⟩
        · exact ⟨.inr c₂.chord.right_mem, hzb⟩
    have hFN : Γ.N ∩ (F₁ ∪ F₂) = {x, y, z} := by
      ext w
      constructor
      · rintro ⟨hN, a | a⟩
        · exact (c₁.nodes.subset ⟨a, hN⟩).elim .inl fun e => .inr (.inl e)
        · exact (c₂.nodes.subset ⟨a, hN⟩).elim (fun e => .inr (.inl e)) fun e => .inr (.inr e)
      · rintro (rfl | rfl | rfl)
        · exact ⟨hxN, .inl c₁.chord.left_mem⟩
        · exact ⟨hyN, .inl c₁.chord.right_mem⟩
        · exact ⟨hzN, .inr c₂.chord.right_mem⟩
    refine .inr ⟨_, x, z, hline, hFU, hFb, hFN, fun Δ hΔ h1 h2 => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnb⟩ := arc_disc_data hS hline hFb hΔ h1 h2
    have D : DiscData Γ (F₁ ∪ F₂) Δ := ⟨hΔ, (GM19.isClosed_of_cuffLine c₁.chord).union
      (GM19.isClosed_of_cuffLine c₂.chord), hFU, hnb, h1, h2⟩
    refine match_of_chg hS h I _ fun r hr n => ?_
    by_cases e₁ : r = r₁
    · subst e₁
      refine iff_chord hS h sys hr c₁ D subset_union_left ?_ hxN hyN hxy H₁ n
      rintro w (a | a) hw
      · exact a
      · exact (h12 (chord_off hr₂ hr c₂ a hw)).elim
    by_cases e₂ : r = r₂
    · subst e₂
      refine iff_chord hS h sys hr c₂ D subset_union_right ?_ hyN hzN hyz H₂ n
      rintro w (a | a) hw
      · exact (h12 (chord_off hr₁ hr c₁ a hw).symm).elim
      · exact a
    have hd : Disjoint r (F₁ ∪ F₂) := disjoint_left.mpr fun w hw ha => by
      rcases ha with a | a
      · exact e₁ (chord_off hr₁ hr c₁ a hw)
      · exact e₂ (chord_off hr₂ hr c₂ a hw)
    exact iff_of_false (Hoth _ (fun e => e₁ (frontier_inj hS h hr hr₁ e)) (fun e => e₂
      (frontier_inj hS h hr hr₂ e)) (hneΘ hr) n) (off_chord_no_chg hS h sys hr D hd n)

omit [ConnectedSpace S] in
omit [T2Space S] in
theorem nodes_coe (A : Finset (CellT Γ)) (T : Set (Set S)) (hT : T ⊆ Γ.C)
  (hA : ∀ c : CellT Γ, c ∈ A ↔ c.1 ∈ T) : (nodesOf cellNodes A : Set S) = Γ.tildeOfCells T := by
  ext n
  simp only [Finset.mem_coe, nodesOf, Finset.mem_biUnion, Painting.tildeOfCells, mem_iUnion,
    exists_prop]
  constructor
  · rintro ⟨c, hc, hn⟩
    exact ⟨c.1, (hA c).mp hc, mem_cellNodes.mp hn⟩
  · rintro ⟨c, hc, hn⟩
    exact ⟨⟨c, hT hc⟩, (hA _).mpr hc, mem_cellNodes.mpr hn⟩

open Classical in
/-- **(11.1) of Graph Minors XVII for paintings.** -/
theorem cellPartitionPainting : CellPartitionPaintingStatement := by
  intro S _ _ hS Γ hreg h2 hn h83 h85 I J hu hd hI hJ hcard
  have ht2 : T2Space S := hS.2.1
  have h : CellHyps Γ := ⟨hreg, h2, hn⟩
  have sys : PSys Γ := arcSystem hS h h83 h85
  have hIC : I ⊆ Γ.C := fun c hc => hu ▸ .inl hc
  have hJC : J ⊆ Γ.C := fun c hc => hu ▸ .inr hc
  let A : Finset (CellT Γ) := Finset.univ.filter fun c => c.1 ∈ I
  have hA : ∀ c : CellT Γ, c ∈ A ↔ c.1 ∈ I := fun c => by simp [A]
  have hAc : ∀ c : CellT Γ, c ∈ Aᶜ ↔ c.1 ∈ J := fun c => by
    rw [Finset.mem_compl, hA]
    have hcu : c.1 ∈ I ∪ J := by
      rw [hu]
      exact c.2
    constructor
    · exact fun h3 => hcu.resolve_left h3
    · exact fun h3 h4 => disjoint_left.mp hd h4 h3
  have hc₁ := nodes_coe A I hIC hA
  have hc₂ := nodes_coe Aᶜ J hJC hAc
  have hNd : ((Γ.finite_N.toFinset : Finset S) : Set S) = Γ.N := by simp
  have hI' : nodesOf cellNodes A ≠ Γ.finite_N.toFinset := fun e => hI (by rw [← hc₁, e, hNd])
  have hJ' : nodesOf cellNodes Aᶜ ≠ Γ.finite_N.toFinset := fun e => hJ (by rw [← hc₂, e, hNd])
  have hZc : ((nodesOf cellNodes A ∩ nodesOf cellNodes Aᶜ : Finset S) : Set S)
    = Γ.tildeOfCells I ∩ Γ.tildeOfCells J := by
    rw [Finset.coe_inter, hc₁, hc₂]
  have hZle : (nodesOf cellNodes A ∩ nodesOf cellNodes Aᶜ).card ≤ 3 := by
    rw [← Set.ncard_coe_finset, hZc]
    exact hcard
  obtain ⟨x, y, z, f, g, k, hxy, hyz, hxz, hZ, hP, hfg, hgk, hfk, hDf, hDg, hDk⟩
    := triangle_of_system sys _ A rfl hI' hJ' hZle
  have hZs : Γ.tildeOfCells I ∩ Γ.tildeOfCells J = {x, y, z} := by
    rw [← hZc, hZ]
    simp
  have Hf : ∀ n, Ch A f n ↔ n = x ∨ n = y := fun n => by
    rw [Ch, ← mem_chgNodes sys, hDf]
    simp
  have Hg : ∀ n, Ch A g n ↔ n = y ∨ n = z := fun n => by
    rw [Ch, ← mem_chgNodes sys, hDg]
    simp
  have Hk : ∀ n, Ch A k n ↔ n = x ∨ n = z := fun n => by
    rw [Ch, ← mem_chgNodes sys, hDk]
    simp
  have Hoth : ∀ e, e ≠ f → e ≠ g → e ≠ k → ∀ n, ¬ Ch A e n := fun e h1 h2 h3 n hc => by
    have hm : e ∈ chgFaces cellOf faceOf gapEnds Γ.finite_N.toFinset A :=
      (mem_chgFaces sys).mpr ⟨n, (mem_chgNodes sys).mpr hc⟩
    rw [hP] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    tauto
  have hface : ∀ {e n}, Ch A e n → Γ.IsFace e ∧ n ∈ e ∧ n ∈ Γ.N := fun {e n} hc => by
    obtain ⟨a, -, ha, -, han, -⟩ := chg_arcs sys hc
    obtain ⟨h3, h4⟩ := faceOf_spec hS h a
    rw [ha] at h3 h4
    exact ⟨h3, h4 (mem_gapEnds.mp han).2, (mem_gapEnds.mp han).1⟩
  obtain ⟨hOf, hxf, hxN⟩ := hface ((Hf x).mpr (.inl rfl))
  obtain ⟨-, hyf, hyN⟩ := hface ((Hf y).mpr (.inr rfl))
  obtain ⟨hOg, hyg, -⟩ := hface ((Hg y).mpr (.inl rfl))
  obtain ⟨-, hzg, hzN⟩ := hface ((Hg z).mpr (.inr rfl))
  obtain ⟨hOk, hxk, -⟩ := hface ((Hk x).mpr (.inl rfl))
  obtain ⟨-, hzk, -⟩ := hface ((Hk z).mpr (.inr rfl))
  have hcon : Concl Γ A {x, y, z} := by
    rcases hOf with ⟨r₁, hr₁, rfl⟩ | hf <;> rcases hOg with ⟨r₂, hr₂, rfl⟩ | hg
      <;> rcases hOk with ⟨r₃, hr₃, rfl⟩ | hk
    · exact tri_regions hS h sys A hr₁ hr₂ hr₃ (fun e => hfg (by rw [e])) (fun e => hgk
      (by rw [e])) (fun e => hfk (by rw [e])) hxy hyz hxz hxN hyN hzN hxf hyf hyg hzg hxk hzk Hf Hg
        Hk Hoth
    · exact tri_cuff hS h h83 sys A hI' hJ' hr₁ hr₂ hk (fun e => hfg (by rw [e])) hxy hyz hxz hxN
        hyN hzN hxf hyf hyg hzg hxk hzk Hf Hg Hoth
    · have hc := tri_cuff hS h h83 sys A hI' hJ' hr₃ hr₁ hg (fun e => hfk
      (by rw [e])) hxz.symm hxy hyz.symm hzN hxN hyN hzk hxk hxf hyf hzg hyg
        (fun n => (Hk n).trans or_comm) Hf (fun e h1 h2 h3 => Hoth e h2 h3 h1)
      have hset : ({z, x, y} : Set S) = {x, y, z} := by
        ext w
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto
      rwa [hset] at hc
    · exact (hgk (cuff_eq hg hk hzg hzk)).elim
    · have hc := tri_cuff hS h h83 sys A hI' hJ' hr₂ hr₃ hf (fun e => hgk
      (by rw [e])) hyz hxz.symm hxy.symm hyN hzN hxN hyg hzg hzk hxk hyf hxf
        Hg (fun n => (Hk n).trans or_comm) (fun e h1 h2 h3 => Hoth e h3 h1 h2)
      have hset : ({y, z, x} : Set S) = {x, y, z} := by
        ext w
        simp only [mem_insert_iff, mem_singleton_iff]
        tauto
      rwa [hset] at hc
    · exact (hfk (cuff_eq hf hk hxf hxk)).elim
    · exact (hfg (cuff_eq hf hg hyf hyg)).elim
    · exact (hfg (cuff_eq hf hg hyf hyg)).elim
  have hconv : ∀ {Δ : Set S}, inside Γ Δ = A ∨ inside Γ Δ = Aᶜ → {c ∈ Γ.C | c ⊆ Δ} = I
    ∨ {c ∈ Γ.C | c ⊆ Δ} = J := fun {Δ} he => by
    have key : ∀ {B : Finset (CellT Γ)} {T : Set (Set S)}, T ⊆ Γ.C → (∀ c : CellT Γ, c ∈ B ↔ c.1 ∈
      T) → inside Γ Δ = B → {c ∈ Γ.C | c ⊆ Δ} = T := fun {B T} hT hB e => by
      ext c
      constructor
      · rintro ⟨hc, hs⟩
        exact (hB ⟨c, hc⟩).mp (e ▸ mem_inside.mpr hs)
      · intro hc
        exact ⟨hT hc, mem_inside.mp (e ▸ (hB ⟨c, hT hc⟩).mpr hc)⟩
    rcases he with e | e
    · exact .inl (key hIC hA e)
    · exact .inr (key hJC hAc e)
  have h3 : (Γ.tildeOfCells I ∩ Γ.tildeOfCells J).ncard = 3 := by
    rw [hZs, ncard_eq_toFinset_card']
    simp [Finset.card_insert_of_notMem, hxy, hxz, hyz]
  refine ⟨h3, ?_⟩
  rw [hZs]
  rcases hcon with ⟨F, h1, h2', h3', h4⟩ | ⟨F, n₁, n₂, h1, h2', h3', h4, h5⟩
  · exact .inl ⟨F, h1, h2', h3', fun Δ hΔ hb => hconv (h4 Δ hΔ hb)⟩
  · exact .inr ⟨F, n₁, n₂, h1, h2', h3', h4, fun Δ hΔ h6 h7 => hconv (h5 Δ hΔ h6 h7)⟩

end GraphMinor.GM17
