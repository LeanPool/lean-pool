/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.NetRefine
import LeanPool.GraphMinor.GM07.NetSeparate
import LeanPool.GraphMinor.GM07.NetSeparateExchange
import LeanPool.GraphMinor.GM07.NetSwap
import LeanPool.GraphMinor.GM07.NetSwapBoundary
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.Section2MinVal
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Fan
import LeanPool.GraphMinor.Surface.InvarianceOfDomain

/-!
# The edges of `J'` in VII (2.6)

The text works with `J'`, whose vertices include `φ(s)` and `φ(t)`, and speaks of a pair `{f, g}`
for each
edge of type (ii). So first subdivide the pairs at `s` and `t` (`Net.exists_refine_ends`). Then each
edge of
`J'` lies in `bd(Σ)`, or it is the open image of one pair (`Net.edge_cases`). The two sides of such
a pair
are each in one piece of the cut along `F` (`Net.exists_cut_pieces`), so an edge that is not of type
(iii)
or (iv) has one side in each piece, and the exchange applies (`Net.edge_contacts_le`).
-/

public section
namespace GraphMinor.GM07
open Set Topology Surface
universe u

variable {S : Type u} [TopologicalSpace S]

/-- The point `x` is on no open paired side. -/
abbrev Net.MissesOpenSides (N : Net S) (x : N.D) : Prop :=
  ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.f j r ≠ x ∧ N.g j r ≠ x

/-- The two boundary arcs of `bd(Δ) - {s, t}`, and the pieces of the cut along `F`. -/
theorem Net.exists_cut_pieces (N : Net S) {F : Set N.D} {s t : N.D}
    (hF : IsLineWithEnds F s t) (hst : s ≠ t) (hFbd : F ∩ bd N.D = {s, t}) :
    ∃ A B C₁ C₂ : Set N.D, IsClosedDisc A ∧ IsClosedDisc B ∧ A ∪ B = univ ∧ A ∩ B = F ∧
      discBd A = (A ∩ bd N.D) ∪ F ∧ discBd B = (B ∩ bd N.D) ∪ F ∧
      componentsIn (bd N.D \ {s, t}) = {C₁, C₂} ∧ C₁ ≠ C₂ ∧
      (A ∩ bd N.D) \ {s, t} ⊆ C₁ ∧ (B ∩ bd N.D) \ {s, t} ⊆ C₂ := by
  have : T2Space N.D := N.isSurface_D.2.1
  have hsbd : s ∈ bd N.D := (hFbd.symm.subset (Or.inl rfl)).2
  have htbd : t ∈ bd N.D := (hFbd.symm.subset (Or.inr rfl)).2
  obtain ⟨B₁, B₂, hcomp, hdis, hunion, hline, -⟩ :=
    Net.oArc_components_diff_pair N.isOArc_bd_D hsbd htbd hst
  obtain ⟨k, hk, hkr, hk0, hk1⟩ := hline.exists_arc
  have hbd : discBd (univ : Set N.D) = bd N.D :=
    image_bd_homeomorph (Homeomorph.Set.univ N.D)
  have hrange : range k ⊆ discBd (univ : Set N.D) := by
    rw [hkr, hbd]
    rintro x (hx | hx)
    · exact (hunion.symm ▸ Or.inl hx : x ∈ bd N.D \ {s, t}).1
    · rcases hx with rfl | hx
      · exact hsbd
      · exact (mem_singleton_iff.mp hx) ▸ htbd
  obtain ⟨C, A, B, -, hcover, hA, hB, hAB, hI, hbA, hbB, -⟩ :=
    exists_disc_cut_with_boundary_arc N.isClosedDisc_D k hk hrange (by rwa [hk0, hk1])
      (subset_univ F) (by rw [hk0, hk1, hbd]; exact hFbd)
  rw [hbd] at hcover
  have hrA : range k ⊆ A := fun x hx => discBd_subset A (hbA ▸ Or.inl hx)
  have hCB : C ⊆ B := fun x hx => discBd_subset B (hbB ▸ Or.inl hx)
  refine ⟨A, B, B₁, B₂, hA, hB, hAB, hI, ?_, ?_, hcomp, ?_, ?_, ?_⟩
  · rw [hbA]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl ⟨hrA hx, hcover ▸ Or.inl hx⟩
      · exact Or.inr hx
    · rintro (⟨hx, hb⟩ | hx)
      · rcases hcover.symm ▸ hb with h | h
        · exact Or.inl h
        · exact Or.inr (hI ▸ ⟨hx, hCB h⟩)
      · exact Or.inr hx
  · rw [hbB]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl ⟨hCB hx, hcover ▸ Or.inr hx⟩
      · exact Or.inr hx
    · rintro (⟨hx, hb⟩ | hx)
      · rcases hcover.symm ▸ hb with h | h
        · exact Or.inr (hI ▸ ⟨hrA h, hx⟩)
        · exact Or.inl h
      · exact Or.inr hx
  · rintro rfl
    obtain ⟨x, hx⟩ : B₁.Nonempty := by
      by_contra hn
      have hempty : B₁ = ∅ := not_nonempty_iff_eq_empty.mp hn
      have hc := hcomp
      rw [hempty] at hc hunion
      have : (bd N.D \ {s, t}) = ∅ := by rw [hunion]; simp
      rw [this] at hc
      have hm : (∅ : Set N.D) ∈ componentsIn (∅ : Set N.D) := hc.symm ▸ Or.inl rfl
      obtain ⟨y, hy, -⟩ := hm
      exact hy
    exact disjoint_left.mp hdis hx hx
  · rintro x ⟨⟨hxA, hxb⟩, hxe⟩
    have hx : x ∈ B₁ ∪ B₂ := hunion ▸ ⟨hxb, hxe⟩
    rcases hx with hx | hx
    · exact hx
    · exfalso
      have hxr : x ∉ range k := by
        rw [hkr]
        rintro (h | h)
        · exact disjoint_left.mp hdis h hx
        · exact hxe h
      have hxC : x ∈ C := (hcover.symm ▸ hxb : x ∈ range k ∪ C).resolve_left hxr
      have hxF : x ∈ F := hI ▸ ⟨hxA, hCB hxC⟩
      exact hxe (hFbd.subset ⟨hxF, hxb⟩)
  · rintro x ⟨⟨hxB, hxb⟩, hxe⟩
    have hx : x ∈ B₁ ∪ B₂ := hunion ▸ ⟨hxb, hxe⟩
    rcases hx with hx | hx
    · exfalso
      have hxr : x ∈ range k := hkr ▸ Or.inl hx
      have hxF : x ∈ F := hI ▸ ⟨hrA hxr, hxB⟩
      exact hxe (hFbd.subset ⟨hxF, hxb⟩)
    · exact hx

/-- Two boundary points of the disc of a net are joined by a line through its interior. We pull the
chord back from the unit disc, since `exists_chord` is stated for spaces in the lowest universe. -/
theorem Net.exists_chord (N : Net S) {a b : N.D} (ha : a ∈ bd N.D) (hb : b ∈ bd N.D) (hab : a ≠ b) :
    ∃ F : Set N.D, IsLineWithEnds F a b ∧ F ∩ bd N.D = {a, b} := by
  obtain ⟨eN⟩ := N.isClosedDisc_D
  have : T2Space N.D := N.isSurface_D.2.1
  let B : Set ℂ := Metric.closedBall (0 : ℂ) 1
  obtain ⟨e₀⟩ := (isClosedDisc_closedBall.1 : IsClosedDisc B)
  let e : B ≃ₜ N.D := e₀.symm.trans (eN.trans (Homeomorph.Set.univ N.D))
  have hbdB : discBd B = Subtype.val '' bd B := rfl
  have he : ∀ z, e z ∈ bd N.D ↔ z ∈ bd B := by
    intro z
    have h := image_bd_homeomorph e
    constructor
    · intro hz
      obtain ⟨w, hw, hwz⟩ := h.symm ▸ hz
      exact e.injective hwz ▸ hw
    · intro hz
      exact h ▸ mem_image_of_mem e hz
  have hmem : ∀ {c : N.D}, c ∈ bd N.D → (e.symm c).1 ∈ discBd B := fun {c} hc =>
    hbdB ▸ ⟨e.symm c, (he _).mp (by rwa [e.apply_symm_apply]), rfl⟩
  have hne : (e.symm a).1 ≠ (e.symm b).1 := fun h => hab (e.symm.injective (Subtype.ext h))
  obtain ⟨F₀, hF₀, hsub, hcap⟩ := Surface.exists_chord (Δ := B) isClosedDisc_closedBall.1 (hmem ha)
    (hmem hb) hne
  obtain ⟨k, hk, hkr, hk0, hk1⟩ := hF₀.exists_arc
  have hkB : ∀ t, k t ∈ B := fun t => hsub (hkr ▸ mem_range_self t)
  let k' : unitInterval → N.D := fun t => e ⟨k t, hkB t⟩
  have hk' : IsArcMap k' := ⟨e.continuous.comp (hk.1.subtype_mk hkB), fun x y h =>
    hk.2 (congrArg Subtype.val (e.injective h))⟩
  have h0 : k' 0 = a := by
    change e ⟨k 0, _⟩ = a
    rw [show (⟨k 0, hkB 0⟩ : B) = e.symm a from Subtype.ext hk0, e.apply_symm_apply]
  have h1 : k' 1 = b := by
    change e ⟨k 1, _⟩ = b
    rw [show (⟨k 1, hkB 1⟩ : B) = e.symm b from Subtype.ext hk1, e.apply_symm_apply]
  refine ⟨range k', by simpa only [h0, h1] using hk'.isLineWithEnds, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, hx⟩
    have hb' : (⟨k t, hkB t⟩ : B) ∈ bd B := (he _).mp hx
    have : k t ∈ F₀ ∩ discBd B := ⟨hkr ▸ mem_range_self t, hbdB ▸ ⟨_, hb', rfl⟩⟩
    rw [hcap] at this
    rcases this with h | h
    · refine Or.inl ?_
      change e ⟨k t, hkB t⟩ = a
      rw [show (⟨k t, hkB t⟩ : B) = e.symm a from Subtype.ext h, e.apply_symm_apply]
    · refine Or.inr ?_
      change e ⟨k t, hkB t⟩ = b
      rw [show (⟨k t, hkB t⟩ : B) = e.symm b from Subtype.ext h, e.apply_symm_apply]
  · rintro (rfl | hx)
    · exact ⟨⟨0, h0⟩, ha⟩
    · obtain rfl : x = b := hx
      exact ⟨⟨1, h1⟩, hb⟩

/-- An inner point of a paired side has its image off `bd(Σ)`. Paste the part of the pair around it,
by
the exchange along a chord. Then the point is the image of an inner point of the new disc. -/
theorem Net.φ_f_notMem_bd (hS : IsSurface S) (N : Net S) (i : Fin N.r) {r : unitInterval}
    (hr : r ∈ Ioo (0 : unitInterval) 1) : N.φ (N.f i r) ∉ bd S := by
  have : T2Space S := hS.2.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hr₀ : (0 : ℝ) < r.val := hr.1
  have hr₁ : r.val < 1 := hr.2
  let u : unitInterval := ⟨r.val / 2, by linarith, by linarith⟩
  let v : unitInterval := ⟨(1 + r.val) / 2, by linarith, by linarith⟩
  have hu : 0 < u := show (0 : ℝ) < r.val / 2 by linarith
  have huv : u < v := show r.val / 2 < (1 + r.val) / 2 by linarith
  have hv : v < 1 := show (1 + r.val) / 2 < 1 by linarith
  have hne : N.f i u ≠ N.f i v := fun h => huv.ne (N.injective_f i h)
  obtain ⟨F, hF, hFb⟩ := N.exists_chord (N.range_f_subset_bd i ⟨u, rfl⟩)
    (N.range_f_subset_bd i ⟨v, rfl⟩) hne
  obtain ⟨M, -, A, B, ψ, -, -, -, -, -, -, hAd, -, -, -, hφA, -, -, -, -, hαbd, -⟩ :=
    N.exists_swap_subarc_model i u v hu huv hv hF hFb
  have hpiece : pieceA (N.f i) u.val v.val r = N.f i r := by
    have heq : u.val + r.val * (v.val - u.val) = r.val := by
      change r.val / 2 + r.val * ((1 + r.val) / 2 - r.val / 2) = r.val
      ring
    change extI (N.f i) (u.val + r.val * (v.val - u.val)) = _
    rw [heq, extI_coe]
  have hfA : N.f i r ∈ A := by
    refine discBd_subset A ?_
    rw [hAd]
    exact Or.inl ⟨r, hpiece⟩
  have hint : ψ (Sum.inl ⟨_, hfA⟩) ∉ bd M.D := fun h =>
    ((hαbd ⟨_, hfA⟩).mp h).2 ⟨r, hr, hpiece⟩
  intro hb
  have hmem : M.φ (ψ (Sum.inl ⟨_, hfA⟩)) ∈ M.φ '' (bd M.D)ᶜ := ⟨_, hint, rfl⟩
  rw [M.image_compl_bd, hφA] at hmem
  exact hmem.2 (M.bd_subset_seamU hb)

/-- Subdivide a pair at `x`, if `x` is on an open side, so that `x` misses all open sides. -/
theorem Net.exists_refine_point (N : Net S) (x : N.D) :
    ∃ (M : Net S) (e : N.D ≃ₜ M.D), N.r ≤ M.r ∧ M.φ ∘ e = N.φ ∧ M.seamU = N.seamU ∧
      N.seamV ⊆ M.seamV ∧ M.seamV ⊆ N.seamV ∪ {N.φ x} ∧
      (∀ G : Drawing S, M.bdVertexPreimageCard G = N.bdVertexPreimageCard G) ∧
      M.MissesOpenSides (e x) ∧ ∀ y, N.MissesOpenSides y → M.MissesOpenSides (e y) := by
  by_cases hx : N.MissesOpenSides x
  · exact ⟨N, Homeomorph.refl _, le_rfl, rfl, rfl, Subset.rfl, subset_union_left, fun _ => rfl, hx,
      fun _ hy => hy⟩
  · obtain ⟨j, r, hr, hne⟩ : ∃ j r, r ∈ Ioo (0 : unitInterval) 1 ∧ (N.f j r = x ∨ N.g j r = x) := by
      unfold Net.MissesOpenSides at hx
      push Not at hx
      obtain ⟨j, r, hr, h⟩ := hx
      by_cases h' : N.f j r = x
      · exact ⟨j, r, hr, Or.inl h'⟩
      · exact ⟨j, r, hr, Or.inr (h h')⟩
    have him : N.φ (N.f j r) = N.φ x := by
      rcases hne with h | h
      · rw [h]
      · rw [N.pasting_eq, h]
    obtain ⟨M, e, hM, hmap, hU, hV, hcount, hmiss⟩ := N.exists_refine_pair j r hr.1 hr.2
    have hme : M.φ (e x) = N.φ x := congrFun hmap x
    refine ⟨M, e, by omega, hmap, hU, ?_, ?_, hcount, ?_, hmiss⟩
    · rw [hV]
      exact subset_union_left
    · rw [hV, him]
    · refine M.paired_interiors_ne_of_image_mem_seamV ?_
      rw [hme, hV, him]
      exact Or.inr rfl

/-- `Net.exists_refine_point` at both `s` and `t`. -/
theorem Net.exists_refine_ends (N : Net S) (s t : N.D) :
    ∃ (M : Net S) (e : N.D ≃ₜ M.D), N.r ≤ M.r ∧ M.φ ∘ e = N.φ ∧ M.seamU = N.seamU ∧
      N.seamV ⊆ M.seamV ∧ M.seamV ⊆ N.seamV ∪ {N.φ s, N.φ t} ∧
      (∀ G : Drawing S, M.bdVertexPreimageCard G = N.bdVertexPreimageCard G) ∧
      M.MissesOpenSides (e s) ∧ M.MissesOpenSides (e t) := by
  obtain ⟨M₁, e₁, hr₁, hm₁, hU₁, hV₁, hV₁', hc₁, hs₁, -⟩ := N.exists_refine_point s
  obtain ⟨M₂, e₂, hr₂, hm₂, hU₂, hV₂, hV₂', hc₂, ht₂, hy₂⟩ := M₁.exists_refine_point (e₁ t)
  have hφt : M₁.φ (e₁ t) = N.φ t := congrFun hm₁ t
  refine ⟨M₂, e₁.trans e₂, hr₁.trans hr₂, ?_, hU₂.trans hU₁, hV₁.trans hV₂, ?_, ?_, hy₂ _ hs₁, ht₂⟩
  · funext z
    exact (congrFun hm₂ (e₁ z)).trans (congrFun hm₁ z)
  · refine hV₂'.trans (union_subset (hV₁'.trans ?_) ?_)
    · refine union_subset subset_union_left ?_
      rintro z rfl
      exact Or.inr (Or.inl rfl)
    · rw [hφt]
      rintro z rfl
      exact Or.inr (Or.inr rfl)
  · exact fun G => (hc₂ G).trans (hc₁ G)

/-- The open image of a pair is an edge, with ends the images of the ends of the pair. -/
theorem Net.pair_is_edge [T2Space S] (N : Net S) {J' : Drawing S} (hU : J'.U = N.seamU)
    (hV : N.seamV ⊆ J'.V) (havoid : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.φ (N.f j r) ∉ J'.V)
    (i : Fin N.r) : N.φ '' (N.f i '' Ioo (0 : unitInterval) 1) ∈ J'.E ∧
      J'.toGraph.IsLink (N.φ '' (N.f i '' Ioo (0 : unitInterval) 1)) (N.φ (N.f i 0))
        (N.φ (N.f i 1)) := by
  let c : C(unitInterval, S) := ⟨N.φ ∘ N.f i, N.quotientMap_φ.continuous.comp (N.f i).continuous⟩
  have h := Drawing.eq_edge_of_injOn_Ioo J' c (hV ⟨i, Or.inl rfl⟩) (hV ⟨i, Or.inr rfl⟩)
    (fun t ht => ⟨hU ▸ ⟨N.f i t, N.range_f_subset_bd i ⟨t, rfl⟩, rfl⟩, havoid i t ht⟩)
    (fun x hx y hy hxy => (N.injective_f i)
      (N.injOn_image_open_side i ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy))
  have himg : c '' Ioo (0 : unitInterval) 1 = N.φ '' (N.f i '' Ioo (0 : unitInterval) 1) :=
    image_comp N.φ (N.f i) _
  rwa [himg] at h

/-- Each edge of `J'` lies in `bd(Σ)`, or it is the open image of a pair. -/
theorem Net.edge_cases [T2Space S] (N : Net S) {J' : Drawing S} (hU : J'.U = N.seamU)
    (hV : N.seamV ⊆ J'.V) (havoid : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.φ (N.f j r) ∉ J'.V)
    {e : Set S} (he : e ∈ J'.E) :
    e ⊆ bd S ∨ ∃ i, e = N.φ '' (N.f i '' Ioo (0 : unitInterval) 1) := by
  by_cases hb : e ⊆ bd S
  · exact Or.inl hb
  obtain ⟨z, hz, hzb⟩ := not_subset.mp hb
  have hzU : z ∈ J'.U := J'.closure_subset_U he (subset_closure hz)
  rw [hU] at hzU
  obtain ⟨x, hx, rfl⟩ := hzU
  have hzV : N.φ x ∉ N.seamV := fun h => (he.2.1 hz).2 (hV h)
  obtain ⟨i, w, hw, hφw, -, -⟩ :=
    N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV hx hzb hzV
  refine Or.inr ⟨i, J'.edge_eq_of_mem he (N.pair_is_edge hU hV havoid i).1 hz ?_⟩
  exact ⟨N.f i w, ⟨w, hw, rfl⟩, hφw⟩

/-- The inequality for an edge `e` of `J'` that is not of type (iii) or (iv) and not in `bd(Σ)`,
with
ends `a, b`. It comes from `Net.pair_contacts_le_of_separating`, which needs one side of the pair in
each piece. -/
theorem Net.edge_contacts_le (hS : IsSurface S) (N : Net S) {G J' : Drawing S}
    (hN : N.IsNormalFor G)
    (hmin : ∀ M : Net S, M.IsNormalFor G → N.bdVertexPreimageCard G ≤ M.bdVertexPreimageCard G)
    {F A B C₁ C₂ : Set N.D} {s t : N.D} (hF : IsLineWithEnds F s t) (hst : s ≠ t)
    (hFbd : F ∩ bd N.D = {s, t}) (hs : N.MissesOpenSides s) (ht : N.MissesOpenSides t)
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ∪ B = univ) (hI : A ∩ B = F)
    (hAd : discBd A = (A ∩ bd N.D) ∪ F) (hBd : discBd B = (B ∩ bd N.D) ∪ F)
    (hC₁ : (A ∩ bd N.D) \ {s, t} ⊆ C₁) (hC₂ : (B ∩ bd N.D) \ {s, t} ⊆ C₂)
    (hNormal : G.IsNormal (N.φ '' F)) (hU : J'.U = N.seamU) (hV : N.seamV ⊆ J'.V)
    (havoid : ∀ j r, r ∈ Ioo (0 : unitInterval) 1 → N.φ (N.f j r) ∉ J'.V)
    {e : Set S} {a b : S} (hab : a ≠ b) (hlink : J'.toGraph.IsLink e a b)
    (i : Fin N.r) (hei : e = N.φ '' (N.f i '' Ioo (0 : unitInterval) 1))
    (h3 : ¬ IsNetEdgeType3 N C₁ e) (h4 : ¬ IsNetEdgeType4 N C₂ e) :
    2 * (e ∩ G.V).ncard + ({a} ∩ G.V).ncard + ({b} ∩ G.V).ncard ≤
      2 * (N.φ '' (F \ {s, t}) ∩ G.V).ncard + ({N.φ s} ∩ G.V).ncard + ({N.φ t} ∩ G.V).ncard := by
  have hT2 : T2Space S := hS.2.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hfbd : ∀ r, N.f i r ∈ bd N.D := fun r => N.range_f_subset_bd i ⟨r, rfl⟩
  have hgbd : ∀ r, N.g i r ∈ bd N.D := fun r => N.range_g_subset_bd i ⟨r, rfl⟩
  obtain ⟨hfp, hgp⟩ := N.sides_subset_one_cut_piece hA hB hAB hI hFbd hs ht
  have hsplit : ∀ {P Q : Set N.D}, IsClosedDisc P → IsClosedDisc Q → P ∪ Q = univ → P ∩ Q = F →
      discBd P = (P ∩ bd N.D) ∪ F → discBd Q = (Q ∩ bd N.D) ∪ F →
      range (N.f i) ⊆ P → range (N.g i) ⊆ Q →
      2 * (e ∩ G.V).ncard + ({N.φ (N.f i 0)} ∩ G.V).ncard + ({N.φ (N.f i 1)} ∩ G.V).ncard ≤
        2 * (N.φ '' (F \ {s, t}) ∩ G.V).ncard + ({N.φ s} ∩ G.V).ncard +
          ({N.φ t} ∩ G.V).ncard := by
    intro P Q hP hQ hPQ hPI hPd hQd hfP hgQ
    rw [hei]
    refine N.pair_contacts_le_of_separating hS i hN hmin hF hst hFbd hs ht hP hQ hPQ hPI hPd hQd
      ?_ ?_ hNormal
    · rintro _ ⟨r, rfl⟩
      exact hPd ▸ Or.inl ⟨hfP ⟨r, rfl⟩, hfbd r⟩
    · rintro _ ⟨r, rfl⟩
      exact hQd ▸ Or.inl ⟨hgQ ⟨r, rfl⟩, hgbd r⟩
  have hoff : e ∩ bd S = ∅ := by
    refine eq_empty_of_forall_notMem ?_
    rintro z ⟨hz, hzb⟩
    rw [hei] at hz
    obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hz
    exact N.φ_f_notMem_bd hS i hr hzb
  have hends : 2 * (e ∩ G.V).ncard + ({N.φ (N.f i 0)} ∩ G.V).ncard +
      ({N.φ (N.f i 1)} ∩ G.V).ncard ≤
        2 * (N.φ '' (F \ {s, t}) ∩ G.V).ncard + ({N.φ s} ∩ G.V).ncard +
          ({N.φ t} ∩ G.V).ncard := by
    have hfib : ∀ {C : Set N.D} {P : Set N.D}, (P ∩ bd N.D) \ {s, t} ⊆ C → range (N.f i) ⊆ P →
        range (N.g i) ⊆ P → ∀ z ∈ e, N.φ ⁻¹' {z} ⊆ C := by
      intro C P hC hf hg z hz
      rw [hei] at hz
      obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hz
      rw [N.fiber_eq_pair_of_mem_Ioo i hr]
      rintro x (rfl | hx)
      · refine hC ⟨⟨hf ⟨r, rfl⟩, hfbd r⟩, ?_⟩
        rintro (h | h)
        · exact (hs i r hr).1 h
        · exact (ht i r hr).1 h
      · obtain rfl : x = N.g i r := hx
        refine hC ⟨⟨hg ⟨r, rfl⟩, hgbd r⟩, ?_⟩
        rintro (h | h)
        · exact (hs i r hr).2 h
        · exact (ht i r hr).2 h
    rcases hfp i with hf | hf <;> rcases hgp i with hg | hg
    · exact absurd ⟨hoff, hfib hC₁ hf hg⟩ h3
    · exact hsplit hA hB hAB hI hAd hBd hf hg
    · exact hsplit hB hA (by rwa [union_comm]) (by rwa [inter_comm]) hBd hAd hf hg
    · exact absurd ⟨hoff, hfib hC₂ hf hg⟩ h4
  have hlink' := (N.pair_is_edge hU hV havoid i).2
  rw [← hei] at hlink'
  rcases hlink.eq_and_eq_or_eq_and_eq hlink' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hends
  · omega

end GraphMinor.GM07
