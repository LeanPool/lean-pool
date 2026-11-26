/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
public import LeanPool.GraphMinor.Surface.ArcTools
import LeanPool.GraphMinor.GM07.NetSwapSides
import LeanPool.GraphMinor.GM07.NetSwapReplacement
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The replacement pair of side maps

In VII (2.6), page 218, the two new paired sides keep the
outer parts of the selected old pair and insert the two lifts
of the cutting line. Construct both maps using the same path
parameters. The retained lift gives one injective side. The
pasting-fiber calculation gives injectivity of its mate. Their
images under the associated surjection agree at every parameter.
-/

public section

namespace GraphMinor.GM07

open Set Surface

private theorem replacement_ranges_subset_boundary
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) {u v : unitInterval}
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D}
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v})
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hBd : discBd B = C ∪ F)
    (α : A → T) (β : B → T)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hmates : range (N.g i) ⊆ discBd B)
    (hleft : N.f i '' Icc 0 u ⊆ discBd B)
    (hright : N.f i '' Icc v 1 ⊆ discBd B) :
    ((β '' {x : B | x.val ∈ N.f i '' Icc 0 u} ∪ β '' {x : B | x.val ∈ F}) ∪
      β '' {x : B | x.val ∈ N.f i '' Icc v 1} ⊆ bd T) ∧
    ((β '' {x : B | x.val ∈ N.g i '' Icc 0 u} ∪ α '' {x : A | x.val ∈ F}) ∪
      β '' {x : B | x.val ∈ N.g i '' Icc v 1} ⊆ bd T) := by
  have hfgOpen : Disjoint (range (N.f i))
      (pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
    rw [image_pieceA_Ioo_unitInterval (N.g i) u v huv]
    apply disjoint_left.mpr
    rintro x hx ⟨w, hw, rfl⟩
    exact N.internally_disjoint_gf i i w ⟨hu.trans hw.1, hw.2.trans hv⟩ hx
  have hFgoff : Disjoint F (pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
    apply disjoint_left.mpr
    intro x hxF hxg
    have hxg' : x ∈ N.g i '' Ioo u v :=
      image_pieceA_Ioo_unitInterval (N.g i) u v huv ▸ hxg
    obtain ⟨w, hw, hwx⟩ := hxg'
    have hxbd : x ∈ bd N.D := N.range_g_subset_bd i ⟨w, hwx⟩
    have hxfi : x ∈ range (N.f i) := by
      rcases hFbd.subset ⟨hxF, hxbd⟩ with he | he
      · exact ⟨u, he.symm⟩
      · exact ⟨v, (mem_singleton_iff.mp he).symm⟩
    exact disjoint_left.mp hfgOpen hxfi hxg
  have hFfoff : Disjoint F (pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1) := by
    rw [image_pieceA_Ioo_unitInterval (N.f i) u v huv]
    apply disjoint_left.mpr
    rintro x hxF ⟨w, hw, rfl⟩
    have hend := hFbd.subset ⟨hxF, N.range_f_subset_bd i (mem_range_self w)⟩
    rcases hend with he | he
    · exact hw.1.ne' (N.injective_f i he)
    · exact hw.2.ne (N.injective_f i (mem_singleton_iff.mp he))
  have hgoff : ∀ t : unitInterval, t ≤ u ∨ v ≤ t →
      N.g i t ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1 := by
    intro t ht
    rw [image_pieceA_Ioo_unitInterval (N.g i) u v huv]
    rintro ⟨w, hw, hwt⟩
    have hwt' : w = t := N.injective_g i hwt
    rcases ht with ht | ht
    · exact (not_le_of_gt hw.1) (hwt'.symm ▸ ht)
    · exact (not_le_of_gt hw.2) (hwt'.symm ▸ ht)
  have hβfL : ∀ x : B, x.val ∈ N.f i '' Icc 0 u → β x ∈ bd T := by
    intro x hx
    exact (hβbd x).mpr ⟨hleft hx,
      fun h => disjoint_left.mp hfgOpen (image_subset_range _ _ hx) h⟩
  have hβfR : ∀ x : B, x.val ∈ N.f i '' Icc v 1 → β x ∈ bd T := by
    intro x hx
    exact (hβbd x).mpr ⟨hright hx,
      fun h => disjoint_left.mp hfgOpen (image_subset_range _ _ hx) h⟩
  have hβF : ∀ x : B, x.val ∈ F → β x ∈ bd T := by
    intro x hx
    exact (hβbd x).mpr ⟨hBd ▸ Or.inr hx, fun h => disjoint_left.mp hFgoff hx h⟩
  have hαF : ∀ x : A, x.val ∈ F → α x ∈ bd T := by
    intro x hx
    exact (hαbd x).mpr ⟨hAd ▸ Or.inr hx, fun h => disjoint_left.mp hFfoff hx h⟩
  have hβgL : ∀ x : B, x.val ∈ N.g i '' Icc 0 u → β x ∈ bd T := by
    rintro x ⟨t, ht, htx⟩
    apply (hβbd x).mpr
    refine ⟨hmates ⟨t, htx⟩, ?_⟩
    rw [← htx]
    exact hgoff t (Or.inl ht.2)
  have hβgR : ∀ x : B, x.val ∈ N.g i '' Icc v 1 → β x ∈ bd T := by
    rintro x ⟨t, ht, htx⟩
    apply (hβbd x).mpr
    refine ⟨hmates ⟨t, htx⟩, ?_⟩
    rw [← htx]
    exact hgoff t (Or.inr ht.1)
  constructor
  · rintro z ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact hβfL x hx
    · exact hβF x hx
    · exact hβfR x hx
  · rintro z ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩)
    · exact hβgL x hx
    · exact hαF x hx
    · exact hβgR x hx

/-- Construct the two replacement side maps in the cut-and-paste
configuration of VII (2.6), page 218. They remain injective and
paired under the associated map, with the old endpoint images. -/
theorem Net.exists_replacement_pair
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (N : Net S) (i : Fin N.r) (u v : unitInterval)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {F C A B : Set N.D} (hF : IsLineWithEnds F (N.f i u) (N.f i v))
    (hFbd : F ∩ bd N.D = {N.f i u, N.f i v}) (hI : A ∩ B = F)
    (hAd : discBd A = range (pieceA (N.f i) u.val v.val) ∪ F)
    (hcover : range (pieceA (N.f i) u.val v.val) ∪ C = bd N.D)
    (hBd : discBd B = C ∪ F)
    (α : A → T) (β : B → T) (hcα : Continuous α) (hcβ : Continuous β)
    (hiα : Function.Injective α) (hiβ : Function.Injective β)
    (hcross : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = pieceA (N.f i) u.val v.val t ∧ y.val = pieceA (N.g i) u.val v.val t)
    (hαbd : ∀ x : A, α x ∈ bd T ↔ x.val ∈ discBd A ∧
      x.val ∉ pieceA (N.f i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (hβbd : ∀ y : B, β y ∈ bd T ↔ y.val ∈ discBd B ∧
      y.val ∉ pieceA (N.g i) u.val v.val '' Ioo (0 : unitInterval) 1)
    (φ : T → S) (hφA : ∀ x : A, φ (α x) = N.φ x.val)
    (hφB : ∀ y : B, φ (β y) = N.φ y.val) :
    ∃ p q : Curve T, Function.Injective p ∧ Function.Injective q ∧
      (∀ t, φ (p t) = φ (q t)) ∧
      φ (p 0) = N.φ (N.f i 0) ∧ φ (p 1) = N.φ (N.f i 1) ∧
      φ (q 0) = N.φ (N.g i 0) ∧ φ (q 1) = N.φ (N.g i 1) ∧
      range p = (β '' {x : B | x.val ∈ N.f i '' Icc 0 u} ∪
        β '' {x : B | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.f i '' Icc v 1} ∧
      range q = (β '' {x : B | x.val ∈ N.g i '' Icc 0 u} ∪
        α '' {x : A | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.g i '' Icc v 1} ∧
      range p ⊆ bd T ∧ range q ⊆ bd T ∧
      p 0 ∈ β '' {x : B | x.val = N.f i 0} ∧ p 1 ∈ β '' {x : B | x.val = N.f i 1} ∧
      q 0 ∈ β '' {x : B | x.val = N.g i 0} ∧ q 1 ∈ β '' {x : B | x.val = N.g i 1} ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, p t ∉ range q) ∧
      (∀ t ∈ Ioo (0 : unitInterval) 1, q t ∉ range p) := by
  let a : Path (N.f i 0) (N.f i 1) :=
    { toContinuousMap := N.f i, source' := rfl, target' := rfl }
  let b : Path (N.g i 0) (N.g i 1) :=
    { toContinuousMap := N.g i, source' := rfl, target' := rfl }
  have ha : IsArcMap a := ⟨a.continuous, N.injective_f i⟩
  have hb : IsArcMap b := ⟨b.continuous, N.injective_g i⟩
  obtain ⟨k, hk, hkF, hk0, hk1⟩ := hF.exists_arc
  let c : Path (a u) (a v) :=
    { toFun := k, continuous_toFun := hk.1, source' := hk0, target' := hk1 }
  have hc : IsArcMap c := hk
  have hcF : range c = F := hkF
  have hca : range c ∩ range a = {a u, a v} := by
    rw [hcF]
    apply Subset.antisymm
    · exact fun x hx => hFbd.subset ⟨hx.1, N.range_f_subset_bd i hx.2⟩
    · rintro x (rfl | rfl)
      · exact ⟨hF.left_mem, mem_range_self u⟩
      · exact ⟨hF.right_mem, mem_range_self v⟩
  have hFA : F ⊆ A := fun x hx => (hI.symm ▸ hx).1
  have hFB : F ⊆ B := fun x hx => (hI.symm ▸ hx).2
  have hcA : ∀ t, c t ∈ A := fun t => hFA (hcF ▸ mem_range_self t)
  have hcB : ∀ t, c t ∈ B := fun t => hFB (hcF ▸ mem_range_self t)
  obtain ⟨hother, hmates, hleft, hright⟩ := N.sides_on_retained_piece i u v hu huv hv hF hcover hBd
  have hbB : ∀ t, b t ∈ B := fun t => discBd_subset B (hmates i (mem_range_self t))
  have hlB : ∀ t, (a.subpath 0 u) t ∈ B := by
    intro t
    have hx := (Path.range_subpath_of_le a 0 u (unitInterval.nonneg u)).subset (mem_range_self t)
    exact discBd_subset B (hleft hx)
  have hrB : ∀ t, (a.subpath v 1) t ∈ B := by
    intro t
    have hx := (Path.range_subpath_of_le a v 1 (unitInterval.le_one v)).subset (mem_range_self t)
    exact discBd_subset B (hright hx)
  let left := (pathWithinSet (a.subpath 0 u) hlB).map hcβ
  let middle := (pathWithinSet c hcB).map hcβ
  let right := (pathWithinSet (a.subpath v 1) hrB).map hcβ
  let p := (left.trans middle).trans right
  let old := (a.subpath 0 u).trans c |>.trans (a.subpath v 1)
  have hOldArc : IsArcMap old := isArcMap_spliced_path a ha hu huv hv c hc hca
  have hOldB : ∀ t, old t ∈ B := by
    intro t
    have ht : old t ∈ range old := mem_range_self t
    rw [Path.trans_range, Path.trans_range] at ht
    rcases ht with (⟨s, hs⟩ | ⟨s, hs⟩) | ⟨s, hs⟩
    · exact hs ▸ hlB s
    · exact hs ▸ hcB s
    · exact hs ▸ hrB s
  have hp : ∀ t, p t = β ⟨old t, hOldB t⟩ := by
    intro t
    change (((left.trans middle).trans right) t) = β ⟨(((a.subpath 0 u).trans c).trans
      (a.subpath v 1)) t, _⟩
    simp only [Path.trans_apply]
    split_ifs <;> rfl
  have hpArc : IsArcMap p := by
    refine ⟨p.continuous, ?_⟩
    intro s t heq
    rw [hp s, hp t] at heq
    exact hOldArc.2 (congrArg Subtype.val (hiβ heq))
  let base := (pathWithinSet b hbB).map hcβ
  let attached := (pathWithinSet c hcA).map hcα
  have hcross' : ∀ (x : A) (y : B), α x = β y ↔
      ∃ t, x.val = (a.subpath u v) t ∧ y.val = (b.subpath u v) t := by
    intro x y
    have h := hcross x y
    change α x = β y ↔ ∃ t, x.val = pieceA a u.val v.val t ∧
      y.val = pieceA b u.val v.val t at h
    simpa only [pieceA_eq_subpath] using h
  have h0 : attached 0 = base u := by
    change α ⟨c 0, hcA 0⟩ = β ⟨b u, hbB u⟩
    exact (hcross' _ _).mpr ⟨0, c.source.trans (a.subpath u v).source.symm,
      (b.subpath u v).source.symm⟩
  have h1 : attached 1 = base v := by
    change α ⟨c 1, hcA 1⟩ = β ⟨b v, hbB v⟩
    exact (hcross' _ _).mpr ⟨1, c.target.trans (a.subpath u v).target.symm,
      (b.subpath u v).target.symm⟩
  let mid := attached.cast (h0.symm.trans attached.source) (h1.symm.trans attached.target)
  let q := ((base.subpath 0 u).trans mid).trans (base.subpath v 1)
  have hqArc : IsArcMap q := isArcMap_spliced_mate_path a b ha hb hu huv hv c hc hca hcA hbB
    α β hiα hiβ hcross' base mid (fun t => rfl) (fun t => rfl)
  have hlφ : ∀ t, φ (left t) = φ ((base.subpath 0 u) t) := by
    intro t
    change φ (β ⟨(a.subpath 0 u) t, hlB t⟩) =
      φ (β ⟨b (Icc.convexComb 0 u t), hbB (Icc.convexComb 0 u t)⟩)
    rw [hφB, hφB]
    exact N.pasting_eq i (Icc.convexComb 0 u t)
  have hmφ : ∀ t, φ (middle t) = φ (mid t) := by
    intro t
    change φ (β ⟨c t, hcB t⟩) = φ (α ⟨c t, hcA t⟩)
    rw [hφB, hφA]
  have hrφ : ∀ t, φ (right t) = φ ((base.subpath v 1) t) := by
    intro t
    change φ (β ⟨(a.subpath v 1) t, hrB t⟩) =
      φ (β ⟨b (Icc.convexComb v 1 t), hbB (Icc.convexComb v 1 t)⟩)
    rw [hφB, hφB]
    exact N.pasting_eq i (Icc.convexComb v 1 t)
  have hpq : ∀ t, φ (p t) = φ (q t) :=
    image_path_trans_eq φ _ _ _ _ (image_path_trans_eq φ _ _ _ _ hlφ hmφ) hrφ
  have hleftRange : range left = β '' {x : B | x.val ∈ N.f i '' Icc 0 u} := by
    change range (fun t => β ⟨(a.subpath 0 u) t, hlB t⟩) = _
    rw [range_map_into_set, Path.range_subpath_of_le a 0 u (unitInterval.nonneg u)]
    rfl
  have hrightRange : range right = β '' {x : B | x.val ∈ N.f i '' Icc v 1} := by
    change range (fun t => β ⟨(a.subpath v 1) t, hrB t⟩) = _
    rw [range_map_into_set, Path.range_subpath_of_le a v 1 (unitInterval.le_one v)]
    rfl
  have hmiddleRange : range middle = β '' {x : B | x.val ∈ F} := by
    change range (fun t => β ⟨c t, hcB t⟩) = _
    rw [range_map_into_set, hcF]
  have hbaseLeft : range (base.subpath 0 u) = β '' {x : B | x.val ∈ N.g i '' Icc 0 u} := by
    change range (fun t => β ⟨(b.subpath 0 u) t, hbB (Icc.convexComb 0 u t)⟩) = _
    have hh := range_map_into_set (fun t => (b.subpath 0 u) t)
      (fun t => hbB (Icc.convexComb 0 u t)) β
    rw [Path.range_subpath_of_le b 0 u (unitInterval.nonneg u)] at hh
    exact hh
  have hbaseRight : range (base.subpath v 1) = β '' {x : B | x.val ∈ N.g i '' Icc v 1} := by
    change range (fun t => β ⟨(b.subpath v 1) t, hbB (Icc.convexComb v 1 t)⟩) = _
    have hh := range_map_into_set (fun t => (b.subpath v 1) t)
      (fun t => hbB (Icc.convexComb v 1 t)) β
    rw [Path.range_subpath_of_le b v 1 (unitInterval.le_one v)] at hh
    exact hh
  have hmidRange : range mid = α '' {x : A | x.val ∈ F} := by
    change range (fun t => α ⟨c t, hcA t⟩) = _
    rw [range_map_into_set, hcF]
  have hpRange : range p = (β '' {x : B | x.val ∈ N.f i '' Icc 0 u} ∪
      β '' {x : B | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.f i '' Icc v 1} := by
    change range ((left.trans middle).trans right) = _
    rw [Path.trans_range, Path.trans_range, hleftRange, hmiddleRange, hrightRange]
  have hqRange : range q = (β '' {x : B | x.val ∈ N.g i '' Icc 0 u} ∪
      α '' {x : A | x.val ∈ F}) ∪ β '' {x : B | x.val ∈ N.g i '' Icc v 1} := by
    change range (((base.subpath 0 u).trans mid).trans (base.subpath v 1)) = _
    rw [Path.trans_range, Path.trans_range, hbaseLeft, hmidRange, hbaseRight]
  obtain ⟨hpbd, hqbd⟩ :=
    replacement_ranges_subset_boundary N i hu huv hv hFbd hAd hBd α β hαbd hβbd
      (hmates i) hleft hright
  have hFg := (N.cutting_line_disjoint_other_sides i hu huv hv hFbd).2 i
  have hP : Disjoint (β '' {x : B | x.val ∈ F})
      (β '' {x : B | x.val ∈ range (N.g i)}) := by
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy : y = x := hiβ heq
    exact disjoint_left.mp hFg hx (hxy ▸ hy)
  have hQ : Disjoint (α '' {x : A | x.val ∈ F})
      (β '' {x : B | x.val ∈ range (N.f i)}) := by
    exact ((N.attached_piece_disjoint_other_sides i hu huv hv α β hcross).1 i).mono_left
      (image_subset_range _ _)
  have hPQ : Disjoint (β '' {x : B | x.val ∈ F}) (α '' {x : A | x.val ∈ F}) := by
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, _, heq⟩
    obtain ⟨t, _, hxt⟩ := (hcross y x).mp heq
    have hxg : x.val ∈ range (N.g i) := by
      have hseg := range_pieceA_unitInterval (N.g i) u v huv.le
      exact image_subset_range _ _ (hseg.subset ⟨t, hxt.symm⟩)
    exact disjoint_left.mp hFg hx hxg
  have hpCoarse : range p ⊆ β '' {x : B | x.val ∈ range (N.f i)} ∪
      β '' {x : B | x.val ∈ F} := by
    rw [hpRange]
    rintro z ((⟨x, hx, rfl⟩ | hz) | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
  have hqCoarse : range q ⊆ β '' {x : B | x.val ∈ range (N.g i)} ∪
      α '' {x : A | x.val ∈ F} := by
    rw [hqRange]
    rintro z ((⟨x, hx, rfl⟩ | hz) | ⟨x, hx, rfl⟩)
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
    · exact Or.inr hz
    · exact Or.inl ⟨x, image_subset_range _ _ hx, rfl⟩
  have hpqDisj := internally_disjoint_replacement_sides (N.f i) (N.g i) β hiβ
    (N.internally_disjoint_fg i i) (N.internally_disjoint_gf i i) p q hpArc.2 hqArc.2
    hpCoarse hqCoarse hP hQ hPQ
    ⟨_, rfl, p.source.symm⟩ ⟨_, rfl, p.target.symm⟩
    ⟨_, rfl, q.source.symm⟩ ⟨_, rfl, q.target.symm⟩
  refine ⟨p.toContinuousMap, q.toContinuousMap, hpArc.2, hqArc.2, hpq, ?_, ?_, ?_, ?_,
    hpRange, hqRange, hpRange ▸ hpbd, hqRange ▸ hqbd, ?_, ?_, ?_, ?_, hpqDisj.1, hpqDisj.2⟩
  · exact (congrArg φ p.source).trans (hφB _)
  · exact (congrArg φ p.target).trans (hφB _)
  · exact (congrArg φ q.source).trans (hφB _)
  · exact (congrArg φ q.target).trans (hφB _)
  · exact ⟨_, rfl, p.source.symm⟩
  · exact ⟨_, rfl, p.target.symm⟩
  · exact ⟨_, rfl, q.source.symm⟩
  · exact ⟨_, rfl, q.target.symm⟩

end GraphMinor.GM07
