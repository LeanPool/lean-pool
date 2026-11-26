/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
public import LeanPool.GraphMinor.Surface.ArcTools
public import Mathlib.Topology.Path
public import Mathlib.Topology.Subpath

/-!
# Joining the replacement sides of the net

For VII (2.6), page 218, the new paired sides join the two
outer parts of each old side to a lift of the cutting line.
Two injective paths joined at their only common point still
form an injective path. The common point has parameter one
on the first path and zero on the second, so the two global
parameters agree there as well.
-/

public section

namespace GraphMinor.GM07

open Set Surface

/-- Joining two arc paths at their only common end gives an
arc path. This is used for the replacement sides in the net
exchange of VII (2.6), page 218. -/
theorem isArcMap_path_trans
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (a : Path x y) (b : Path y z) (ha : IsArcMap a) (hb : IsArcMap b)
    (hmeet : ∀ s t, a s = b t → s = 1 ∧ t = 0) : IsArcMap (a.trans b) := by
  refine ⟨(a.trans b).continuous, ?_⟩
  intro s t heq
  rw [Path.trans_apply, Path.trans_apply] at heq
  split_ifs at heq with hs ht
  · have h := congrArg Subtype.val (ha.2 heq)
    exact Subtype.ext (by dsimp at h; linarith)
  · obtain ⟨h1, h0⟩ := hmeet _ _ heq
    have h1' := congrArg Subtype.val h1
    have h0' := congrArg Subtype.val h0
    exact Subtype.ext (by dsimp at h1' h0'; linarith)
  · obtain ⟨h1, h0⟩ := hmeet _ _ heq.symm
    have h1' := congrArg Subtype.val h1
    have h0' := congrArg Subtype.val h0
    exact Subtype.ext (by dsimp at h1' h0'; linarith)
  · have h := congrArg Subtype.val (hb.2 heq)
    exact Subtype.ext (by dsimp at h; linarith)

/-- An increasing restriction of an arc path remains an arc.
This parametrizes the outer pieces of a side in VII (2.6). -/
theorem isArcMap_subpath_of_lt
    {X : Type*} [TopologicalSpace X] {x y : X} (a : Path x y) (ha : IsArcMap a)
    {u v : unitInterval} (huv : u < v) : IsArcMap (a.subpath u v) := by
  refine ⟨(a.subpath u v).continuous, ?_⟩
  intro s t heq
  have h := congrArg Subtype.val (ha.2 heq)
  change ((1 - s.val) * u.val + s.val * v.val) =
    ((1 - t.val) * u.val + t.val * v.val) at h
  have hmul : (v.val - u.val) * s.val = (v.val - u.val) * t.val := by
    nlinarith only [h]
  have huvR : u.val < v.val := huv
  exact Subtype.ext (mul_left_cancel₀ (sub_pos.mpr huvR).ne' hmul)

/-- The range-intersection form of injective path concatenation,
used when the side pieces have only their common end in common. -/
theorem isArcMap_path_trans_of_range_inter
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (a : Path x y) (b : Path y z) (ha : IsArcMap a) (hb : IsArcMap b)
    (hmeet : Set.range a ∩ Set.range b = {y}) : IsArcMap (a.trans b) := by
  apply isArcMap_path_trans a b ha hb
  intro s t heq
  have hsy : a s = y := Set.mem_singleton_iff.mp
    (hmeet.subset ⟨Set.mem_range_self s, ⟨t, heq.symm⟩⟩)
  have hty : b t = y := heq.symm.trans hsy
  exact ⟨ha.2 (hsy.trans a.target.symm), hb.2 (hty.trans b.source.symm)⟩

/-- Replace an interior subarc by a new arc meeting the old arc
only at the two cut points. The two outer pieces and the new
arc form the replacement side used in VII (2.6), page 218. -/
theorem isArcMap_spliced_path
    {X : Type*} [TopologicalSpace X] {x y : X} (a : Path x y) (ha : IsArcMap a)
    {u v : unitInterval} (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (c : Path (a u) (a v)) (hc : IsArcMap c)
    (hcut : Set.range c ∩ Set.range a = {a u, a v}) :
    IsArcMap (((a.subpath 0 u).trans c).trans (a.subpath v 1)) := by
  have hl := isArcMap_subpath_of_lt a ha hu
  have hr := isArcMap_subpath_of_lt a ha hv
  have hleft : Set.range (a.subpath 0 u) = a '' Set.Icc 0 u :=
    Path.range_subpath_of_le a 0 u (unitInterval.nonneg u)
  have hright : Set.range (a.subpath v 1) = a '' Set.Icc v 1 :=
    Path.range_subpath_of_le a v 1 (unitInterval.le_one v)
  have hLC : Set.range (a.subpath 0 u) ∩ Set.range c = {a u} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzL, hzC⟩
      obtain ⟨s, hs, rfl⟩ := hleft.subset hzL
      have hsC := hcut.subset ⟨hzC, Set.mem_range_self s⟩
      rcases hsC with heq | heq
      · exact heq
      · have hsv : s = v := ha.2 (Set.mem_singleton_iff.mp heq)
        exact False.elim ((not_le_of_gt huv) (hsv ▸ hs.2))
    · rintro z rfl
      exact ⟨⟨1, (a.subpath 0 u).target⟩, ⟨0, c.source⟩⟩
  have hlc : IsArcMap ((a.subpath 0 u).trans c) :=
    isArcMap_path_trans_of_range_inter _ _ hl hc hLC
  have hLCR : Set.range ((a.subpath 0 u).trans c) ∩ Set.range (a.subpath v 1) = {a v} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzLC, hzR⟩
      obtain ⟨t, ht, rfl⟩ := hright.subset hzR
      rw [Path.trans_range] at hzLC
      rcases hzLC with hzL | hzC
      · obtain ⟨s, hs, hst⟩ := hleft.subset hzL
        have heq : s = t := ha.2 hst
        exact False.elim ((not_le_of_gt huv) (ht.1.trans (heq ▸ hs.2)))
      · have htC := hcut.subset ⟨hzC, Set.mem_range_self t⟩
        rcases htC with heq | heq
        · have htu : t = u := ha.2 heq
          exact False.elim ((not_le_of_gt huv) (htu ▸ ht.1))
        · exact heq
    · rintro z rfl
      exact ⟨⟨1, ((a.subpath 0 u).trans c).target⟩, ⟨0, (a.subpath v 1).source⟩⟩
  exact isArcMap_path_trans_of_range_inter _ _ hlc hr hLCR

/-- Three side pieces give an arc when adjacent pieces meet only
at the joining ends and the two outer pieces are disjoint. -/
theorem isArcMap_three_paths
    {X : Type*} [TopologicalSpace X] {w x y z : X}
    (a : Path w x) (b : Path x y) (c : Path y z)
    (ha : IsArcMap a) (hb : IsArcMap b) (hc : IsArcMap c)
    (hab : Set.range a ∩ Set.range b = {x})
    (hbc : Set.range b ∩ Set.range c = {y})
    (hac : Disjoint (Set.range a) (Set.range c)) : IsArcMap ((a.trans b).trans c) := by
  have habc : Set.range (a.trans b) ∩ Set.range c = {y} := by
    rw [Path.trans_range, Set.union_inter_distrib_right, hac.inter_eq, Set.empty_union, hbc]
  exact isArcMap_path_trans_of_range_inter _ _
    (isArcMap_path_trans_of_range_inter _ _ ha hb hab) hc habc

/-- Pointwise agreement of the images of two pairs of paths is
preserved by their concatenation. The paired replacement sides
therefore retain the old net's pasting equations. -/
theorem image_path_trans_eq
    {X Y : Type*} [TopologicalSpace X] (φ : X → Y)
    {x₁ y₁ z₁ x₂ y₂ z₂ : X}
    (a₁ : Path x₁ y₁) (b₁ : Path y₁ z₁) (a₂ : Path x₂ y₂) (b₂ : Path y₂ z₂)
    (ha : ∀ t, φ (a₁ t) = φ (a₂ t)) (hb : ∀ t, φ (b₁ t) = φ (b₂ t)) :
    ∀ t, φ ((a₁.trans b₁) t) = φ ((a₂.trans b₂) t) := by
  intro t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact ha _
  · exact hb _

/-- The affine parametrization of a side piece has exactly the
closed parameter interval as its image. -/
theorem range_pieceA_unitInterval
    {X : Type*} (a : unitInterval → X)
    (u v : unitInterval) (huv : u ≤ v) :
    Set.range (pieceA a u.val v.val) = a '' Set.Icc u v := by
  rw [range_pieceA a u.property.1 huv v.property.2]
  apply Set.Subset.antisymm
  · rintro x ⟨r, hr, rfl⟩
    have hr0 : 0 ≤ r := u.property.1.trans hr.1
    have hr1 : r ≤ 1 := hr.2.trans v.property.2
    exact ⟨⟨r, hr0, hr1⟩, hr, (extI_of_mem a ⟨hr0, hr1⟩).symm⟩
  · rintro x ⟨t, ht, rfl⟩
    exact ⟨t.val, ht, extI_coe a t⟩

/-- Regard a path contained in a cut piece as a path in that
piece, with the induced topology. -/
@[expose] def pathWithinSet
    {X : Type*} [TopologicalSpace X] {x y : X} (a : Path x y)
    {A : Set X} (hA : ∀ t, a t ∈ A) :
    Path (⟨x, a.source ▸ hA 0⟩ : A) ⟨y, a.target ▸ hA 1⟩ where
  toFun t := ⟨a t, hA t⟩
  continuous_toFun := a.continuous.subtype_mk _
  source' := Subtype.ext a.source
  target' := Subtype.ext a.target

/-- Passing to the topology of a cut piece preserves an arc's
injectivity and continuity. -/
theorem isArcMap_pathWithinSet
    {X : Type*} [TopologicalSpace X] {x y : X} (a : Path x y) (ha : IsArcMap a)
    {A : Set X} (hA : ∀ t, a t ∈ A) : IsArcMap (pathWithinSet a hA) := by
  exact ⟨(pathWithinSet a hA).continuous, fun s t h => ha.2 (congrArg Subtype.val h)⟩

/-- The side-piece parametrization and the subpath operation
use the same increasing affine parameter. -/
theorem pieceA_eq_subpath
    {X : Type*} [TopologicalSpace X] {x y : X} (a : Path x y)
    (u v : unitInterval) : pieceA a u.val v.val = (a.subpath u v : unitInterval → X) := by
  funext t
  change extI a (u.val + t.val * (v.val - u.val)) = a (Icc.convexComb u v t)
  have harg : u.val + t.val * (v.val - u.val) = (Icc.convexComb u v t).val := by
    rw [Icc.coe_convexComb]
    ring
  rw [harg, extI_coe]

/-- Two side pieces use the same parameter in the old interval.
The common parameter lies between the subarc endpoints. -/
theorem pieceA_common_parameter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (a : Curve X) (b : Curve Y) (u v : unitInterval) (huv : u ≤ v) (t : unitInterval) :
    ∃ w ∈ Icc u v, pieceA a u.val v.val t = a w ∧ pieceA b u.val v.val t = b w := by
  let ap : Path (a 0) (a 1) := { toContinuousMap := a, source' := rfl, target' := rfl }
  let bp : Path (b 0) (b 1) := { toContinuousMap := b, source' := rfl, target' := rfl }
  refine ⟨Icc.convexComb u v t, ⟨Icc.le_convexComb huv t, Icc.convexComb_le huv t⟩, ?_, ?_⟩
  · change pieceA ap u.val v.val t = _
    rw [pieceA_eq_subpath]
    rfl
  · change pieceA bp u.val v.val t = _
    rw [pieceA_eq_subpath]
    rfl

/-- Every old parameter between the subarc endpoints occurs at
a common parameter of both side pieces. -/
theorem exists_pieceA_common_parameter
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (a : Curve X) (b : Curve Y) (u v t : unitInterval) (ht : t ∈ Icc u v) :
    ∃ r, pieceA a u.val v.val r = a t ∧ pieceA b u.val v.val r = b t := by
  obtain ⟨r, hr⟩ : ∃ r, t = Icc.convexComb u v r :=
    ⟨_, Icc.eq_convexComb ht.1 ht.2⟩
  let ap : Path (a 0) (a 1) := { toContinuousMap := a, source' := rfl, target' := rfl }
  let bp : Path (b 0) (b 1) := { toContinuousMap := b, source' := rfl, target' := rfl }
  refine ⟨r, ?_, ?_⟩
  · change pieceA ap u.val v.val r = _
    rw [pieceA_eq_subpath, hr]
    rfl
  · change pieceA bp u.val v.val r = _
    rw [pieceA_eq_subpath, hr]
    rfl

/-- The image of a map into a cut piece is the image of its
range in that piece. This records the ranges of the spliced
side maps without changing their parameters. -/
theorem range_map_into_set
    {I X Y : Type*} (a : I → X) {A : Set X} (ha : ∀ t, a t ∈ A) (f : A → Y) :
    range (fun t => f ⟨a t, ha t⟩) = f '' {x : A | x.val ∈ range a} := by
  apply Subset.antisymm
  · rintro y ⟨t, rfl⟩
    exact ⟨⟨a t, ha t⟩, mem_range_self t, rfl⟩
  · rintro y ⟨x, ⟨t, ht⟩, rfl⟩
    exact ⟨t, congrArg f (Subtype.ext ht)⟩

/-- The open part of a side piece corresponds exactly to the
open parameter interval. Its endpoints are excluded on both
sides of this equation. -/
theorem image_pieceA_Ioo_unitInterval
    {X : Type*} (a : unitInterval → X)
    (u v : unitInterval) (huv : u < v) :
    pieceA a u.val v.val '' Ioo (0 : unitInterval) 1 = a '' Ioo u v := by
  have huvR : u.val < v.val := huv
  have hd : 0 < v.val - u.val := sub_pos.mpr huvR
  apply Subset.antisymm
  · rintro x ⟨r, hr, rfl⟩
    have hr0 : 0 < r.val := hr.1
    have hr1 : r.val < 1 := hr.2
    have hm0 := mul_pos hr0 hd
    have hm1 := mul_lt_mul_of_pos_right hr1 hd
    let w : unitInterval := ⟨u.val + r.val * (v.val - u.val),
      by linarith [u.property.1], by linarith [v.property.2]⟩
    refine ⟨w, ⟨?_, ?_⟩, ?_⟩
    · change u.val < u.val + r.val * (v.val - u.val)
      linarith
    · change u.val + r.val * (v.val - u.val) < v.val
      linarith
    · exact (extI_of_mem a w.property).symm
  · rintro x ⟨t, ht, rfl⟩
    have hut : u.val < t.val := ht.1
    have htv : t.val < v.val := ht.2
    let r : unitInterval := ⟨(t.val - u.val) / (v.val - u.val),
      (div_pos (sub_pos.mpr hut) hd).le,
      (div_lt_one hd).mpr (by linarith) |>.le⟩
    have hr0 : 0 < r := div_pos (sub_pos.mpr hut) hd
    have hr1 : r < 1 := (div_lt_one hd).mpr (by linarith)
    refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
    change extI a (u.val + r.val * (v.val - u.val)) = a t
    have harg : u.val + r.val * (v.val - u.val) = t.val := by
      dsimp [r]
      rw [div_mul_cancel₀ _ hd.ne']
      ring
    rw [harg, extI_coe]

/-- If an arc's open part misses another set, their intersection
consists only of its two endpoints. -/
theorem range_inter_subset_endpoints
    {X : Type*} (a : unitInterval → X) {K : Set X}
    (h : ∀ t ∈ Ioo (0 : unitInterval) 1, a t ∉ K) :
    range a ∩ K ⊆ {a 0, a 1} := by
  rintro x ⟨⟨t, rfl⟩, hx⟩
  by_cases ht0 : 0 < t
  · by_cases ht1 : t < 1
    · exact (h t ⟨ht0, ht1⟩ hx).elim
    · have ht : t = 1 := le_antisymm (unitInterval.le_one t) (le_of_not_gt ht1)
      exact Or.inr (ht ▸ rfl)
  · have ht : t = 0 := le_antisymm (le_of_not_gt ht0) (unitInterval.nonneg t)
    exact Or.inl (ht ▸ rfl)

/-- An injective interval map has no endpoint in its open part. -/
theorem not_mem_endpoints_of_injective
    {X : Type*} {a : unitInterval → X} (ha : Function.Injective a)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    a t ∉ ({a 0, a 1} : Set X) := by
  rintro (h0 | h1)
  · exact (ne_of_gt ht.1) (ha h0)
  · exact (ne_of_lt ht.2) (ha (mem_singleton_iff.mp h1))

end GraphMinor.GM07
