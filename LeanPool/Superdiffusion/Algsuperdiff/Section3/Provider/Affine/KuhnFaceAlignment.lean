/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.KuhnInterpolation
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology

/-!
# KuhnFaceAlignment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Equal-scale face alignment for Kuhn cells

> "A face-alignment lemma for equal-scale adjacent cubes, together with the
> nested-refinement lemma, supplies the complete-face compatibility actually
> used."

and the gluing step it exists for.

## What is proved

* `closedCarrier_eq_convexHull_vertexSet` -- a closed Kuhn cell **is** the
  convex hull of its `d + 1` labelled corners.  This resolves the second of the
  two identities queued as a disclosure by `KuhnCell.vertex`
  (`Whitney/KuhnCells.lean`).  Still open, and still used nowhere: the first
  queued identity `vertexSet = extremePoints ℝ closedCarrier`, and the
  separate item `affineSpan ℝ vertexSet = ⊤` queued by the uniqueness scope
  note of `KuhnInterpolation.lean`.
* `closedCarrier_inter_subset_commonClosedFace` -- **the face-alignment
  lemma.**  Two Kuhn cells of the *same scale* on the globally aligned triadic
  grid meet only inside the convex hull of the vertices they *share*.  No
  adjacency, face-compatibility or simplicial-complex hypothesis is assumed:
  the conclusion is proved for an arbitrary pair of equal-scale cells, whether
  they sit on the same support cube, on neighbouring cubes, or on cubes that do
  not meet at all.
* `kuhnInterp_eqOn_closedCarrier_inter` and
  `kuhnInterpAffine_eqOn_closedCarrier_inter` -- **the gluing step.**  Two
  equal-scale cells interpolating one global vertex datum agree at every point
  of the intersection of their closed carriers.  Combined with the proved
  refinement statements this is the well-definedness input for the global
  piecewise-affine `ℓ̂_p` of `l.piecewise.affine.approx`.
* `isClosed_closedCarrier` -- a by-product of the convex-hull description,
  recorded because the gluing consumer needs it to patch continuity.

## Scope: exactly what is and is not claimed

The cross-scale direction is deliberately **not** stated in face form: the only
cross-scale facts are the proved containments (a fine cell lies *inside* a
coarse cell), which is all needs and all that is true.

The equal-scale hypothesis is not cosmetic.  It is what makes the two support
cubes members of one aligned grid, so that at any common point their indices
differ by at most one in each coordinate; the proof of
`closedCarrier_inter_subset_commonClosedFace` runs on exactly that trichotomy.

## Method

For `x` in the closed cell `T` the ordered normalized coordinates
`0 = y₀ ≤ y₁ ≤ ⋯ ≤ y_d ≤ y_{d+1} = 1` (`kuhnLevel`) give the barycentric
weights `kuhnWeight T x k = y_{d+1-k} − y_{d-k}` of the `d + 1` corners; these
are nonnegative, sum to `1`, and reproduce `x`.  That is
`closedCarrier_eq_convexHull_vertexSet`.  If a weight is *strictly* positive
then, in the second cell, every coordinate of the corresponding corner is
forced to the lower or the upper face of the second support cube; so the
corner is a corner of the second cell too.  Averaging the positive-weight
corners then places `x` in the convex hull of the common corners.

## References

* ABK26, (`e.simplex.def`, `V(△)`), (`e.SW.def`), (Step 1 of
  `l.piecewise.affine.approx`, the "adjacent coarse simplices share complete
  faces" sentence).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Normalized cube coordinates -/

/-- The coordinate of `x` in direction `i` normalized by the cube `Q`: it is
`0` on the lower face of `Q` and `1` on the upper face. -/
def normCoord (Q : TriadicCube d) (i : Fin d) (x : Vec d) : ℝ :=
  (cubeScaleFactor Q)⁻¹ * (x i - (Q.index i : ℝ) * cubeScaleFactor Q) + 1 / 2

private theorem normCoord_vertex (T : KuhnCell d) (k : Fin (d + 1)) (r : Fin d) :
    normCoord T.supportCube (T.order r) (T.vertex k) =
      if d ≤ r.val + k.val then 1 else 0 := by
  have hs : cubeScaleFactor T.supportCube ≠ 0 := (zpow_pos (by norm_num) _).ne'
  simp only [normCoord, KuhnCell.vertex, Equiv.symm_apply_apply]
  split_ifs <;> field_simp <;> ring

private theorem normCoord_nonneg_of_mem_closedBall (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q)) (i : Fin d) :
    0 ≤ normCoord Q i x := by
  rw [closedBall_cubeCenter_eq_pi_Icc] at hx
  have hxi := (hx i (Set.mem_univ i)).1
  have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  simp only [normCoord, cubeCenter, cubeRadius] at hxi ⊢
  have hdiv :
      -(1 / 2 : ℝ) ≤ (x i - (Q.index i : ℝ) * cubeScaleFactor Q) / cubeScaleFactor Q :=
    (le_div_iff₀ hs).2 (by nlinarith)
  rw [← div_eq_inv_mul]
  linarith

private theorem normCoord_le_one_of_mem_closedBall (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q)) (i : Fin d) :
    normCoord Q i x ≤ 1 := by
  rw [closedBall_cubeCenter_eq_pi_Icc] at hx
  have hxi := (hx i (Set.mem_univ i)).2
  have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  simp only [normCoord, cubeCenter, cubeRadius] at hxi ⊢
  have hdiv :
      (x i - (Q.index i : ℝ) * cubeScaleFactor Q) / cubeScaleFactor Q ≤ (1 / 2 : ℝ) :=
    (div_le_iff₀ hs).2 (by nlinarith)
  rw [← div_eq_inv_mul]
  linarith

private theorem normCoord_mono_of_localCoordinate_le (Q : TriadicCube d) (x : Vec d)
    {i j : Fin d}
    (hij : triadicLocalCoordinate Q x i ≤ triadicLocalCoordinate Q x j) :
    normCoord Q i x ≤ normCoord Q j x := by
  have hinv : (0 : ℝ) ≤ (cubeScaleFactor Q)⁻¹ :=
    (inv_pos.mpr (zpow_pos (by norm_num) _)).le
  simp only [normCoord, triadicLocalCoordinate] at hij ⊢
  linarith [mul_le_mul_of_nonneg_left hij hinv]

private theorem triadicLocalCoordinate_le_of_normCoord_le (Q : TriadicCube d) (x : Vec d)
    {i j : Fin d} (hij : normCoord Q i x ≤ normCoord Q j x) :
    triadicLocalCoordinate Q x i ≤ triadicLocalCoordinate Q x j := by
  have hinv : (0 : ℝ) < (cubeScaleFactor Q)⁻¹ := inv_pos.mpr (zpow_pos (by norm_num) _)
  simp only [normCoord, triadicLocalCoordinate] at hij ⊢
  have hmul :
      (cubeScaleFactor Q)⁻¹ * (x i - (Q.index i : ℝ) * cubeScaleFactor Q) ≤
        (cubeScaleFactor Q)⁻¹ * (x j - (Q.index j : ℝ) * cubeScaleFactor Q) := by
    linarith
  exact le_of_mul_le_mul_left hmul hinv

private theorem normCoord_inj (Q : TriadicCube d) {x y : Vec d} (i : Fin d)
    (hxy : normCoord Q i x = normCoord Q i y) : x i = y i := by
  have hinv : (cubeScaleFactor Q)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by norm_num))
  simp only [normCoord] at hxy
  have hmul :
      (cubeScaleFactor Q)⁻¹ * (x i - (Q.index i : ℝ) * cubeScaleFactor Q) =
        (cubeScaleFactor Q)⁻¹ * (y i - (Q.index i : ℝ) * cubeScaleFactor Q) := by
    linarith
  have := mul_left_cancel₀ hinv hmul
  linarith

/-! ## The barycentric coordinates of a closed Kuhn cell -/

/-- The ordered normalized coordinates of `x` in the cell `T`, with the
endpoint conventions `y₀ = 0` and `y_{d+1} = 1`. -/
def kuhnLevel (T : KuhnCell d) (x : Vec d) (j : ℕ) : ℝ :=
  if hj0 : j = 0 then 0
  else if hj : j ≤ d then normCoord T.supportCube (T.order ⟨j - 1, by omega⟩) x
  else 1

private theorem kuhnLevel_zero (T : KuhnCell d) (x : Vec d) : kuhnLevel T x 0 = 0 := by
  simp [kuhnLevel]

private theorem kuhnLevel_succ_fin (T : KuhnCell d) (x : Vec d) (r : Fin d) :
    kuhnLevel T x (r.val + 1) = normCoord T.supportCube (T.order r) x := by
  simp only [kuhnLevel]
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2

private theorem kuhnLevel_d_succ (T : KuhnCell d) (x : Vec d) :
    kuhnLevel T x (d + 1) = 1 := by
  simp [kuhnLevel]

private theorem kuhnLevel_of_pos_le (T : KuhnCell d) (x : Vec d) {j : ℕ}
    (hj0 : 0 < j) (hjd : j ≤ d) :
    kuhnLevel T x j = normCoord T.supportCube (T.order ⟨j - 1, by omega⟩) x := by
  simp [kuhnLevel, Nat.ne_of_gt hj0, hjd]

/-- The barycentric weight of the `k`-th corner of the Kuhn chain. -/
def kuhnWeight (T : KuhnCell d) (x : Vec d) (k : Fin (d + 1)) : ℝ :=
  kuhnLevel T x (d + 1 - k.val) - kuhnLevel T x (d - k.val)

private theorem kuhnLevel_mono_succ (T : KuhnCell d) {x : Vec d}
    (hx : x ∈ T.closedCarrier) {j : ℕ} (hj : j ≤ d) :
    kuhnLevel T x j ≤ kuhnLevel T x (j + 1) := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [kuhnLevel_zero]
    by_cases hd0 : d = 0
    · subst hd0
      simp [kuhnLevel]
    · rw [kuhnLevel_of_pos_le T x (by omega) (by omega)]
      exact normCoord_nonneg_of_mem_closedBall T.supportCube hx.1 (T.order ⟨0, by omega⟩)
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    by_cases hjd : j = d
    · subst hjd
      rw [kuhnLevel_d_succ, kuhnLevel_of_pos_le T x (by omega) le_rfl]
      exact normCoord_le_one_of_mem_closedBall T.supportCube hx.1
        (T.order ⟨j - 1, by omega⟩)
    · have hjlt : j < d := lt_of_le_of_ne hj hjd
      rw [kuhnLevel_of_pos_le T x hjpos hj, kuhnLevel_of_pos_le T x (by omega) (by omega)]
      exact normCoord_mono_of_localCoordinate_le T.supportCube x
        (hx.2 ⟨j - 1, by omega⟩ ⟨j, hjlt⟩ (by simp))

private theorem kuhnLevel_mono (T : KuhnCell d) {x : Vec d} (hx : x ∈ T.closedCarrier)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ d + 1) :
    kuhnLevel T x a ≤ kuhnLevel T x b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (kuhnLevel_mono_succ T hx (by omega))

private theorem kuhnWeight_nonneg (T : KuhnCell d) {x : Vec d}
    (hx : x ∈ T.closedCarrier) (k : Fin (d + 1)) : 0 ≤ kuhnWeight T x k := by
  have hmono := kuhnLevel_mono_succ T hx (j := d - k.val) (by omega)
  have heq : d + 1 - k.val = d - k.val + 1 := by omega
  simp only [kuhnWeight, heq]
  exact sub_nonneg.mpr hmono

private theorem kuhnWeight_rev (T : KuhnCell d) (x : Vec d) (j : Fin (d + 1)) :
    kuhnWeight T x (Fin.rev j) = kuhnLevel T x (j.val + 1) - kuhnLevel T x j.val := by
  simp only [kuhnWeight, Fin.val_rev]
  congr 2 <;> omega

private theorem sum_kuhnWeight (T : KuhnCell d) (x : Vec d) :
    ∑ k : Fin (d + 1), kuhnWeight T x k = 1 := by
  rw [← Equiv.sum_comp Fin.revPerm (kuhnWeight T x)]
  change (∑ j : Fin (d + 1), kuhnWeight T x (Fin.rev j)) = 1
  rw [Finset.sum_congr rfl fun j _ => kuhnWeight_rev T x j,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => kuhnLevel T x (j + 1) - kuhnLevel T x j),
    Finset.sum_range_sub, kuhnLevel_d_succ, kuhnLevel_zero]
  norm_num

private theorem sum_kuhnWeight_raised (T : KuhnCell d) (x : Vec d) (r : Fin d) :
    (∑ k : Fin (d + 1), if d ≤ r.val + k.val then kuhnWeight T x k else 0) =
      normCoord T.supportCube (T.order r) x := by
  rw [← Equiv.sum_comp Fin.revPerm
    (fun k : Fin (d + 1) => if d ≤ r.val + k.val then kuhnWeight T x k else 0)]
  change (∑ j : Fin (d + 1),
      if d ≤ r.val + (Fin.rev j).val then kuhnWeight T x (Fin.rev j) else 0) = _
  have hstep : ∀ j : Fin (d + 1),
      (if d ≤ r.val + (Fin.rev j).val then kuhnWeight T x (Fin.rev j) else 0) =
        if j.val ≤ r.val then kuhnLevel T x (j.val + 1) - kuhnLevel T x j.val else 0 := by
    intro j
    have hval : (Fin.rev j).val = d - j.val := by
      simp only [Fin.val_rev]
      omega
    have hjd : j.val ≤ d := Nat.lt_succ_iff.mp j.isLt
    have hiff : (d ≤ r.val + (d - j.val)) ↔ (j.val ≤ r.val) := by omega
    rw [hval, kuhnWeight_rev, if_congr hiff rfl rfl]
  rw [Finset.sum_congr rfl fun j _ => hstep j,
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => if j ≤ r.val then kuhnLevel T x (j + 1) - kuhnLevel T x j else 0)]
  have hfilter :
      (∑ j ∈ Finset.range (d + 1),
          if j ≤ r.val then kuhnLevel T x (j + 1) - kuhnLevel T x j else 0) =
        ∑ j ∈ Finset.range (r.val + 1), (kuhnLevel T x (j + 1) - kuhnLevel T x j) := by
    have hsub : Finset.range (r.val + 1) ⊆ Finset.range (d + 1) :=
      Finset.range_subset_range.2 (Nat.succ_le_succ r.isLt.le)
    calc
      _ = ∑ j ∈ Finset.range (r.val + 1),
            if j ≤ r.val then kuhnLevel T x (j + 1) - kuhnLevel T x j else 0 := by
          refine (Finset.sum_subset hsub ?_).symm
          intro j _ hjr
          simp only [Finset.mem_range] at hjr
          rw [ite_eq_right (by omega)]
      _ = _ := by
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_range] at hj
          rw [ite_eq_left (by omega)]
  rw [hfilter, Finset.sum_range_sub, kuhnLevel_succ_fin, kuhnLevel_zero]
  norm_num

private theorem weighted_vertex_eq (T : KuhnCell d) (x : Vec d) :
    ∑ k : Fin (d + 1), kuhnWeight T x k • T.vertex k = x := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, KuhnCell.vertex]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_kuhnWeight]
  have hrank : i = T.order (T.order.symm i) := (T.order.apply_symm_apply i).symm
  have hhalf :
      (∑ k : Fin (d + 1),
          kuhnWeight T x k *
            (if d ≤ (T.order.symm i).val + k.val then (1 / 2 : ℝ) else -(1 / 2 : ℝ))) =
        -(1 / 2 : ℝ) +
          ∑ k : Fin (d + 1),
            if d ≤ (T.order.symm i).val + k.val then kuhnWeight T x k else 0 := by
    calc
      _ = ∑ k : Fin (d + 1),
            (-(1 / 2 : ℝ) * kuhnWeight T x k +
              if d ≤ (T.order.symm i).val + k.val then kuhnWeight T x k else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
      _ = -(1 / 2 : ℝ) * (∑ k : Fin (d + 1), kuhnWeight T x k) +
            ∑ k : Fin (d + 1),
              if d ≤ (T.order.symm i).val + k.val then kuhnWeight T x k else 0 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [sum_kuhnWeight]; ring
  rw [hhalf]
  have hraised := sum_kuhnWeight_raised T x (T.order.symm i)
  rw [T.order.apply_symm_apply] at hraised
  rw [hraised]
  have hs : cubeScaleFactor T.supportCube ≠ 0 := (zpow_pos (by norm_num) _).ne'
  simp only [normCoord]
  rw [hrank]
  simp only [Equiv.apply_symm_apply]
  field_simp
  ring

/-- The one algebraic step of convexity: a convex combination preserves a
weak inequality between two shifted coordinates. -/
private theorem convex_le_step {a b p q p' q' ci cj : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hp : p - ci ≤ p' - cj) (hq : q - ci ≤ q' - cj) :
    a * p + b * q - ci ≤ a * p' + b * q' - cj := by
  have hsum : a * (p - ci) + b * (q - ci) ≤ a * (p' - cj) + b * (q' - cj) :=
    add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
  have hl : a * (p - ci) + b * (q - ci) = a * p + b * q - (a + b) * ci := by ring
  have hr : a * (p' - cj) + b * (q' - cj) = a * p' + b * q' - (a + b) * cj := by ring
  rw [hl, hr, hab, one_mul, one_mul] at hsum
  exact hsum

/-- **A closed Kuhn cell is the convex hull of its `d + 1` corners.**  This is one
of the two identities queued as a disclosure by `KuhnCell.vertex`
(`Whitney/KuhnCells.lean`); it is what makes the labelled corner list of
`KuhnCell.vertex` an honest stand-in for the printed "extreme points"
definition on the closed simplex. -/
theorem closedCarrier_eq_convexHull_vertexSet (T : KuhnCell d) :
    T.closedCarrier = convexHull ℝ T.vertexSet := by
  refine Set.Subset.antisymm (fun x hx => ?_) (convexHull_min ?_ ?_)
  · exact mem_convexHull_of_exists_fintype (kuhnWeight T x) T.vertex
      (kuhnWeight_nonneg T hx) (sum_kuhnWeight T x) (fun k => ⟨k, rfl⟩)
      (weighted_vertex_eq T x)
  · rintro _ ⟨k, rfl⟩
    exact T.vertex_mem_closedCarrier k
  · intro x hx y hy a b ha hb hab
    refine ⟨convex_closedBall (cubeCenter T.supportCube) (cubeRadius T.supportCube)
      hx.1 hy.1 ha hb hab, ?_⟩
    intro i j hij
    have hxij := hx.2 i j hij
    have hyij := hy.2 i j hij
    simp only [triadicLocalCoordinate, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at hxij hyij ⊢
    exact convex_le_step ha hb hab hxij hyij

/-- Closed Kuhn cells are closed sets. -/
theorem isClosed_closedCarrier (T : KuhnCell d) : IsClosed T.closedCarrier := by
  rw [closedCarrier_eq_convexHull_vertexSet T]
  exact (Set.finite_range T.vertex).isClosed_convexHull (𝕜 := ℝ)

/-! ## Strictness at a positive-weight corner -/

private theorem kuhnWeight_pos_gap (T : KuhnCell d) {x : Vec d} {k : Fin (d + 1)}
    (hk : 0 < kuhnWeight T x k) :
    kuhnLevel T x (d - k.val) < kuhnLevel T x (d - k.val + 1) := by
  have heq : d + 1 - k.val = d - k.val + 1 := by omega
  exact sub_pos.mp (by simpa only [kuhnWeight, heq] using hk)

private theorem normCoord_pos_of_kuhnWeight_pos_of_raised (T : KuhnCell d) {x : Vec d}
    (hx : x ∈ T.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) (i : Fin d)
    (hi : d ≤ (T.order.symm i).val + k.val) :
    0 < normCoord T.supportCube i x := by
  have hgap := kuhnWeight_pos_gap T hk
  have hzero : 0 ≤ kuhnLevel T x (d - k.val) := by
    simpa only [kuhnLevel_zero] using
      kuhnLevel_mono T hx (a := 0) (b := d - k.val) (Nat.zero_le _) (by omega)
  have htail : kuhnLevel T x (d - k.val + 1) ≤ kuhnLevel T x ((T.order.symm i).val + 1) :=
    kuhnLevel_mono T hx (by omega) (by omega)
  have hr : kuhnLevel T x ((T.order.symm i).val + 1) = normCoord T.supportCube i x := by
    rw [kuhnLevel_succ_fin, T.order.apply_symm_apply]
  rw [← hr]
  exact lt_of_lt_of_le (lt_of_le_of_lt hzero hgap) htail

private theorem normCoord_lt_one_of_kuhnWeight_pos_of_not_raised (T : KuhnCell d)
    {x : Vec d} (hx : x ∈ T.closedCarrier) {k : Fin (d + 1)}
    (hk : 0 < kuhnWeight T x k) (i : Fin d)
    (hi : ¬d ≤ (T.order.symm i).val + k.val) :
    normCoord T.supportCube i x < 1 := by
  have hgap := kuhnWeight_pos_gap T hk
  have hhead : kuhnLevel T x ((T.order.symm i).val + 1) ≤ kuhnLevel T x (d - k.val) :=
    kuhnLevel_mono T hx (by omega) (by omega)
  have hone : kuhnLevel T x (d - k.val + 1) ≤ 1 := by
    simpa only [kuhnLevel_d_succ] using
      kuhnLevel_mono T hx (a := d - k.val + 1) (b := d + 1) (by omega) le_rfl
  have hr : kuhnLevel T x ((T.order.symm i).val + 1) = normCoord T.supportCube i x := by
    rw [kuhnLevel_succ_fin, T.order.apply_symm_apply]
  rw [← hr]
  exact lt_of_le_of_lt hhead (lt_of_lt_of_le hgap hone)

private theorem normCoord_lt_of_kuhnWeight_pos_of_cut (T : KuhnCell d) {x : Vec d}
    (hx : x ∈ T.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k)
    {i j : Fin d} (hi : ¬d ≤ (T.order.symm i).val + k.val)
    (hj : d ≤ (T.order.symm j).val + k.val) :
    normCoord T.supportCube i x < normCoord T.supportCube j x := by
  have hleft : kuhnLevel T x ((T.order.symm i).val + 1) ≤ kuhnLevel T x (d - k.val) :=
    kuhnLevel_mono T hx (by omega) (by omega)
  have hright : kuhnLevel T x (d - k.val + 1) ≤ kuhnLevel T x ((T.order.symm j).val + 1) :=
    kuhnLevel_mono T hx (by omega) (by omega)
  have hgap := kuhnWeight_pos_gap T hk
  have hri : kuhnLevel T x ((T.order.symm i).val + 1) = normCoord T.supportCube i x := by
    rw [kuhnLevel_succ_fin, T.order.apply_symm_apply]
  have hrj : kuhnLevel T x ((T.order.symm j).val + 1) = normCoord T.supportCube j x := by
    rw [kuhnLevel_succ_fin, T.order.apply_symm_apply]
  rw [← hri, ← hrj]
  exact hleft.trans_lt (hgap.trans_le hright)

/-! ## Equal-scale grid geometry -/

private theorem supportIndex_trichotomy {Q R : TriadicCube d} (hscale : Q.scale = R.scale)
    {x : Vec d} (hxQ : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q))
    (hxR : x ∈ Metric.closedBall (cubeCenter R) (cubeRadius R)) (i : Fin d) :
    R.index i = Q.index i - 1 ∨ R.index i = Q.index i ∨ R.index i = Q.index i + 1 := by
  rw [closedBall_cubeCenter_eq_pi_Icc] at hxQ hxR
  have hQi := hxQ i (Set.mem_univ i)
  have hRi := hxR i (Set.mem_univ i)
  have hfac : cubeScaleFactor R = cubeScaleFactor Q := by
    simp only [cubeScaleFactor, hscale]
  have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  simp only [Set.mem_Icc, cubeCenter, cubeRadius] at hQi hRi
  rw [hfac] at hRi
  have hQRmul :
      (((Q.index i - R.index i : ℤ) : ℝ)) * cubeScaleFactor Q ≤ 1 * cubeScaleFactor Q := by
    push_cast
    nlinarith
  have hRQmul :
      (((R.index i - Q.index i : ℤ) : ℝ)) * cubeScaleFactor Q ≤ 1 * cubeScaleFactor Q := by
    push_cast
    nlinarith
  have hQR : Q.index i - R.index i ≤ 1 := by
    exact_mod_cast le_of_mul_le_mul_right hQRmul hs
  have hRQ : R.index i - Q.index i ≤ 1 := by
    exact_mod_cast le_of_mul_le_mul_right hRQmul hs
  omega

private theorem normCoord_eq_zero_of_left_neighbor {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) {x : Vec d}
    (hxQ : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q))
    (hxR : x ∈ Metric.closedBall (cubeCenter R) (cubeRadius R)) (i : Fin d)
    (hindex : R.index i = Q.index i - 1) : normCoord Q i x = 0 := by
  rw [closedBall_cubeCenter_eq_pi_Icc] at hxQ hxR
  have hQi := hxQ i (Set.mem_univ i)
  have hRi := hxR i (Set.mem_univ i)
  have hfac : cubeScaleFactor R = cubeScaleFactor Q := by
    simp only [cubeScaleFactor, hscale]
  have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  simp only [Set.mem_Icc, cubeCenter, cubeRadius] at hQi hRi
  rw [hfac, hindex] at hRi
  push_cast at hRi
  have hxeq : x i = ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q := by nlinarith
  simp only [normCoord, hxeq]
  field_simp
  ring

private theorem normCoord_eq_one_of_right_neighbor {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) {x : Vec d}
    (hxQ : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q))
    (hxR : x ∈ Metric.closedBall (cubeCenter R) (cubeRadius R)) (i : Fin d)
    (hindex : R.index i = Q.index i + 1) : normCoord Q i x = 1 := by
  rw [closedBall_cubeCenter_eq_pi_Icc] at hxQ hxR
  have hQi := hxQ i (Set.mem_univ i)
  have hRi := hxR i (Set.mem_univ i)
  have hfac : cubeScaleFactor R = cubeScaleFactor Q := by
    simp only [cubeScaleFactor, hscale]
  have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
  simp only [Set.mem_Icc, cubeCenter, cubeRadius] at hQi hRi
  rw [hfac, hindex] at hRi
  push_cast at hRi
  have hxeq : x i = ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by nlinarith
  simp only [normCoord, hxeq]
  field_simp
  ring

private theorem normCoord_eq_of_scale_index_eq {Q R : TriadicCube d}
    (hscale : Q.scale = R.scale) {x : Vec d} (i : Fin d) (hindex : R.index i = Q.index i) :
    normCoord R i x = normCoord Q i x := by
  have hfac : cubeScaleFactor R = cubeScaleFactor Q := by
    simp only [cubeScaleFactor, hscale]
  simp only [normCoord, hfac, hindex]

private theorem not_raised_of_left_neighbor (T U : KuhnCell d) {x : Vec d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hxT : x ∈ T.closedCarrier)
    (hxU : x ∈ U.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) (i : Fin d)
    (hindex : U.supportCube.index i = T.supportCube.index i - 1) :
    ¬d ≤ (T.order.symm i).val + k.val := by
  have hzero := normCoord_eq_zero_of_left_neighbor hscale hxT.1 hxU.1 i hindex
  intro hraised
  have hpos := normCoord_pos_of_kuhnWeight_pos_of_raised T hxT hk i hraised
  linarith

private theorem raised_of_right_neighbor (T U : KuhnCell d) {x : Vec d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hxT : x ∈ T.closedCarrier)
    (hxU : x ∈ U.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) (i : Fin d)
    (hindex : U.supportCube.index i = T.supportCube.index i + 1) :
    d ≤ (T.order.symm i).val + k.val := by
  have hone := normCoord_eq_one_of_right_neighbor hscale hxT.1 hxU.1 i hindex
  by_contra hnraised
  have hlt := normCoord_lt_one_of_kuhnWeight_pos_of_not_raised T hxT hk i hnraised
  linarith

/-! ## A positive-weight corner of the first cell is a corner of the second -/

private theorem vertex_mem_second_closedBall (T U : KuhnCell d) {x : Vec d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hxT : x ∈ T.closedCarrier)
    (hxU : x ∈ U.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) :
    T.vertex k ∈
      Metric.closedBall (cubeCenter U.supportCube) (cubeRadius U.supportCube) := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hfac : cubeScaleFactor U.supportCube = cubeScaleFactor T.supportCube := by
    simp only [cubeScaleFactor, hscale]
  rw [closedBall_cubeCenter_eq_pi_Icc]
  intro i _
  rcases supportIndex_trichotomy hscale hxT.1 hxU.1 i with hleft | hsame | hright
  · have hnraised := not_raised_of_left_neighbor T U hscale hxT hxU hk i hleft
    simp only [KuhnCell.vertex, hnraised, ite_false, cubeCenter, cubeRadius, hfac, hleft]
    push_cast
    constructor <;> nlinarith
  · simp only [KuhnCell.vertex, cubeCenter, cubeRadius, hfac, hsame]
    split_ifs <;> constructor <;> nlinarith
  · have hraised := raised_of_right_neighbor T U hscale hxT hxU hk i hright
    simp only [KuhnCell.vertex, hraised, ite_true, cubeCenter, cubeRadius, hfac, hright]
    push_cast
    constructor <;> nlinarith

private theorem normCoord_vertex_eq_one_of_left_of_not_raised (T U : KuhnCell d)
    (hscale : T.supportCube.scale = U.supportCube.scale) (k : Fin (d + 1)) (i : Fin d)
    (hindex : U.supportCube.index i = T.supportCube.index i - 1)
    (hi : ¬d ≤ (T.order.symm i).val + k.val) :
    normCoord U.supportCube i (T.vertex k) = 1 := by
  have hfac : cubeScaleFactor U.supportCube = cubeScaleFactor T.supportCube := by
    simp only [cubeScaleFactor, hscale]
  have hs : cubeScaleFactor T.supportCube ≠ 0 := (zpow_pos (by norm_num) _).ne'
  simp only [normCoord, KuhnCell.vertex, hi, ite_false, hfac, hindex]
  push_cast
  field_simp
  ring

private theorem normCoord_vertex_eq_zero_of_same_of_not_raised (T U : KuhnCell d)
    (hscale : T.supportCube.scale = U.supportCube.scale) (k : Fin (d + 1)) (i : Fin d)
    (hindex : U.supportCube.index i = T.supportCube.index i)
    (hi : ¬d ≤ (T.order.symm i).val + k.val) :
    normCoord U.supportCube i (T.vertex k) = 0 := by
  have hfac : cubeScaleFactor U.supportCube = cubeScaleFactor T.supportCube := by
    simp only [cubeScaleFactor, hscale]
  have hs : cubeScaleFactor T.supportCube ≠ 0 := (zpow_pos (by norm_num) _).ne'
  simp only [normCoord, KuhnCell.vertex, hi, ite_false, hfac, hindex]
  field_simp
  ring

private theorem normCoord_vertex_eq_one_of_same_of_raised (T U : KuhnCell d)
    (hscale : T.supportCube.scale = U.supportCube.scale) (k : Fin (d + 1)) (i : Fin d)
    (hindex : U.supportCube.index i = T.supportCube.index i)
    (hi : d ≤ (T.order.symm i).val + k.val) :
    normCoord U.supportCube i (T.vertex k) = 1 := by
  have hfac : cubeScaleFactor U.supportCube = cubeScaleFactor T.supportCube := by
    simp only [cubeScaleFactor, hscale]
  have hs : cubeScaleFactor T.supportCube ≠ 0 := (zpow_pos (by norm_num) _).ne'
  simp only [normCoord, KuhnCell.vertex, hi, ite_true, hfac, hindex]
  field_simp
  ring

private theorem normCoord_vertex_eq_zero_of_right_of_raised (T U : KuhnCell d)
    (hscale : T.supportCube.scale = U.supportCube.scale) (k : Fin (d + 1)) (i : Fin d)
    (hindex : U.supportCube.index i = T.supportCube.index i + 1)
    (hi : d ≤ (T.order.symm i).val + k.val) :
    normCoord U.supportCube i (T.vertex k) = 0 := by
  have hfac : cubeScaleFactor U.supportCube = cubeScaleFactor T.supportCube := by
    simp only [cubeScaleFactor, hscale]
  have hs : cubeScaleFactor T.supportCube ≠ 0 := (zpow_pos (by norm_num) _).ne'
  simp only [normCoord, KuhnCell.vertex, hi, ite_true, hfac, hindex]
  push_cast
  field_simp
  ring

private theorem normCoord_vertex_eq_zero_or_one (T U : KuhnCell d) {x : Vec d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hxT : x ∈ T.closedCarrier)
    (hxU : x ∈ U.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) (i : Fin d) :
    normCoord U.supportCube i (T.vertex k) = 0 ∨
      normCoord U.supportCube i (T.vertex k) = 1 := by
  rcases supportIndex_trichotomy hscale hxT.1 hxU.1 i with hleft | hsame | hright
  · exact Or.inr (normCoord_vertex_eq_one_of_left_of_not_raised T U hscale k i hleft
      (not_raised_of_left_neighbor T U hscale hxT hxU hk i hleft))
  · by_cases hraised : d ≤ (T.order.symm i).val + k.val
    · exact Or.inr (normCoord_vertex_eq_one_of_same_of_raised T U hscale k i hsame hraised)
    · exact Or.inl
        (normCoord_vertex_eq_zero_of_same_of_not_raised T U hscale k i hsame hraised)
  · exact Or.inl (normCoord_vertex_eq_zero_of_right_of_raised T U hscale k i hright
      (raised_of_right_neighbor T U hscale hxT hxU hk i hright))

private theorem vertex_mem_second_closedCarrier (T U : KuhnCell d) {x : Vec d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hxT : x ∈ T.closedCarrier)
    (hxU : x ∈ U.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) :
    T.vertex k ∈ U.closedCarrier := by
  have hvball := vertex_mem_second_closedBall T U hscale hxT hxU hk
  refine ⟨hvball, ?_⟩
  intro a b hab
  have hUx :
      normCoord U.supportCube (U.order a) x ≤ normCoord U.supportCube (U.order b) x :=
    normCoord_mono_of_localCoordinate_le U.supportCube x (hxU.2 a b hab)
  have hva0 : 0 ≤ normCoord U.supportCube (U.order a) (T.vertex k) :=
    normCoord_nonneg_of_mem_closedBall U.supportCube hvball (U.order a)
  have hvb0 : 0 ≤ normCoord U.supportCube (U.order b) (T.vertex k) :=
    normCoord_nonneg_of_mem_closedBall U.supportCube hvball (U.order b)
  have hva1 : normCoord U.supportCube (U.order a) (T.vertex k) ≤ 1 :=
    normCoord_le_one_of_mem_closedBall U.supportCube hvball (U.order a)
  refine triadicLocalCoordinate_le_of_normCoord_le U.supportCube _ ?_
  rcases supportIndex_trichotomy hscale hxT.1 hxU.1 (U.order a) with haL | haS | haR
  · have haNot := not_raised_of_left_neighbor T U hscale hxT hxU hk (U.order a) haL
    have hva : normCoord U.supportCube (U.order a) (T.vertex k) = 1 :=
      normCoord_vertex_eq_one_of_left_of_not_raised T U hscale k (U.order a) haL haNot
    rcases supportIndex_trichotomy hscale hxT.1 hxU.1 (U.order b) with hbL | hbS | hbR
    · rw [hva, normCoord_vertex_eq_one_of_left_of_not_raised T U hscale k (U.order b) hbL
        (not_raised_of_left_neighbor T U hscale hxT hxU hk (U.order b) hbL)]
    · by_cases hbRaised : d ≤ (T.order.symm (U.order b)).val + k.val
      · rw [hva,
          normCoord_vertex_eq_one_of_same_of_raised T U hscale k (U.order b) hbS hbRaised]
      · have hUxa : normCoord U.supportCube (U.order a) x = 1 :=
          normCoord_eq_one_of_right_neighbor (Q := U.supportCube) (R := T.supportCube)
            hscale.symm hxU.1 hxT.1 (U.order a) (by omega)
        have hUxb :
            normCoord U.supportCube (U.order b) x = normCoord T.supportCube (U.order b) x :=
          normCoord_eq_of_scale_index_eq hscale (U.order b) hbS
        have hlt :=
          normCoord_lt_one_of_kuhnWeight_pos_of_not_raised T hxT hk (U.order b) hbRaised
        exact absurd hUx (by rw [hUxa, hUxb]; linarith)
    · have hUxa : normCoord U.supportCube (U.order a) x = 1 :=
        normCoord_eq_one_of_right_neighbor (Q := U.supportCube) (R := T.supportCube)
          hscale.symm hxU.1 hxT.1 (U.order a) (by omega)
      have hUxb : normCoord U.supportCube (U.order b) x = 0 :=
        normCoord_eq_zero_of_left_neighbor (Q := U.supportCube) (R := T.supportCube)
          hscale.symm hxU.1 hxT.1 (U.order b) (by omega)
      exact absurd hUx (by rw [hUxa, hUxb]; norm_num)
  · rcases supportIndex_trichotomy hscale hxT.1 hxU.1 (U.order b) with hbL | hbS | hbR
    · rw [normCoord_vertex_eq_one_of_left_of_not_raised T U hscale k (U.order b) hbL
        (not_raised_of_left_neighbor T U hscale hxT hxU hk (U.order b) hbL)]
      exact hva1
    · by_cases haRaised : d ≤ (T.order.symm (U.order a)).val + k.val
      · by_cases hbRaised : d ≤ (T.order.symm (U.order b)).val + k.val
        · rw [normCoord_vertex_eq_one_of_same_of_raised T U hscale k (U.order a) haS
              haRaised,
            normCoord_vertex_eq_one_of_same_of_raised T U hscale k (U.order b) hbS hbRaised]
        · have hUa :
              normCoord U.supportCube (U.order a) x =
                normCoord T.supportCube (U.order a) x :=
            normCoord_eq_of_scale_index_eq hscale (U.order a) haS
          have hUb :
              normCoord U.supportCube (U.order b) x =
                normCoord T.supportCube (U.order b) x :=
            normCoord_eq_of_scale_index_eq hscale (U.order b) hbS
          have hstrict := normCoord_lt_of_kuhnWeight_pos_of_cut T hxT hk hbRaised haRaised
          exact absurd hUx (by rw [hUa, hUb]; linarith)
      · rw [normCoord_vertex_eq_zero_of_same_of_not_raised T U hscale k (U.order a) haS
          haRaised]
        exact hvb0
    · have hbRaised := raised_of_right_neighbor T U hscale hxT hxU hk (U.order b) hbR
      have hvb : normCoord U.supportCube (U.order b) (T.vertex k) = 0 :=
        normCoord_vertex_eq_zero_of_right_of_raised T U hscale k (U.order b) hbR hbRaised
      by_cases haRaised : d ≤ (T.order.symm (U.order a)).val + k.val
      · have hUa :
            normCoord U.supportCube (U.order a) x = normCoord T.supportCube (U.order a) x :=
          normCoord_eq_of_scale_index_eq hscale (U.order a) haS
        have hUxb : normCoord U.supportCube (U.order b) x = 0 :=
          normCoord_eq_zero_of_left_neighbor (Q := U.supportCube) (R := T.supportCube)
            hscale.symm hxU.1 hxT.1 (U.order b) (by omega)
        have hpos :=
          normCoord_pos_of_kuhnWeight_pos_of_raised T hxT hk (U.order a) haRaised
        exact absurd hUx (by rw [hUa, hUxb]; linarith)
      · rw [normCoord_vertex_eq_zero_of_same_of_not_raised T U hscale k (U.order a) haS
          haRaised, hvb]
  · have haRaised := raised_of_right_neighbor T U hscale hxT hxU hk (U.order a) haR
    rw [normCoord_vertex_eq_zero_of_right_of_raised T U hscale k (U.order a) haR haRaised]
    exact hvb0

private theorem vertex_mem_second_vertexSet (T U : KuhnCell d) {x : Vec d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hxT : x ∈ T.closedCarrier)
    (hxU : x ∈ U.closedCarrier) {k : Fin (d + 1)} (hk : 0 < kuhnWeight T x k) :
    T.vertex k ∈ U.vertexSet := by
  have hvU := vertex_mem_second_closedCarrier T U hscale hxT hxU hk
  have hsumpos : 0 < ∑ l : Fin (d + 1), kuhnWeight U (T.vertex k) l := by
    rw [sum_kuhnWeight]
    norm_num
  obtain ⟨l, -, hl⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := (Finset.univ : Finset (Fin (d + 1))))
      (fun l _ => kuhnWeight_nonneg U hvU l)).mp hsumpos
  refine ⟨l, ?_⟩
  funext i
  refine normCoord_inj U.supportCube i ?_
  by_cases hi : d ≤ (U.order.symm i).val + l.val
  · have hpos := normCoord_pos_of_kuhnWeight_pos_of_raised U hvU hl i hi
    have huv := normCoord_vertex U l (U.order.symm i)
    rw [U.order.apply_symm_apply, ite_eq_left hi] at huv
    rcases normCoord_vertex_eq_zero_or_one T U hscale hxT hxU hk i with hzero | hone
    · exact absurd hpos (by rw [hzero]; norm_num)
    · rw [hone, huv]
  · have hlt := normCoord_lt_one_of_kuhnWeight_pos_of_not_raised U hvU hl i hi
    have huv := normCoord_vertex U l (U.order.symm i)
    rw [U.order.apply_symm_apply, ite_eq_right hi] at huv
    rcases normCoord_vertex_eq_zero_or_one T U hscale hxT hxU hk i with hzero | hone
    · rw [hzero, huv]
    · exact absurd hlt (by rw [hone]; norm_num)

/-! ## The face-alignment lemma and the gluing step -/

/-- The closed geometric face shared by two Kuhn cells: the convex hull of
exactly their common corners.  It is empty when they share no corner. -/
def commonClosedFace (T U : KuhnCell d) : Set (Vec d) :=
  convexHull ℝ (T.vertexSet ∩ U.vertexSet)

theorem commonClosedFace_subset_affineSpan (T U : KuhnCell d) :
    commonClosedFace T U ⊆ affineSpan ℝ (T.vertexSet ∩ U.vertexSet) :=
  convexHull_subset_affineSpan _

/-- **The equal-scale face-alignment lemma** of the Correction paragraph (used;
pin corrected).  Two Kuhn cells of the *same* scale on the globally aligned
triadic grid meet only inside the convex hull of the corners they share: their
closed carriers overlap in a common face.

The hypothesis is only that the two support cubes have the same scale, i.e.
belong to one aligned grid. -/
theorem closedCarrier_inter_subset_commonClosedFace (T U : KuhnCell d)
    (hscale : T.supportCube.scale = U.supportCube.scale) :
    T.closedCarrier ∩ U.closedCarrier ⊆ commonClosedFace T U := by
  classical
  intro x hx
  set positiveVertices : Finset (Fin (d + 1)) :=
    Finset.univ.filter fun k => 0 < kuhnWeight T x k with hpv
  have hw0 : ∀ k : Fin (d + 1), 0 ≤ kuhnWeight T x k := kuhnWeight_nonneg T hx.1
  have hzero : ∀ k : Fin (d + 1), k ∉ positiveVertices → kuhnWeight T x k = 0 := by
    intro k hk
    have hnpos : ¬0 < kuhnWeight T x k := by
      intro hpos
      exact hk (by simp [hpv, hpos])
    exact le_antisymm (le_of_not_gt hnpos) (hw0 k)
  have hsum : ∑ k ∈ positiveVertices, kuhnWeight T x k = 1 := by
    calc
      _ = ∑ k : Fin (d + 1), kuhnWeight T x k := by
          refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => hzero k hk
      _ = 1 := sum_kuhnWeight T x
  have hweighted : ∑ k ∈ positiveVertices, kuhnWeight T x k • T.vertex k = x := by
    calc
      _ = ∑ k : Fin (d + 1), kuhnWeight T x k • T.vertex k := by
          refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
          rw [hzero k hk, zero_smul]
      _ = x := weighted_vertex_eq T x
  rw [commonClosedFace, ← hweighted,
    ← positiveVertices.centerMass_eq_of_sum_1 T.vertex hsum]
  refine positiveVertices.centerMass_mem_convexHull (fun k _ => hw0 k)
    (by rw [hsum]; norm_num) fun k hk => ⟨⟨k, rfl⟩, ?_⟩
  exact vertex_mem_second_vertexSet T U hscale hx.1 hx.2
    (by simpa only [hpv, Finset.mem_filter, Finset.mem_univ, true_and] using hk)

/-- **The gluing step**, in bundled form: two equal-scale Kuhn cells interpolating
one *global* vertex datum define the same affine value at every point of the
intersection of their closed carriers.  This is the manuscript's "since
adjacent coarse simplices share complete faces, this extension is well-defined
and continuous" (; mesh-interior half —), with the face-sharing supplied by
`closedCarrier_inter_subset_commonClosedFace` rather than assumed. -/
theorem kuhnInterpAffine_eqOn_closedCarrier_inter (T U : KuhnCell d) (g : Vec d → ℝ)
    (hscale : T.supportCube.scale = U.supportCube.scale) :
    Set.EqOn (kuhnInterpAffine T g) (kuhnInterpAffine U g)
      (T.closedCarrier ∩ U.closedCarrier) := fun _ hx =>
  kuhnInterpAffine_eqOn_affineSpan_inter_vertexSet T U g
    (commonClosedFace_subset_affineSpan T U
      (closedCarrier_inter_subset_commonClosedFace T U hscale hx))

/-- **The gluing step**, in the unbundled form the piecewise-affine competitor
uses: the two cell interpolants of one global vertex datum agree on the
overlap of their closed carriers. -/
theorem kuhnInterp_eqOn_closedCarrier_inter (T U : KuhnCell d) (g : Vec d → ℝ)
    (hscale : T.supportCube.scale = U.supportCube.scale) :
    Set.EqOn (kuhnInterp T g) (kuhnInterp U g)
      (T.closedCarrier ∩ U.closedCarrier) := fun _ hx =>
  kuhnInterpAffine_eqOn_closedCarrier_inter T U g hscale hx

end

end Algsuperdiff.Section3.Provider.Affine
