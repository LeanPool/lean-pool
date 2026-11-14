/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.KuhnCells
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# KuhnInterpolation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Kuhn-cell affine interpolant

This module provides a proved local *carrier-level implementation* for ABK26's
`l.piecewise.affine.approx`: the operation "assign a value at each vertex, then
extend affinely to the simplex" of the lemma's Step 1, together with the Step-2
gradient computation.

On a Kuhn cell `T` -- one triadic simplex of `e.simplex.def`, with the `d + 1`
vertices `V(△)` represented by `KuhnCell.vertex` -- the affine function
agreeing with a datum `g : Vec d → ℝ` at those vertices is unique, and its
gradient is the vector of Kuhn-edge difference quotients.  This file defines
that gradient (`kuhnSlope`) and that affine function (`kuhnInterp`) and proves
the characterizing A:

* `kuhnInterp_vertex` -- the interpolant agrees with `g` at every vertex;
* `kuhnInterp_sub` / `kuhnInterp_apply` -- the interpolant is affine on all of
  `Vec d`, with constant gradient `kuhnSlope T g`;
* `kuhnInterp_congr` -- the interpolant depends on the vertex datum only
  through its `d + 1` vertex values.  Together with `kuhnInterp_vertex` this
  pins `kuhnInterp` as the affine extension of vertex data.  A uniqueness
  statement against an arbitrary competitor in the coordinate presentation
  `c + v·x` is not among the statements below: the manuscript's "affine on the
  simplex" reading would additionally need `affineSpan ℝ T.vertexSet = ⊤`,
  which the edge chain `v_{d-r} - v_{d-r-1} = 3^{scale}·e_{π(r)}` supplies but
  which is not recorded here;
* `kuhnSlope_apply` / `kuhnSlope_order` -- the gradient formula in terms of
  vertex differences, `∂_{π(r)} = (g(v_{d-r}) − g(v_{d-r-1})) / 3^{scale}`;
* `vertex_kuhnEdge_sub_apply` -- the Kuhn edge chain: consecutive vertices
  differ by one cube side in one coordinate direction, the chain running from
  the lower to the upper corner of the support cube;
* `kuhnInterpAffine` -- the same function bundled as a `Vec d →ᵃ[ℝ] ℝ`, whose
  only purpose is `kuhnInterpAffine_eqOn_affineSpan_inter_vertexSet`: two cells
  interpolating one global vertex datum agree on the affine span of the
  vertices they share.  That is the well-definedness instrument for a global
  interpolant assembled cell by cell, and it assumes no face-to-face property
  of `SW(□_m)`.

## What of the manuscript this file already carries

* `e.hat.linear.linearity` at the cell level: `kuhnSlope_add`,
  `kuhnSlope_smul`, `kuhnInterp_add`.
* Clause 1 of `e.hat.linear.properties`  at the cell level:
  `kuhnSlope_eq_zero_of_vertex_const`, `kuhnSlope_eq_zero_of_eqOn_vertexSet` --
  a competitor whose vertex values are all equal has vanishing gradient on the
  cell.  This is the manuscript's "inside `𝒞_j`, all coarse vertices receive
  the same value `⨍_{𝒞_j} ℓ_e`, so `∇ℓ̂_e = 0` there".
* Clause 3 of `e.hat.linear.properties` ((clause 3; the cases-end line asserts
  nothing —, format)) at the cell level: `kuhnSlope_linearFn`,
  `kuhnInterp_linearFn`, `kuhnSlope_eq_of_eqOn_vertexSet`,
  `kuhnInterp_eq_linearFn_of_eqOn_vertexSet` -- if the vertex datum is `ℓ_p` on
  `V(△)` then the interpolant is `ℓ_p` and its gradient is `p`.
* Step 2's gradient display: `abs_kuhnSlope_sub_le_of_vertex_oscillation`,
  `vecNormSq_kuhnSlope_sub_le_of_vertex_oscillation` and its pointwise-vertex
  forms `vecNormSq_kuhnSlope_sub_le_of_vertex_bound`,
  `vecNormSq_kuhnSlope_sub_le_of_vertexSet_bound` are `|∇ℓ̂_e − e|_{L^∞(𝔰)} ≤
  (C / diam 𝔰) · max_{v,w ∈ V(𝔰)} |(ℓ̂_e − ℓ_e)(v) − (ℓ̂_e − ℓ_e)(w)|` with the
  explicit constants of this implementation: the per-coordinate constant is `1`
  against the cube side `3^{scale}`, and the Euclidean form carries `√d`.

## Scope: what this file does NOT do

This file is the cell-level carrier only.  It does **not** construct the global
`ℓ̂_p` of `l.piecewise.affine.approx`, does not mention bad cubes, components,
neighborhoods, layers, or the collar, and asserts nothing about how cells of
different scales meet.  In particular:

* (the neighborhood `𝒩(𝒞_j)` spans three layers, not two) (neighborhoods of
  distinct components are **not** disjoint): no layer window and no
  disjointness statement occurs here.
* What it provides is the per-cell input to either reading -- the exact
  gradient of one affine piece in terms of its own vertex data -- so it is
  neutral with respect to the layer count and the overlap.  *: no face-to-face
  or simplicial-complex property of `SW(□_m)` is used or asserted.
  `kuhnInterp_eqOn_inter_vertexSet` compares two cells only at points that are
  vertices of both.
* : no slope-square or collar constant enters.
* (ruled): not consumed -- no connectivity or cluster geometry appears.

## References

* ABK26, (`l.piecewise.affine.approx` with `e.hat.linear.properties`), (its
  proof, Steps 1 and 2), (`e.simplex.def`, `V(△)`), (`ℓ_e(x) = e · x`),
  (`e.hat.linear.linearity`).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The linear function `ℓ_p` -/

/-- **ABK26 `ℓ_p`**: "we let `ℓ_e(x) = e · x` denote the linear function with slope
`e ∈ ℝ^d`". -/
def linearFn (p : Vec d) : Vec d → ℝ := fun x => vecDot p x

@[simp] theorem linearFn_apply (p x : Vec d) : linearFn p x = vecDot p x := rfl

/-! ## Elementary `vecDot` algebra -/

private theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [vecDot, vecDot, vecDot, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply]
  ring

private theorem vecDot_add_left' (x y z : Vec d) :
    vecDot (x + y) z = vecDot x z + vecDot y z := by
  rw [vecDot, vecDot, vecDot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

private theorem vecDot_add_right' (x y z : Vec d) :
    vecDot x (y + z) = vecDot x y + vecDot x z := by
  rw [vecDot, vecDot, vecDot, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply]
  ring

private theorem vecDot_smul_right' (x : Vec d) (c : ℝ) (y : Vec d) :
    vecDot x (c • y) = c * vecDot x y := by
  rw [vecDot, vecDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The Kuhn edge chain -/

/-- The upper endpoint of the `r`-th edge of the Kuhn vertex chain of a cell:
the vertex `v_{d-r}` of `KuhnCell.vertex`. -/
def kuhnEdgeVertex (r : Fin d) : Fin (d + 1) := ⟨d - r.val, by omega⟩

/-- The lower endpoint of the `r`-th edge of the Kuhn vertex chain of a cell:
the vertex `v_{d-r-1}` of `KuhnCell.vertex`. -/
def kuhnEdgePrevVertex (r : Fin d) : Fin (d + 1) := ⟨d - r.val - 1, by omega⟩

/-- **The Kuhn edge chain.**  Consecutive vertices of a Kuhn cell differ in
exactly one coordinate, by exactly one cube side: the `r`-th edge points along
the coordinate direction `T.order r`.  This is the geometric fact that makes
the vertex list of `KuhnCell.vertex` a monotone lattice path from the lower to
the upper corner of the support cube. -/
theorem vertex_kuhnEdge_sub_apply (T : KuhnCell d) (r j : Fin d) :
    T.vertex (kuhnEdgeVertex r) j - T.vertex (kuhnEdgePrevVertex r) j =
      if j = T.order r then cubeScaleFactor T.supportCube else 0 := by
  have hr : r.val < d := r.isLt
  have hkv : (kuhnEdgeVertex r).val = d - r.val := rfl
  have hkpv : (kuhnEdgePrevVertex r).val = d - r.val - 1 := rfl
  simp only [KuhnCell.vertex]
  rw [hkv, hkpv]
  by_cases hj : j = T.order r
  · subst hj
    rw [Equiv.symm_apply_apply, ite_eq_left (by omega : d ≤ r.val + (d - r.val)),
      ite_eq_right (by omega : ¬ d ≤ r.val + (d - r.val - 1)), ite_eq_left rfl]
    ring
  · have hne : (T.order.symm j).val ≠ r.val := by
      intro h
      exact hj (by rw [← T.order.apply_symm_apply j, Fin.ext h])
    rw [ite_eq_right hj]
    by_cases hge : r.val ≤ (T.order.symm j).val
    · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      ring

/-! ## The slope of the interpolant -/

/-- **The gradient of the affine interpolant on a Kuhn cell.**  Along the
coordinate direction `T.order r` the cell has exactly one edge, from
`v_{d-r-1}` to `v_{d-r}`, of length `3^{scale}`; the gradient coordinate is the
corresponding difference quotient.  This is the "`∇ℓ̂_e` is constant on each
coarse simplex" made explicit. -/
def kuhnSlope (T : KuhnCell d) (g : Vec d → ℝ) : Vec d := fun i =>
  (g (T.vertex (kuhnEdgeVertex (T.order.symm i))) -
      g (T.vertex (kuhnEdgePrevVertex (T.order.symm i)))) / cubeScaleFactor T.supportCube

/-- The gradient formula, indexed in the ambient coordinate order. -/
theorem kuhnSlope_apply (T : KuhnCell d) (g : Vec d → ℝ) (i : Fin d) :
    kuhnSlope T g i =
      (g (T.vertex (kuhnEdgeVertex (T.order.symm i))) -
          g (T.vertex (kuhnEdgePrevVertex (T.order.symm i)))) /
        cubeScaleFactor T.supportCube := rfl

/-- The gradient formula, indexed in the cell's own edge order. -/
theorem kuhnSlope_order (T : KuhnCell d) (g : Vec d → ℝ) (r : Fin d) :
    kuhnSlope T g (T.order r) =
      (g (T.vertex (kuhnEdgeVertex r)) - g (T.vertex (kuhnEdgePrevVertex r))) /
        cubeScaleFactor T.supportCube := by
  rw [kuhnSlope_apply, Equiv.symm_apply_apply]

/-- The gradient depends on the vertex datum only through its `d + 1` vertex
values. -/
theorem kuhnSlope_congr (T : KuhnCell d) {g g' : Vec d → ℝ}
    (hvert : ∀ k : Fin (d + 1), g (T.vertex k) = g' (T.vertex k)) :
    kuhnSlope T g = kuhnSlope T g' := by
  funext i
  simp only [kuhnSlope, hvert]

/-- **`e.hat.linear.linearity`** at the cell level: the interpolant's gradient is
additive in the vertex datum. -/
theorem kuhnSlope_add (T : KuhnCell d) (g g' : Vec d → ℝ) :
    kuhnSlope T (fun x => g x + g' x) = kuhnSlope T g + kuhnSlope T g' := by
  funext i
  simp only [kuhnSlope, Pi.add_apply]
  ring

theorem kuhnSlope_sub (T : KuhnCell d) (g g' : Vec d → ℝ) :
    kuhnSlope T (fun x => g x - g' x) = kuhnSlope T g - kuhnSlope T g' := by
  funext i
  simp only [kuhnSlope, Pi.sub_apply]
  ring

theorem kuhnSlope_smul (T : KuhnCell d) (c : ℝ) (g : Vec d → ℝ) :
    kuhnSlope T (fun x => c * g x) = c • kuhnSlope T g := by
  funext i
  simp only [kuhnSlope, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Clause 1 of `e.hat.linear.properties`**  at the cell level, as the manuscript
proves it: if every vertex of the cell receives the same value, the interpolant
has vanishing gradient there. -/
theorem kuhnSlope_eq_zero_of_vertex_const (T : KuhnCell d) {g : Vec d → ℝ} {c : ℝ}
    (hconst : ∀ k : Fin (d + 1), g (T.vertex k) = c) :
    kuhnSlope T g = 0 := by
  funext i
  simp only [kuhnSlope, hconst, Pi.zero_apply, sub_self, zero_div]

/-- **Clause 3 of `e.hat.linear.properties`** ((clause 3; the cases-end line
asserts nothing —, format)) at the cell level, as the manuscript proves it: the
vertex datum `ℓ_p` has interpolant gradient exactly `p`. -/
theorem kuhnSlope_linearFn (T : KuhnCell d) (p : Vec d) :
    kuhnSlope T (linearFn p) = p := by
  funext i
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hdiff :
      linearFn p (T.vertex (kuhnEdgeVertex (T.order.symm i))) -
          linearFn p (T.vertex (kuhnEdgePrevVertex (T.order.symm i))) =
        p i * cubeScaleFactor T.supportCube := by
    have hedge := vertex_kuhnEdge_sub_apply T (T.order.symm i)
    calc
      linearFn p (T.vertex (kuhnEdgeVertex (T.order.symm i))) -
            linearFn p (T.vertex (kuhnEdgePrevVertex (T.order.symm i)))
          = ∑ j, (p j * T.vertex (kuhnEdgeVertex (T.order.symm i)) j -
              p j * T.vertex (kuhnEdgePrevVertex (T.order.symm i)) j) := by
            simp only [linearFn, vecDot]
            rw [← Finset.sum_sub_distrib]
      _ = ∑ j, (if j = i then p j * cubeScaleFactor T.supportCube else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have h := hedge j
            rw [T.order.apply_symm_apply] at h
            rw [← mul_sub, h]
            split_ifs with hji
            · rfl
            · rw [mul_zero]
      _ = p i * cubeScaleFactor T.supportCube := by simp
  rw [kuhnSlope_apply, hdiff, mul_div_assoc, div_self (ne_of_gt hs), mul_one]

/-! ## The interpolant -/

/-- **The affine interpolant of vertex data on a Kuhn cell**, the object of Step 1
of the proof of `l.piecewise.affine.approx`: the affine function anchored at
the cell's lower corner `v_0` with gradient `kuhnSlope T g`.
`kuhnInterp_vertex` shows it agrees with `g` at all `d + 1` vertices, and
`eq_kuhnInterp_of_vertex_eq` shows it is the only affine function that does; so
this *is* the manuscript's "extend affinely" of the vertex datum `g`.  It is
defined, and affine, on all of `Vec d`; the manuscript uses its restriction to
the cell. -/
def kuhnInterp (T : KuhnCell d) (g : Vec d → ℝ) : Vec d → ℝ := fun x =>
  g (T.vertex 0) + vecDot (kuhnSlope T g) (x - T.vertex 0)

theorem kuhnInterp_apply (T : KuhnCell d) (g : Vec d → ℝ) (x : Vec d) :
    kuhnInterp T g x = g (T.vertex 0) + vecDot (kuhnSlope T g) (x - T.vertex 0) := rfl

/-- **`e.hat.linear.2`** at the cell level: `kuhnInterp T g` is affine, with
constant gradient `kuhnSlope T g`. -/
theorem kuhnInterp_sub (T : KuhnCell d) (g : Vec d → ℝ) (x y : Vec d) :
    kuhnInterp T g x - kuhnInterp T g y = vecDot (kuhnSlope T g) (x - y) := by
  simp only [kuhnInterp]
  rw [vecDot_sub_right, vecDot_sub_right, vecDot_sub_right]
  ring

/-- **`e.hat.linear.linearity`** at the cell level. -/
theorem kuhnInterp_add (T : KuhnCell d) (g g' : Vec d → ℝ) :
    kuhnInterp T (fun x => g x + g' x) =
      fun x => kuhnInterp T g x + kuhnInterp T g' x := by
  funext x
  simp only [kuhnInterp, kuhnSlope_add T g g']
  rw [vecDot_add_left']
  ring

/-! ### Agreement at the vertices -/

private theorem sum_range_reflect_telescope (A : ℕ → ℝ) (n K : ℕ) (hK : K ≤ n) :
    ∑ t ∈ Finset.range n,
        (A (n - t) - A (n - t - 1)) * (if n ≤ t + K then (1 : ℝ) else 0) =
      A K - A 0 := by
  classical
  have hrefl :=
    Finset.sum_range_reflect
      (fun t => (A (n - t) - A (n - t - 1)) * (if n ≤ t + K then (1 : ℝ) else 0)) n
  rw [← hrefl]
  have hstep : ∀ j ∈ Finset.range n,
      (A (n - (n - 1 - j)) - A (n - (n - 1 - j) - 1)) *
          (if n ≤ (n - 1 - j) + K then (1 : ℝ) else 0) =
        (A (j + 1) - A j) * (if j < K then (1 : ℝ) else 0) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have e1 : n - (n - 1 - j) = j + 1 := by omega
    have e2 : n - (n - 1 - j) - 1 = j := by omega
    have e3 : (n ≤ (n - 1 - j) + K) ↔ (j < K) := by omega
    rw [e2, e1, if_congr e3 rfl rfl]
  rw [Finset.sum_congr rfl hstep]
  have hres :
      ∑ j ∈ Finset.range n, (A (j + 1) - A j) * (if j < K then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.range K, (A (j + 1) - A j) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hK)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [ite_eq_left (Finset.mem_range.mp hj), mul_one]
    · intro x _ hx
      rw [ite_eq_right (by simpa using hx), mul_zero]
  rw [hres, Finset.sum_range_sub A K]

private theorem kuhn_edge_telescope (a : Fin (d + 1) → ℝ) (k : Fin (d + 1)) :
    ∑ r : Fin d,
        (a (kuhnEdgeVertex r) - a (kuhnEdgePrevVertex r)) *
          (if d ≤ r.val + k.val then (1 : ℝ) else 0) = a k - a 0 := by
  classical
  have hkd : k.val ≤ d := by omega
  have hterm : ∀ r : Fin d,
      (a (kuhnEdgeVertex r) - a (kuhnEdgePrevVertex r)) *
          (if d ≤ r.val + k.val then (1 : ℝ) else 0) =
        (fun t : ℕ =>
          ((fun j : ℕ => a ⟨min j d, by omega⟩) (d - t) -
              (fun j : ℕ => a ⟨min j d, by omega⟩) (d - t - 1)) *
            (if d ≤ t + k.val then (1 : ℝ) else 0)) r.val := by
    intro r
    have hr : r.val < d := r.isLt
    have h1 : (⟨min (d - r.val) d, by omega⟩ : Fin (d + 1)) = kuhnEdgeVertex r :=
      Fin.ext (by simp only [kuhnEdgeVertex]; omega)
    have h2 : (⟨min (d - r.val - 1) d, by omega⟩ : Fin (d + 1)) = kuhnEdgePrevVertex r :=
      Fin.ext (by simp only [kuhnEdgePrevVertex]; omega)
    simp only []
    rw [h1, h2]
  rw [Finset.sum_congr rfl fun r _ => hterm r,
    Fin.sum_univ_eq_sum_range
      (fun t : ℕ =>
        ((fun j : ℕ => a ⟨min j d, by omega⟩) (d - t) -
            (fun j : ℕ => a ⟨min j d, by omega⟩) (d - t - 1)) *
          (if d ≤ t + k.val then (1 : ℝ) else 0)) d,
    sum_range_reflect_telescope (fun j : ℕ => a ⟨min j d, by omega⟩) d k.val hkd]
  have hk : (⟨min k.val d, by omega⟩ : Fin (d + 1)) = k := by
    refine Fin.ext ?_
    change min k.val d = k.val
    omega
  have h0 : (⟨min 0 d, by omega⟩ : Fin (d + 1)) = 0 := by
    refine Fin.ext ?_
    change min 0 d = (0 : Fin (d + 1)).val
    simp
  rw [hk, h0]

/-- **The interpolant agrees with the vertex datum at every vertex.**  This is the
defining property of Step 1's "extend affinely". -/
theorem kuhnInterp_vertex (T : KuhnCell d) (g : Vec d → ℝ) (k : Fin (d + 1)) :
    kuhnInterp T g (T.vertex k) = g (T.vertex k) := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hcancel : ∀ A c : ℝ,
      (A / cubeScaleFactor T.supportCube) * (c * cubeScaleFactor T.supportCube) = A * c := by
    intro A c
    rw [div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self (ne_of_gt hs), mul_one]
  have hdiff : ∀ i : Fin d,
      (T.vertex k - T.vertex 0) i =
        (if d ≤ (T.order.symm i).val + k.val then (1 : ℝ) else 0) *
          cubeScaleFactor T.supportCube := by
    intro i
    have hlt : (T.order.symm i).val < d := (T.order.symm i).isLt
    simp only [Pi.sub_apply, KuhnCell.vertex, Fin.val_zero, add_zero]
    rw [ite_eq_right (by omega : ¬ d ≤ (T.order.symm i).val)]
    split_ifs <;> ring
  have hsum :
      vecDot (kuhnSlope T g) (T.vertex k - T.vertex 0) =
        ∑ r : Fin d,
          (g (T.vertex (kuhnEdgeVertex r)) - g (T.vertex (kuhnEdgePrevVertex r))) *
            (if d ≤ r.val + k.val then (1 : ℝ) else 0) := by
    simp only [vecDot]
    rw [← Equiv.sum_comp T.order
      (fun i => kuhnSlope T g i * (T.vertex k - T.vertex 0) i)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hdiff (T.order r), kuhnSlope_order, Equiv.symm_apply_apply, hcancel]
  rw [kuhnInterp_apply, hsum, kuhn_edge_telescope (fun j => g (T.vertex j)) k]
  ring

/-- Two cells interpolating the *same* global vertex datum agree at every point
that is a vertex of both.  No face-to-face property of the partition is used or
asserted. -/
theorem kuhnInterp_eqOn_inter_vertexSet (T U : KuhnCell d) (g : Vec d → ℝ) :
    Set.EqOn (kuhnInterp T g) (kuhnInterp U g) (T.vertexSet ∩ U.vertexSet) := by
  rintro x ⟨⟨k, rfl⟩, hU⟩
  obtain ⟨l, hl⟩ := hU
  rw [kuhnInterp_vertex, ← hl, kuhnInterp_vertex, hl]

/-! ### The bundled affine map -/

/-- `kuhnInterp T g` bundled as an affine map on `Vec d`, with linear part `v ↦
(∇ℓ̂) · v`.  The bundling exists for exactly one purpose: it makes
`kuhnInterpAffine_eqOn_affineSpan_inter_vertexSet` available, which is the
well-definedness instrument for a global interpolant assembled cell by cell
(the manuscript's "since adjacent coarse simplices share complete faces, this
extension is well-defined and continuous"; the mesh-interior half ---).  No
face-to-face property is assumed anywhere: the statement is about the affine
span of whatever vertices two cells happen to share. -/
def kuhnInterpAffine (T : KuhnCell d) (g : Vec d → ℝ) : Vec d →ᵃ[ℝ] ℝ where
  toFun := kuhnInterp T g
  linear :=
    { toFun := fun v => vecDot (kuhnSlope T g) v
      map_add' := fun a b => by exact vecDot_add_right' (kuhnSlope T g) a b
      map_smul' := fun c a => by exact vecDot_smul_right' (kuhnSlope T g) c a }
  map_vadd' := by
    intro x v
    change kuhnInterp T g (v + x) = vecDot (kuhnSlope T g) v + kuhnInterp T g x
    have h := kuhnInterp_sub T g (v + x) x
    rw [add_sub_cancel_right] at h
    linarith

@[simp] theorem kuhnInterpAffine_linear_apply (T : KuhnCell d) (g : Vec d → ℝ)
    (v : Vec d) : (kuhnInterpAffine T g).linear v = vecDot (kuhnSlope T g) v := rfl

/-- Two cells interpolating the *same* global vertex datum agree on the affine
span of the vertices they share.  Nothing here asserts that any two cells of
`SW(□_m)` do share a face. -/
theorem kuhnInterpAffine_eqOn_affineSpan_inter_vertexSet (T U : KuhnCell d)
    (g : Vec d → ℝ) :
    Set.EqOn (kuhnInterpAffine T g) (kuhnInterpAffine U g)
      (affineSpan ℝ (T.vertexSet ∩ U.vertexSet)) := by
  refine AffineMap.eqOn_affineSpan ?_
  intro x hx
  exact kuhnInterp_eqOn_inter_vertexSet T U g hx

/-! ### Determination by the vertex values -/

/-- The interpolant of the vertex datum `ℓ_p` is `ℓ_p` itself: clause 3 of
`e.hat.linear.properties` ((clause 3; the cases-end line asserts nothing —,
format)) at the cell level. -/
theorem kuhnInterp_linearFn (T : KuhnCell d) (p : Vec d) :
    kuhnInterp T (linearFn p) = linearFn p := by
  funext x
  rw [kuhnInterp_apply, kuhnSlope_linearFn, vecDot_sub_right]
  simp only [linearFn_apply]
  ring

/-- The interpolant depends on the vertex datum only through its `d + 1` vertex
values. -/
theorem kuhnInterp_congr (T : KuhnCell d) {g g' : Vec d → ℝ}
    (hvert : ∀ k : Fin (d + 1), g (T.vertex k) = g' (T.vertex k)) :
    kuhnInterp T g = kuhnInterp T g' := by
  funext x
  simp only [kuhnInterp, kuhnSlope_congr T hvert, hvert]

/-! ### The `Set.EqOn` interface of clauses 1 and 3

These are the shapes that the global competitor of `l.piecewise.affine.approx`
feeds to `Multiscale.sum_of_a_decomp` (SubadditiveDecomposition.lean), whose
`hbadF`/`hbadG` carry clause 1 and whose `hoffF`/`hoffG` carry clause 3 as
statements about the per-cell gradient value.  Each is the corresponding vertex
statement above, restated over `V(△)`. -/

/-- **Clause 1 of `e.hat.linear.properties`**  in the vertex-set form: a competitor
whose vertex datum is constant on `V(△)` has zero gradient on the cell. -/
theorem kuhnSlope_eq_zero_of_eqOn_vertexSet (T : KuhnCell d) {g : Vec d → ℝ} {c : ℝ}
    (hconst : Set.EqOn g (fun _ => c) T.vertexSet) : kuhnSlope T g = 0 := by
  refine kuhnSlope_eq_zero_of_vertex_const T (c := c) fun k => ?_
  exact hconst (Set.mem_range_self k)

/-- **Clause 3 of `e.hat.linear.properties`** ((clause 3; the cases-end line
asserts nothing —, format)) in the vertex-set form: a competitor whose vertex
datum agrees with `ℓ_p` on `V(△)` has gradient exactly `p` on the cell. -/
theorem kuhnSlope_eq_of_eqOn_vertexSet (T : KuhnCell d) {g : Vec d → ℝ} {p : Vec d}
    (hlin : Set.EqOn g (linearFn p) T.vertexSet) : kuhnSlope T g = p := by
  rw [kuhnSlope_congr T (g' := linearFn p) fun k => hlin (Set.mem_range_self k),
    kuhnSlope_linearFn]

/-- The function form of `kuhnSlope_eq_of_eqOn_vertexSet`: a competitor whose
vertex datum agrees with `ℓ_p` on `V(△)` *is* `ℓ_p` on the cell. -/
theorem kuhnInterp_eq_linearFn_of_eqOn_vertexSet (T : KuhnCell d) {g : Vec d → ℝ}
    {p : Vec d} (hlin : Set.EqOn g (linearFn p) T.vertexSet) :
    kuhnInterp T g = linearFn p :=
  (kuhnInterp_congr T fun k => hlin (Set.mem_range_self k)).trans
    (kuhnInterp_linearFn T p)

/-! ## Step 2: the gradient estimate -/

/-- **Step 2 of the proof of `l.piecewise.affine.approx`**, in the coordinate form.
If the vertex values of `ℓ̂ − ℓ_p` oscillate by at most `B` over the vertices
of the cell, then each coordinate of `∇ℓ̂ − p` is at most `B` over the cube
side `3^{scale}`.  This is the printed `|∇ℓ̂_e − e|_{L^∞(𝔰)} ≤ (C / diam 𝔰) ·
max_{v,w ∈ V(𝔰)} |(ℓ̂_e − ℓ_e)(v) − (ℓ̂_e − ℓ_e)(w)|` with `C = 1` against the
cube side. -/
theorem abs_kuhnSlope_sub_le_of_vertex_oscillation (T : KuhnCell d)
    (g : Vec d → ℝ) (p : Vec d) {B : ℝ}
    (hB : ∀ k l : Fin (d + 1),
      |(g (T.vertex k) - linearFn p (T.vertex k)) -
        (g (T.vertex l) - linearFn p (T.vertex l))| ≤ B) (i : Fin d) :
    |kuhnSlope T g i - p i| ≤ B / cubeScaleFactor T.supportCube := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hdec :
      kuhnSlope T g - p = kuhnSlope T (fun x => g x - linearFn p x) := by
    rw [kuhnSlope_sub, kuhnSlope_linearFn]
  have hval : kuhnSlope T g i - p i =
      ((g (T.vertex (kuhnEdgeVertex (T.order.symm i))) -
            linearFn p (T.vertex (kuhnEdgeVertex (T.order.symm i)))) -
          (g (T.vertex (kuhnEdgePrevVertex (T.order.symm i))) -
            linearFn p (T.vertex (kuhnEdgePrevVertex (T.order.symm i))))) /
        cubeScaleFactor T.supportCube := by
    have := congrFun hdec i
    rw [Pi.sub_apply] at this
    rw [this, kuhnSlope_apply]
  rw [hval, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right
    (hB (kuhnEdgeVertex (T.order.symm i)) (kuhnEdgePrevVertex (T.order.symm i))) hs.le

/-- **Step 2 of the proof of `l.piecewise.affine.approx`**, in the Euclidean form
used downstream: the squared Euclidean norm of `∇ℓ̂ − p` on the cell is at most
`d · (B / 3^{scale})²`.  Against the cube side `3^{scale}` the constant is
`√d`; the printed display normalizes by `diam(𝔰) = √d·3^{scale}`, so the
printed `C(d)` is `d`, not `√d`. -/
theorem vecNormSq_kuhnSlope_sub_le_of_vertex_oscillation (T : KuhnCell d)
    (g : Vec d → ℝ) (p : Vec d) {B : ℝ}
    (hB : ∀ k l : Fin (d + 1),
      |(g (T.vertex k) - linearFn p (T.vertex k)) -
        (g (T.vertex l) - linearFn p (T.vertex l))| ≤ B) :
    vecNormSq (kuhnSlope T g - p) ≤
      (d : ℝ) * (B / cubeScaleFactor T.supportCube) ^ 2 := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB 0 0)
  have hquot : (0 : ℝ) ≤ B / cubeScaleFactor T.supportCube := div_nonneg hB0 hs.le
  have hsq : ∀ i : Fin d,
      (kuhnSlope T g - p) i * (kuhnSlope T g - p) i ≤
        (B / cubeScaleFactor T.supportCube) ^ 2 := by
    intro i
    have habs := abs_kuhnSlope_sub_le_of_vertex_oscillation T g p hB i
    have hmul := mul_self_le_mul_self (abs_nonneg (kuhnSlope T g i - p i)) habs
    rw [abs_mul_abs_self] at hmul
    rw [Pi.sub_apply, pow_two]
    exact hmul
  calc
    vecNormSq (kuhnSlope T g - p)
        = ∑ i, (kuhnSlope T g - p) i * (kuhnSlope T g - p) i := rfl
    _ ≤ ∑ _i : Fin d, (B / cubeScaleFactor T.supportCube) ^ 2 :=
        Finset.sum_le_sum fun i _ => hsq i
    _ = (d : ℝ) * (B / cubeScaleFactor T.supportCube) ^ 2 := by simp

/-- The form of Step 2 that the manuscript actually feeds: a *pointwise* vertex
bound `|ℓ̂ − ℓ_p| ≤ B` at the vertices of the cell gives the gradient bound
with the oscillation replaced by `2B`. -/
theorem vecNormSq_kuhnSlope_sub_le_of_vertex_bound (T : KuhnCell d)
    (g : Vec d → ℝ) (p : Vec d) {B : ℝ}
    (hB : ∀ k : Fin (d + 1), |g (T.vertex k) - linearFn p (T.vertex k)| ≤ B) :
    vecNormSq (kuhnSlope T g - p) ≤
      (d : ℝ) * (2 * B / cubeScaleFactor T.supportCube) ^ 2 := by
  refine vecNormSq_kuhnSlope_sub_le_of_vertex_oscillation T g p ?_
  intro k l
  have h1 := abs_le.mp (hB k)
  have h2 := abs_le.mp (hB l)
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Step 2 in the vertex-set form: this is the shape a global competitor feeds,
since the manuscript's Step-2 vertex bound `|ℓ̂_e(v) − ℓ_e(v)| ≤ |e| diam(𝒞_j)
1_{v ∈ V(𝒞_j)}` is a statement about the points of `V(△)`. -/
theorem vecNormSq_kuhnSlope_sub_le_of_vertexSet_bound (T : KuhnCell d)
    (g : Vec d → ℝ) (p : Vec d) {B : ℝ}
    (hB : ∀ v ∈ T.vertexSet, |g v - linearFn p v| ≤ B) :
    vecNormSq (kuhnSlope T g - p) ≤
      (d : ℝ) * (2 * B / cubeScaleFactor T.supportCube) ^ 2 :=
  vecNormSq_kuhnSlope_sub_le_of_vertex_bound T g p fun k =>
    hB _ (Set.mem_range_self k)

end

end Algsuperdiff.Section3.Provider.Affine
