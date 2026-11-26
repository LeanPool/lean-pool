/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Subpath
import Mathlib.Tactic.Ring

/-!
# Original parameters of retained outer subpaths

The homotopic rerouting used in the Section 8 reduction for XII (3.1),
page 245, produces outer subpaths of partition subpaths. Affine
reparametrization identifies them with closed intervals of the original
path. This makes the finite-graph subarc construction apply directly.
-/

public section

namespace GraphMinor.GM12

open Set

/-- Taking a subpath of a subpath composes its affine parameters. -/
theorem subpath_subpath_eq
    {S : Type*} [TopologicalSpace S] {a b : S} (p : Path a b)
    (u v r s : unitInterval) :
    (p.subpath u v).subpath r s =
      p.subpath (Icc.convexComb u v r) (Icc.convexComb u v s) := by
  ext t
  change p (Icc.convexComb u v (Icc.convexComb r s t)) =
    p (Icc.convexComb (Icc.convexComb u v r) (Icc.convexComb u v s) t)
  apply congrArg p
  apply Subtype.ext
  simp only [Icc.coe_convexComb]
  ring

/-- The left outer subpath is the corresponding initial closed
interval of the original path. -/
theorem range_left_outer_subpath
    {S : Type*} [TopologicalSpace S] {a b : S} (p : Path a b)
    {u v : unitInterval} (huv : u ≤ v) (r : unitInterval) :
    range ((p.subpath u v).subpath 0 r) = p '' Icc u (Icc.convexComb u v r) := by
  have heq := congrArg (fun γ : Path ((p.subpath u v) 0) ((p.subpath u v) r) => range γ)
    (subpath_subpath_eq p u v 0 r)
  have hle : Icc.convexComb u v 0 ≤ Icc.convexComb u v r := by
    rw [Icc.convexComb_zero]
    exact Icc.le_convexComb huv r
  exact heq.trans ((Path.range_subpath_of_le p _ _ hle).trans
    (congrArg (fun z => p '' Icc z (Icc.convexComb u v r)) (Icc.convexComb_zero u v)))

/-- The right outer subpath is the corresponding final closed
interval of the original path. -/
theorem range_right_outer_subpath
    {S : Type*} [TopologicalSpace S] {a b : S} (p : Path a b)
    {u v : unitInterval} (huv : u ≤ v) (r : unitInterval) :
    range ((p.subpath u v).subpath r 1) = p '' Icc (Icc.convexComb u v r) v := by
  have heq := congrArg (fun γ : Path ((p.subpath u v) r) ((p.subpath u v) 1) => range γ)
    (subpath_subpath_eq p u v r 1)
  have hle : Icc.convexComb u v r ≤ Icc.convexComb u v 1 := by
    rw [Icc.convexComb_one]
    exact Icc.convexComb_le huv r
  exact heq.trans ((Path.range_subpath_of_le p _ _ hle).trans
    (congrArg (fun z => p '' Icc (Icc.convexComb u v r) z) (Icc.convexComb_one u v)))

end GraphMinor.GM12
