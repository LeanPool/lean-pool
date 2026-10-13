/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.ZeroExtension
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.MuOperator.CoeffOperator
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives

/-!
# SubadditivityBetter

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: variational simplex subadditivity (`l.subadd.betterer`)

This file is a finite-carrier candidate/provider implementation for Lemma
`l.subadd.betterer` and its display `e.subadd.betterer` of ABK26.

for a partition `SW` of a cube `cu_m` into (triadic) simplices and a family of
piecewise-affine competitors `hat-linear_p`, `hat-D_q` satisfying the displayed
boundary conditions `e.hat.linear.1` and `e.hat.D.bc`,

```
  (p,q) . bfA(cu_m; a) (p,q)
    <= sum_{s in SW} (|s| / |cu_m|) (grad hat-linear_p (s), div hat-D_q (s))
         . bfA(s; a) (grad hat-linear_p (s), div hat-D_q (s)).
```

## Carrier choices

* `bfA(U; a)` is CoarseGraining's `Homogenization.Book.Ch02.coarseBlockMatrix U
  a`, whose defining property
  `Homogenization.Book.Ch02.DoubledMuTheory.doubledMu_eq_coarseBlockMatrix` is
  exactly the paper's `e.bigA.def` `mu(U,P) = 1/2 P . bfA(U) P`, with `mu(U,P)
  = doubledMu U a P` the paper's `e.variational.mu.U.P`: the infimum of `⨍_U
  1/2 X. bfA X` over `X ∈ P + L²_pot,0(U) × L²_sol,0(U)`.

* The partition `SW` is carried by a finite family `S : ι → Domain d` of
  subdomains of `Q`, pairwise disjoint, whose union exhausts `Q` up to a
  Lebesgue-null set.  Open triadic simplices of a triangulation of `cu_m` are
  exactly of this form (an open simplex is an open bounded convex nonempty set,
  distinct open cells of a triangulation are disjoint, and the union of the
  closed cells is the cube, so only the faces — a null set — are missed).  No
  simplicial structure is used by the proof and none is assumed.

  **Finite-carrier form.**  `[Fintype ι]` restricts this file's statement to
  *finite* partitions.  The paper's own Whitney partition `W(cu_m)` and hence
  its simplicial refinement `SW(cu_m)` are countably infinite, and the
  application sums over that infinite family.

* The competitor pair is carried at the level of the two *fields* `F = grad
  hat-linear_p` and `G = div hat-D_q`, through exactly the two displayed
  boundary properties the paper's proof invokes, `F ∈ p + L²_pot,0(cu_m)`
  (`e.hat.linear.1`) and `G ∈ q + L²_sol,0(cu_m)` (`e.hat.D.bc`), together with
  the paper's `e.hat.linear.2`, that these fields are constant on each element
  of the partition, with constant values `Fc i` and `Gc i` — the paper's `grad
  hat-linear_p (s)` and `div hat-D_q (s)`.  This is weaker than the paper's
  hypotheses (it forgets that the fields come from a *linear* family of
  piecewise affine potentials, which the paper's proof never uses), so the
  theorem below implies the paper's statement.
-/

namespace Algsuperdiff
namespace Section3
namespace Provider
namespace Whitney

open HCPolySupport
open MeasureTheory

variable {d : ℕ}

/-! ## Auxiliary `L²` facts -/

/-- A pair of vector `L²` fields is a block `L²` field. -/
theorem memBlockL2_pair {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    MemBlockL2 U fun x => ((f x, g x) : BlockVec d) := by
  refine MeasureTheory.MemLp.mono (hf.norm.add hg.norm)
    (hf.aestronglyMeasurable.prodMk hg.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have h1 : ‖((f x, g x) : BlockVec d)‖ = max ‖f x‖ ‖g x‖ := rfl
  have h2 : ‖(((fun y => ‖f y‖) + fun y => ‖g y‖) x : ℝ)‖ = ‖f x‖ + ‖g x‖ := by
    simp only [Pi.add_apply, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [h1, h2]
  exact max_le (by linarith [norm_nonneg (g x)]) (by linarith [norm_nonneg (f x)])

/-- Adding back a constant to a zero-trace correction keeps `L²` membership on a
finite-measure set. -/
theorem memVectorL2_of_sub_const {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {f : Vec d → Vec d} {c : Vec d}
    (hf : MemVectorL2 U fun x => f x - c) : MemVectorL2 U f := by
  have hconst : MemVectorL2 U fun _ : Vec d => c :=
    MeasureTheory.memLp_const c
  have hsum := hf.add hconst
  have heq : ((fun x => f x - c) + fun _ : Vec d => c) = f := by
    funext x
    simp
  rwa [heq] at hsum

end Whitney
end Provider
end Section3
end Algsuperdiff
