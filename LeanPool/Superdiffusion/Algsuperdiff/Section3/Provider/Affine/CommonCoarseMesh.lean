/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.CompetitorVertexData
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalGluing

/-!
# CommonCoarseMesh

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The common coarse mesh and the competitor on it

This module provides a proved local implementation of the **corrected Step 1**
construction associated with ABK26's `l.piecewise.affine.approx`, in the form
prescribed:

> Let `j` be the least layer occupied by the **neighborhood**.  Then
> `𝒩(𝒞) ⊆ 𝒲(□_m, j) ∪ 𝒲(□_m, j+1)`.  The target-`j` common mesh is exactly the
> final `e.SW.def` mesh on layer `j`.  On layer `j+1`, the printed final mesh
> refines that common coarse mesh.  Hence one may prescribe values and extend
> affinely on the common coarse mesh, then restrict the affine maps to the
> deeper final simplices.  The restriction remains affine, continuous, and
> subordinate to the printed `SW(□_m)`.

`commonCoarseMesh N s` is that mesh: every cube of the window `N` triangulated
at the single scale `s`.

## Scope: what this module does NOT do

* **The two-layer window is a hypothesis here, not a theorem.**  Every
  statement takes the window `N` and the layer bound as explicit binders; the
  fact that the *actual* touching neighborhood `𝒩(𝒞)` occupies at most two
  consecutive layers -- the second "small point" -- is a statement about
  `l.bad.clusters.geometry`, is not proved here, and is not assumed anywhere
  below in disguise: nothing in this file mentions `𝒩(𝒞)`.
* **No global assembly.**  The competitor is built on *one* window.  Assembling
  the per-component window competitors into a single global `ℓ̂_p` on `□_m`
  still requires handling the overlap (neighborhoods of distinct components are
  **not** disjoint) and the matching of each window competitor with `ℓ_p`
  across the outer boundary of its window.  Neither is proved here or anywhere
  in this repository.
* **No `H¹` statement.**  `e.hat.linear.1` (label and content) and the
  `hF`/`hG` binders of `sum_of_a_decomp` require an `H10Function` witness and
  an `L²` weak gradient; see the scope section of `GlobalGluing.lean`.
* /`-c1` are not consumed: no gradient estimate, no collar constant and no
  component diameter occurs here.

## References

* ABK26, (`e.SW.def`), (`l.piecewise.affine.approx`,
  `e.hat.linear.properties`), (Step 1), (the prescribed vertex values),
  (`ℓ_e(x) = e·x`).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The common coarse mesh -/

/-- **The common coarse mesh**: every cube of the window `N` triangulated at the
one scale `s`.  On the shallow layer of a two-layer window this is `e.SW.def`
itself; on the deeper layer it is the `d!`-simplex decomposition of the cube at
its own scale, which the final `e.SW.def` mesh refines. -/
def commonCoarseMesh (N : Finset (TriadicCube d)) (s : ℤ) : Finset (KuhnCell d) :=
  N.biUnion fun R => triadicSimplexPartition R s

theorem mem_commonCoarseMesh_iff {N : Finset (TriadicCube d)} {s : ℤ} {T : KuhnCell d} :
    T ∈ commonCoarseMesh N s ↔ ∃ R ∈ N, T.supportCube ∈ descendantsAtScale R s := by
  classical
  simp only [commonCoarseMesh, Finset.mem_biUnion, mem_triadicSimplexPartition_iff]

/-! ## The two-layer window -/

/-- **The scale identity**, in the form the window needs: a layer-`(j+1)` Whitney
cube has exactly the layer-`j` simplex scale. -/
theorem scale_eq_simplexScale_of_mem_whitneyLayer_succ {m : ℤ} {hn : ℕ → ℕ} {j : ℕ}
    {R : TriadicCube d} (hR : R ∈ whitneyLayer m hn (j + 1)) :
    R.scale = simplexScale m hn j := by
  rw [scale_eq_of_mem_whitneyLayer hR, simplexScale]
  push_cast
  ring

end

end Algsuperdiff.Section3.Provider.Affine
