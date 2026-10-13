/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.KuhnFaceAlignment
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeColoring

/-!
# GlobalGluing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The glued piecewise-affine function of `l.piecewise.affine.approx`

This module builds the function that Step 1 of ABK26's
`l.piecewise.affine.approx` constructs: "we prescribe the values at the
vertices and extend affinely to each simplex; since adjacent coarse simplices
share complete faces, this extension is well-defined and continuous".

`gluedKuhnAffine S g` is that function for a **finite equal-scale** family `S`
of Kuhn cells and a **global** vertex datum `g`.

* *equal scale.* rules **false** the printed inference that the final
  nonuniform family `SW(□_m)` is face-to-face; its Correction, and the
  clarifications/, prescribe instead that the values be prescribed and extended
  affinely on the **common coarse mesh**, which is a single-scale mesh, and
  only *then* restricted to the finer final cells.  The equal-scale hypothesis
  is exactly the hypothesis of the face-alignment lemma
  `closedCarrier_inter_subset_commonClosedFace` (`KuhnFaceAlignment.lean`),
  which is what makes the gluing well defined.  See the STOP note below for why
  no cross-scale variant of this definition is available.
* *finite.*  Local finiteness of the closed cells is what patches the per-cell
  continuity into continuity on the union
  (`LocallyFinite.continuousOn_iUnion`).  The common coarse mesh of a bounded
  Whitney-layer window is finite, which is the case needs; no statement below
  is about all of `SW(□_m)`, which is countably infinite.

## STOP: the cross-scale seam is not a gluing statement (recorded)

The obvious cross-scale generalization -- glue the per-cell interpolants
`kuhnInterp T g` over the *final* nonuniform family `SW(□_m)` -- is **not** the
manuscript's function and is **not** available from the proved inputs.  On a
final layer-`(j+1)` cell `T'` the manuscript's `ℓ̂_p` is the *coarse* affine
map of the common cell `U ⊇ T'`, whose values at the hanging vertices of `T'`
are "inherited from the coarse affine trace", **not** the prescribed datum `g`
at those points.

## Scope: what this module does NOT do

* No bad cube, component, neighborhood, layer or collar occurs; the mesh `S`
  and the datum `g` are arbitrary.  In particular nothing here assumes the
  neighborhoods of distinct components are disjoint  and no layer window is
  fixed.
* No `H¹` statement.
* No slope field of the glued function is defined here, and no identification
  of a piecewise-constant field with the distributional `∇ℓ̂_p` is proved or
  used.  What is proved is the cell-wise identification
  `gluedKuhnAffine_eqOn_closedCarrier`: on the closed carrier of each cell of
  the mesh the glued function *is* that cell's interpolant `kuhnInterp T g`,
  which is affine with the constant slope `kuhnSlope T g`.  That is the
  classical content of "`∇ℓ̂_p` is constant on each coarse simplex", read at
  the level of the function rather than of its gradient.
* is not consumed: no slope-square and no collar constant enters.

## References

* ABK26, (`l.piecewise.affine.approx`, `e.hat.linear.properties`), (Step 1, the
  "well-defined and continuous" sentence), (`e.SW.def`),
  (`e.hat.linear.linearity`), (`ℓ_e(x) = e·x`).
-/

namespace Algsuperdiff.Section3.Provider.Affine

open HCPolySupport
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Continuity and disjointness of single cells -/

/-- The interpolant on one cell is continuous: it is an affine function of the
coordinates. -/
theorem continuous_kuhnInterp (T : KuhnCell d) (g : Vec d → ℝ) :
    Continuous (kuhnInterp T g) := by
  show Continuous fun x : Vec d =>
    g (T.vertex 0) + ∑ i, kuhnSlope T g i * (x - T.vertex 0) i
  refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_const.mul ((continuous_apply i).comp (continuous_id.sub continuous_const))

/-- Distinct Kuhn cells of one scale have disjoint open simplices: either they
share their support cube and differ in the coordinate order, or their support
cubes are distinct members of one aligned triadic grid. -/
theorem disjoint_openCarrier_of_supportCube_scale_eq {T U : KuhnCell d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hTU : T ≠ U) :
    Disjoint T.openCarrier U.openCarrier := by
  by_cases hsupport : T.supportCube = U.supportCube
  · exact (KuhnCell.disjoint_carrier_of_supportCube_eq hTU hsupport).mono
      T.openCarrier_subset_carrier U.openCarrier_subset_carrier
  · exact (disjoint_cubeSet_of_scale_eq_of_ne hscale hsupport).mono
      (T.openCarrier_subset_openCubeSet.trans (openCubeSet_subset_cubeSet _))
      (U.openCarrier_subset_openCubeSet.trans (openCubeSet_subset_cubeSet _))

/-! ## The glued function -/

open Classical in
/-- **The piecewise-affine function of Step 1 of `l.piecewise.affine.approx`**: on
each cell of the mesh `S` it is that cell's affine interpolant of the global
vertex datum `g`, and away from the mesh it is the datum itself.

Well-definedness is *proved*, not assumed: two cells of one scale agree on the
overlap of their closed carriers
(`kuhnInterp_eqOn_closedCarrier_inter`), so the cell selected here is
immaterial.  See `gluedKuhnAffine_eqOn_closedCarrier`,
`gluedKuhnAffine_of_forall_notMem` and `existsUnique_gluedKuhnAffine` for the
characterization that pins the definition. -/
def gluedKuhnAffine (S : Finset (KuhnCell d)) (g : Vec d → ℝ) (x : Vec d) : ℝ :=
  if h : ∃ T ∈ S, x ∈ T.closedCarrier then kuhnInterp h.choose g x else g x

/-- **The first defining equation**: on every closed cell of a single-scale mesh
the glued function is that cell's interpolant. -/
theorem gluedKuhnAffine_eqOn_closedCarrier {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (g : Vec d → ℝ)
    {T : KuhnCell d} (hT : T ∈ S) :
    Set.EqOn (gluedKuhnAffine S g) (kuhnInterp T g) T.closedCarrier := by
  classical
  intro x hx
  have hex : ∃ U ∈ S, x ∈ U.closedCarrier := ⟨T, hT, hx⟩
  have hspec := hex.choose_spec
  show (if h : ∃ U ∈ S, x ∈ U.closedCarrier then kuhnInterp h.choose g x else g x) =
    kuhnInterp T g x
  rw [dite_eq_left hex]
  exact kuhnInterp_eqOn_closedCarrier_inter hex.choose T g
    ((hscale _ hspec.1).trans (hscale T hT).symm) ⟨hspec.2, hx⟩

/-- Pointwise form of `gluedKuhnAffine_eqOn_closedCarrier`. -/
theorem gluedKuhnAffine_of_mem_closedCarrier {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (g : Vec d → ℝ)
    {T : KuhnCell d} (hT : T ∈ S) {x : Vec d} (hx : x ∈ T.closedCarrier) :
    gluedKuhnAffine S g x = kuhnInterp T g x :=
  gluedKuhnAffine_eqOn_closedCarrier hscale g hT hx

/-! ## Continuity -/

/-- **"this extension is well-defined and continuous"** (; the M half — the
off-mesh join is the unlanded boundary matching;).  The closed cells of a
finite mesh are a locally finite closed cover of their union, and on each of
them the glued function is an affine map. -/
theorem continuousOn_gluedKuhnAffine {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (g : Vec d → ℝ) :
    ContinuousOn (gluedKuhnAffine S g)
      (⋃ T ∈ (S : Set (KuhnCell d)), T.closedCarrier) := by
  classical
  rw [Set.biUnion_eq_iUnion]
  refine (locallyFinite_of_finite
    (fun T : ↥(S : Set (KuhnCell d)) => (T : KuhnCell d).closedCarrier)).continuousOn_iUnion
    (fun T => isClosed_closedCarrier (T : KuhnCell d)) fun T => ?_
  exact (continuous_kuhnInterp (T : KuhnCell d) g).continuousOn.congr
    (gluedKuhnAffine_eqOn_closedCarrier hscale g T.2)

/-! ## `e.hat.linear.linearity` and clause 3 at the glued level -/

/-- The cell interpolant is homogeneous in the vertex datum; the additive half
is `kuhnInterp_add` of `KuhnInterpolation.lean`. -/
theorem kuhnInterp_smul (T : KuhnCell d) (c : ℝ) (g : Vec d → ℝ) :
    kuhnInterp T (fun x => c * g x) = fun x => c * kuhnInterp T g x := by
  funext x
  have hdot : vecDot (c • kuhnSlope T g) (x - T.vertex 0) =
      c * vecDot (kuhnSlope T g) (x - T.vertex 0) := by
    simp only [vecDot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [kuhnInterp, kuhnSlope_smul, hdot]
  ring

end

end Algsuperdiff.Section3.Provider.Affine
