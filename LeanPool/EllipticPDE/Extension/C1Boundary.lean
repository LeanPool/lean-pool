/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Extension.BoundaryChart


/-!
# Domains with `C¹` boundary

The extension operator asks that the boundary be `C¹`, and this file states that hypothesis as
Evans states it (§C.1, p. 665): the boundary `∂U` is `C^k` when for each `x⁰ ∈ ∂U` there are
`r > 0` and a `C^k` function `γ : ℝ^{n-1} → ℝ` such that, upon relabelling and reorienting the
coordinate axes if necessary, `U ∩ B(x⁰, r) = {x ∈ B(x⁰, r) | xₙ > γ(x₁, …, x_{n-1})}`. Guo asks
the same in Theorem III.2.2 (p. 20).

Two points of encoding. The relabelling and reorientation of the axes is a linear isometry of
the whole space, split here between that isometry and the direction the graph is taken in. A
function of the coordinates other than the `j`-th is a function of all of them that does not
depend on the `j`-th, which is `IndepCoord`.

Nothing else is added. In particular the chart asks for no bound on the gradient of the graph,
which the statements about the shear all need: `exists_bounded_graph` supplies one instead, by
cutting the graph off in the tangential directions outside the ball the chart describes, where
the chart constrains nothing.

## Main declarations

* `EllipticPdes.Extension.tangential`: the projection killing the direction of the graph.
* `EllipticPdes.Extension.exists_bound_on_cylinder`: a continuous function independent of a
  coordinate is bounded on a cylinder around that coordinate's axis.
* `EllipticPdes.Extension.exists_bounded_graph`: every graph agrees on a ball with one of
  bounded gradient.
* `EllipticPdes.Extension.C1Chart`: a boundary chart.
* `EllipticPdes.Extension.C1Chart.Fits`: the chart describes the domain near a point.
* `EllipticPdes.Extension.HasC1Boundary`: every boundary point admits a chart.
* `EllipticPdes.Extension.C1Chart.fits_ball`: the chart read in the original coordinates.
* `EllipticPdes.Extension.isCompact_frontier`: the boundary of a bounded domain is compact.
* `EllipticPdes.Extension.exists_finite_chart_cover`: finitely many charts' balls cover the
  boundary.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20) and its proof, step 2 (p. 21); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§C.1 (p. 665) and §5.4 Theorem 1 (p. 253).
-/

@[expose] public section

open MeasureTheory Metric Set

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-! ### The tangential projection -/

/-- **Projection killing the `j`-th coordinate**, the direction a chart is a graph in. -/
def tangential (j : Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))
    - (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single j (1 : ℝ))

theorem tangential_apply (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    tangential j y = y - y j • EuclideanSpace.single j (1 : ℝ) := rfl

theorem tangential_coord (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    tangential j y i = if i = j then 0 else y i := by
  rw [tangential_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem tangential_add_smul (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    tangential j (y + t • EuclideanSpace.single j (1 : ℝ)) = tangential j y := by
  ext i
  rw [tangential_coord, tangential_coord]
  by_cases h : i = j
  · simp [h]
  · simp [h]

/-- The projection does not increase the norm. -/
theorem norm_tangential_le (j : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    ‖tangential j y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [tangential_coord]
  by_cases h : i = j
  · rw [ite_eq_left h, norm_zero, zero_pow (by norm_num)]
    positivity
  · rw [ite_eq_right h]

/-- A function independent of the `j`-th coordinate factors through the projection. -/
theorem apply_tangential {j : Fin d} {f : EuclideanSpace ℝ (Fin d) → ℝ} (hind : IndepCoord j f)
    (y : EuclideanSpace ℝ (Fin d)) : f (tangential j y) = f y := by
  have h : tangential j y = y + (-(y j)) • EuclideanSpace.single j (1 : ℝ) := by
    rw [tangential_apply, neg_smul]; abel
  rw [h, hind y (-(y j))]

/-- **Boundedness on a cylinder of a continuous function independent of a coordinate.** The
function factors through the projection, so its values on the cylinder are its values on a
closed ball, which is compact. -/
theorem exists_bound_on_cylinder {j : Fin d} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : Continuous f) (hind : IndepCoord j f) (z : EuclideanSpace ℝ (Fin d)) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : EuclideanSpace ℝ (Fin d),
      ‖tangential j y - tangential j z‖ ≤ R → ‖f y‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (tangential j z) R).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y hy => ?_⟩
  rw [← apply_tangential hind y]
  refine le_trans (hM _ ?_) (le_max_left _ _)
  rw [mem_closedBall, dist_eq_norm]
  exact hy

/-- A partial derivative is bounded by the derivative, the coordinate direction being a unit
vector. -/
theorem norm_partialD_le_fderiv {f : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    (y : EuclideanSpace ℝ (Fin d)) : ‖partialD k f y‖ ≤ ‖fderiv ℝ f y‖ := by
  have h := (fderiv ℝ f y).le_opNorm (EuclideanSpace.single k (1 : ℝ))
  rwa [PiLp.norm_single, norm_one, mul_one] at h

/-! ### Cutting a graph off outside the ball it describes -/

/-- **Every graph agrees on a ball with one of bounded gradient.** A chart constrains its graph
only on the ball it describes, so cutting the graph off in the tangential directions leaves the
description alone and bounds the gradient. This is what lets the chart ask for no bound while
every statement about the shear has one. -/
theorem exists_bounded_graph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) (z : EuclideanSpace ℝ (Fin d)) {r : ℝ}
    (hr : 0 < r) :
    ∃ (γ' : EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ), ContDiff ℝ 1 γ' ∧ IndepCoord j γ' ∧
      (∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ' y‖ ≤ M) ∧
      aboveGraph j γ' ∩ ball z r = aboveGraph j γ ∩ ball z r := by
  classical
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  set ρ : ContDiffBump (tangential j z) :=
    { rIn := r, rOut := 2 * r, rIn_pos := hr, rIn_lt_rOut := by linarith } with hρdef
  set ζ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ρ (tangential j y) with hζdef
  have hζsmooth : ContDiff ℝ (⊤ : ℕ∞) ζ := ρ.contDiff.comp (tangential j).contDiff
  have hζd : Differentiable ℝ ζ := hζsmooth.differentiable (by simp)
  have hζind : IndepCoord j ζ := fun y t => by
    simp only [hζdef, tangential_add_smul]
  have hζ01 : ∀ y, ζ y ≤ 1 ∧ 0 ≤ ζ y := fun y => ⟨ρ.le_one, ρ.nonneg⟩
  -- inside the ball the cutoff is one
  have hζone : ∀ y ∈ ball z r, ζ y = 1 := by
    intro y hy
    refine ρ.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_eq_norm, ← map_sub]
    exact le_of_lt (lt_of_le_of_lt (norm_tangential_le j (y - z))
      (by rwa [← dist_eq_norm, ← mem_ball]))
  -- outside the wider cylinder both the cutoff and its derivative vanish
  have hζzero : ∀ y, 2 * r < ‖tangential j y - tangential j z‖ →
      ζ y = 0 ∧ fderiv ℝ ζ y = 0 := by
    intro y hy
    have hopen : IsOpen {w : EuclideanSpace ℝ (Fin d) |
        2 * r < ‖tangential j w - tangential j z‖} :=
      isOpen_lt continuous_const (by fun_prop)
    have heq : ζ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hy] with w hw
      exact ρ.zero_of_le_dist (by rw [dist_eq_norm]; exact le_of_lt hw)
    exact ⟨ρ.zero_of_le_dist (by rw [dist_eq_norm]; exact le_of_lt hy),
      by rw [heq.fderiv_eq]; simp⟩
  -- the three bounds on the wider cylinder
  obtain ⟨A, hA0, hA⟩ := exists_bound_on_cylinder (j := j)
    (f := fun y => ‖fderiv ℝ γ y‖) ((hγ.continuous_fderiv one_ne_zero).norm)
    (fun y t => by simp only; rw [fderiv_eq_of_indepCoord hγd hind y t]) z (2 * r)
  obtain ⟨B, hB0, hB⟩ := exists_bound_on_cylinder (j := j)
    (f := fun y => ‖fderiv ℝ ζ y‖)
    (((hζsmooth.of_le (by exact_mod_cast le_top)).continuous_fderiv one_ne_zero).norm)
    (fun y t => by simp only; rw [fderiv_eq_of_indepCoord hζd hζind y t]) z (2 * r)
  obtain ⟨C, hC0, hC⟩ := exists_bound_on_cylinder (j := j)
    (f := fun y => γ y - γ z) (hγ.continuous.sub continuous_const)
    (fun y t => by simp only; rw [hind y t]) z (2 * r)
  refine ⟨fun y => ζ y * (γ y - γ z) + γ z, A + C * B, ?_, ?_, ?_, ?_⟩
  · exact (((hζsmooth.of_le (by exact_mod_cast le_top)).mul
      (hγ.sub contDiff_const)).add contDiff_const)
  · intro y t
    simp only
    rw [hζind y t, hind y t]
  · intro k y
    have hderiv : partialD k (fun w => ζ w * (γ w - γ z) + γ z) y
        = ζ y * partialD k γ y + (γ y - γ z) * partialD k ζ y := by
      have h1 : HasFDerivAt (fun w => ζ w * (γ w - γ z) + γ z)
          (ζ y • fderiv ℝ γ y + (γ y - γ z) • fderiv ℝ ζ y) y := by
        have hsub : HasFDerivAt (fun w => γ w - γ z) (fderiv ℝ γ y) y :=
          ((hγd y).hasFDerivAt).sub_const _
        exact ((hζd y).hasFDerivAt.mul hsub).add_const (γ z)
      rw [partialD, h1.fderiv]
      simp [partialD]
    rw [hderiv]
    by_cases hy : 2 * r < ‖tangential j y - tangential j z‖
    · obtain ⟨hz1, hz2⟩ := hζzero y hy
      have hpz : partialD k ζ y = 0 := by rw [partialD, hz2]; rfl
      rw [hz1, hpz, zero_mul, mul_zero, add_zero, norm_zero]
      positivity
    · replace hy : ‖tangential j y - tangential j z‖ ≤ 2 * r := not_lt.mp hy
      have h1 : ‖ζ y * partialD k γ y‖ ≤ A := by
        rw [norm_mul]
        calc ‖ζ y‖ * ‖partialD k γ y‖ ≤ 1 * ‖fderiv ℝ γ y‖ := by
              refine mul_le_mul ?_ (norm_partialD_le_fderiv k y) (norm_nonneg _) zero_le_one
              rw [Real.norm_eq_abs, abs_of_nonneg (hζ01 y).2]
              exact (hζ01 y).1
          _ = ‖fderiv ℝ γ y‖ := one_mul _
          _ ≤ A := by simpa using hA y hy
      have h2 : ‖(γ y - γ z) * partialD k ζ y‖ ≤ C * B := by
        rw [norm_mul]
        exact mul_le_mul (by simpa using hC y hy)
          ((norm_partialD_le_fderiv k y).trans (by simpa using hB y hy)) (norm_nonneg _) hC0
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
  · ext y
    simp only [Set.mem_inter_iff, aboveGraph, Set.mem_ofPred_eq, and_congr_left_iff]
    intro hy
    rw [hζone y hy]
    constructor <;> intro h <;> linarith [h]

/-- An isometry pulls a ball about an image point back to the ball about the point. -/
theorem preimage_motion_ball
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) :
    (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' ball (e x) r = ball x r := by
  ext y
  simp only [Set.mem_preimage, mem_ball, e.dist_map]

/-! ### The boundary chart -/

/-- **Boundary chart of class `C¹`.** The isometry is the relabelling and reorientation of the
axes, the direction is the coordinate the graph is taken in, and the radius is the size of the
neighbourhood the description covers. -/
structure C1Chart (d : ℕ) where
  /-- The relabelling and reorientation of the coordinate axes. -/
  motion : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)
  /-- The coordinate the graph is taken in. -/
  dir : Fin d
  /-- The graph, which depends on the coordinates other than `dir`. -/
  graph : EuclideanSpace ℝ (Fin d) → ℝ
  /-- The radius of the neighbourhood the chart describes. -/
  radius : ℝ
  /-- The neighbourhood is nonempty. -/
  radius_pos : 0 < radius
  /-- The graph is of class `C¹`. -/
  graph_contDiff : ContDiff ℝ 1 graph
  /-- The graph does not depend on the coordinate it is a graph in. -/
  graph_indep : IndepCoord dir graph

namespace C1Chart

variable (c : C1Chart d)

/-- The region the chart describes, in the coordinates the chart puts the domain in. -/
def region : Set (EuclideanSpace ℝ (Fin d)) := aboveGraph c.dir c.graph

/-- **Description of `Ω` near `x` by the chart.** After the rigid motion, the domain and the
region above the graph agree on the ball of the chart's radius. -/
def Fits (Ω : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) : Prop :=
  c.motion '' Ω ∩ ball (c.motion x) c.radius = c.region ∩ ball (c.motion x) c.radius

/-- **Chart read in the original coordinates.** On the ball about `x`, the domain agrees
with the region above the graph pulled back through the motion. -/
theorem fits_ball {Ω : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (h : c.Fits Ω x) :
    Ω ∩ ball x c.radius
      = (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' c.region
        ∩ ball x c.radius := by
  have himg := congrArg (fun s =>
    (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' s) h
  simpa [Set.preimage_inter, Set.preimage_image_eq _ c.motion.injective,
    preimage_motion_ball] using himg

/-- The graph is differentiable, being of class `C¹`. -/
theorem graph_differentiable : Differentiable ℝ c.graph :=
  c.graph_contDiff.differentiable (by simp)

/-- The region the chart describes is open. -/
theorem isOpen_region : IsOpen c.region :=
  isOpen_aboveGraph c.graph_differentiable.continuous

/-- **Every chart admits a graph of bounded gradient describing the same region on its ball.**
The chart itself asks for no bound, as Evans' definition does not. -/
theorem exists_bounded_graph (z : EuclideanSpace ℝ (Fin d)) :
    ∃ (γ' : EuclideanSpace ℝ (Fin d) → ℝ) (M : ℝ), ContDiff ℝ 1 γ' ∧ IndepCoord c.dir γ' ∧
      (∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)), ‖partialD k γ' y‖ ≤ M) ∧
      aboveGraph c.dir γ' ∩ ball z c.radius = c.region ∩ ball z c.radius :=
  EllipticPdes.Extension.exists_bounded_graph c.graph_contDiff c.graph_indep z c.radius_pos

end C1Chart

/-- **`Ω` has `C¹` boundary.** Every boundary point admits a chart, which is the hypothesis of
Guo's Theorem III.2.2 and of Evans' §5.4 Theorem 1. -/
def HasC1Boundary (Ω : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ x ∈ frontier Ω, ∃ c : C1Chart d, c.Fits Ω x

/-! ### Instances and consequences -/

/-- The chart taken by a region that is already the region above a graph: the identity motion,
and any radius. -/
def graphChart {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ} (hγ : ContDiff ℝ 1 γ)
    (hind : IndepCoord j γ) : C1Chart d where
  motion := LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))
  dir := j
  graph := γ
  radius := 1
  radius_pos := one_pos
  graph_contDiff := hγ
  graph_indep := hind

/-- **`C¹` boundary of the region above a graph**, the identity being a chart at every point. -/
theorem hasC1Boundary_aboveGraph {j : Fin d} {γ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hind : IndepCoord j γ) : HasC1Boundary (aboveGraph j γ) := by
  intro x _
  refine ⟨graphChart hγ hind, ?_⟩
  change (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin d))) '' aboveGraph j γ ∩ _
    = aboveGraph j γ ∩ _
  rw [LinearIsometryEquiv.coe_refl, Set.image_id]

/-- **`C¹` boundary of the half space**, its chart being the zero graph. -/
theorem hasC1Boundary_halfSpace (j : Fin d) : HasC1Boundary (halfSpace j) := by
  have hset : halfSpace j = aboveGraph j fun _ => (0 : ℝ) := rfl
  rw [hset]
  exact hasC1Boundary_aboveGraph contDiff_const fun _ _ => rfl

/-- **Compactness of the boundary of a bounded domain**, which is what a finite subcover of
charts asks for. -/
theorem isCompact_frontier {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Bornology.IsBounded Ω) :
    IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    (hΩ.closure.subset (frontier_subset_closure))

/-- **Finite cover of the boundary by charts.** The boundary of a bounded domain is compact
and a domain with `C¹` boundary has a chart at each of its points, so finitely many of the
charts' balls cover it. The chart is returned as a function on the whole space, which asks the
dimension to be positive: in dimension zero there is no direction for a graph to be taken in,
and no chart at all. -/
theorem exists_finite_chart_cover (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) :
    ∃ (F : Finset (EuclideanSpace ℝ (Fin d)))
      (c : EuclideanSpace ℝ (Fin d) → C1Chart d),
      (∀ x ∈ F, x ∈ frontier Ω) ∧ (∀ x ∈ F, (c x).Fits Ω x) ∧
      frontier Ω ⊆ ⋃ x ∈ F, ball x (c x).radius := by
  classical
  choose C hC using hC1
  -- a chart to fall back on away from the boundary, which needs a direction to exist
  set cjunk : C1Chart d :=
    graphChart (j := ⟨0, hd⟩) (γ := fun _ => (0 : ℝ)) contDiff_const (fun _ _ => rfl) with hjunk
  set c : EuclideanSpace ℝ (Fin d) → C1Chart d :=
    fun x => if hx : x ∈ frontier Ω then C x hx else cjunk with hcdef
  have hcfits : ∀ x (hx : x ∈ frontier Ω), (c x).Fits Ω x := by
    intro x hx
    rw [hcdef]
    simp only [dite_eq_left hx]
    exact hC x hx
  have hcover : frontier Ω ⊆ ⋃ x ∈ frontier Ω, ball x (c x).radius := fun x hx =>
    Set.mem_biUnion hx (mem_ball_self (c x).radius_pos)
  obtain ⟨t, hts, htfin, htcover⟩ :=
    (isCompact_frontier hΩ).elim_finite_subcover_image
      (fun x _ => isOpen_ball) hcover
  refine ⟨htfin.toFinset, c, ?_, ?_, ?_⟩
  · intro x hx
    exact hts (htfin.mem_toFinset.mp hx)
  · intro x hx
    exact hcfits x (hts (htfin.mem_toFinset.mp hx))
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (htcover hy)
    exact Set.mem_biUnion (htfin.mem_toFinset.mpr hx) hyx

end EllipticPdes.Extension
