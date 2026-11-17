/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Convex.Extrema
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Boundary maxima of convex functions

A continuous convex function on the closure of a bounded open convex domain
is bounded above by any upper bound on its frontier. This pure real-normed
statement supplies the upper boundary control for Alexandrov Dirichlet
approximation (Gutierrez 2001, Section 1.6); it uses no Monge–Ampere equation
or differentiability. The maximum statement requires positive dimension.

The actual interior strong-maximum rigidity is shared with UNIT Dirichlet
negativity. That pure rigidity requires only a real normed space and an actual
interior maximum; the frontier bound retains its finite-dimensional scope.

For an open convex set, an open ball in its closure contains every smaller closed ball in the set
itself. This normed-space interior step is shared by the affine-normalized section estimates.
-/

@[expose] public section

namespace FunctionalInequalities.Analysis
open Set Metric Topology

/-- A smaller closed ball lies in an open convex set when the larger open ball lies in its
closure. No dimension, completeness, inner product or sign of the radii is required. -/
theorem closedBall_subset_of_ball_subset_closure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty)
    {x : E} {r R : ℝ} (hrR : r < R) (hball : ball x R ⊆ closure s) :
    closedBall x r ⊆ s := by
  have hint : interior (closure s) = s := by
    rw [hc.interior_closure_eq_interior_of_nonempty_interior
      (by rwa [hs.interior_eq]), hs.interior_eq]
  exact (closedBall_subset_ball hrR).trans ((interior_maximal hball isOpen_ball).trans hint.le)

section BoundedFrontier
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]

/-- A nonempty bounded subset of a nontrivial real normed space has nonempty
frontier. Openness, finite dimension and convexity are unnecessary. -/
theorem frontier_nonempty_of_isBounded {Ω : Set F} (hb : Bornology.IsBounded Ω) {x : F}
    (hx : x ∈ Ω) : (frontier Ω).Nonempty := by
  have hnot : Ω ≠ Set.univ := by
    intro h
    exact NormedSpace.unbounded_univ ℝ F (h ▸ hb)
  exact nonempty_frontier_iff.mpr ⟨⟨x, hx⟩, hnot⟩

end BoundedFrontier

/-- A real interior maximum of a convex function forces constancy on its whole
convex domain. The smaller neighbourhood need only be open. No continuity,
completeness, dimension, inner product, nontriviality or measure is required. -/
theorem eq_on_of_interior_max_of_convexOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {D Ω : Set E} (hu : ConvexOn ℝ D u) (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) {m : E}
    (hmΩ : m ∈ Ω) (hmax : IsMaxOn u D m) : ∀ y ∈ D, u y = u m := by
  intro y hy
  by_cases hym : y = m
  · simp [hym]
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ m hmΩ
    have hd : 0 < dist m y := dist_pos.mpr (Ne.symm hym)
    let t : ℝ := r / (2 * dist m y)
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have htd : t * dist m y = r / 2 := by
      dsimp [t]
      field_simp [ne_of_gt hd]
    have htdr : t * dist m y < r := by
      rw [htd]
      linarith
    let z : E := m + t • (m - y)
    have hdist : dist z m < r := by
      calc
        dist z m = ‖t • (m - y)‖ := by
          rw [dist_eq_norm]
          change ‖(m + t • (m - y)) - m‖ = ‖t • (m - y)‖
          congr 1
          abel
        _ = t * ‖m - y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        _ = t * dist m y := by rw [dist_eq_norm]
        _ < r := htdr
    have hz : z ∈ Ω := hball (Metric.mem_ball.mpr hdist)
    let α : ℝ := t / (1 + t)
    let β : ℝ := 1 / (1 + t)
    have hden : 0 < 1 + t := by linarith
    have hα : 0 < α := by
      dsimp [α]
      positivity
    have hβ : 0 < β := by
      dsimp [β]
      positivity
    have hα0 : 0 ≤ α := hα.le
    have hβ0 : 0 ≤ β := hβ.le
    have hαβ : α + β = 1 := by
      change t / (1 + t) + 1 / (1 + t) = 1
      field_simp [ne_of_gt hden]
      ring
    have hbt : β * t = α := by
      change (1 / (1 + t)) * t = t / (1 + t)
      ring
    have hmrep : α • y + β • z = m := by
      change α • y + β • (m + t • (m - y)) = m
      calc
        _ = (α - β * t) • y + (β + β * t) • m := by module
        _ = m := by rw [hbt, sub_self, zero_smul, zero_add, add_comm β α, hαβ, one_smul]
    have hconv : u (α • y + β • z) ≤ α • u y + β • u z := hu.2 hy (hΩD hz) hα0 hβ0 hαβ
    have hcombo : α • y + β • z ∈ D := hu.1 hy (hΩD hz) hα0 hβ0 hαβ
    have hmy : u y ≤ u m := hmax hy
    have hmz : u z ≤ u m := hmax (hΩD hz)
    have hcombo_max : u (α • y + β • z) ≤ u m := hmax hcombo
    rw [hmrep] at hconv hcombo_max
    have hconv' : u m ≤ α * u y + β * u z := by simpa only [smul_eq_mul] using hconv
    have hβbound := mul_le_mul_of_nonneg_left hmz hβ.le
    have hsum : α * u m + β * u m = u m := by rw [← add_mul, hαβ, one_mul]
    have hmul : α * u m ≤ α * u y := by nlinarith only [hconv', hβbound, hsum]
    exact le_antisymm hmy (by nlinarith only [hα, hmul])
/-- A frontier upper bound controls a closure-continuous convex function on
an entire bounded open convex domain. The proof uses an actual compact maximum
and an interior reflected point, without differentiability or a MA premise. -/
theorem le_on_closure_of_le_frontier_of_convexOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩconv : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {u : E → ℝ}
    (hu : ConvexOn ℝ (closure Ω) u) (huc : ContinuousOn u (closure Ω)) {b : ℝ}
    (hfr : ∀ x ∈ frontier Ω, u x ≤ b) : ∀ x ∈ closure Ω, u x ≤ b := by
  classical
  by_cases hΩne : Ω.Nonempty
  · obtain ⟨q, hq⟩ := hΩne
    have hcompact : IsCompact (closure Ω) := hb.isCompact_closure
    obtain ⟨m, hm, hmax⟩ := hcompact.exists_isMaxOn ⟨q, subset_closure hq⟩ huc
    obtain ⟨w, hw⟩ := frontier_nonempty_of_isBounded hb hq
    have hΩclconv : Convex ℝ (closure Ω) := hΩconv.closure
    have hmb : u m ≤ b := by
      by_cases hm_int : m ∈ interior Ω
      · have hmΩ : m ∈ Ω := interior_subset hm_int
        have hall : ∀ y ∈ closure Ω, u y = u m :=
          eq_on_of_interior_max_of_convexOn ⟨hΩclconv, hu.2⟩ hΩ subset_closure hmΩ hmax
        calc
          u m = u w := (hall w (frontier_subset_closure hw)).symm
          _ ≤ b := hfr w hw
      · have hmfr : m ∈ frontier Ω := by
          change m ∈ closure Ω \ interior Ω
          exact ⟨hm, hm_int⟩
        exact hfr m hmfr
    intro x hx
    exact (hmax hx).trans hmb
  · have hΩempty : Ω = ∅ := not_nonempty_iff_eq_empty.mp hΩne
    subst Ω
    simp

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set
section BoundedDomainGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]

/-- In a nontrivial real normed space, the distance of a point of a bounded
set to its frontier is at most the set's diameter. No finite dimension,
inner product, openness, convexity or measurability is required. -/
theorem infDist_frontier_le_diam_of_mem {Ω : Set F} (hb : Bornology.IsBounded Ω) {x : F}
    (hx : x ∈ Ω) : Metric.infDist x (frontier Ω) ≤ Metric.diam Ω := by
  obtain ⟨y, hy⟩ := frontier_nonempty_of_isBounded hb hx
  calc
    Metric.infDist x (frontier Ω) ≤ dist x y := Metric.infDist_le_dist_of_mem hy
    _ ≤ Metric.diam Ω := by
      simpa only [Metric.diam_closure] using
        Metric.dist_le_diam_of_mem hb.closure (subset_closure hx) (frontier_subset_closure hy)

end BoundedDomainGeometry
end FunctionalInequalities.Analysis
