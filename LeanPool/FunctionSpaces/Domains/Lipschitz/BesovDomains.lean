/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.HalfSpace
public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphStraightening
public import LeanPool.FunctionSpaces.Domains.Traces.GraphTraceCharts
public import LeanPool.FunctionSpaces.Domains.Lipschitz.SurfaceMeasure
public import LeanPool.FunctionSpaces.Domains.Lipschitz.ConvexDomains
public import Mathlib.Analysis.Convex.Measure

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov domains: graph domains, the quadrant, bounded domains

The results rest on the extension property (`Rd.HasBesovExtension`) of Lipschitz graph domains
(`Rd.LipschitzGraph.hasBesovExtension`) and on Besov domains up to null sets
(`Rd.BesovDomain.of_ae_eq`).

**Lipschitz graph domains.** Their graph `{φ = ⟪·, e⟫}` is a null set
(`Rd.LipschitzGraph.volume_graph`): it lies in the image of the hyperplane `e^⊥` under the
Lipschitz map `y ↦ y + φ(y) e`. So is their frontier (`Rd.LipschitzGraph.volume_frontier_domain`).
Hence the closure of a graph domain with convex `φ` is a Besov domain
(`Rd.BesovDomain.closure_lipschitzGraph`).

**The quadrant** `{y : ∀ i, 0 < y_i}` in `ℝ^n` is a single Lipschitz graph domain, near the corner
as well, in the diagonal direction (`Rd.LipschitzGraph.quadrant`): with the diagonal unit vector
`e = (1, …, 1)/√n` (`Rd.quadrantDir`) and the smallest coordinate `m(y) = min_i y_i`
(`Rd.quadrantMin`), the graph function `φ(y) = ⟪y, e⟫ - √n m(y)` is `(1 + √n)`-Lipschitz and
constant along `e`, and `φ(y) < ⟪y, e⟫` exactly when `m(y) > 0`. The closed quadrant differs from
the open one by its frontier, a null set (Mathlib's `Convex.addHaar_frontier`), so the range of
Mathlib's model with corners `modelWithCornersEuclideanQuadrant n` is a Besov domain
(`Rd.BesovDomain.range_euclideanQuadrant`). The results on Besov spaces on compact manifolds
therefore hold for manifolds with corners.

**Bounded Lipschitz domains** have the property (`Rd.BoundedLipschitzDomain.hasBesovExtension`),
by the extension with a bound (`Rd.BoundedLipschitzDomain.exists_besov_extension_le`), so the order
of the differences does not matter on them (`Rd.BoundedLipschitzDomain.modNormOn_order_le`). Their
frontier is a null set, so their closure agrees with them up to a null set
(`Rd.BoundedLipschitzDomain.closure_ae_eq`), and the closure of a nonempty convex one is a Besov
domain (`Rd.BesovDomain.closure_boundedLipschitzDomain`). Bounded open convex sets are bounded
Lipschitz domains, so the closure of every nonempty bounded open convex set is a Besov domain
(`Rd.BesovDomain.closure_of_convex`): closed balls of positive radius
(`Rd.BesovDomain.closedBall`) and the closed unit cube `[0, 1]^n`
(`Rd.BesovDomain.closedUnitCube`) are examples.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric Set
open scoped ENNReal NNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Lipschitz graph domains -/

namespace LipschitzGraph

variable (G : LipschitzGraph V)

/-- **The graph of a Lipschitz graph domain is a null set**: `{x : φ(x) = ⟪x, e⟫}` lies in a
Lipschitz image of the null hyperplane `e^⊥` (`Rd.LipschitzGraph.graph_subset_image_unflatten`,
`Rd.volume_image_eq_zero_of_lipschitzWith`). -/
theorem volume_graph : volume {x | G.phi x = inner ℝ x G.e} = 0 :=
  measure_mono_null G.graph_subset_image_unflatten
    (volume_image_eq_zero_of_lipschitzWith rfl G.lipschitzWith_unflatten
      (volume_orthogonal_singleton_eq_zero G.e_ne_zero))

/-- **The boundary of a Lipschitz graph domain is a null set**: the frontier of
`{x : φ(x) < ⟪x, e⟫}` lies in the graph (Mathlib's `frontier_lt_subset_eq`), a null set
(`Rd.LipschitzGraph.volume_graph`). -/
theorem volume_frontier_domain : volume (frontier G.domain) = 0 :=
  measure_mono_null (frontier_lt_subset_eq G.continuous_phi (continuous_id.inner continuous_const))
    G.volume_graph

/-- **The closure of a Lipschitz graph domain is the domain up to a null set**, since the frontier
is a null set (`Rd.LipschitzGraph.volume_frontier_domain`, Mathlib's
`closure_ae_eq_of_null_frontier`). -/
theorem closure_domain_ae_eq : closure G.domain =ᵐ[volume] G.domain :=
  closure_ae_eq_of_null_frontier G.volume_frontier_domain

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A graph domain with convex graph function is convex**: `{x : φ(x) < ⟪x, e⟫}` is a strict
sublevel set of the convex function `φ - ⟪e, ·⟫` (Mathlib's `ConvexOn.convex_lt`), convex since
`⟪e, ·⟫` is linear (Mathlib's `LinearMap.concaveOn`). -/
theorem convex_domain (hφ : ConvexOn ℝ univ G.phi) : Convex ℝ G.domain := by
  have h := (hφ.sub ((innerₛₗ ℝ G.e).concaveOn convex_univ)).convex_lt 0
  convert h using 1
  ext x
  simp [LipschitzGraph.domain, real_inner_comm, sub_neg]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **A Lipschitz graph domain is nonempty**: it contains `(φ(0) + 1) e`, since `φ` is constant
along `e`. -/
theorem domain_nonempty : G.domain.Nonempty := by
  refine ⟨(G.phi 0 + 1) • G.e, ?_⟩
  change G.phi ((G.phi 0 + 1) • G.e) < inner ℝ ((G.phi 0 + 1) • G.e) G.e
  have h := G.const 0 (G.phi 0 + 1)
  rw [zero_add] at h
  rw [h, real_inner_smul_left, real_inner_self_eq_norm_sq, G.norm_e]
  linarith

end LipschitzGraph

/-- **The closure of a convex Lipschitz graph domain is a Besov domain**: for a convex graph
function `φ` the closure of `{x : φ(x) < ⟪x, e⟫}` is closed and convex, contains the open domain in
its interior, and agrees with the domain up to the null graph. Examples are half-spaces, the
quadrant (`Rd.LipschitzGraph.quadrant`), the circular cones `{x : M ‖x - ⟪x, e⟫ e‖ < ⟪x, e⟫}` and
the epigraphs of convex Lipschitz functions. -/
theorem BesovDomain.closure_lipschitzGraph (G : LipschitzGraph V)
    (hφ : ConvexOn ℝ Set.univ G.phi) : BesovDomain (closure G.domain) :=
  of_ae_eq (G.convex_domain hφ).closure isClosed_closure
    (G.domain_nonempty.mono G.isOpen_domain.subset_interior_closure) G.hasBesovExtension
    G.closure_domain_ae_eq

/-! ### The quadrant -/

section Quadrant

variable (n : ℕ)

/-- The **diagonal direction** `(1, …, 1)/√n` of `ℝ^n`. -/
noncomputable def quadrantDir : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun _ => (Real.sqrt n)⁻¹

/-- Each coordinate of the diagonal direction is `1/√n`. -/
theorem quadrantDir_apply (i : Fin n) : quadrantDir n i = (Real.sqrt n)⁻¹ := rfl

/-- `⟪y, (1, …, 1)/√n⟫ = (y_1 + … + y_n)/√n`. -/
theorem inner_quadrantDir (y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y (quadrantDir n) = (Real.sqrt n)⁻¹ * ∑ i, y i := by
  rw [PiLp.inner_apply, Finset.mul_sum]
  simp [quadrantDir_apply]

section Positive

variable [NeZero n]

/-- The diagonal direction is a unit vector. -/
theorem norm_quadrantDir : ‖quadrantDir n‖ = 1 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  rw [EuclideanSpace.norm_eq]
  simp [quadrantDir_apply, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), hn]

/-- The **smallest coordinate** `min_i y_i` of `y ∈ ℝ^n`, for `n ≥ 1`. -/
noncomputable def quadrantMin (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => y i

/-- The smallest coordinate is at most every coordinate. -/
theorem quadrantMin_le (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) : quadrantMin n y ≤ y i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- `c ≤ min_i y_i` iff `c ≤ y_i` for every `i`. -/
theorem le_quadrantMin_iff {y : EuclideanSpace ℝ (Fin n)} {c : ℝ} :
    c ≤ quadrantMin n y ↔ ∀ i, c ≤ y i := by
  simp [quadrantMin, Finset.le_inf'_iff]

/-- `c < min_i y_i` iff `c < y_i` for every `i`. -/
theorem lt_quadrantMin_iff {y : EuclideanSpace ℝ (Fin n)} {c : ℝ} :
    c < quadrantMin n y ↔ ∀ i, c < y i := by
  simp [quadrantMin, Finset.lt_inf'_iff]

/-- **The smallest coordinate along the diagonal**: `m(y + t e) = m(y) + t/√n`, since every
coordinate grows by `t/√n`. -/
theorem quadrantMin_add_smul (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    quadrantMin n (y + t • quadrantDir n) = quadrantMin n y + t / Real.sqrt n := by
  have hc : ∀ i, (y + t • quadrantDir n) i = y i + t / Real.sqrt n := fun i => by
    rw [PiLp.add_apply, PiLp.smul_apply, quadrantDir_apply, smul_eq_mul, div_eq_mul_inv]
  refine le_antisymm ?_ ((le_quadrantMin_iff n).2 fun i => ?_)
  · have h : quadrantMin n (y + t • quadrantDir n) - t / Real.sqrt n ≤ quadrantMin n y :=
      (le_quadrantMin_iff n).2 fun i => by
        linarith [quadrantMin_le n (y + t • quadrantDir n) i, hc i]
    linarith
  · rw [hc i]
    linarith [quadrantMin_le n y i]

/-- `min_i y_i ≤ min_i z_i + ‖y - z‖`, since `y_i ≤ z_i + |y_i - z_i|` and every coordinate is
at most the Euclidean norm (Mathlib's `PiLp.norm_apply_le`). -/
theorem quadrantMin_le_add_norm (y z : EuclideanSpace ℝ (Fin n)) :
    quadrantMin n y ≤ quadrantMin n z + ‖y - z‖ := by
  have h : quadrantMin n y - ‖y - z‖ ≤ quadrantMin n z := (le_quadrantMin_iff n).2 fun i => by
    have h1 : |y i - z i| ≤ ‖y - z‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (y - z) i
    linarith [quadrantMin_le n y i, le_abs_self (y i - z i)]
  linarith

/-- **The smallest coordinate is `1`-Lipschitz**: `|m(y) - m(z)| ≤ ‖y - z‖`. -/
theorem abs_quadrantMin_sub_le (y z : EuclideanSpace ℝ (Fin n)) :
    |quadrantMin n y - quadrantMin n z| ≤ ‖y - z‖ :=
  abs_sub_le_iff.2 ⟨by linarith [quadrantMin_le_add_norm n y z],
    by linarith [quadrantMin_le_add_norm n z y, norm_sub_rev y z]⟩

/-- **The smallest coordinate is concave**, as a minimum of linear functions. -/
theorem concaveOn_quadrantMin : ConcaveOn ℝ univ (quadrantMin n) := by
  refine ⟨convex_univ, fun y _ z _ a b ha hb _ => (le_quadrantMin_iff n).2 fun i => ?_⟩
  rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (quadrantMin_le n y i) ha)
    (mul_le_mul_of_nonneg_left (quadrantMin_le n z i) hb)

/-- **The quadrant as a Lipschitz graph domain**: the direction is the diagonal
`e = (1, …, 1)/√n`, the graph function `φ(y) = ⟪y, e⟫ - √n min_i y_i` is `(1 + √n)`-Lipschitz and
constant along `e`. Its domain is the open quadrant (`Rd.LipschitzGraph.quadrant_domain`). -/
noncomputable def LipschitzGraph.quadrant : LipschitzGraph (EuclideanSpace ℝ (Fin n)) where
  e := quadrantDir n
  norm_e := norm_quadrantDir n
  M := 1 + Real.sqrt n
  M_nonneg := by positivity
  phi y := inner ℝ y (quadrantDir n) - Real.sqrt n * quadrantMin n y
  lipschitz y z := by
    have h1 : |inner ℝ (y - z) (quadrantDir n)| ≤ ‖y - z‖ := by
      simpa [norm_quadrantDir] using abs_real_inner_le_norm (y - z) (quadrantDir n)
    have h2 : Real.sqrt n * |quadrantMin n y - quadrantMin n z| ≤ Real.sqrt n * ‖y - z‖ :=
      mul_le_mul_of_nonneg_left (abs_quadrantMin_sub_le n y z) (Real.sqrt_nonneg _)
    rw [inner_sub_left] at h1
    calc |inner ℝ y (quadrantDir n) - Real.sqrt n * quadrantMin n y -
          (inner ℝ z (quadrantDir n) - Real.sqrt n * quadrantMin n z)|
        = |(inner ℝ y (quadrantDir n) - inner ℝ z (quadrantDir n)) -
            Real.sqrt n * (quadrantMin n y - quadrantMin n z)| := by ring_nf
      _ ≤ |inner ℝ y (quadrantDir n) - inner ℝ z (quadrantDir n)| +
            |Real.sqrt n * (quadrantMin n y - quadrantMin n z)| := abs_sub _ _
      _ ≤ (1 + Real.sqrt n) * ‖y - z‖ := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          linarith
  const y t := by
    have hn : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (NeZero.pos n))
    rw [quadrantMin_add_smul, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_quadrantDir, mul_add, mul_div_cancel₀ t hn]
    ring

/-- **The domain of the quadrant graph is the open quadrant** `{y : ∀ i, 0 < y_i}`:
`φ(y) < ⟪y, e⟫` iff `√n min_i y_i > 0`. -/
theorem LipschitzGraph.quadrant_domain :
    (LipschitzGraph.quadrant n).domain = {y | ∀ i, 0 < y i} := by
  have hn : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 (NeZero.pos n))
  ext y
  change inner ℝ y (quadrantDir n) - Real.sqrt n * quadrantMin n y < inner ℝ y (quadrantDir n) ↔ _
  rw [sub_lt_self_iff, mul_pos_iff_of_pos_left hn, lt_quadrantMin_iff]
  rfl

/-- **The graph function of the quadrant is convex**: it is a linear function, convex by Mathlib's
`LinearMap.convexOn`, minus `√n` times the concave smallest coordinate
(`Rd.concaveOn_quadrantMin`). -/
theorem LipschitzGraph.convexOn_quadrant_phi : ConvexOn ℝ univ (LipschitzGraph.quadrant n).phi := by
  have hlin : ConvexOn ℝ univ fun y : EuclideanSpace ℝ (Fin n) => inner ℝ y (quadrantDir n) := by
    convert (innerₛₗ ℝ (quadrantDir n)).convexOn convex_univ using 1
    funext y
    simp [real_inner_comm]
  exact hlin.sub ((concaveOn_quadrantMin n).smul (Real.sqrt_nonneg _))

end Positive

/-- **The closed quadrant is the open quadrant up to a null set**: the open quadrant is the interior
of the closed one (Mathlib's `interior_quadrant`), and the frontier of a convex set is a
null set (Mathlib's `Convex.addHaar_frontier`). -/
theorem quadrant_ae_eq :
    {y : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ y i} =ᵐ[volume] {y | ∀ i, 0 < y i} := by
  rw [← interior_quadrant (n := n) 2 0]
  exact (interior_ae_eq_of_null_frontier (EuclideanQuadrant.convex.addHaar_frontier volume)).symm

/-- **The quadrant model of manifolds with corners is a Besov domain**: the range
`{y : ∀ i, 0 ≤ y_i}` of `modelWithCornersEuclideanQuadrant n` agrees up to a null set with the open
quadrant, a Lipschitz graph domain (`Rd.LipschitzGraph.quadrant`). For `n = 0` the range is the
whole (one-point) space. -/
instance BesovDomain.range_euclideanQuadrant :
    BesovDomain (range (modelWithCornersEuclideanQuadrant n)) := by
  have hrange : range (modelWithCornersEuclideanQuadrant n) = {y | ∀ i, 0 ≤ y i} :=
    _root_.range_euclideanQuadrant n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : {y : EuclideanSpace ℝ (Fin 0) | ∀ i, 0 ≤ y i} = Set.univ :=
      eq_univ_of_forall fun _ i => Fin.elim0 i
    rw [hrange, h]
    exact BesovDomain.univ
  · have : NeZero n := ⟨hn.ne'⟩
    refine BesovDomain.range_of_ae_eq _ (LipschitzGraph.quadrant n).hasBesovExtension ?_
    rw [hrange, LipschitzGraph.quadrant_domain]
    exact quadrant_ae_eq n

end Quadrant

/-! ### Bounded Lipschitz domains -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **Bounded Lipschitz domains have the extension property**
(`Rd.BoundedLipschitzDomain.exists_besov_extension_le`). -/
theorem hasBesovExtension : HasBesovExtension Ω.measurableSet := by
  intro p _ hp r s hs hsr q hq
  exact Ω.exists_besov_extension_le hp hs hsr hq

/-- **The closure of a bounded Lipschitz domain is the domain up to a null set**, since the
frontier is a null set (`Rd.BoundedLipschitzDomain.volume_frontier`, Mathlib's
`closure_ae_eq_of_null_frontier`). -/
theorem closure_ae_eq : closure Ω.carrier =ᵐ[volume] Ω.carrier :=
  closure_ae_eq_of_null_frontier Ω.volume_frontier

/-- **The order of the differences does not matter on a bounded Lipschitz domain**
(DeVore–Sharpley): for `1 ≤ p < ∞`, `0 < s < r`, `s < r'` and `1 ≤ q ≤ ∞` there is `C < ∞` with
`N_Ω(f; r') ≤ C N_Ω(f; r)` whenever `N_Ω(f; r) < ∞`, where
`N_Ω(f; r) = ‖1_Ω f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), Ω)_p)_k‖_{ℓ_q}`. This holds for every bounded
Lipschitz domain, convex or not (`Rd.HasBesovExtension.modNormOn_order_le`). -/
theorem modNormOn_order_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) {r r' : ℕ} {s : ℝ}
    (hs : 0 < s) (hsr : s < r) (hsr' : s < r') {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V),
      modNormOn Ω.measurableSet r s q f < ∞ →
      modNormOn Ω.measurableSet r' s q f ≤ C * modNormOn Ω.measurableSet r s q f :=
  Ω.hasBesovExtension.modNormOn_order_le hp hs hsr hsr' hq

end BoundedLipschitzDomain

/-- **The closure of a nonempty convex bounded Lipschitz domain is a Besov domain**: it is closed
and convex, contains the nonempty open domain in its interior, and agrees with the domain up to the
null frontier (`Rd.BoundedLipschitzDomain.closure_ae_eq`). -/
theorem BesovDomain.closure_boundedLipschitzDomain (Ω : BoundedLipschitzDomain V)
    (hc : Convex ℝ Ω.carrier) (hne : Ω.carrier.Nonempty) : BesovDomain (closure Ω.carrier) :=
  of_ae_eq hc.closure isClosed_closure (hne.mono Ω.isOpen.subset_interior_closure)
    Ω.hasBesovExtension Ω.closure_ae_eq

/-- **The closure of a nonempty bounded open convex set is a Besov domain**: for every nonempty
bounded open convex set `U`, the closure `Ū` is a Besov domain, since `U` is a bounded Lipschitz
domain (`Rd.BoundedLipschitzDomain.ofConvex`; Grisvard, Corollary 1.2.2.3). -/
theorem BesovDomain.closure_of_convex {U : Set V} (hc : Convex ℝ U) (ho : IsOpen U)
    (hb : Bornology.IsBounded U) (hne : U.Nonempty) : BesovDomain (closure U) :=
  closure_boundedLipschitzDomain (BoundedLipschitzDomain.ofConvex hc ho hb) hc hne

/-- **Closed balls are Besov domains**: for every `c` and `R > 0` the closed ball `closedBall(c,
R)` is
the closure of the open ball (Mathlib's `closure_ball`), a nonempty bounded open convex set
(`Rd.BesovDomain.closure_of_convex`). -/
theorem BesovDomain.closedBall (c : V) {R : ℝ} (hR : 0 < R) :
    BesovDomain (Metric.closedBall c R) := by
  rw [← closure_ball c hR.ne']
  exact closure_of_convex (convex_ball c R) isOpen_ball isBounded_ball (nonempty_ball.2 hR)

/-- **The closed unit cube is a Besov domain**: `[0, 1]^n ⊆ ℝ^n` is the closure of the open unit
cube (`Rd.closure_unitCube`), a nonempty bounded open convex set
(`Rd.BoundedLipschitzDomain.unitCube`, `Rd.BesovDomain.closure_boundedLipschitzDomain`). -/
instance BesovDomain.closedUnitCube (n : ℕ) :
    BesovDomain {x : EuclideanSpace ℝ (Fin n) | ∀ i, x i ∈ Icc (0 : ℝ) 1} := by
  rw [← closure_unitCube n]
  exact closure_boundedLipschitzDomain (BoundedLipschitzDomain.unitCube n) (convex_unitCube n)
    (nonempty_unitCube n)

end Rd
