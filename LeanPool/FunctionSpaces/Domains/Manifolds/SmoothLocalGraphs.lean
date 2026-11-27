/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.LocalLipschitzGraphs
public import LeanPool.FunctionSpaces.Domains.Manifolds.SmoothDomainBesov

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smooth bounded domains from smooth local graphs

A set `Ω ⊆ V` is **smooth near `z`** (`Rd.IsSmoothDomainAt`) if there are `r > 0`, a unit vector
`ν` and a function `φ` on the hyperplane `ν^⊥`, smooth on its ball of radius `r`, with
`Ω ∩ B(z, r) = {x : φ(P(x - z)) < ⟪ν, x - z⟫} ∩ B(z, r)`, `P` the orthogonal projection onto
`ν^⊥`; `Ω` is a **bounded smooth set** (`Rd.IsBoundedSmoothDomain`) if it is open, bounded and
smooth near each point of its frontier.

* A set smooth near `z` is Lipschitz near `z`, since a smooth function is Lipschitz near the
  origin (`Rd.IsSmoothDomainAt.isLipschitzDomainAt`); so bounded smooth sets are bounded
  Lipschitz sets.
* In finite dimension, a function smooth on a ball agrees on the ball of a quarter of the radius
  with a smooth Lipschitz function on the whole space, its product with a smooth bump
  (`Rd.exists_contDiff_lipschitzWith_eqOn_ball`, through `Rd.contDiff_mul_of_tsupport_subset`).
  So being smooth near `z` means agreeing on a ball around `z` with a Lipschitz graph domain with
  smooth graph function (`Rd.isSmoothDomainAt_iff`).
* The charts at the frontier points of a bounded smooth set in `ℝ^n` form a smooth domain with
  carrier `Ω` (`Rd.SmoothDomain.ofIsBoundedSmoothDomain`, through
  `Rd.BoundedLipschitzDomain.ofCharts`), and the carrier of every smooth domain is a bounded
  smooth set (`Rd.isBoundedSmoothDomain_iff_exists`).
* Every open ball is a bounded smooth set (`Rd.isBoundedSmoothDomain_ball`): near a point of its
  sphere it lies above the graph of `y ↦ R - √(R² - ‖y‖²)`, smooth for `‖y‖ < R/2`
  (`Rd.contDiffOn_sphereProfile_norm`). Hence the smooth domain `Rd.SmoothDomain.ball`, whose
  closure is a compact manifold with boundary, with the Besov spaces of
  `Rd.SmoothDomain.memBesov_ball_iff`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal Manifold ContDiff

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The local condition -/

/-- A set `Ω` is **smooth near the point `z`** if there are a radius `r > 0`, a unit vector `ν`
and a function `φ` on the hyperplane `ν^⊥`, smooth on the ball of radius `r` of `ν^⊥`, with
`Ω ∩ B(z, r) = {x : φ(P(x - z)) < ⟪ν, x - z⟫} ∩ B(z, r)`, where `P` is the orthogonal projection
onto `ν^⊥`: near `z`, `Ω` is the region above the graph of `φ` in the direction `ν`. This is the
local condition of Grisvard, Definition 1.2.1.1, with `φ` of class `C^∞`, the rotation of
coordinates replaced by the direction `ν` and balls in place of hypercubes. -/
def IsSmoothDomainAt (Ω : Set V) (z : V) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ ν : V, ‖ν‖ = 1 ∧ ∃ φ : (ℝ ∙ ν)ᗮ → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (ball 0 r) ∧
    Ω ∩ ball z r =
      {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩ ball z r

/-- A **bounded smooth set**: an open bounded set that is smooth near each point of its frontier
(`Rd.IsSmoothDomainAt`), the usual definition of a bounded domain with smooth boundary. In `ℝ^n`
these are exactly the carriers of `Rd.SmoothDomain` (`Rd.isBoundedSmoothDomain_iff_exists`). -/
def IsBoundedSmoothDomain (Ω : Set V) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ ∀ z ∈ frontier Ω, IsSmoothDomainAt Ω z

/-! ### The smooth cut-off -/

/-- The product of a `C^n` function `b` with a function `φ` that is `C^n` on an open set
containing the closed support `tsupport b` is `C^n` on the whole space: near the points of
`tsupport b` both factors are `C^n`, and near the other points the product vanishes (Mathlib's
`notMem_tsupport_iff_eventuallyEq`). This is the flat analogue of Mathlib's
`ContMDiffOn.smul_section_of_tsupport`. -/
theorem contDiff_mul_of_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {b φ : E → ℝ} {U : Set E} (hb : ContDiff ℝ n b) (hU : IsOpen U)
    (hbU : tsupport b ⊆ U) (hφ : ContDiffOn ℝ n φ U) : ContDiff ℝ n (fun x => b x * φ x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport b
  · exact hb.contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds (hbU hx)))
  · have hev : (fun x => b x * φ x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **The smooth cut-off**: a function `φ` smooth on the ball `B(0, r)` of a finite-dimensional
real inner product space agrees on `B(0, r/4)` with a smooth Lipschitz function `ψ` on the whole
space, namely `ψ = b φ` for a smooth bump `b` equal to `1` on `closedBall(0, r/4)` and supported in
`closedBall(0, r/2)`. `ψ` is smooth by `Rd.contDiff_mul_of_tsupport_subset` and has compact
support, so
it is Lipschitz (Mathlib's `ContDiff.lipschitzWith_of_hasCompactSupport`). -/
theorem exists_contDiff_lipschitzWith_eqOn_ball {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ : E → ℝ} {r : ℝ} (hr : 0 < r)
    (hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (ball 0 r)) :
    ∃ (L : ℝ≥0) (ψ : E → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ LipschitzWith L ψ ∧
      EqOn ψ φ (ball 0 (r / 4)) := by
  let b : ContDiffBump (0 : E) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbU : tsupport b ⊆ ball 0 r := by
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hsmooth := contDiff_mul_of_tsupport_subset b.contDiff isOpen_ball hbU hφ
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (b.hasCompactSupport.mul_right (f' := φ)) hsmooth (by simp)
  refine ⟨L, _, hsmooth, hL, fun x hx => ?_⟩
  change b x * φ x = φ x
  rw [b.one_of_mem_closedBall (ball_subset_closedBall hx), one_mul]

/-! ### Smooth local graphs and smooth graph domains -/

/-- **A set smooth near `z` agrees with a smooth Lipschitz graph domain on a ball** around `z`:
cut off the local graph function with `Rd.exists_contDiff_lipschitzWith_eqOn_ball` and take the
graph domain of the local graph (`Rd.LipschitzGraph.ofLocal`) on the ball of a quarter of the
radius (`Rd.localGraph_inter_ball_eq_of_eqOn`), whose graph function is smooth
(`Rd.LipschitzGraph.contDiff_phi_ofLocal`). -/
theorem IsSmoothDomainAt.exists_ball_inter_eq [FiniteDimensional ℝ V] {Ω : Set V} {z : V}
    (h : IsSmoothDomainAt Ω z) :
    ∃ r : ℝ, 0 < r ∧ ∃ G : LipschitzGraph V, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G.phi ∧
      ball z r ∩ Ω = ball z r ∩ G.domain := by
  obtain ⟨r, hr, ν, hν, φ, hφ, hΩ⟩ := h
  obtain ⟨L, ψ, hψ, hψL, heq⟩ := exists_contDiff_lipschitzWith_eqOn_ball hr hφ
  have hsub : ball z (r / 4) ⊆ ball z r := ball_subset_ball (by linarith)
  refine ⟨r / 4, by positivity, LipschitzGraph.ofLocal z ν hν ψ hψL, ?_, ?_⟩
  · exact LipschitzGraph.contDiff_phi_ofLocal z ν hν hψL hψ
  · calc ball z (r / 4) ∩ Ω = Ω ∩ ball z r ∩ ball z (r / 4) := by
          rw [inter_assoc, inter_eq_right.2 hsub, inter_comm]
      _ = {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩
          ball z (r / 4) := by rw [hΩ, inter_assoc, inter_eq_right.2 hsub]
      _ = {x | ψ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩
          ball z (r / 4) := localGraph_inter_ball_eq_of_eqOn heq.symm
      _ = ball z (r / 4) ∩ (LipschitzGraph.ofLocal z ν hν ψ hψL).domain := by
          rw [LipschitzGraph.domain_ofLocal, inter_comm]

/-- **Agreeing with a smooth Lipschitz graph domain on a ball** around `z` makes a set smooth near
`z`: the graph function seen from `z` (`Rd.LipschitzGraph.localPhi`) is smooth on the whole
hyperplane (`Rd.LipschitzGraph.contDiff_localPhi`), and `Rd.LipschitzGraph.domain_eq_localPhi`
describes the graph domain. -/
theorem isSmoothDomainAt_of_ball_inter_eq {Ω : Set V} {z : V} {r : ℝ} (hr : 0 < r)
    (G : LipschitzGraph V) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G.phi)
    (h : ball z r ∩ Ω = ball z r ∩ G.domain) : IsSmoothDomainAt Ω z := by
  refine ⟨r, hr, G.e, G.norm_e, G.localPhi z, ?_, ?_⟩
  · exact (G.contDiff_localPhi z hG).contDiffOn
  · rw [inter_comm, h, G.domain_eq_localPhi z, inter_comm]
    rfl

/-- **Smooth near `z` means agreeing with a smooth Lipschitz graph domain on a ball** around `z`,
in finite dimension. -/
theorem isSmoothDomainAt_iff [FiniteDimensional ℝ V] {Ω : Set V} {z : V} :
    IsSmoothDomainAt Ω z ↔
      ∃ r : ℝ, 0 < r ∧ ∃ G : LipschitzGraph V, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G.phi ∧
        ball z r ∩ Ω = ball z r ∩ G.domain :=
  ⟨IsSmoothDomainAt.exists_ball_inter_eq, fun ⟨_, hr, G, hG, h⟩ =>
    isSmoothDomainAt_of_ball_inter_eq hr G hG h⟩

/-- **Smooth near a point implies Lipschitz near it**: the local graph function `φ` is `C^1` at
the origin, hence `K`-Lipschitz on a ball `B(0, ε)` (Mathlib's `ContDiffAt.exists_lipschitzOnWith`),
and `Rd.isLipschitzDomainAt_of_lipschitzOnWith` applies with the radius `min ε r`. -/
theorem IsSmoothDomainAt.isLipschitzDomainAt {Ω : Set V} {z : V}
    (h : IsSmoothDomainAt Ω z) : IsLipschitzDomainAt Ω z := by
  obtain ⟨r, hr, ν, hν, φ, hφ, hΩ⟩ := h
  obtain ⟨K, t, ht, hK⟩ := ((hφ.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).of_le
    (by exact_mod_cast le_top)).exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
  have hsub : ball z (min ε r) ⊆ ball z r := ball_subset_ball (min_le_right _ _)
  refine isLipschitzDomainAt_of_lipschitzOnWith (lt_min hε hr) hν
    (hK.mono ((ball_subset_ball (min_le_left _ _)).trans hεt)) ?_
  rw [← inter_eq_right.2 hsub, ← inter_assoc, hΩ, inter_assoc]

/-- **Every bounded smooth set is a bounded Lipschitz set**
(`Rd.IsSmoothDomainAt.isLipschitzDomainAt`). -/
theorem IsBoundedSmoothDomain.isBoundedLipschitzDomain {Ω : Set V}
    (h : IsBoundedSmoothDomain Ω) : IsBoundedLipschitzDomain Ω :=
  ⟨h.1, h.2.1, fun z hz => (h.2.2 z hz).isLipschitzDomainAt⟩

/-! ### The constructor from the set-level definition -/

namespace IsBoundedSmoothDomain

variable [FiniteDimensional ℝ V] {Ω : Set V}

/-- **A smooth chart at each frontier point**: a radius `r > 0` and a Lipschitz graph domain with
smooth graph function that agrees with `Ω` on `B(z, r)`
(`Rd.IsSmoothDomainAt.exists_ball_inter_eq`). -/
theorem exists_chart (h : IsBoundedSmoothDomain Ω) (z : frontier Ω) :
    ∃ q : ℝ × LipschitzGraph V, 0 < q.1 ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q.2.phi ∧
      ball (z : V) q.1 ∩ Ω = ball (z : V) q.1 ∩ q.2.domain := by
  obtain ⟨r, hr, G, hG, h'⟩ := (h.2.2 z z.2).exists_ball_inter_eq
  exact ⟨(r, G), hr, hG, h'⟩

/-- A chosen smooth chart at the frontier point `z`: its radius and its graph domain. -/
noncomputable def chart (h : IsBoundedSmoothDomain Ω) (z : frontier Ω) : ℝ × LipschitzGraph V :=
  Classical.choose (h.exists_chart z)

/-- The radius of the chosen smooth chart is positive. -/
theorem chart_fst_pos (h : IsBoundedSmoothDomain Ω) (z : frontier Ω) : 0 < (h.chart z).1 :=
  (Classical.choose_spec (h.exists_chart z)).1

/-- The graph function of the chosen smooth chart is smooth. -/
theorem contDiff_chart_phi (h : IsBoundedSmoothDomain Ω) (z : frontier Ω) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h.chart z).2.phi :=
  (Classical.choose_spec (h.exists_chart z)).2.1

/-- On the ball of the chosen smooth chart, `Ω` is its graph domain. -/
theorem ball_inter_chart (h : IsBoundedSmoothDomain Ω) (z : frontier Ω) :
    ball (z : V) (h.chart z).1 ∩ Ω = ball (z : V) (h.chart z).1 ∩ (h.chart z).2.domain :=
  (Classical.choose_spec (h.exists_chart z)).2.2

end IsBoundedSmoothDomain

namespace SmoothDomain

variable {n : ℕ} [NeZero n] {Ω : Set (EuclideanSpace ℝ (Fin n))}

/-- **The smooth domain of a bounded smooth set** in `ℝ^n`: the chosen smooth charts at the
frontier points (`Rd.IsBoundedSmoothDomain.chart`) give a bounded Lipschitz domain with carrier
`Ω` (`Rd.BoundedLipschitzDomain.ofCharts`), whose graph functions are smooth since each graph
domain is one of the charts (`Rd.BoundedLipschitzDomain.exists_graph_ofCharts_eq`). -/
noncomputable def ofIsBoundedSmoothDomain (h : IsBoundedSmoothDomain Ω) : SmoothDomain n where
  toBoundedLipschitzDomain := BoundedLipschitzDomain.ofCharts h.1 h.2.1 (fun z => (h.chart z).1)
    h.chart_fst_pos (fun z => (h.chart z).2) h.ball_inter_chart
  contDiff_phi j := by
    obtain ⟨z, hz⟩ := BoundedLipschitzDomain.exists_graph_ofCharts_eq h.1 h.2.1 _
      h.chart_fst_pos _ h.ball_inter_chart j
    rw [hz]
    exact h.contDiff_chart_phi z

/-- The carrier of `Rd.SmoothDomain.ofIsBoundedSmoothDomain h` is `Ω`. -/
@[simp]
theorem carrier_ofIsBoundedSmoothDomain (h : IsBoundedSmoothDomain Ω) :
    (ofIsBoundedSmoothDomain h).carrier = Ω :=
  rfl

/-- **The carrier of a smooth domain is a bounded smooth set**: near a frontier point it agrees
with one of its graph domains (`Rd.BoundedLipschitzDomain.exists_ball_inter_eq_graph`), whose
graph function is smooth. -/
theorem isBoundedSmoothDomain (D : SmoothDomain n) : IsBoundedSmoothDomain D.carrier :=
  ⟨D.isOpen, D.isBounded, fun _ hz => by
    obtain ⟨j, ρ, hρ, h⟩ := D.toBoundedLipschitzDomain.exists_ball_inter_eq_graph hz
    exact isSmoothDomainAt_of_ball_inter_eq hρ (D.graph j) (D.contDiff_phi j) h⟩

end SmoothDomain

/-- **The set-level definition and the structure agree**: a set in `ℝ^n` is a bounded smooth set
iff it is the carrier of some `Rd.SmoothDomain`. -/
theorem isBoundedSmoothDomain_iff_exists {n : ℕ} [NeZero n] {Ω : Set (EuclideanSpace ℝ (Fin n))} :
    IsBoundedSmoothDomain Ω ↔ ∃ D : SmoothDomain n, D.carrier = Ω :=
  ⟨fun h => ⟨SmoothDomain.ofIsBoundedSmoothDomain h, rfl⟩,
    fun ⟨D, hD⟩ => hD ▸ D.isBoundedSmoothDomain⟩

/-! ### The ball -/

/-- For `R > 0` the function `y ↦ g_R(‖y‖)` (`Rd.sphereProfile`) is smooth on the ball of radius
`R/2` of any real inner product space: there it equals `R - √(R² - ‖y‖²)`, since
`min(‖y‖, R/2) = ‖y‖`; `y ↦ ‖y‖²` is smooth (Mathlib's `contDiff_norm_sq`), and the square root
is smooth away from `0` (`ContDiffOn.sqrt`). -/
theorem contDiffOn_sphereProfile_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => sphereProfile R ‖y‖) (ball 0 (R / 2)) := by
  have hpos : ∀ y ∈ ball (0 : E) (R / 2), R ^ 2 - ‖y‖ ^ 2 ≠ 0 := fun y hy => by
    rw [mem_ball_zero_iff] at hy
    nlinarith [norm_nonneg y]
  refine ((contDiffOn_const (c := R)).sub
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn.sqrt hpos)).congr fun y hy => ?_
  rw [mem_ball_zero_iff] at hy
  rw [sphereProfile, min_eq_left hy.le]

/-- **The ball is smooth near each point of its sphere**: at `z` with `‖z - c‖ = R`, with the
inward normal `ν = (c - z)/R`, radius `R/2` and the function `y ↦ g_R(‖y‖)`, smooth on the ball of
radius `R/2` (`Rd.contDiffOn_sphereProfile_norm`, `Rd.inter_ball_eq_sphereProfile`). -/
theorem isSmoothDomainAt_ball (c : V) {R : ℝ} (hR : 0 < R) {z : V} (hz : dist z c = R) :
    IsSmoothDomainAt (ball c R) z :=
  ⟨R / 2, by positivity, R⁻¹ • (c - z), norm_inv_smul_sub_eq_one hR hz,
    fun y => sphereProfile R ‖(y : V)‖, contDiffOn_sphereProfile_norm hR,
    inter_ball_eq_sphereProfile c hR hz⟩

/-- **Every open ball is a bounded smooth set**: for `R > 0` by `Rd.isSmoothDomainAt_ball` at the
points of the sphere, which contains the frontier (Mathlib's `Metric.frontier_ball_subset_sphere`);
for `R ≤ 0` the ball is empty. -/
theorem isBoundedSmoothDomain_ball (c : V) (R : ℝ) : IsBoundedSmoothDomain (ball c R) := by
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR]
    exact ⟨isOpen_empty, Bornology.isBounded_empty, fun _ hz => by simp at hz⟩
  · exact ⟨isOpen_ball, isBounded_ball, fun _ hz =>
      isSmoothDomainAt_ball c hR (mem_sphere.1 (frontier_ball_subset_sphere hz))⟩

/-- **The ball as a smooth domain**: `B(c, R) ⊆ ℝ^n`, from `Rd.isBoundedSmoothDomain_ball`. Its
closure is a compact smooth manifold with boundary (`Rd.SmoothDomain.isManifold`) with the
Lebesgue measure as a smooth measure. The name is protected, so that `ball` keeps meaning
`Metric.ball` inside the namespace `Rd.SmoothDomain`. -/
protected noncomputable def SmoothDomain.ball {n : ℕ} [NeZero n] (c : EuclideanSpace ℝ (Fin n))
    (R : ℝ) : SmoothDomain n :=
  SmoothDomain.ofIsBoundedSmoothDomain (isBoundedSmoothDomain_ball c R)

/-- The carrier of `Rd.SmoothDomain.ball c R` is the ball `B(c, R)`. -/
@[simp]
theorem SmoothDomain.carrier_ball {n : ℕ} [NeZero n] (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    (SmoothDomain.ball c R).carrier = ball c R :=
  rfl

/-- **The Besov spaces of the closed ball**: for `1 ≤ p < ∞`, `0 < s < r` and `1 ≤ q ≤ ∞`, a
function `f ∈ L_p` of the closure of the ball `B(c, R)`, a compact manifold with boundary with the
Lebesgue measure, lies in its Besov space `B^s_{p,q}` iff
`‖f‖_{L_p(B(c, R))} + ‖(2^(ks) ω_r(f, 2^(-k), B(c, R))_p)_k‖_{ℓ_q} < ∞`, with `f` extended by `0`
(`Rd.SmoothDomain.memBesov_iff_modNormOn_lt_top` for `Rd.SmoothDomain.ball`). -/
theorem SmoothDomain.memBesov_ball_iff {n : ℕ} [NeZero n] (c : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {s : ℝ} (hs : 0 < s) {r : ℕ} (hsr : s < r)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (SmoothDomain.ball c R).volumeOn) :
    Manifold.MemBesov (𝓡∂ n) (SmoothDomain.ball c R).volumeOn hp s q f ↔
      modNormOn (measurableSet_ball : MeasurableSet (ball c R)) r s q
        ((SmoothDomain.ball c R).extLp hp f) < ⊤ :=
  memBesov_iff_modNormOn_lt_top hp hs hsr hq f

end Rd
