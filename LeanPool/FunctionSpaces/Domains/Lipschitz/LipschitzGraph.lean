/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.LocalMeans.LocalMeans
public import LeanPool.FunctionSpaces.Analysis.Lp.IndicatorOperator
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Lipschitz graph domains

A **Lipschitz graph domain** in `V` is `Ω = {x : φ(x) < ⟪x, e⟫}` for a unit vector `e` and an
`M`-Lipschitz function `φ` that is constant along `e` (`Rd.LipschitzGraph`); for `V = ℝ^d` and
`e = e_d` this is `{x_d > φ(x_1, …, x_(d-1))}`. The function `φ` is Lipschitz in Mathlib's sense
(`Rd.LipschitzGraph.lipschitzWith_phi`), `Ω` is open (`Rd.LipschitzGraph.toOpens`), and its
closure is `{x : φ(x) ≤ ⟪x, e⟫}` (`Rd.LipschitzGraph.closure_domain`). With the
cone `K = {y : M ‖y - ⟪y, e⟫ e‖ < ⟪y, e⟫}` (`Rd.LipschitzGraph.cone`), `Ω + K ⊆ Ω`
(`Rd.LipschitzGraph.add_mem`): a step into the cone raises `⟪·, e⟫` faster than `φ`. The cone is
closed under positive scaling and contains a ball around `e/4`
(`Rd.LipschitzGraph.ball_subset_cone`). The closed cone `KBar = {y : M ‖y - ⟪y, e⟫ e‖ ≤ ⟪y, e⟫}`
(`Rd.LipschitzGraph.closedCone`) is closed under nonnegative scaling, and still `Ω + KBar ⊆ Ω`
(`Rd.LipschitzGraph.add_mem_of_mem_closedCone`); for the closure, `ΩBar + K ⊆ Ω`
(`Rd.LipschitzGraph.add_mem_of_mem_closure`). Both rest on `φ(x + y) ≤ φ(x) + M ‖y - ⟪y, e⟫ e‖`
(`Rd.LipschitzGraph.phi_add_le`). If the closed support of `η` lies in `K`, so does that of every
dilate `η_c`, `c > 0` (`Rd.LipschitzGraph.mem_cone_of_mem_tsupport_dilate`).

The **cone bump** (`Rd.LipschitzGraph.coneBump`) is a bump for local means supported in
`-K ∩ B(0, 1/2)`: the bump of the smooth bump function around `-e/4` of radius `ρ`
(`Rd.LocalMeansBump.ofContDiffBump`). A kernel `k` is **supported in `-K`** if `k(y) ≠ 0` implies
`-y ∈ K` (`Rd.LipschitzGraph.ConeSupported`); this passes to sums, differences and dilations, so
the moment kernels and the dual kernels of every bump supported in `-K` are supported in `-K`
(`Rd.LipschitzGraph.coneSupported_momentKernel_of`, `Rd.LipschitzGraph.coneSupported_dual_of`),
and so are the local means kernels of the cone bump (`Rd.LipschitzGraph.coneSupported_kernel`).

**Support principle** (`Rd.LipschitzGraph.conv_indicator_eq`): for a kernel supported in `-K` and
`x ∈ Ω`, `(k ⋆ f)(x)` depends only on `f` on `Ω`, since `x - y ∈ x + K ⊆ Ω` whenever `k(y) ≠ 0`.
This is the support principle for two sets, `(k ⋆ 1_W f)(x) = (k ⋆ f)(x)` if `x - y ∈ W` whenever
`k(y) ≠ 0` (`Rd.conv_indicator_eq_of_forall`, `Rd.indicatorLp_convLp_indicatorLp`), for `W = Ω`.
On `L_p`, with the cut-off `f ↦ 1_Ω f` (`Rd.LipschitzGraph.cutoff`, from `Rd.indicatorLp`):
`1_Ω (k ⋆ (1_Ω h)) = 1_Ω (k ⋆ h)` (`Rd.LipschitzGraph.cutoff_convLp_cutoff`).
Two classes have the same cut-off iff they agree almost everywhere on the set
(`Rd.indicatorLp_eq_iff_ae_eq_restrict`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The support principle for two sets -/

section SupportPrincipleTwoSets

variable [MeasurableSpace V]

omit [InnerProductSpace ℝ V] in
/-- **The support principle for two sets**: if `x - y ∈ W` whenever `k(y) ≠ 0`, then
`(k ⋆ 1_W f)(x) = (k ⋆ f)(x)`. -/
theorem conv_indicator_eq_of_forall {k : V → ℂ} {W : Set V} (f : V → ℂ) {x : V}
    (hx : ∀ y, k y ≠ 0 → x - y ∈ W) (μ : Measure V) :
    conv k (W.indicator f) μ x = conv k f μ x := by
  rw [conv_apply, conv_apply]
  congr 1
  funext y
  by_cases hy : k y = 0
  · simp [hy]
  · rw [Set.indicator_of_mem (hx y hy)]

variable [FiniteDimensional ℝ V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The support principle for two sets on `L_p`**: `1_U (k ⋆ (1_W h)) = 1_U (k ⋆ h)` if
`x - y ∈ W` for `x ∈ U` and `k(y) ≠ 0`. -/
theorem indicatorLp_convLp_indicatorLp (hp : p ≠ ∞) {k : V → ℂ} (hk : Integrable k)
    {U W : Set V} (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ y, k y ≠ 0 → x - y ∈ W) (h : Lp ℂ p (volume : Measure V)) :
    indicatorLp hU (convLp hp hk (indicatorLp hW h)) = indicatorLp hU (convLp hp hk h) := by
  refine Lp.ext ?_
  have h3 : conv k (indicatorLp hW h : V → ℂ) volume = conv k (W.indicator h) volume :=
    conv_congr_ae (indicatorLp_apply_ae hW h)
  filter_upwards [indicatorLp_apply_ae hU (convLp hp hk (indicatorLp hW h)),
    convLp_apply_ae hp hk (indicatorLp hW h), indicatorLp_apply_ae hU (convLp hp hk h),
    convLp_apply_ae hp hk h] with x hx1 hx2 hx4 hx5
  rw [hx1, hx4]
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hx2, hx5, h3,
      conv_indicator_eq_of_forall _ (hUW x hx) volume]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

end SupportPrincipleTwoSets

/-! ### Lipschitz graph domains and their cones -/

variable (V) in
/-- A **Lipschitz graph domain** `{x : φ(x) < ⟪x, e⟫}`, given by a unit vector `e` and a function
`φ` that is `M`-Lipschitz and constant along `e`. -/
structure LipschitzGraph where
  /-- The upward direction. -/
  e : V
  norm_e : ‖e‖ = 1
  /-- The Lipschitz constant. -/
  M : ℝ
  M_nonneg : 0 ≤ M
  /-- The graph function. -/
  phi : V → ℝ
  lipschitz : ∀ x y, |phi x - phi y| ≤ M * ‖x - y‖
  const : ∀ (x : V) (t : ℝ), phi (x + t • e) = phi x

namespace LipschitzGraph

variable (Ω : LipschitzGraph V)

/-- The domain `{x : φ(x) < ⟪x, e⟫}`. -/
def domain : Set V := {x | Ω.phi x < inner ℝ x Ω.e}

/-- The cone `K = {y : M ‖y - ⟪y, e⟫ e‖ < ⟪y, e⟫}`. -/
def cone : Set V := {y | Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e}

/-- The closed cone `KBar = {y : M ‖y - ⟪y, e⟫ e‖ ≤ ⟪y, e⟫}`, which contains `K`. -/
def closedCone : Set V := {y | Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ ≤ inner ℝ y Ω.e}

/-- The cone lies in the closed cone. -/
theorem cone_subset_closedCone : Ω.cone ⊆ Ω.closedCone := fun y hy => by
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e := hy
  exact hy'.le

/-- **The graph function along a step**: `φ(x + y) ≤ φ(x) + M ‖y - ⟪y, e⟫ e‖`, since `φ` is
constant along `e` and `M`-Lipschitz. -/
theorem phi_add_le (x y : V) : Ω.phi (x + y) ≤ Ω.phi x + Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ := by
  set d := y - inner ℝ y Ω.e • Ω.e
  have h1 : Ω.phi (x + y) = Ω.phi (x + d) := by
    rw [← Ω.const (x + d) (inner ℝ y Ω.e)]
    congr 1
    simp only [d]
    abel
  have h := Ω.lipschitz (x + d) x
  rw [add_sub_cancel_left] at h
  rw [h1]
  linarith [le_abs_self (Ω.phi (x + d) - Ω.phi x)]

/-- **Steps into the closed cone stay in the domain**: `Ω + KBar ⊆ Ω`, since the domain is
defined by
a strict inequality (`Rd.LipschitzGraph.phi_add_le`). -/
theorem add_mem_of_mem_closedCone {x y : V} (hx : x ∈ Ω.domain) (hy : y ∈ Ω.closedCone) :
    x + y ∈ Ω.domain := by
  have hx' : Ω.phi x < inner ℝ x Ω.e := hx
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ ≤ inner ℝ y Ω.e := hy
  change Ω.phi (x + y) < inner ℝ (x + y) Ω.e
  rw [inner_add_left]
  linarith [Ω.phi_add_le x y]

/-- **Steps into the cone stay in the domain**: `Ω + K ⊆ Ω`, the case `K ⊆ KBar` of
`Rd.LipschitzGraph.add_mem_of_mem_closedCone`. -/
theorem add_mem {x y : V} (hx : x ∈ Ω.domain) (hy : y ∈ Ω.cone) : x + y ∈ Ω.domain :=
  Ω.add_mem_of_mem_closedCone hx (Ω.cone_subset_closedCone hy)

/-- The cone is closed under positive scaling. -/
theorem smul_mem_cone {c : ℝ} (hc : 0 < c) {y : V} (hy : y ∈ Ω.cone) : c • y ∈ Ω.cone := by
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e := hy
  change Ω.M * ‖c • y - inner ℝ (c • y) Ω.e • Ω.e‖ < inner ℝ (c • y) Ω.e
  rw [real_inner_smul_left, ← smul_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hc.le]
  nlinarith

/-- Multiples of a step in the cone stay in the domain: `x + l h ∈ Ω`. -/
theorem add_nsmul_mem {x h : V} (hx : x ∈ Ω.domain) (hh : h ∈ Ω.cone) (l : ℕ) :
    x + (l : ℝ) • h ∈ Ω.domain := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simpa using hx
  · exact Ω.add_mem hx (Ω.smul_mem_cone (by exact_mod_cast hl) hh)

/-- The closed cone is closed. -/
theorem isClosed_closedCone : IsClosed Ω.closedCone :=
  isClosed_le (continuous_const.mul ((continuous_id.sub ((continuous_id.inner continuous_const).smul
    continuous_const)).norm)) (continuous_id.inner continuous_const)

/-- The closed cone is closed under nonnegative scaling. -/
theorem smul_mem_closedCone {c : ℝ} (hc : 0 ≤ c) {y : V} (hy : y ∈ Ω.closedCone) :
    c • y ∈ Ω.closedCone := by
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ ≤ inner ℝ y Ω.e := hy
  change Ω.M * ‖c • y - inner ℝ (c • y) Ω.e • Ω.e‖ ≤ inner ℝ (c • y) Ω.e
  rw [real_inner_smul_left, ← smul_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hc]
  nlinarith

/-- The graph function `φ` is `M`-Lipschitz, in the form of Mathlib's `LipschitzWith`. -/
theorem lipschitzWith_phi : LipschitzWith ⟨Ω.M, Ω.M_nonneg⟩ Ω.phi :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, dist_eq_norm]
    exact Ω.lipschitz x y

/-- The graph function is continuous. -/
theorem continuous_phi : Continuous Ω.phi :=
  Ω.lipschitzWith_phi.continuous

/-- **Steps into the open cone from the closure stay in the domain**: `ΩBar + K ⊆ Ω`, since
`φ(x) ≤ ⟪x, e⟫` on the closure of `Ω` and the cone is defined by a strict inequality
(`Rd.LipschitzGraph.phi_add_le`). -/
theorem add_mem_of_mem_closure {x y : V} (hx : x ∈ closure Ω.domain) (hy : y ∈ Ω.cone) :
    x + y ∈ Ω.domain := by
  have hx' : Ω.phi x ≤ inner ℝ x Ω.e :=
    closure_lt_subset_le Ω.continuous_phi (continuous_id.inner continuous_const) hx
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e := hy
  change Ω.phi (x + y) < inner ℝ (x + y) Ω.e
  rw [inner_add_left]
  linarith [Ω.phi_add_le x y]

/-- The domain is open. -/
theorem isOpen_domain : IsOpen Ω.domain :=
  isOpen_lt Ω.continuous_phi (continuous_id.inner continuous_const)

/-- **The closure of a graph domain** is `{x : φ(x) ≤ ⟪x, e⟫}`: the points with `φ(x) = ⟪x, e⟫`
are limits of `x + t e`, `t ↓ 0`. -/
theorem closure_domain : closure Ω.domain = {x | Ω.phi x ≤ inner ℝ x Ω.e} := by
  refine Set.Subset.antisymm
    (closure_lt_subset_le Ω.continuous_phi (continuous_id.inner continuous_const)) fun x hx => ?_
  have hlim : Tendsto (fun t : ℝ => x + t • Ω.e) (𝓝[>] 0) (𝓝 x) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' (0 : ℝ) x
      (by simp)).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
  change Ω.phi (x + t • Ω.e) < inner ℝ (x + t • Ω.e) Ω.e
  rw [Ω.const, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, Ω.norm_e]
  have hx' : Ω.phi x ≤ inner ℝ x Ω.e := hx
  linarith

/-- The graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` as an element of Mathlib's `Opens V`, the form in
which open sets carry weak derivatives. -/
def toOpens : TopologicalSpace.Opens V := ⟨Ω.domain, Ω.isOpen_domain⟩

/-- The points of `Ω.toOpens` are the points of the graph domain. -/
@[simp]
theorem coe_toOpens : (Ω.toOpens : Set V) = Ω.domain :=
  rfl

/-- The radius `1/(8(M + 1))` of a ball around `e/4` inside the cone. -/
noncomputable def coneRadius : ℝ := 1 / (8 * (Ω.M + 1))

/-- The radius is positive. -/
theorem coneRadius_pos : 0 < Ω.coneRadius := by
  have := Ω.M_nonneg
  unfold coneRadius
  positivity

/-- `ρ ≤ 1/8`. -/
theorem coneRadius_le : Ω.coneRadius ≤ 1 / 8 := by
  have := Ω.M_nonneg
  unfold coneRadius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `(2M + 1) ρ ≤ 1/4`. -/
theorem two_mul_add_one_mul_coneRadius_le : (2 * Ω.M + 1) * Ω.coneRadius ≤ 1 / 4 := by
  have := Ω.M_nonneg
  unfold coneRadius
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **A ball inside the cone**: `B(e/4, ρ) ⊆ K`, since the component orthogonal to `e` of a point
of the ball is at most `2ρ` and its component along `e` at least `1/4 - ρ`. -/
theorem ball_subset_cone : Metric.ball ((1 / 4 : ℝ) • Ω.e) Ω.coneRadius ⊆ Ω.cone := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  set d := w - (1 / 4 : ℝ) • Ω.e with hd
  have hwd : w = (1 / 4 : ℝ) • Ω.e + d := by rw [hd]; abel
  have hee : inner ℝ Ω.e Ω.e = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, Ω.norm_e, one_pow]
  have hde : |inner ℝ d Ω.e| ≤ ‖d‖ := by
    have h := abs_real_inner_le_norm d Ω.e
    rwa [Ω.norm_e, mul_one] at h
  have hinner : inner ℝ w Ω.e = 1 / 4 + inner ℝ d Ω.e := by
    rw [hwd, inner_add_left, real_inner_smul_left, hee, mul_one]
  have hperp : w - inner ℝ w Ω.e • Ω.e = d - inner ℝ d Ω.e • Ω.e := by
    rw [hinner, add_smul]
    rw [hwd]
    abel
  have hnorm : ‖d - inner ℝ d Ω.e • Ω.e‖ ≤ 2 * ‖d‖ := by
    calc ‖d - inner ℝ d Ω.e • Ω.e‖ ≤ ‖d‖ + ‖inner ℝ d Ω.e • Ω.e‖ := norm_sub_le _ _
      _ = ‖d‖ + |inner ℝ d Ω.e| := by rw [norm_smul, Real.norm_eq_abs, Ω.norm_e, mul_one]
      _ ≤ 2 * ‖d‖ := by linarith
  have hM := Ω.M_nonneg
  have h1 : Ω.M * ‖d - inner ℝ d Ω.e • Ω.e‖ ≤ Ω.M * (2 * ‖d‖) :=
    mul_le_mul_of_nonneg_left hnorm hM
  have h2 : (2 * Ω.M + 1) * ‖d‖ < (2 * Ω.M + 1) * Ω.coneRadius :=
    mul_lt_mul_of_pos_left hw (by positivity)
  have h3 := Ω.two_mul_add_one_mul_coneRadius_le
  have h4 : -‖d‖ ≤ inner ℝ d Ω.e := (abs_le.1 hde).1
  change Ω.M * ‖w - inner ℝ w Ω.e • Ω.e‖ < inner ℝ w Ω.e
  rw [hperp, hinner]
  nlinarith

/-! ### Kernels supported in `-K` -/

/-- A kernel `k` is **supported in `-K`** if `k(y) ≠ 0` implies `-y ∈ K`. -/
def ConeSupported (k : V → ℂ) : Prop := ∀ y, k y ≠ 0 → -y ∈ Ω.cone

variable {Ω}

/-- Sums of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.add {k k' : V → ℂ} (hk : Ω.ConeSupported k) (hk' : Ω.ConeSupported k') :
    Ω.ConeSupported (k + k') := fun y hy => by
  by_cases h : k y = 0
  · exact hk' y fun h' => hy (by simp [h, h'])
  · exact hk y h

/-- Differences of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.sub {k k' : V → ℂ} (hk : Ω.ConeSupported k) (hk' : Ω.ConeSupported k') :
    Ω.ConeSupported (k - k') := fun y hy => by
  by_cases h : k y = 0
  · exact hk' y fun h' => hy (by simp [h, h'])
  · exact hk y h

/-- Dilations of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.dilate {k : V → ℂ} (hk : Ω.ConeSupported k) {c : ℝ} (hc : 0 < c) :
    Ω.ConeSupported (Rd.dilate c k) := fun y hy => by
  have hky : k (c • y) ≠ 0 := fun h => hy (by simp [Rd.dilate, h])
  have h := Ω.smul_mem_cone (inv_pos.2 hc) (hk (c • y) hky)
  rwa [smul_neg, inv_smul_smul₀ hc.ne'] at h

variable (Ω) in
/-- **Dilates of a cone kernel are cone kernels**: if the closed support of `η` lies in the cone
`K` and `c > 0`, so does the closed support of `η_c`, since `c x ∈ supp η` for `x ∈ supp η_c`
(`Rd.smul_mem_tsupport_of_mem_tsupport_dilate`) and `c⁻¹ K ⊆ K`
(`Rd.LipschitzGraph.smul_mem_cone`). -/
theorem mem_cone_of_mem_tsupport_dilate {η : V → ℂ} (hη : tsupport η ⊆ Ω.cone) {c : ℝ}
    (hc : 0 < c) {x : V} (hx : x ∈ tsupport (Rd.dilate c η)) : x ∈ Ω.cone := by
  have h := Ω.smul_mem_cone (inv_pos.2 hc)
    (hη (smul_mem_tsupport_of_mem_tsupport_dilate hc.ne' hx))
  rwa [inv_smul_smul₀ hc.ne'] at h

/-- Finite combinations of kernels supported in `-K` are supported in `-K`. -/
theorem ConeSupported.finsetSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) {k : ι → V → ℂ}
    (hk : ∀ i ∈ s, Ω.ConeSupported (k i)) :
    Ω.ConeSupported (fun x => ∑ i ∈ s, a i * k i x) := fun y hy => by
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  exact hk i hi y (right_ne_zero_of_mul hne)

/-- **Kernels supported in `-K` look into `Ω` from points of `Ω`**: if `x ∈ Ω` and `k(y) ≠ 0`,
then `x - y ∈ x + K ⊆ Ω` (`Rd.LipschitzGraph.add_mem`). -/
theorem ConeSupported.sub_mem {k : V → ℂ} (hk : Ω.ConeSupported k) {x y : V}
    (hx : x ∈ Ω.domain) (hy : k y ≠ 0) : x - y ∈ Ω.domain := by
  rw [sub_eq_add_neg]
  exact Ω.add_mem hx (hk y hy)

variable (Ω)

/-! ### The cone bump -/

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The smooth bump around `-e/4` with outer radius `ρ`. -/
noncomputable def coneBumpBase : ContDiffBump (-((1 / 4 : ℝ) • Ω.e)) :=
  ⟨Ω.coneRadius / 2, Ω.coneRadius, by have := Ω.coneRadius_pos; positivity,
    by have := Ω.coneRadius_pos; linarith⟩

/-- The **cone bump**: a bump for local means supported in `-K ∩ B(0, 1/2)`, the normalised
`ContDiffBump` around `-e/4` of radius `ρ` (`Rd.LocalMeansBump.ofContDiffBump`, since
`‖-e/4‖ + ρ ≤ 1/4 + 1/8 ≤ 1/2`). -/
noncomputable def coneBump : LocalMeansBump V :=
  LocalMeansBump.ofContDiffBump Ω.coneBumpBase (R := 1 / 2) (by
    have h : Ω.coneBumpBase.rOut = Ω.coneRadius := rfl
    rw [h, norm_neg, norm_smul, Ω.norm_e, mul_one, Real.norm_of_nonneg (by norm_num)]
    linarith [Ω.coneRadius_le])

/-- The cone bump vanishes outside the ball of radius `1/2`. -/
theorem coneBump_radius : Ω.coneBump.radius = 1 / 2 := rfl

/-- The cone bump is supported in `-K`. -/
theorem coneSupported_coneBump : Ω.ConeSupported Ω.coneBump.toFun := fun y hy => by
  have hy' : y ∈ Function.support (Ω.coneBumpBase.normed volume) := fun h =>
    hy (show ((Ω.coneBumpBase.normed volume y : ℝ) : ℂ) = 0 by rw [h, Complex.ofReal_zero])
  rw [Ω.coneBumpBase.support_normed_eq, Metric.mem_ball, dist_eq_norm] at hy'
  refine Ω.ball_subset_cone ?_
  rw [Metric.mem_ball, dist_eq_norm, show -y - (1 / 4 : ℝ) • Ω.e = -(y - -((1 / 4 : ℝ) • Ω.e))
    by abel, norm_neg]
  exact hy'

/-- The moment kernels of a bump supported in `-K` are supported in `-K`. -/
theorem coneSupported_momentKernel_of {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    (L : ℕ) : Ω.ConeSupported (momentKernel b.toFun L) :=
  ConeSupported.finsetSum _ _ fun _ _ => hb.dilate (by positivity)

/-- The dilated moment kernels of a bump supported in `-K` are supported in `-K`. -/
theorem coneSupported_scaled_of {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    (L j : ℕ) : Ω.ConeSupported (b.scaled L j) :=
  (Ω.coneSupported_momentKernel_of hb L).dilate (by positivity)

/-- The dual kernels of a bump supported in `-K` are supported in `-K`. -/
theorem coneSupported_dual_of {b : LocalMeansBump V} (hb : Ω.ConeSupported b.toFun)
    (L j : ℕ) : Ω.ConeSupported (b.dual L j) := by
  cases j with
  | zero => exact Ω.coneSupported_scaled_of hb L 0
  | succ j => exact (Ω.coneSupported_scaled_of hb L (j + 1)).add (Ω.coneSupported_scaled_of hb L j)

/-- The moment kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_momentKernel (L : ℕ) :
    Ω.ConeSupported (momentKernel Ω.coneBump.toFun L) :=
  Ω.coneSupported_momentKernel_of Ω.coneSupported_coneBump L

/-- The dilated moment kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_scaled (L j : ℕ) : Ω.ConeSupported (Ω.coneBump.scaled L j) :=
  Ω.coneSupported_scaled_of Ω.coneSupported_coneBump L j

/-- The local means kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_kernel (L j : ℕ) : Ω.ConeSupported (Ω.coneBump.kernel L j) := by
  cases j with
  | zero => exact Ω.coneSupported_scaled L 0
  | succ j => exact (Ω.coneSupported_scaled L (j + 1)).sub (Ω.coneSupported_scaled L j)

/-- The dual kernels of the cone bump are supported in `-K`. -/
theorem coneSupported_dual (L j : ℕ) : Ω.ConeSupported (Ω.coneBump.dual L j) :=
  Ω.coneSupported_dual_of Ω.coneSupported_coneBump L j

/-! ### The support principle -/

omit [FiniteDimensional ℝ V] in
/-- The domain is measurable. -/
theorem measurableSet_domain : MeasurableSet Ω.domain := Ω.isOpen_domain.measurableSet

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **The support principle**: for a kernel supported in `-K` and `x ∈ Ω`,
`(k ⋆ (1_Ω f))(x) = (k ⋆ f)(x)`. -/
theorem conv_indicator_eq {k : V → ℂ} (hk : Ω.ConeSupported k) (f : V → ℂ) {x : V}
    (hx : x ∈ Ω.domain) (μ : Measure V) :
    conv k (Ω.domain.indicator f) μ x = conv k f μ x :=
  conv_indicator_eq_of_forall f (fun _ hy => hk.sub_mem hx hy) μ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The **cut-off** `f ↦ 1_Ω f` on `L_p`. -/
noncomputable def cutoff : Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  indicatorLp Ω.measurableSet_domain

/-- The cut-off is `1_Ω f` almost everywhere. -/
theorem cutoff_apply_ae (f : Lp ℂ p (volume : Measure V)) :
    Ω.cutoff f =ᵐ[volume] Ω.domain.indicator f :=
  indicatorLp_apply_ae Ω.measurableSet_domain f

/-- `‖1_Ω f‖_p = ‖f‖_{L_p(Ω)}`. -/
theorem enorm_cutoff (f : Lp ℂ p (volume : Measure V)) :
    ‖Ω.cutoff f‖ₑ = eLpNorm (Ω.domain.indicator f) p volume := by
  rw [Lp.eNorm_def, eLpNorm_congr_ae (Ω.cutoff_apply_ae f)]

/-- `‖1_Ω f‖_p ≤ ‖f‖_p`. -/
theorem enorm_cutoff_le (f : Lp ℂ p (volume : Measure V)) : ‖Ω.cutoff f‖ₑ ≤ ‖f‖ₑ :=
  enorm_indicatorLp_le _ f

/-- Elements of `L_p` with the same cut-off agree almost everywhere on `Ω`. -/
theorem indicator_ae_eq_of_cutoff_eq {F f : Lp ℂ p (volume : Measure V)}
    (hFf : Ω.cutoff F = Ω.cutoff f) : Ω.domain.indicator F =ᵐ[volume] Ω.domain.indicator f := by
  filter_upwards [Ω.cutoff_apply_ae F, Ω.cutoff_apply_ae f] with x h1 h2
  rw [← h1, ← h2, hFf]

/-- **The support principle on `L_p`**: `1_Ω (k ⋆ (1_Ω h)) = 1_Ω (k ⋆ h)` for an integrable
kernel supported in `-K` (`Rd.indicatorLp_convLp_indicatorLp` for `U = W = Ω`). -/
theorem cutoff_convLp_cutoff (hp : p ≠ ∞) {k : V → ℂ} (hk : Integrable k)
    (hks : Ω.ConeSupported k) (h : Lp ℂ p (volume : Measure V)) :
    Ω.cutoff (convLp hp hk (Ω.cutoff h)) = Ω.cutoff (convLp hp hk h) :=
  indicatorLp_convLp_indicatorLp hp hk Ω.measurableSet_domain Ω.measurableSet_domain
    (fun _ hx _ hy => hks.sub_mem hx hy) h

/-- **Convolutions of functions that agree on `Ω` agree on `Ω`**: if `1_Ω F = 1_Ω f`, then
`1_Ω (k ⋆ F) = 1_Ω (k ⋆ f)` for an integrable kernel supported in `-K`. -/
theorem cutoff_convLp_eq (hp : p ≠ ∞) {k : V → ℂ} (hk : Integrable k)
    (hks : Ω.ConeSupported k) {F f : Lp ℂ p (volume : Measure V)}
    (hFf : Ω.cutoff F = Ω.cutoff f) :
    Ω.cutoff (convLp hp hk F) = Ω.cutoff (convLp hp hk f) := by
  rw [← Ω.cutoff_convLp_cutoff hp hk hks F, hFf, Ω.cutoff_convLp_cutoff hp hk hks f]

end LipschitzGraph

end Rd
