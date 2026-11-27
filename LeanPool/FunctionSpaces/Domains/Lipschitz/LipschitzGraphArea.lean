/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphParametrization
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The area formula for Lipschitz graphs

Let `Ω = {x : φ(x) < ⟪x, e⟫}` be a Lipschitz graph domain in `V`, `dim V = n`, with the graph map
`γ(x') = x' + φ(x') e` over the hyperplane `H = e^⊥` (`Rd.LipschitzGraph.graphMap`), whose range is
the boundary of `Ω`. By Rademacher's theorem `φ|_H` has a
gradient `∇φ(x') ∈ H` almost everywhere (`Rd.LipschitzGraph.gradPhi`). The **area formula**
(`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphMap_image`) states, for every measurable
`A ⊆ H`, `μHE[n-1] (γ(A)) = ∫_A √(1 + ‖∇φ(x')‖²) dx'` for Mathlib's Euclidean Hausdorff measure
`μHE[n-1]`, normalised to be the volume on hyperplanes. In measure form, the image of the measure
with density `√(1 + ‖∇φ‖²)` (`Rd.LipschitzGraph.gram`) is `μHE[n-1]` on `γ(H)`
(`Rd.LipschitzGraph.map_graphMap_withDensity`), and in integral form
`∫_{γ(H)} F dμHE[n-1] = ∫_H F(γ x') √(1 + ‖∇φ(x')‖²) dx'` for every `F : V → [0, ∞]` and every
`F : V → ℂ` (`Rd.LipschitzGraph.lintegral_graphMap`, `Rd.LipschitzGraph.integral_graphMap`).

The proof is the one of Federer, 3.2.3, and Evans–Gariepy, §3.3, for a graph, which is injective
and antilipschitz with constant `1`:

* **Linear graphs** (`Rd.LipschitzGraph.euclideanHausdorffMeasure_linearGraph_image`): the linear
  map `S_g x' = x' + ⟪g, x'⟫ e` satisfies `S_g* S_g x' = x' + ⟪g, x'⟫ g`, a transvection of
  determinant `1 + ‖g‖²`, so its norm determinant is `√(1 + ‖g‖²)`
  (`Rd.LipschitzGraph.normDet_linearGraph`), and Mathlib's area formula for linear maps
  (`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`) applies. Explicitly, `S_g`
  is a stretch of `H` by `√(1 + ‖g‖²)` along `g` (`Rd.stretch`) followed by an isometry
  (`Rd.LipschitzGraph.tilt`, `Rd.LipschitzGraph.linearGraph_eq_tilt_comp_stretch`).
* **Nearby graphs** (`Rd.LipschitzGraph.euclideanHausdorffMeasure_graphOver_image_le`): if the
  increments of two functions on `P ⊆ H` differ by at most `δ ‖x' - y'‖`, the Hausdorff measures
  of their graphs over `P` differ at most by the factor `(1 + δ)^(n-1)`, by the bound for
  Lipschitz maps (`LipschitzOnWith.euclideanHausdorffMeasure_image_le`, from Mathlib's
  `LipschitzOnWith.hausdorffMeasure_image_le`).
* **Good pieces** (`Rd.LipschitzGraph.exists_goodPartition`): for `ε > 0`, `H` is, up to a null
  set, a countable disjoint union of measurable sets on which `φ` is `2ε`-close to an affine
  function with gradient `g` and `‖∇φ - g‖ ≤ ε`.
* Summing over the pieces gives the formula up to the factor `(1 + 2ε)^(n-1) (1 + ε)`
  (`Rd.areaFactor`), and `ε → 0`.

The **outward unit normal** `ν = (∇φ - e)/√(1 + ‖∇φ‖²)` (`Rd.LipschitzGraph.normalAt`) is a
measurable unit vector with `⟪ν, y⟫ < 0` for every `y` in the cone of `Ω`.
-/

@[expose] public section

open MeasureTheory Module Metric Filter Topology Function
open scoped ENNReal NNReal

/-! ### Euclidean Hausdorff measures under Lipschitz maps -/

/-- **Lipschitz maps and the Euclidean Hausdorff measure**: a map that is `K`-Lipschitz on `s`
increases `μHE[d]` by at most the factor `K^d`, `μHE[d] (f '' s) ≤ K^d μHE[d] s`. This is
Mathlib's `LipschitzOnWith.hausdorffMeasure_image_le` for the normalised measure `μHE[d]`, a
fixed multiple of `μH[d]`. -/
theorem LipschitzOnWith.euclideanHausdorffMeasure_image_le {X Y : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} {s : Set X} (h : LipschitzOnWith K f s) (d : ℕ) :
    μHE[d] (f '' s) ≤ (K : ℝ≥0∞) ^ d * μHE[d] s := by
  simp only [Measure.euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def,
    smul_eq_mul]
  have h1 := h.hausdorffMeasure_image_le (d := d) (Nat.cast_nonneg d)
  rw [ENNReal.rpow_natCast] at h1
  calc _ ≤ _ * ((K : ℝ≥0∞) ^ d * μH[d] s) := mul_le_mul' le_rfl h1
    _ = _ := by ring

namespace Rd

/-- **Hausdorff measures of nearby images**: let `f₂` satisfy `‖x - y‖ ≤ ‖f₂ x - f₂ y‖` on `P`,
and let the increments of `f₁` differ from those of `f₂` by at most `δ ‖x - y‖` on `P`. Then
`μHE[d] (f₁ '' P) ≤ (1 + δ)^d μHE[d] (f₂ '' P)`. Indeed `f₂` is injective on `P`, so it has a
left inverse `q` on `P` (Mathlib's `Function.invFunOn`), and `f₁ ∘ q` maps `f₂ '' P` onto
`f₁ '' P` and is `(1 + δ)`-Lipschitz there. -/
theorem euclideanHausdorffMeasure_image_le_of_near {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    {f₁ f₂ : X → Y} {P : Set X} {δ : ℝ} (hδ : 0 ≤ δ)
    (h₂ : ∀ x ∈ P, ∀ y ∈ P, ‖x - y‖ ≤ ‖f₂ x - f₂ y‖)
    (h : ∀ x ∈ P, ∀ y ∈ P, ‖(f₁ x - f₁ y) - (f₂ x - f₂ y)‖ ≤ δ * ‖x - y‖) (d : ℕ) :
    μHE[d] (f₁ '' P) ≤ ENNReal.ofReal (1 + δ) ^ d * μHE[d] (f₂ '' P) := by
  have hinj : Set.InjOn f₂ P := fun x hx y hy hxy => by
    have hle := h₂ x hx y hy
    rw [hxy, sub_self, norm_zero] at hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)
  obtain ⟨q, hq⟩ : ∃ q : Y → X, ∀ x ∈ P, q (f₂ x) = x :=
    ⟨Function.invFunOn f₂ P, fun x hx => hinj.leftInvOn_invFunOn hx⟩
  have himg : (f₁ ∘ q) '' (f₂ '' P) = f₁ '' P := by
    rw [Set.image_image]
    exact Set.image_congr fun x hx => by simp only [Function.comp_apply, hq x hx]
  have hlip : LipschitzOnWith (Real.toNNReal (1 + δ)) (f₁ ∘ q) (f₂ '' P) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hq x hx, hq y hy, dist_eq_norm]
    rw [Real.coe_toNNReal _ (by linarith)]
    calc ‖f₁ x - f₁ y‖ ≤ ‖f₂ x - f₂ y‖ + ‖(f₁ x - f₁ y) - (f₂ x - f₂ y)‖ :=
          norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖f₂ x - f₂ y‖ + δ * ‖f₂ x - f₂ y‖ :=
          add_le_add le_rfl ((h x hx y hy).trans (mul_le_mul_of_nonneg_left (h₂ x hx y hy) hδ))
      _ = (1 + δ) * ‖f₂ x - f₂ y‖ := by ring
  rw [← himg]
  exact hlip.euclideanHausdorffMeasure_image_le d

/-- **The function `t ↦ √(1 + t²)` is `1`-Lipschitz**:
`|√(1 + a²) - √(1 + b²)| ≤ |a - b|`. -/
theorem abs_sqrt_one_add_sq_sub_le (a b : ℝ) : |√(1 + a ^ 2) - √(1 + b ^ 2)| ≤ |a - b| := by
  have ha : |a| ≤ √(1 + a ^ 2) := Real.abs_le_sqrt (by linarith)
  have hb : |b| ≤ √(1 + b ^ 2) := Real.abs_le_sqrt (by linarith)
  have hpos : 0 < √(1 + a ^ 2) + √(1 + b ^ 2) := by positivity
  have hsq : (√(1 + a ^ 2) - √(1 + b ^ 2)) * (√(1 + a ^ 2) + √(1 + b ^ 2)) = (a - b) * (a + b) := by
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + a ^ 2 by positivity)
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + b ^ 2 by positivity)
    linear_combination h1 - h2
  have key : |√(1 + a ^ 2) - √(1 + b ^ 2)| * (√(1 + a ^ 2) + √(1 + b ^ 2)) ≤
      |a - b| * (√(1 + a ^ 2) + √(1 + b ^ 2)) := by
    rw [← abs_of_pos hpos, ← abs_mul, hsq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left ((abs_add_le a b).trans (add_le_add ha hb)) (abs_nonneg _)
  exact le_of_mul_le_mul_right key hpos

/-- **Letting a factor tend to one**: if `a ≤ c(ε) b` for every `ε > 0` and `c(ε) → 1` as
`ε → 0+`, then `a ≤ b`. -/
theorem le_of_forall_pos_le_ofReal_mul_of_tendsto {a b : ℝ≥0∞} {c : ℝ → ℝ}
    (hc : Tendsto c (𝓝[>] 0) (𝓝 1)) (h : ∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal (c ε) * b) :
    a ≤ b := by
  have h1 := ENNReal.tendsto_ofReal hc
  rw [ENNReal.ofReal_one] at h1
  have h2 := ENNReal.Tendsto.mul_const (b := b) h1 (Or.inl one_ne_zero)
  rw [one_mul] at h2
  exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun ε hε => h ε hε)

/-- The **area factor** `(1 + 2ε)^m (1 + ε)` of the area formula for the accuracy `ε`, with
`m = n - 1`: comparing a graph with a linear graph costs the factor `(1 + 2ε)^m`, and comparing
the Gram density with a constant costs `1 + ε`. -/
noncomputable def areaFactor (m : ℕ) (ε : ℝ) : ℝ := (1 + 2 * ε) ^ m * (1 + ε)

/-- The area factor tends to `1` as `ε → 0+`, by continuity. -/
theorem tendsto_areaFactor (m : ℕ) : Tendsto (areaFactor m) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous (areaFactor m) := by
    unfold areaFactor
    fun_prop
  have h0 := hc.tendsto 0
  simp only [areaFactor, mul_zero, add_zero, one_pow, one_mul] at h0
  exact h0.mono_left nhdsWithin_le_nhds

/-! ### Stretches -/

section Stretch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **stretch** `D x = x + (c - 1) ⟪u, x⟫ u` by the factor `c` in the direction `u`: for a
unit vector `u` it multiplies `u` by `c` and fixes the vectors orthogonal to `u`. It is Mathlib's
`LinearMap.transvection` of the linear form `(c - 1) ⟪u, ·⟫` and the vector `u`. -/
noncomputable def stretch (u : E) (c : ℝ) : E →ₗ[ℝ] E :=
  LinearMap.transvection ((c - 1) • (innerSL ℝ u).toLinearMap) u

/-- `D x = x + (c - 1) ⟪u, x⟫ u`. -/
theorem stretch_apply (u : E) (c : ℝ) (x : E) :
    stretch u c x = x + ((c - 1) * inner ℝ u x) • u := by
  rw [stretch, LinearMap.transvection.apply]
  rfl

/-- **The determinant of a stretch** by `c` along a unit vector is `c` (Mathlib's
`LinearMap.transvection.det`: `det = 1 + (c - 1) ⟪u, u⟫`). -/
theorem det_stretch [FiniteDimensional ℝ E] {u : E} (hu : ‖u‖ = 1) (c : ℝ) :
    LinearMap.det (stretch u c) = c := by
  rw [stretch, LinearMap.transvection.det, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, real_inner_self_eq_norm_sq, hu, smul_eq_mul]
  ring

end Stretch

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-! ### Graphs over the hyperplane -/

/-- The **graph over the hyperplane** of a function `h : H → ℝ`, the map `x' ↦ x' + h(x') e`
from `H` to `V`. The graph map of `Ω` is the graph of `φ`; the graphs of the linear functions
`⟪g, ·⟫` are linear maps. -/
noncomputable def graphOver (h : Ω.hyperplane → ℝ) (x' : Ω.hyperplane) : V :=
  (x' : V) + h x' • Ω.e

/-- `P(x' + h(x') e) = x'`. -/
theorem proj_graphOver (h : Ω.hyperplane → ℝ) (x' : Ω.hyperplane) :
    Ω.proj (Ω.graphOver h x') = x' := by
  rw [graphOver, map_add, map_smul, Ω.proj_e, smul_zero, add_zero, Ω.proj_coe]

/-- Graphs over the hyperplane are injective. -/
theorem graphOver_injective (h : Ω.hyperplane → ℝ) : Function.Injective (Ω.graphOver h) :=
  fun x' y' hxy => by rw [← Ω.proj_graphOver h x', hxy, Ω.proj_graphOver]

/-- **Pythagoras**: `‖x' + a e‖² = ‖x'‖² + a²` for `x' ∈ H`, since `x' ⊥ e`. -/
theorem norm_coe_add_smul_e_sq (x' : Ω.hyperplane) (a : ℝ) :
    ‖(x' : V) + a • Ω.e‖ ^ 2 = ‖x'‖ ^ 2 + a ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, Ω.inner_coe_e, mul_zero, mul_zero, add_zero,
    norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs, sq_abs, Submodule.norm_coe]

/-- `‖x'‖ ≤ ‖x' + a e‖` for `x' ∈ H`, since `x'` is the projection of `x' + a e` onto `H`. -/
theorem norm_le_norm_coe_add_smul_e (x' : Ω.hyperplane) (a : ℝ) :
    ‖x'‖ ≤ ‖(x' : V) + a • Ω.e‖ :=
  calc ‖x'‖ = ‖Ω.proj (Ω.graphOver (fun _ => a) x')‖ := by rw [Ω.proj_graphOver]
    _ ≤ ‖(x' : V) + a • Ω.e‖ := Ω.norm_proj_le _

/-- The increments of a graph over the hyperplane:
`γ_h x' - γ_h y' = (x' - y') + (h x' - h y') e`. -/
theorem graphOver_sub (h : Ω.hyperplane → ℝ) (x' y' : Ω.hyperplane) :
    Ω.graphOver h x' - Ω.graphOver h y' =
      ((x' - y' : Ω.hyperplane) : V) + (h x' - h y') • Ω.e := by
  simp only [graphOver, Submodule.coe_sub, sub_smul]
  abel

/-- **Graphs over the hyperplane are antilipschitz with constant `1`**:
`‖x' - y'‖ ≤ ‖γ_h x' - γ_h y'‖`, since `x' - y'` is the projection of `γ_h x' - γ_h y'` onto
`H`. -/
theorem norm_sub_le_norm_graphOver_sub (h : Ω.hyperplane → ℝ) (x' y' : Ω.hyperplane) :
    ‖x' - y'‖ ≤ ‖Ω.graphOver h x' - Ω.graphOver h y'‖ :=
  calc ‖x' - y'‖ = ‖Ω.proj (Ω.graphOver h x' - Ω.graphOver h y')‖ := by
        rw [map_sub, Ω.proj_graphOver, Ω.proj_graphOver]
    _ ≤ _ := Ω.norm_proj_le _

/-- The increments of two graphs differ by a multiple of `e`:
`(γ_{h₁} x' - γ_{h₁} y') - (γ_{h₂} x' - γ_{h₂} y') = ((h₁ x' - h₁ y') - (h₂ x' - h₂ y')) e`. -/
theorem graphOver_sub_sub (h₁ h₂ : Ω.hyperplane → ℝ) (x' y' : Ω.hyperplane) :
    (Ω.graphOver h₁ x' - Ω.graphOver h₁ y') - (Ω.graphOver h₂ x' - Ω.graphOver h₂ y') =
      ((h₁ x' - h₁ y') - (h₂ x' - h₂ y')) • Ω.e := by
  rw [Ω.graphOver_sub, Ω.graphOver_sub]
  simp only [sub_smul]
  abel

/-- **Hausdorff measures of two nearby graphs**: if the increments of `h₁` and `h₂` differ by at
most `δ ‖x' - y'‖` on `P`, then `μHE[d] (γ_{h₁} '' P) ≤ (1 + δ)^d μHE[d] (γ_{h₂} '' P)`, since
`γ_{h₂}` is antilipschitz with constant `1`. -/
theorem euclideanHausdorffMeasure_graphOver_image_le [MeasurableSpace V] [BorelSpace V]
    (h₁ h₂ : Ω.hyperplane → ℝ) {P : Set Ω.hyperplane} {δ : ℝ} (hδ : 0 ≤ δ)
    (hP : ∀ x' ∈ P, ∀ y' ∈ P, |(h₁ x' - h₁ y') - (h₂ x' - h₂ y')| ≤ δ * ‖x' - y'‖) (d : ℕ) :
    μHE[d] (Ω.graphOver h₁ '' P) ≤ ENNReal.ofReal (1 + δ) ^ d * μHE[d] (Ω.graphOver h₂ '' P) :=
  euclideanHausdorffMeasure_image_le_of_near hδ
    (fun x' _ y' _ => Ω.norm_sub_le_norm_graphOver_sub h₂ x' y')
    (fun x' hx y' hy => by
      rw [Ω.graphOver_sub_sub, norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs]
      exact hP x' hx y' hy) d

/-- The **linear graph** `S_g x' = x' + ⟪g, x'⟫ e` of `g ∈ H`, the graph of the linear function
`⟪g, ·⟫` over the hyperplane, as a linear map from `H` to `V`: the inclusion of `H` plus the
rank-one map `x' ↦ ⟪g, x'⟫ e`. -/
noncomputable def linearGraph (g : Ω.hyperplane) : Ω.hyperplane →ₗ[ℝ] V :=
  Ω.hyperplane.subtype + (innerSL ℝ g).toLinearMap.smulRight Ω.e

/-- The linear graph of `g` is the graph over the hyperplane of `⟪g, ·⟫`. -/
theorem coe_linearGraph (g : Ω.hyperplane) :
    ⇑(Ω.linearGraph g) = Ω.graphOver fun x' => inner ℝ g x' :=
  rfl

/-- **Inner products of a linear graph**:
`⟪S_g x', S_g y'⟫ = ⟪x', y'⟫ + ⟪g, x'⟫ ⟪g, y'⟫`, since `x', y' ⊥ e` and `‖e‖ = 1`. -/
theorem inner_linearGraph (g x' y' : Ω.hyperplane) :
    inner ℝ (Ω.linearGraph g x') (Ω.linearGraph g y') =
      inner ℝ x' y' + inner ℝ g x' * inner ℝ g y' := by
  rw [coe_linearGraph, graphOver, graphOver]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    Ω.inner_coe_e, Ω.inner_e_self, Submodule.coe_inner]
  rw [real_inner_comm (y' : V) Ω.e, Ω.inner_coe_e]
  ring

/-! ### The tilt of the hyperplane -/

/-- The **tilt** of `H` into `V` along a unit vector `u ∈ H` with slope `b`:
`J x' = x' + ⟪u, x'⟫ (c⁻¹ (u + b e) - u)` with `c = √(1 + b²)`. It maps `u` to the unit vector
`(u + b e)/c` and fixes the vectors of `H` orthogonal to `u`, so it preserves norms. -/
noncomputable def tilt (u : Ω.hyperplane) (b : ℝ) (x' : Ω.hyperplane) : V :=
  (x' : V) + inner ℝ u x' • ((√(1 + b ^ 2))⁻¹ • ((u : V) + b • Ω.e) - u)

/-- The tilt is additive in the sense `J (x' - y') = J x' - J y'`. -/
theorem tilt_sub (u : Ω.hyperplane) (b : ℝ) (x' y' : Ω.hyperplane) :
    Ω.tilt u b (x' - y') = Ω.tilt u b x' - Ω.tilt u b y' := by
  simp only [tilt, Submodule.coe_sub, inner_sub_right, sub_smul]
  abel

/-- **The tilt preserves norms**: `‖J x'‖ = ‖x'‖` for a unit vector `u`. With `a = ⟪u, x'⟫` and
`w = c⁻¹ (u + b e) - u`, `⟪x', w⟫ = a (c⁻¹ - 1)` and `‖w‖² = 2 - 2c⁻¹`, so
`‖x' + a w‖² = ‖x'‖²`. -/
theorem norm_tilt {u : Ω.hyperplane} (hu : ‖u‖ = 1) (b : ℝ) (x' : Ω.hyperplane) :
    ‖Ω.tilt u b x'‖ = ‖x'‖ := by
  have hc : 0 < √(1 + b ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hc2 : √(1 + b ^ 2) ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hxu : inner ℝ (x' : V) (u : V) = inner ℝ u x' := by
    rw [← Submodule.coe_inner, real_inner_comm]
  have hux : inner ℝ (u : V) (x' : V) = inner ℝ u x' := by rw [← Submodule.coe_inner]
  have huu : inner ℝ (u : V) (u : V) = 1 := by
    rw [real_inner_self_eq_norm_sq, Submodule.norm_coe, hu, one_pow]
  have hue : inner ℝ (u : V) Ω.e = 0 := Ω.inner_coe_e u
  have heu : inner ℝ Ω.e (u : V) = 0 := by rw [real_inner_comm, hue]
  have hxe : inner ℝ (x' : V) Ω.e = 0 := Ω.inner_coe_e x'
  have hex : inner ℝ Ω.e (x' : V) = 0 := by rw [real_inner_comm, hxe]
  have hee := Ω.inner_e_self
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [tilt, ← real_inner_self_eq_norm_sq, ← Submodule.norm_coe, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hxu, hux, huu, hue, heu, hxe, hex, hee]
  field_simp
  linear_combination (-inner ℝ u x' ^ 2) * hc2

/-- The tilt along a unit vector is an isometry of `H` into `V`. -/
theorem isometry_tilt {u : Ω.hyperplane} (hu : ‖u‖ = 1) (b : ℝ) : Isometry (Ω.tilt u b) :=
  Isometry.of_dist_eq fun x' y' => by
    rw [dist_eq_norm, dist_eq_norm, ← Ω.tilt_sub, Ω.norm_tilt hu]

/-- **Tilt after stretch**: stretching by `c = √(1 + b²)` along the unit vector `u` and then
tilting gives the graph of the linear function `b ⟪u, ·⟫`:
`J (D x') = x' + b ⟪u, x'⟫ e`. -/
theorem tilt_stretch {u : Ω.hyperplane} (hu : ‖u‖ = 1) (b : ℝ) (x' : Ω.hyperplane) :
    Ω.tilt u b (stretch u √(1 + b ^ 2) x') = Ω.graphOver (fun y' => b * inner ℝ u y') x' := by
  have hc : √(1 + b ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hinner : inner ℝ u (stretch u √(1 + b ^ 2) x') = √(1 + b ^ 2) * inner ℝ u x' := by
    rw [stretch_apply, inner_add_right, real_inner_smul_right, huu]
    ring
  rw [tilt, hinner, stretch_apply, graphOver, Submodule.coe_add, Submodule.coe_smul, smul_sub,
    smul_smul, show √(1 + b ^ 2) * inner ℝ u x' * (√(1 + b ^ 2))⁻¹ = inner ℝ u x' by
      field_simp]
  module

/-- For `g ≠ 0` and `u = g/‖g‖`, the linear graph of `g` is the tilt of slope `‖g‖` after the
stretch by `√(1 + ‖g‖²)` along `u`. -/
theorem linearGraph_eq_tilt_comp_stretch {g : Ω.hyperplane} (hg : g ≠ 0) :
    ⇑(Ω.linearGraph g) =
      Ω.tilt (‖g‖⁻¹ • g) ‖g‖ ∘ stretch (‖g‖⁻¹ • g) √(1 + ‖g‖ ^ 2) := by
  have hu : ‖‖g‖⁻¹ • g‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hg)]
  rw [coe_linearGraph]
  funext x'
  rw [Function.comp_apply, Ω.tilt_stretch hu]
  congr 1
  funext y'
  rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 hg), one_mul]

/-! ### The graph map -/

/-- The graph map is the graph of `φ|_H` over the hyperplane. -/
theorem graphMap_eq_graphOver : Ω.graphMap = Ω.graphOver Ω.phiH := rfl

/-- The graph map is injective. -/
theorem graphMap_injective : Function.Injective Ω.graphMap := Ω.graphOver_injective Ω.phiH

/-- The graph map is Lipschitz with constant `1 + M`. -/
theorem lipschitzWith_graphMap :
    LipschitzWith ⟨1 + Ω.M, by linarith [Ω.M_nonneg]⟩ Ω.graphMap :=
  LipschitzWith.of_dist_le_mul fun x' y' => by
    rw [dist_eq_norm, dist_eq_norm]
    exact Ω.norm_graphMap_sub_le x' y'

/-- The graph map is antilipschitz with constant `1`: `‖x' - y'‖ ≤ ‖γ x' - γ y'‖`. -/
theorem antilipschitzWith_graphMap : AntilipschitzWith 1 Ω.graphMap :=
  AntilipschitzWith.of_le_mul_dist fun x' y' => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact Ω.norm_sub_le_norm_graphOver_sub Ω.phiH x' y'

/-- The graph map does not shrink distances: `|x' - y'| ≤ |γ x' - γ y'|`
(`Rd.LipschitzGraph.antilipschitzWith_graphMap`). -/
theorem enorm_sub_le_enorm_graphMap_sub (x' y' : Ω.hyperplane) :
    ‖x' - y'‖ₑ ≤ ‖Ω.graphMap x' - Ω.graphMap y'‖ₑ := by
  simpa [eDist_eq_eNorm_sub] using Ω.antilipschitzWith_graphMap x' y'

/-- The graph map is Lipschitz: `|γ x' - γ y'| ≤ (1 + M) |x' - y'|`
(`Rd.LipschitzGraph.lipschitzWith_graphMap`). -/
theorem enorm_graphMap_sub_le (x' y' : Ω.hyperplane) :
    ‖Ω.graphMap x' - Ω.graphMap y'‖ₑ ≤ ENNReal.ofReal (1 + Ω.M) * ‖x' - y'‖ₑ := by
  have h := Ω.lipschitzWith_graphMap.edist_le_mul x' y'
  rw [eDist_eq_eNorm_sub, eDist_eq_eNorm_sub] at h
  rw [ENNReal.ofReal_eq_coe_nnreal (by linarith [Ω.M_nonneg])]
  exact h

variable [FiniteDimensional ℝ V]

/-- The graph map is a measurable embedding: an antilipschitz uniformly continuous map from the
complete space `H` is a closed embedding. -/
theorem measurableEmbedding_graphMap [MeasurableSpace V] [BorelSpace V] :
    MeasurableEmbedding Ω.graphMap :=
  (Ω.antilipschitzWith_graphMap.isClosedEmbedding
    Ω.lipschitzWith_graphMap.uniformContinuous).measurableEmbedding

/-! ### The norm determinant of a linear graph -/

/-- `S_g* S_g x' = x' + ⟪g, x'⟫ g`: the Gram operator of the linear graph is Mathlib's
transvection of `⟪g, ·⟫` and `g`, by `inner_linearGraph`. -/
theorem adjoint_comp_linearGraph (g : Ω.hyperplane) :
    LinearMap.adjoint (Ω.linearGraph g) ∘ₗ Ω.linearGraph g =
      LinearMap.transvection (innerSL ℝ g).toLinearMap g := by
  refine LinearMap.ext fun x' => ext_inner_right ℝ fun y' => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_linearGraph,
    LinearMap.transvection.apply, inner_add_left, real_inner_smul_left]
  rfl

/-- **The norm determinant of a linear graph** is `√(1 + ‖g‖²)` (Mathlib's
`LinearMap.normDet`, the volume factor `√(det(S_g* S_g))` of a linear map between spaces of
different dimensions): `S_g* S_g` is a transvection of determinant `1 + ⟪g, g⟫`
(Mathlib's `LinearMap.normDet_sq` and `LinearMap.transvection.det`). -/
theorem normDet_linearGraph (g : Ω.hyperplane) :
    (Ω.linearGraph g).normDet = √(1 + ‖g‖ ^ 2) := by
  have h := (Ω.linearGraph g).normDet_sq
  rw [adjoint_comp_linearGraph, LinearMap.transvection.det, ContinuousLinearMap.coe_coe,
    innerSL_apply_apply, real_inner_self_eq_norm_sq] at h
  rw [← h]
  exact (Real.sqrt_sq (LinearMap.normDet_nonneg _)).symm

/-! ### The gradient and the Gram density -/

/-- The **gradient** `∇φ(x') ∈ H` of `φ|_H` (Mathlib's `gradient`; it is `0` where `φ|_H` is not
differentiable). -/
noncomputable def gradPhi (x' : Ω.hyperplane) : Ω.hyperplane := gradient Ω.phiH x'

/-- `⟪∇φ(x'), v⟫` is the derivative of `φ|_H` at `x'` in the direction `v` (Mathlib's
`inner_gradient_left`). -/
theorem inner_gradPhi (x' v : Ω.hyperplane) :
    inner ℝ (Ω.gradPhi x') v = fderiv ℝ Ω.phiH x' v :=
  inner_gradient_left

/-- `‖∇φ(x')‖ ≤ M`. -/
theorem norm_gradPhi_le (x' : Ω.hyperplane) : ‖Ω.gradPhi x'‖ ≤ Ω.M := by
  rw [gradPhi, gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ Ω.lipschitzWith_phiH

/-- The **Gram density** `√(1 + ‖∇φ(x')‖²)` of the graph map. Where `φ|_H` is differentiable,
the derivative of the graph map at `x'` is the linear graph of `∇φ(x')`, and the density is its
norm determinant in Mathlib's sense (`normDet_linearGraph`). -/
noncomputable def gram (x' : Ω.hyperplane) : ℝ := √(1 + ‖Ω.gradPhi x'‖ ^ 2)

/-- The Gram density is at least `1`. -/
theorem one_le_gram (x' : Ω.hyperplane) : 1 ≤ Ω.gram x' :=
  Real.one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))

/-- The Gram density is positive. -/
theorem gram_pos (x' : Ω.hyperplane) : 0 < Ω.gram x' := one_pos.trans_le (Ω.one_le_gram x')

/-- The Gram density `√(1 + ‖∇φ(x')‖²)` is at least `1`, as an element of `[0, ∞]`. -/
theorem one_le_ofReal_gram (x' : Ω.hyperplane) : 1 ≤ ENNReal.ofReal (Ω.gram x') :=
  ENNReal.one_le_ofReal.2 (Ω.one_le_gram x')

/-- The Gram density is at most `√(1 + M²)`. -/
theorem gram_le (x' : Ω.hyperplane) : Ω.gram x' ≤ √(1 + Ω.M ^ 2) := by
  refine Real.sqrt_le_sqrt (add_le_add le_rfl ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (Ω.norm_gradPhi_le x') 2

/-- `|√(1 + ‖∇φ(x')‖²) - √(1 + ‖g‖²)| ≤ ‖∇φ(x') - g‖`. -/
theorem abs_gram_sub_le (x' g : Ω.hyperplane) :
    |Ω.gram x' - √(1 + ‖g‖ ^ 2)| ≤ ‖Ω.gradPhi x' - g‖ :=
  (abs_sqrt_one_add_sq_sub_le _ _).trans (abs_norm_sub_norm_le _ _)

/-! ### The outward unit normal -/

/-- The **outward unit normal** at the boundary point `γ x'`:
`ν(x') = (∇φ(x') - e) / √(1 + ‖∇φ(x')‖²)`. Where `φ|_H` is differentiable, it is the
normalised gradient at `γ x'` of `x ↦ φ(Px) - ⟪x, e⟫`, a function that is negative on `Ω`. -/
noncomputable def normalAt (x' : Ω.hyperplane) : V :=
  (Ω.gram x')⁻¹ • ((Ω.gradPhi x' : V) - Ω.e)

/-- `‖∇φ(x') - e‖ = √(1 + ‖∇φ(x')‖²)`, by Pythagoras. -/
theorem norm_gradPhi_sub_e (x' : Ω.hyperplane) : ‖(Ω.gradPhi x' : V) - Ω.e‖ = Ω.gram x' := by
  have h := Ω.norm_coe_add_smul_e_sq (Ω.gradPhi x') (-1)
  rw [neg_one_smul, ← sub_eq_add_neg, neg_one_sq, add_comm] at h
  rw [gram, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- The normal is a unit vector. -/
theorem norm_normalAt (x' : Ω.hyperplane) : ‖Ω.normalAt x'‖ = 1 := by
  rw [normalAt, norm_smul, norm_inv, Real.norm_of_nonneg (Ω.gram_pos x').le,
    Ω.norm_gradPhi_sub_e, inv_mul_cancel₀ (Ω.gram_pos x').ne']

/-- `⟪ν(x'), e⟫ = -1/√(1 + ‖∇φ(x')‖²) < 0`: the normal points downwards, out of `Ω`. -/
theorem inner_normalAt_e (x' : Ω.hyperplane) : inner ℝ (Ω.normalAt x') Ω.e = -(Ω.gram x')⁻¹ := by
  rw [normalAt, real_inner_smul_left, inner_sub_left, Ω.inner_coe_e, Ω.inner_e_self]
  ring

/-- **The normal points away from the cone**: `⟪ν(x'), y⟫ < 0` for every `y` in the cone `K`,
since `⟪∇φ(x'), y⟫ = ⟪∇φ(x'), Py⟫ ≤ M ‖Py‖ < ⟪y, e⟫`. -/
theorem inner_normalAt_neg_of_mem_cone (x' : Ω.hyperplane) {y : V} (hy : y ∈ Ω.cone) :
    inner ℝ (Ω.normalAt x') y < 0 := by
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e := hy
  have hP : inner ℝ (Ω.gradPhi x' : V) y =
      inner ℝ (Ω.gradPhi x' : V) (y - inner ℝ y Ω.e • Ω.e) := by
    rw [inner_sub_right, real_inner_smul_right, Ω.inner_coe_e, mul_zero, sub_zero]
  have hle : inner ℝ (Ω.gradPhi x' : V) y ≤ Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ := by
    rw [hP]
    refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Submodule.norm_coe]
    exact Ω.norm_gradPhi_le x'
  have hneg : inner ℝ ((Ω.gradPhi x' : V) - Ω.e) y < 0 := by
    rw [inner_sub_left, real_inner_comm y Ω.e]
    linarith
  rw [normalAt, real_inner_smul_left]
  exact mul_neg_of_pos_of_neg (inv_pos.2 (Ω.gram_pos x')) hneg

/-! ### Good pieces -/

/-- A **good piece** for the accuracy `ε` and the gradient value `g`: on `P` the increments of
`φ|_H` are within `2ε ‖x' - y'‖` of those of the linear function `⟪g, ·⟫`, and
`‖∇φ - g‖ ≤ ε`. -/
def IsGoodPiece (ε : ℝ) (g : Ω.hyperplane) (P : Set Ω.hyperplane) : Prop :=
  (∀ x' ∈ P, ∀ y' ∈ P,
    |(Ω.phiH x' - Ω.phiH y') - (inner ℝ g x' - inner ℝ g y')| ≤ 2 * ε * ‖x' - y'‖) ∧
  ∀ x' ∈ P, ‖Ω.gradPhi x' - g‖ ≤ ε

variable {Ω} in
/-- Subsets of good pieces are good pieces. -/
theorem IsGoodPiece.mono {ε : ℝ} {g : Ω.hyperplane} {P Q : Set Ω.hyperplane}
    (h : Ω.IsGoodPiece ε g P) (hQ : Q ⊆ P) : Ω.IsGoodPiece ε g Q :=
  ⟨fun x' hx y' hy => h.1 x' (hQ hx) y' (hQ hy), fun x' hx => h.2 x' (hQ hx)⟩

variable {Ω} in
/-- On a good piece, `√(1 + ‖g‖²) ≤ (1 + ε) √(1 + ‖∇φ(x')‖²)`, since the Gram density is at
least `1` and within `ε` of `√(1 + ‖g‖²)`. -/
theorem IsGoodPiece.sqrt_le_mul_gram {ε : ℝ} (hε : 0 ≤ ε) {g : Ω.hyperplane}
    {P : Set Ω.hyperplane} (h : Ω.IsGoodPiece ε g P) {x' : Ω.hyperplane} (hx : x' ∈ P) :
    √(1 + ‖g‖ ^ 2) ≤ (1 + ε) * Ω.gram x' := by
  have h1 := (abs_sub_comm _ _).trans_le ((Ω.abs_gram_sub_le x' g).trans (h.2 x' hx))
  have h2 := Ω.one_le_gram x'
  have h3 := (abs_le.1 h1).2
  nlinarith

variable {Ω} in
/-- On a good piece, `√(1 + ‖∇φ(x')‖²) ≤ (1 + ε) √(1 + ‖g‖²)`. -/
theorem IsGoodPiece.gram_le_mul_sqrt {ε : ℝ} (hε : 0 ≤ ε) {g : Ω.hyperplane}
    {P : Set Ω.hyperplane} (h : Ω.IsGoodPiece ε g P) {x' : Ω.hyperplane} (hx : x' ∈ P) :
    Ω.gram x' ≤ (1 + ε) * √(1 + ‖g‖ ^ 2) := by
  have h1 := (Ω.abs_gram_sub_le x' g).trans (h.2 x' hx)
  have h2 : 1 ≤ √(1 + ‖g‖ ^ 2) := Real.one_le_sqrt.2 (le_add_of_nonneg_right (sq_nonneg _))
  have h3 := (abs_le.1 h1).2
  nlinarith

open TopologicalSpace in
/-- The **good sets**, for `ε > 0` and `i, k ∈ ℕ`: the points `x'` where `φ|_H` is
differentiable, `‖∇φ(x') - u_i‖ < ε`, and the first-order Taylor remainder at `x'` is at most
`ε ‖y' - x'‖` for every member `y' = u_l` of the dense sequence `(u_l)_l` of `H`
(Mathlib's `TopologicalSpace.denseSeq`) with `‖y' - x'‖ < 1/(k+1)`. -/
def goodSet (ε : ℝ) (i k : ℕ) : Set Ω.hyperplane :=
  {x' | DifferentiableAt ℝ Ω.phiH x' ∧ ‖Ω.gradPhi x' - denseSeq Ω.hyperplane i‖ < ε ∧
    ∀ l, ‖denseSeq Ω.hyperplane l - x'‖ < 1 / (k + 1) →
      |Ω.phiH (denseSeq Ω.hyperplane l) - Ω.phiH x' -
        inner ℝ (Ω.gradPhi x') (denseSeq Ω.hyperplane l - x')| ≤
        ε * ‖denseSeq Ω.hyperplane l - x'‖}

open TopologicalSpace in
/-- **The Taylor bound on a good set holds near `x'`**: for `x'` in a good set,
`|φ(y') - φ(x') - ⟪∇φ(x'), y' - x'⟫| ≤ ε ‖y' - x'‖` for every `y'` with `‖y' - x'‖ < 1/(k+1)`,
since the inequality is closed in `y'` and holds on the dense sequence. -/
theorem abs_taylor_le_of_mem_goodSet {ε : ℝ} {i k : ℕ} {x' : Ω.hyperplane}
    (hx : x' ∈ Ω.goodSet ε i k) (y' : Ω.hyperplane) (hy : ‖y' - x'‖ < 1 / (k + 1)) :
    |Ω.phiH y' - Ω.phiH x' - inner ℝ (Ω.gradPhi x') (y' - x')| ≤ ε * ‖y' - x'‖ := by
  refine (denseRange_denseSeq Ω.hyperplane).induction_on
    (p := fun y' => ‖y' - x'‖ < 1 / (k + 1) →
      |Ω.phiH y' - Ω.phiH x' - inner ℝ (Ω.gradPhi x') (y' - x')| ≤ ε * ‖y' - x'‖) y' ?_
    hx.2.2 hy
  exact isClosed_imp (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    (isClosed_le (((Ω.continuous_phiH.sub continuous_const).sub
      (continuous_const.inner (continuous_id.sub continuous_const))).abs)
      (continuous_const.mul (continuous_id.sub continuous_const).norm))

open TopologicalSpace in
/-- **Good sets cut into small balls are good pieces**: on `goodSet ε i k ∩ B(c, 1/(2(k+1)))`
the increments of `φ|_H` are within `2ε ‖x' - y'‖` of those of `⟪u_i, ·⟫`: the Taylor bound at
`y'` and `‖∇φ(y') - u_i‖ < ε`. -/
theorem isGoodPiece_goodSet_inter_ball (ε : ℝ) (i k : ℕ) (c : Ω.hyperplane) :
    Ω.IsGoodPiece ε (denseSeq Ω.hyperplane i)
      (Ω.goodSet ε i k ∩ ball c (1 / (2 * (k + 1)))) := by
  refine ⟨fun x' hx y' hy => ?_, fun x' hx => hx.1.2.1.le⟩
  have hxy : ‖x' - y'‖ < 1 / (k + 1) := by
    rw [← dist_eq_norm]
    calc dist x' y' ≤ dist x' c + dist y' c := dist_triangle_right _ _ _
      _ < 1 / (2 * (k + 1)) + 1 / (2 * (k + 1)) := add_lt_add hx.2 hy.2
      _ = 1 / (k + 1) := by field_simp; ring
  have ht := Ω.abs_taylor_le_of_mem_goodSet hy.1 x' hxy
  have hin : |inner ℝ (Ω.gradPhi y' - denseSeq Ω.hyperplane i) (x' - y')| ≤ ε * ‖x' - y'‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right hy.1.2.1.le (norm_nonneg _))
  have heq : (Ω.phiH x' - Ω.phiH y') -
      (inner ℝ (denseSeq Ω.hyperplane i) x' - inner ℝ (denseSeq Ω.hyperplane i) y') =
      (Ω.phiH x' - Ω.phiH y' - inner ℝ (Ω.gradPhi y') (x' - y')) +
        inner ℝ (Ω.gradPhi y' - denseSeq Ω.hyperplane i) (x' - y') := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [heq]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ε * ‖x' - y'‖ + ε * ‖x' - y'‖ := add_le_add ht hin
    _ = 2 * ε * ‖x' - y'‖ := by ring

open TopologicalSpace in
/-- **The good sets cover the differentiability points**: if `φ|_H` is differentiable at `x'`,
then `x' ∈ goodSet ε i k ∩ B(u_j, 1/(2(k+1)))` for some `i`, `k`, `j`: `k` from the definition
of the derivative, `i` and `j` by density. -/
theorem exists_mem_goodSet_inter_ball {ε : ℝ} (hε : 0 < ε) {x' : Ω.hyperplane}
    (hx : DifferentiableAt ℝ Ω.phiH x') :
    ∃ i k j, x' ∈ Ω.goodSet ε i k ∩ ball (denseSeq Ω.hyperplane j) (1 / (2 * (k + 1))) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hx.hasFDerivAt.isLittleO.def hε)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  obtain ⟨i, hi⟩ := (denseRange_denseSeq Ω.hyperplane).exists_dist_lt (Ω.gradPhi x') hε
  obtain ⟨j, hj⟩ := (denseRange_denseSeq Ω.hyperplane).exists_dist_lt x'
    (by positivity : (0 : ℝ) < 1 / (2 * (k + 1)))
  refine ⟨i, k, j, ⟨hx, by rwa [← dist_eq_norm], fun l hl => ?_⟩, ?_⟩
  · have h := hball (y := denseSeq Ω.hyperplane l) (by rw [dist_eq_norm]; exact hl.trans hk)
    rwa [Real.norm_eq_abs, ← Ω.inner_gradPhi] at h
  · rw [mem_ball]
    exact hj

variable [MeasurableSpace V] [BorelSpace V]

/-- The gradient is measurable (Mathlib's `measurable_fderiv`). -/
theorem measurable_gradPhi : Measurable Ω.gradPhi :=
  (InnerProductSpace.toDual ℝ Ω.hyperplane).symm.continuous.measurable.comp
    (measurable_fderiv ℝ Ω.phiH)

/-- The Gram density is measurable. -/
theorem measurable_gram : Measurable Ω.gram :=
  ((Ω.measurable_gradPhi.norm.pow_const 2).const_add 1).sqrt

/-- The outward unit normal is measurable. -/
theorem measurable_normalAt : Measurable Ω.normalAt :=
  (Ω.measurable_gram.inv).smul
    ((continuous_subtype_val.measurable.comp Ω.measurable_gradPhi).sub measurable_const)

/-- **Rademacher's theorem** for `φ|_H`: it is differentiable almost everywhere on `H`. -/
theorem ae_differentiableAt_phiH :
    ∀ᵐ x' ∂(volume : Measure Ω.hyperplane), DifferentiableAt ℝ Ω.phiH x' :=
  Ω.lipschitzWith_phiH.ae_differentiableAt

/-! ### The linear case -/

/-- **The area formula for linear graphs**: for the linear graph `S_g x' = x' + ⟪g, x'⟫ e` and
every `P ⊆ H`, `μHE[m] (S_g '' P) = √(1 + ‖g‖²) vol(P)`, `m = dim H`: Mathlib's area formula
for linear maps (`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume`) with the
norm determinant `√(1 + ‖g‖²)` (`normDet_linearGraph`). -/
theorem euclideanHausdorffMeasure_linearGraph_image (g : Ω.hyperplane) (P : Set Ω.hyperplane) :
    μHE[finrank ℝ Ω.hyperplane] (Ω.linearGraph g '' P) =
      ENNReal.ofReal √(1 + ‖g‖ ^ 2) * volume P := by
  rw [LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, normDet_linearGraph]

/-! ### The graph map on null sets and on good pieces -/

/-- **The graph map keeps null sets**: `μHE[m] (γ '' N) = 0` for every null set `N ⊆ H`, since
`γ` is Lipschitz and `μHE[m]` is the volume on `H`. -/
theorem euclideanHausdorffMeasure_graphMap_image_eq_zero {N : Set Ω.hyperplane}
    (hN : volume N = 0) : μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' N) = 0 := by
  have h := Ω.lipschitzWith_graphMap.lipschitzOnWith.euclideanHausdorffMeasure_image_le
    (s := N) (finrank ℝ Ω.hyperplane)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Ω.hyperplane), hN,
    mul_zero] at h
  exact le_antisymm h zero_le

variable {Ω} in
/-- **Upper bound on a good piece**:
`μHE[m] (γ '' P) ≤ C_ε ∫_P √(1 + ‖∇φ‖²)` with the area factor `C_ε = (1 + 2ε)^m (1 + ε)`, from
the comparison with the linear graph of `g` (`euclideanHausdorffMeasure_graphOver_image_le` with
`δ = 2ε`) and its area. -/
theorem IsGoodPiece.euclideanHausdorffMeasure_image_le {ε : ℝ} (hε : 0 ≤ ε)
    {g : Ω.hyperplane} {P : Set Ω.hyperplane} (h : Ω.IsGoodPiece ε g P) :
    μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' P) ≤
      ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        ∫⁻ x' in P, ENNReal.ofReal (Ω.gram x') := by
  have h1 : μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' P) ≤
      ENNReal.ofReal (1 + 2 * ε) ^ finrank ℝ Ω.hyperplane *
        μHE[finrank ℝ Ω.hyperplane] (Ω.linearGraph g '' P) :=
    Ω.euclideanHausdorffMeasure_graphOver_image_le Ω.phiH (fun x' => inner ℝ g x')
      (by positivity) h.1 _
  have h2 : ENNReal.ofReal √(1 + ‖g‖ ^ 2) * volume P ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ x' in P, ENNReal.ofReal (Ω.gram x') := by
    rw [← setLIntegral_const, ← lintegral_const_mul _ Ω.measurable_gram.ennreal_ofReal]
    refine setLIntegral_mono (measurable_const.mul Ω.measurable_gram.ennreal_ofReal)
      fun x' hx => ?_
    rw [← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (h.sqrt_le_mul_gram hε hx)
  rw [Ω.euclideanHausdorffMeasure_linearGraph_image] at h1
  calc _ ≤ _ := h1
    _ ≤ ENNReal.ofReal (1 + 2 * ε) ^ finrank ℝ Ω.hyperplane *
        (ENNReal.ofReal (1 + ε) * ∫⁻ x' in P, ENNReal.ofReal (Ω.gram x')) :=
      mul_le_mul' le_rfl h2
    _ = _ := by
      rw [areaFactor, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by linarith),
        mul_assoc]

variable {Ω} in
/-- **Lower bound on a good piece**:
`∫_P √(1 + ‖∇φ‖²) ≤ C_ε μHE[m] (γ '' P)` with the area factor `C_ε = (1 + 2ε)^m (1 + ε)`. -/
theorem IsGoodPiece.lintegral_gram_le {ε : ℝ} (hε : 0 ≤ ε) {g : Ω.hyperplane}
    {P : Set Ω.hyperplane} (h : Ω.IsGoodPiece ε g P) :
    ∫⁻ x' in P, ENNReal.ofReal (Ω.gram x') ≤
      ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' P) := by
  have h1 : μHE[finrank ℝ Ω.hyperplane] (Ω.linearGraph g '' P) ≤
      ENNReal.ofReal (1 + 2 * ε) ^ finrank ℝ Ω.hyperplane *
        μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' P) :=
    Ω.euclideanHausdorffMeasure_graphOver_image_le (fun x' => inner ℝ g x') Ω.phiH
      (by positivity)
      (fun x' hx y' hy => by rw [abs_sub_comm]; exact h.1 x' hx y' hy) _
  have h2 : ∫⁻ x' in P, ENNReal.ofReal (Ω.gram x') ≤
      ENNReal.ofReal (1 + ε) * (ENNReal.ofReal √(1 + ‖g‖ ^ 2) * volume P) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), ← setLIntegral_const]
    exact setLIntegral_mono measurable_const fun x' hx =>
      ENNReal.ofReal_le_ofReal (h.gram_le_mul_sqrt hε hx)
  rw [← Ω.euclideanHausdorffMeasure_linearGraph_image] at h2
  calc _ ≤ _ := h2
    _ ≤ ENNReal.ofReal (1 + ε) * (ENNReal.ofReal (1 + 2 * ε) ^ finrank ℝ Ω.hyperplane *
        μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' P)) := mul_le_mul' le_rfl h1
    _ = _ := by
      rw [areaFactor, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by linarith)]
      ring

/-! ### A countable partition into good pieces -/

open TopologicalSpace in
/-- The good sets are measurable: the differentiability set is measurable (Mathlib's
`measurableSet_of_differentiableAt`), the gradient is measurable, and the Taylor condition
quantifies over the countable dense sequence only. -/
theorem measurableSet_goodSet (ε : ℝ) (i k : ℕ) : MeasurableSet (Ω.goodSet ε i k) := by
  have hset : Ω.goodSet ε i k = {x' | DifferentiableAt ℝ Ω.phiH x'} ∩
      ({x' | ‖Ω.gradPhi x' - denseSeq Ω.hyperplane i‖ < ε} ∩
        ⋂ l, {x' | ‖denseSeq Ω.hyperplane l - x'‖ < 1 / (k + 1) →
          |Ω.phiH (denseSeq Ω.hyperplane l) - Ω.phiH x' -
            inner ℝ (Ω.gradPhi x') (denseSeq Ω.hyperplane l - x')| ≤
            ε * ‖denseSeq Ω.hyperplane l - x'‖}) := by
    ext x'
    simp only [goodSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine (measurableSet_of_differentiableAt ℝ Ω.phiH).inter
    ((measurableSet_lt (Ω.measurable_gradPhi.sub_const _).norm measurable_const).inter
      (MeasurableSet.iInter fun l => MeasurableSet.imp
        (measurableSet_lt (measurable_const.sub measurable_id).norm measurable_const)
        (measurableSet_le ?_ (measurable_const.mul (measurable_const.sub measurable_id).norm))))
  exact continuous_abs.measurable.comp ((measurable_const.sub Ω.continuous_phiH.measurable).sub
    (Measurable.inner Ω.measurable_gradPhi (measurable_const.sub measurable_id)))

open TopologicalSpace in
/-- **A countable partition into good pieces**: for `ε > 0` there are disjoint measurable sets
`Q_n ⊆ H` covering `H` up to a null set, and gradient values `g_n`, such that each `Q_n` is a
good piece for `ε` and `g_n`. The sets `goodSet ε i k ∩ B(u_j, 1/(2(k+1)))` cover the
differentiability points of `φ|_H`, whose complement is null by Rademacher's theorem; Mathlib's
`disjointed` makes them disjoint. -/
theorem exists_goodPartition {ε : ℝ} (hε : 0 < ε) :
    ∃ (Q : ℕ → Set Ω.hyperplane) (g : ℕ → Ω.hyperplane), (∀ n, MeasurableSet (Q n)) ∧
      Pairwise (Disjoint on Q) ∧ volume (⋃ n, Q n)ᶜ = 0 ∧ ∀ n, Ω.IsGoodPiece ε (g n) (Q n) := by
  let e := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm
  let f : ℕ → Set Ω.hyperplane := fun n => Ω.goodSet ε (e n).1 (e n).2.1 ∩
    ball (denseSeq Ω.hyperplane (e n).2.2) (1 / (2 * ((e n).2.1 + 1)))
  refine ⟨disjointed f, fun n => denseSeq Ω.hyperplane (e n).1,
    MeasurableSet.disjointed fun n => (Ω.measurableSet_goodSet _ _ _).inter measurableSet_ball,
    disjoint_disjointed f, ?_,
    fun n => (Ω.isGoodPiece_goodSet_inter_ball _ _ _ _).mono (disjointed_le f n)⟩
  rw [iUnion_disjointed]
  refine measure_mono_null ?_ (ae_iff.1 Ω.ae_differentiableAt_phiH)
  intro x' hx hd
  obtain ⟨i, k, j, hmem⟩ := Ω.exists_mem_goodSet_inter_ball hε hd
  refine hx (Set.mem_iUnion.2 ⟨e.symm (i, k, j), ?_⟩)
  simpa only [f, Equiv.apply_symm_apply] using hmem

/-! ### The area formula -/

/-- **Upper bound for a fixed accuracy**: for `ε > 0` and measurable `A ⊆ H`,
`μHE[m] (γ '' A) ≤ C_ε ∫_A √(1 + ‖∇φ‖²)` with the area factor `C_ε = (1 + 2ε)^m (1 + ε)`: sum
the bounds on the good pieces
`A ∩ Q_n`; the rest of `A` is null and so is its image. -/
theorem euclideanHausdorffMeasure_graphMap_image_le_mul {ε : ℝ} (hε : 0 < ε)
    {A : Set Ω.hyperplane} (hA : MeasurableSet A) :
    μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' A) ≤
      ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        ∫⁻ x' in A, ENNReal.ofReal (Ω.gram x') := by
  obtain ⟨Q, g, hQm, hQd, hQnull, hQg⟩ := Ω.exists_goodPartition hε
  have hsplit : Ω.graphMap '' A ⊆
      (⋃ n, Ω.graphMap '' (A ∩ Q n)) ∪ Ω.graphMap '' (A \ ⋃ n, Q n) := by
    rintro _ ⟨x', hx, rfl⟩
    by_cases h : x' ∈ ⋃ n, Q n
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
      exact Or.inl (Set.mem_iUnion.2 ⟨n, x', ⟨hx, hn⟩, rfl⟩)
    · exact Or.inr ⟨x', ⟨hx, h⟩, rfl⟩
  have hnull : μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' (A \ ⋃ n, Q n)) = 0 :=
    Ω.euclideanHausdorffMeasure_graphMap_image_eq_zero
      (measure_mono_null (fun x' hx => hx.2) hQnull)
  have hdisj : Pairwise (Disjoint on fun n => A ∩ Q n) := fun i j hij =>
    (hQd hij).mono Set.inter_subset_right Set.inter_subset_right
  calc μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' A)
      ≤ μHE[finrank ℝ Ω.hyperplane] (⋃ n, Ω.graphMap '' (A ∩ Q n)) := by
        refine (measure_mono hsplit).trans ((measure_union_le _ _).trans ?_)
        rw [hnull, add_zero]
    _ ≤ ∑' n, μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' (A ∩ Q n)) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        ∫⁻ x' in A ∩ Q n, ENNReal.ofReal (Ω.gram x') := tsum_le_tsum fun n =>
          ((hQg n).mono Set.inter_subset_right).euclideanHausdorffMeasure_image_le hε.le
    _ = ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        ∫⁻ x' in ⋃ n, A ∩ Q n, ENNReal.ofReal (Ω.gram x') := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun n => hA.inter (hQm n)) hdisj]
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set (Set.iUnion_subset fun n =>
          Set.inter_subset_left))

/-- **Lower bound for a fixed accuracy**: for `ε > 0` and measurable `A ⊆ H`,
`∫_A √(1 + ‖∇φ‖²) ≤ C_ε μHE[m] (γ '' A)` with the area factor `C_ε = (1 + 2ε)^m (1 + ε)`: the
integral over the null rest of `A` vanishes, and the images `γ '' (A ∩ Q_n)` are disjoint and
measurable, since `γ` is an injective measurable embedding. -/
theorem lintegral_gram_le_mul {ε : ℝ} (hε : 0 < ε) {A : Set Ω.hyperplane}
    (hA : MeasurableSet A) :
    ∫⁻ x' in A, ENNReal.ofReal (Ω.gram x') ≤
      ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' A) := by
  obtain ⟨Q, g, hQm, hQd, hQnull, hQg⟩ := Ω.exists_goodPartition hε
  have hdisj : Pairwise (Disjoint on fun n => A ∩ Q n) := fun i j hij =>
    (hQd hij).mono Set.inter_subset_right Set.inter_subset_right
  have hA' : ∫⁻ x' in A, ENNReal.ofReal (Ω.gram x') =
      ∫⁻ x' in ⋃ n, A ∩ Q n, ENNReal.ofReal (Ω.gram x') := by
    have hzero : ∫⁻ x' in A \ ⋃ n, Q n, ENNReal.ofReal (Ω.gram x') = 0 :=
      setLIntegral_measure_zero _ _ (measure_mono_null (fun x' hx => hx.2) hQnull)
    rw [← lintegral_inter_add_sdiff _ A (MeasurableSet.iUnion hQm), hzero, add_zero,
      Set.inter_iUnion]
  have himg : Pairwise (Disjoint on fun n => Ω.graphMap '' (A ∩ Q n)) := fun i j hij =>
    (Set.disjoint_image_iff Ω.graphMap_injective).2 (hdisj hij)
  calc ∫⁻ x' in A, ENNReal.ofReal (Ω.gram x')
      = ∑' n, ∫⁻ x' in A ∩ Q n, ENNReal.ofReal (Ω.gram x') := by
        rw [hA', lintegral_iUnion (fun n => hA.inter (hQm n)) hdisj]
    _ ≤ ∑' n, ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        μHE[finrank ℝ Ω.hyperplane] (Ω.graphMap '' (A ∩ Q n)) := tsum_le_tsum fun n =>
          ((hQg n).mono Set.inter_subset_right).lintegral_gram_le hε.le
    _ = ENNReal.ofReal (areaFactor (finrank ℝ Ω.hyperplane) ε) *
        μHE[finrank ℝ Ω.hyperplane] (⋃ n, Ω.graphMap '' (A ∩ Q n)) := by
      rw [ENNReal.tsum_mul_left, measure_iUnion himg fun n =>
        Ω.measurableEmbedding_graphMap.measurableSet_image.2 (hA.inter (hQm n))]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (Set.iUnion_subset fun n =>
          Set.image_mono Set.inter_subset_left))

/-- **The area formula for Lipschitz graphs**: for every measurable `A ⊆ H`,
`μHE[n-1] (γ '' A) = ∫_A √(1 + ‖∇φ(x')‖²) dx'`, where `n = dim V`, `μHE[n-1]` is Mathlib's
`(n-1)`-dimensional Euclidean Hausdorff measure on `V`, normalised to be the volume on
hyperplanes, and `γ x' = x' + φ(x') e` is the graph map. The two bounds for a fixed `ε > 0`
(`euclideanHausdorffMeasure_graphMap_image_le_mul`, `lintegral_gram_le_mul`) carry the area
factor `(1 + 2ε)^(n-1) (1 + ε)` (`Rd.areaFactor`), which tends to `1` as `ε → 0`
(`Rd.tendsto_areaFactor`, `Rd.le_of_forall_pos_le_ofReal_mul_of_tendsto`). -/
theorem euclideanHausdorffMeasure_graphMap_image {A : Set Ω.hyperplane} (hA : MeasurableSet A) :
    μHE[finrank ℝ V - 1] (Ω.graphMap '' A) = ∫⁻ x' in A, ENNReal.ofReal (Ω.gram x') := by
  rw [← Ω.finrank_hyperplane_eq_sub_one]
  exact le_antisymm
    (le_of_forall_pos_le_ofReal_mul_of_tendsto (tendsto_areaFactor _) fun _ hε =>
      Ω.euclideanHausdorffMeasure_graphMap_image_le_mul hε hA)
    (le_of_forall_pos_le_ofReal_mul_of_tendsto (tendsto_areaFactor _) fun _ hε =>
      Ω.lintegral_gram_le_mul hε hA)

/-- **The area formula in measure form**: the image under the graph map of the measure on `H`
with density `√(1 + ‖∇φ‖²)` is `μHE[n-1]` restricted to the graph `γ(H)`. -/
theorem map_graphMap_withDensity :
    Measure.map Ω.graphMap
        ((volume : Measure Ω.hyperplane).withDensity fun x' => ENNReal.ofReal (Ω.gram x')) =
      (μHE[finrank ℝ V - 1] : Measure V).restrict (Set.range Ω.graphMap) := by
  ext B hB
  have hpre := Ω.measurableEmbedding_graphMap.measurable hB
  rw [Measure.map_apply Ω.measurableEmbedding_graphMap.measurable hB, withDensity_apply _ hpre,
    Measure.restrict_apply hB, ← Set.image_preimage_eq_inter_range,
    Ω.euclideanHausdorffMeasure_graphMap_image hpre]

/-- **The area formula in integral form**: for every `F : V → [0, ∞]`,
`∫_{γ(H)} F dμHE[n-1] = ∫_H F(γ x') √(1 + ‖∇φ(x')‖²) dx'`. The formula holds for every `F`,
measurable or not, since `γ` is a measurable embedding and the density is finite. -/
theorem lintegral_graphMap (F : V → ℝ≥0∞) :
    ∫⁻ y in Set.range Ω.graphMap, F y ∂(μHE[finrank ℝ V - 1] : Measure V) =
      ∫⁻ x', F (Ω.graphMap x') * ENNReal.ofReal (Ω.gram x') := by
  rw [← Ω.map_graphMap_withDensity, Ω.measurableEmbedding_graphMap.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ Ω.measurable_gram.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [Pi.mul_apply, mul_comm]

/-- **The area formula for complex integrals**: for every `F : V → ℂ`,
`∫_{γ(H)} F dμHE[n-1] = ∫_H F(γ x') √(1 + ‖∇φ(x')‖²) dx'`. It holds for every `F`, since `γ` is a
measurable embedding and the density is finite (`Rd.LipschitzGraph.map_graphMap_withDensity`). -/
theorem integral_graphMap (F : V → ℂ) :
    ∫ y in Set.range Ω.graphMap, F y ∂(μHE[finrank ℝ V - 1] : Measure V) =
      ∫ x', F (Ω.graphMap x') * (Ω.gram x' : ℂ) := by
  rw [← Ω.map_graphMap_withDensity, Ω.measurableEmbedding_graphMap.integral_map,
    integral_withDensity_eq_integral_toReal_smul Ω.measurable_gram.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x' => ?_)
  simp only [ENNReal.toReal_ofReal (Ω.gram_pos x').le, Complex.real_smul, mul_comm]

end LipschitzGraph

end Rd
