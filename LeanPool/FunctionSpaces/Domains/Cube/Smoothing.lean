/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.Modulus
public import LeanPool.FunctionSpaces.Domains.Interval.Taylor

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smoothing in one coordinate

The **Steklov smoothing in coordinate `i`** smooths every slice in coordinate `i`,
`S^{(i)}_δ f(x) = S_δ (slice f x i)(x_i)` (`Cube.cubeSmooth`), with the smoothing `S_δ` of one
variable (`Interval.smooth`). For continuous `f` its two identities hold pointwise on the cube:

* `f - S^{(i)}_δ f = (-1)^r avg_v Δ^r_{(v_1 + ⋯ + v_r) e_i} f`, the average being over the steps
  only (`Cube.sub_cubeSmooth_eq`, from `Interval.sub_smooth_eq` and
  `Interval.avgStepIter_congr_point`);
* the derivative of order `r` in `x_i` (`Cube.cubeSmoothDeriv`) is the finite combination
  `∑_k (-1)^(k+1) C(r,k) (kδ)^(-r) Δ^r_{kδ e_i} f` (`Cube.cubeSmoothDeriv_eq`).

Minkowski's inequality for averages on the cube (`Interval.eLpNorm_avgStepIter_le`, for any point
space) and the derivative bound for any measure (`Interval.eLpNorm_sum_smoothCoeff_smul_le`) then
bound both by the coordinate modulus, with the supremum over the steps outside the integral over
the cube (`Cube.eLpNorm_sub_cubeSmooth_le`, `Cube.eLpNorm_cubeSmoothDeriv_le`). With `δ = L / r²`
this gives smoothings on the regions `{x_i ≤ w}` and, by the reflection `x_i ↦ 1 - x_i`
(`Cube.coordModulus_reflect`), `{x_i ≥ 1 - w}`, `w + L ≤ 1`, whose slices have Taylor polynomials
on all intervals (`Cube.exists_left_cubeSmoothing`, `Cube.exists_right_cubeSmoothing`), with the
step bounds and the reflected Taylor polynomials of the interval (`Interval.step_div_sq_bounds`,
`Interval.two_pow_mul_inv_div_sq_pow_mul_le`, `Interval.exists_eLpNorm_sub_polyFun_reflect_le`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open Rd (higherDiff)
open scoped ENNReal

namespace Cube

open Interval

variable {d : ℕ}

/-- Coordinate differences of a continuous function are jointly continuous in the step and the
point. -/
theorem continuous_cubeDiff_uncurry {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ)
    (i : Fin d) :
    Continuous (Function.uncurry fun (h : ℝ) (x : Fin d → ℝ) => cubeDiff r h i f x) := by
  have : (Function.uncurry fun (h : ℝ) (x : Fin d → ℝ) => cubeDiff r h i f x) =
      fun q : ℝ × (Fin d → ℝ) => ∑ k ∈ Finset.range (r + 1),
        ((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) * f (Function.update q.2 i (q.2 i + k * q.1)) :=
    funext fun q => cubeDiff_eq r q.1 i f q.2
  rw [this]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul (hf.comp ?_)
  exact continuous_snd.update i (((continuous_apply i).comp continuous_snd).add
    (continuous_const.mul continuous_fst))

/-- Coordinate differences of a continuous function are continuous. -/
theorem continuous_cubeDiff {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) (h : ℝ)
    (i : Fin d) : Continuous (cubeDiff r h i f) :=
  (continuous_cubeDiff_uncurry hf r i).comp (continuous_const.prodMk continuous_id)

/-! ### The smoothing and its identities -/

/-- The **Steklov smoothing in coordinate `i`**: `S^{(i)}_δ f(x) = S_δ (slice f x i)(x_i)`. -/
noncomputable def cubeSmooth (r : ℕ) (δ : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℝ) : ℂ :=
  smooth r δ (slice f x i) (x i)

/-- The **derivative of order `r` in coordinate `i`** of the smoothing,
`∂_i^r S^{(i)}_δ f(x) = (S_δ (slice f x i))^(r)(x_i)`. -/
noncomputable def cubeSmoothDeriv (r : ℕ) (δ : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℝ) : ℂ :=
  iteratedDeriv r (smooth r δ (slice f x i)) (x i)

/-- The slices of the smoothing are the smoothings of the slices. -/
theorem slice_cubeSmooth (r : ℕ) (δ : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    slice (cubeSmooth r δ i f) x i = smooth r δ (slice f x i) := by
  funext t
  simp only [slice, cubeSmooth]
  rw [slice_update, Function.update_self]

/-- The slices of the derivative are the derivatives of the smoothed slices. -/
theorem slice_cubeSmoothDeriv (r : ℕ) (δ : ℝ) (i : Fin d) (f : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℝ) :
    slice (cubeSmoothDeriv r δ i f) x i = iteratedDeriv r (smooth r δ (slice f x i)) := by
  funext t
  simp only [slice, cubeSmoothDeriv]
  rw [slice_update, Function.update_self]

/-- **`f - S^{(i)}_δ f` is an averaged coordinate difference**:
`f(x) - S^{(i)}_δ f(x) = (-1)^r avg_h Δ^r_{h e_i} f(x)`, the average over the steps only. -/
theorem sub_cubeSmooth_eq {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : δ ≠ 0) (i : Fin d) (x : Fin d → ℝ) :
    f x - cubeSmooth r δ i f x =
      (-1 : ℂ) ^ r * avgStepIter r δ (fun h y => cubeDiff r h i f y) 0 x := by
  have h := sub_smooth_eq (continuous_slice hf x i) r hδ (x i)
  rw [show slice f x i (x i) = f x by simp [slice] ] at h
  rw [cubeSmooth, h]
  congr 1
  exact avgStepIter_congr_point (G := fun h y => higherDiff r h (slice f x i) y)
    (G' := fun h y => cubeDiff r h i f y) (x := x i) (x' := x) (fun s => rfl) r δ 0

/-- **The derivative of the smoothing is a combination of coordinate differences**:
`∂_i^r S^{(i)}_δ f = ∑_{k=1}^r (-1)^(k+1) C(r,k) (kδ)^(-r) Δ^r_{kδ e_i} f`. -/
theorem cubeSmoothDeriv_eq {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ)
    (i : Fin d) (x : Fin d → ℝ) :
    cubeSmoothDeriv r δ i f x = ∑ k ∈ Finset.range r,
      ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        ((((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r * cubeDiff r ((k + 1 : ℕ) * δ) i f x) := by
  rw [cubeSmoothDeriv, iteratedDeriv_smooth (continuous_slice hf x i) r δ]
  rfl

/-- **The derivative of the smoothing as a sum of functions**:
`∂_i^r S^{(i)}_δ f = ∑_{k=1}^r (-1)^(k+1) C(r,k) (kδ)^(-r) Δ^r_{kδ e_i} f` as an identity of
functions on `ℝ^d` (`Cube.cubeSmoothDeriv_eq` at every point), written as a sum `∑_k c_k • g_k`,
the form to which the triangle inequality in `L_p` applies. -/
theorem cubeSmoothDeriv_eq_sum_smul {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ)
    (i : Fin d) :
    cubeSmoothDeriv r δ i f = ∑ k ∈ Finset.range r,
      (((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        (((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r) • cubeDiff r ((k + 1 : ℕ) * δ) i f := by
  funext x
  rw [cubeSmoothDeriv_eq hf r δ i x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

/-- The smoothing of a continuous function is continuous. -/
theorem continuous_cubeSmooth {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : δ ≠ 0) (i : Fin d) : Continuous (cubeSmooth r δ i f) := by
  have : cubeSmooth r δ i f = fun x =>
      f x - (-1 : ℂ) ^ r * avgStepIter r δ (fun h y => cubeDiff r h i f y) 0 x := by
    funext x
    rw [← sub_cubeSmooth_eq hf r hδ i x]
    ring
  rw [this]
  exact hf.sub (continuous_const.mul ((continuous_avgStepIter
    (continuous_cubeDiff_uncurry hf r i) r δ).comp (continuous_const.prodMk continuous_id)))

/-- The derivative of the smoothing of a continuous function is continuous. -/
theorem continuous_cubeSmoothDeriv {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) (δ : ℝ)
    (i : Fin d) : Continuous (cubeSmoothDeriv r δ i f) := by
  rw [show cubeSmoothDeriv r δ i f = fun x => ∑ k ∈ Finset.range r,
      ((-1 : ℂ) ^ (k + 2) * (r.choose (k + 1) : ℂ)) *
        ((((k + 1 : ℕ) * δ : ℝ) : ℂ)⁻¹ ^ r * cubeDiff r ((k + 1 : ℕ) * δ) i f x) from
    funext (cubeSmoothDeriv_eq hf r δ i)]
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (continuous_const.mul (continuous_cubeDiff hf r _ i))

/-! ### Bounds by the coordinate modulus -/

/-- **Coordinate differences on a region are bounded by the modulus**: for `w + r (rδ) ≤ 1` and
`0 ≤ h ≤ rδ`, `‖Δ^r_{h e_i} f‖_{L_p({x_i ≤ w})} ≤ ω_r^{(i)}(f, rδ)_p`, since the region
`{0 ≤ x_i ≤ w}` lies in `{0 ≤ x_i ≤ 1 - rh}`. -/
theorem eLpNorm_cubeDiff_regionVol_le {f : (Fin d → ℝ) → ℂ} {r : ℕ} {δ : ℝ} {p : ℝ≥0∞}
    {i : Fin d} {w h : ℝ} (hwb : w + r * (r * δ) ≤ 1) (h0 : 0 ≤ h) (hh : h ≤ r * δ) :
    eLpNorm (cubeDiff r h i f) p (regionVol d i 0 w) ≤ coordModulus r p i f (r * δ) := by
  have hsub : {x : Fin d → ℝ | x i ∈ Icc 0 w} ⊆ {x | x i ∈ Icc 0 (1 - r * h)} := fun x hx => by
    have : (r : ℝ) * h ≤ r * (r * δ) := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg r)
    exact ⟨hx.1, by linarith [hx.2]⟩
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans
    (eLpNorm_cubeDiff_le_coordModulus ⟨h0, hh⟩)

/-- **The smoothing is close to `f`**: on `{x_i ≤ w}` with `w + r² δ ≤ 1`,
`‖f - S^{(i)}_δ f‖_p ≤ ω_r^{(i)}(f, rδ)_p`. -/
theorem eLpNorm_sub_cubeSmooth_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) {w : ℝ}
    (hwb : w + r * (r * δ) ≤ 1) :
    eLpNorm (fun x => f x - cubeSmooth r δ i f x) p (regionVol d i 0 w) ≤
      coordModulus r p i f (r * δ) := by
  have heq : (fun x => f x - cubeSmooth r δ i f x) =
      ((-1 : ℂ) ^ r) • avgStepIter r δ (fun h y => cubeDiff r h i f y) 0 := by
    funext x
    rw [sub_cubeSmooth_eq hf r hδ.ne' i x]
    rfl
  rw [heq, eLpNorm_const_smul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul]
  refine (eLpNorm_avgStepIter_le (continuous_cubeDiff_uncurry hf r i) hδ hp hp' _ r 0).trans ?_
  refine iSup₂_le fun h hh => ?_
  rw [zero_add] at hh
  exact eLpNorm_cubeDiff_regionVol_le hwb hh.1 hh.2

/-- **The derivative of the smoothing**: on `{x_i ≤ w}` with `w + r² δ ≤ 1`,
`‖∂_i^r S^{(i)}_δ f‖_p ≤ 2^r δ^(-r) ω_r^{(i)}(f, rδ)_p`. -/
theorem eLpNorm_cubeSmoothDeriv_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) {p : ℝ≥0∞} (hp : 1 ≤ p) (i : Fin d) {w : ℝ} (hwb : w + r * (r * δ) ≤ 1) :
    eLpNorm (cubeSmoothDeriv r δ i f) p (regionVol d i 0 w) ≤
      2 ^ r * (ENNReal.ofReal δ)⁻¹ ^ r * coordModulus r p i f (r * δ) := by
  rw [cubeSmoothDeriv_eq_sum_smul hf r δ i]
  exact eLpNorm_sum_smoothCoeff_smul_le (D := fun h => cubeDiff r h i f) hδ hp
    fun h h0 hh => eLpNorm_cubeDiff_regionVol_le hwb h0 hh

/-! ### Smoothings on the two ends of a coordinate -/

/-- **Smoothing on a left region**: for continuous `f`, `r ≥ 1`, a scale `L > 0` and
`w + L ≤ 1`, the smoothing `G = S^{(i)}_δ f`, `δ = L/r²`, and `D = ∂_i^r G` satisfy
`‖f - G‖_{L_p({x_i ≤ w})} ≤ ω_r^{(i)}(f, L)_p` and
`‖D‖_{L_p({x_i ≤ w})} ≤ L^(-r) 2^r r^(2r) ω_r^{(i)}(f, L)_p`, and every slice of `G` has Taylor
polynomials `‖G - T‖_{L_p[u,v]} ≤ (v - u)^r ‖D‖_{L_p[u,v]}` on the slice. -/
theorem exists_left_cubeSmoothing {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {r : ℕ}
    (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) {L w : ℝ} (hL : 0 < L)
    (hwL : w + L ≤ 1) :
    ∃ G D : (Fin d → ℝ) → ℂ, Measurable G ∧ Measurable D ∧
      eLpNorm (fun x => f x - G x) p (regionVol d i 0 w) ≤ coordModulus r p i f L ∧
      eLpNorm D p (regionVol d i 0 w) ≤
        ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * coordModulus r p i f L ∧
      ∀ x : Fin d → ℝ, ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun t => slice G x i t - polyFun T t) p (volume.restrict (Icc u v)) ≤
          ENNReal.ofReal (v - u) ^ r * eLpNorm (slice D x i) p (volume.restrict (Icc u v)) := by
  obtain ⟨hδ, hrδ, hrrδ⟩ := step_div_sq_bounds hr hL
  have hwb : w + r * (r * (L / r ^ 2)) ≤ 1 := by rw [hrrδ]; exact hwL
  refine ⟨cubeSmooth r (L / r ^ 2) i f, cubeSmoothDeriv r (L / r ^ 2) i f,
    (continuous_cubeSmooth hf r hδ.ne' i).measurable,
    (continuous_cubeSmoothDeriv hf r (L / r ^ 2) i).measurable, ?_, ?_, fun x u v huv => ?_⟩
  · exact (eLpNorm_sub_cubeSmooth_le hf r hδ hp hp' i hwb).trans (coordModulus_mono r p i f hrδ)
  · exact (eLpNorm_cubeSmoothDeriv_le hf r hδ hp i hwb).trans
      (two_pow_mul_inv_div_sq_pow_mul_le hr hL (coordModulus_mono r p i f hrδ))
  · rw [slice_cubeSmooth, slice_cubeSmoothDeriv]
    exact exists_eLpNorm_sub_polyFun_le hp r
      (contDiff_smooth (continuous_slice hf x i) r (L / r ^ 2)) huv

/-- The **reflection in coordinate `i`**, `x ↦ x` with `x_i` replaced by `1 - x_i`. -/
def reflect (i : Fin d) (x : Fin d → ℝ) : Fin d → ℝ := Function.update x i (1 - x i)

/-- The reflection is an involution. -/
theorem reflect_reflect (i : Fin d) (x : Fin d → ℝ) : reflect i (reflect i x) = x := by
  simp [reflect]

/-- The reflection is continuous. -/
theorem continuous_reflect (i : Fin d) : Continuous (reflect (d := d) i) :=
  continuous_id.update i (continuous_const.sub (continuous_apply i))

/-- The slice of a reflected function is the reflected slice. -/
theorem slice_reflect (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) (i : Fin d) :
    slice (fun y => f (reflect i y)) x i = fun t => slice f x i (1 - t) := by
  funext t
  simp [slice, reflect]

/-- **Reflection preserves the coordinate modulus**: `ω_r^{(i)}(f(reflect_i ·), t) =
ω_r^{(i)}(f, t)`,
slice by slice (`Interval.eLpNorm_higherDiff_reflect`, `Cube.coordModulus_eq_of_slice`). -/
theorem coordModulus_reflect {f : (Fin d → ℝ) → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (r : ℕ) (i : Fin d) (t : ℝ) :
    coordModulus r p i (fun y => f (reflect i y)) t = coordModulus r p i f t :=
  coordModulus_eq_of_slice (f := fun y => f (reflect i y))
    (hf.comp (continuous_reflect i).measurable) hf hp0 hp r i t fun h _ => ae_of_all _ fun x => by
      rw [slice_reflect]
      simpa only [zero_add] using eLpNorm_higherDiff_reflect (measurable_slice hf x i) r p 0 1 h

/-- **Reflection of a region**: `‖F(reflect_i ·)‖_{L_p({x_i ∈ [0, w]})} = ‖F‖_{L_p({x_i ∈ [1-w,
1]})}`
for `w ≤ 1`. -/
theorem eLpNorm_reflect_regionVol {F : (Fin d → ℝ) → ℂ} (hF : Measurable F) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (i : Fin d) {w : ℝ} (hw1 : w ≤ 1) :
    eLpNorm (fun y => F (reflect i y)) p (regionVol d i 0 w) =
      eLpNorm F p (regionVol d i (1 - w) 1) := by
  have hFr : Measurable fun y => F (reflect i y) := hF.comp (continuous_reflect i).measurable
  rw [eLpNorm_regionVol_eq_slice hFr hp0 hp i le_rfl hw1,
    eLpNorm_regionVol_eq_slice hF hp0 hp i (by linarith) le_rfl]
  congr 1
  funext x
  rw [slice_reflect, eLpNorm_comp_sub_Icc (measurable_slice hF x i), sub_zero]

/-- **Smoothing on a right region**: the same as `Cube.exists_left_cubeSmoothing` on
`{x_i ≥ 1 - w}`, by the reflection in coordinate `i`. -/
theorem exists_right_cubeSmoothing {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {r : ℕ}
    (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) {L w : ℝ} (hL : 0 < L)
    (hwL : w + L ≤ 1) :
    ∃ G D : (Fin d → ℝ) → ℂ, Measurable G ∧ Measurable D ∧
      eLpNorm (fun x => f x - G x) p (regionVol d i (1 - w) 1) ≤ coordModulus r p i f L ∧
      eLpNorm D p (regionVol d i (1 - w) 1) ≤
        ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * coordModulus r p i f L ∧
      ∀ x : Fin d → ℝ, ∀ u v : ℝ, u ≤ v → ∃ T ∈ degreeLT ℂ r,
        eLpNorm (fun t => slice G x i t - polyFun T t) p (volume.restrict (Icc u v)) ≤
          ENNReal.ofReal (v - u) ^ r * eLpNorm (slice D x i) p (volume.restrict (Icc u v)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hw1 : w ≤ 1 := by linarith
  have hfr : Continuous fun y => f (reflect i y) := hf.comp (continuous_reflect i)
  obtain ⟨G, D, hGm, hDm, h1, h2, h3⟩ := exists_left_cubeSmoothing hfr hr hp hp' i hL hwL
  rw [coordModulus_reflect hf.measurable hp0 hp'] at h1 h2
  have hrefl : Measurable (reflect (d := d) i) := (continuous_reflect i).measurable
  refine ⟨fun y => G (reflect i y), fun y => D (reflect i y), hGm.comp hrefl, hDm.comp hrefl,
    ?_, ?_, fun x u v huv => ?_⟩
  · have h := eLpNorm_reflect_regionVol (F := fun y => f y - G (reflect i y))
      (hf.measurable.sub (hGm.comp hrefl)) hp0 hp' i hw1
    simp only [reflect_reflect] at h
    rw [← h]
    exact h1
  · have h := eLpNorm_reflect_regionVol (F := fun y => D (reflect i y)) (hDm.comp hrefl) hp0 hp'
      i hw1
    simp only [reflect_reflect] at h
    rw [← h]
    exact h2
  · simp only [slice_reflect]
    exact exists_eLpNorm_sub_polyFun_reflect_le (measurable_slice hGm x i)
      (measurable_slice hDm x i) (h3 x (1 - v) (1 - u) (by linarith))

end Cube
