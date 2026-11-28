/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.PiecewisePoly
public import LeanPool.FunctionSpaces.Domains.Cube.Smoothing
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseJackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for piecewise polynomials on the cube

For `1 ≤ p < ∞`, `r ≥ 1` and `k ≥ 1`, the error of best approximation in `L_p(Q)`,
`Q = [0, 1]^d`, by piecewise polynomials of level `k` and degree `< r` in each variable is bounded
by the modulus on the cube,
`E_{2^k}(f)_p ≤ (1 + C_r)^(d+1) 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k))_p`
(`Cube.approxError_cubePPScheme_le`), with the bound `C_r` of the local projections.

The approximant of a bounded continuous `f` is the tensor projection
`P_k^d f = P_k^{(0)} ⋯ P_k^{(d-1)} f`. Its error telescopes into the errors of the projections in
single coordinates (`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le`). In coordinate `i`, every slice
of `f - P_k^{(i)} f` is the error of the local projection in one variable, and Lebesgue's
inequality (`Cube.eLpNorm_sub_ppKernel_apply_le`) bounds it by the error of any piecewise
polynomial. That piecewise polynomial is built slice by slice from Taylor polynomials of the
smoothings in coordinate `i` on the halves `{x_i ≤ 1/2}` and `{x_i ≥ 1/2}`
(`Cube.exists_left_cubeSmoothing`, `Cube.exists_right_cubeSmoothing`,
`Interval.exists_ppFun_approx_of_taylor`), so it need not depend measurably on the slice.
Minkowski's inequality in the point turns the bounds of the slices into bounds on two regions of
the cube (`Cube.eLpNorm_le_of_slice_le`), and every one-variable bound through such smoothings
becomes a bound in coordinate `i` (`Cube.eLpNorm_sub_slicewise_le_of_smoothing`, used in
`Cube.eLpNorm_sub_slicewise_ppKernel_le`).
General `f ∈ L_p(Q)` follow by density of the bounded continuous functions
(`Cube.approxError_le_of_continuous`).

At level `0` the approximants are the polynomials of degree `< r` in each variable, and
**Whitney's inequality on the cube** `E_1(f)_p ≤ W ω_r(f, 2^(-m))_p`, `m ≥ 2`
(`Cube.exists_approxError_cubePPScheme_one_le`), follows in the same way: on every slice, the Taylor
polynomials of the smoothings on `{x_i ≤ 1 - t}` and `{x_i ≥ t}`, `t = 2^(-m)`, are glued as in
one variable (`Interval.exists_eLpNorm_sub_polyFun_le_glue`,
`Cube.exists_eLpNorm_sub_ppKernel_zero_apply_le`). So Jackson's inequality holds at every level
(`Cube.exists_approxError_cubePPScheme_le`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal BoundedContinuousFunction

namespace Cube

open Interval

variable {d : ℕ}

/-! ### From slices to the cube -/

/-- **From slices to the cube, on two regions**: if every slice of `F` in coordinate `i` satisfies
`‖F_{x,i}‖_{L_p[0,1]} ≤ c ((‖(G₁)_{x,i}‖_{L_p[a₁,b₁]} + M ‖(D₁)_{x,i}‖_{L_p[a₁,b₁]}) +
(‖(G₂)_{x,i}‖_{L_p[a₂,b₂]} + M ‖(D₂)_{x,i}‖_{L_p[a₂,b₂]}))`,
then the same bound holds for the norms on the cube and on the regions `{x_i ∈ [a_ν, b_ν]}`: the
norms are mixed norms of the slices (`Cube.eLpNorm_cubeVol_eq_slice`,
`Cube.eLpNorm_regionVol_eq_slice`), and Minkowski's inequality in `L_p` over the point applies. -/
theorem eLpNorm_le_of_slice_le {F G₁ D₁ G₂ D₂ : (Fin d → ℝ) → ℂ} (hF : Measurable F)
    (hG₁ : Measurable G₁) (hD₁ : Measurable D₁) (hG₂ : Measurable G₂) (hD₂ : Measurable D₂)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁)
    (hb₁ : b₁ ≤ 1) (ha₂ : 0 ≤ a₂) (hb₂ : b₂ ≤ 1) {c M : ℝ≥0∞}
    (h : ∀ x, eLpNorm (slice F x i) p unitVol ≤
      c * ((eLpNorm (slice G₁ x i) p (volume.restrict (Icc a₁ b₁)) +
          M * eLpNorm (slice D₁ x i) p (volume.restrict (Icc a₁ b₁))) +
        (eLpNorm (slice G₂ x i) p (volume.restrict (Icc a₂ b₂)) +
          M * eLpNorm (slice D₂ x i) p (volume.restrict (Icc a₂ b₂))))) :
    eLpNorm F p (cubeVol d) ≤
      c * ((eLpNorm G₁ p (regionVol d i a₁ b₁) + M * eLpNorm D₁ p (regionVol d i a₁ b₁)) +
        (eLpNorm G₂ p (regionVol d i a₂ b₂) + M * eLpNorm D₂ p (regionVol d i a₂ b₂))) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hm : ∀ {G : (Fin d → ℝ) → ℂ} (a b : ℝ), Measurable G →
      Measurable fun x => eLpNorm (slice G x i) p (volume.restrict (Icc a b)) :=
    fun a b hG => measurable_eLpNorm_slice hG hp0 hp' i _
  rw [eLpNorm_cubeVol_eq_slice hF hp0 hp' i, eLpNorm_regionVol_eq_slice hG₁ hp0 hp' i ha₁ hb₁,
    eLpNorm_regionVol_eq_slice hD₁ hp0 hp' i ha₁ hb₁,
    eLpNorm_regionVol_eq_slice hG₂ hp0 hp' i ha₂ hb₂,
    eLpNorm_regionVol_eq_slice hD₂ hp0 hp' i ha₂ hb₂,
    ← eLpNorm_const_mul_ennreal (c := M) (hm a₁ b₁ hD₁).aestronglyMeasurable,
    ← eLpNorm_const_mul_ennreal (c := M) (hm a₂ b₂ hD₂).aestronglyMeasurable]
  refine (eLpNorm_mono_eNorm (g := fun x =>
      c * ((eLpNorm (slice G₁ x i) p (volume.restrict (Icc a₁ b₁)) +
          M * eLpNorm (slice D₁ x i) p (volume.restrict (Icc a₁ b₁))) +
        (eLpNorm (slice G₂ x i) p (volume.restrict (Icc a₂ b₂)) +
          M * eLpNorm (slice D₂ x i) p (volume.restrict (Icc a₂ b₂)))))
    (measurable_eLpNorm_slice hF hp0 hp' i _).aestronglyMeasurable
    fun x => by simpa only [eNorm_eq_self] using h x).trans ?_
  refine (eLpNorm_const_mul_ennreal (c := c) ?_).trans_le ?_
  · exact (((hm a₁ b₁ hG₁).add ((hm a₁ b₁ hD₁).const_mul M)).add
      ((hm a₂ b₂ hG₂).add ((hm a₂ b₂ hD₂).const_mul M))).aestronglyMeasurable
  gcongr
  exact (eLpNorm_add_le hp).trans (add_le_add (eLpNorm_add_le hp) (eLpNorm_add_le hp))

/-- **From one coordinate to all**: if `‖T u‖_{L_p[0,1]} ≤ C ‖u‖_{L_p[0,1]}` and
`‖f - T^{(i)} f‖_{L_p(Q)} ≤ B ω_r^{(i)}(f, t)_p` in every coordinate, then
`‖f - T^{(0)} ⋯ T^{(d-1)} f‖_{L_p(Q)} ≤ (1 + C)^d B ω_r(f, t)_p`, by telescoping
(`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le`). -/
theorem KernelOp.eLpNorm_sub_foldSlicewise_le_of_coord {ι : Type*} [Fintype ι] (T : KernelOp ι)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {C : ℝ≥0∞}
    (hT : ∀ u : ℝ → ℂ, Measurable u → eLpNorm (T.apply u) p unitVol ≤ C * eLpNorm u p unitVol)
    {f : (Fin d → ℝ) → ℂ} (hfb : BddMeas f) {r : ℕ} {B : ℝ≥0∞} {t : ℝ}
    (h : ∀ i, eLpNorm (fun x => f x - T.slicewise i f x) p (cubeVol d) ≤
      B * coordModulus r p i f t) :
    eLpNorm (fun x => f x - T.foldSlicewise (List.finRange d) f x) p (cubeVol d) ≤
      (1 + C) ^ d * B * cubeModulus r p f t := by
  refine (T.eLpNorm_sub_foldSlicewise_le hp hp' hT (List.finRange d) hfb).trans ?_
  rw [List.length_finRange, ← Fin.sum_univ_def]
  calc (1 + C) ^ d * ∑ i, eLpNorm (fun x => f x - T.slicewise i f x) p (cubeVol d)
      ≤ (1 + C) ^ d * ∑ i, B * coordModulus r p i f t :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => h i)
    _ = (1 + C) ^ d * B * cubeModulus r p f t := by
        rw [cubeModulus, ← Finset.mul_sum, mul_assoc]

/-- **From one coordinate to all, for the tensor projection**: if
`‖f - P_k^{(i)} f‖_{L_p(Q)} ≤ B ω_r^{(i)}(f, t)_p` in every coordinate, then
`‖f - P_k^d f‖_{L_p(Q)} ≤ (1 + C_r)^d B ω_r(f, t)_p`. -/
theorem eLpNorm_sub_cubeProj_le_of_coord {f : (Fin d → ℝ) → ℂ} (hfb : BddMeas f) {r k : ℕ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {B : ℝ≥0∞} {t : ℝ}
    (h : ∀ i, eLpNorm (fun x => f x - (ppKernel r k).slicewise i f x) p (cubeVol d) ≤
      B * coordModulus r p i f t) :
    eLpNorm (fun x => f x - cubeProj r k f x) p (cubeVol d) ≤
      (1 + ppProjConst r) ^ d * B * cubeModulus r p f t :=
  (ppKernel r k).eLpNorm_sub_foldSlicewise_le_of_coord hp hp'
    (fun _ hu => eLpNorm_ppKernel_apply_le hp hp' r k hu) hfb h

/-- **Jackson's estimate in one coordinate from the smoothings**: let `f` be continuous, `r ≥ 1`,
`L > 0` and `w + L ≤ 1`. Suppose that in one variable the error of `T` on every continuous `u` is
bounded through any functions `g₁, g₂` that are approximated on every interval `[a, b]` by
polynomials of degree `< r` up to `(b - a)^r ‖D_ν‖_{L_p[a,b]}`:
`‖u - T u‖_{L_p[0,1]} ≤ c ((‖u - g₁‖_{L_p[0,w]} + M ‖D₁‖_{L_p[0,w]})`
`+ (‖u - g₂‖_{L_p[1-w,1]} + M ‖D₂‖_{L_p[1-w,1]}))`.
If `a + M b ≤ J ω` whenever `a ≤ ω` and `b ≤ L^(-r) 2^r r^(2r) ω`, then
`‖f - T^{(i)} f‖_{L_p(Q)} ≤ c (2 J) ω_r^{(i)}(f, L)_p`: apply the bound on every slice to the
smoothings of `f` in coordinate `i` (`Cube.exists_left_cubeSmoothing`,
`Cube.exists_right_cubeSmoothing`) and pass to the cube as in `Cube.eLpNorm_le_of_slice_le`.
The constants `c, M, J` may be any elements of `[0, ∞]`. -/
theorem eLpNorm_sub_slicewise_le_of_smoothing {ι : Type*} [Fintype ι] (T : KernelOp ι)
    {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (i : Fin d) {L w : ℝ} (hL : 0 < L) (hwL : w + L ≤ 1) {c M J : ℝ≥0∞}
    (hT : ∀ {u g₁ D₁ g₂ D₂ : ℝ → ℂ}, Continuous u → Measurable g₁ → Measurable D₁ →
      Measurable g₂ → Measurable D₂ →
      (∀ a b : ℝ, a ≤ b → ∃ P ∈ degreeLT ℂ r,
        eLpNorm (fun t => g₁ t - polyFun P t) p (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (b - a) ^ r * eLpNorm D₁ p (volume.restrict (Icc a b))) →
      (∀ a b : ℝ, a ≤ b → ∃ P ∈ degreeLT ℂ r,
        eLpNorm (fun t => g₂ t - polyFun P t) p (volume.restrict (Icc a b)) ≤
          ENNReal.ofReal (b - a) ^ r * eLpNorm D₂ p (volume.restrict (Icc a b))) →
      eLpNorm (fun t => u t - T.apply u t) p unitVol ≤
        c * ((eLpNorm (fun t => u t - g₁ t) p (volume.restrict (Icc 0 w)) +
            M * eLpNorm D₁ p (volume.restrict (Icc 0 w))) +
          (eLpNorm (fun t => u t - g₂ t) p (volume.restrict (Icc (1 - w) 1)) +
            M * eLpNorm D₂ p (volume.restrict (Icc (1 - w) 1)))))
    (hJ : ∀ {a b ω : ℝ≥0∞}, a ≤ ω →
      b ≤ ENNReal.ofReal L⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) * ω → a + M * b ≤ J * ω) :
    eLpNorm (fun x => f x - T.slicewise i f x) p (cubeVol d) ≤
      c * (2 * J) * coordModulus r p i f L := by
  have hfm := hf.measurable
  obtain ⟨G₁, D₁, hG₁, hD₁, h1L, h2L, hTL⟩ := exists_left_cubeSmoothing hf hr hp hp' i hL hwL
  obtain ⟨G₂, D₂, hG₂, hD₂, h1R, h2R, hTR⟩ := exists_right_cubeSmoothing hf hr hp hp' i hL hwL
  refine (eLpNorm_le_of_slice_le (hfm.sub (T.measurable_slicewise hfm i)) (hfm.sub hG₁) hD₁
    (hfm.sub hG₂) hD₂ hp hp' i (a₁ := 0) (b₁ := w) (a₂ := 1 - w) (b₂ := 1) le_rfl (by linarith)
    (by linarith) le_rfl (c := c) (M := M) fun x => ?_).trans ?_
  · exact (congrArg (eLpNorm · p unitVol) (slice_sub_slicewise T f i x)).trans_le
      (hT (continuous_slice hf x i) (measurable_slice hG₁ x i) (measurable_slice hD₁ x i)
        (measurable_slice hG₂ x i) (measurable_slice hD₂ x i) (hTL x) (hTR x))
  · rw [mul_assoc, two_mul, add_mul]
    exact mul_le_mul' le_rfl (add_le_add (hJ h1L h2L) (hJ h1R h2R))

/-! ### Jackson's inequality from level `1` on -/

/-- **Jackson's estimate in one coordinate**: for continuous `f`, `r ≥ 1` and `k ≥ 0`,
`‖f - P_{k+1}^{(i)} f‖_{L_p(Q)} ≤ (1 + C_r) 2 (1 + 2^r r^(2r)) ω_r^{(i)}(f, 2^(-(k+1)))_p`. -/
theorem eLpNorm_sub_slicewise_ppKernel_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {r : ℕ}
    (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (i : Fin d) (k : ℕ) :
    eLpNorm (fun x => f x - (ppKernel r (k + 1)).slicewise i f x) p (cubeVol d) ≤
      (1 + ppProjConst r) * (2 * jacksonConst r) * coordModulus r p i f (1 / 2 ^ (k + 1)) := by
  have hL : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  refine eLpNorm_sub_slicewise_le_of_smoothing (ppKernel r (k + 1)) hf hr hp hp' i hL
    (one_half_add_le_one k) (c := 1 + ppProjConst r) (M := ENNReal.ofReal (1 / 2 ^ (k + 1)) ^ r)
    (fun hu hG₁ hD₁ hG₂ hD₂ hTL hTR => ?_)
    fun ha hb => add_ofReal_pow_mul_le_jacksonConst hL r ha hb
  obtain ⟨Q, hQ, hb⟩ := exists_ppFun_approx_of_taylor hu.measurable hG₁ hD₁ hG₂ hD₂ hp hp' hTL hTR k
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact (eLpNorm_sub_ppKernel_apply_le hp hp' hu.measurable hu.integrableOn_Icc hQ).trans
    (mul_le_mul' le_rfl hb)

/-- The constant of Jackson's inequality on the cube, `(1 + C_r)^(d+1) 2 (1 + 2^r r^(2r))`, with
the bound `C_r` of the local projections. -/
noncomputable def cubeJacksonConst (d r : ℕ) : ℝ≥0∞ :=
  (1 + ppProjConst r) ^ (d + 1) * (2 * jacksonConst r)

/-- The Jackson constant on the cube is finite. -/
theorem cubeJacksonConst_ne_top (d r : ℕ) : cubeJacksonConst d r ≠ ∞ :=
  ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩))
    (ENNReal.mul_ne_top (by norm_num) (jacksonConst_ne_top r))

/-- **Jackson's estimate for continuous functions on the cube**: for bounded continuous `f`,
`r ≥ 1` and `k ≥ 0`, the tensor projection satisfies
`‖f - P_{k+1}^d f‖_{L_p(Q)} ≤ (1 + C_r)^(d+1) 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-(k+1)))_p`. -/
theorem eLpNorm_sub_cubeProj_le {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) (hfb : BddMeas f)
    {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    eLpNorm (fun x => f x - cubeProj r (k + 1) f x) p (cubeVol d) ≤
      cubeJacksonConst d r * cubeModulus r p f (1 / 2 ^ (k + 1)) := by
  refine (eLpNorm_sub_cubeProj_le_of_coord hfb hp hp'
    fun i => eLpNorm_sub_slicewise_ppKernel_le hf hr hp hp' i k).trans_eq ?_
  rw [cubeJacksonConst, pow_succ]
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **From continuous functions to `L_p(Q)` by density**: a bound
`E_n(g) ≤ C ω_r(g, 2^(-k))_p` for every bounded continuous `g`, given by an approximant
`u ∈ A_n` of `g`, holds for every `f ∈ L_p(Q)`, `p < ∞`, as in one variable
(`Interval.approxError_le_of_continuous`). -/
theorem approxError_le_of_continuous {A : ApproximationScheme (Lp ℂ p (cubeVol d))} (hp : p ≠ ∞)
    {r n k : ℕ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ g : (Fin d → ℝ) →ᵇ ℂ, ∃ u : (Fin d → ℝ) → ℂ,
      (∃ a ∈ A n, (a : (Fin d → ℝ) → ℂ) =ᵐ[cubeVol d] u) ∧
        eLpNorm (fun x => g x - u x) p (cubeVol d) ≤ C * cubeModulus r p g (1 / 2 ^ k))
    (f : Lp ℂ p (cubeVol d)) : A.approxError f n ≤ C * lpCubeModulus p r f k := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  refine ApproximationScheme.approxError_le_of_dense
    (BoundedContinuousFunction.toLp_denseRange ℂ (cubeVol d) ℝ hp)
    (fun f g => lpCubeModulus_add_le hp r f g k) (C0 := d * 2 ^ r)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    (fun f => lpCubeModulus_le hp r f k) hC ?_ f
  rintro _ ⟨g, rfl⟩
  obtain ⟨u, ⟨a, ha, hau⟩, hbound⟩ := h g
  have hg := BoundedContinuousFunction.coeFn_toLp (E := ℂ) p (cubeVol d) ℝ g
  refine (A.approxError_le_of_mem ha _).trans ?_
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hg.sub hau)), lpCubeModulus,
    cubeModulus_congr_ae (Lp.stronglyMeasurable _).measurable g.continuous.measurable hg hp0 hp]
  exact hbound

/-- **Jackson's inequality for piecewise polynomials on the cube**: for `1 ≤ p < ∞`, `r ≥ 1` and
`k ≥ 1`, `E_{2^k}(f)_p ≤ (1 + C_r)^(d+1) 2 (1 + 2^r r^(2r)) ω_r(f, 2^(-k))_p` for every
`f ∈ L_p(Q)`; first for bounded continuous functions with the tensor projection
(`Cube.eLpNorm_sub_cubeProj_le`), then by density. -/
theorem approxError_cubePPScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) (f : Lp ℂ p (cubeVol d))
    {k : ℕ} (hk : 1 ≤ k) :
    (cubePPScheme p d r).approxError f (2 ^ k) ≤ cubeJacksonConst d r * lpCubeModulus p r f k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  refine approxError_le_of_continuous hp (cubeJacksonConst_ne_top d r) (fun g => ?_) f
  have hgb : BddMeas (g : (Fin d → ℝ) → ℂ) := ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩
  have hP := isCubePP_cubeProj r (k + 1) hgb
  exact ⟨cubeProj r (k + 1) g, ⟨(hP.1.memLp p (cubeVol d)).toLp _,
    mem_cubePPScheme_two_pow.2 ⟨_, hP, MemLp.coeFn_toLp _⟩, MemLp.coeFn_toLp _⟩,
    eLpNorm_sub_cubeProj_le g.continuous hgb hr Fact.out hp k⟩

/-! ### Whitney's inequality: level `0` -/

/-- **Whitney's estimate for the projection of level `0`**: there is `K < ∞` such that for `u`
integrable on `[0, 1]` and polynomials `T₁, T₂` of degree `< r`,
`‖u - P_0 u‖_{L_p[0,1]} ≤ K (‖u - T₁‖_{L_p[0,2/3]} + ‖u - T₂‖_{L_p[1/3,1]})`: the projection is
quasi-optimal (`Cube.eLpNorm_sub_ppKernel_apply_le`), and `T₁` and `T₂` are glued as in Whitney's
inequality (`Interval.exists_eLpNorm_sub_polyFun_le_glue`). -/
theorem exists_eLpNorm_sub_ppKernel_zero_apply_le (r : ℕ) (hp' : p ≠ ∞) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ {u : ℝ → ℂ}, Measurable u → IntegrableOn u (Icc 0 1) →
      ∀ {T₁ T₂ : ℂ[X]}, T₁ ∈ degreeLT ℂ r → T₂ ∈ degreeLT ℂ r →
        eLpNorm (fun s => u s - (ppKernel r 0).apply u s) p unitVol ≤
          K * (eLpNorm (fun s => u s - polyFun T₁ s) p (volume.restrict (Icc 0 (2 / 3))) +
            eLpNorm (fun s => u s - polyFun T₂ s) p (volume.restrict (Icc (1 / 3) 1))) := by
  have hp : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hKb⟩ := exists_eLpNorm_sub_polyFun_le_glue (p := p) r hp'
  refine ⟨(1 + ppProjConst r) * (1 + K),
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hK⟩), fun {u} hu hui {T₁ T₂} hT₁ hT₂ => ?_⟩
  have hae : (fun s => u s - ppFun 0 (fun _ => T₁) s) =ᵐ[unitVol]
      fun s => u s - polyFun T₁ s := by
    filter_upwards [ae_mem_Ico_unitVol] with s hs
    obtain ⟨hmem, hlt⟩ := mem_dyadicIco_floor (k := 0) hs
    rw [ppFun_eq_of_mem _ hlt hmem]
  calc eLpNorm (fun s => u s - (ppKernel r 0).apply u s) p unitVol
      ≤ (1 + ppProjConst r) * eLpNorm (fun s => u s - ppFun 0 (fun _ => T₁) s) p unitVol :=
        eLpNorm_sub_ppKernel_apply_le hp hp' hu hui fun _ => hT₁
    _ = (1 + ppProjConst r) *
          eLpNorm (fun s => u s - polyFun T₁ s) p (volume.restrict (Icc 0 1)) := by
        rw [eLpNorm_congr_ae hae]
    _ ≤ (1 + ppProjConst r) * ((1 + K) *
          (eLpNorm (fun s => u s - polyFun T₁ s) p (volume.restrict (Icc 0 (2 / 3))) +
            eLpNorm (fun s => u s - polyFun T₂ s) p (volume.restrict (Icc (1 / 3) 1)))) :=
        mul_le_mul' le_rfl (hKb hu hT₁ hT₂)
    _ = _ := (mul_assoc _ _ _).symm

/-- **Whitney's estimate in one coordinate**: for `0 < t ≤ 1/3` there is `W < ∞` with
`‖f - P_0^{(i)} f‖_{L_p(Q)} ≤ W ω_r^{(i)}(f, t)_p` for every continuous `f` and every
coordinate `i`, where `P_0` is the projection onto the polynomials of degree `< r` in one
variable. On every slice, the Taylor polynomials of the smoothings on `{x_i ≤ 1 - t}` and on
`{x_i ≥ t}` are glued as in Whitney's inequality on `[0, 1]`
(`Cube.exists_eLpNorm_sub_ppKernel_zero_apply_le`). -/
theorem exists_eLpNorm_sub_slicewise_ppKernel_zero_le {r : ℕ} (hr : 1 ≤ r) (hp' : p ≠ ∞)
    {t : ℝ} (ht : 0 < t) (ht3 : t ≤ 1 / 3) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ {f : (Fin d → ℝ) → ℂ}, Continuous f → ∀ i : Fin d,
      eLpNorm (fun x => f x - (ppKernel r 0).slicewise i f x) p (cubeVol d) ≤
        W * coordModulus r p i f t := by
  have hp : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hKb⟩ := exists_eLpNorm_sub_ppKernel_zero_apply_le (p := p) r hp'
  obtain ⟨c, hc_eq⟩ : ∃ c : ℝ≥0∞,
      c = ENNReal.ofReal t⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r)) := ⟨_, rfl⟩
  have hc : c ≠ ∞ := hc_eq ▸ ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))
  refine ⟨K * (2 * (1 + c)), ENNReal.mul_ne_top hK
    (ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hc⟩)),
    fun {f} hf i => eLpNorm_sub_slicewise_le_of_smoothing (ppKernel r 0) hf hr hp hp' i ht
      (by linarith : (1 - t) + t ≤ 1) (c := K) (M := 1) (J := 1 + c)
      (fun hu _ _ _ _ hTL hTR => ?_) fun ha hb => ?_⟩
  · obtain ⟨T₁, hT₁, hT₁b⟩ := hTL 0 (1 - t) (by linarith)
    obtain ⟨T₂, hT₂, hT₂b⟩ := hTR t 1 (by linarith)
    rw [sub_sub_cancel]
    refine (hKb hu.measurable hu.integrableOn_Icc hT₁ hT₂).trans
      (mul_le_mul' le_rfl (add_le_add ?_ ?_))
    · rw [one_mul]
      exact (eLpNorm_Icc_mono _ p le_rfl (by linarith)).trans
        (eLpNorm_sub_polyFun_le_add (by linarith) hT₁b)
    · rw [one_mul]
      exact (eLpNorm_Icc_mono _ p ht3 le_rfl).trans
        (eLpNorm_sub_polyFun_le_add (by linarith) hT₂b)
  · rw [one_mul, add_mul, one_mul, hc_eq]
    exact add_le_add ha hb

/-- **Whitney's inequality on the cube**: for `m ≥ 2` there is `W < ∞` with
`E_1(f)_p ≤ W ω_r(f, 2^(-m))_p` for every `f ∈ L_p(Q)`; the approximants of complexity `1` are the
polynomials of degree `< r` in each variable. -/
theorem exists_approxError_cubePPScheme_one_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {m : ℕ}
    (hm : 2 ≤ m) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ f : Lp ℂ p (cubeVol d),
      (cubePPScheme p d r).approxError f 1 ≤ W * lpCubeModulus p r f m := by
  have ht : (0 : ℝ) < 1 / 2 ^ m := by positivity
  have ht3 : (1 : ℝ) / 2 ^ m ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
    calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  obtain ⟨W, hW, hWb⟩ :=
    exists_eLpNorm_sub_slicewise_ppKernel_zero_le (d := d) (p := p) hr hp ht ht3
  have hW' : (1 + ppProjConst r) ^ d * W ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ppProjConst_ne_top r⟩)) hW
  refine ⟨(1 + ppProjConst r) ^ d * W, hW',
    fun f => approxError_le_of_continuous hp hW' (fun g => ?_) f⟩
  have hgb : BddMeas (g : (Fin d → ℝ) → ℂ) := ⟨g.continuous.measurable, ‖g‖, g.norm_coe_le_norm⟩
  have hP := isCubePP_cubeProj r 0 hgb
  refine ⟨cubeProj r 0 g, ⟨(hP.1.memLp p (cubeVol d)).toLp _, ?_, MemLp.coeFn_toLp _⟩, ?_⟩
  · change _ ∈ cubePPScheme p d r (2 ^ 0)
    exact mem_cubePPScheme_two_pow.2 ⟨_, hP, MemLp.coeFn_toLp _⟩
  · exact eLpNorm_sub_cubeProj_le_of_coord hgb Fact.out hp fun i => hWb g.continuous i

/-- **Jackson's inequality for piecewise polynomials on the cube at every level**: for
`1 ≤ p < ∞` and `r ≥ 1` there is `C_J < ∞` with `E_{2^k}(f)_p ≤ C_J ω_r(f, 2^(-k))_p` for every
`f ∈ L_p(Q)` and every `k ≥ 0`; level `0` is Whitney's inequality. -/
theorem exists_approxError_cubePPScheme_le {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧ ∀ (f : Lp ℂ p (cubeVol d)) (k : ℕ),
      (cubePPScheme p d r).approxError f (2 ^ k) ≤ CJ * lpCubeModulus p r f k := by
  obtain ⟨W, hW, hWb⟩ := exists_approxError_cubePPScheme_one_le (d := d) (p := p) hr hp le_rfl
  refine ⟨W + cubeJacksonConst d r,
    ENNReal.add_ne_top.2 ⟨hW, cubeJacksonConst_ne_top d r⟩, fun f k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    exact (hWb f).trans (mul_le_mul' le_self_add (lpCubeModulus_anti r f (Nat.zero_le 2)))
  · exact (approxError_cubePPScheme_le hr hp f hk).trans (mul_le_mul' le_add_self le_rfl)

end Cube
