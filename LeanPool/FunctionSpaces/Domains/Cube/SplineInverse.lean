/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.SplineJackson
public import LeanPool.FunctionSpaces.Domains.Interval.SplineInverse

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The inverse inequality for tensor splines and the coincidence theorem

The slices of a spline of level `j` on the cube are dyadic splines of level `j` on `[0, 1]`
(`Cube.IsCubeSpline`), so the local inverse estimate for splines in one variable
(`Interval.eLpNorm_higherDiff_ppFun_spline_le`), applied to every slice and integrated over the
point, bounds the differences in each coordinate (`Cube.eLpNorm_cubeDiff_le_of_isCubeSpline`).
Summed over the coordinates this is the **inverse inequality of order `r - 1 + 1/p`**
(`Cube.exists_inverse_cubeSplineScheme`).

With Jackson's inequality at every level (`Cube.exists_approxError_cubeSplineScheme_le`) the modulus
on the cube is compatible with the scheme of tensor splines (`Cube.cubeSplineModulusData`), and
`A^s_q = B^s_{p,q}([0, 1]^d)` for `0 ≤ s < r - 1 + 1/p` (`Cube.memApprox_cubeSplineScheme_iff`),
beyond smoothness `1` for `r ≥ 2`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Cube

open Interval

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The strip constant of the local inverse estimate for splines is finite. -/
theorem splineStripConst_ne_top (r j : ℕ) {K : ℝ≥0∞} (hK : K ≠ ∞) (h : ℝ) :
    splineStripConst r j K h p ≠ ∞ := by
  unfold splineStripConst
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by simp) (ENNReal.natCast_ne_top r)) (by simp)) hK)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)

/-- **The local inverse estimate for tensor splines**: for a spline `g` of level `j` on the cube
and `0 ≤ h ≤ 2^(-j)`,
`‖Δ^r_{h e_i} g‖_{L_p({x_i ≤ 1 - rh})} ≤ S_j(h) (r h (r + 1))^(1/p) ‖g‖_{L_p(Q)}`, from the
estimate in one variable on every slice (`Interval.eLpNorm_higherDiff_ppFun_spline_le`). -/
theorem eLpNorm_cubeDiff_le_of_isCubeSpline {r j : ℕ} {g : (Fin d → ℝ) → ℂ}
    (hg : IsCubeSpline r j g) {K : ℝ≥0∞} (hKb : NikolskiiBound p r K)
    (hp : p ≠ ∞) (i : Fin d) {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) :
    eLpNorm (cubeDiff r h i g) p (diffRegion d r h i) ≤
      splineStripConst r j K h p * (ENNReal.ofReal (r * h) * (r + 1)) ^ (1 / p.toReal) *
        eLpNorm g p (cubeVol d) := by
  refine eLpNorm_cubeDiff_le_of_slice_le hg.1.1
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp r hh0 i fun x => ?_
  obtain ⟨Q, hQ, hJ, hs⟩ := hg.2 i x
  rw [hs]
  exact eLpNorm_higherDiff_ppFun_spline_le hQ hJ hKb hp hh0 hh

/-- **The inverse inequality for tensor splines**, of order `θ = r - 1 + 1/p`: there is
`C_B < ∞` with `ω_r(a, 2^(-k))_p ≤ C_B 2^(-(k-j)θ) ‖a‖_p` for every spline `a` of order `r` and
level `j` on the cube (and `k - j` truncated at `0`). -/
theorem exists_inverse_cubeSplineScheme {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ cubeSplineScheme p d r (2 ^ j),
      lpCubeModulus p r a k ≤
        CB * dyadicWeight (-(((r - 1 : ℕ) : ℝ) + 1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨d * (2 ^ r * (1 + splineInverseConst r K p)),
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, splineInverseConst_ne_top r hK⟩)),
    fun j k a ha => ?_⟩
  obtain ⟨g, hg, hae⟩ := mem_cubeSplineScheme_two_pow.1 ha
  refine lpCubeModulus_le_of_coord hp (two_pow_le_two_pow_mul_one_add r _) hg.1.1 hae
    fun hjk i h hh0 hh => ?_
  refine ((eLpNorm_cubeDiff_le_of_isCubeSpline hg hKb hp i hh0 (hh.trans
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hjk)))).trans
    (splineStripConst_mul_le hjk K hh _)).trans ?_
  gcongr
  exact le_two_pow_mul_one_add r _

/-- The modulus `ω_r(f, 2^(-k))_p` on the cube is compatible with the scheme of tensor splines of
order `r`, with inverse order `θ = r - 1 + 1/p` and Jackson's inequality at every level. -/
noncomputable def cubeSplineModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (cubeSplineScheme p d r) (((r - 1 : ℕ) : ℝ) + 1 / p.toReal) :=
  .ofExists (lpCubeModulus p r) (lpCubeModulus_add_le hp r) (d * 2 ^ r)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (by simp)) (lpCubeModulus_le hp r) 0
    ((exists_approxError_cubeSplineScheme_le hr hp).imp fun _ h => ⟨h.1, fun f k _ => h.2 f k⟩)
    (exists_inverse_cubeSplineScheme hp)

/-- **Approximation by tensor splines on the cube.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`, `r ≥ 1` and
`0 ≤ s < r - 1 + 1/p`, an `f ∈ L_p([0, 1]^d)` lies in the approximation space `A^s_q` of the
splines of order `r` in each variable on dyadic cubes iff its Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite, where `ω_r = ∑_i ω_r^{(i)}` is the sum
of the moduli in the coordinates. -/
theorem memApprox_cubeSplineScheme_iff {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsr : s < (r : ℝ) - 1 + 1 / p.toReal) (f : Lp ℂ p (cubeVol d)) :
    (cubeSplineScheme p d r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpCubeModulus p r f k) < ∞ := by
  have hθ : (r : ℝ) - 1 + 1 / p.toReal = ((r - 1 : ℕ) : ℝ) + 1 / p.toReal := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  exact (cubeSplineModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs (hθ ▸ hsr) f

end Cube
