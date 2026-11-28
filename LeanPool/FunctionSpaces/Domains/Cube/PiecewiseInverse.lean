/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.PiecewiseJackson
public import LeanPool.FunctionSpaces.Domains.Interval.PiecewiseInverse

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The inverse inequality on the cube and the coincidence theorem

The slices of a piecewise polynomial of level `j` on the cube are piecewise polynomials of level
`j` on `[0, 1]` (`Cube.IsCubePP.exists_slice_eq_ppFun`). So the local inverse estimate in one
variable (`Interval.eLpNorm_higherDiff_ppFun_le`), applied to every slice and integrated over the
point, bounds the differences in each coordinate:
`‖Δ^r_{h e_i} g‖_{L_p({x_i ≤ 1 - rh})} ≤ 2^r K (r (r + 1) 2^j h)^(1/p) ‖g‖_{L_p(Q)}` for
`0 ≤ h ≤ 2^(-j)` (`Cube.eLpNorm_cubeDiff_le_of_isCubePP`). Summed over the coordinates this is the
**inverse inequality of order `1/p`** (`Cube.exists_inverse_cubePPScheme`).

With Jackson's inequality at every level (`Cube.exists_approxError_cubePPScheme_le`, Whitney's
inequality at level `0`) the modulus on the cube is compatible with the scheme
(`Cube.cubePPModulusData`), and the coincidence theorem of
`ApproximationSpaces.Moduli` gives `A^s_q = B^s_{p,q}([0, 1]^d)` for `0 ≤ s < 1/p`
(`Cube.memApprox_cubePPScheme_iff`), with the Besov space defined by the moduli in the
coordinates.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Cube

open Interval

variable {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The local inverse estimate on the cube**: for a piecewise polynomial `g` of level `j` on
the cube and `0 ≤ h ≤ 2^(-j)`,
`‖Δ^r_{h e_i} g‖_{L_p({x_i ≤ 1 - rh})} ≤ 2^r K (r (r + 1) 2^j h)^(1/p) ‖g‖_{L_p(Q)}`, with the
Nikolskii constant `K` of the polynomials of degree `< r`. Each slice satisfies the estimate in
one variable (`Interval.eLpNorm_higherDiff_ppFun_le`). -/
theorem eLpNorm_cubeDiff_le_of_isCubePP {r j : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : IsCubePP r j g)
    {K : ℝ≥0∞} (hKb : NikolskiiBound p r K) (hp : p ≠ ∞) (i : Fin d) {h : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 1 / 2 ^ j) :
    eLpNorm (cubeDiff r h i g) p (diffRegion d r h i) ≤
      2 ^ r * K * (((r * (r + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 ^ j * h)) ^ (1 / p.toReal) *
        eLpNorm g p (cubeVol d) := by
  refine eLpNorm_cubeDiff_le_of_slice_le hg.1.1
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp r hh0 i fun x => ?_
  obtain ⟨Q, hQ, hs⟩ := hg.exists_slice_eq_ppFun i x
  rw [hs]
  exact eLpNorm_higherDiff_ppFun_le hQ hKb hp j hh0 hh

/-- **The inverse inequality for piecewise polynomials on the cube**, of order `θ = 1/p`: there is
`C_B < ∞` with `ω_r(a, 2^(-k))_p ≤ C_B 2^(-(k-j)/p) ‖a‖_p` for every piecewise polynomial `a` of
level `j` on the cube (and `k - j` truncated at `0`). -/
theorem exists_inverse_cubePPScheme {r : ℕ} (hp : p ≠ ∞) :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ j k : ℕ, ∀ a ∈ cubePPScheme p d r (2 ^ j),
      lpCubeModulus p r a k ≤ CB * dyadicWeight (-(1 / p.toReal)) (k - j) * ‖a‖ₑ := by
  obtain ⟨K, hK, hKb⟩ := enorm_polyFun_le (p := p) r hp
  refine ⟨d * ppInverseConst p r K, ENNReal.mul_ne_top (ENNReal.natCast_ne_top d)
    (ppInverseConst_ne_top r hK), fun j k a ha => ?_⟩
  obtain ⟨g, hg, hae⟩ := mem_cubePPScheme_two_pow.1 ha
  refine lpCubeModulus_le_of_coord hp (two_pow_le_ppInverseConst r K) hg.1.1 hae
    fun hjk i h hh0 hh => ?_
  exact (eLpNorm_cubeDiff_le_of_isCubePP hg hKb hp i hh0 (hh.trans (one_div_le_one_div_of_le
    (by positivity) (pow_le_pow_right₀ (by norm_num) hjk)))).trans
    (le_ppInverseConst_mul hjk K hh _)

/-- The modulus `ω_r(f, 2^(-k))_p` on the cube is compatible with the scheme of piecewise
polynomials on the cube, with inverse order `θ = 1/p` and Jackson's inequality at every level
(Whitney's inequality at level `0`). -/
noncomputable def cubePPModulusData {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) :
    ApproximationScheme.ModulusData (cubePPScheme p d r) (1 / p.toReal) :=
  .ofExists (lpCubeModulus p r) (lpCubeModulus_add_le hp r) (d * 2 ^ r)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (by simp)) (lpCubeModulus_le hp r) 0
    ((exists_approxError_cubePPScheme_le hr hp).imp fun _ h => ⟨h.1, fun f k _ => h.2 f k⟩)
    (exists_inverse_cubePPScheme hp)

/-- **Approximation by piecewise polynomials on the cube.** For `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`r ≥ 1` and `0 ≤ s < 1/p`, an `f ∈ L_p([0, 1]^d)` lies in the approximation space `A^s_q` of the
piecewise polynomials of degree `< r` in each variable on dyadic cubes iff its Besov quasi-norm
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}` is finite, where `ω_r = ∑_i ω_r^{(i)}` is the sum of
the moduli in the coordinates. -/
theorem memApprox_cubePPScheme_iff {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (hs : 0 ≤ s) (hsp : s < 1 / p.toReal) (f : Lp ℂ p (cubeVol d)) :
    (cubePPScheme p d r).MemApprox s q f ↔
      ‖f‖ₑ + ENNReal.lqNorm q (fun k => dyadicWeight s k * lpCubeModulus p r f k) < ∞ :=
  (cubePPModulusData hr hp).memApprox_iff_modNorm_lt_top hq hs hsp f

end Cube
