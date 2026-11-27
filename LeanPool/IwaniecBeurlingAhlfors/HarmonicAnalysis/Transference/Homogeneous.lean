/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Transference.ContinuousSymbol

/-!
# Transference from the torus to the plane for homogeneous symbols

`HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm` is the inequality `I ≤ II` of Corollary
5.7.6 of Hytönen–van Neerven–Veraar–Weis (HNVW), for `ℝ² ≅ ℂ` and scalar symbols: let `m : ℂ → ℂ`
be continuous at every `ξ ≠ 0`, with `m (t ξ) = m (ξ)` for `t > 0`. Then for `1 < p < ∞`,
`‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}`, where on the torus `T_m` multiplies the `n`-th Fourier
coefficient by `m (n₀ + i n₁)`.

As in HNVW, it is Proposition 5.7.4
(`HarmonicAnalysis.multiplierNorm_le_liminf_torusMultiplierNorm`) for a symbol homogeneous of degree
`0`: `m (n / R) = m (n)`, so the torus norms in the `liminf` are all equal.

HNVW sets `m (0)` to be the mean of `m` over the unit circle. Here `m (0)` is arbitrary, since it
does not matter for `L^p (ℝ²)` nor for the mean-zero functions on `𝕋²`; it matters for the norm
`III` on `L^p (𝕋²)`, and HNVW's `II ≤ III ≤ I` is not formalized. (The proof of `III ≤ I` there
quotes Proposition 5.7.1, which asks that every `k ∈ ℤ²` be a Lebesgue point of `m`; unless `m` is
constant, `0` is not one, and the choice of `m (0)` has to be used instead.)

## Main results

* `HarmonicAnalysis.multiplierNorm_le_torusMultiplierNorm`: the transference.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces, Volume I*, Ergebnisse
  der Mathematik 63, Springer, 2016: Corollary 5.7.6 (pp. 462–463), Proposition 5.7.1 (p. 458).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace HarmonicAnalysis

/-- **HNVW, Corollary 5.7.6**, the inequality `I ≤ II` (for `ℝ² ≅ ℂ` and scalar symbols): for a
symbol `m` that is continuous off `0` and homogeneous of degree `0`,
`‖T_m‖_{L^p (ℝ²)} ≤ ‖T_m‖_{L^p_0 (𝕋²)}` for `1 < p < ∞`.

By homogeneity, `m (n / R) = m (n)`, and Proposition 5.7.4
(`HarmonicAnalysis.multiplierNorm_le_liminf_torusMultiplierNorm`) applies. -/
theorem multiplierNorm_le_torusMultiplierNorm {m : ℂ → ℂ} (hmc : ∀ ξ ≠ 0, ContinuousAt m ξ)
    (hmh : ∀ t : ℝ, 0 < t → ∀ ξ, m (t * ξ) = m ξ) {p : ℝ} (hp : 1 < p) :
    multiplierNorm m p ≤ torusMultiplierNorm (fun n => m (latticePoint n)) p := by
  have h := multiplierNorm_le_liminf_torusMultiplierNorm hmc tendsto_natCast_atTop_atTop hp
  rwa [tendsto_const_nhds.congr' ?_ |>.liminf_eq] at h
  filter_upwards [eventually_gt_atTop 0] with j hj
  congr 1
  funext n
  rw [div_eq_inv_mul, ← Complex.ofReal_inv, hmh _ (inv_pos.2 (Nat.cast_pos.2 hj))]

end HarmonicAnalysis
