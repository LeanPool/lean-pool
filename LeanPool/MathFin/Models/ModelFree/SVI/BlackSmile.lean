/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.LocalVol.ForwardSmile
public import LeanPool.MathFin.Models.ModelFree.SVI.Reduction

/-! # The Black call with an SVI smile

Part of the SVI polynomial-sign certificate (#174).

The forward-normalised Black call as a function of log-strike and of strike, with total variance
given by raw SVI, and the derivatives of its `d₊`, `d₋` terms and of its delta
(`blackDelta_hasDerivAt`).

The Black terms are the abstract-variance ones of `Models/LocalVol/ForwardSmile.lean` at the SVI
total
variance `w(k)`: `dpl k (w k)`, `dmi k (w k)` and `blackForm k (w k)` are used directly, and the
Gaussian density cancellation is `exp_mul_pdf_dmi` at `w(k)`.
`durrleman_eq_one_add_smileDelta` relates Durrleman's function to the denominator deformation
`1 + smileDelta` of Dupire's ratio.

## Main definitions

* `rootVariance`: the square root `√w(k)` of the SVI total variance.
* `dmiSlope`: the explicit derivative of `d₋` in log-strike.
* `blackDelta`: the derivative of the Black call `blackForm k (w k)` in log-strike divided by `eᵏ`,
  the smile term minus `Φ(d₋)`.
* `blackCall`: the forward-normalised Black call as a function of the positive strike ratio.

## Main results

* `dpl_eq_rootVariance`, `dmi_eq_rootVariance`: `d₊ = −k/√w + √w/2` and `d₋ = −k/√w − √w/2` at the
  SVI total variance `w`.
* `rootVariance_hasDerivAt`, `dmi_hasDerivAt`, `dpl_hasDerivAt`: the derivatives of `√w`, `d₋` and
  `d₊` in log-strike, given the derivative of the variance and `w > 0`.
* `blackForm_hasDerivAt`: the log-strike derivative of the Black call `blackForm k (w k)` is
  `eᵏ · blackDelta p k`.
* `blackDelta_hasDerivAt`: given the derivatives of the variance and of its slope and `w > 0`, the
  derivative of `blackDelta` is the Gaussian factor `ϕ(d₋)/√w` times `durrleman p k`.
* `durrleman_eq_one_add_smileDelta`: where the SVI slice and the tilted surface of `ForwardSmile`
  share total variance, slope and curvature, `durrleman p k = 1 + smileDelta σ ψ₁ T₀ ε k T`.

## Tags

SVI smile, Black call, Durrleman function, Dupire local volatility, total variance, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Real ProbabilityTheory
open ForwardSmile (dpl dmi blackForm)

/-- The square root `√w(k)` of the SVI total variance. -/
noncomputable def rootVariance (p : Params) (k : ℝ) : ℝ := Real.sqrt (variance p k)
/-- `d₊ = −k/√w + √w/2` at the SVI total variance, in terms of `rootVariance`. -/
theorem dpl_eq_rootVariance (p : Params) (k : ℝ) :
    dpl k (variance p k) = -k / rootVariance p k + rootVariance p k / 2 :=
  ForwardSmile.dpl_eq k _

/-- `d₋ = −k/√w − √w/2` at the SVI total variance, in terms of `rootVariance`. -/
theorem dmi_eq_rootVariance (p : Params) (k : ℝ) :
    dmi k (variance p k) = -k / rootVariance p k - rootVariance p k / 2 :=
  ForwardSmile.dmi_eq k _

/-- The explicit derivative of `d₋` in log-strike (`dmi_hasDerivAt`). -/
noncomputable def dmiSlope (p : Params) (k : ℝ) : ℝ :=
  -1 / rootVariance p k + k*slope p k / (2*(rootVariance p k)^3) - slope p k / (4*rootVariance p k)

/-- The explicit derivative of the Black call `blackForm k (w k)` in log-strike, divided by `eᵏ`:
the smile term minus `Φ(d₋)`. -/
noncomputable def blackDelta (p : Params) (k : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (dmi k (variance p k)) * slope p k / (2*rootVariance p k) -
    MathFin.Phi (dmi k (variance p k))

/-- Forward-normalized Black call, as a function of positive strike ratio. -/
noncomputable def blackCall (p : Params) (K : ℝ) : ℝ :=
  blackForm (Real.log K) (variance p (Real.log K))

theorem rootVariance_pos (p : Params) (k : ℝ) (hw : 0 < variance p k) :
    0 < rootVariance p k := Real.sqrt_pos.mpr hw

theorem rootVariance_sq (p : Params) (k : ℝ) (hw : 0 ≤ variance p k) :
    (rootVariance p k)^2 = variance p k := Real.sq_sqrt hw

/-- The derivative of `√w`, given that of the SVI total variance `w`. -/
theorem rootVariance_hasDerivAt (p : Params) (k : ℝ)
    (hv : HasDerivAt (variance p) (slope p k) k)
    (hw : 0 < variance p k) :
    HasDerivAt (rootVariance p) (slope p k / (2*rootVariance p k)) k :=
  hv.sqrt (ne_of_gt hw)

theorem dmi_hasDerivAt (p : Params) (k : ℝ)
    (hv : HasDerivAt (variance p) (slope p k) k)
    (hw : 0 < variance p k) :
    HasDerivAt (fun k ↦ dmi k (variance p k)) (dmiSlope p k) k := by
  have hr := rootVariance_hasDerivAt p k hv hw
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have h := (((hasDerivAt_id k).neg).div hr hn).sub (hr.div_const 2)
  simp only [dmi_eq_rootVariance]
  convert h using 1 <;> try rfl
  dsimp [dmiSlope]
  field_simp
  ring

theorem dpl_hasDerivAt (p : Params) (k : ℝ)
    (hv : HasDerivAt (variance p) (slope p k) k)
    (hw : 0 < variance p k) :
    HasDerivAt (fun k ↦ dpl k (variance p k))
      (dmiSlope p k + slope p k / (2*rootVariance p k)) k := by
  have h := (dmi_hasDerivAt p k hv hw).add (rootVariance_hasDerivAt p k hv hw)
  convert h using 1
  funext x
  simp only [dpl_eq_rootVariance, dmi_eq_rootVariance, Pi.add_apply]
  ring

theorem blackForm_hasDerivAt (p : Params) (k : ℝ)
    (hv : HasDerivAt (variance p) (slope p k) k)
    (hw : 0 < variance p k) :
    HasDerivAt (fun k ↦ blackForm k (variance p k)) (Real.exp k * blackDelta p k) k := by
  have hp := (MathFin.hasDerivAt_Phi (dpl k (variance p k))).comp k (dpl_hasDerivAt p k hv hw)
  have hm := (MathFin.hasDerivAt_Phi (dmi k (variance p k))).comp k (dmi_hasDerivAt p k hv hw)
  have h := hp.sub ((Real.hasDerivAt_exp k).mul hm)
  convert h using 1 <;> try rfl
  rw [← ForwardSmile.exp_mul_pdf_dmi hw]
  dsimp [blackDelta]
  ring

/-- The derivative of the strike delta is the positive Gaussian factor times
Durrleman's expression, given the derivatives of the total variance and of its slope (the
regime-specific input: `variance_hasDerivAt`, `slope_hasDerivAt` for `σ > 0`, and their
zero-scale counterparts off the kink). -/
theorem blackDelta_hasDerivAt (p : Params) (k : ℝ)
    (hv : HasDerivAt (variance p) (slope p k) k)
    (hslope : HasDerivAt (slope p) (curvature p k) k)
    (hw : 0 < variance p k) :
    HasDerivAt (blackDelta p)
      (gaussianPDFReal 0 1 (dmi k (variance p k)) / rootVariance p k * durrleman p k) k := by
  have hm := dmi_hasDerivAt p k hv hw
  have hp := (MathFin.hasDerivAt_gaussianPDFReal_zero_one (dmi k (variance p k))).comp k hm
  have hc := (MathFin.hasDerivAt_Phi (dmi k (variance p k))).comp k hm
  have hr := rootVariance_hasDerivAt p k hv hw
  have hn := ne_of_gt (rootVariance_pos p k hw)
  have h := ((hp.mul hslope).div (hr.const_mul 2)
    (mul_ne_zero (by norm_num) hn)).sub hc
  convert h using 1 <;> try rfl
  simp only [durrleman, dmiSlope, dmi_eq_rootVariance, Function.comp_apply, Pi.mul_apply]
  rw [← rootVariance_sq p k hw.le]
  field_simp
  ring

/-- **`1 + smileDelta` is Durrleman's function.** The denominator deformation `1 + δ` of Dupire's
ratio on the tilted surface (`smileDelta`) has the algebraic form of Durrleman's `g`: at a
log-strike where the SVI slice and the tilted surface have the same total variance, slope and
curvature (`w'' = 2(εψ₁/√(T+T₀))²T`, the surface's constant `∂_kk w`), with the variance nonzero,
`durrleman p k = 1 + smileDelta σ ψ₁ T₀ ε k T`. -/
theorem durrleman_eq_one_add_smileDelta (p : Params) {σ ψ₁ T₀ ε k T : ℝ}
    (hw : variance p k = ForwardSmile.totalVar σ ψ₁ T₀ ε k T)
    (hw0 : ForwardSmile.totalVar σ ψ₁ T₀ ε k T ≠ 0)
    (hs : slope p k = ForwardSmile.wSlope σ ψ₁ T₀ ε T k)
    (hc : curvature p k = 2 * ((ε * ψ₁ / Real.sqrt (T + T₀)) ^ 2 * T)) :
    durrleman p k = 1 + ForwardSmile.smileDelta σ ψ₁ T₀ ε k T := by
  rw [durrleman, hw, hs, hc, ForwardSmile.smileDelta]
  field_simp
  ring

end SVI
end MathFin
