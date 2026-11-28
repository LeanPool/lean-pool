/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.CallConvexity

/-! # The certificate and MathFin's Black–Scholes price

Part of the SVI polynomial-sign certificate (#174).

`bsSmile` is `MathFin.bsV` with the SVI volatility substituted strike by strike, spot, maturity
and discount factor normalised to one. `fullCertificateFormula_iff_bsSmile_convex`: the finite
sign formula holds exactly when `σ > 0`, `b ≥ 0`, `ρ² ≤ 1`, the variance is positive, and that
price is convex in the strike.

## Main definitions

* `bsSmile`: `MathFin.bsV` with the SVI volatility substituted strike by strike, spot, maturity and
  discount factor normalised to one.

## Main results

* `blackCall_eq_bsSmile`: for `K > 0` and positive variance at `log K`, the forward-normalised Black
  call `blackCall p K` equals `bsSmile p K`.
* `bsSmile_convex_iff`: for `σ > 0` and positive variance, `bsSmile p` is convex on `(0, ∞)` iff
  `durrleman p k ≥ 0` for all `k`.
* `fullCertificateFormula_iff_bsSmile_convex`: the finite sign formula holds iff `σ > 0`, `b ≥ 0`,
  `ρ² ≤ 1`, the variance is positive and `bsSmile p` is convex on `(0, ∞)`.

## Tags

SVI smile, convex call price, butterfly arbitrage, Durrleman condition, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Real Set
open ForwardSmile (dpl dmi blackForm)

/-- The SVI-smiled Black–Scholes price in MathFin's existing price API,
with spot, maturity and discount factor normalized to one. -/
noncomputable def bsSmile (p : Params) (K : ℝ) : ℝ :=
  MathFin.bsV K 0 (rootVariance p (Real.log K)) 1 1

theorem blackCall_eq_bsSmile (p : Params) (K : ℝ) (hK : 0 < K)
    (hw : 0 < variance p (Real.log K)) : blackCall p K = bsSmile p K := by
  have hn := ne_of_gt (rootVariance_pos p (Real.log K) hw)
  have hd1 : MathFin.bsd1 1 K 0 (rootVariance p (Real.log K)) 1 =
      dpl (Real.log K) (variance p (Real.log K)) := by
    simp only [MathFin.bsd1, dpl_eq_rootVariance, Real.sqrt_one, mul_one, zero_add, one_div,
      Real.log_inv]
    field_simp
  have hd2 : MathFin.bsd2 1 K 0 (rootVariance p (Real.log K)) 1 =
      dmi (Real.log K) (variance p (Real.log K)) := by
    rw [MathFin.bsd2, hd1]
    simp only [Real.sqrt_one, mul_one, dpl_eq_rootVariance, dmi_eq_rootVariance]
    ring
  simp [blackCall, ForwardSmile.blackForm, bsSmile, MathFin.bsV, hd1, hd2, Real.exp_log hK]

/-- The certificate applies to the existing Black–Scholes function with SVI
volatility substituted strike by strike, not a constant-volatility derivative. -/
theorem bsSmile_convex_iff (p : Params) (hs : 0 < p.sigma)
    (hw : ∀ k : ℝ, 0 < variance p k) :
    ConvexOn ℝ (Ioi 0) (bsSmile p) ↔ ∀ k : ℝ, 0 ≤ durrleman p k := by
  have he : EqOn (blackCall p) (bsSmile p) (Ioi 0) :=
    fun K hK ↦ blackCall_eq_bsSmile p K hK (hw _)
  constructor
  · intro hc
    exact (blackCall_convex_iff p hs hw).mp (hc.congr he.symm)
  · intro hg
    exact ((blackCall_convex_iff p hs hw).mpr hg).congr he

theorem fullCertificateFormula_iff_bsSmile_convex (p : Params) :
    fullCertificateFormula.eval p = true ↔
      0 < p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧
      (∀ k : ℝ, 0 < variance p k) ∧ ConvexOn ℝ (Ioi 0) (bsSmile p) := by
  rw [fullCertificateFormula_iff]
  constructor
  · rintro ⟨hs,hb,hr,hw,hg⟩
    exact ⟨hs,hb,hr,hw,(bsSmile_convex_iff p hs hw).mpr hg⟩
  · rintro ⟨hs,hb,hr,hw,hc⟩
    exact ⟨hs,hb,hr,hw,(bsSmile_convex_iff p hs hw).mp hc⟩

end SVI
end MathFin
