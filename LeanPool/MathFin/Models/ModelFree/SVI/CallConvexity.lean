/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.BlackSmile
public import LeanPool.MathFin.Models.ModelFree.SVI.DomainFormula
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Smooth.Flat

/-! # Durrleman's condition is convexity of the call in strike

Part of the SVI polynomial-sign certificate (#174).

The second strike derivative of the SVI-smiled Black call is computed (`blackCall_deriv2`), and
for `σ > 0` and positive variance its convexity on `(0, ∞)` is equivalent to `g(k) ≥ 0` for every
`k` (`blackCall_convex_iff`).

## Main definitions

* `strikeDelta`: the first strike derivative of `blackCall`, `blackDelta p (log K)`.
* `strikeDensity`: the second strike derivative of `blackCall`, a positive Gaussian factor times
  Durrleman's function.

## Main results

* `blackCall_deriv2`: for `σ > 0` and positive variance, the second derivative of `blackCall p` in
  strike `K > 0` equals `strikeDensity p K`.
* `strikeDensity_nonneg_iff`: `0 ≤ strikeDensity p K` iff `0 ≤ durrleman p (log K)`.
* `blackCall_convex_iff`: for `σ > 0` and positive variance, `blackCall p` is convex on `(0, ∞)`
  iff `0 ≤ durrleman p k` for every `k`.
* `certificateFormula_iff_call_convex`: on `σ > 0`, `b ≥ 0`, `1 - ρ² ≥ 0` and the variance gate,
  the finite sign formula `certificateFormula` holds iff `blackCall p` is convex on `(0, ∞)`.
* `fullCertificateFormula_iff_call_convex`: `fullCertificateFormula` holds iff the parameters
  satisfy the domain conditions and `blackCall p` is convex on `(0, ∞)`.

## Tags

Durrleman condition, call convexity in strike, butterfly arbitrage, SVI smile, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Real ProbabilityTheory Set
open ForwardSmile (dpl dmi blackForm)

/-- The first derivative of `blackCall` in strike (`blackCall_hasDerivAt`). -/
noncomputable def strikeDelta (p : Params) (K : ℝ) : ℝ := blackDelta p (Real.log K)
/-- The second derivative of `blackCall` in strike: a positive Gaussian factor times Durrleman's
function (`strikeDelta_hasDerivAt`). -/
noncomputable def strikeDensity (p : Params) (K : ℝ) : ℝ :=
  gaussianPDFReal 0 1 (dmi (Real.log K) (variance p (Real.log K))) /
    (K*rootVariance p (Real.log K)) * durrleman p (Real.log K)

theorem blackCall_hasDerivAt (p : Params) (hs : 0 < p.sigma) (K : ℝ) (hK : 0 < K)
    (hw : 0 < variance p (Real.log K)) :
    HasDerivAt (blackCall p) (strikeDelta p K) K := by
  have h := (blackForm_hasDerivAt p (Real.log K) (variance_hasDerivAt p hs _) hw).comp K
    (Real.hasDerivAt_log (ne_of_gt hK))
  convert h using 1 <;> try rfl
  simp only [Real.exp_log hK, strikeDelta]
  field_simp

theorem strikeDelta_hasDerivAt (p : Params) (hs : 0 < p.sigma) (K : ℝ) (hK : 0 < K)
    (hw : 0 < variance p (Real.log K)) :
    HasDerivAt (strikeDelta p) (strikeDensity p K) K := by
  have h := (blackDelta_hasDerivAt p (Real.log K) (variance_hasDerivAt p hs _)
    (slope_hasDerivAt p hs _) hw).comp K
    (Real.hasDerivAt_log (ne_of_gt hK))
  convert h using 1 <;> try rfl
  dsimp [strikeDensity]
  ring

theorem strikeDensity_nonneg_iff (p : Params) (K : ℝ) (hK : 0 < K)
    (hw : 0 < variance p (Real.log K)) :
    0 ≤ strikeDensity p K ↔ 0 ≤ durrleman p (Real.log K) := by
  have hp := gaussianPDFReal_pos 0 1 (dmi (Real.log K) (variance p (Real.log K))) (by norm_num)
  have hs := rootVariance_pos p (Real.log K) hw
  exact mul_nonneg_iff_of_pos_left (div_pos hp (mul_pos hK hs))

/-- The actual second strike derivative, including the smile's first and
second variance derivatives. -/
theorem blackCall_deriv2 (p : Params) (hs : 0 < p.sigma)
    (hw : ∀ k : ℝ, 0 < variance p k) (K : ℝ) (hK : 0 < K) :
    deriv (deriv (blackCall p)) K = strikeDensity p K := by
  have he : deriv (blackCall p) =ᶠ[nhds K] strikeDelta p := by
    filter_upwards [eventually_gt_nhds hK] with x hx
    exact (blackCall_hasDerivAt p hs x hx (hw _)).deriv
  exact ((strikeDelta_hasDerivAt p hs K hK (hw _)).congr_of_eventuallyEq he).deriv

/-- Durrleman's condition is exactly convexity in positive strike ratio of
the forward-normalized Black call with this SVI total variance. -/
theorem blackCall_convex_iff (p : Params) (hs : 0 < p.sigma)
    (hw : ∀ k : ℝ, 0 < variance p k) :
    ConvexOn ℝ (Ioi 0) (blackCall p) ↔ ∀ k : ℝ, 0 ≤ durrleman p k := by
  have hfirst (K : ℝ) (hK : K ∈ Ioi (0 : ℝ)) := blackCall_hasDerivAt p hs K hK (hw _)
  have hsecond (K : ℝ) (hK : K ∈ Ioi (0 : ℝ)) := strikeDelta_hasDerivAt p hs K hK (hw _)
  constructor
  · intro hc k
    have hm := hc.monotoneOn_deriv (fun K hK ↦ (hfirst K hK).differentiableAt)
    have hm' : MonotoneOn (strikeDelta p) (Ioi 0) := by
      intro x hx y hy hxy
      rw [← (hfirst x hx).deriv, ← (hfirst y hy).deriv]
      exact hm hx hy hxy
    have hh : 0 ≤ derivWithin (strikeDelta p) (Ioi 0) (Real.exp k) := hm'.derivWithin_nonneg
    rw [(hsecond _ (Real.exp_pos k)).hasDerivWithinAt.derivWithin
        (isOpen_Ioi.uniqueDiffOn _ (Real.exp_pos k))] at hh
    have hg := (strikeDensity_nonneg_iff p _ (Real.exp_pos k) (hw _)).mp hh
    simpa using hg
  · intro hg
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi (0 : ℝ))
      (fun K hK ↦ (hfirst K hK).continuousAt.continuousWithinAt)
      (f' := strikeDelta p) (f'' := strikeDensity p)
    · intro K hK
      exact (hfirst K (interior_subset hK)).hasDerivWithinAt
    · intro K hK
      exact (hsecond K (interior_subset hK)).hasDerivWithinAt
    · intro K hK
      exact (strikeDensity_nonneg_iff p K (interior_subset hK) (hw _)).mpr (hg _)

/-- The finite determinant formula characterizes call-price convexity on the
entire stated smooth positive-variance parameter domain. -/
theorem certificateFormula_iff_call_convex (p : Params) (hs : 0 < p.sigma)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1 - p.rho ^ 2) (hg : varianceGate p) :
    certificateFormula.eval p = true ↔ ConvexOn ℝ (Ioi 0) (blackCall p) := by
  rw [blackCall_convex_iff p hs ((varianceGate_iff p hs hb hr).mp hg)]
  exact certificateFormula_iff p hs hb hr hg

theorem fullCertificateFormula_iff_call_convex (p : Params) :
    fullCertificateFormula.eval p = true ↔
      0 < p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1-p.rho^2 ∧
      (∀ k : ℝ, 0 < variance p k) ∧ ConvexOn ℝ (Ioi 0) (blackCall p) := by
  rw [fullCertificateFormula_iff]
  constructor
  · rintro ⟨hs,hb,hr,hw,hg⟩
    exact ⟨hs,hb,hr,hw,(blackCall_convex_iff p hs hw).mpr hg⟩
  · rintro ⟨hs,hb,hr,hw,hc⟩
    exact ⟨hs,hb,hr,hw,(blackCall_convex_iff p hs hw).mp hc⟩

end SVI
end MathFin
