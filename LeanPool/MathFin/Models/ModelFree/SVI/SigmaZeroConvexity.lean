/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.SigmaZeroDerivatives
public import LeanPool.MathFin.Models.ModelFree.SVI.ConvexKink
public import LeanPool.MathFin.Models.ModelFree.SVI.BlackScholesBridge

/-! # Convexity of the call at zero scale

Part of the SVI polynomial-sign certificate (#174).

The σ = 0 Black-price convexity bridge, including the nonnegative
first-derivative jump at the kink. No smoothness at the kink is assumed.

## Main results

* `sigmaZero_blackCall_hasDerivAt`, `sigmaZero_strikeDelta_hasDerivAt`: at `σ = 0`, away from the
  kink `log K = m` and with positive variance, `blackCall p` has derivative `strikeDelta p K` and
  `strikeDelta p` has derivative `strikeDensity p K` at `K`.
* `sigmaZero_blackCall_hasDerivWithinAt_left`, `sigmaZero_blackCall_hasDerivWithinAt_right`: at
  `σ = 0` and `a > 0`, the one-sided derivatives of `blackCall p` at `exp m` are
  `branchDelta p (leftSlope p) m` and `branchDelta p (rightSlope p) m`.
* `sigmaZero_delta_jump`: the jump `branchDelta p (rightSlope p) m - branchDelta p (leftSlope p) m`
  equals `gaussianPDFReal 0 1 (dmi m w) * b / rootVariance p m` with `w = variance p m`.
* `sigmaZero_delta_jump_nonneg`: for `b ≥ 0` and `variance p m > 0`, the jump is nonnegative.
* `sigmaZero_blackCall_convex_iff`: for `σ = 0`, `b ≥ 0` and `variance p k > 0` for all `k`,
  `blackCall p` is convex on `(0, ∞)` iff `durrleman p k ≥ 0` for every `k ≠ m`.
* `sigmaZero_bsSmile_convex_iff`: the same equivalence for `bsSmile p`.

## Tags

zero-scale SVI, call convexity at kink, one-sided derivative jump, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI
open Real ProbabilityTheory Set
open ForwardSmile (dpl dmi blackForm)

theorem sigmaZero_blackCall_hasDerivAt (p : Params) (hs : p.sigma = 0)
    (K : ℝ) (hK : 0 < K) (hk : Real.log K ≠ p.m)
    (hw : 0 < variance p (Real.log K)) :
    HasDerivAt (blackCall p) (strikeDelta p K) K := by
  have h := (blackForm_hasDerivAt p (Real.log K)
    (sigmaZero_variance_hasDerivAt p hs _ hk) hw).comp K (Real.hasDerivAt_log (ne_of_gt hK))
  convert h using 1 <;> try rfl
  simp only [Real.exp_log hK, strikeDelta]
  field_simp

theorem sigmaZero_strikeDelta_hasDerivAt (p : Params) (hs : p.sigma = 0)
    (K : ℝ) (hK : 0 < K) (hk : Real.log K ≠ p.m)
    (hw : 0 < variance p (Real.log K)) :
    HasDerivAt (strikeDelta p) (strikeDensity p K) K := by
  have h := (blackDelta_hasDerivAt p (Real.log K) (sigmaZero_variance_hasDerivAt p hs _ hk)
    (sigmaZero_slope_hasDerivAt p hs _ hk) hw).comp K
    (Real.hasDerivAt_log (ne_of_gt hK))
  convert h using 1 <;> try rfl
  dsimp [strikeDensity]
  ring

theorem sigmaZero_blackCall_hasDerivWithinAt_left (p : Params) (hs : p.sigma = 0)
    (ha : 0 < p.a) : HasDerivWithinAt (blackCall p)
      (branchDelta p (leftSlope p) p.m) (Iic (Real.exp p.m)) (Real.exp p.m) := by
  have hw : 0 < variance p p.m := by rwa [sigmaZero_variance_at_m p hs]
  have h := blackForm_hasDerivWithinAt p (leftSlope p) p.m (Iic p.m) hw
    (sigmaZero_variance_hasDerivWithinAt_left p hs)
  have hm : MapsTo Real.log (Iic (Real.exp p.m) ∩ Ioi 0) (Iic p.m) := by
    intro x hx
    exact (Real.log_le_iff_le_exp hx.2).mpr hx.1
  have hc := h.comp_of_eq (Real.exp p.m)
    (Real.hasDerivAt_log (ne_of_gt (Real.exp_pos p.m))).hasDerivWithinAt hm
    (Real.log_exp p.m).symm
  have he : Real.exp p.m * branchDelta p (leftSlope p) p.m * (Real.exp p.m)⁻¹ =
      branchDelta p (leftSlope p) p.m := by field_simp
  rw [he] at hc
  exact (hasDerivWithinAt_inter (Ioi_mem_nhds (Real.exp_pos p.m))).mp hc

theorem sigmaZero_blackCall_hasDerivWithinAt_right (p : Params) (hs : p.sigma = 0)
    (ha : 0 < p.a) : HasDerivWithinAt (blackCall p)
      (branchDelta p (rightSlope p) p.m) (Ici (Real.exp p.m)) (Real.exp p.m) := by
  have hw : 0 < variance p p.m := by rwa [sigmaZero_variance_at_m p hs]
  have h := blackForm_hasDerivWithinAt p (rightSlope p) p.m (Ici p.m) hw
    (sigmaZero_variance_hasDerivWithinAt_right p hs)
  have hm : MapsTo Real.log (Ici (Real.exp p.m)) (Ici p.m) := by
    intro x hx
    exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hx)).mpr hx
  have hc := h.comp_of_eq (Real.exp p.m)
    (Real.hasDerivAt_log (ne_of_gt (Real.exp_pos p.m))).hasDerivWithinAt hm
    (Real.log_exp p.m).symm
  convert hc using 1 <;> first | rfl | field_simp

theorem sigmaZero_delta_jump (p : Params) :
    branchDelta p (rightSlope p) p.m - branchDelta p (leftSlope p) p.m =
      gaussianPDFReal 0 1 (dmi p.m (variance p p.m)) * p.b / rootVariance p p.m := by
  unfold branchDelta leftSlope rightSlope
  ring

theorem sigmaZero_delta_jump_nonneg (p : Params) (hb : 0 ≤ p.b)
    (hw : 0 < variance p p.m) :
    branchDelta p (leftSlope p) p.m ≤ branchDelta p (rightSlope p) p.m := by
  have hp := (gaussianPDFReal_pos 0 1 (dmi p.m (variance p p.m)) (by norm_num)).le
  have hr := (rootVariance_pos p p.m hw).le
  have hs : leftSlope p ≤ rightSlope p := by unfold leftSlope rightSlope; nlinarith
  unfold branchDelta
  exact sub_le_sub_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hp)
    (mul_nonneg (by norm_num) hr)) _

theorem variance_continuous (p : Params) : Continuous (variance p) := by
  unfold variance
  fun_prop

theorem blackCall_continuousOn (p : Params) (hw : ∀ k : ℝ, 0 < variance p k) :
    ContinuousOn (blackCall p) (Ioi 0) := by
  have hr : Continuous (rootVariance p) := (variance_continuous p).sqrt
  have hn : ∀ k, rootVariance p k ≠ 0 := fun k ↦ ne_of_gt (rootVariance_pos p k (hw k))
  have hm : Continuous (fun k ↦ dmi k (variance p k)) := by
    simp only [dmi_eq_rootVariance]
    exact (continuous_id.neg.div hr hn).sub (hr.div_const 2)
  have hp : Continuous (fun k ↦ dpl k (variance p k)) := by
    simp only [dpl_eq_rootVariance]
    exact (continuous_id.neg.div hr hn).add (hr.div_const 2)
  have hphi : Continuous MathFin.Phi := continuous_iff_continuousAt.mpr
    (fun x ↦ (MathFin.hasDerivAt_Phi x).continuousAt)
  have hc : Continuous (fun k ↦ blackForm k (variance p k)) := (hphi.comp hp).sub
    (Real.continuous_exp.mul (hphi.comp hm))
  exact hc.comp_continuousOn (Real.continuousOn_log.mono (fun x hx ↦ ne_of_gt hx))

/-- Convexity on either closed side follows from the ordinary density there. -/
theorem sigmaZero_convexOn_of_nonneg (p : Params) (hs : p.sigma = 0)
    (hw : ∀ k : ℝ, 0 < variance p k) (D : Set ℝ) (hD : Convex ℝ D)
    (hpos : D ⊆ Ioi 0) (hk : ∀ K ∈ interior D, Real.log K ≠ p.m)
    (hg : ∀ k : ℝ, k ≠ p.m → 0 ≤ durrleman p k) :
    ConvexOn ℝ D (blackCall p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg hD
    ((blackCall_continuousOn p hw).mono hpos)
    (f' := strikeDelta p) (f'' := strikeDensity p)
  · intro K hK
    exact (sigmaZero_blackCall_hasDerivAt p hs K (hpos (interior_subset hK))
      (hk K hK) (hw _)).hasDerivWithinAt
  · intro K hK
    exact (sigmaZero_strikeDelta_hasDerivAt p hs K (hpos (interior_subset hK))
      (hk K hK) (hw _)).hasDerivWithinAt
  · intro K hK
    exact (strikeDensity_nonneg_iff p K (hpos (interior_subset hK)) (hw _)).mpr
      (hg _ (hk K hK))

/-- The density criterion on both open wings, with the automatically
nonnegative vega-weighted derivative jump at the kink, is exactly convexity. -/
theorem sigmaZero_blackCall_convex_iff (p : Params) (hs : p.sigma = 0)
    (hb : 0 ≤ p.b) (hw : ∀ k : ℝ, 0 < variance p k) :
    ConvexOn ℝ (Ioi 0) (blackCall p) ↔
      ∀ k : ℝ, k ≠ p.m → 0 ≤ durrleman p k := by
  constructor
  · intro hc k hk
    let D : Set ℝ := Ioi 0 ∩ {K | Real.log K ≠ p.m}
    have hDopen : IsOpen D := by
      have he : D = Ioi 0 \ {Real.exp p.m} := by
        ext K
        simp only [D, mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_sdiff,
          mem_singleton_iff]
        constructor
        · rintro ⟨hK, hne⟩
          exact ⟨hK, fun hh ↦ hne (by rw [hh, Real.log_exp])⟩
        · rintro ⟨hK, hne⟩
          exact ⟨hK, fun hh ↦ hne (by rw [← hh, Real.exp_log hK])⟩
      rw [he]
      exact isOpen_Ioi.sdiff isClosed_singleton
    have hd (K : ℝ) (hK : K ∈ D) :=
      sigmaZero_blackCall_hasDerivAt p hs K hK.1 hK.2 (hw _)
    have hm : MonotoneOn (strikeDelta p) D := by
      intro x hx y hy hxy
      rcases eq_or_lt_of_le hxy with rfl | hxy
      · rfl
      rw [← (hd x hx).deriv, ← (hd y hy).deriv]
      exact (hc.deriv_le_slope hx.1 hy.1 hxy (hd x hx).differentiableAt).trans
        (hc.slope_le_deriv hx.1 hy.1 hxy (hd y hy).differentiableAt)
    have he : Real.exp k ∈ D := ⟨Real.exp_pos _, by simpa using hk⟩
    have hh : 0 ≤ derivWithin (strikeDelta p) D (Real.exp k) := hm.derivWithin_nonneg
    rw [(sigmaZero_strikeDelta_hasDerivAt p hs _ he.1 he.2 (hw _)).hasDerivWithinAt.derivWithin
      (hDopen.uniqueDiffOn _ he)] at hh
    have hg := (strikeDensity_nonneg_iff p _ he.1 (hw _)).mp hh
    simpa using hg
  · intro hg
    have ha : 0 < p.a := by simpa [sigmaZero_variance_at_m p hs] using hw p.m
    apply convexOn_Ioi_of_convex_pieces (Real.exp_pos p.m)
    · apply sigmaZero_convexOn_of_nonneg p hs hw (Ioc 0 (Real.exp p.m))
        (convex_Ioc _ _) (fun _ h ↦ h.1) _ hg
      intro K hK
      rw [interior_Ioc] at hK
      exact ne_of_lt ((Real.log_lt_iff_lt_exp hK.1).mpr hK.2)
    · apply sigmaZero_convexOn_of_nonneg p hs hw (Ici (Real.exp p.m))
        (convex_Ici _) (fun _ h ↦ lt_of_lt_of_le (Real.exp_pos _) h) _ hg
      intro K hK
      rw [interior_Ici] at hK
      exact ne_of_gt ((Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hK)).mpr hK)
    · exact sigmaZero_blackCall_hasDerivWithinAt_left p hs ha
    · exact sigmaZero_blackCall_hasDerivWithinAt_right p hs ha
    · exact sigmaZero_delta_jump_nonneg p hb (hw _)

theorem sigmaZero_bsSmile_convex_iff (p : Params) (hs : p.sigma = 0)
    (hb : 0 ≤ p.b) (hw : ∀ k : ℝ, 0 < variance p k) :
    ConvexOn ℝ (Ioi 0) (bsSmile p) ↔
      ∀ k : ℝ, k ≠ p.m → 0 ≤ durrleman p k := by
  have he : EqOn (blackCall p) (bsSmile p) (Ioi 0) :=
    fun K hK ↦ blackCall_eq_bsSmile p K hK (hw _)
  constructor
  · intro hc
    exact (sigmaZero_blackCall_convex_iff p hs hb hw).mp (hc.congr he.symm)
  · intro hg
    exact ((sigmaZero_blackCall_convex_iff p hs hb hw).mpr hg).congr he

end SVI
end MathFin
