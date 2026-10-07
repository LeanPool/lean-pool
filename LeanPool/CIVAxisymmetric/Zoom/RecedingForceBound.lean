/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.Receding
public import LeanPool.CIVAxisymmetric.Identities.ForceQuotient

/-! ### The `H_n` half of the zoom force terms

The receding vorticity equation carries the force term `λ^4 λ^{2h} (curl f)_θ` at the recentred
point. This module attaches the missing bound and its vanishing in the zoom scale, the companion
of `abs_zoomForce_le` and `tendsto_zoomForce_bound_nhdsWithin_zero` for the other force term.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV



/-- `|H_n| ≤ 2 M λ^4 λ^{2h}` at every recentred point of the unit cylinder, uniformly in the
point: the azimuthal vorticity of a `C²`-bounded force is bounded by `2 M`
(`abs_azimuthalVorticity_le_of_forceC2Bounded`), and `λ^4 λ^{2h} ≥ 0` for `λ > 0`. -/
theorem abs_recedingForce_le {lam h rc zc : ℝ} (hlam : 0 < lam)
    {f : ParabolicPoint → Vec3} {M : ℝ}
    (hM : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ M)
    {p : (ℝ × ℝ) × ℝ} (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    |lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc p)|
      ≤ 2 * M * (lam ^ 4 * lam ^ (2 * h)) := by
  have hpos : (0 : ℝ) ≤ lam ^ 4 * lam ^ (2 * h) := by positivity
  have hcurl : |curlComp f 1 (zoomPointRec lam h rc zc p)| ≤ 2 * M :=
    abs_azimuthalVorticity_le_of_forceC2Bounded hM hp
  rw [abs_mul, abs_of_nonneg hpos]
  calc lam ^ 4 * lam ^ (2 * h) * |curlComp f 1 (zoomPointRec lam h rc zc p)|
      ≤ lam ^ 4 * lam ^ (2 * h) * (2 * M) := mul_le_mul_of_nonneg_left hcurl hpos
    _ = 2 * M * (lam ^ 4 * lam ^ (2 * h)) := by ring

/-- The `ForceC2Bounded` form of `abs_recedingForce_le`, with a nonnegative constant depending
only on the force, matching the shape of `abs_zoomForce_le`. -/
theorem abs_recedingForce_le_of_forceC2Bounded {lam h rc zc : ℝ} (hlam : 0 < lam)
    {f : ParabolicPoint → Vec3} (hMf : ForceC2Bounded f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : (ℝ × ℝ) × ℝ, zoomPointRec lam h rc zc p ∈ unitCylinder →
      |lam ^ 4 * lam ^ (2 * h) * curlComp f 1 (zoomPointRec lam h rc zc p)|
        ≤ C * (lam ^ 4 * lam ^ (2 * h)) := by
  obtain ⟨M, hM⟩ := hMf
  have hMax : ∀ z ∈ unitCylinder, ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
      |multiPartial (fun w => f w i) α z| ≤ max M 0 :=
    fun z hz i α hα => (hM z hz i α hα).trans (le_max_left _ _)
  refine ⟨2 * max M 0, by positivity, fun p hp => ?_⟩
  exact abs_recedingForce_le hlam hMax hp

/-- The bound of `abs_recedingForce_le` tends to zero as `λ → 0⁺`, since
`λ^4 λ^{2h} = λ^{4 + 2h}` and `4 + 2h > 0`. This is the uniform vanishing of the `H_n` term. -/
theorem tendsto_recedingForce_bound_nhdsWithin_zero {C h : ℝ} (hh0 : 0 ≤ h) :
    Tendsto (fun lam : ℝ => C * (lam ^ 4 * lam ^ (2 * h))) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcongr : EqOn (fun lam : ℝ => C * (lam ^ 4 * lam ^ (2 * h)))
      (fun lam : ℝ => C * lam ^ (4 + 2 * h)) (Ioi (0 : ℝ)) := by
    intro lam hlam
    have hlam0 : (0 : ℝ) < lam := hlam
    simp only
    rw [Real.rpow_add hlam0]
    norm_num [Real.rpow_natCast]
  rw [Filter.tendsto_congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hcongr)]
  have hexp : (0 : ℝ) < 4 + 2 * h := by linarith only [hh0]
  have hcont : ContinuousAt (fun lam : ℝ => C * lam ^ (4 + 2 * h)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (4 + 2 * h) (Or.inr hexp.le))
  have hzero : (0 : ℝ) ^ (4 + 2 * h) = 0 := Real.zero_rpow (ne_of_gt hexp)
  have hres := hcont.tendsto
  rw [hzero, mul_zero] at hres
  exact hres.mono_left nhdsWithin_le_nhds

end CIV
