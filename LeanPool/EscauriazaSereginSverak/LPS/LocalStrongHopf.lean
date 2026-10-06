/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEnergy
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

/-!
# Slice properties of strong solutions

These consequences of `IsLpsStrongSolution` are used when verifying the
Leray–Hopf clauses (`def:leray-hopf`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Every closed-interval slice of a strong solution is suitable as local
strong data (`prop:lps-local-strong`). -/
theorem lps_strong_solution_good_time
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    IsLpsGoodTime u Du t := by
  rcases hU with ⟨_hT, hSlices, _hContinuity, _hDerivatives, _hPressure,
    _hEquation⟩
  rcases hSlices t ht with ⟨hJ, hH1⟩
  exact ⟨hH1, hJ⟩

/-- The velocity and its specified gradient are square integrable on every
closed-interval slice (`prop:lps-local-strong`). -/
theorem lps_strong_solution_slice_memLp_two
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    MemLp (fun x : Vec3 => u (x,t)) 2 volume ∧
      MemLp (fun x : Vec3 => Du (x,t)) 2 volume := by
  rcases hU with ⟨_hT, hSlices, _hContinuity, _hDerivatives, _hPressure,
    _hEquation⟩
  rcases hSlices t ht with ⟨hJ, hH1⟩
  refine ⟨hJ.1, memLp_pi_iff.2 (fun i => ?_)⟩
  rcases hH1 i with ⟨h, _hFun, hGrad⟩
  apply memLp_pi_iff.2
  intro j
  simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ,
    hGrad] using h.gradMemL2 j

/-- The specified gradient on a strong slice is its weak gradient
(`prop:lps-local-strong`). -/
theorem lps_strong_solution_slice_weak_gradient
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x : Vec3 => u (x,t) i) (fun x : Vec3 => Du (x,t) i) := by
  rcases hU with ⟨_hT, hSlices, _hContinuity, _hDerivatives, _hPressure,
    _hEquation⟩
  rcases hSlices t ht with ⟨_hJ, hH1⟩
  intro i
  rcases hH1 i with ⟨h, hFun, hGrad⟩
  rw [← hFun, ← hGrad]
  exact h.hasWeakGradient

/-- Every strong slice is weakly divergence free (`prop:lps-local-strong`). -/
theorem lps_strong_solution_slice_weak_div_free
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    IsWeakDivFreeL2 (fun x : Vec3 => u (x,t)) := by
  exact isInJ_weakDivFree (lps_strong_solution_good_time hU ht).2

/-- The a.e. initial representative agrees with the strong right `L²` trace
(`prop:lps-local-strong`). -/
theorem lps_strong_solution_initial_trace
    {t₀ T : ℝ} {b : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    (hTrace : (fun x : Vec3 => u (x,t₀)) =ᵐ[volume] b) :
    Tendsto (fun t : ℝ => eLpNorm
      (fun x : Vec3 => u (x,t₀+t) - b x) 2 volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rcases hU with ⟨hT, _hSlices, hContinuity, _hDerivs, _hPressure,
    _hEquation⟩
  let U : ℝ → Vec3 → Vec3 := fun s x => u (x,s)
  have hCont : ∀ t ∈ Icc t₀ T,
      Tendsto (fun s => eLpNorm (fun x : Vec3 => U s x - U t x) 2 volume)
        (nhdsWithin t (Icc t₀ T)) (nhds 0) := by
    intro t ht
    exact hContinuity t ht |>.1
  simpa [U] using ESS.LPS.lps_l2_trace_of_ae_initial hT hCont hTrace

end ESS

end
