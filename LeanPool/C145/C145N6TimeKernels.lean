/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145N6Uncalibrated
public import LeanPool.C145.C145DelayKernelTransfer

/-!
# Recovery of six-vertex time kernels from terminal observations.
-/

@[expose] public section
noncomputable section
namespace C145N6Frame
open MeasureTheory Set C145.DelayKernel
open scoped BigOperators

theorem literal_N6_time_kernels_identification {n : ℕ}
    (c1 : ℝ) (Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates1 b1 : Fin (n + 1) → ℝ)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hGround1 : ∀ v, Q1 v 0 = c1)
    (hRates1 : Function.Injective rates1)
    (hRateGround1 : rates1 0 = 1)
    (hAbove1 : ∀ j : Fin n, 1 < rates1 j.succ)
    (ha1 : ∀ j, 0 < C145.Pulse.modalOverlap Q1 b1 j)
    (hK1 : ∀ r : ℝ, 0 ≤ r →
      firstKernel frame literalRates port r = firstKernel Q1 rates1 b1 r)
    (hK2 : ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
      delayKernel frame literalRates port r₁ r₂ =
        delayKernel Q1 rates1 b1 r₁ r₂) :
    ∃ e : Fin (5 + 1) ≃ Fin (n + 1),
      5 = n ∧ e 0 = 0 ∧
      (∀ i, rates1 (e i) = literalRates i) ∧
      (∀ i, C145.Pulse.modalOverlap Q1 b1 (e i) =
        C145.Pulse.modalOverlap frame port i) ∧
      (1 / Real.sqrt 6) = c1 ∧ (∑ v, port v) = (∑ w, b1 w) ∧
      ∃ π : Fin (5 + 1) ≃ Fin (n + 1),
        (∀ (w : Fin (n + 1)) (v : Fin (5 + 1)),
          (∑ i : Fin (5 + 1), Q1 w (e i) * frame v i) =
            if w = π v then 1 else 0) ∧
        (∀ (v i : Fin (5 + 1)), Q1 (π v) (e i) = frame v i) ∧
        (∀ (v u : Fin (5 + 1)),
          C145CoordinatePermutation.spectralGenerator rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.spectralGenerator literalRates frame v u) ∧
        (∀ v : Fin (5 + 1), b1 (π v) = port v) ∧
        (∀ (v u : Fin (5 + 1)),
          C145CoordinatePermutation.decayLaplacian 1 rates1 Q1 (π v) (π u) =
            C145CoordinatePermutation.decayLaplacian 1 literalRates frame v u) := by
  have hPos0 : ∀ i, 0 < literalRates i := by
    intro i; fin_cases i <;> norm_num [literalRates]
  have hPos1 : ∀ i, 0 < rates1 i := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j,rfl⟩
    · rw [h,hRateGround1]; norm_num
    · exact lt_trans (by norm_num : (0 : ℝ) < 1) (hAbove1 j)
  have hH1 : ∀ s : ℝ, 0 < s →
      C145.H1.firstTransfer literalRates (C145.Pulse.modalOverlap frame port) s =
        C145.H1.firstTransfer rates1 (C145.Pulse.modalOverlap Q1 b1) s := by
    intro s hs
    rw [← (firstKernel_transform frame literalRates port hPos0 s hs).2,
      ← (firstKernel_transform Q1 rates1 b1 hPos1 s hs).2]
    unfold laplace
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change Real.exp (-s * r) * firstKernel frame literalRates port r =
      Real.exp (-s * r) * firstKernel Q1 rates1 b1 r
    rw [hK1 r hr.le]
  have hB : ∀ t : ℝ, 0 ≤ t →
      C145.Pulse.coincidentPulse frame literalRates port t =
        C145.Pulse.coincidentPulse Q1 rates1 b1 t := by
    intro t ht
    rw [← delayKernel_diagonal frame literalRates port t,
      ← delayKernel_diagonal Q1 rates1 b1 t]
    exact hK2 t t ht ht
  have hH2 : ∀ s t : ℝ, 0 < s → 0 < t →
      C145.H2.H literalRates (C145PhysicalFrame.T frame (C145.Pulse.modalOverlap frame port)) s t =
        C145.H2.H rates1 (C145PhysicalFrame.T Q1 (C145.Pulse.modalOverlap Q1 b1)) s t := by
    intro s t hs ht
    rw [← (delayKernel_transform frame literalRates port hPos0 s t hs ht).2,
      ← (delayKernel_transform Q1 rates1 b1 hPos1 s t hs ht).2]
    unfold doubleLaplace
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r₁ hr₁
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r₂ hr₂
    change Real.exp (-s * r₁) * Real.exp (-t * r₂) * delayKernel frame literalRates port r₁ r₂ =
      Real.exp (-s * r₁) * Real.exp (-t * r₂) * delayKernel Q1 rates1 b1 r₁ r₂
    rw [hK2 r₁ r₂ hr₁.le hr₂.le]
  exact literal_N6_uncalibrated_identification c1 Q1 rates1 b1 hQ1 hGround1 hRates1
    hRateGround1 hAbove1 ha1 hH1 hB hH2

end C145N6Frame

end
