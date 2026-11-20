/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.ProductWindowColour
public import LeanPool.WordRepTensor.ProductWindows

/-! Full answers: the common colour would alternate around the longer odd cycle. -/

@[expose] public section

namespace WordRepTensor

/-- The affirmative answer to Alshammari’s Problem 5.2. -/
theorem not_wordRepresentable_mycielskian_tensor_extended :
  ∀ n m : ℕ, 1 ≤ n → n < m →
      ¬ WordRepresentable (tensorProd (mu (2 * n + 1)) (muExt (2 * m + 1))) := by
  intro n m hn hnm hwr
  let _ : NeZero (2 * m + 1) := ⟨by omega⟩
  have hk : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨w, hw⟩ := hwr
  refine no_flip_cycle (by omega : (2 * m + 1) % 2 = 1)
    (fun i => colOf winMuCol (stateOf (orient w (productWinMap hk i) winMuEdges) winMuS0)) ?_
  intro i
  obtain ⟨hi, hwin⟩ := productWindowsMu (2 * n + 1) (2 * m + 1) hk
    (by omega) (by omega) (by omega) (by omega) i
  have hf := commonWindowStep _ _ w (productWinMap hk i) hw hi hwin
  rw [productStateShift (2 * n + 1) (2 * m + 1) hk w i] at hf
  exact hf

/-- The affirmative answer to Alshammari’s Problem 5.3. -/
theorem not_wordRepresentable_extended_tensor_extended :
  ∀ n m : ℕ, 1 ≤ n → n < m →
      ¬ WordRepresentable (tensorProd (muExt (2 * n + 1)) (muExt (2 * m + 1))) := by
  intro n m hn hnm hwr
  let _ : NeZero (2 * m + 1) := ⟨by omega⟩
  have hk : 3 ≤ 2 * n + 1 := by omega
  obtain ⟨w, hw⟩ := hwr
  refine no_flip_cycle (by omega : (2 * m + 1) % 2 = 1)
    (fun i => colOf winMuCol (stateOf (orient w (productWinMap hk i) winMuEdges) winMuS0)) ?_
  intro i
  obtain ⟨hi, hwin⟩ := productWindowsExt (2 * n + 1) (2 * m + 1) hk
    (by omega) (by omega) (by omega) (by omega) i
  have hf := commonWindowStep _ _ w (productWinMap hk i) hw hi hwin
  rw [productStateShift (2 * n + 1) (2 * m + 1) hk w i] at hf
  exact hf

end WordRepTensor
