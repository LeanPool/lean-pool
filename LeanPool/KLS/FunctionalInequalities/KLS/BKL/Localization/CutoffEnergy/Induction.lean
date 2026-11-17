/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Base
public import LeanPool.KLS.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Basic

/-!
# Strong induction for the compact cumulant theorem
-/

@[expose] public section

noncomputable section
section CompactTheoremAssembly

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

/-! The strong induction over the order and Theorem 4.1 for compactly supported laws with `K = 153`,
given the induction step and the claim-to-bound passage as hypotheses. -/

namespace FunctionalInequalities.KLS.BKL.Localization

/--
**The cutoff claim at every order** (BKL (95) for all `m ≥ 2`), by induction from the base case and
the step. -/
theorem cutoffEnergyClaim_all (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ}
    (hK : 153 ≤ K)
    (hstep :
      ∀ m : ℕ,
        3 ≤ m →
          (∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1)) →
            (∀ r : ℕ,
                2 ≤ r →
                  r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) →
              CutoffEnergyClaim K (m - 1))
    (hbound :
      ∀ d : ℕ,
        CutoffEnergyClaim K d →
          LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1))) :
    ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim K d := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro n ih hn
  by_cases h1 : n = 1
  · subst n
    exact cutoffEnergyClaim_one hL (by linarith)
  · have hn2 : 2 ≤ n := by omega
    let m : ℕ := n + 1
    have hm : 3 ≤ m := by
      dsimp [m]
      omega
    have hs : CutoffEnergyClaim K (m - 1) := by
      apply hstep m hm
      · intro r hr2 hrm
        exact ih (r - 1) (by omega) (by omega)
      · intro r hr2 hrm
        have hclaim : CutoffEnergyClaim K (r - 1) := ih (r - 1) (by omega) (by omega)
        have hb := hbound (r - 1) hclaim
        rw [Nat.sub_add_cancel (by omega)] at hb
        exact hb
    have hm_sub : m - 1 = n := by dsimp [m]
    rw [hm_sub] at hs
    exact hs

/--
**BKL Theorem 4.1 for compactly supported laws** (conditional on the compact Letwin bound): there is
a universal
`K ≥ 1` with `R^ν_{d+1} ≤ (d!)² K^d · Id` for every compactly supported isotropic log-concave `ν`
and every `d ≥ 2`. -/
theorem theorem41Compact_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound)
    (hstep :
      ∀ m : ℕ,
        3 ≤ m →
          (∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim 153 (r - 1)) →
            (∀ r : ℕ,
                2 ≤ r →
                  r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope 153 r)) →
              CutoffEnergyClaim 153 (m - 1))
    (hbound :
      ∀ d : ℕ,
        CutoffEnergyClaim 153 d →
          LogConcave.Suspension.CumulantBoundCompact d (envelope 153 (d + 1))) :
    ∃ K : ℝ,
      1 ≤ K ∧
        ∀ d : ℕ,
          2 ≤ d →
            LogConcave.Suspension.CumulantBoundCompact d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  refine ⟨153, by norm_num, ?_⟩
  intro d hd
  have hclaim : CutoffEnergyClaim 153 d :=
    cutoffEnergyClaim_all hL (by norm_num) hstep hbound d (by omega)
  have hb := hbound d hclaim
  have henvelope : envelope 153 (d + 1) = (d.factorial : ℝ) ^ 2 * 153 ^ d := by
    unfold envelope
    rw [Nat.add_sub_cancel d 1]
    exact mul_comm _ _
  rw [henvelope] at hb
  exact hb

end FunctionalInequalities.KLS.BKL.Localization

end CompactTheoremAssembly
