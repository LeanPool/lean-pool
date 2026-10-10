/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Main.Theorem1
public import LeanPool.ArnoldKAM.Arnold1963.Audit.W9Example

/-!
The full KAM theorem applied to the cubic two-branch Hamiltonian and a nonconstant small
perturbation, yielding actual disjoint tori and strict physical measure bounds.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Audit.W10Example
open W9Example
local instance w10ExamplePeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- The actual KAM result for the cubic Hamiltonian and its small nonconstant perturbation. -/
def result : Theorem1Result 1 cubic ambient 1 (1 / 2) perturbation :=
  localization.theorem1Result cubicOriginalData.compact perturbation perturbation_bound

theorem original_data_threshold :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction 1 ambient 1,
      f.uniformNorm ≤ M → Nonempty (Theorem1Result 1 cubic ambient 1 (1 / 2) f) :=
  theorem1 cubicOriginalData (by norm_num) (by norm_num)

theorem actual_disjoint_tori : result.tori.Pairwise Disjoint := result.pairwise_disjoint

theorem actual_torus_realization (T : Set (RealPhaseSpace 1)) (hT : T ∈ result.tori) :
    Nonempty (KAMTorus 1 cubic perturbation.toFun ambient result.width (1 / 2) T) :=
  result.realization T hT

theorem actual_good_nonempty : result.goodSet.Nonempty := result.good_nonempty

theorem actual_large_measure : ENNReal.ofReal (1 / 2 : ℝ) *
    volume (realSlice ambient ×ˢ (univ : Set (RealTorus 1))) < volume result.goodSet := by
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using result.good_large

theorem actual_bad_measure : volume result.badSet < ENNReal.ofReal (1 / 2 : ℝ) *
    volume (realSlice ambient ×ˢ (univ : Set (RealTorus 1))) := result.bad_small

end KamProject.Arnold1963.Audit.W10Example
