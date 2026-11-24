/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicLimits
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LogLevi
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A genuine logarithmic pole

The extended-real logarithm takes the value negative infinity at the origin.
Its disc plurisubharmonicity follows from the checked smooth regularizations
and the checked decreasing-limit theorem, including discs through the pole.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E]

/-- The squared-norm logarithm, with its actual negative-infinite pole. -/
def logNormSq (x : E) : EReal := ENNReal.log (ENNReal.ofReal (‖x‖ ^ 2))

@[simp] theorem logNormSq_zero : logNormSq (0 : E) = ⊥ := by
  simp [logNormSq]

@[simp] theorem logNormSq_eq_bot_iff (x : E) : logNormSq x = ⊥ ↔ x = 0 := by
  simp only [logNormSq, ENNReal.log_eq_bot_iff, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have : ‖x‖ = 0 := by nlinarith [sq_nonneg ‖x‖]
    exact norm_eq_zero.mp this
  · rintro rfl
    simp

theorem logNormSq_ne_top (x : E) : logNormSq x ≠ ⊤ := by
  simp [logNormSq]

theorem logNormSq_of_ne_zero {x : E} (hx : x ≠ 0) :
    logNormSq x = (Real.log (‖x‖ ^ 2) : EReal) :=
  ENNReal.log_ofReal_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- Continuity here is in the order topology of the extended real line. -/
theorem continuous_logNormSq : Continuous (logNormSq (E := E)) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp (continuous_norm.pow 2))

theorem tendsto_regularizedLogNormSq {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (x : E) :
    Tendsto (fun n => (regularizedLogNormSq (ε n) x : EReal))
      atTop (𝓝 (logNormSq x)) := by
  have h : Tendsto (fun n => ENNReal.log (ENNReal.ofReal (‖x‖ ^ 2 + ε n)))
      atTop (𝓝 (ENNReal.log (ENNReal.ofReal (‖x‖ ^ 2 + 0)))) :=
    ENNReal.continuous_log.continuousAt.tendsto.comp
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.add hlim))
  have heq (n : ℕ) : ENNReal.log (ENNReal.ofReal (‖x‖ ^ 2 + ε n)) =
      (regularizedLogNormSq (ε n) x : EReal) :=
    ENNReal.log_ofReal_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (hε n))
  simpa only [Function.comp_def, add_zero, heq, logNormSq] using h

theorem antitone_regularizedLogNormSq {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hanti : Antitone ε) (x : E) :
    Antitone (fun n => (regularizedLogNormSq (ε n) x : EReal)) := by
  intro m n hmn
  change (Real.log (‖x‖ ^ 2 + ε n) : EReal) ≤ Real.log (‖x‖ ^ 2 + ε m)
  rw [← ENNReal.log_ofReal_of_pos
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (hε n)),
    ← ENNReal.log_ofReal_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (hε m))]
  exact ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (by linarith [hanti hmn]))

/-- Any positive decreasing regularization tending to zero has this exact
pointwise infimum, including at the negative-infinite pole. -/
theorem iInf_regularizedLogNormSq {ε : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hanti : Antitone ε)
    (hlim : Tendsto ε atTop (𝓝 0)) (x : E) :
    (⨅ n, (regularizedLogNormSq (ε n) x : EReal)) = logNormSq x :=
  tendsto_nhds_unique
    (tendsto_atTop_iInf (antitone_regularizedLogNormSq hε hanti x))
    (tendsto_regularizedLogNormSq hε hlim x)

section ComplexInnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The logarithmic pole satisfies the disc criterion on every subset of a
complex inner product space. In particular this includes discs through zero. -/
theorem discPshOn_logNormSq (U : Set H) : DiscPshOn logNormSq U := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hanti : Antitone ε := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (m : ℝ) + 1)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hi := DiscPshOn.iInf_of_antitone
    (fun n => discPshOn_regularizedLogNormSq (hε n) U)
    (fun y _ => antitone_regularizedLogNormSq hε hanti y)
  simpa only [iInf_regularizedLogNormSq hε hanti hlim] using hi

theorem plurisubharmonicAt_logNormSq (x : H) : PlurisubharmonicAt logNormSq x :=
  (discPshOn_logNormSq univ).plurisubharmonicOn isOpen_univ x (mem_univ x)

end ComplexInnerProduct

end SGPT.Foundations.Analysis
