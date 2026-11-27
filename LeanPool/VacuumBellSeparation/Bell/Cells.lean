/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Defs
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Outcome effects, cell probabilities and correlators

For a self-adjoint contraction `A` the binary measurement has outcome effects `(1 ± A)/2`.
For commuting algebras the products of outcome effects are positive, so a state assigns
them probabilities (`cellProb`), and the correlator `ω (A * B)` is the signed sum of the
four cell probabilities.
-/

@[expose] public section

open scoped ComplexOrder

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Product of commuting positive operators -/

/-- The product of two commuting positive operators is positive. -/
theorem isPositive_mul_of_commute {E P : H →L[ℂ] H} (hE : E.IsPositive) (hP : P.IsPositive)
    (h : E * P = P * E) : (E * P).IsPositive := by
  have hE' : (0 : H →L[ℂ] H) ≤ E := ContinuousLinearMap.nonneg_iff_isPositive.mpr hE
  have hP' : (0 : H →L[ℂ] H) ≤ P := ContinuousLinearMap.nonneg_iff_isPositive.mpr hP
  have hc : Commute E P := h
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (Commute.mul_nonneg hE' hP' hc)

/-! ### Linearity of states -/

theorem state_add (ω : State H) (S T : H →L[ℂ] H) : ω (S + T) = ω S + ω T :=
  map_add ω.toLinearMap S T

theorem state_sub (ω : State H) (S T : H →L[ℂ] H) : ω (S - T) = ω S - ω T :=
  map_sub ω.toLinearMap S T

theorem state_one (ω : State H) : ω (1 : H →L[ℂ] H) = 1 :=
  ω.map_one'

/-- A complex number with vanishing imaginary part is the cast of its real part. -/
theorem ofReal_re_eq_of_im_eq_zero {z : ℂ} (h : z.im = 0) : ((z.re : ℝ) : ℂ) = z :=
  Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, h])

/-! ### Positivity of `1 ± A` for a self-adjoint contraction -/

theorem isPositive_one_add_of_saContraction {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A)
    (hn : ‖A‖ ≤ 1) : (1 + A).IsPositive := by
  have h1sa : IsSelfAdjoint (1 : H →L[ℂ] H) := by
    first | exact IsSelfAdjoint.one _
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨h1sa.add hsa, fun x => ?_⟩
  change 0 ≤ RCLike.re (inner ℂ ((1 + A) x) x)
  have h1 : ‖A x‖ ≤ ‖x‖ :=
    calc ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have h2 : |RCLike.re (inner ℂ (A x) x)| ≤ ‖x‖ * ‖x‖ :=
    calc |RCLike.re (inner ℂ (A x) x)| ≤ ‖inner ℂ (A x) x‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖A x‖ * ‖x‖ := norm_inner_le_norm ..
      _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
  have key : RCLike.re (inner ℂ ((1 + A) x) x)
      = ‖x‖ * ‖x‖ + RCLike.re (inner ℂ (A x) x) := by
    first
      | rw [add_apply, one_apply_eq_self, inner_add_left,
          map_add, inner_self_eq_norm_mul_norm]
  rw [key]
  have h3 := (abs_le.mp h2).1
  linarith

theorem isPositive_one_sub_of_saContraction {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A)
    (hn : ‖A‖ ≤ 1) : (1 - A).IsPositive := by
  have h := isPositive_one_add_of_saContraction hsa.neg (by rwa [norm_neg])
  rwa [← sub_eq_add_neg] at h

theorem half_nonneg_complex : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
  first
    | exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩

/-- Von Neumann algebras are closed under complex scalar multiplication. -/
theorem smul_mem_vonNeumann (M : VonNeumannAlgebra H) (c : ℂ) {x : H →L[ℂ] H} (hx : x ∈ M) :
    c • x ∈ M := by
  first
    | exact (show c • x ∈ M.toStarSubalgebra from M.toStarSubalgebra.smul_mem hx c)

/-! ### Outcome effects -/

/-- outcome `true` ↦ `(1 + A)/2`, outcome `false` ↦ `(1 - A)/2`. -/
noncomputable def outcomeEffect (A : H →L[ℂ] H) (α : Bool) : H →L[ℂ] H :=
  if α then (1 / 2 : ℂ) • (1 + A) else (1 / 2 : ℂ) • (1 - A)

omit [CompleteSpace H] in
theorem outcomeEffect_true (A : H →L[ℂ] H) :
    outcomeEffect A true = (1 / 2 : ℂ) • (1 + A) := by
  first | rfl

omit [CompleteSpace H] in
theorem outcomeEffect_false (A : H →L[ℂ] H) :
    outcomeEffect A false = (1 / 2 : ℂ) • (1 - A) := by
  first | rfl

omit [CompleteSpace H] in
theorem outcomeEffect_true_add_false (A : H →L[ℂ] H) :
    outcomeEffect A true + outcomeEffect A false = 1 := by
  rw [outcomeEffect_true, outcomeEffect_false]
  have h2 : (1 + A) + (1 - A) = (2 : ℂ) • (1 : H →L[ℂ] H) := by
    rw [two_smul]; abel
  first
    | module


omit [CompleteSpace H] in
theorem outcomeEffect_true_sub_false (A : H →L[ℂ] H) :
    outcomeEffect A true - outcomeEffect A false = A := by
  rw [outcomeEffect_true, outcomeEffect_false]
  have h2 : (1 + A) - (1 - A) = (2 : ℂ) • A := by
    rw [two_smul]; abel
  first
    | module


theorem outcomeEffect_isPositive {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1)
    (α : Bool) : (outcomeEffect A α).IsPositive := by
  cases α with
  | false =>
    rw [outcomeEffect_false]
    exact (isPositive_one_sub_of_saContraction hsa hn).smul_of_nonneg half_nonneg_complex
  | true =>
    rw [outcomeEffect_true]
    exact (isPositive_one_add_of_saContraction hsa hn).smul_of_nonneg half_nonneg_complex

theorem outcomeEffect_mem_effects {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ saContractions M) (α : Bool) : outcomeEffect A α ∈ effects M := by
  have hA' : A ∈ M ∧ IsSelfAdjoint A ∧ ‖A‖ ≤ 1 := hA
  obtain ⟨hAM, hsa, hn⟩ := hA'
  change outcomeEffect A α ∈ M ∧ (outcomeEffect A α).IsPositive ∧
    (1 - outcomeEffect A α).IsPositive
  refine ⟨?_, outcomeEffect_isPositive hsa hn α, ?_⟩
  · cases α with
    | false =>
      rw [outcomeEffect_false]
      exact smul_mem_vonNeumann M _ (sub_mem (one_mem M) hAM)
    | true =>
      rw [outcomeEffect_true]
      exact smul_mem_vonNeumann M _ (add_mem (one_mem M) hAM)
  · cases α with
    | false =>
      have h : 1 - outcomeEffect A false = outcomeEffect A true := by
        rw [← outcomeEffect_true_add_false A]; abel
      rw [h]
      exact outcomeEffect_isPositive hsa hn true
    | true =>
      have h : 1 - outcomeEffect A true = outcomeEffect A false := by
        rw [← outcomeEffect_true_add_false A]; abel
      rw [h]
      exact outcomeEffect_isPositive hsa hn false

/-- For commuting algebras, the product of outcome effects is positive. -/
theorem outcomeEffect_mul_isPositive {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions 𝔄) (hB : B ∈ saContractions 𝔅) (α β : Bool) :
    (outcomeEffect A α * outcomeEffect B β).IsPositive := by
  have hE : outcomeEffect A α ∈ 𝔄 ∧ (outcomeEffect A α).IsPositive ∧
      (1 - outcomeEffect A α).IsPositive := outcomeEffect_mem_effects hA α
  have hP : outcomeEffect B β ∈ 𝔅 ∧ (outcomeEffect B β).IsPositive ∧
      (1 - outcomeEffect B β).IsPositive := outcomeEffect_mem_effects hB β
  exact isPositive_mul_of_commute hE.2.1 hP.2.1 (hcomm _ hE.1 _ hP.1)

/-! ### Cell and outcome probabilities -/

/-- joint probability of outcomes α (for A) and β (for B) -/
noncomputable def cellProb (ω : State H) (A B : H →L[ℂ] H) (α β : Bool) : ℝ :=
  (ω (outcomeEffect A α * outcomeEffect B β)).re

/-- probability of outcome α for A -/
noncomputable def outcomeProb (ω : State H) (A : H →L[ℂ] H) (α : Bool) : ℝ :=
  (ω (outcomeEffect A α)).re

theorem cellProb_nonneg (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions 𝔄) (hB : B ∈ saContractions 𝔅) (α β : Bool) :
    0 ≤ cellProb ω A B α β :=
  (ω.map_nonneg' _ (outcomeEffect_mul_isPositive hcomm hA hB α β)).2

theorem ofReal_cellProb (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions 𝔄) (hB : B ∈ saContractions 𝔅) (α β : Bool) :
    ((cellProb ω A B α β : ℝ) : ℂ) = ω (outcomeEffect A α * outcomeEffect B β) :=
  ofReal_re_eq_of_im_eq_zero
    (ω.map_nonneg' _ (outcomeEffect_mul_isPositive hcomm hA hB α β)).1

theorem ofReal_outcomeProb (ω : State H) {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ saContractions M) (α : Bool) :
    ((outcomeProb ω A α : ℝ) : ℂ) = ω (outcomeEffect A α) := by
  have hE : outcomeEffect A α ∈ M ∧ (outcomeEffect A α).IsPositive ∧
      (1 - outcomeEffect A α).IsPositive := outcomeEffect_mem_effects hA α
  exact ofReal_re_eq_of_im_eq_zero (ω.map_nonneg' _ hE.2.1).1

theorem outcomeProb_nonneg (ω : State H) {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ saContractions M) (α : Bool) : 0 ≤ outcomeProb ω A α := by
  have hE : outcomeEffect A α ∈ M ∧ (outcomeEffect A α).IsPositive ∧
      (1 - outcomeEffect A α).IsPositive := outcomeEffect_mem_effects hA α
  exact (ω.map_nonneg' _ hE.2.1).2

theorem cellProb_add_right (ω : State H) (A B : H →L[ℂ] H) (α : Bool) :
    cellProb ω A B α true + cellProb ω A B α false = outcomeProb ω A α := by
  unfold cellProb outcomeProb
  rw [← Complex.add_re, ← state_add, ← mul_add, outcomeEffect_true_add_false, mul_one]

theorem cellProb_add_left (ω : State H) (A B : H →L[ℂ] H) (β : Bool) :
    cellProb ω A B true β + cellProb ω A B false β = outcomeProb ω B β := by
  unfold cellProb outcomeProb
  rw [← Complex.add_re, ← state_add, ← add_mul, outcomeEffect_true_add_false, one_mul]

theorem outcomeProb_true_add_false (ω : State H) (A : H →L[ℂ] H) :
    outcomeProb ω A true + outcomeProb ω A false = 1 := by
  unfold outcomeProb
  rw [← Complex.add_re, ← state_add, outcomeEffect_true_add_false, state_one, Complex.one_re]

/-! ### Correlators as real numbers -/

omit [CompleteSpace H] in
theorem mul_eq_outcomeEffect_cells (A B : H →L[ℂ] H) :
    A * B = outcomeEffect A true * outcomeEffect B true
      + outcomeEffect A false * outcomeEffect B false
      - outcomeEffect A true * outcomeEffect B false
      - outcomeEffect A false * outcomeEffect B true :=
  calc A * B = (outcomeEffect A true - outcomeEffect A false)
        * (outcomeEffect B true - outcomeEffect B false) := by
        rw [outcomeEffect_true_sub_false, outcomeEffect_true_sub_false]
    _ = _ := by
        first
          | noncomm_ring

theorem state_mul_eq_cells (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {A B : H →L[ℂ] H} (hA : A ∈ saContractions 𝔄) (hB : B ∈ saContractions 𝔅) :
    ω (A * B) = ((cellProb ω A B true true + cellProb ω A B false false
      - cellProb ω A B true false - cellProb ω A B false true : ℝ) : ℂ) := by
  rw [Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_add,
    ofReal_cellProb ω hcomm hA hB true true, ofReal_cellProb ω hcomm hA hB false false,
    ofReal_cellProb ω hcomm hA hB true false, ofReal_cellProb ω hcomm hA hB false true,
    ← state_add, ← state_sub, ← state_sub, ← mul_eq_outcomeEffect_cells]

theorem state_eq_outcomes (ω : State H) {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ saContractions M) :
    ω A = ((outcomeProb ω A true - outcomeProb ω A false : ℝ) : ℂ) := by
  rw [Complex.ofReal_sub, ofReal_outcomeProb ω hA true, ofReal_outcomeProb ω hA false,
    ← state_sub, outcomeEffect_true_sub_false]

end VacuumBellSeparation
