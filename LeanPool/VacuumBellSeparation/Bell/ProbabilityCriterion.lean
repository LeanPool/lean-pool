/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Cells
public import LeanPool.VacuumBellSeparation.Probability.CellChain

/-!
# The probability criterion for the classical CHSH bound

This file assembles the operator-algebraic part of Theorem 3.1 (`thm:probability`) of the
manuscript from the real-number box lemma `chsh_box_le_one` and the cell lemmas of
`VacuumBellSeparation.Bell.Cells`.

## Main results

* `chshValue_le_one_of_event_bounds` : for a state `ω` on two commuting von Neumann algebras,
  if the two event bounds hold on sets `SA`, `SB` of operators containing the outcome
  effects `(1 ± Aᵢ)/2`, `(1 ± Bⱼ)/2` of a quartet of self-adjoint contractions, and the
  clustering bound and the cutoff inequality (3.5) hold, then the CHSH value of the quartet
  is at most `1`.
* `bellCorrelation_eq_one_of_effect_bounds` : the **effect form** of Theorem 3.1: if the
  event bounds hold for all pairs of local *effects*, then `β(ω; 𝔄, 𝔅) = 1`.

## Relation to the manuscript

This module proves the criterion for local effects, with the event bounds assumed for all pairs of
local effects, as (8.9)–(8.10) give them. The manuscript states and applies Theorem 3.1 in its
projection form (event bounds for local *projections*, through the constants `K_{r,±}` of (3.1),
bounded in (8.11)); that form is `probability_criterion` in `VacuumBellSeparation.Bell.Theorem31`,
which the main proof applies (`freeFieldBell_unit_eq_one`, `FreeField/MainReduction.lean`).

The event bounds are stated with real constants `Kp`, `Km` in denominator-free form:
`ω(EP)^{r₊} ≤ Kp (ω(E)ω(P))^{r₊-1}` and `(ω(E)ω(P))^{r₋} ≤ Km ω(EP)^{r₋-1}`.
-/

@[expose] public section

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The negative of a self-adjoint contraction is a self-adjoint contraction. -/
theorem neg_mem_saContractions {M : VonNeumannAlgebra H} {A : H →L[ℂ] H}
    (hA : A ∈ saContractions M) : -A ∈ saContractions M :=
  ⟨neg_mem hA.1, hA.2.1.neg, by rw [norm_neg]; exact hA.2.2⟩

/-- The identity is a self-adjoint contraction of every von Neumann algebra. -/
theorem one_mem_saContractions (M : VonNeumannAlgebra H) :
    (1 : H →L[ℂ] H) ∈ saContractions M :=
  ⟨one_mem M, by simp,
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)⟩

/-- The identity is an effect of every von Neumann algebra. -/
theorem one_mem_effects (M : VonNeumannAlgebra H) : (1 : H →L[ℂ] H) ∈ effects M :=
  ⟨one_mem M, ContinuousLinearMap.isPositive_one, by
    rw [sub_self]; exact ContinuousLinearMap.isPositive_zero⟩

/-- Core step: for two families `A, B : Bool → B(H)` of local self-adjoint contractions
(settings `false`, `true`), the expectation of the CHSH operator in the state `ω` is a real
number `s`
with `s / 2 ≤ 1`, provided the event bounds hold on sets containing all outcome effects. -/
theorem chsh_family_le
    (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {rp rm Kp Km q : ℝ} (hrp : 1 < rp) (hrm : 1 < rm) (hη : 0 < expEta rp rm)
    (hKp : 0 < Kp) (hKm : 0 < Km) (SA SB : Set (H →L[ℂ] H))
    (hup : ∀ E ∈ SA, ∀ P ∈ SB,
      (ω (E * P)).re ^ rp ≤ Kp * ((ω E).re * (ω P).re) ^ (rp - 1))
    (hlow : ∀ E ∈ SA, ∀ P ∈ SB,
      ((ω E).re * (ω P).re) ^ rm ≤ Km * (ω (E * P)).re ^ (rm - 1))
    (hcl : ∀ A ∈ saContractions 𝔄, ∀ B ∈ saContractions 𝔅,
      ‖ω (A * B) - ω A * ω B‖ ≤ q)
    (hcut : q ^ expEta rp rm * Kp ^ nuPlus rp rm * Km ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp))))
    (A B : Bool → H →L[ℂ] H)
    (hA : ∀ i, A i ∈ saContractions 𝔄) (hB : ∀ j, B j ∈ saContractions 𝔅)
    (hSA : ∀ i α, outcomeEffect (A i) α ∈ SA) (hSB : ∀ j β, outcomeEffect (B j) β ∈ SB) :
    ∃ s : ℝ, ω (chshOp (A false) (A true) (B false) (B true)) = (s : ℂ) ∧
      (1 / 2 : ℝ) * s ≤ 1 := by
  have hcorr : ∀ i j, ω (A i * B j) =
      ((boxCorr (fun i j α β => cellProb ω (A i) (B j) α β) i j : ℝ) : ℂ) :=
    fun i j => state_mul_eq_cells ω hcomm (hA i) (hB j)
  have key : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hbox := chsh_box_le_one hrp hrm hη hKp hKm
    (fun i j α β => cellProb ω (A i) (B j) α β)
    (fun i α => outcomeProb ω (A i) α) (fun j β => outcomeProb ω (B j) β)
    (fun i j α β => cellProb_nonneg ω hcomm (hA i) (hB j) α β)
    (fun i j α => cellProb_add_right ω (A i) (B j) α)
    (fun i j β => cellProb_add_left ω (A i) (B j) β)
    (fun i => outcomeProb_true_add_false ω (A i))
    (fun i j α β => hup _ (hSA i α) _ (hSB j β))
    (fun i j α β => hlow _ (hSA i α) _ (hSB j β))
    (fun i j => by
      have h := hcl _ (hA i) _ (hB j)
      rw [hcorr i j, state_eq_outcomes ω (hA i), state_eq_outcomes ω (hB j),
        ← Complex.ofReal_mul, ← Complex.ofReal_sub, key] at h
      exact h)
    hcut
  refine ⟨_, ?_, hbox⟩
  have hop : chshOp (A false) (A true) (B false) (B true)
      = A false * B false + A false * B true + A true * B false - A true * B true := by
    unfold chshOp
    rw [mul_add, mul_sub]
    abel
  rw [hop, map_sub, map_add, map_add, hcorr, hcorr, hcorr, hcorr]
  simp only [Complex.ofReal_sub, Complex.ofReal_add]

/-- If the event bounds hold on sets `SA`, `SB` containing the outcome effects of the
quartet `(±A₀, ±A₁, B₀, B₁)`, then its CHSH value is at most `1`. -/
theorem chshValue_le_one_of_event_bounds
    (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {rp rm Kp Km q : ℝ} (hrp : 1 < rp) (hrm : 1 < rm) (hη : 0 < expEta rp rm)
    (hKp : 0 < Kp) (hKm : 0 < Km) (SA SB : Set (H →L[ℂ] H))
    (hup : ∀ E ∈ SA, ∀ P ∈ SB,
      (ω (E * P)).re ^ rp ≤ Kp * ((ω E).re * (ω P).re) ^ (rp - 1))
    (hlow : ∀ E ∈ SA, ∀ P ∈ SB,
      ((ω E).re * (ω P).re) ^ rm ≤ Km * (ω (E * P)).re ^ (rm - 1))
    (hcl : ∀ A ∈ saContractions 𝔄, ∀ B ∈ saContractions 𝔅,
      ‖ω (A * B) - ω A * ω B‖ ≤ q)
    (hcut : q ^ expEta rp rm * Kp ^ nuPlus rp rm * Km ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp))))
    {A₀ A₁ B₀ B₁ : H →L[ℂ] H}
    (hA₀ : A₀ ∈ saContractions 𝔄) (hA₁ : A₁ ∈ saContractions 𝔄)
    (hB₀ : B₀ ∈ saContractions 𝔅) (hB₁ : B₁ ∈ saContractions 𝔅)
    (hSA : ∀ α, outcomeEffect A₀ α ∈ SA ∧ outcomeEffect A₁ α ∈ SA ∧
      outcomeEffect (-A₀) α ∈ SA ∧ outcomeEffect (-A₁) α ∈ SA)
    (hSB : ∀ β, outcomeEffect B₀ β ∈ SB ∧ outcomeEffect B₁ β ∈ SB) :
    (1 / 2 : ℝ) * ‖ω (chshOp A₀ A₁ B₀ B₁)‖ ≤ 1 := by
  have hB : ∀ j : Bool, cond j B₁ B₀ ∈ saContractions 𝔅 := by
    intro j
    cases j
    · exact hB₀
    · exact hB₁
  have hSB' : ∀ (j : Bool) (β : Bool), outcomeEffect (cond j B₁ B₀) β ∈ SB := by
    intro j β
    cases j
    · exact (hSB β).1
    · exact (hSB β).2
  have hA : ∀ i : Bool, cond i A₁ A₀ ∈ saContractions 𝔄 := by
    intro i
    cases i
    · exact hA₀
    · exact hA₁
  have hSA' : ∀ (i : Bool) (α : Bool), outcomeEffect (cond i A₁ A₀) α ∈ SA := by
    intro i α
    cases i
    · exact (hSA α).1
    · exact (hSA α).2.1
  have hAn : ∀ i : Bool, cond i (-A₁) (-A₀) ∈ saContractions 𝔄 := by
    intro i
    cases i
    · exact neg_mem_saContractions hA₀
    · exact neg_mem_saContractions hA₁
  have hSAn : ∀ (i : Bool) (α : Bool), outcomeEffect (cond i (-A₁) (-A₀)) α ∈ SA := by
    intro i α
    cases i
    · exact (hSA α).2.2.1
    · exact (hSA α).2.2.2
  obtain ⟨s, hs, hs1⟩ : ∃ s : ℝ, ω (chshOp A₀ A₁ B₀ B₁) = (s : ℂ) ∧ (1 / 2 : ℝ) * s ≤ 1 :=
    chsh_family_le ω hcomm hrp hrm hη hKp hKm SA SB hup hlow hcl hcut
      (fun i => cond i A₁ A₀) (fun j => cond j B₁ B₀) hA hB hSA' hSB'
  obtain ⟨t, ht, ht1⟩ :
      ∃ t : ℝ, ω (chshOp (-A₀) (-A₁) B₀ B₁) = (t : ℂ) ∧ (1 / 2 : ℝ) * t ≤ 1 :=
    chsh_family_le ω hcomm hrp hrm hη hKp hKm SA SB hup hlow hcl hcut
      (fun i => cond i (-A₁) (-A₀)) (fun j => cond j B₁ B₀) hAn hB hSAn hSB'
  have hneg : chshOp (-A₀) (-A₁) B₀ B₁ = -chshOp A₀ A₁ B₀ B₁ := by
    unfold chshOp
    rw [neg_mul, neg_mul, neg_add]
  rw [hneg, map_neg, hs] at ht
  have hts : t = -s := by
    have h := congrArg Complex.re ht
    simpa using h.symm
  rw [hs, Complex.norm_real, Real.norm_eq_abs]
  have habs : |s| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **Theorem 3.1, effect form.**  Let `ω` be a state and `𝔄`, `𝔅` commuting von Neumann
algebras.  Let `r₊ > 2`, `1 < r₋ < 2` with `η > 0`.  Suppose that for all effects `E ∈ 𝔄`,
`P ∈ 𝔅` the event bounds `ω(EP)^{r₊} ≤ K₊ (ω(E)ω(P))^{r₊-1}` and
`(ω(E)ω(P))^{r₋} ≤ K₋ ω(EP)^{r₋-1}` hold, that `|ω(AB) - ω(A)ω(B)| ≤ q` for all local
self-adjoint contractions, and that `q^η K₊^{ν₊} K₋^{ν₋} ≤ 2^{-2/(ab)}`.  Then the
Summers–Werner Bell correlation equals `1`. -/
theorem bellCorrelation_eq_one_of_effect_bounds
    (ω : State H) {𝔄 𝔅 : VonNeumannAlgebra H} (hcomm : Commuting 𝔄 𝔅)
    {rp rm Kp Km q : ℝ} (hrp : 2 < rp) (hrm : 1 < rm) (_hrm2 : rm < 2)
    (hη : 0 < expEta rp rm)
    (hup : ∀ E ∈ effects 𝔄, ∀ P ∈ effects 𝔅,
      (ω (E * P)).re ^ rp ≤ Kp * ((ω E).re * (ω P).re) ^ (rp - 1))
    (hlow : ∀ E ∈ effects 𝔄, ∀ P ∈ effects 𝔅,
      ((ω E).re * (ω P).re) ^ rm ≤ Km * (ω (E * P)).re ^ (rm - 1))
    (hcl : ∀ A ∈ saContractions 𝔄, ∀ B ∈ saContractions 𝔅,
      ‖ω (A * B) - ω A * ω B‖ ≤ q)
    (hcut : q ^ expEta rp rm * Kp ^ nuPlus rp rm * Km ^ nuMinus rm
        ≤ (2 : ℝ) ^ (-(2 / (expA rm * expB rp)))) :
    bellCorrelation ω 𝔄 𝔅 = 1 := by
  have hKp : (1 : ℝ) ≤ Kp := by
    simpa [ω.map_one'] using hup 1 (one_mem_effects 𝔄) 1 (one_mem_effects 𝔅)
  have hKm : (1 : ℝ) ≤ Km := by
    simpa [ω.map_one'] using hlow 1 (one_mem_effects 𝔄) 1 (one_mem_effects 𝔅)
  have hle : ∀ x ∈ chshValues ω 𝔄 𝔅, x ≤ 1 := by
    rintro x ⟨A₀, hA₀, A₁, hA₁, B₀, hB₀, B₁, hB₁, rfl⟩
    exact chshValue_le_one_of_event_bounds ω hcomm (by linarith) hrm hη (by linarith)
      (by linarith) (effects 𝔄) (effects 𝔅) hup hlow hcl hcut hA₀ hA₁ hB₀ hB₁
      (fun α => ⟨outcomeEffect_mem_effects hA₀ α, outcomeEffect_mem_effects hA₁ α,
        outcomeEffect_mem_effects (neg_mem_saContractions hA₀) α,
        outcomeEffect_mem_effects (neg_mem_saContractions hA₁) α⟩)
      (fun β => ⟨outcomeEffect_mem_effects hB₀ β, outcomeEffect_mem_effects hB₁ β⟩)
  have hone : (1 : ℝ) ∈ chshValues ω 𝔄 𝔅 := by
    refine ⟨1, one_mem_saContractions 𝔄, 1, one_mem_saContractions 𝔄,
      1, one_mem_saContractions 𝔅, 1, one_mem_saContractions 𝔅, ?_⟩
    have h2 : chshOp (1 : H →L[ℂ] H) 1 1 1 = (2 : ℂ) • (1 : H →L[ℂ] H) := by
      unfold chshOp
      rw [sub_self, mul_zero, add_zero, one_mul, two_smul]
    have h3 : ω (chshOp (1 : H →L[ℂ] H) 1 1 1) = ((2 : ℝ) : ℂ) := by
      rw [h2, map_smul, ω.map_one']
      simp
    rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_two]
    norm_num
  exact le_antisymm (csSup_le ⟨1, hone⟩ hle) (le_csSup ⟨1, hle⟩ hone)

end VacuumBellSeparation
