/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Defs

/-!
# Tail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Concentration for scale arrays — Step 2 (geometric tail for `Z_j`)

This module formalizes the paper's Step 2 (`e.Zj.tail.twosided`) for a single
column `j`: the combinatorial `⌈n/2⌉`-shells argument, the per-shell Markov bound,
and the union-bound + geometric-series assembly giving

`P[Z_j ≥ n] ≤ C₂ (2/λ)^p 3^{-(sp/2) d_j} 3^{-(sp/4)(n-2)₊}`.

No independence is used here.
-/

namespace Algsuperdiff.Section4.Probability.ScalesConcentration

open MeasureTheory Finset
open scoped ENNReal NNReal

/-- **Combinatorial core of Step 2** (the `⌈n/2⌉`-shells argument).

If `E` is a finite set of integers, each at "shell distance" `≥ d` from `j`, with
at most `2` members per shell, then having `≥ n` members forces some member at
shell distance `≥ d + (n-2)/2` (written `2 d + n ≤ 2·shell + 2`). -/
lemma shell_max {j : ℤ} {d : ℕ} (E : Finset ℤ) (hne : E.Nonempty)
    (hE : ∀ k ∈ E, d ≤ (k - j).natAbs)
    (hfib : ∀ ℓ : ℕ, (E.filter (fun k => (k - j).natAbs = ℓ)).card ≤ 2)
    {n : ℕ} (hn : n ≤ E.card) :
    ∃ k ∈ E, 2 * d + n ≤ 2 * (k - j).natAbs + 2 := by
  classical
  have hcard : E.card ≤ 2 * (E.image (fun k => (k - j).natAbs)).card :=
    Finset.card_le_mul_card_image E 2 (fun b _ => hfib b)
  have hInn : (E.image (fun k => (k - j).natAbs)).Nonempty := hne.image _
  set M : ℕ := (E.image (fun k => (k - j).natAbs)).max' hInn with hM
  obtain ⟨k, hk, hkM⟩ :=
    Finset.mem_image.1 ((E.image (fun k => (k - j).natAbs)).max'_mem hInn)
  refine ⟨k, hk, ?_⟩
  have hdM : d ≤ M := by rw [hM, ← hkM]; exact hE k hk
  have hIsub : E.image (fun k => (k - j).natAbs) ⊆ Finset.Icc d M := by
    intro x hx
    rw [Finset.mem_Icc]
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hx
    exact ⟨hE k' hk', Finset.le_max' _ _ hx⟩
  have hIcard : (E.image (fun k => (k - j).natAbs)).card ≤ M + 1 - d := by
    calc (E.image (fun k => (k - j).natAbs)).card
        ≤ (Finset.Icc d M).card := Finset.card_le_card hIsub
      _ = M + 1 - d := Nat.card_Icc d M
  have hkMv : (k - j).natAbs = M := hkM
  rw [hkMv]
  omega

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **Per-shell Markov bound.**  For a nonnegative variable `Y` with
`∫⁻ ofReal(Y^p) ≤ 1` and `t > 0`, `P[Y > t] ≤ t^{-p}`. -/
lemma column_markov {Y : Ω → ℝ} {p : ℝ} (hYmeas : Measurable Y)
    (hmomL : ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ p) ∂P ≤ 1)
    (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    P {ω | t < Y ω} ≤ ENNReal.ofReal (t ^ (-p)) := by
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((Y ω) ^ p) with hf
  have hfmeas : Measurable f := by
    apply Measurable.ennreal_ofReal
    exact ((Real.continuous_rpow_const hp.le).measurable).comp hYmeas
  have htp : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hεne : ENNReal.ofReal (t ^ p) ≠ 0 := (ENNReal.ofReal_pos.2 htp).ne'
  have hεtop : ENNReal.ofReal (t ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- subset into the Markov super-level set
  have hsub : {ω | t < Y ω} ⊆ {ω | ENNReal.ofReal (t ^ p) ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hf]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht.le hω.le hp.le)
  have hmarkov := mul_meas_ge_le_lintegral₀ (hfmeas.aemeasurable (μ := P))
    (ENNReal.ofReal (t ^ p))
  -- P{level set} ≤ (∫⁻ f)/ofReal(t^p) ≤ 1/ofReal(t^p)
  have h1 : ENNReal.ofReal (t ^ p) * P {ω | ENNReal.ofReal (t ^ p) ≤ f ω} ≤ 1 :=
    le_trans hmarkov hmomL
  have h2 : P {ω | ENNReal.ofReal (t ^ p) ≤ f ω} ≤ 1 / ENNReal.ofReal (t ^ p) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hεne) (Or.inl hεtop), mul_comm]
    exact h1
  calc P {ω | t < Y ω} ≤ P {ω | ENNReal.ofReal (t ^ p) ≤ f ω} := measure_mono hsub
    _ ≤ 1 / ENNReal.ofReal (t ^ p) := h2
    _ = ENNReal.ofReal (t ^ (-p)) := by
        rw [one_div, ← ENNReal.ofReal_inv_of_pos htp, ← Real.rpow_neg ht.le]

end Algsuperdiff.Section4.Probability.ScalesConcentration
