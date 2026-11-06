/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Lemma `lem:ineqs`: tail transfer for a maximum

Source lines 2426–2437. Let `H_i` be integer valued and let `N_i, L_i` be nonnegative random
variables with `{H_i ≥ h_i} = {N_i ≥ 1}` and `{L_i ≥ 1} ⊆ {H_i ≥ h_i}`. If `E[N_i] → 0` then
`P(H_i ≥ h_i) → 0`; if `L_i → ∞` in probability then `P(H_i ≥ h_i) → 1`.

The index runs along an arbitrary filter, and each `i` carries its own probability space (the
laws `𝒯^n` of the paper). Expectations are `lintegral`s in `ℝ≥0∞`, so that a statement
`E[N_i] → 0` cannot be satisfied by a junk value of an infinite expectation. "`L_i → ∞` in
probability" means `P(L_i ≤ K) → 0` for every `K`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace PoissonDeclumping

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {P : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)]

omit [∀ i, IsProbabilityMeasure (P i)] in
/-- First half of Lemma `lem:ineqs`: if the expected witness count `N_i(h_i)` vanishes, the
upper-tail probability `P(H_i ≥ h_i)` vanishes (Markov's inequality). -/
theorem tendsto_zero_of_tendsto_lintegral_zero (l : Filter ι)
    (H : ∀ i, Ω i → ℤ) (N : ∀ i, Ω i → ℝ) (h : ι → ℤ)
    (hN : ∀ i, Measurable (N i))
    (hHN : ∀ i ω, h i ≤ H i ω ↔ 1 ≤ N i ω)
    (hE : Tendsto (fun i => ∫⁻ ω, ENNReal.ofReal (N i ω) ∂P i) l (𝓝 0)) :
    Tendsto (fun i => (P i).real {ω | h i ≤ H i ω}) l (𝓝 0) := by
  have key : ∀ i, (P i) {ω | h i ≤ H i ω} ≤ ∫⁻ ω, ENNReal.ofReal (N i ω) ∂P i := by
    intro i
    have hset : {ω | h i ≤ H i ω} = {ω | (1 : ℝ≥0∞) ≤ ENNReal.ofReal (N i ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hHN, ENNReal.one_le_ofReal]
    rw [hset]
    have := meas_ge_le_lintegral_div (μ := P i) (f := fun ω => ENNReal.ofReal (N i ω))
      (hN i).ennreal_ofReal.aemeasurable (ε := 1) one_ne_zero ENNReal.one_ne_top
    simpa using this
  have h1 : Tendsto (fun i => (P i) {ω | h i ≤ H i ω}) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
      (fun _ => bot_le) key
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1

/-- Second half of Lemma `lem:ineqs`: if the lower witness count `L_i(h_i)` tends to infinity in
probability (here: `P(L_i < 1) → 0` suffices, which follows from `P(L_i ≤ K) → 0` for any
`K ≥ 1`), then `P(H_i ≥ h_i) → 1`. -/
theorem tendsto_one_of_witness (l : Filter ι)
    (H : ∀ i, Ω i → ℤ) (L : ∀ i, Ω i → ℝ) (h : ι → ℤ)
    (hL : ∀ i, Measurable (L i))
    (hLH : ∀ i ω, 1 ≤ L i ω → h i ≤ H i ω)
    (hinf : ∀ K : ℝ, Tendsto (fun i => (P i).real {ω | L i ω ≤ K}) l (𝓝 0)) :
    Tendsto (fun i => (P i).real {ω | h i ≤ H i ω}) l (𝓝 1) := by
  have hlow : ∀ i, 1 - (P i).real {ω | L i ω ≤ 1} ≤ (P i).real {ω | h i ≤ H i ω} := by
    intro i
    have hsub : {ω | 1 < L i ω} ⊆ {ω | h i ≤ H i ω} := fun ω hω => hLH i ω hω.le
    have hc : {ω | 1 < L i ω} = {ω | L i ω ≤ 1}ᶜ := by
      ext ω; simp
    have hm : MeasurableSet {ω | L i ω ≤ 1} := measurableSet_le (hL i) measurable_const
    calc 1 - (P i).real {ω | L i ω ≤ 1} = (P i).real {ω | 1 < L i ω} := by
          rw [hc, probReal_compl_eq_one_sub hm]
      _ ≤ _ := measureReal_mono hsub
  have hup : ∀ i, (P i).real {ω | h i ≤ H i ω} ≤ 1 := fun i => measureReal_le_one
  have hlim : Tendsto (fun i => 1 - (P i).real {ω | L i ω ≤ 1}) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hinf 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

end PoissonDeclumping
