/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system (module
-- header, public imports, exposed public section) for Lean/Mathlib v4.35.0; proofs use
-- `continuous_abs.measurable.comp` for the no longer reachable `Measurable.abs`.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoThirdMoment
public import LeanPool.KLS.LevyStochCalc.Brownian.TaylorTwoModulus

/-!
# The Taylor remainder of a vector Itô process along a uniform grid

Expanding a twice-differentiable function of a vector Itô process cell by cell leaves a
second-order Taylor remainder. For a Lipschitz second derivative that remainder is cubic in the
increment, so the third moments of the increments bound it in `L¹`; across a uniform grid of `m`
cells the bound is of order `m^{-1/2}`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed` — the remainder along a
  measurable sequence is measurable.
* `LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le` — the second moments of
  the increments sum to `O(1)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine` — the `L¹` bound under
  an affine oscillation bound on the second derivative.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section RemainderMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The second-order Taylor remainder along a measurable sequence of a function with continuous
first and second derivatives is measurable. -/
theorem measurable_taylorRemainderNormed {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hfc : Continuous f) (hf'c : Continuous f')
    (hf''c : Continuous f'') {x : ℕ → Ω → E} (hx : ∀ i, Measurable (x i)) (m : ℕ) :
    Measurable fun ω => taylorRemainderNormed f f' f'' (fun i => x i ω) m := by
  have hfirst : ∀ i : ℕ, Measurable fun ω => f' (x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f' p.1 (p.2 - p.1) :=
      (hf'c.comp continuous_fst).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  have hsecond : ∀ i : ℕ,
      Measurable fun ω => f'' (x i ω) (x (i + 1) ω - x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f'' p.1 (p.2 - p.1) (p.2 - p.1) :=
      ((hf''c.comp continuous_fst).clm_apply
        (continuous_snd.sub continuous_fst)).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  unfold taylorRemainderNormed
  exact ((hfc.measurable.comp (hx m)).sub (hfc.measurable.comp (hx 0))).sub
    ((Finset.measurable_sum _ fun i _ => hfirst i).add
      (Finset.measurable_sum _ fun i _ => (hsecond i).div_const 2))

end RemainderMeasurable

section VectorTaylor

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- **The second moments of a vector Itô process's increments along a uniform grid sum to
`O(1)`.** -/
theorem sum_integral_sq_norm_vectorItoIncrement_le (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
      ≤ (n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  have hterm : ∀ i ∈ Finset.range m, ∫ ω,
      ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
      ≤ (n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))) := by
    intro i _
    have hle := (integral_sq_norm_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs
      hC0 hCH X₀ bdrift hbm hB0 hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)).2
    rwa [unifGrid_succ_sub hm0 i] at hle
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsplit : (m : ℝ) * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))
      = (n : ℝ) * (2 * (B ^ 2 * (((m : ℝ) * (T / (m : ℝ))) * (T / (m : ℝ))))
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * ((m : ℝ) * (T / (m : ℝ)))))) := by ring
  rw [hsplit, hTm]

include hC0 hCH in
/-- **The second-order Taylor remainder of a vector Itô process along a uniform grid under an
affine oscillation bound on the second derivative.** -/
theorem integral_abs_vectorTaylorRemainder_le_affine (X₀ : Ω → Fin n → ℝ)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A)
    (hK0 : 0 ≤ K) (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf''c : Continuous f'') (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainderNormed f f' f''
          (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by
  have hX : ∀ i : ℕ,
      Measurable (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i)) :=
    fun i => measurable_vectorItoProcess W ℱ hcoord H hHm hHp hHs hX₀ hbm _
  have hfd : Differentiable ℝ f := fun z => (hf z).differentiableAt
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hR := measurable_taylorRemainderNormed hfd.continuous hf'd.continuous hf''c hX m
  have hptw : ∀ ω : Ω, |taylorRemainderNormed f f' f''
      (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m|
      ≤ A * ∑ i ∈ Finset.range m,
          ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
            - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2
        + K * ∑ i ∈ Finset.range m,
          ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
            - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 :=
    fun ω => abs_taylorRemainderNormed_le_affine hA0 hK0 hf hf' hf'' _ m
  have hsq : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2) P :=
    fun i _ => (integral_sq_norm_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)).1
  have hcu : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3) P :=
    fun i _ => integrable_norm_vectorItoProcess_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
  have hsumint : Integrable (fun ω : Ω =>
      A * ∑ i ∈ Finset.range m,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2
      + K * ∑ i ∈ Finset.range m,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3) P :=
    ((MeasureTheory.integrable_finsetSum _ hsq).const_mul A).add
      ((MeasureTheory.integrable_finsetSum _ hcu).const_mul K)
  have hRint : Integrable (fun ω : Ω => |taylorRemainderNormed f f' f''
      (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m|) P := by
    refine hsumint.mono (continuous_abs.measurable.comp hR).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hptw ω).trans (le_abs_self _)
  have hRint0 : Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
      (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P := by
    refine hsumint.mono hR.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hptw ω).trans (le_abs_self _)
  refine ⟨hRint0, ?_⟩
  calc ∫ ω, |taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
      ≤ ∫ ω, (A * ∑ i ∈ Finset.range m,
            ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
              - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2
          + K * ∑ i ∈ Finset.range m,
            ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
              - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3) ∂P :=
        MeasureTheory.integral_mono hRint hsumint hptw
    _ = A * ∑ i ∈ Finset.range m, ∫ ω,
            ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
              - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 2 ∂P
          + K * ∑ i ∈ Finset.range m, ∫ ω,
            ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
              - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 ∂P := by
        rw [MeasureTheory.integral_add ((MeasureTheory.integrable_finsetSum _ hsq).const_mul A)
          ((MeasureTheory.integrable_finsetSum _ hcu).const_mul K),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ hsq, MeasureTheory.integral_finsetSum _ hcu]
    _ ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by
        gcongr
        · exact sum_integral_sq_norm_vectorItoIncrement_le W ℱ hcoord H hHm hHp hHs hC0 hCH
            X₀ bdrift hbm hB0 hB hT hm0
        · exact sum_integral_norm_vectorItoIncrement_pow_three_le W ℱ hcoord H hHm hHp hHs
            hC0 hCH X₀ bdrift hbm hB0 hB hT hm0

end VectorTaylor

end LevyStochCalc.Brownian.Ito
