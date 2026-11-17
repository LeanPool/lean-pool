/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoVersionExists
public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoProcessVersion

/-!
# Existence of a continuous adapted version of a vector Itô process

Each entry of the diffusion matrix contributes an Itô integral against its own Brownian
coordinate, and each of those has a continuous adapted modification. Summing them over the
Brownian index and adding the initial value and the drift's window integral gives a continuous
adapted version of the vector Itô process.

## Main statements

* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion` — a continuous adapted version exists.
* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_aug` — the same over the augmented
  filtration, with no side conditions.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Exists

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
  (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
  (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in
/-- **A continuous adapted version of a vector Itô process exists** when the filtration is
constant before time `0` and contains the measurable null sets. -/
theorem exists_isVectorItoVersion
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by
  classical
  choose Y hYcont hYadapt hYmod using fun (p : Fin n) (k : Fin d) =>
    exists_continuousAdapted_modification (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
      (hHs p k) hC0 (hCH p k) hℱ0 hnull
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  refine ⟨fun t ω p => X₀ ω p + (∫ s in Set.Icc (0 : ℝ) t, bdrift p ω s ∂volume)
      + ∑ k : Fin d, Y p k t ω, ?_, ?_, ?_⟩
  · intro ω
    refine continuous_pi fun p => (continuous_const.add
      (continuous_setIntegral_Icc (Measurable.of_uncurry_left (hbm p)) hB0 (hB p ω))).add ?_
    exact continuous_finsetSum _ fun k _ => hYcont p k ω
  · intro t
    have hcoordm : ∀ p : Fin n, Measurable[ℱ t] fun ω =>
        X₀ ω p + (∫ s in Set.Icc (0 : ℝ) t, bdrift p ω s ∂volume) + ∑ k : Fin d, Y p k t ω := by
      intro p
      refine Measurable.add (Measurable.add (fun A hA => hle0 t _ (hX₀ p hA)) ?_)
        (Finset.measurable_sum _ fun k _ => hYadapt p k t)
      exact (((hbp p).stronglyMeasurable_setIntegral measurableSet_Icc
        Set.Icc_subset_Iic_self volume).mono le_rfl).measurable
    refine Measurable.stronglyMeasurable ?_
    let : MeasurableSpace Ω := ℱ t
    exact Measurable.of_eval hcoordm
  · intro t ht
    have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
        Y p k t ω = coordItoIntegral W ℱ hcoord H hHm hHp hHs p k t ω :=
      MeasureTheory.ae_all_iff.mpr fun p =>
        MeasureTheory.ae_all_iff.mpr fun k => hYmod p k t ht
    filter_upwards [hall] with ω hω
    funext p
    simp only [vectorItoProcess, vectorItoMartingale]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hω p k

include hC0 hCH in
/-- **A continuous adapted version of a vector Itô process exists over the augmented
filtration**, with no side conditions on the filtration. -/
theorem exists_isVectorItoVersion_aug
    (Hp : ∀ p k, Probability.ProgressivelyMeasurable (augFiltration ℱ P) (H p k))
    (Hs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable (augFiltration ℱ P) (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ, IsVectorItoVersion W (augFiltration ℱ P)
      (fun k => isBrownianFiltration_augFiltration (hcoord k)) H hHm Hp Hs X₀ bdrift X :=
  exists_isVectorItoVersion W (augFiltration ℱ P)
    (fun k => isBrownianFiltration_augFiltration (hcoord k)) H hHm Hp Hs hC0 hCH
    (fun _ ht => le_of_eq (augFiltration_of_nonpos ℱ P ht).symm)
    (fun _ hs h0 => measurableSet_augFiltration_of_null ℱ P hs h0)
    (fun p _ hA => le_augFiltration ℱ P 0 _ (hX₀ p hA)) bdrift hbm hbp hB0 hB

end Exists

end LevyStochCalc.Brownian.Ito
