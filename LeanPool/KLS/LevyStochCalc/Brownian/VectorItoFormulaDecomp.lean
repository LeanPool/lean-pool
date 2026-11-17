/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoTaylor
public import LeanPool.KLS.LevyStochCalc.Brownian.CoordDerivative
public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoProcessVersion

/-!
# The grid decomposition behind Itô's formula in the vector case

Expanding `f(X_T) − f(X_0)` cell by cell along a uniform grid leaves the second-order Taylor
remainder together with three Riemann sums — one for each of the drift, the stochastic and the
quadratic-variation integrals. In coordinates the first-order term splits over the state index
and the Brownian index, and the second-order term over a pair of state indices.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_apply_fderiv_eq` — the first-order Taylor sum in coordinates.
* `LevyStochCalc.Brownian.Ito.sum_apply_fderiv₂_eq` — the second-order Taylor sum in coordinates.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae` — the defect of
  Itô's formula as the remainder plus the three families of Riemann-sum errors.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Reindex

variable {n d : ℕ}

/-- Reordering a triple sum whose summand splits into a scalar and a sum over a second index. -/
theorem sum_range_add_sum_comm (m : ℕ) (A : Fin n → ℕ → ℝ) (Bc : Fin n → Fin d → ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ p : Fin n, (A p i + ∑ k : Fin d, Bc p k i)
      = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
        + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m, Bc p k i := by
  calc ∑ i ∈ Finset.range m, ∑ p : Fin n, (A p i + ∑ k : Fin d, Bc p k i)
      = ∑ i ∈ Finset.range m,
          ((∑ p : Fin n, A p i) + ∑ p : Fin n, ∑ k : Fin d, Bc p k i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = (∑ i ∈ Finset.range m, ∑ p : Fin n, A p i)
          + ∑ i ∈ Finset.range m, ∑ p : Fin n, ∑ k : Fin d, Bc p k i :=
        Finset.sum_add_distrib
    _ = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
          + ∑ p : Fin n, ∑ i ∈ Finset.range m, ∑ k : Fin d, Bc p k i := by
        congr 1 <;> exact Finset.sum_comm
    _ = (∑ p : Fin n, ∑ i ∈ Finset.range m, A p i)
          + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m, Bc p k i := by
        congr 1
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- Reordering a triple sum over two state indices and the grid. -/
theorem sum_range_sum_sum_comm (m : ℕ) (E : Fin n → Fin n → ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ p : Fin n, ∑ q : Fin n, E p q i
      = ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m, E p q i := by
  calc ∑ i ∈ Finset.range m, ∑ p : Fin n, ∑ q : Fin n, E p q i
      = ∑ p : Fin n, ∑ i ∈ Finset.range m, ∑ q : Fin n, E p q i := Finset.sum_comm
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m, E p q i :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- A doubly indexed difference of sums. -/
theorem sum_sub_sum_two {ι κ : Type*} [Fintype ι] [Fintype κ] (A Bc : ι → κ → ℝ) :
    ∑ i : ι, ∑ j : κ, (A i j - Bc i j)
      = (∑ i : ι, ∑ j : κ, A i j) - ∑ i : ι, ∑ j : κ, Bc i j := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_sub_distrib]

end Reindex

section TaylorSums

variable {n : ℕ}

/-- The second-order Taylor sum along a sequence, in coordinates. -/
theorem sum_apply_fderiv₂_eq (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (Y : ℕ → Fin n → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, f'' (Y i) (Y (i + 1) - Y i) (Y (i + 1) - Y i) / 2
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m,
          coordDeriv₂ f'' p q (Y i) * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q)) := by
  have hstep : ∀ i ∈ Finset.range m,
      f'' (Y i) (Y (i + 1) - Y i) (Y (i + 1) - Y i) / 2
        = (∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p q (Y i)
              * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q))) / 2 := by
    intro i _
    rw [apply₂_eq_sum_coordDeriv₂]
    congr 1
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div,
    sum_range_sum_sum_comm m fun p q i =>
      coordDeriv₂ f'' p q (Y i) * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q))]
  ring

end TaylorSums

section Decomposition

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}

/-- **The first-order Taylor sum in coordinates.** Along a uniform grid the increments of a
version split into their drift and Itô parts, so the sum of `f'(X_{tᵢ})(ΔXᵢ)` splits into one
drift Riemann sum per state index and one martingale Riemann sum per pair of state and Brownian
indices. -/
theorem sum_apply_fderiv_eq
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∀ᵐ ω ∂P, ∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
          (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω)
      = (∑ p : Fin n, ∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        + ∑ p : Fin n, ∑ k : Fin d, ∑ i ∈ Finset.range m,
            coordDeriv f' p (X (unifGrid T m i) ω)
              * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω) := by
  have hsub : ∀ᵐ ω ∂P, ∀ (p : Fin n) (i : ℕ),
      X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p
        = (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω) :=
    MeasureTheory.ae_all_iff.mpr fun p => MeasureTheory.ae_all_iff.mpr fun i =>
      h.sub_ae hbm hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i).le p
  filter_upwards [hsub] with ω hω
  have hcell : ∀ i ∈ Finset.range m,
      f' (X (unifGrid T m i) ω) (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω)
        = ∑ p : Fin n, ((coordDeriv f' p (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            + ∑ k : Fin d, coordDeriv f' p (X (unifGrid T m i) ω)
              * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω)) := by
    intro i _
    rw [apply_eq_sum_coordDeriv]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) p
        = X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p := rfl
    rw [hp, hω p i, vectorItoMartingale_sub, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hcell,
    sum_range_add_sum_comm m
      (fun p i => coordDeriv f' p (X (unifGrid T m i) ω)
        * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
      (fun p k i => coordDeriv f' p (X (unifGrid T m i) ω)
        * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))]

/-- **The grid decomposition of Itô's formula in the vector case.** The defect of the formula on
`[0, T]` equals the second-order Taylor remainder along the uniform grid plus the errors of the
drift, martingale and quadratic-variation Riemann sums. -/
theorem IsVectorItoVersion.vectorItoFormula_decomp_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume))
      =ᵐ[P] fun ω : Ω =>
        taylorRemainderNormed f f' f'' (fun i => X (unifGrid T m i) ω) m
        + (∑ p : Fin n, ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * bdrift p ω s ∂volume))
        + (∑ p : Fin n, ∑ k : Fin d,
            ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
                * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                  - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
              - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                  (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                  (hmg p k) (hpg p k) (hqg p k) T ω))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
                * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
                  * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
              - ∫ s in Set.Ioc (0 : ℝ) T,
                  coordDeriv₂ f'' p q (X s ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) := by
  filter_upwards [sum_apply_fderiv_eq h hbm hB f' hT hm0] with ω hω1
  have hsecond := sum_apply_fderiv₂_eq f'' (fun i => X (unifGrid T m i) ω) m
  have htay : taylorRemainderNormed f f' f'' (fun i => X (unifGrid T m i) ω) m
      = f (X T ω) - f (X 0 ω)
        - ((∑ i ∈ Finset.range m, f' (X (unifGrid T m i) ω)
              (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω))
          + ∑ i ∈ Finset.range m, f'' (X (unifGrid T m i) ω)
              (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω)
              (X (unifGrid T m (i + 1)) ω - X (unifGrid T m i) ω) / 2) := by
    simp only [taylorRemainderNormed, unifGrid_self hm0, unifGrid_zero]
  rw [htay, hω1, hsecond]
  simp only [Finset.sum_sub_distrib]
  ring

end Decomposition

end LevyStochCalc.Brownian.Ito
