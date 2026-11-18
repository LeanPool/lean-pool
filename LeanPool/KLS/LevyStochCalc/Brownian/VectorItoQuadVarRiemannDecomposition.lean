/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds

/-!
# Decomposition and convergence of the quadratic-variation Riemann sum

The product of the increments of two coordinates of a continuous vector Itô process splits into a
drift–drift term, two drift–martingale terms and the product of the increments of the martingale
parts, and the last splits further into the compensated products on the diagonal in the Brownian
index, their compensators, and the cross terms off that diagonal. Weighting the products by a
bounded continuous function of the process frozen at the left endpoint of each cell of a uniform
grid, the five error terms are `O(m^{-1/2})` in `L¹` and the sixth group is a frozen-weight
Riemann sum for `∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`, so the weighted Riemann sum converges
in `L¹` to that integral at rate `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.prod_sub_ae` — the product of the increments of
  two coordinates.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae` — the decomposition of
  the weighted product sum into six groups.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le` — the `L¹`
  rate of convergence of the weighted quadratic-variation Riemann sum.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

/-- The product of the increments of two coordinates splits into a drift–drift term, two
drift–martingale terms and the product of the martingale parts. -/
theorem IsVectorItoVersion.prod_sub_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ᵐ ω ∂P, (X v ω p - X u ω p) * (X v ω q - X u ω q)
      = (∫ s in Set.Ioc u v, bdrift p ω s ∂volume)
          * (∫ s in Set.Ioc u v, bdrift q ω s ∂volume)
        + (∫ s in Set.Ioc u v, bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
        + (∫ s in Set.Ioc u v, bdrift q ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω) := by
  filter_upwards [h.sub_ae hbm hB hu huv p, h.sub_ae hbm hB hu huv q] with ω e1 e2
  rw [e1, e2]
  ring

include hC0 hCH in
/-- The product of the martingale parts' increments splits into the compensated products on the
diagonal in the Brownian index, their compensators, and the cross terms off that diagonal. -/
theorem vectorItoMartingale_prod_eq (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
      * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
        + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
  have hcomp : ∀ k : Fin d,
      (∫ s in Set.Icc (0 : ℝ) v, H p k ω s * H q k ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) u, H p k ω s * H q k ω s ∂volume
      = ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
    intro k
    refine setIntegral_Icc_sub_Icc (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) hu huv
    change |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have key : ∀ k : Fin d,
      (∑ l : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω))
      = polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
        + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
    intro k
    have hcross : ∀ l : Fin d,
        (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
          * (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω)
        = crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l u v ω := fun l => rfl
    simp only [hcross]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    have hdiag : crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q k) (hHp q k)
          (hHs q k) k k u v ω
        = polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
      simp only [crossIncrement, polarQuadVarIncrement]
      rw [← hcomp k]
      ring
    rw [hdiag]
  calc (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω))
          * ∑ l : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := by
        rw [vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs p u v,
          vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs q u v]
    _ = ∑ k : Fin d, ∑ l : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := Finset.sum_mul_sum _ _ _ _
    _ = ∑ k : Fin d, (polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ l ∈ Finset.univ.erase k,
              crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω) := Finset.sum_congr rfl fun k _ => key k
    _ = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
          + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
              crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

include hC0 hCH in
/-- **The weighted product sum decomposes into six groups.** -/
theorem IsVectorItoVersion.quadVarRiemann_decomp_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (φ : (Fin n → ℝ) → ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∀ᵐ ω ∂P, (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
      = (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω)))
        + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
            φ (X (unifGrid T m i) ω)
              * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : ℕ =>
    h.prod_sub_ae hbm hB p q (unifGrid_nonneg hT.le m i)
      (unifGrid_lt_succ hT hm0 i).le] with ω hω
  have hswap : ∀ i : ℕ, (∑ k : Fin d, ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        H p k ω s * H q k ω s ∂volume)
      = ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
          ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
    intro i
    refine (MeasureTheory.integral_finsetSum _ fun k _ => ?_).symm
    refine integrableOn_of_bounded_of_measurable (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) (measure_Ioc_lt_top).ne
    change |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have hterm : ∀ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
        * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q))
      = φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
        + φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))
        + φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω))
        + (∑ k : Fin d, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, φ (X (unifGrid T m i) ω)
            * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + φ (X (unifGrid T m i) ω)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
    intro i _
    rw [hω i, vectorItoMartingale_prod_eq hC0 hCH p q (unifGrid_nonneg hT.le m i)
      (unifGrid_lt_succ hT hm0 i).le ω, ← hswap i]
    simp only [mul_add, Finset.mul_sum]
    ring
  have hcomm1 : (∑ i ∈ Finset.range m, ∑ k : Fin d, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω)
      = ∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω := Finset.sum_comm
  have hcomm2 : (∑ i ∈ Finset.range m, ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
        φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
      = ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
          φ (X (unifGrid T m i) ω)
            * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm1, hcomm2]

include hC0 hCH in
/-- **The weighted quadratic-variation Riemann sum converges in `L¹` at rate `√(T/m)`.** The
product of the increments of two coordinates, weighted by a bounded Lipschitz `φ(X)`, approximates
`∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`; the six groups of the decomposition contribute the six
summands of the bound. -/
theorem IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (hma : ∀ k : Fin d, Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (d : ℝ) * Real.sqrt (Kφ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
        + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        + (Mφ * ((d : ℝ) * C ^ 2) * T
          + L * ((d : ℝ) * C ^ 2)
            * (T * ((n : ℝ) * (B * (T / (m : ℝ))
              + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
  classical
  -- the weight of the frozen Riemann sum
  have hwm : Measurable (Function.uncurry fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) :=
    Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hA0 : (0 : ℝ) ≤ (d : ℝ) * C ^ 2 := by positivity
  have hA : ∀ (ω : Ω) (s : ℝ), |∑ k : Fin d, H p k ω s * H q k ω s| ≤ (d : ℝ) * C ^ 2 := by
    intro ω s
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin d)), |H p k ω s * H q k ω s| ≤ C ^ 2 := by
      intro k _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the six groups
  obtain ⟨i1, b1⟩ := h.integral_abs_sum_drift_sq_le hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i2, b2⟩ := h.integral_abs_sum_driftCross_le hC0 hCH hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i3, b3⟩ := h.integral_abs_sum_driftCross_le hC0 hCH hbm hB0 hB q p hφc hKφ0 hφbd hT hm0
  have hpol : ∀ k : Fin d, Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := fun k =>
    h.integral_abs_sum_polarQuadVar_le hC0 hCH p q k (hma k) (hpa k) (hqa k) hφc hKφ0 hφbd hT hm0
  have hcr : ∀ (k : Fin d), ∀ l ∈ Finset.univ.erase k,
      Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
        ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
          ≤ Real.sqrt (Kφ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T ^ 2 / (m : ℝ))) := fun k l hl =>
    h.integral_abs_sum_offDiagCross_le hC0 hCH p q ((Finset.mem_erase.mp hl).1.symm)
      hφc hKφ0 hφbd hT hm0
  obtain ⟨i6, b6⟩ := h.integral_abs_frozenRiemann_sub_le hC0 hCH hbm hB0 hB
    (fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) hwm hA0 hA hφc hφbd hMφ0 hL0 hφaff hT hm0
  -- integrability of the grouped sums
  have i4 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ i ∈ Finset.range m,
      φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ => (hpol k).1
  have i5 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
      ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ =>
      MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1
  -- the bounds on the two grouped sums
  have b4 : ∫ ω, |∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
        * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ))) := by
    refine (integral_abs_finsetSum_le _ _ (fun k _ => (hpol k).1) _
      (fun k _ => (hpol k).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have b5 : ∫ ω, |∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
        * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Kφ ^ 2
        * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) :=
      Real.sqrt_nonneg _
    refine (integral_abs_finsetSum_le _ _
      (fun k _ => MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1)
      (fun k => ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
        * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))))
      (fun k _ => integral_abs_finsetSum_le _ _ (fun l hl => (hcr k l hl).1) _
        (fun l hl => (hcr k l hl).2))).trans ?_
    have hk : ∀ k : Fin d, ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
          * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
          * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
      intro k
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun l _ _ => hsqrt0)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_rfl
  -- assemble
  have hae : (fun ω : Ω => |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
          * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
      - ∫ s in Set.Ioc (0 : ℝ) T,
          φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume|)
      =ᵐ[P] fun ω => |((((∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume))
            + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
                  - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))))
            + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume)
                * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
                  - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω))))
            + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                  (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                  (unifGrid T m i) (unifGrid T m (i + 1)) ω))
            + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
              φ (X (unifGrid T m i) ω)
                * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                    (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                  ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T,
                φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
    filter_upwards [h.quadVarRiemann_decomp_ae hC0 hCH hbm hB p q φ hT hm0] with ω hω
    rw [hω]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · refine (((((i1.add i2).add i3).add i4).add i5).add i6).congr ?_
    filter_upwards [h.quadVarRiemann_decomp_ae hC0 hCH hbm hB p q φ hT hm0] with ω hω
    simp only [Pi.add_apply]
    rw [hω]
    ring
  rw [MeasureTheory.integral_congr_ae hae]
  exact integral_abs_add_le ((((i1.add i2).add i3).add i4).add i5) i6
    (integral_abs_add_le (((i1.add i2).add i3).add i4) i5
      (integral_abs_add_le ((i1.add i2).add i3) i4
        (integral_abs_add_le (i1.add i2) i3 (integral_abs_add_le i1 i2 b1 b2) b3) b4) b5) b6

end VectorQuadVar

end LevyStochCalc.Brownian.Ito
