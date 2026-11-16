/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoFormulaDecomp
public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoQuadVarRiemann
public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoMartingaleRiemann
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFormulaScalar

/-!
# Itô's formula for a vector Itô process on a uniform grid

The grid decomposition leaves four errors: the second-order Taylor remainder, one drift Riemann
sum per state index, one martingale Riemann sum per state-and-Brownian index pair, and one
weighted quadratic variation per pair of state indices. Under an affine oscillation bound
`A + K‖z − w‖` on the second derivative each is bounded by a function of the mesh whose limit is
proportional to `A`; a uniformly continuous second derivative supplies such a bound for every
`A > 0`, so the `L¹` defect of Itô's formula vanishes.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoGridError` — the mesh-error function.
* `LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError` — it vanishes as the mesh does.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le` — the `L¹`
  defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula` — Itô's formula in the vector case.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

/-- The residue of the uniform-grid error that the oscillation scale `A` of the second derivative
leaves behind as the mesh vanishes, per unit of `A`. -/
noncomputable def vectorItoGridResidue (nR dR C T : ℝ) : ℝ :=
  nR * (2 * (dR ^ 2 * (C ^ 2 * T))) + 1 / 2 * (nR ^ 2 * (dR * C ^ 2 * T))

theorem vectorItoGridResidue_nonneg {nR dR C T : ℝ} (hnR : 0 ≤ nR) (hdR : 0 ≤ dR)
    (hT : 0 ≤ T) : 0 ≤ vectorItoGridResidue nR dR C T := by
  unfold vectorItoGridResidue
  positivity

/-- The `L¹` error of the uniform-grid approximation in Itô's formula for a vector Itô process,
as a function of the mesh. The four summands are the Taylor remainder, the drift Riemann sums,
the martingale Riemann sums and the weighted quadratic variations; `A` and `K` are the two
constants of the affine oscillation bound `A + K‖z − w‖` on the second derivative. -/
noncomputable def vectorItoGridError (nR dR B C T A K K₂ : ℝ) (x : ℝ) : ℝ :=
  (A * (nR * (2 * (B ^ 2 * (T * x)) + 2 * (dR ^ 2 * (C ^ 2 * T))))
      + K * (nR ^ 2 * (nR * (4 * (B ^ 3 * T * x ^ 2
        + dR ^ 2 * (dR * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt x))))))))
    + nR * (K₂ * B * (T * (nR * (B * x + dR * (C * Real.sqrt x)))))
    + nR * dR * Real.sqrt (C ^ 2 * (K₂ ^ 2
        * (T * (nR * (2 * (B * x) ^ 2 + 2 * (dR ^ 2 * (C ^ 2 * x)))))))
    + 1 / 2 * (nR ^ 2 * (K₂ * B ^ 2 * T * x
        + 2 * (K₂ * B * dR * C * T * Real.sqrt x)
        + dR * Real.sqrt (K₂ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * x))
        + dR ^ 2 * Real.sqrt (K₂ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T * x))
        + (A * (dR * C ^ 2) * T
          + K * (dR * C ^ 2) * (T * (nR * (B * x + dR * (C * Real.sqrt x)))))))

@[simp] theorem vectorItoGridError_zero (nR dR B C T A K K₂ : ℝ) :
    vectorItoGridError nR dR B C T A K K₂ 0 = A * vectorItoGridResidue nR dR C T := by
  simp only [vectorItoGridError, vectorItoGridResidue]
  norm_num
  ring

theorem continuous_vectorItoGridError (nR dR B C T A K K₂ : ℝ) :
    Continuous (vectorItoGridError nR dR B C T A K K₂) := by
  unfold vectorItoGridError
  fun_prop

theorem tendsto_vectorItoGridError (nR dR B C T A K K₂ : ℝ) :
    Filter.Tendsto (fun m : ℕ => vectorItoGridError nR dR B C T A K K₂ (T / (m : ℝ)))
      Filter.atTop (𝓝 (A * vectorItoGridResidue nR dR C T)) := by
  have hx : Filter.Tendsto (fun m : ℕ => T / (m : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hcomp := ((continuous_vectorItoGridError nR dR B C T A K K₂).tendsto 0).comp hx
  rwa [vectorItoGridError_zero] at hcomp

section Formula

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
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in
/-- **The `L¹` defect of Itô's formula for a vector Itô process on a uniform grid.** -/
theorem IsVectorItoVersion.integral_abs_vectorItoFormula_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hf''c : Continuous f'')
    (hf''aff : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ vectorItoGridError (n : ℝ) (d : ℝ) B C T A K K₂ (T / (m : ℝ)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hf'c : Continuous f' := hf'd.continuous
  have hdecomp := h.vectorItoFormula_decomp_ae (f := f) (f'' := f'') hbm hB hmg hpg hqg hT hm0
  -- (1) the Taylor remainder, transferred to the version
  obtain ⟨hZ1int0, hZ1le0⟩ := integral_abs_vectorTaylorRemainder_le_affine W ℱ hcoord H hHm hHp
    hHs hC0 hCH X₀ hX₀ bdrift hbm hB0 hB hA0 hK0 hf hf' hf''c hf''aff hT hm0
  have hRae : (fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => X (unifGrid T m i) ω) m)
      =ᵐ[P] fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m := by
    filter_upwards [h.ae_eq_all (unifGrid T m) fun i => unifGrid_nonneg hT.le m i] with ω hω
    have hfun : (fun i => X (unifGrid T m i) ω)
        = fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω :=
      funext hω
    rw [hfun]
  have e1 : (m : ℝ) * (B * (T / (m : ℝ))) ^ 3 = B ^ 3 * T * (T / (m : ℝ)) ^ 2 := by field_simp
  rw [e1] at hZ1le0
  have hZ1int : Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
      (fun i => X (unifGrid T m i) ω) m) P := hZ1int0.congr hRae.symm
  have hZ1le := le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hRae.fun_comp abs))) hZ1le0
  -- (2) the drift Riemann sums
  have hZ2 := fun p : Fin n =>
    h.integral_abs_frozenRiemann_sub_le hC0 hCH hbm hB0 hB (bdrift p) (hbm p) hB0 (hB p)
      (continuous_coordDeriv hf'c p) (abs_coordDeriv_le hf'bd p) le_rfl hK₂0
      (fun x y => by simpa using abs_coordDeriv_sub_le hf' hf''bd p x y) hT hm0
  -- (3) the martingale Riemann sums
  have hZ3 : ∀ (p : Fin n) (k : Fin d),
      Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
              - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω) P
        ∧ ∫ ω, |(∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
              * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω| ∂P
          ≤ Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
              + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))) := by
    intro p k
    have hfin : ∀ ω : Ω,
        (∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
              - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
          = ∑ i : Fin m, coordDeriv f' p (X (unifGrid T m (i : ℕ)) ω)
            * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
                  (hHs p k) (unifGrid T m ((i : ℕ) + 1)) ω
              - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
                  (hHs p k) (unifGrid T m (i : ℕ)) ω) := fun ω =>
      (Fin.sum_univ_eq_sum_range (fun i => coordDeriv f' p (X (unifGrid T m i) ω)
        * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (unifGrid T m i) ω)) m).symm
    have hmeas : Measurable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
              - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω) := by
      refine Measurable.sub (Finset.measurable_sum _ fun i _ =>
        (((continuous_coordDeriv hf'c p).measurable.comp
            (h.measurable (unifGrid T m i))).mul
          ((measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k _).sub
            (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k _)))) ?_
      exact ((stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) _ (hmg p k)
        (hpg p k) (hqg p k) T).mono (ℱ.le T)).measurable
    have hV0 : (0 : ℝ) ≤ C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by positivity
    refine integral_abs_le_sqrt_of_lintegral_sq_le hmeas.aestronglyMeasurable hV0 ?_
    have hsq := h.lintegral_sq_martingaleRiemann_sub_le hC0 hCH hbm hB0 hB
      (abs_coordDeriv_le hf'bd p) hK₂0 (abs_coordDeriv_sub_le hf' hf''bd p) k
      (hHm p k) (hHp p k) (hHs p k) hC0 (hCH p k) (hmg p k) (hpg p k) (hqg p k) hT hm0
    simp only [hfin]
    refine hsq.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  -- (4) the weighted quadratic variations
  have hZ4 := fun p q : Fin n =>
    h.integral_abs_quadVarRiemann_sub_le hC0 hCH hbm hB0 hB p q (hma p q) (hpa p q) (hqa p q)
      (continuous_coordDeriv₂ hf''c p q) hK₂0 (abs_coordDeriv₂_le hf''bd p q) hA0 hK0
      (abs_coordDeriv₂_sub_le_affine hf''aff p q) hT hm0
  have e2 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2) = K₂ * B ^ 2 * T * (T / (m : ℝ)) := by
    field_simp
  have e3 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
      = K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ)) := by
    field_simp
  have e4 : T ^ 2 / (m : ℝ) = T * (T / (m : ℝ)) := by
    field_simp
  simp only [e2, e3, e4] at hZ4
  -- assemble the four families
  have hZ2int : Integrable (fun ω : Ω => ∑ p : Fin n,
      ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        - ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)) P :=
    MeasureTheory.integrable_finsetSum _ fun p _ => (hZ2 p).1
  have hZ2le : ∫ ω, |∑ p : Fin n,
        ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)| ∂P
      ≤ (n : ℝ) * (0 * B * T + K₂ * B * (T * ((n : ℝ) * (B * (T / (m : ℝ))
        + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
    refine (integral_abs_finsetSum_le _ _ (fun p _ => (hZ2 p).1) _ (fun p _ => (hZ2 p).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ3int : Integrable (fun ω : Ω => ∑ p : Fin n, ∑ k : Fin d,
      ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
          * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)) P :=
    MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun k _ => (hZ3 p k).1
  have hZ3le : ∫ ω, |∑ p : Fin n, ∑ k : Fin d,
        ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
            * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
              - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
          - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)| ∂P
      ≤ (n : ℝ) * ((d : ℝ) * Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ)
        * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))))) := by
    refine (integral_abs_finsetSum_le _ _
      (fun p _ => MeasureTheory.integrable_finsetSum _ fun k _ => (hZ3 p k).1)
      (fun _ => (d : ℝ) * Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ)
        * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))))
      (fun p _ => ?_)).trans ?_
    · refine (integral_abs_finsetSum_le _ _ (fun k _ => (hZ3 p k).1) _
        (fun k _ => (hZ3 p k).2)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ4int : Integrable (fun ω : Ω => 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
      ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P :=
    (MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun q _ => (hZ4 p q).1).const_mul _
  have hZ4le : ∫ ω, |1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
        ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
            * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
              * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
          - ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
      ≤ 1 / 2 * ((n : ℝ) * ((n : ℝ) * (K₂ * B ^ 2 * T * (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + (d : ℝ) * Real.sqrt (K₂ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * (T / (m : ℝ))))
        + (d : ℝ) ^ 2 * Real.sqrt (K₂ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T * (T / (m : ℝ))))
        + (A * ((d : ℝ) * C ^ 2) * T
          + K * ((d : ℝ) * C ^ 2) * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))))) := by
    have habs : ∀ ω : Ω, |1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
          ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
              * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
                * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
            - ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)|
        = 1 / 2 * |∑ p : Fin n, ∑ q : Fin n,
          ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
              * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
                * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
            - ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
      intro ω
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp_rw [habs]
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (integral_abs_finsetSum_le _ _
      (fun p _ => MeasureTheory.integrable_finsetSum _ fun q _ => (hZ4 p q).1)
      (fun _ => (n : ℝ) * (K₂ * B ^ 2 * T * (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + (d : ℝ) * Real.sqrt (K₂ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * (T / (m : ℝ))))
        + (d : ℝ) ^ 2 * Real.sqrt (K₂ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T * (T / (m : ℝ))))
        + (A * ((d : ℝ) * C ^ 2) * T
          + K * ((d : ℝ) * C ^ 2) * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))))
      (fun p _ => ?_)).trans ?_
    · refine (integral_abs_finsetSum_le _ _ (fun q _ => (hZ4 p q).1) _
        (fun q _ => (hZ4 p q).2)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨(((hZ1int.add hZ2int).add hZ3int).add hZ4int).congr hdecomp.symm, ?_⟩
  refine le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hdecomp.fun_comp abs))) ?_
  refine le_trans (integral_abs_add_four_le hZ1int hZ2int hZ3int hZ4int hZ1le hZ2le hZ3le hZ4le)
    (le_of_eq ?_)
  unfold vectorItoGridError
  ring

include hC0 hCH in
/-- **Itô's formula for a vector Itô process.** For a continuous adapted version `X` of
`X₀ + ∫ b ds + ∑ₖ ∫ H^{·,k} dWᵏ` with bounded coefficients, and `f` twice Fréchet differentiable
with bounded derivatives and uniformly continuous second derivative,

  `f(X_T) − f(X_0) = ∑_p ∫_0^T ∂_p f(X_s) b^p_s ds + ∑_{p,k} ∫_0^T ∂_p f(X_s) H^{p,k}_s dWᵏ_s
      + ½ ∑_{p,q} ∫_0^T ∂²_{pq} f(X_s) (∑ₖ H^{p,k}_s H^{q,k}_s) ds`

almost surely. -/
theorem IsVectorItoVersion.itoFormula
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  have haff : ∀ ε : ℝ, 0 < ε →
      ∃ Kε : ℝ, 0 ≤ Kε ∧ ∀ z w, ‖f'' z - f'' w‖ ≤ ε + Kε * ‖z - w‖ := by
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := hf''unif ε hε
    refine ⟨2 * K₂ / δ, by positivity, fun z w => ?_⟩
    have hnn : (0 : ℝ) ≤ 2 * K₂ / δ * ‖z - w‖ := by positivity
    rcases lt_or_ge ‖z - w‖ δ with hlt | hge
    · have hle : ‖f'' z - f'' w‖ ≤ ε := hδ z w hlt
      linarith
    · have h1 : ‖f'' z - f'' w‖ ≤ 2 * K₂ := by
        refine (norm_sub_le (f'' z) (f'' w)).trans ?_
        linarith [hf''bd z, hf''bd w]
      have h2 : 2 * K₂ / δ * δ ≤ 2 * K₂ / δ * ‖z - w‖ :=
        mul_le_mul_of_nonneg_left hge (by positivity)
      rw [div_mul_cancel₀ _ (ne_of_gt hδ0)] at h2
      linarith
  obtain ⟨K₁ε, hK₁ε0, haff1⟩ := haff 1 one_pos
  obtain ⟨hZint, -⟩ := h.integral_abs_vectorItoFormula_le hC0 hCH hX₀ hbm hB0 hB hma hpa hqa
    hf hf' hf'bd hK₂0 hf''bd zero_le_one hK₁ε0 hf''c haff1 hmg hpg hqg hT one_ne_zero
  have hkey : ∀ ε : ℝ, 0 < ε →
      ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ ε * vectorItoGridResidue (n : ℝ) (d : ℝ) C T := by
    intro ε hε
    obtain ⟨Kε, hKε0, haffε⟩ := haff ε hε
    have hgrid := fun (m : ℕ) (hm0 : m ≠ 0) =>
      h.integral_abs_vectorItoFormula_le hC0 hCH hX₀ hbm hB0 hB hma hpa hqa hf hf' hf'bd
        hK₂0 hf''bd hε.le hKε0 hf''c haffε hmg hpg hqg hT hm0
    exact ge_of_tendsto (tendsto_vectorItoGridError (n : ℝ) (d : ℝ) B C T ε Kε K₂)
      ((Filter.eventually_gt_atTop 0).mono fun m hmpos => (hgrid m hmpos.ne').2)
  have htend : Filter.Tendsto
      (fun j : ℕ => (1 / ((j : ℝ) + 1)) * vectorItoGridResidue (n : ℝ) (d : ℝ) C T)
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul_const (vectorItoGridResidue (n : ℝ) (d : ℝ) C T)
  have hzero := ge_of_tendsto htend (Filter.Eventually.of_forall fun j : ℕ =>
    hkey (1 / ((j : ℝ) + 1)) (by positivity))
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun ω => abs_nonneg _) hZint.abs).mp
    (le_antisymm hzero (MeasureTheory.integral_nonneg fun ω => abs_nonneg _))
  filter_upwards [hae] with ω hω
  have hz := abs_eq_zero.mp hω
  linarith

end Formula

end LevyStochCalc.Brownian.Ito
