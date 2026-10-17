/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.ScalesConcentration.Statement
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Basic

/-!
# IndicatorArray

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The column-only Appendix-D array and its two probabilistic hypotheses

ABK26, Appendix D (`p.concentration.for.scales`) and §4.1 (the three ratio
lemmas).  Proposition `p.concentration.for.scales` consumes a two-index array
together with two probabilistic hypotheses,

* `hmomL : ∀ k j, ∫⁻ ω.ofReal ((X k j ω) ^ p) ∂P ≤ 1`
  (`e.Xk.p.moment.twosided`),
* `hindep : ColumnsIndep r`  (`e.independent.columns.twosided`).

This module supplies the carrier-neutral machinery that produces both from a
sequence of per-scale atoms with a `Γ_σ` upper tail.

## The array is column-only

In each of the three ratio lemmas the array fed to `p.concentration.for.scales`
is a single sequence of per-scale atoms, constant along the row index: for `𝒢₀`
it is `X_{k,n} = 𝒴_n`, and the row sum is `Y_k = ∑_n 3^{-¼γ|k-n|} 𝒴_n`.  The
two Appendix-D hypotheses then read: unit `p`-th moments of the atoms, and
`r`-dependence of the atom sequence.  `colArray` is that embedding.

## The moment route

A `Γ_σ` upper tail with scale `K` gives `E[Y^p]^{1/p} ≤ gammaMomentConst σ ·
p^{1/σ} · K` (CoarseGraining `lintegral_rpow_le_of_isBigOWith_gammaSigma`);
normalizing the atom by any `D` above that constant delivers the *unit* moment
`∫⁻ (Y/D)^p ≤ 1`.  This is the paper's "by taking `p := exp(K⁻¹c⋆²γ⁻¹)` with
`K(d)` large enough we obtain `E[𝒴ⁿ_p] ≤ 1`".

## Scope

Provider material: carrier-neutral local helpers over an abstract probability
space.  The `Γ_σ` tails, the nonnegativity/measurability of the atoms, and the
residue-class independence enter as conditional A hypotheses; no ABK carrier,
model, or standing assumption is used.  No `sorry`, no custom axioms, no
`set_option maxHeartbeats`.
-/

open MeasureTheory ProbabilityTheory HCPolySupport.IndependentSums
open Algsuperdiff.Section4.Probability.ScalesConcentration
open scoped ENNReal

namespace Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {Ω : Type*}

/-! ### The column-only Appendix-D array -/

/-- **The Appendix-D array of a sequence of per-scale atoms**, `X_{k,j} = Y_j`.
This is the array shape of all three ratio lemmas: the row index only selects
the geometric weight, the randomness lives in the columns. -/
def colArray (Y : ℤ → Ω → ℝ) : ℤ → ℤ → Ω → ℝ := fun _ j ω => Y j ω

@[simp] theorem colArray_apply (Y : ℤ → Ω → ℝ) (k j : ℤ) (ω : Ω) :
    colArray Y k j ω = Y j ω := rfl

theorem Yk_colArray (Y : ℤ → Ω → ℝ) (s : ℝ) (k : ℤ) (ω : Ω) :
    Yk (colArray Y) s k ω = ∑' j : ℤ, wt s k j * Y j ω := rfl

/-- The weighted row sum is homogeneous in the atoms. -/
theorem Yk_colArray_const_mul (Y : ℤ → Ω → ℝ) (c s : ℝ) (k : ℤ) (ω : Ω) :
    Yk (colArray (fun j ω => c * Y j ω)) s k ω = c * Yk (colArray Y) s k ω := by
  simp only [Yk_colArray]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-! ### `hmomL` — unit `p`-th moments from a `Γ_σ` tail

The Appendix-D moment hypothesis in its honest `∫⁻` reading (see the module
docstring of `ScalesConcentration/Statement.lean`). -/

variable [MeasurableSpace Ω]

/-- **Scaling of the weak-Orlicz upper-tail relation.**  `X = O_Ψ(A)` implies
`cX = O_Ψ(cA)` for `c > 0`: the tail events coincide. -/
theorem isBigOWith_const_mul {μ : Measure Ω} {Ψ : ℝ → ℝ} {X : Ω → ℝ} {A c : ℝ}
    (hc : 0 < c) (h : IsBigOWith μ Ψ X A) :
    IsBigOWith μ Ψ (fun ω => c * X ω) (c * A) := by
  intro t ht
  have hset : upperTailEvent (fun ω => c * X ω) (c * A * t) = upperTailEvent X (A * t) := by
    ext ω
    simp only [upperTailEvent, Set.mem_ofPred_eq]
    constructor
    · intro hx
      have : c * (A * t) < c * X ω := by rw [← mul_assoc]; exact hx
      exact lt_of_mul_lt_mul_left this hc.le
    · intro hx
      rw [mul_assoc]
      exact mul_lt_mul_of_pos_left hx hc
  rw [hset]
  exact h ht

/-- **Unit `p`-th moment from a `Γ_σ` tail (the `hmomL` engine).**  A nonnegative
random variable with a stretched-exponential upper tail at scale `K` satisfies the
Appendix-D moment hypothesis `∫⁻ Y^p ≤ 1` as soon as the moment-growth constant
`gammaMomentConst σ · p^{1/σ} · K` is at most `1`.

This is the Lean rendering of the paper's "by taking `p := exp(K⁻¹c⋆²γ⁻¹)` with
`K(d)` large enough, we obtain `E[𝒴ⁿ_p] ≤ 1`". -/
theorem lintegral_rpow_le_one_of_isBigOWith
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ} {σ p K : ℝ}
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p)
    (hYnn : ∀ ω, 0 ≤ Y ω) (hYm : AEMeasurable Y P)
    (hY : IsBigOWith P (gammaSigma σ) Y K)
    (hsmall : gammaMomentConst σ * p ^ σ⁻¹ * K ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ p) ∂P ≤ 1 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hc0 : 0 ≤ gammaMomentConst σ * p ^ σ⁻¹ * K :=
    mul_nonneg (mul_nonneg (gammaMomentConst_pos hσ).le (Real.rpow_nonneg hp0.le _)) hK.le
  refine le_trans (lintegral_rpow_le_of_isBigOWith_gammaSigma hσ hK hp hYnn hYm hY) ?_
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_one hc0 hsmall hp0.le)) ?_
  simp

/-- **`hmomL` for an arbitrary (two-index) Appendix-D array.**  Normalizing
entries with a common `Γ_σ` tail scale `K` by any `D ≥ gammaMomentConst σ · p^{1/σ}·K`
yields the Appendix-D unit-moment hypothesis for `X_{m,k} = D⁻¹ Y_{m,k}`.  Stated at
the two-index shape because not every §4.1 lane has a column-only array; the
column-only case is the instance below. -/
theorem lintegral_rpow_le_one_of_array
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℤ → ℤ → Ω → ℝ} {σ p K D : ℝ}
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p) (hD : 0 < D)
    (hYnn : ∀ m j ω, 0 ≤ Y m j ω) (hYm : ∀ m j, AEMeasurable (Y m j) P)
    (hY : ∀ m j, IsBigOWith P (gammaSigma σ) (Y m j) K)
    (hnorm : gammaMomentConst σ * p ^ σ⁻¹ * K ≤ D) :
    ∀ m j, ∫⁻ ω, ENNReal.ofReal ((D⁻¹ * Y m j ω) ^ p) ∂P ≤ 1 := by
  intro m j
  refine lintegral_rpow_le_one_of_isBigOWith (σ := σ) (K := D⁻¹ * K) hσ
    (mul_pos (inv_pos.2 hD) hK) hp
    (fun ω => mul_nonneg (inv_nonneg.2 hD.le) (hYnn m j ω)) ((hYm m j).const_mul _)
    (isBigOWith_const_mul (inv_pos.2 hD) (hY m j)) ?_
  have hstep : gammaMomentConst σ * p ^ σ⁻¹ * (D⁻¹ * K)
      = D⁻¹ * (gammaMomentConst σ * p ^ σ⁻¹ * K) := by ring
  rw [hstep]
  calc D⁻¹ * (gammaMomentConst σ * p ^ σ⁻¹ * K) ≤ D⁻¹ * D :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hD.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hD)

/-- **`hmomL` for the column array.**  The column-only instance of
`lintegral_rpow_le_one_of_array`. -/
theorem colArray_lintegral_rpow_le_one
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℤ → Ω → ℝ} {σ p K D : ℝ}
    (hσ : 0 < σ) (hK : 0 < K) (hp : 1 ≤ p) (hD : 0 < D)
    (hYnn : ∀ j ω, 0 ≤ Y j ω) (hYm : ∀ j, AEMeasurable (Y j) P)
    (hY : ∀ j, IsBigOWith P (gammaSigma σ) (Y j) K)
    (hnorm : gammaMomentConst σ * p ^ σ⁻¹ * K ≤ D) :
    ∀ k j, ∫⁻ ω, ENNReal.ofReal
        ((colArray (fun n ω => D⁻¹ * Y n ω) k j ω) ^ p) ∂P ≤ 1 :=
  lintegral_rpow_le_one_of_array (Y := fun _ j => Y j) hσ hK hp hD
    (fun _ j ω => hYnn j ω) (fun _ j => hYm j) (fun _ j => hY j) hnorm

/-! ### `hindep` — `ColumnsIndep` for a column-only array -/

/-- **`ColumnsIndep` for a column-only array reduces to independence of the atoms
within each residue class.**  A column of `colArray Y` is the constant-in-`k`
`(ℤ → ℝ)`-valued random variable `ω ↦ (fun _ => Y_j ω)`, a measurable image of the
atom `Y_j`; `iIndepFun.comp` transports mutual independence. -/
theorem columnsIndep_colArray {P : Measure Ω} (Y : ℤ → Ω → ℝ) (r : ℕ)
    (h : ∀ b : ℤ, iIndepFun (fun j : ℤ => Y (j * r + b)) P) :
    ColumnsIndep P (colArray Y) r := by
  intro b
  have hcomp := (h b).comp (g := fun (_ : ℤ) (x : ℝ) => (fun (_ : ℤ) => x))
    (fun _ => Measurable.of_eval (fun _ => measurable_id))
  exact hcomp

end

end Algsuperdiff.Section4.Probability.IndicatorDensity
