/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LargeWaves
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.SmallWavesArith
import LeanPool.Superdiffusion.Algsuperdiff.Section3.Probability.OneSidedOrlicz

/-!
# SmallWaves

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Step 2 of `l.ratio.of.good.scales.for.k`: the small-waves lane

This module realizes the `𝒢₁b` half of `l.ratio.of.good.scales.for.k`: the
**genuinely two-index** Appendix-D array `X_{m,k}`, its reduction of the second
`𝒢₁` condition, and the resulting proportion tail
`e.small.waves.scale.counting`.

## The array really is two-index, and that is not a problem here

* the array `arrayG1b` is written at the honest two-index shape, which is also
  the shape of the proved `p.concentration.for.scales` (its array is `X: ℤ → ℤ
  → Ω → ℝ`, and `colArray` is a derived special case), so **no new
  concentration inequality is needed**;
* the independence hypothesis is discharged by `columnsIndep_of_shellColumn`,
  the genuine two-index producer: column `k` reads the single layer `j_k`, and
  the row index enters only through deterministic data (the discount and the
  deterministic centre set), so (J1) gives independence at every `r ≥ 1`.

## The gap in `e.Xmk.pedant.bound`, paid explicitly

The graph records that the lattice-max penalty `≍ C(d)(m-k)^{1/σ}` grows with
`m - k` and is absorbed by nothing displayed except the discount, so the printed
uniform constant implicitly consumes `sup_j (1+j)3^{-sj/8} ≍ Cs^{-1}` — one power
of `s^{-1}` beyond the `s^{-2}` shown.  Here that absorption is
`SmallWavesArith.rpow_mul_penalty_sq_le`, and the resulting uniform amplitude is
`smallWaveScale`, explicitly `8 s^{-1}(1 + 2d log 3)` times the squared atom
amplitude.

## References

* ABK26, `l.ratio.of.good.scales.for.k`, Step 2.
* ABK26, `d.good.event.for.lambda`, (the second `𝒢₁` condition).
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Probability
open Algsuperdiff.Section4.Probability.ScalesConcentration
open Algsuperdiff.Section4.Probability.IndicatorDensity
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 0. A `Γ_σ` tail for the identically zero observable -/

private theorem isBigOWith_gammaSigma_zero {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {sigma A : ℝ} (hA : 0 < A) :
    IsBigOWith mu (gammaSigma sigma) (fun _ : Omega => (0 : ℝ)) A :=
  Algsuperdiff.Section3.Probability.isBigOWith_gammaSigma_of_eq_zero hA.le (fun _ => rfl)

/-! ## 1. The `𝒢₁b` score field: the lattice maximum at scale `k` inside `□_m` -/

/-- **The `𝒢₁b` score field**: `3^{(2-γ)k} max_{z ∈ 3^kℤ^d ∩ □_m}
‖j_k‖_{W^{2,∞}(z+□_k)}`, as the `0`-floored maximum over the explicit lattice
`Finset`. -/
def scoreG1b (M : ABKModel d) (m k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  fmax (latticeCubeFinset d k m)
    fun v => atomG1b M k (Support.triadicLatticePoint k v) omega

theorem scoreG1b_nonneg (M : ABKModel d) (m k : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ scoreG1b M m k omega :=
  fmax_nonneg _ _

theorem measurable_scoreG1b (M : ABKModel d) (m k : ℤ) :
    Measurable (scoreG1b M m k) :=
  measurable_fmax _ fun v =>
    measurable_atomG1b M k (Support.triadicLatticePoint k v)

/-- The score field reads exactly one shell — the (J1) input of the independence
hypothesis, at the genuinely two-index shape. -/
theorem shellLocal_scoreG1b (M : ABKModel d) (m k : ℤ) :
    Measurable[shellSigma d k] (scoreG1b M m k) := by
  let : MeasurableSpace (Cutoff.CutoffSample d) := shellSigma d k
  exact measurable_fmax _ fun v =>
    measurable_shellSigma_comp k
      ((measurable_shellW2InfNormAt (Support.triadicLatticePoint k v) k).const_mul
        (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))))

/-- **`e.maxy.bound` at the `𝒢₁b` lattice cube.**  The per-centre `Γ₂` tail of
`atomG1b`, lifted through the maximum at the machine-computed union-bound
penalty `(1 + d(m-k+1) log 3)^{1/2}`. -/
theorem isBigOWith_scoreG1b (M : ABKModel d) (m k : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (scoreG1b M m k)
      (annulusPenalty d 2 (m - k).toNat * atomG1bScale) :=
  isBigOWith_fmax _ (by norm_num) atomG1bScale_pos.le
    (one_le_annulusPenalty d (by norm_num) _)
    (log_card_cube_le_annulusPenalty_rpow_sub_one d (by norm_num) k m)
    fun v _ => isBigOWith_atomG1b M k _

/-! ## 2. The two-index Appendix-D array -/

/-- **The `𝒢₁b` Appendix-D array, genuinely two-index**: `X_{m,k} =
3^{-s(m-k)/8}(3^{(2-γ)k}max_{z ∈ 3^kℤ^d ∩ □_m}‖j_k‖_{W^{2,∞}(z+□_k)})²` for `k
≤ m`, and `0` otherwise. -/
def arrayG1b (M : ABKModel d) (s : ℝ) (m k : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  if k ≤ m then
    Real.rpow (3 : ℝ) (-(s / 8) * ((m - k : ℤ) : ℝ)) * scoreG1b M m k omega ^ 2
  else 0

theorem arrayG1b_nonneg (M : ABKModel d) (s : ℝ) (m k : ℤ)
    (omega : Cutoff.CutoffSample d) : 0 ≤ arrayG1b M s m k omega := by
  unfold arrayG1b
  split_ifs
  · exact mul_nonneg (rpow_nonneg_three _) (sq_nonneg _)
  · exact le_rfl

theorem measurable_arrayG1b (M : ABKModel d) (s : ℝ) (m k : ℤ) :
    Measurable (arrayG1b M s m k) := by
  unfold arrayG1b
  split_ifs
  · exact ((measurable_scoreG1b M m k).pow_const 2).const_mul _
  · exact measurable_const

theorem shellLocal_arrayG1b (M : ABKModel d) (s : ℝ) (m k : ℤ) :
    Measurable[shellSigma d k] (arrayG1b M s m k) := by
  unfold arrayG1b
  split_ifs
  · exact ((shellLocal_scoreG1b M m k).pow_const 2).const_mul _
  · exact measurable_const

/-- The uniform `Γ₁` amplitude of the two-index array: the squared atom
amplitude, times the `8 s^{-1}(1 + 2d log 3)` produced by absorbing the growing
lattice-max penalty into the discount. -/
def smallWaveScale (d : ℕ) (s : ℝ) : ℝ :=
  8 / s * (1 + 2 * (d : ℝ) * Real.log 3) * atomG1bScale ^ 2

theorem smallWaveScale_pos (d : ℕ) {s : ℝ} (hs0 : 0 < s) : 0 < smallWaveScale d s := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hA : (0 : ℝ) < atomG1bScale ^ 2 := pow_pos atomG1bScale_pos 2
  have hfac : (0 : ℝ) < 8 / s * (1 + 2 * (d : ℝ) * Real.log 3) := by positivity
  exact mul_pos hfac hA

private theorem penalty_sq_eq (d : ℕ) (p : ℕ) :
    annulusPenalty d 2 p ^ 2 = 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by
  have h := annulusPenalty_rpow d (show (0 : ℝ) < 2 by norm_num) p
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast] at h
  exact h

/-- **`e.Xmk.pedant.bound`, in tail form, with the accounting made explicit.**
Every entry of the two-index array has a `Γ₁` upper tail at the *uniform*
amplitude `smallWaveScale d s`.  The three inputs are: the per-centre `Γ₂` tail
of `atomG1b`, the union-bound penalty over the growing lattice cube, and
`e.powerofGammasigma` (squaring moves `σ = 2` to `σ = 1`). -/
theorem isBigOWith_arrayG1b (M : ABKModel d) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (m k : ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 1)
      (arrayG1b M s m k) (smallWaveScale d s) := by
  unfold arrayG1b
  split_ifs with hk
  · have hpen : (0 : ℝ) ≤ annulusPenalty d 2 (m - k).toNat * atomG1bScale :=
      mul_nonneg (le_trans zero_le_one (one_le_annulusPenalty d (by norm_num) _))
        atomG1bScale_pos.le
    have hsq := (Provider.Orlicz.isBigOWith_gammaSigma_sq_iff_of_nonneg
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (X := scoreG1b M m k)
      (K := annulusPenalty d 2 (m - k).toNat * atomG1bScale) (σ := (2 : ℝ))
      hpen (scoreG1b_nonneg M m k)).1 (isBigOWith_scoreG1b M m k)
    rw [show (2 : ℝ) / 2 = 1 from by norm_num] at hsq
    have hmul := hsq.const_mul
      (c := Real.rpow (3 : ℝ) (-(s / 8) * ((m - k : ℤ) : ℝ))) (rpow_nonneg_three _)
    refine hmul.mono_scale ?_
    have hcast : ((m - k : ℤ) : ℝ) = (((m - k).toNat : ℕ) : ℝ) := by
      have hz : (((m - k).toNat : ℕ) : ℤ) = m - k :=
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m - k)
      exact_mod_cast hz.symm
    have harith := rpow_mul_penalty_sq_le d hs0 hs1 (m - k).toNat
    have hA2 : (0 : ℝ) ≤ atomG1bScale ^ 2 := (pow_pos atomG1bScale_pos 2).le
    calc Real.rpow (3 : ℝ) (-(s / 8) * ((m - k : ℤ) : ℝ)) *
          (annulusPenalty d 2 (m - k).toNat * atomG1bScale) ^ 2
        = (Real.rpow (3 : ℝ) (-(s / 8 * (((m - k).toNat : ℕ) : ℝ))) *
            (1 + (d : ℝ) * ((((m - k).toNat : ℕ) : ℝ) + 1) * Real.log 3)) *
              atomG1bScale ^ 2 := by
          rw [mul_pow, penalty_sq_eq, hcast]
          ring_nf
      _ ≤ (8 / s * (1 + 2 * (d : ℝ) * Real.log 3)) * atomG1bScale ^ 2 :=
          mul_le_mul_of_nonneg_right harith hA2
      _ = smallWaveScale d s := rfl
  · exact isBigOWith_gammaSigma_zero (smallWaveScale_pos d hs0)

/-! ## 3. The reduction of the second `𝒢₁` condition -/

private theorem inner_le_score (M : ABKModel d) {m k : ℤ} (hk : k ≤ m)
    (omega : Cutoff.CutoffSample d) :
    ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
        ⨆ v : ↥(Support.latticeCubeSet d k m),
          ENNReal.ofReal
            (shellW2InfNormAt (Support.triadicLatticePoint k v.1) k (omega.1 k)) ≤
      ENNReal.ofReal (scoreG1b M m k omega) := by
  rw [ENNReal.mul_iSup]
  refine iSup_le fun v => ?_
  rw [← ENNReal.ofReal_mul (rpow_nonneg_three _)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact le_fmax (f := fun v => atomG1b M k (Support.triadicLatticePoint k v) omega)
    ((mem_latticeCubeFinset_iff hk).2 v.2)

/-- The inner block of `𝒢₁b` at one scale is below the squared score field. -/
theorem eventG1b_inner_le (M : ABKModel d) {m k : ℤ} (hk : k ≤ m)
    (omega : Cutoff.CutoffSample d) :
    (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
        ⨆ v : ↥(Support.latticeCubeSet d k m),
          ENNReal.ofReal
            (shellW2InfNormAt (Support.triadicLatticePoint k v.1) k (omega.1 k))) ^ 2 ≤
      ENNReal.ofReal (scoreG1b M m k omega ^ 2) := by
  rw [ENNReal.ofReal_pow (scoreG1b_nonneg M m k omega)]
  exact pow_le_pow_left' (inner_le_score M hk omega) 2

private theorem wt_mul_arrayG1b (M : ABKModel d) (s : ℝ) {m k : ℤ} (hk : k ≤ m)
    (omega : Cutoff.CutoffSample d) :
    ENNReal.ofReal (wt (s / 8) m k * arrayG1b M s m k omega) =
      gwG1b s (m - k) * ENNReal.ofReal (scoreG1b M m k omega ^ 2) := by
  have hid : idist m k = ((m - k : ℤ) : ℝ) := by
    have hle : ((k : ℤ) : ℝ) ≤ ((m : ℤ) : ℝ) := by exact_mod_cast hk
    simp only [idist]
    push_cast
    exact abs_of_nonneg (by linarith only [hle])
  have hpow : Real.rpow (3 : ℝ) (-(s / 8 * ((m - k : ℤ) : ℝ))) *
      Real.rpow (3 : ℝ) (-(s / 8) * ((m - k : ℤ) : ℝ)) =
      Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - k : ℤ) : ℝ)) := by
    rw [← rpow_add_three]
    congr 1
    ring
  have hwt : wt (s / 8) m k = Real.rpow (3 : ℝ) (-(s / 8 * ((m - k : ℤ) : ℝ))) := by
    rw [wt, hid]
    rfl
  rw [arrayG1b, ite_eq_left hk, hwt, gwG1b,
    ← ENNReal.ofReal_mul (rpow_nonneg_three _),
    show Real.rpow (3 : ℝ) (-(s / 8 * ((m - k : ℤ) : ℝ))) *
        (Real.rpow (3 : ℝ) (-(s / 8) * ((m - k : ℤ) : ℝ)) *
          scoreG1b M m k omega ^ 2) =
        (Real.rpow (3 : ℝ) (-(s / 8 * ((m - k : ℤ) : ℝ))) *
          Real.rpow (3 : ℝ) (-(s / 8) * ((m - k : ℤ) : ℝ))) *
            scoreG1b M m k omega ^ 2 from by ring,
    hpow]

/-- **The `𝒢₁b` reduction, against the honest two-index array.**  The left side of
the second `𝒢₁` condition at row `m` is at most `g1bConst s` times the
Appendix-D row sum of `arrayG1b` at rate `s/8`.  Two steps: the interchange (an
identity in `ℝ≥0∞`) and the geometric partial weight (the manuscript's
`4s^{-1}`). -/
theorem eventG1b_lhs_le_rowGE (M : ABKModel d) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (m : ℤ) (omega : Cutoff.CutoffSample d) :
    (∑' n : {n : ℤ // n ≤ m},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
          ∑ k ∈ Finset.Icc (n.1 - 1) m,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                ⨆ v : ↥(Support.latticeCubeSet d k m),
                  ENNReal.ofReal
                    (shellW2InfNormAt (Support.triadicLatticePoint k v.1) k
                      (omega.1 k))) ^ 2) ≤
      ENNReal.ofReal (g1bConst s) * rowGE (arrayG1b M s) (s / 8) m omega := by
  classical
  set g : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal (scoreG1b M m k omega ^ 2) with hg
  set w : ℤ → ℝ≥0∞ := fun n => gwG1b s (m - n) with hw
  set F : ℤ → ℝ≥0∞ :=
    fun n => if n ≤ m then w n * ∑ k ∈ Finset.Icc (n - 1) m, g k else 0 with hF
  have hstep1 : (∑' n : {n : ℤ // n ≤ m},
      ENNReal.ofReal
          (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
        ∑ k ∈ Finset.Icc (n.1 - 1) m,
          (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
              ⨆ v : ↥(Support.latticeCubeSet d k m),
                ENNReal.ofReal
                  (shellW2InfNormAt (Support.triadicLatticePoint k v.1) k
                    (omega.1 k))) ^ 2) ≤ ∑' n : {n : ℤ // n ≤ m}, F n.1 := by
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [hF]
    simp only [ite_eq_left n.2, hw, hg, gwG1b]
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun k hk => ?_)
    exact eventG1b_inner_le M (Finset.mem_Icc.1 hk).2 omega
  have hstep2 : (∑' n : {n : ℤ // n ≤ m}, F n.1) ≤ ∑' n : ℤ, F n :=
    ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
  have hstep3 : (∑' n : ℤ, F n) =
      ∑' k : ℤ,
        (if k ≤ m then (∑' n : ℤ, (if n ≤ min (k + 1) m then w n else 0)) * g k
          else 0) := tsum_block_comm w g m
  have hstep4 : ∀ k : ℤ,
      (if k ≤ m then (∑' n : ℤ, (if n ≤ min (k + 1) m then w n else 0)) * g k else 0) ≤
        ENNReal.ofReal (g1bConst s) *
          ENNReal.ofReal (wt (s / 8) m k * arrayG1b M s m k omega) := by
    intro k
    by_cases hk : k ≤ m
    · rw [ite_eq_left hk, wt_mul_arrayG1b M s hk omega, hw]
      refine le_trans (mul_le_mul' (tsum_partialWeight_le hs0 hs1 m k) le_rfl) ?_
      rw [mul_assoc]
    · rw [ite_eq_right hk]
      exact zero_le
  calc (∑' n : {n : ℤ // n ≤ m},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
          ∑ k ∈ Finset.Icc (n.1 - 1) m,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                ⨆ v : ↥(Support.latticeCubeSet d k m),
                  ENNReal.ofReal
                    (shellW2InfNormAt (Support.triadicLatticePoint k v.1) k
                      (omega.1 k))) ^ 2)
      ≤ ∑' n : ℤ, F n := le_trans hstep1 hstep2
    _ = ∑' k : ℤ,
          (if k ≤ m then (∑' n : ℤ, (if n ≤ min (k + 1) m then w n else 0)) * g k
            else 0) := hstep3
    _ ≤ ∑' k : ℤ, ENNReal.ofReal (g1bConst s) *
          ENNReal.ofReal (wt (s / 8) m k * arrayG1b M s m k omega) :=
        ENNReal.tsum_le_tsum hstep4
    _ = ENNReal.ofReal (g1bConst s) * rowGE (arrayG1b M s) (s / 8) m omega :=
        ENNReal.tsum_mul_left

/-- Off the lane's good event the `ℝ≥0∞` row exceeds the scaled threshold. -/
theorem lt_rowGE_of_notMem_eventG1b (M : ABKModel d) {s T : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) (m : ℤ) {omega : Cutoff.CutoffSample d}
    (hnot : omega ∉ eventG1b M m s T) :
    ENNReal.ofReal (T ^ 2 / g1bConst s) < rowGE (arrayG1b M s) (s / 8) m omega := by
  rw [eventG1b, Set.mem_ofPred_eq, not_le] at hnot
  have hC : 0 < g1bConst s := g1bConst_pos hs0
  have hlt : ENNReal.ofReal (T ^ 2) <
      ENNReal.ofReal (g1bConst s) * rowGE (arrayG1b M s) (s / 8) m omega :=
    hnot.trans_le (eventG1b_lhs_le_rowGE M hs0 hs1 m omega)
  have heq : ENNReal.ofReal (g1bConst s) * ENNReal.ofReal (T ^ 2 / g1bConst s) =
      ENNReal.ofReal (T ^ 2) := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    field_simp
  rw [← heq] at hlt
  by_contra hcon
  push Not at hcon
  exact absurd hlt (not_lt.2 (mul_le_mul' (le_refl (ENNReal.ofReal (g1bConst s))) hcon))

end

end Algsuperdiff.Section4.Provider.Proportion
