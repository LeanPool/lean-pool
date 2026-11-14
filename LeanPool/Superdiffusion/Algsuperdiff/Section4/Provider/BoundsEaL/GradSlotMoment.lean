/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.TsumTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.TailSummability

/-!
# GradSlotMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# B6, first half: the `Γ₂` display of the `L`-free gradient slot

## What this module does

`ShellSlotBounds.lFreeGradSlot m T R ω` is

```
3^{2j} ( Σ_{i ∈ (j−2, m]} ‖∇ j_i‖_{W^{1,∞}(3^j v + □_j)}  +  T j v ω ) ,
```

This module produces the Step-4 target shape `𝒪_{Γ₂}(^{γj})` for that object,
and isolates exactly one layer that the shape does not yet cover.

* **The deep block** `Σ_{i ≥ j}` -- every layer whose shell index is at least the
  cube scale -- carries the display
  ```
  3^{2j} Σ_{i ≥ j} ‖∇ j_i‖_{W^{1,∞}(3^j v + □_j)}
      = 𝒪_{Γ₂}( gammaTriangleConst 2 · (1 − 3^{γ−1})^{-1} · 3^{γ j} ) .
  ```
  The per-layer amplitude is `3^{j} 3^{(γ−1)i}` (`TailSummability`'s
  cross-scale reading of `e.nabla.jk.O`), the geometric sum over `i ≥ j` is
  `3^{γj}(1 − 3^{γ−1})^{-1}`, and the `Γ₂` triangle inequality for countable
  sums is the proved `Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le`.  The
  constant is explicit and absolute: `γ ≤ 1/4` gives `(1 − 3^{γ−1})^{-1} ≤ (1 −
  3^{-3/4})^{-1}`.

* **The bottom layer** `i = j − 1` is separated out
  (`ae_lFreeGradSlot_eq_bottomLayer_add_deep`).  It is the ONE layer of the
  slot whose gauge is read on a cube strictly larger than the shell's own
  scale, and the proved per-shell display does not reach it.

## References

* ABK26, (`e.nabla.jk.O`), (`e.ugly.estimate.for.J.pre`), (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## 1. The layer gauge, and the deep block -/

/-- One layer of the gradient slot: `‖∇ j_i‖_{W^{1,∞}(3^k v + □_k)}`. -/
def gradLayerGauge (k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) (i : ℤ) : ℝ :=
  Support.shellW1InfGradNorm k
    (ShellField.translate (Support.triadicLatticePoint k v) (omega.1 i))

theorem gradLayerGauge_nonneg (k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d)
    (i : ℤ) : 0 ≤ gradLayerGauge k v omega i :=
  Support.shellW1InfGradNorm_nonneg _ _

theorem measurable_gradLayerGauge (k : ℤ) (v : Fin d → ℤ) (i : ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => gradLayerGauge k v omega i :=
  ((Support.measurable_shellW1InfGradNorm k).comp
    (ShellField.measurable_translate (Support.triadicLatticePoint k v))).comp
    ((measurable_pi_apply i).comp measurable_subtype_coe)

/-- The layer term of the D block: the layers whose shell index is at least the
cube scale, where the proved per-shell display applies. -/
def deepGradTerm (k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) (i : ℤ) : ℝ :=
  if k ≤ i then gradLayerGauge k v omega i else 0

theorem deepGradTerm_nonneg (k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d)
    (i : ℤ) : 0 ≤ deepGradTerm k v omega i := by
  unfold deepGradTerm
  split
  · exact gradLayerGauge_nonneg _ _ _ _
  · exact le_rfl

/-- **The deep block** of the gradient slot, before the cube weight. -/
def deepGradSeries (k : ℤ) (v : Fin d → ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  ∑' i : ℤ, deepGradTerm k v omega i

/-! ## 2. The per-layer `Γ₂` display at the cube weight -/

/-- The cube weight times the per-layer amplitude of `TailSummability`, in closed
form. -/
private theorem weightedLayerScale_eq (gam : ℝ) (k i : ℤ) :
    Real.rpow 3 (2 * (k : ℝ)) *
        ((3 : ℝ) ^ (-k) * Real.rpow 3 ((gam - 1) * (i : ℝ))) =
      Real.rpow 3 ((k : ℝ) + (gam - 1) * (i : ℝ)) := by
  have hz : (3 : ℝ) ^ (-k) = Real.rpow 3 (((-k : ℤ) : ℝ)) :=
    (Real.rpow_intCast 3 (-k)).symm
  rw [hz, ← mul_assoc, ← rpow3_add, ← rpow3_add]
  congr 1
  push_cast
  ring

/-- **The weighted layer display.**  For a shell index `i` at least the cube
scale `k`, the weighted layer `3^{2k} ‖∇ j_i‖_{W^{1,∞}(3^k v + □_k)}` has a `Γ₂`
upper tail at amplitude `3^{k + (γ−1)i}`. -/
theorem isBigOWith_gammaSigma_weightedGradLayer (M : ABKModel d) {k i : ℤ} (hki : k ≤ i)
    (v : Fin d → ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega i)
      (Real.rpow 3 ((k : ℝ) + (M.gamma - 1) * (i : ℝ))) := by
  have hc : (0 : ℝ) ≤ Real.rpow 3 (2 * (k : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have h := IsBigOWith.const_mul hc
    (isBigOWith_gammaSigma_shellW1InfGradNorm_translate M hki
      (Support.triadicLatticePoint k v))
  rw [weightedLayerScale_eq M.gamma k i] at h
  exact h

/-! ## 3. The geometric amplitude sum -/

/-- The amplitude at the deep index `i = k + n`, in explicitly geometric form. -/
private theorem deepAmp_eq (gam : ℝ) (k : ℤ) (n : ℕ) :
    Real.rpow 3 ((k : ℝ) + (gam - 1) * ((k + (n : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 (gam * (k : ℝ)) * Real.rpow 3 (gam - 1) ^ n := by
  have hcast : ((k + (n : ℤ) : ℤ) : ℝ) = (k : ℝ) + (n : ℝ) := by push_cast; ring
  rw [hcast,
    show (k : ℝ) + (gam - 1) * ((k : ℝ) + (n : ℝ)) = gam * (k : ℝ) + (gam - 1) * (n : ℝ) by
      ring,
    rpow3_add, rpow3_mul_natCast]

/-- **The absolute constant of the deep block.**  Only `γ ≤ 1/4` enters. -/
def deepGradConst (M : ABKModel d) : ℝ :=
  gammaTriangleConst 2 * (1 - Real.rpow 3 (M.gamma - 1))⁻¹

theorem deepGradConst_pos (M : ABKModel d) : 0 < deepGradConst M := by
  have h1 : Real.rpow 3 (M.gamma - 1) < 1 := rpow_gamma_sub_one_lt_one M
  have h2 : (0 : ℝ) < 1 - Real.rpow 3 (M.gamma - 1) := by linarith only [h1]
  have h3 := gammaTriangleConst_pos (σ := (2 : ℝ))
  unfold deepGradConst
  positivity

/-- The geometric sum of the deep amplitudes. -/
private theorem tsum_deepAmp (M : ABKModel d) (k : ℤ) :
    ∑' n : ℕ, Real.rpow 3 (M.gamma * (k : ℝ)) * Real.rpow 3 (M.gamma - 1) ^ n =
      Real.rpow 3 (M.gamma * (k : ℝ)) * (1 - Real.rpow 3 (M.gamma - 1))⁻¹ := by
  have hgeo : ∑' n : ℕ, Real.rpow 3 (M.gamma - 1) ^ n =
      (1 - Real.rpow 3 (M.gamma - 1))⁻¹ :=
    tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (rpow_gamma_sub_one_lt_one M)
  rw [tsum_mul_left, hgeo]

/-! ## 4. The deep block's `Γ₂` display -/

/-- The `ℕ`-indexed reading of the deep block. -/
theorem tsum_deepGradTerm_eq (k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) :
    ∑' n : ℕ, gradLayerGauge k v omega (k + (n : ℤ)) = deepGradSeries k v omega := by
  have hinj : Function.Injective fun n : ℕ => k + (n : ℤ) := by
    intro a b hab
    have hab' : k + (a : ℤ) = k + (b : ℤ) := hab
    omega
  have hsupp : Function.support (deepGradTerm k v omega) ⊆
      Set.range fun n : ℕ => k + (n : ℤ) := by
    intro x hx
    have hkx : k ≤ x := by
      by_contra hcon
      exact hx (by rw [deepGradTerm, ite_eq_right hcon])
    exact ⟨(x - k).toNat, by change k + (((x - k).toNat : ℕ) : ℤ) = x; omega⟩
  refine Eq.trans (tsum_congr fun n => ?_) (hinj.tsum_eq hsupp)
  rw [deepGradTerm, ite_eq_left (by omega : k ≤ k + (n : ℤ))]

/-- **B6, first half: the deep block of the gradient slot has the Step-4 target
shape.**

`3^{2j} Σ_{i ≥ j} ‖∇ j_i‖_{W^{1,∞}(3^j v + □_j)} = 𝒪_{Γ₂}(^{γ j})` with the
explicit absolute constant `C = gammaTriangleConst 2 · (1 − 3^{γ−1})^{-1}`.  No
exponent is moved: the per-layer amplitude is the manuscript's own
`3^{(γ−1)i}`, the cube weight contributes `3^{k}`, and the geometric sum over
`i ≥ k` contributes `3^{γk}(1 − 3^{γ−1})^{-1}`. -/
theorem isBigOWith_gammaSigma_deepGradSeries (M : ABKModel d) (k : ℤ) (v : Fin d → ℤ) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * deepGradSeries k v omega)
      (deepGradConst M * Real.rpow 3 (M.gamma * (k : ℝ))) := by
  have hlayer : ∀ n : ℕ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k + (n : ℤ)))
      (Real.rpow 3 (M.gamma * (k : ℝ)) * Real.rpow 3 (M.gamma - 1) ^ n) := by
    intro n
    have h := isBigOWith_gammaSigma_weightedGradLayer M
      (by omega : k ≤ k + (n : ℤ)) v
    rwa [deepAmp_eq M.gamma k n] at h
  have hsummable : Summable fun n : ℕ =>
      Real.rpow 3 (M.gamma * (k : ℝ)) * Real.rpow 3 (M.gamma - 1) ^ n :=
    (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _)
      (rpow_gamma_sub_one_lt_one M)).mul_left _
  have hbase := Provider.Orlicz.isBigOWith_gammaSigma_tsum_of_tsum_le
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (σ := 2)
    (X := fun (n : ℕ) (omega : Cutoff.CutoffSample d) =>
      Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k + (n : ℤ)))
    (a := fun n : ℕ =>
      Real.rpow 3 (M.gamma * (k : ℝ)) * Real.rpow 3 (M.gamma - 1) ^ n)
    (by norm_num)
    (fun n omega => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (gradLayerGauge_nonneg _ _ _ _))
    (fun n => (measurable_gradLayerGauge k v (k + (n : ℤ))).const_mul _)
    (fun n => mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (pow_pos (Real.rpow_pos_of_pos (by norm_num) _) n))
    hsummable hlayer (le_of_eq (tsum_deepAmp M k))
  have hfun : (fun omega : Cutoff.CutoffSample d => ∑' n : ℕ,
      Real.rpow 3 (2 * (k : ℝ)) * gradLayerGauge k v omega (k + (n : ℤ))) =
      fun omega : Cutoff.CutoffSample d =>
        Real.rpow 3 (2 * (k : ℝ)) * deepGradSeries k v omega := by
    funext omega
    rw [tsum_mul_left, tsum_deepGradTerm_eq]
  rw [hfun] at hbase
  refine hbase.mono_scale (le_of_eq ?_)
  unfold deepGradConst
  ring

/-! ## 5. The slot decomposition: the deep block plus ONE bottom layer -/

/-- The gradient slot, spelled with the cube weight in `Real.rpow` form. -/
private theorem lFreeGradSlot_eq (m : ℤ)
    (T : ℤ → (Fin d → ℤ) → Cutoff.CutoffSample d → ℝ) (R : TriadicCube d)
    (omega : Cutoff.CutoffSample d) :
    lFreeGradSlot m T R omega =
      Real.rpow 3 (2 * (R.scale : ℝ)) *
        (headLayerSum m R.scale R.index omega + T R.scale R.index omega) :=
  rfl

/-- The layer bookkeeping: below the truncation the deep term splits into the
`(m, ∞)` tail term and a finitely supported middle block. -/
theorem deepGradTerm_eq_add (m k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) (hkm : k ≤ m) (i : ℤ) :
    deepGradTerm k v omega i =
      tailLayerTerm m k v omega i +
        (if k ≤ i ∧ i ≤ m then gradLayerGauge k v omega i else 0) := by
  rcases lt_or_ge i k with hik | hik
  · rw [deepGradTerm, ite_eq_right (by omega), tailLayerTerm, ite_eq_right (by omega),
      ite_eq_right (by omega : ¬ (k ≤ i ∧ i ≤ m))]
    ring
  · rcases le_or_gt i m with him | him
    · rw [deepGradTerm, ite_eq_left hik, tailLayerTerm, ite_eq_right (by omega),
        ite_eq_left (⟨hik, him⟩ : k ≤ i ∧ i ≤ m)]
      ring
    · rw [deepGradTerm, ite_eq_left hik, gradLayerGauge, tailLayerTerm, ite_eq_left him,
        ite_eq_right (by omega : ¬ (k ≤ i ∧ i ≤ m))]
      ring

/-- **The slot bracket, resolved.**  Wherever the upper shell series converges,
the `L`-free bracket of the gradient slot is the bottom layer `i = k − 1` plus
the deep block. -/
theorem headLayerSum_add_tailSeriesGauge_eq (m k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) (hkm : k ≤ m)
    (hsum : Summable (tailLayerTerm m k v omega)) :
    headLayerSum m k v omega + tailSeriesGauge m k v omega =
      gradLayerGauge k v omega (k - 1) + deepGradSeries k v omega := by
  have hmidsum : Summable fun i : ℤ =>
      (if k ≤ i ∧ i ≤ m then gradLayerGauge k v omega i else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.Icc k m) fun i hi => ?_
    rw [ite_eq_right (fun h => hi (Finset.mem_Icc.mpr h))]
  have hmid : (∑' i : ℤ, if k ≤ i ∧ i ≤ m then gradLayerGauge k v omega i else 0) =
      ∑ i ∈ Finset.Icc k m, gradLayerGauge k v omega i := by
    rw [tsum_eq_sum (s := Finset.Icc k m) fun i hi => by
      rw [ite_eq_right (fun h => hi (Finset.mem_Icc.mpr h))]]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ite_eq_left (Finset.mem_Icc.mp hi)]
  have hdeep : deepGradSeries k v omega =
      tailSeriesGauge m k v omega + ∑ i ∈ Finset.Icc k m, gradLayerGauge k v omega i := by
    rw [deepGradSeries, tsum_congr (deepGradTerm_eq_add m k v omega hkm),
      hsum.tsum_add hmidsum, hmid, tailSeriesGauge]
  have hIoc : Finset.Ioc (k - 2) m = insert (k - 1) (Finset.Icc k m) := by
    ext i
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotmem : (k - 1) ∉ Finset.Icc k m := by
    simp only [Finset.mem_Icc]
    omega
  have hhead : headLayerSum m k v omega =
      gradLayerGauge k v omega (k - 1) + ∑ i ∈ Finset.Icc k m, gradLayerGauge k v omega i := by
    rw [headLayerSum, hIoc, Finset.sum_insert hnotmem]
    rfl
  rw [hhead, hdeep]
  ring

/-- **B6, first half: the gradient slot resolved almost surely.**

At the canonical tail gauge the `L`-free gradient slot is, almost surely, the
weighted bottom layer `i = R.scale − 1` plus the weighted deep block. -/
theorem ae_lFreeGradSlot_eq_bottomLayer_add_deep (M : ABKModel d) (m : ℤ)
    (R : TriadicCube d) (hkm : R.scale ≤ m) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lFreeGradSlot m (tailSeriesGauge m) R omega =
        Real.rpow 3 (2 * (R.scale : ℝ)) *
            gradLayerGauge R.scale R.index omega (R.scale - 1) +
          Real.rpow 3 (2 * (R.scale : ℝ)) * deepGradSeries R.scale R.index omega := by
  filter_upwards [ae_forall_summable_tailLayerTerm M m] with omega hsum
  rw [lFreeGradSlot_eq,
    headLayerSum_add_tailSeriesGauge_eq m R.scale R.index omega hkm (hsum R.scale R.index)]
  ring

end

end Algsuperdiff.Section4.Provider.BoundsEaL
