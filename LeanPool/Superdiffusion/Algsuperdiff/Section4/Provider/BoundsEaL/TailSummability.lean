/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.AESummability
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.NegationSymmetry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.ShellSlotBounds

/-!
# TailSummability

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The upper shell series converges almost surely: `hTae` discharged

## What this module does

```
tailLayerSum m k v ω L = Σ_{i ∈ (m, L]} ‖∇ j_i‖_{W^{1,∞}(3^k v + □_k)} ,
```

and `tailLayerSum_le_tailSeriesGauge` reduced an `L`-uniform bound for it to the
`Summable`ity of the layer terms.  This module proves that summability -- for
every cube `(k, v)` simultaneously -- almost surely, and therefore discharges
the `hTae` binder of
`AeMajorantTransport.lintegral_observableSup_rpow_le_tsum_lintegral_lFreeStep3Majorant_of_ae`
at the canonical gauge `T := tailSeriesGauge m`.

## The route

1. **The per-layer display.**  `Support.shellW1InfGradNorm k j` is the maximum
   of `‖∇²j‖_{L∞(□_k)}` and `3^{-k}‖∇j‖_{L∞(□_k)}`, hence at most
   `3^{-k}(‖∇j‖_{L∞(□_k)} + 3^{k}‖∇²j‖_{L∞(□_k)})`.  For the shell `j_i` with
   `k ≤ i` the bracket is exactly the manuscript's `e.nabla.jk.O` gauge
   measured on the smaller cube, i.e. the proved
   `Stream.isBigOWith_gammaSigma_shellDerivGauge_cube` at amplitude
   `3^{(γ−1)i}`.  So the layer term is `𝒪_{Γ₂}(3^{-k} 3^{(γ−1)i})`, and the
   amplitudes are summable in `i` because `γ ≤ 1/4 < 1`.

2. **The carriers.**  The display lives on `Cutoff.ShellSeq d` under `M.P`; the
   transfers to `Cutoff.CutoffSample d` under `Cutoff.cutoffSampleLaw M` and to
   the translated cube `3^k v + □_k` are the proved
   `Stream.isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val` and
   `Stream.isBigOWith_comp_translateCutoffSample` -- exactly the pair
   `Proportion.G1AtomTails` uses for the `𝒢₁` atoms.  No lattice restriction is
   used: the statement holds at every real centre, so at every `(k, v)`.

3. **The first-moment bridge.**  `Orlicz.ae_summable_of_isBigOWith_gammaSigma`:
   a summable family of positive `Γ_σ` scales forces almost sure summability
   (Tonelli on the first moments).  It is indexed by `ℕ`, so the `ℤ`-indexed
   layer family is re-indexed at `i₀ = max (m+1) k` -- the finitely many layers
   `i ∈ (m, k)`, where the cross-scale display is unavailable, are irrelevant to
   summability and are absorbed by `summable_nat_add_iff`.

4. **The countable family.**  `MeasureTheory.ae_all_iff` over the countable index
   `ℤ × (Fin d → ℤ)`.

5. **The negated leg.**, and pointwise: every layer gauge is even
   (`Annular.shellW1InfGradNorm_negate`, `Localization.translate_negate`), so
   `tailLayerTerm`, `tailLayerSum` and `tailSeriesGauge` are all literally
   invariant under `Cutoff.negateCutoffSample`.  The law-level invariance
   `Cutoff.map_negateCutoffSample_cutoffSampleLaw` is NOT consumed.

## References

* ABK26, (`e.nabla.jk.O`); (the gradient slot); (Step 3).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Localization
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-layer deterministic domination -/

/-- The volume-normalized gradient gauge on `□_k` is dominated by the
`e.nabla.jk.O` gauge on the same cube, rescaled by `3^{-k}`: the gauge is a
maximum of two nonnegative legs and the bracket is their `3^{k}`-weighted sum. -/
theorem shellW1InfGradNorm_le_zpow_mul_shellDerivGauge (k : ℤ) (j : ShellField d) :
    Support.shellW1InfGradNorm k j ≤
      (3 : ℝ) ^ (-k) *
        (localCubeDerivNorm k j + (3 : ℝ) ^ k * localCubeSecondDerivNorm k j) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  have hcancel : (3 : ℝ) ^ (-k) * ((3 : ℝ) ^ k * localCubeSecondDerivNorm k j) =
      localCubeSecondDerivNorm k j := by
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero,
      one_mul]
  have hA : (0 : ℝ) ≤ localCubeSecondDerivNorm k j := localCubeSecondDerivNorm_nonneg k j
  have hB : (0 : ℝ) ≤ (3 : ℝ) ^ (-k) * localCubeDerivNorm k j :=
    mul_nonneg hpos.le (localCubeDerivNorm_nonneg k j)
  rw [Support.shellW1InfGradNorm_def, mul_add, hcancel]
  exact max_le (by linarith only [hB]) (by linarith only [hA])

/-! ## 2. The cross-scale `Γ₂` tail of one layer gauge -/

/-- **The layer gauge at a smaller cube, on the shell-sequence law.**  For `k ≤ i`
the gauge `‖∇j_i‖_{W^{1,∞}(□_k)}` has a `Γ₂` upper tail at amplitude `3^{-k}
3^{(γ−1)i}`: the manuscript's `e.nabla.jk.O` measured on `□_k` and
renormalized.  Only proved Section 3 material enters. -/
theorem isBigOWith_gammaSigma_shellW1InfGradNorm_shellSeq (M : ABKModel d) {k i : ℤ}
    (hki : k ≤ i) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : Cutoff.ShellSeq d => Support.shellW1InfGradNorm k (omega i))
      ((3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i : ℝ))) :=
  (IsBigOWith.const_mul (zpow_pos (show (0 : ℝ) < 3 by norm_num) (-k)).le
      (isBigOWith_gammaSigma_shellDerivGauge_cube M hki)).of_le
    fun omega => shellW1InfGradNorm_le_zpow_mul_shellDerivGauge k (omega i)

/-- **The layer gauge at a translated cube, on the cutoff-sample law.**  The two
proved transfers -- the measurable-embedding transfer to `Cutoff.CutoffSample`
and the real-translation invariance of the cutoff-sample law -- carry the
display of `isBigOWith_gammaSigma_shellW1InfGradNorm_shellSeq` to
`‖∇j_i‖_{W^{1,∞}(z + □_k)}` real centre `z`, at the same amplitude. -/
theorem isBigOWith_gammaSigma_shellW1InfGradNorm_translate (M : ABKModel d) {k i : ℤ}
    (hki : k ≤ i) (z : Vec d) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d =>
        Support.shellW1InfGradNorm k (ShellField.translate z (omega.1 i)))
      ((3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i : ℝ))) := by
  have hbase : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega : Cutoff.CutoffSample d => Support.shellW1InfGradNorm k (omega.1 i))
      ((3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i : ℝ))) :=
    isBigOWith_cutoffSampleLaw_of_forall_eq_comp_val (fun _ => rfl)
      (isBigOWith_gammaSigma_shellW1InfGradNorm_shellSeq M hki)
  have hmeas : Measurable fun omega : Cutoff.CutoffSample d =>
      Support.shellW1InfGradNorm k (omega.1 i) :=
    (Support.measurable_shellW1InfGradNorm k).comp
      ((measurable_pi_apply i).comp measurable_subtype_coe)
  exact isBigOWith_comp_translateCutoffSample M z hmeas hbase

/-! ## 3. The geometric amplitude family -/

/-- The common ratio of the layer amplitudes: `3^{γ−1} < 1` because `γ ≤ 1/4`. -/
theorem rpow_gamma_sub_one_lt_one (M : ABKModel d) :
    Real.rpow 3 (M.gamma - 1) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith only [M.shellPrefix.gamma_le_quarter])

/-- The exponent addition law at base `3`, in the explicit `Real.rpow` spelling
used throughout this file. -/
theorem rpow3_add (x y : ℝ) :
    Real.rpow 3 (x + y) = Real.rpow 3 x * Real.rpow 3 y :=
  Real.rpow_add (by norm_num) x y

/-- The natural-power law at base `3`, in the explicit `Real.rpow` spelling. -/
theorem rpow3_mul_natCast (x : ℝ) (n : ℕ) :
    Real.rpow 3 (x * (n : ℝ)) = Real.rpow 3 x ^ n := by
  have h1 : Real.rpow 3 (x * (n : ℝ)) = Real.rpow (Real.rpow 3 x) (n : ℝ) :=
    Real.rpow_mul (by norm_num) x (n : ℝ)
  have h2 : Real.rpow (Real.rpow 3 x) (n : ℝ) = Real.rpow 3 x ^ n :=
    Real.rpow_natCast (Real.rpow 3 x) n
  rw [h1, h2]

/-- The layer amplitude at `i = i₀ + n`, in explicitly geometric form. -/
private theorem layerScale_eq (M : ABKModel d) (k i0 : ℤ) (n : ℕ) :
    (3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * ((i0 + (n : ℤ) : ℤ) : ℝ)) =
      ((3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i0 : ℝ))) *
        Real.rpow 3 (M.gamma - 1) ^ n := by
  have hcast : ((i0 + (n : ℤ) : ℤ) : ℝ) = (i0 : ℝ) + (n : ℝ) := by push_cast; ring
  rw [hcast, mul_add, rpow3_add, rpow3_mul_natCast, mul_assoc]

/-! ## 4. Almost sure summability of the layer terms -/

/-- **The upper shell series converges almost surely, at one cube.**

For every scale `k` and lattice index `v`, the `ℤ`-indexed layer family of
`ShellSlotBounds.tailLayerTerm` is almost surely summable.  This is the
probabilistic content of `hTae`. -/
theorem ae_summable_tailLayerTerm (M : ABKModel d) (m k : ℤ) (v : Fin d → ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (tailLayerTerm m k v omega) := by
  obtain ⟨i0, hi0m, hi0k⟩ : ∃ i0 : ℤ, m + 1 ≤ i0 ∧ k ≤ i0 :=
    ⟨max (m + 1) k, le_max_left _ _, le_max_right _ _⟩
  have hr0 : (0 : ℝ) ≤ Real.rpow 3 (M.gamma - 1) := Real.rpow_nonneg (by norm_num) _
  have hrpos : (0 : ℝ) < Real.rpow 3 (M.gamma - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hApos : (0 : ℝ) < (3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i0 : ℝ)) :=
    mul_pos (zpow_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  have hae := Provider.Orlicz.ae_summable_of_isBigOWith_gammaSigma
    (mu := (Cutoff.cutoffSampleLaw M).toMeasure) (sigma := 2)
    (X := fun (n : ℕ) (om : Cutoff.CutoffSample d) =>
      Support.shellW1InfGradNorm k
        (ShellField.translate (Support.triadicLatticePoint k v) (om.1 (i0 + (n : ℤ)))))
    (a := fun n : ℕ =>
      ((3 : ℝ) ^ (-k) * Real.rpow 3 ((M.gamma - 1) * (i0 : ℝ))) *
        Real.rpow 3 (M.gamma - 1) ^ n)
    (by norm_num) (fun _ _ => Support.shellW1InfGradNorm_nonneg _ _)
    (fun n => (((Support.measurable_shellW1InfGradNorm k).comp
      (ShellField.measurable_translate (Support.triadicLatticePoint k v))).comp
      ((measurable_pi_apply (i0 + (n : ℤ))).comp measurable_subtype_coe)).aemeasurable)
    (fun n => mul_pos hApos (pow_pos hrpos n))
    ((summable_geometric_of_lt_one hr0 (rpow_gamma_sub_one_lt_one M)).mul_left _)
    (fun n => by
      have hle : k ≤ i0 + (n : ℤ) := by omega
      have h := isBigOWith_gammaSigma_shellW1InfGradNorm_translate M hle
        (Support.triadicLatticePoint k v)
      rwa [layerScale_eq M k i0 n] at h)
  filter_upwards [hae] with omega hsum
  -- from the head-shifted `ℕ` family back to the full `ℤ` family
  have hemb : Function.Injective fun n : ℕ => m + 1 + (n : ℤ) := by
    intro a b hab
    have hab' : m + 1 + (a : ℤ) = m + 1 + (b : ℤ) := hab
    omega
  have hzero : ∀ x : ℤ, x ∉ Set.range (fun n : ℕ => m + 1 + (n : ℤ)) →
      tailLayerTerm m k v omega x = 0 := by
    intro x hx
    have hxm : ¬ m < x := by
      intro hlt
      refine hx ⟨(x - (m + 1)).toNat, ?_⟩
      change m + 1 + (((x - (m + 1)).toNat : ℕ) : ℤ) = x
      omega
    rw [tailLayerTerm, ite_eq_right hxm]
  refine (hemb.summable_iff hzero).mp ?_
  refine (summable_nat_add_iff (f := fun n : ℕ => tailLayerTerm m k v omega (m + 1 + (n : ℤ)))
    (i0 - (m + 1)).toNat).mp ?_
  refine hsum.congr fun n => ?_
  have hidx : m + 1 + ((n + (i0 - (m + 1)).toNat : ℕ) : ℤ) = i0 + (n : ℤ) := by
    have hshift : (((i0 - (m + 1)).toNat : ℕ) : ℤ) = i0 - (m + 1) :=
      Int.toNat_of_nonneg (by omega)
    push_cast [hshift]
    ring
  rw [hidx, tailLayerTerm, ite_eq_left (by omega : m < i0 + (n : ℤ))]

/-- **The upper shell series converges almost surely, at every cube
simultaneously.**  The index `ℤ × (Fin d → ℤ)` is countable, so the null sets of
`ae_summable_tailLayerTerm` may be unioned. -/
theorem ae_forall_summable_tailLayerTerm (M : ABKModel d) (m : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (k : ℤ) (v : Fin d → ℤ), Summable (tailLayerTerm m k v omega) := by
  have hpair : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ kv : ℤ × (Fin d → ℤ), Summable (tailLayerTerm m kv.1 kv.2 omega) :=
    ae_all_iff.2 fun kv => ae_summable_tailLayerTerm M m kv.1 kv.2
  filter_upwards [hpair] with omega hsum k v
  exact hsum (k, v)

/-! ## 5. The negated leg, pointwise -/

/-- Every layer gauge is even, so the `ℤ`-indexed layer term is literally
invariant under whole-sequence negation. -/
theorem tailLayerTerm_negateCutoffSample (m k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) (i : ℤ) :
    tailLayerTerm m k v (Cutoff.negateCutoffSample omega) i =
      tailLayerTerm m k v omega i := by
  by_cases h : m < i
  · rw [tailLayerTerm, tailLayerTerm, ite_eq_left h, ite_eq_left h, Cutoff.negateCutoffSample_val,
      ShellField.negateSequence_apply, translate_negate, shellW1InfGradNorm_negate]
  · rw [tailLayerTerm, tailLayerTerm, ite_eq_right h, ite_eq_right h]

/-- The finite layer block is `N`-invariant. -/
theorem tailLayerSum_negateCutoffSample (m k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) (L : ℤ) :
    tailLayerSum m k v (Cutoff.negateCutoffSample omega) L =
      tailLayerSum m k v omega L := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Cutoff.negateCutoffSample_val, ShellField.negateSequence_apply, translate_negate,
    shellW1InfGradNorm_negate]

/-- The canonical tail gauge is `N`-invariant. -/
theorem tailSeriesGauge_negateCutoffSample (m k : ℤ) (v : Fin d → ℤ)
    (omega : Cutoff.CutoffSample d) :
    tailSeriesGauge m k v (Cutoff.negateCutoffSample omega) =
      tailSeriesGauge m k v omega :=
  tsum_congr fun i => tailLayerTerm_negateCutoffSample m k v omega i

/-! ## 6. `hTae`, in the exact shape the transport asks for -/

/-- **`hTae` discharged at `T := tailSeriesGauge m`.**

Almost surely, the value of the upper shell series dominates every truncated
layer block, at the sample AND at the negated sample.  The second conjunct is
free: it is the first one composed with the pointwise `N`-invariances of §5, so
no law-level symmetry input is consumed. -/
theorem ae_tailLayerSum_le_tailSeriesGauge (M : ABKModel d) (m : ℤ) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
        tailLayerSum m k v omega L ≤ tailSeriesGauge m k v omega) ∧
      ∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
        tailLayerSum m k v (Cutoff.negateCutoffSample omega) L ≤
          tailSeriesGauge m k v (Cutoff.negateCutoffSample omega) := by
  filter_upwards [ae_forall_summable_tailLayerTerm M m] with omega hsum
  have hfirst : ∀ (k : ℤ) (v : Fin d → ℤ) (L : ℤ), m ≤ L →
      tailLayerSum m k v omega L ≤ tailSeriesGauge m k v omega := fun k v L _ =>
    tailLayerSum_le_tailSeriesGauge m k v omega (hsum k v) L
  refine ⟨hfirst, fun k v L hL => ?_⟩
  rw [tailLayerSum_negateCutoffSample, tailSeriesGauge_negateCutoffSample]
  exact hfirst k v L hL

/-! ## 7. The transport with `hTae` discharged -/

end

end Algsuperdiff.Section4.Provider.BoundsEaL
