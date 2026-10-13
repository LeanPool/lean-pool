/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerZeroEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumScaledTransport

/-!
# ShellSumLayerDilation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-layer dilation `3^{2γk}` of `e.perturb.assumption`

`ShellSumLayerFlip.lean` reduces the shell-sum corrector energy to the diagonal
sum `Σ_{k ∈ (n,m]} ‖P 𝐟_k‖²` on the layer carrier, and
`ShellSumLayerZeroEnergy.lean` evaluates the `k = 0` term as `c⋆ (log 3)`.  This
module supplies the missing per-layer factor: for every `k`,

`‖P 𝐟_k‖ = 3^{γk} ‖P 𝐟_0‖`,  hence  `‖P 𝐟_k‖² = 3^{2γk} ‖P 𝐟_0‖²`.

## The route

The transport is carried by the **triadic dilation of a value path**

`pathScale γ k f = 3^{γk} · f(3^{-k} ·)`,

which is `ShellField.triadicScale γ k` read on the compact-open carrier
(`pathScale_valuePath`, a definitional identity).  Two facts about it are used.

* `map_pathScale_shellSumValuePathLaw` — it pushes the layer-`0` path law onto
  the layer-`k` path law.  This is exactly `e.diff.law.shift`, i.e. the frozen
  `ShellLawPrefix.marginal_scaling`, and **no independence is used**: the
  statement is about one marginal at a time.
* `pathScale_vadd` — it is equivariant only **up to the dilation `c = 3^k`** of
  the acting group, `Ψ (x +ᵥ f) = (3^k • x) +ᵥ Ψ f`.  This is why the ordinary
  naturality of `StationaryCarrierTransport.lean` does not apply and the
  dilating naturality of `ShellSumScaledTransport.lean` is needed.

The reduction of the *joint* projection to a *marginal* one is the already
proved naturality along the equivariant coordinate factor map `F ↦ F k`
(`measurePreserving_seqPathCoord`), the same device by which
`ShellSumLayerZeroEnergy.lean` evaluates the `k = 0` layer.

## What is supplied

* `pathScale`, `pathScale_apply`, `continuous_pathScale`, `measurable_pathScale`,
  `pathScale_valuePath`, `pathScale_vadd`.
* `shellSumValuePathLaw_pred_self` — the one-layer block law is the `valuePath`
  pushforward of the shell marginal.
* `map_pathScale_shellSumValuePathLaw`, `measurePreserving_pathScale`.
* `valuePathForcing_pathScale`, `carrierTransport_pathScale_shellSumForcingL2`.
* `norm_stationaryPotentialProjection_layerForcingL2` and its square
  `norm_sq_stationaryPotentialProjection_layerForcingL2` — **the per-layer
  dilation.**
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The triadic dilation on the value-path carrier -/

/-- The spatial dilation `x ↦ r • x`, as a continuous map. -/
def dilationMap (r : ℝ) : C(Vec d, Vec d) :=
  ⟨fun x => r • x, continuous_const_smul r⟩

/-- **The triadic dilation of a value path**, `f ↦ 3^{γk} f(3^{-k} ·)`.  This is
`ShellField.triadicScale γ k` read on the compact-open carrier. -/
def pathScale (gamma : ℝ) (k : ℤ) (f : C(Vec d, Mat d)) : C(Vec d, Mat d) :=
  (3 : ℝ) ^ (gamma * (k : ℝ)) • f.comp (dilationMap (((3 : ℝ) ^ k)⁻¹))

@[simp]
theorem pathScale_apply (gamma : ℝ) (k : ℤ) (f : C(Vec d, Mat d)) (x : Vec d) :
    pathScale gamma k f x
      = (3 : ℝ) ^ (gamma * (k : ℝ)) • f ((((3 : ℝ) ^ k)⁻¹) • x) :=
  rfl

theorem continuous_pathScale (gamma : ℝ) (k : ℤ) :
    Continuous (pathScale (d := d) gamma k) :=
  (continuous_const_smul _).comp (continuous_id.compCM continuous_const)

theorem measurable_pathScale (gamma : ℝ) (k : ℤ) :
    Measurable (pathScale (d := d) gamma k) :=
  (continuous_pathScale gamma k).measurable

/-- The dilation of a value path is the value path of the dilated shell field.
Both sides are the same term. -/
theorem pathScale_valuePath (gamma : ℝ) (k : ℤ) (j : ShellField d) :
    pathScale gamma k (ShellField.valuePath j)
      = ShellField.valuePath (ShellField.triadicScale gamma k j) :=
  rfl

/-- **The dilation is equivariant up to the dilation `3^k` of the acting
group.**  This is the reason `StationaryCarrierTransport.lean` does not apply
and `ShellSumScaledTransport.lean` does. -/
theorem pathScale_vadd (gamma : ℝ) (k : ℤ) (z : Vec d) (f : C(Vec d, Mat d)) :
    pathScale gamma k (z +ᵥ f) = (((3 : ℝ) ^ k) • z) +ᵥ pathScale (d := d) gamma k f := by
  refine ContinuousMap.ext fun x => ?_
  rw [pathScale_apply, ShellField.vadd_apply, ShellField.vadd_apply, pathScale_apply]
  congr 1
  rw [smul_add, smul_smul, inv_mul_cancel₀ (by positivity : ((3 : ℝ) ^ k) ≠ 0), one_smul]

/-! ### The layer laws and the dilation between them -/

/-- The one-layer block law `(k-1, k]` is the `valuePath` pushforward of the
`k`-th shell marginal. -/
theorem shellSumValuePathLaw_pred_self (M : ABKModel d) (k : ℤ) :
    (shellSumValuePathLaw M.P (k - 1) k).toMeasure
      = Measure.map (ShellField.valuePath (d := d))
          (ShellField.shellMarginalLaw M.P k).toMeasure := by
  rw [shellSumValuePathLaw_toMeasure]
  have h1 : shellSumValuePath (d := d) (k - 1) k
      = ShellField.valuePath ∘ fun F : ShellSeq d => F k :=
    funext fun omega => shellSumValuePath_pred_self k omega
  rw [h1, ← Measure.map_map ShellField.measurable_valuePath
    (ShellField.measurable_shellCoordinate k)]
  rfl

/-- **The triadic dilation pushes the layer-`0` law onto the layer-`k` law.**
The only input is `e.diff.law.shift`, i.e. the frozen
`ShellLawPrefix.marginal_scaling`; no independence enters. -/
theorem map_pathScale_shellSumValuePathLaw (M : ABKModel d) (k : ℤ) :
    Measure.map (pathScale (d := d) M.gamma k)
        (shellSumValuePathLaw M.P (0 - 1) 0).toMeasure
      = (shellSumValuePathLaw M.P (k - 1) k).toMeasure := by
  have hzero : (shellSumValuePathLaw M.P (0 - 1) 0).toMeasure
      = Measure.map (ShellField.valuePath (d := d))
          (ShellField.zeroShellLaw M.P).toMeasure := by
    rw [shellSumValuePathLaw_pred_self M 0, ShellField.shellMarginalLaw_zero]
  have hmarg : (ShellField.shellMarginalLaw M.P k).toMeasure
      = Measure.map (ShellField.triadicScale (d := d) M.gamma k)
          (ShellField.zeroShellLaw M.P).toMeasure := by
    rw [M.shellPrefix.marginal_scaling k, ProbabilityMeasure.toMeasure_map]
  rw [shellSumValuePathLaw_pred_self M k, hmarg, hzero,
    Measure.map_map (measurable_pathScale M.gamma k) ShellField.measurable_valuePath,
    Measure.map_map ShellField.measurable_valuePath
      (ShellField.measurable_triadicScale M.gamma k)]
  refine congrArg
    (fun g : ShellField d → C(Vec d, Mat d) =>
      Measure.map g (ShellField.zeroShellLaw M.P).toMeasure) ?_
  funext j
  exact (pathScale_valuePath M.gamma k j).symm

theorem measurePreserving_pathScale (M : ABKModel d) (k : ℤ) :
    MeasurePreserving (pathScale (d := d) M.gamma k)
      (shellSumValuePathLaw M.P (0 - 1) 0).toMeasure
      (shellSumValuePathLaw M.P (k - 1) k).toMeasure :=
  ⟨measurable_pathScale M.gamma k, map_pathScale_shellSumValuePathLaw M k⟩

/-! ### The forcing under the dilation -/

private theorem ofVec_matVecMul_smul_left (c : ℝ) (A : Mat d) (e : Vec d) :
    HilbertVec.ofVec (matVecMul (c • A) e) = c • HilbertVec.ofVec (matVecMul A e) := by
  have h : matVecMul (c • A) e = c • matVecMul A e := by
    funext i
    simp only [matVecMul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h]
  simpa only [HilbertVec.ofVecL_apply] using
    map_smul (HilbertVec.ofVecL d) c (matVecMul A e)

/-- The dilation multiplies the path forcing by `3^{γk}`: the forcing only sees
the value at the origin, which the spatial dilation fixes. -/
theorem valuePathForcing_pathScale (gamma : ℝ) (k : ℤ) (e : Vec d)
    (f : C(Vec d, Mat d)) :
    valuePathForcing e (pathScale gamma k f)
      = (3 : ℝ) ^ (gamma * (k : ℝ)) • valuePathForcing e f := by
  show HilbertVec.ofVec (matVecMul (pathScale gamma k f 0) e) = _
  rw [pathScale_apply, smul_zero]
  exact ofVec_matVecMul_smul_left _ _ _

theorem carrierTransport_pathScale_shellSumForcingL2 (M : ABKModel d) (e : Vec d)
    (k : ℤ) :
    carrierTransport (HilbertVec d) (measurePreserving_pathScale M k)
        (shellSumForcingL2 M e (k - 1) k)
      = (3 : ℝ) ^ (M.gamma * (k : ℝ)) • shellSumForcingL2 M e (0 - 1) 0 := by
  have hcomp := Lp.toLp_compMeasurePreserving (p := 2)
    (f := pathScale (d := d) M.gamma k)
    (memLp_two_valuePathForcing_shellSum M e (k - 1) k) (measurePreserving_pathScale M k)
  refine hcomp.trans ?_
  have hsmul : (3 : ℝ) ^ (M.gamma * (k : ℝ)) • shellSumForcingL2 M e (0 - 1) 0
      = ((memLp_two_valuePathForcing_shellSum M e (0 - 1) 0).const_smul
            ((3 : ℝ) ^ (M.gamma * (k : ℝ)))).toLp
          ((3 : ℝ) ^ (M.gamma * (k : ℝ)) • valuePathForcing e) :=
    (MemLp.toLp_const_smul _ _).symm
  rw [hsmul]
  refine (MemLp.toLp_eq_toLp_iff _ _).2 ?_
  exact Filter.Eventually.of_forall fun f => valuePathForcing_pathScale M.gamma k e f

/-- **The layer-`k` marginal corrector energy is `3^{2γk}` times the layer-`0`
one**, in norm form.  The dilating naturality of `ShellSumScaledTransport.lean`
is applied at `c = 3^k`. -/
theorem norm_stationaryPotentialProjection_shellSumForcingL2_layer (M : ABKModel d)
    (e : Vec d) (k : ℤ) :
    ‖stationaryPotentialProjection
        (μ := (shellSumValuePathLaw M.P (k - 1) k).toMeasure)
        (shellSumForcingL2 M e (k - 1) k)‖
      = (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
          ‖stationaryPotentialProjection
            (μ := (shellSumValuePathLaw M.P (0 - 1) 0).toMeasure)
            (shellSumForcingL2 M e (0 - 1) 0)‖ := by
  have hc : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have h := norm_stationaryPotentialProjection_carrierTransport_smul (d := d) hc
    (measurePreserving_pathScale M k)
    (fun z f => pathScale_vadd M.gamma k z f) (shellSumForcingL2 M e (k - 1) k)
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ (M.gamma * (k : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  rw [carrierTransport_pathScale_shellSumForcingL2 M e k, map_smul, norm_smul,
    Real.norm_of_nonneg hpos] at h
  exact h.symm

/-! ### From the joint layer carrier to the single-layer marginal -/

theorem carrierTransport_seqPathCoord_shellSumForcingL2 (M : ABKModel d) (e : Vec d)
    (k : ℤ) :
    carrierTransport (HilbertVec d) (measurePreserving_seqPathCoord M k)
        (shellSumForcingL2 M e (k - 1) k)
      = layerForcingL2 M e k := by
  have hcomp := Lp.toLp_compMeasurePreserving (p := 2)
    (f := fun F : ℤ → C(Vec d, Mat d) => F k)
    (memLp_two_valuePathForcing_shellSum M e (k - 1) k)
    (measurePreserving_seqPathCoord M k)
  refine hcomp.trans ?_
  exact (MemLp.toLp_eq_toLp_iff _ (memLp_two_layerForcing M e k)).2
    (Filter.Eventually.of_forall fun _ => rfl)

/-- The layer-`k` corrector energy on the joint layer carrier is the corrector
energy of the layer-`k` marginal.  This is the naturality of the stationary
potential projection along the equivariant coordinate factor map, exactly as in
the `k = 0` case of `ShellSumLayerZeroEnergy.lean`. -/
theorem norm_stationaryPotentialProjection_layerForcingL2_eq_shellSum (M : ABKModel d)
    (e : Vec d) (k : ℤ) :
    ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (layerForcingL2 M e k)‖
      = ‖stationaryPotentialProjection
          (μ := (shellSumValuePathLaw M.P (k - 1) k).toMeasure)
          (shellSumForcingL2 M e (k - 1) k)‖ := by
  have h := norm_stationaryPotentialProjection_carrierTransport (d := d)
    (measurePreserving_seqPathCoord M k)
    (fun (_ : Vec d) (_ : ℤ → C(Vec d, Mat d)) => rfl) (shellSumForcingL2 M e (k - 1) k)
  rwa [carrierTransport_seqPathCoord_shellSumForcingL2 M e k] at h

/-! ### The per-layer dilation of `e.perturb.assumption` -/

/-- **The per-layer dilation, in norm form.**  No normalization of `e` is
assumed. -/
theorem norm_stationaryPotentialProjection_layerForcingL2 (M : ABKModel d) (e : Vec d)
    (k : ℤ) :
    ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (layerForcingL2 M e k)‖
      = (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
          ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
            (layerForcingL2 M e 0)‖ := by
  rw [norm_stationaryPotentialProjection_layerForcingL2_eq_shellSum M e k,
    norm_stationaryPotentialProjection_layerForcingL2_eq_shellSum M e 0,
    norm_stationaryPotentialProjection_shellSumForcingL2_layer M e k]

/-- **The per-layer factor `3^{2γk}` of `e.perturb.assumption`.** -/
theorem norm_sq_stationaryPotentialProjection_layerForcingL2 (M : ABKModel d)
    (e : Vec d) (k : ℤ) :
    ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
        (layerForcingL2 M e k)‖ ^ 2
      = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          ‖stationaryPotentialProjection (μ := (seqPathLaw M.P).toMeasure)
            (layerForcingL2 M e 0)‖ ^ 2 := by
  have hpow : ((3 : ℝ) ^ (M.gamma * (k : ℝ))) ^ (2 : ℕ)
      = (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (k : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  rw [norm_stationaryPotentialProjection_layerForcingL2 M e k, mul_pow, hpow]

end

end Algsuperdiff.Section3.Provider.Corrector
