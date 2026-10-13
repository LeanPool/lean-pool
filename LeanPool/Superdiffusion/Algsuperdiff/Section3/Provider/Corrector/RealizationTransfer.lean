/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.Realization
public import LeanPool.HighContrastHomogenization.Support.Multiscale.NormalizedNorms

/-!
# RealizationTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the stationary product-average transfer

This file proves item of the corrector-limit design: for stationary
square-integrable fields `X`, `Y` on the abstract carrier and *any* triadic
cube `Q`,

`E[ ⨍_Q (realize X) · (realize Y) ] = E[X · Y]`,

together with the corollaries that hang off it, in particular

`E[ ‖realize X‖²_{L²(Q)} ] = E[|X|²]`.

This is the identity that converts every cube-averaged quantity appearing in
`l.approximation.stationary.by.local` and `l.corrector.limit` into a quantity of
the abstract stationary Hilbert space, where
`Algsuperdiff/Section3/Provider/Corrector/StationaryCorrector.lean` operates.

CoarseGraining does not supply this.  Its stationarity transfer
`Homogenization.Book.Ch04.integral_eq_of_isTranslationCovariantR_of_stationary`
moves a set-indexed observable along an *integer* translation under
`IsStationaryR`, which is the wrong shape twice over: it is discrete, and it
moves the set rather than the field inside a spatial average.

The proof is Fubini on `μ ⊗ (volume.restrict (cubeSet Q))` — legitimate exactly
because of the joint measurability established in `Realization.lean` — followed
by the real-shift Koopman transfer `integral_comp_const_vadd` for each fixed
point of the cube, which makes the inner integral constant in the space
variable.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **, the stationary product-average transfer.**  The expectation of the cube
average of the pointwise product of two realizations equals the expectation of
the product itself, for every triadic cube.  In the notation of ABK26,
`E[⨍_{cu_K} X · Y] = E[X · Y]`. -/
theorem integral_cubeAverage_vecDot_realize (Q : TriadicCube d)
    {X Y : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hYm : StronglyMeasurable Y)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ∫ ω, cubeAverage Q (fun x => vecDot (realize X ω x).toVec (realize Y ω x).toVec) ∂μ
      = ∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂μ := by
  have := isFiniteMeasure_volume_restrict_cubeSet (d := d) Q
  have hswap :
      ∫ ω, (∫ x, vecDot (realize X ω x).toVec (realize Y ω x).toVec
            ∂volume.restrict (cubeSet Q)) ∂μ
        = ∫ x, (∫ ω, vecDot (realize X ω x).toVec (realize Y ω x).toVec ∂μ)
            ∂volume.restrict (cubeSet Q) :=
    integral_integral_swap (integrable_prod_vecDot_realize Q hXm hYm hX hY)
  have hconst : ∀ x : Vec d,
      (∫ ω, vecDot (realize X ω x).toVec (realize Y ω x).toVec ∂μ)
        = ∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂μ := fun x =>
    integral_comp_const_vadd (fun ω => vecDot (X ω).toVec (Y ω).toVec) x
  calc
    ∫ ω, cubeAverage Q (fun x => vecDot (realize X ω x).toVec (realize Y ω x).toVec) ∂μ
        = ∫ ω, (cubeVolume Q)⁻¹ *
            (∫ x, vecDot (realize X ω x).toVec (realize Y ω x).toVec
              ∂volume.restrict (cubeSet Q)) ∂μ := by
          simp only [cubeAverage]
    _ = (cubeVolume Q)⁻¹ *
          ∫ ω, (∫ x, vecDot (realize X ω x).toVec (realize Y ω x).toVec
            ∂volume.restrict (cubeSet Q)) ∂μ := integral_const_mul _ _
    _ = (cubeVolume Q)⁻¹ *
          ∫ x, (∫ ω, vecDot (realize X ω x).toVec (realize Y ω x).toVec ∂μ)
            ∂volume.restrict (cubeSet Q) := by rw [hswap]
    _ = (cubeVolume Q)⁻¹ *
          ∫ _x : Vec d, (∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂μ)
            ∂volume.restrict (cubeSet Q) := by simp only [hconst]
    _ = ∫ ω, vecDot (X ω).toVec (Y ω).toVec ∂μ := by
          rw [integral_const, Measure.real_def, Measure.restrict_apply_univ,
            volume_cubeSet_toReal, smul_eq_mul,
            inv_mul_cancel_left₀ (cubeVolume_pos Q).ne']

/-- **, quadratic form.**  `E[⨍_Q |realize X|²] = E[|X|²]`. -/
theorem integral_cubeAverage_normSq_realize (Q : TriadicCube d)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∫ ω, cubeAverage Q (fun x => ‖realize X ω x‖ ^ 2) ∂μ = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  have hpt : ∀ v : HilbertVec d, vecDot v.toVec v.toVec = ‖v‖ ^ 2 := fun v =>
    (HilbertVec.inner_def v v).symm.trans (real_inner_self_eq_norm_sq v)
  simpa only [hpt] using integral_cubeAverage_vecDot_realize Q hXm hXm hX hX

/-- A realization that is square integrable on a cube is square integrable for the
normalized cube measure, the measure underlying CoarseGraining's `cubeLpNorm`. -/
theorem memLp_normalizedCubeMeasure_of_memHilbertVectorL2 {Q : TriadicCube d}
    {f : Vec d → HilbertVec d} (hf : MemHilbertVectorL2 (cubeSet Q) f) :
    MemLp f 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure, cubeMeasure]
  exact hf.smul_measure ENNReal.ofReal_ne_top

end

end Algsuperdiff.Section3.Provider.Corrector
