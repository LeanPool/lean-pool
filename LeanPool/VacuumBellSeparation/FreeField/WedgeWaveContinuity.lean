/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWaveL2
public import LeanPool.VacuumBellSeparation.FreeField.L2DominatedDifferentiation

/-!
# Strong L2 continuity of the actual wave on the closed rapidity strip

Continuity is in the original mass-shell Hilbert norm, including both
edges. A bounded neighborhood in real rapidity has a common integrable
square majorant, obtained from the full-strip integration-by-parts bound.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology

/-- Closed rapidity strip with membership specified by `{ζ | 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi}`. -/
def closedRapidityStrip : Set ℂ := {ζ | 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi}

/-- Wedge wave closed strip L² defined as `wedgeWaveL2 hm F hF ζ.1 ζ.2`. -/
noncomputable def wedgeWaveClosedStripL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) (ζ : closedRapidityStrip) :
    Lp ℂ 2 (oneParticleMeasure m) := wedgeWaveL2 hm F hF ζ.1 ζ.2

theorem continuous_wedgeWaveClosedStripL2 {m : ℝ} (hm : 0 < m) (F : RealTestFunction)
    (hF : tsupport F.1 ⊆ leftWedge 0) : Continuous (wedgeWaveClosedStripL2 hm F hF) := by
  rw [continuous_iff_continuousAt]
  intro ζ₀
  let B : ℝ := |ζ₀.1.re| + 1
  let A (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
    (2 * Real.exp B / dispersion m p) ^ 2 * maxCoordDerivNorm F 2
  let bound (p : EuclideanSpace ℝ (Fin 3)) : ℝ :=
    (64 * Real.exp B ^ 4 * maxCoordDerivNorm F 2 ^ 2) * (dispersion m p ^ 4)⁻¹
  have hbound : Integrable bound (oneParticleMeasure m) :=
    (integrable_inv_dispersion_pow_four_massShell hm).const_mul _
  have hB : ∀ᶠ ζ : closedRapidityStrip in 𝓝 ζ₀, |ζ.1.re| ≤ B := by
    have hc : Continuous (fun ζ : closedRapidityStrip => |ζ.1.re|) :=
      (Complex.continuous_re.comp continuous_subtype_val).abs
    exact (hc.continuousAt.eventually_lt_const (show |ζ₀.1.re| < B by
      dsimp [B]; linarith)).mono fun ζ hζ => hζ.le
  have hrep (ζ : closedRapidityStrip) :
      (wedgeWaveClosedStripL2 hm F hF ζ - wedgeWaveClosedStripL2 hm F hF ζ₀ :
        Lp ℂ 2 (oneParticleMeasure m)) =ᵐ[oneParticleMeasure m]
      fun p => wedgeWave m F ζ.1 p - wedgeWave m F ζ₀.1 p := by
    filter_upwards [Lp.coeFn_sub (wedgeWaveClosedStripL2 hm F hF ζ)
      (wedgeWaveClosedStripL2 hm F hF ζ₀), wedgeWaveL2_ae hm F hF ζ.1 ζ.2,
      wedgeWaveL2_ae hm F hF ζ₀.1 ζ₀.2] with p hsub hζ hzero
    apply hsub.trans
    change wedgeWaveL2 hm F hF ζ.1 ζ.2 p - wedgeWaveL2 hm F hF ζ₀.1 ζ₀.2 p = _
    rw [hζ, hzero]
  have hlim : Tendsto
      (fun ζ => wedgeWaveClosedStripL2 hm F hF ζ - wedgeWaveClosedStripL2 hm F hF ζ₀)
      (𝓝 ζ₀) (𝓝 (0 : Lp ℂ 2 (oneParticleMeasure m))) := by
    apply tendsto_L2_zero_of_dominated_representatives (oneParticleMeasure m)
      (β := closedRapidityStrip) (l := 𝓝 ζ₀)
      (fun ζ : closedRapidityStrip =>
        wedgeWaveClosedStripL2 hm F hF ζ - wedgeWaveClosedStripL2 hm F hF ζ₀)
      (fun (ζ : closedRapidityStrip) (p : EuclideanSpace ℝ
        (Fin 3)) => wedgeWave m F ζ.1 p - wedgeWave m F ζ₀.1 p) hrep bound hbound
    · filter_upwards [hB] with ζ hζ
      exact Eventually.of_forall fun p => by
        have h₁ : ‖wedgeWave m F ζ.1 p‖ ≤ A p :=
          norm_wedgeWave_closedStrip_le hm F hF ζ.2 hζ p
        have h₂ : ‖wedgeWave m F ζ₀.1 p‖ ≤ A p :=
          norm_wedgeWave_closedStrip_le hm F hF ζ₀.2
            (show |ζ₀.1.re| ≤ B by dsimp [B]; linarith) p
        have hd : ‖wedgeWave m F ζ.1 p - wedgeWave m F ζ₀.1 p‖ ≤ 2 * A p :=
          (norm_sub_le _ _).trans (by linarith)
        calc
          ‖wedgeWave m F ζ.1 p - wedgeWave m F ζ₀.1 p‖ ^ 2 ≤ (2 * A p) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hd 2
          _ = bound p := by dsimp [A, bound]; ring
    · exact Eventually.of_forall fun p => by
        have ht := (hasDerivAt_wedgeWave m F p ζ₀.1).continuousAt.tendsto.comp
          continuous_subtype_val.continuousAt.tendsto
        simpa only [sub_self, Function.comp_apply] using ht.sub (tendsto_const_nhds
          (x := wedgeWave m F ζ₀.1 p))
  have h := hlim.add_const (wedgeWaveClosedStripL2 hm F hF ζ₀)
  simpa only [ContinuousAt, sub_add_cancel, zero_add] using h

end VacuumBellSeparation
