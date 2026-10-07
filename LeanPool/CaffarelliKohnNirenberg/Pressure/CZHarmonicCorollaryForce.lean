/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryForceLocal
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryForceSlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryParts
public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceDivergenceFreeBridge

/-!
# The force part of `cor:CZ-harmonic` needs only `div f = 0`

`def:sws` already forces the two Liouville inputs for `p_f = p₇ + p₈` used by
`cor:CZ-harmonic`: on almost every slice of `J_ρ` the sum is `L^{3/2}` on every
round ball about the origin, with a linear growth constant.  Consequently the
vanishing `p_f = 0` of `cor:CZ-harmonic` follows from the distributional
divergence-free condition on the force alone.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- On almost every slice of `J_ρ` the force part `p₇ + p₈` is `L^{3/2}` on every
round ball about the origin, with linear growth in the radius. -/
theorem czHarmonic_forcePart_local_growth_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ R : ℝ, 0 < R →
        MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      0 ≤ czHarmonicForceGrowthConstant z.1 hρ f s ∧
      ∀ R : ℝ, 0 < R →
        lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤
          czHarmonicForceGrowthConstant z.1 hρ f s * (1 + R) := by
  have hq : 5 / 2 < q := hsol.2.2.2.1
  filter_upwards [sws_force_memLp_slice_ae hsol hρ hsub] with s hs
  exact pressureP7_add_pressureP8_local_of_slice_memLp hρ
    (by linarith only [hq]) hs

/-- `p_f = 0` of `cor:CZ-harmonic`: for a suitable weak solution whose force is
divergence free in the sense of distributions on almost every slice, the force
part of `eq:CZ-harmonic` vanishes almost everywhere. -/
theorem czHarmonic_forcePart_eq_zero_of_divergenceFree_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hdiv : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      DistributionalDivergenceFree (fun x : Vec3 => f (x, s))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      forcePressurePart (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  simpa only [forcePressurePart] using
    pressure_force_eq_zero_of_sws hsol hρ hsub hdiv

end CKN
