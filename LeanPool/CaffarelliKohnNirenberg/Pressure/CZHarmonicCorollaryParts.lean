/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartDerivatives
public import LeanPool.CaffarelliKohnNirenberg.Pressure.OscillationLin34Solution

/-!
# The three parts of the local pressure on the inner ball (`cor:CZ-harmonic`)

The display `eq:CZ-harmonic` splits the localized pressure of
`prop:pressure-decomposition` into

* the Calderón–Zygmund part `p_CZ = p₁`,
* the harmonic part `p_har = p₂ + p₃ + p₄ + p₅ + p₆`, and
* the force part `p_f = p₇ + p₈`.

This file names the first and the third part, records that the three add up to
the pressure itself on the inner ball `B_{13ρ/20}(x₀)` (where the cutoff is
identically one), and exports the statement of `cor:CZ-harmonic` that needs no
further input: the harmonic part is weakly harmonic on that ball.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- The Calderón–Zygmund part `p_CZ` of `eq:CZ-harmonic`. -/
@[expose]
def czPressurePart (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) : Vec3 → ℝ :=
  pressureP1 η u c p f s

/-- The force part `p_f` of `eq:CZ-harmonic`. -/
@[expose]
def forcePressurePart (η : Vec3 → ℝ) (f : ParabolicPoint → Vec3) (s : ℝ) :
    Vec3 → ℝ :=
  pressureP7 η f s + pressureP8 η f s

/-- The tensor source `η U` of the Calderón–Zygmund part: the datum whose second
Riesz transform is `-p_CZ` in `eq:CZ-harmonic`. -/
@[expose]
def czPressureSource (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3) (c : ℝ → Vec3)
    (s : ℝ) : Fin 3 → Fin 3 → Vec3 → ℝ :=
  fun i j x => η x * pressureUTensor u c (x, s) i j

/-- The splitting `p = p_CZ + p_har + p_f` of `eq:CZ-harmonic` on the inner ball
`B_{13ρ/20}(x₀)`, where the cutoff of `lem:cutoff` is identically one. -/
theorem czHarmonic_decomposition_on_inner_ball
    (u : ParabolicPoint → Vec3) (c : ℝ → Vec3) (p : ParabolicPoint → ℝ)
    (f : ParabolicPoint → Vec3) (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ)
    {x : Vec3} (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) :
    p (x, s) =
      czPressurePart (mollifiedBallCutoff x₀ hρ) u c p f s x +
        harmonicPressurePart (mollifiedBallCutoff x₀ hρ) u c p s x +
        forcePressurePart (mollifiedBallCutoff x₀ hρ) f s x := by
  have hη : mollifiedBallCutoff x₀ hρ x = 1 :=
    mollifiedBallCutoff_eq_one_on_inner x₀ hρ hx
  have hpoint := pressure_decomposition_pointwise
    (mollifiedBallCutoff x₀ hρ) u c p f s x
  rw [hη, one_mul] at hpoint
  simp only [czPressurePart, forcePressurePart, harmonicPressurePart,
    Pi.add_apply]
  linarith only [hpoint]

/-- The harmonic part of `eq:CZ-harmonic` is weakly harmonic on the inner ball
`B_{13ρ/20}(x₀)` for almost every time of `J_ρ`. -/
theorem czHarmonic_harmonicPart_weaklyHarmonicOn_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s) := by
  filter_upwards [pressure_harmonic_potential_data_ae_of_sws_inner
    hsol hρ hsub] with s hs
  exact harmonicPressurePart_weaklyHarmonicOn_of_data hs

end CKN
