/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryIdentification
public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZHarmonicCorollaryForce
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicPartBoundsAE

/-!
# `cor:CZ-harmonic`: Calderón–Zygmund part, harmonic part, force part

Fix a suitable weak solution of `def:sws` and a parabolic cylinder
`Q_ρ(z₀)` whose closure lies in the space-time domain.  With the cutoff `η` of
`lem:cutoff` and the ball average `c` of `prop:pressure-decomposition`, the
display `eq:CZ-harmonic` sets

```
p_CZ = p₁ = -RᵢRⱼ(η Uᵢⱼ),   p_har = p₂ + p₃ + p₄ + p₅ + p₆,   p_f = p₇ + p₈,
```

and the corollary asserts, for almost every `t ∈ J_ρ`:

* `p = p_CZ + p_har + p_f` on `B_{13ρ/20}(x₀)`;
* `p_CZ(·, t)` is the second Riesz transform of the tensor source `η U(·, t)`;
* `p_har(·, t)` is harmonic on `B_{13ρ/20}(x₀)`;
* `p_f(·, t) = 0` when `div f = 0` in the sense of distributions (which
  `def:sws` does not assume); and
* the interior derivative estimate `eq:har-Ck` on `B_{ρ/2}(x₀)`, with a
  constant `C₁₆(k)` fixed before the solution.

Only the Riesz identification of `p_CZ` still enters as a hypothesis, in the
exact shape in which it is currently produced: the tensor source `η U(·, t)` is
`L^{3/2}`, `p₁(·, t)` solves `Δ p₁ = ∂ᵢ∂ⱼ(η Uᵢⱼ)` against every smooth
compactly supported test, and the residual `p₁ - T(η U)` has linear `L^{3/2}`
growth on the round balls.  The splitting, the harmonicity, `eq:har-Ck` and the
two Liouville inputs for `p_f` need no extra input beyond `def:sws`; the force
part vanishes as soon as `div f = 0` on almost every slice.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
noncomputable section

namespace CKN

/-- The four slice statements of `cor:CZ-harmonic` that do not involve a
derivative constant: the splitting `eq:CZ-harmonic` on `B_{13ρ/20}(x₀)`, the
Riesz identification of `p_CZ`, the harmonicity of `p_har`, and the vanishing
of `p_f`. -/
theorem czHarmonic_decomposition_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} {C : ℝ → ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hG : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ i j, MemLp (czPressureSource (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) s i j)
        (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (hP1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p f s x *
          spatialLaplacian ψ x) volume →
        ∫ x, czPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x * spatialLaplacian ψ x =
          pressureSecondPairing (czPressureSource (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) s) ψ)
    (hP1Int : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p f s x *
          spatialLaplacian ψ x) volume)
    (hresidual : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      0 ≤ C s ∧
      (∀ R : ℝ, 0 < R →
        MemLp (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x -
          czPressureRieszPart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) s x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      ∀ R : ℝ, 0 < R →
        lpNorm (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) p f s x -
          czPressureRieszPart (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) s x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C s * (1 + R))
    (hdiv : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      DistributionalDivergenceFree (fun x : Vec3 => f (x, s))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ x ∈ euclideanBall z.1 (13 * ρ / 20),
          p (x, s) =
            czPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p f s x +
            harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p s x +
            forcePressurePart (mollifiedBallCutoff z.1 hρ) f s x) ∧
      czPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p f s =ᵐ[volume]
        czPressureRieszPart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) s ∧
      WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
            (fun y : Vec3 => u (y, t) j)) p s) ∧
      forcePressurePart (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 := by
  filter_upwards [hG, hP1, hP1Int, hresidual,
    czHarmonic_harmonicPart_weaklyHarmonicOn_ae_of_sws hsol hρ hsub,
    czHarmonic_forcePart_eq_zero_of_divergenceFree_ae_of_sws hsol hρ hsub
      hdiv] with s hsG hsP1 hsP1Int hsres hsharm hsforce
  refine ⟨fun x hx => czHarmonic_decomposition_on_inner_ball u _ p f z.1 hρ s hx,
    ?_, hsharm, hsforce⟩
  exact czHarmonic_czPart_eq_rieszPart hsres.1 hsG hsP1 hsP1Int
    hsres.2.1 hsres.2.2

/-- `cor:CZ-harmonic`.  For a suitable weak solution and a parabolic cylinder
whose closure lies in the domain, and for every order `k`, there is a constant
`C₁₆(k)` — fixed before the solution — such that for almost every `t ∈ J_ρ` the
splitting `eq:CZ-harmonic` holds on `B_{13ρ/20}(x₀)`, its Calderón–Zygmund part
is `-RᵢRⱼ(η Uᵢⱼ)(·, t)`, its harmonic part is weakly harmonic on
`B_{13ρ/20}(x₀)` and obeys the interior estimate `eq:har-Ck` on `B_{ρ/2}(x₀)`,
and its force part vanishes.  The `p₁` identification data enter in the shapes
in which they are produced; the force needs only its distributional
divergence-free condition, which `def:sws` does not assume. -/
theorem czHarmonic_corollary :
    ∀ k : ℕ, ∃ C₁₆ : ℝ, 0 ≤ C₁₆ ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ} {C : ℝ → ℝ},
        (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ i j, MemLp (czPressureSource (mollifiedBallCutoff z.1 hρ) u
            (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
              (fun y : Vec3 => u (y, t) j)) s i j)
            (ENNReal.ofReal ((3 : ℝ) / 2)) volume) →
        (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            Integrable (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p f s x *
              spatialLaplacian ψ x) volume →
            ∫ x, czPressurePart (mollifiedBallCutoff z.1 hρ) u
                (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) p f s x *
                spatialLaplacian ψ x =
              pressureSecondPairing
                (czPressureSource (mollifiedBallCutoff z.1 hρ) u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y : Vec3 => u (y, t) j)) s) ψ) →
        (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            Integrable (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p f s x *
              spatialLaplacian ψ x) volume) →
        (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          0 ≤ C s ∧
          (∀ R : ℝ, 0 < R →
            MemLp (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
                (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) p f s x -
              czPressureRieszPart (mollifiedBallCutoff z.1 hρ) u
                (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) s x)
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
          ∀ R : ℝ, 0 < R →
            lpNorm (fun x => czPressurePart (mollifiedBallCutoff z.1 hρ) u
                (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) p f s x -
              czPressureRieszPart (mollifiedBallCutoff z.1 hρ) u
                (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) s x)
              (ENNReal.ofReal (3 / 2 : ℝ))
              (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C s * (1 + R)) →
        (∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          DistributionalDivergenceFree (fun x : Vec3 => f (x, s))) →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          (∀ x ∈ euclideanBall z.1 (13 * ρ / 20),
              p (x, s) =
                czPressurePart (mollifiedBallCutoff z.1 hρ) u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y : Vec3 => u (y, t) j)) p f s x +
                harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y : Vec3 => u (y, t) j)) p s x +
                forcePressurePart (mollifiedBallCutoff z.1 hρ) f s x) ∧
          czPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p f s =ᵐ[volume]
            czPressureRieszPart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) s ∧
          WeaklyHarmonicOn (euclideanBall z.1 (13 * ρ / 20))
            (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
              (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) p s) ∧
          forcePressurePart (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0 ∧
          ∀ x ∈ vec3Ball z.1 (ρ / 2),
            ‖iteratedFDeriv ℝ k
                (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
                  (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                    (fun y : Vec3 => u (y, t) j)) p s) x‖ ≤
              C₁₆ * ρ ^ (-(2 + k : ℝ)) *
                (alpha u z ρ ^ 2 +
                  lpNorm (fun y : Vec3 => p (y, s))
                    (ENNReal.ofReal (3 / 2 : ℝ))
                    (volume.restrict (vec3Ball z.1 ρ))) := by
  intro k
  obtain ⟨C₁₆, hC₁₆, hCk⟩ := exists_harmonicPressurePart_Ck_ae_of_sws k
  refine ⟨C₁₆, hC₁₆, ?_⟩
  intro Ω I q u Du p f hsol z ρ C hρ hsub hG hP1 hP1Int hresidual hdiv
  filter_upwards [czHarmonic_decomposition_ae_of_sws hsol hρ hsub hG hP1
      hP1Int hresidual hdiv,
    hCk hsol hρ hsub] with s hs hsCk
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hsCk⟩

end CKN
