/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralTiltOUSurvival.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltOUSublevel

/-!
# Ginibre Brownian integral tilt OU survival

Part of the stochastic calculus foundations development of the
Ginibre Poincaré formalization.

Main results: `ginibreActualOU_sublevel_killed_coupling_exists`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Deterministic consequence of the genuine stopped coupling: literal OU
survival identifies the complete original canonical path through the horizon.
The stochastic witnesses are constructed in
`ginibreActualOU_sublevel_tilted_canonical_prefix_exists`. -/
theorem ginibreOU_canonical_prefix_eq_reference_on_survival {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (θ : Ω → ℝ≥0)
    (hStopped : ∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω)
    (hActual : ∀ ω, θ ω = ginibreHamiltonianOUSublevelStop n α z B R T ω)
    (N : Ω → ℝ → Configuration n) (ω : Ω)
    (hCanonical : ∀ t : ℝ≥0, t≤θ ω → ginibreDrivenMaximalValue n α (N ω) z t=Y t ω)
    (hStay : ∀ t ≤ T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
      ginibreHamiltonianOUSublevelDomain n R) :
    ∀ t ≤ T, ginibreDrivenMaximalValue n α (N ω) z t=
      ginibreHamiltonianOUReferenceProcess n α z B t ω := by
  obtain ⟨hθ, hY⟩ := ginibreHamiltonianOUSublevelStopped_eq_reference_of_stays
    n α z B R T Y θ hStopped hActual ω hStay
  intro t ht
  exact (hCanonical t (hθ ▸ ht)).trans (hY t ht)

/-- Literal survival events coincide under the actual canonical stopped
coupling, because a failed OU survival hits the closed complement at the
stopping time, including an exit at the terminal endpoint. -/
theorem ginibreOU_canonical_survival_iff_reference_survival {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (θ : Ω → ℝ≥0)
    (hStopped : ∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω)
    (hActual : ∀ ω, θ ω = ginibreHamiltonianOUSublevelStop n α z B R T ω)
    (N : Ω → ℝ → Configuration n) (ω : Ω) (hθ : θ ω ≤ T)
    (hCanonical : ∀ t : ℝ≥0, t≤θ ω → ginibreDrivenMaximalValue n α (N ω) z t=Y t ω) :
    (∀ t≤T, ginibreDrivenMaximalValue n α (N ω) z t ∈ ginibreHamiltonianOUSublevelDomain n R) ↔
    (∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ ginibreHamiltonianOUSublevelDomain n
        R) := by
  constructor
  · intro hStay
    by_contra hNot
    have hExit := ginibreHamiltonianOUSublevelStop_mem_complement_of_not_stays
      n α z B R T ω hNot
    have hEq : ginibreDrivenMaximalValue n α (N ω) z (θ ω)=
        ginibreHamiltonianOUReferenceProcess n α z B (θ ω) ω := by
      rw [hCanonical _ le_rfl, hStopped, min_self]
    have hMem := hStay (θ ω) hθ
    rw [hEq, hActual ω] at hMem
    exact hExit hMem
  · intro hStay t ht
    rw [ginibreOU_canonical_prefix_eq_reference_on_survival n α z B R T Y θ
      hStopped hActual N ω hCanonical hStay t ht]
    exact hStay t ht

/-- Unconditional genuine killed coupling on a prescribed horizon: the
normalized interaction likelihood produces Brownian corrected noise, equal
literal survival events, and the complete canonical original path equals
the actual OU reference on that event. -/
theorem ginibreActualOU_sublevel_killed_coupling_exists {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z < R) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n, ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω))
      Q.map (fun ω (t : Icc (0 : ℝ≥0) T) i => ginibreInteractionCorrectedBrownian n α B Y i t.val
          ω)=
        P.map (fun ω (t : Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω) ∧
      ∀ᵐ ω ∂Q,
        let N := ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α
            ω
        ((∀ t≤T, ginibreDrivenMaximalValue n α N z t ∈ ginibreHamiltonianOUSublevelDomain n R) ↔
          (∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
              ginibreHamiltonianOUSublevelDomain n R)) ∧
        ((∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
            ginibreHamiltonianOUSublevelDomain n R) →
          (∀ t≤T, ginibreDrivenMaximalValue n α N z t=ginibreHamiltonianOUReferenceProcess n α z B t
              ω) ∧
          brownianVectorExponentialIntegralDensity
            (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω =
            Real.exp (ginibreInteractionPotential n z)*
              (ginibreHamiltonianGradientPathWeight n α T (fun s => Y s.toNNReal ω)/
                ginibreQuadraticGradientPathWeight n α T (fun s => Y s.toNNReal ω))) := by
  obtain ⟨Y, hYC, hCF, hY0, θ, hStop, hθ, hStopped, hActual, M, hM, hDi, hD1, hLaw, hCan, hAction⟩
      :=
    ginibreActualOU_sublevel_tilted_canonical_prefix_exists hn B P hB hind α z hz R hR T hT
  refine ⟨Y, M, hDi, hD1, hLaw,?_⟩
  filter_upwards [hCan, hAction] with ω hC hA
  refine ⟨ginibreOU_canonical_survival_iff_reference_survival n α z B R T Y θ
    hStopped hActual _ ω (hθ ω).2 hC,?_⟩
  intro hStay
  have hEq := ginibreOU_canonical_prefix_eq_reference_on_survival n α z B R T Y θ
    hStopped hActual _ ω hC hStay
  have hθT : θ ω=T := (hActual ω).trans
    (ginibreHamiltonianOUSublevelStop_eq_horizon_of_stays n α z B R T ω hStay)
  exact ⟨hEq, hA T (hθT ▸ le_rfl)⟩

end
end GinibrePoincare
