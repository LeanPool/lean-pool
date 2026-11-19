/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticHamiltonianItoTerminal.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousGradientIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRestrictedIto
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticGeneratorCompensator
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianRestrictedVolterra

/-! Actual Hamiltonian Itô identities for the canonical Brownian maximal solution. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianHamiltonian_ito_at_surviving_time
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T S : ℝ≥0) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      ∀ᵐ ω ∂P, S ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω →
        ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T S ω)-
          ginibreHamiltonian n z = J S ω+
            ∫ s in (0 : ℝ)..S, ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n)
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let U : Set (Configuration n) := {x | CollisionFree x}
  let K := ginibreHamiltonianSublevel n R
  have hU : IsOpen U := isOpen_collisionFree n
  have hf : ContDiffOn ℝ 2 (ginibreHamiltonian n) U := fun x hx =>
    ((ginibreHamiltonian_contDiffAt n x hx).of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ENat)
                                                        ≤ ⊤ from le_top))).contDiffWithinAt
  have hK : IsCompact K := ginibreHamiltonianSublevel_isCompact hn R
  have hKU : K ⊆ U := fun x hx => hx.1
  have hRange : ∀ t ω, X t ω ∈ K := ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR
      T
  have hCont : ∀ ω, Continuous (fun t => X t ω) :=
      ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T
  have hX := ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJP, hJEnd⟩ :=
      ginibreCompactProcess_continuous_gradient_integral_exists
    n B P hB hind α X hX hCont (ginibreHamiltonian n) U K hU hf hK hKU hRange S
  obtain ⟨M, hM, hbound⟩ := ginibreBrownianHamiltonianStoppedDrift_bounded hn α z hz B R hR T
  let b := fun (s : ℝ) ω => ginibreLangevinDrift n α (X s.toNNReal ω)
  have hb : ∀ ω, Continuous (fun s => b s ω) := ginibreBrownianHamiltonianStoppedDrift_continuous hn
      α z hz B R hR T
  have hEq := ginibreCompactVolterra_restricted_ito_identify n B P hB hind α X hX hCont
    (ginibreHamiltonian n) U K hU hf hK hKU hRange S b (fun ω => (hb ω).continuousOn)
    M hM.le (fun s hs ω => hbound s ω)
    {ω | S ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω}
    (ginibreBrownianHamiltonianBoundedStop_survival_measurable hn α z hz B P hB R hR T S)
    (ginibreBrownianHamiltonianStoppedProcess_restricted_volterra hn α z hz B P hB R hR T S)
    (J S) hJEnd
  refine ⟨J, hJM, hJC, hJL, hJ0,?_⟩
  filter_upwards [hEq] with ω hω
  intro hs
  have hh := hω hs
  have hg := ginibreConfigurationTestCompensator_eq_generator hn α X hCont
    (fun t ω => (hRange t ω).1) (ginibreHamiltonian n) U hU hf
    (fun t ω => hKU (hRange t ω)) S ω
  unfold ginibreConfigurationTestCompensator at hg
  have hinit : X 0 ω=z := ginibreBrownianHamiltonianStoppedProcess_initial n α z hz B R T ω
  rw [hinit] at hg hh
  dsimp [b] at hh
  change ginibreHamiltonian n (X S ω)-ginibreHamiltonian n z=J S ω+
    ∫ s in (0 : ℝ)..S, ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) (X s.toNNReal ω)
  linarith
end
end GinibrePoincare
