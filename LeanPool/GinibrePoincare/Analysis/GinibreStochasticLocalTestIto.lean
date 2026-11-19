/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticLocalTestIto.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactItoMartingale
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticHamiltonianItoTerminal

/-! # Localized Itô martingale for a C² test

Hamiltonian localization places the stopped process in a compact subset of
the collision-free open set. This allows a test with C² regularity on that
open set, even when it has no smooth extension across collisions.

The proof checks continuity, adaptation, the bounded drift and the Volterra
equation, then applies `ginibreCompactVolterra_continuous_ito_martingale_exists`.
Its test compensator is identified with the concrete generator. Evaluating
the resulting pathwise identity at the bounded stop gives the terminal
formula. Use `GinibreStochasticLocalTestItoIntegral` when the downstream
argument also needs the explicit gradient-sum approximation of the integral. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownianMaximalProcess_local_test_ito_martingale_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : ContDiffOn ℝ 2 f {x | CollisionFree x}) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        f (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-
          f z = J t ω+
            ∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α f
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) ∧
      ((fun ω => f (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω)) =ᵐ[P]
        (fun ω => f z+J (ginibreBrownianHamiltonianBoundedStop n α z B R T ω) ω+
          ∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
            ginibreRealPaperSpeedGenerator n α f
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω))) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  let U : Set (Configuration n) := {x | CollisionFree x}
  let K := ginibreHamiltonianSublevel n R
  let b := fun (s : ℝ) ω => ginibreLangevinDrift n α (X s.toNNReal ω)
  have hU : IsOpen U := isOpen_collisionFree n
  have hfo : ContDiffOn ℝ 2 f U := hf
  have hK : IsCompact K := ginibreHamiltonianSublevel_isCompact hn R
  have hKU : K ⊆ U := fun x hx => hx.1
  have hRange : ∀ t ω, X t ω ∈ K := ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR
      T
  have hCont : ∀ ω, Continuous (fun t => X t ω) :=
      ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T
  have hX := ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T
  have hb : ∀ ω, Continuous (fun s => b s ω) := ginibreBrownianHamiltonianStoppedDrift_continuous hn
      α z hz B R hR T
  obtain ⟨M, hM, hbound⟩ := ginibreBrownianHamiltonianStoppedDrift_bounded hn α z hz B R hR T
  have hσ : Measurable σ := measurable_of_Ici (fun t =>
    ginibreBrownianHamiltonianBoundedStop_survival_measurable hn α z hz B P hB R hR T t)
  have hσT (ω : Ω) : σ ω ≤ T := ginibreDrivenHamiltonianBoundedStop_le n α _ z R T
  have hVE : ∀ᵐ ω ∂P, ∀ t ≤ σ ω, X t ω=X 0 ω+
      (ginibreConfigurationBrownianNoise n B α ω t-ginibreConfigurationBrownianNoise n B α ω 0)+
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω := by
    filter_upwards [ginibreBrownianHamiltonianStoppedProcess_equation_ae hn α z hz B P hB R hR T,
      ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω he hNoise
    intro t ht
    have hh := (he t).2
    rw [min_eq_left ht] at hh
    have hzero : ginibreConfigurationBrownianNoise n B α ω 0=0 := by
      rw [← hNoise 0]
      exact (ginibreBrownianFullContinuousNoise n B α ω).property
    rw [hzero, sub_zero]
    have hinit : X 0 ω=z := ginibreBrownianHamiltonianStoppedProcess_initial n α z hz B R T ω
    rw [hinit]
    exact hh
  obtain ⟨J, hJM, hJC, hJL, hJ0, hEq⟩ := ginibreCompactVolterra_continuous_ito_martingale_exists
    n B P hB hind α X hX hCont f U K hU hfo hK hKU hRange T b hb
    M hM.le (fun s hs ω => hbound s ω) σ hσ hσT hVE
  have hIto : ∀ᵐ ω ∂P, ∀ t ≤ σ ω, f (X t ω)-f z=J t ω+
      ∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α f (X s.toNNReal ω) := by
    filter_upwards [hEq] with ω hω
    intro t ht
    have hh := hω t ht
    have hg := ginibreConfigurationTestCompensator_eq_generator hn α X hCont
      (fun t ω => (hRange t ω).1) f U hU hfo
      (fun t ω => hKU (hRange t ω)) t ω
    rw [hg] at hh
    have hinit : X 0 ω=z := ginibreBrownianHamiltonianStoppedProcess_initial n α z hz B R T ω
    rw [hinit] at hh
    linarith
  refine ⟨J, hJM, hJC, hJL, hJ0, hIto,?_⟩
  filter_upwards [hIto] with ω hω
  have hh := hω (σ ω) le_rfl
  have hEnd : X (σ ω) ω=X T ω := by
    change ginibreBrownianMaximalProcess n α z B (min (σ ω) (σ ω)) ω =
      ginibreBrownianMaximalProcess n α z B (min T (σ ω)) ω
    rw [min_self, min_eq_right (hσT ω)]
  rw [hEnd] at hh
  linarith
end
end GinibrePoincare
