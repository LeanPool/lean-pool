/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianMaximalLevel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalBlowup

/-! Finite maximal lifetimes cross every Hamiltonian level before death. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenMaximalPath_hamiltonian_continuousOn (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) :
    ContinuousOn (fun t => ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z t))
      (ginibreDrivenMaximalDomain n α N z) := by
  intro t ht
  exact (ginibreHamiltonian_contDiffAt n _
    (ginibreDrivenMaximalPath_equation ht).1).continuousAt.comp_continuousWithinAt
      (ginibreDrivenMaximalPath_continuousOn n α N z t ht)

theorem ginibreDrivenMaximalLifetime_finite_hamiltonian_level {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z)
    (hfin : ginibreDrivenMaximalLifetime n α N z ≠ ⊤)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) :
    ∃ t ∈ Ico 0 (ginibreDrivenMaximalLifetime n α N z).toReal,
      ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z t) = R := by
  obtain ⟨b, hb, hbR⟩ := ginibreDrivenMaximalLifetime_finite_hamiltonian_unbounded
    hn α N hN hN0 z hz hfin R
  have hc := (ginibreDrivenMaximalPath_hamiltonian_continuousOn n α N z).mono
    (show Icc 0 b ⊆ ginibreDrivenMaximalDomain n α N z from by
      rw [ginibreDrivenMaximalDomain_eq_Ico_of_finite hfin]
      intro u hu
      exact ⟨hu.1, hu.2.trans_lt hb.2⟩)
  have hzero := ginibreDrivenMaximalPath_initial n α N hN hN0 z hz
  obtain ⟨t, ht, hval⟩ := intermediate_value_Icc hb.1 hc
    (show R ∈ Icc (ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z 0))
      (ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z b)) from by
      rw [hzero]
      exact ⟨hR, hbR.le⟩)
  exact ⟨t, ⟨ht.1, ht.2.trans_lt hb.2⟩, hval⟩

end
end GinibrePoincare
