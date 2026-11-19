/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianLevelLocalization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianFirstLevel

/-! Hamiltonian level localization gives an actual compact collision-free stopped range. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreDrivenHamiltonianFirstLevel_hamiltonian_le {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} (hN : Continuous N) (hN0 : N 0 = 0)
    {z : Configuration n} (hz : CollisionFree z) {R : ℝ}
    (hR : ginibreHamiltonian n z ≤ R) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z)
    (hτ : (t : ℝ≥0∞) ≤ ginibreDrivenHamiltonianFirstLevel n α N z R) :
    ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z t) ≤ R := by
  by_contra hh
  have hgt := lt_of_not_ge hh
  let f := fun u : ℝ≥0 => ginibreHamiltonian n
    (ginibreDrivenMaximalValue n α N z (min u t))
  have hc : Continuous f := ginibreDrivenHamiltonianPrefix_continuous t ht
  have hzero : f 0 = ginibreHamiltonian n z := by
    have hi := ginibreDrivenMaximalPath_initial n α N hN hN0 z hz
    change ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z (min 0 t)) = _
    rw [min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)]
    simpa only [ginibreDrivenMaximalPath, Real.toNNReal_zero] using congrArg (ginibreHamiltonian n)
        hi
  obtain ⟨j, hj, hjR⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ t)
    hc.continuousOn (show R ∈ Icc (f 0) (f t) from by
      simpa only [hzero, f, min_self] using (show R ∈ Icc (ginibreHamiltonian n z)
        (ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z t)) from ⟨hR, hgt.le⟩))
  have hjt : j < t := lt_of_le_of_ne hj.2 (by
    intro he
    have hbad : ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z t) = R := by
      simpa only [he, f, min_self] using hjR
    linarith)
  have hjhit : j ∈ ginibreDrivenLevelHit n α N z R := by
    refine ⟨(ENNReal.coe_le_coe.mpr hj.2).trans_lt ht, ?_⟩
    simpa only [f, min_eq_left hj.2] using hjR.ge
  have hfirst := (ginibreDrivenHamiltonianFirstLevel_le_iff j).mpr ⟨j, hjhit, le_rfl⟩
  have hle : t ≤ j := ENNReal.coe_le_coe.mp (hτ.trans hfirst)
  exact (not_lt_of_ge hle) hjt

/-- The first time the Hamiltonian of the driven maximal Ginibre path reaches the level `R`,
truncated at the horizon `T`. -/
def ginibreDrivenHamiltonianBoundedStop (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) (R : ℝ) (T : ℝ≥0) : ℝ≥0 :=
  (min (T : ℝ≥0∞) (ginibreDrivenHamiltonianFirstLevel n α N z R)).toNNReal

theorem ginibreDrivenHamiltonianBoundedStop_lt_lifetime {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    (ginibreDrivenHamiltonianBoundedStop n α N z R T : ℝ≥0∞) <
      ginibreDrivenMaximalLifetime n α N z := by
  have hfin : min (T : ℝ≥0∞) (ginibreDrivenHamiltonianFirstLevel n α N z R) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [ginibreDrivenHamiltonianBoundedStop, ENNReal.coe_toNNReal hfin]
  by_cases hτ : ginibreDrivenHamiltonianFirstLevel n α N z R ≤ (T : ℝ≥0∞)
  · have hh := (ginibreDrivenHamiltonianFirstLevel_le_iff T).mp hτ
    have hne : (ginibreDrivenLevelHit n α N z R).Nonempty := by
      obtain ⟨t, ht, _⟩ := hh
      exact ⟨t, ht⟩
    obtain ⟨t, he, ht⟩ := ginibreDrivenHamiltonianFirstLevel_attained hne
    rw [min_eq_right hτ, he]
    exact ht.1
  · rw [min_eq_left (le_of_not_ge hτ)]
    by_contra hnot
    have hd : ginibreDrivenMaximalLifetime n α N z ≤ (T : ℝ≥0∞) := le_of_not_gt hnot
    exact hτ ((ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime hn α N hN hN0 z hz R hR T).mpr
        (Or.inl hd))

theorem ginibreDrivenHamiltonianBoundedStop_coe (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) (R : ℝ) (T : ℝ≥0) :
    (ginibreDrivenHamiltonianBoundedStop n α N z R T : ℝ≥0∞) =
      min (T : ℝ≥0∞) (ginibreDrivenHamiltonianFirstLevel n α N z R) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))

theorem ginibreDrivenHamiltonianBoundedStop_le (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) (R : ℝ) (T : ℝ≥0) :
    ginibreDrivenHamiltonianBoundedStop n α N z R T ≤ T := by
  apply ENNReal.coe_le_coe.mp
  rw [ginibreDrivenHamiltonianBoundedStop_coe]
  exact min_le_left _ _

theorem ginibreDrivenHamiltonianBoundedStop_range {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z ≤ R) (T t : ℝ≥0) :
    ginibreDrivenMaximalValue n α N z
      (min t (ginibreDrivenHamiltonianBoundedStop n α N z R T)) ∈ ginibreHamiltonianSublevel n R :=
          by
  let s := ginibreDrivenHamiltonianBoundedStop n α N z R T
  have hs := ginibreDrivenHamiltonianBoundedStop_lt_lifetime hn α N hN hN0 z hz R hR T
  have ht : ((min t s : ℝ≥0) : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z :=
    (ENNReal.coe_le_coe.mpr (min_le_right t s)).trans_lt hs
  have hprops := ginibreDrivenMaximalPath_equation (n := n) (α := α) (N := N) (z := z)
    (t := ((min t s : ℝ≥0) : ℝ)) ⟨(min t s).coe_nonneg, by
      simpa only [ENNReal.ofReal_coe_nnreal] using ht⟩
  refine ⟨?_, ginibreDrivenHamiltonianFirstLevel_hamiltonian_le hN hN0 hz hR (min t s) ht ?_⟩
  · simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe] using hprops.1
  · apply (ENNReal.coe_le_coe.mpr (min_le_right t s)).trans
    dsimp only [s]
    rw [ginibreDrivenHamiltonianBoundedStop_coe]
    exact min_le_right _ _

theorem ginibreDrivenHamiltonianBoundedStop_hamiltonian_eq {n : ℕ} (_ : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (hHit : ginibreDrivenHamiltonianFirstLevel n α N z R ≤ (T : ℝ≥0∞)) :
    ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z
      (ginibreDrivenHamiltonianBoundedStop n α N z R T)) = R := by
  obtain ⟨t, ht, htT⟩ := (ginibreDrivenHamiltonianFirstLevel_le_iff T).mp hHit
  obtain ⟨s, hs, hsHit⟩ := ginibreDrivenHamiltonianFirstLevel_attained
    (show (ginibreDrivenLevelHit n α N z R).Nonempty from ⟨t, ht⟩)
  have hσ : ginibreDrivenHamiltonianBoundedStop n α N z R T = s := by
    apply ENNReal.coe_injective
    rw [ginibreDrivenHamiltonianBoundedStop_coe, min_eq_right hHit, hs]
  rw [hσ]
  apply le_antisymm
  · exact ginibreDrivenHamiltonianFirstLevel_hamiltonian_le hN hN0 hz hR s hsHit.1 hs.symm.le
  · exact hsHit.2

end
end GinibrePoincare
