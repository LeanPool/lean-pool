/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianFirstLevel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianMaximalLevel
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathClosedHittingTime

/-! Actual first Hamiltonian threshold crossing before the canonical maximal lifetime. -/

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section

/-- The times before the maximal lifetime at which the Hamiltonian of the driven maximal
Ginibre path is at least `R`. -/
def ginibreDrivenLevelHit (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) (R : ℝ) : Set ℝ≥0 :=
  {t | (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z ∧
    R ≤ ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z t)}

open Classical in
/-- The first time the Hamiltonian of the driven maximal Ginibre path reaches the level `R`,
computed as a hitting time on `[0, b]` for a chosen time `b` in `ginibreDrivenLevelHit`; it is
`⊤` when the level is never reached before the lifetime. -/
def ginibreDrivenHamiltonianFirstLevel (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) (R : ℝ) : ℝ≥0∞ :=
  if h : (ginibreDrivenLevelHit n α N z R).Nonempty then
    let b := h.choose
    ((hittingBtwn (fun t (_ : Unit) => ginibreHamiltonian n
      (ginibreDrivenMaximalValue n α N z (min t b))) (Ici R) 0 b () : ℝ≥0) : ℝ≥0∞)
  else ⊤

theorem ginibreDrivenHamiltonianPrefix_continuous {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} (b : ℝ≥0)
    (hb : (b : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    Continuous (fun t : ℝ≥0 => ginibreHamiltonian n
      (ginibreDrivenMaximalValue n α N z (min t b))) := by
  have hc := ginibreDrivenMaximalPath_hamiltonian_continuousOn n α N z
  have hg : Continuous (fun t : ℝ≥0 => ((min t b : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hh := hc.comp_continuous hg (fun t =>
    (show ((min t b : ℝ≥0) : ℝ) ∈ ginibreDrivenMaximalDomain n α N z from by
      refine ⟨(min t b).coe_nonneg, ?_⟩
      rw [ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.coe_le_coe.mpr (min_le_right t b)).trans_lt hb))
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe, Function.comp_def] using hh

theorem ginibreDrivenHamiltonianFirstLevel_le_iff {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} {R : ℝ} (s : ℝ≥0) :
    ginibreDrivenHamiltonianFirstLevel n α N z R ≤ (s : ℝ≥0∞) ↔
      ∃ t ∈ ginibreDrivenLevelHit n α N z R, t ≤ s := by
  classical
  unfold ginibreDrivenHamiltonianFirstLevel
  split_ifs with h
  · let b := h.choose
    have hb : b ∈ ginibreDrivenLevelHit n α N z R := h.choose_spec
    let u : ℝ≥0 → Unit → ℝ := fun t _ => ginibreHamiltonian n
      (ginibreDrivenMaximalValue n α N z (min t b))
    have hc : Continuous (fun t => u t ()) := ginibreDrivenHamiltonianPrefix_continuous b hb.1
    have hhit : ∃ j ∈ Icc 0 b, u j () ∈ Ici R := ⟨b, by simp, by simpa [u] using hb.2⟩
    have hτb : hittingBtwn u (Ici R) 0 b () ≤ b := hittingBtwn_le ()
    have hτhit := drivenContinuous_closed_hitting_mem u (Ici R) isClosed_Ici b () hc hhit
    have hτmem : hittingBtwn u (Ici R) 0 b () ∈ ginibreDrivenLevelHit n α N z R := by
      refine ⟨(ENNReal.coe_le_coe.mpr hτb).trans_lt hb.1, ?_⟩
      simpa only [u, min_eq_left hτb, mem_Ici] using hτhit
    change ((hittingBtwn u (Ici R) 0 b () : ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞) ↔ _
    rw [ENNReal.coe_le_coe]
    constructor
    · intro hs
      exact ⟨_, hτmem, hs⟩
    · rintro ⟨t, ht, hts⟩
      by_cases htb : t ≤ b
      · have hi : u t () ∈ Ici R := by simpa only [u, min_eq_left htb, mem_Ici] using ht.2
        exact (hittingBtwn_le_of_mem (u := u) (s := Ici R) (n := 0) (m := b)
          (i := t) (ω := ()) (bot_le) htb hi).trans hts
      · exact hτb.trans ((le_of_not_ge htb).trans hts)
  · simp only [top_le_iff, ENNReal.coe_ne_top, false_iff]
    rintro ⟨t, ht, _⟩
    exact h ⟨t, ht⟩

theorem drivenContinuous_real_le_until_hitting {Ω : Type*}
    (u : ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω)
    (hu : Continuous (fun t => u t ω)) (h0 : u 0 ω ≤ R)
    (t : ℝ≥0) (ht : t ≤ hittingBtwn u (Ici R) 0 T ω) : u t ω ≤ R := by
  by_contra hn
  have hrt : R < u t ω := lt_of_not_ge hn
  obtain ⟨j, hj, hjr⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ t)
    hu.continuousOn ⟨h0, hrt.le⟩
  have hjt : j < t := lt_of_le_of_ne hj.2 (by intro he; rw [he] at hjr; linarith)
  have hjT := hj.2.trans (ht.trans (hittingBtwn_le (u := u) (s := Ici R) (n := 0) (m := T) ω))
  have hτj := hittingBtwn_le_of_mem (u := u) (s := Ici R) (n := 0) (m := T)
    (i := j) (ω := ω) hj.1 hjT (show u j ω ∈ Ici R from hjr.ge)
  exact (not_lt_of_ge (ht.trans hτj)) hjt

theorem ginibreDrivenHamiltonianFirstLevel_attained {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} {R : ℝ}
    (h : (ginibreDrivenLevelHit n α N z R).Nonempty) :
    ∃ t : ℝ≥0, ginibreDrivenHamiltonianFirstLevel n α N z R = (t : ℝ≥0∞) ∧
      t ∈ ginibreDrivenLevelHit n α N z R := by
  classical
  let b := h.choose
  have hb : b ∈ ginibreDrivenLevelHit n α N z R := h.choose_spec
  let u : ℝ≥0 → Unit → ℝ := fun t _ => ginibreHamiltonian n
    (ginibreDrivenMaximalValue n α N z (min t b))
  let τ := hittingBtwn u (Ici R) 0 b ()
  have hτb : τ ≤ b := hittingBtwn_le ()
  have hc : Continuous (fun t => u t ()) := ginibreDrivenHamiltonianPrefix_continuous b hb.1
  have hh : ∃ j ∈ Icc 0 b, u j () ∈ Ici R := ⟨b, by simp, by simpa [u] using hb.2⟩
  have hτhit := drivenContinuous_closed_hitting_mem u (Ici R) isClosed_Ici b () hc hh
  refine ⟨τ, ?_, (ENNReal.coe_le_coe.mpr hτb).trans_lt hb.1, ?_⟩
  · simp only [ginibreDrivenHamiltonianFirstLevel, dite_eq_left h]
    rfl
  · simpa only [u, τ, min_eq_left hτb, mem_Ici] using hτhit

theorem ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z ≤ R) (s : ℝ≥0) :
    ginibreDrivenHamiltonianFirstLevel n α N z R ≤ (s : ℝ≥0∞) ↔
      ginibreDrivenMaximalLifetime n α N z ≤ (s : ℝ≥0∞) ∨
      ((s : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z ∧
        ∃ t ∈ Icc 0 s, R ≤ ginibreHamiltonian n (ginibreDrivenMaximalValue n α N z t)) := by
  rw [ginibreDrivenHamiltonianFirstLevel_le_iff]
  constructor
  · rintro ⟨t, ht, hts⟩
    by_cases hs : ginibreDrivenMaximalLifetime n α N z ≤ (s : ℝ≥0∞)
    · exact Or.inl hs
    · exact Or.inr ⟨lt_of_not_ge hs, t, ⟨bot_le, hts⟩, ht.2⟩
  · rintro (hs | ⟨hs, t, ht, hval⟩)
    · have hfin : ginibreDrivenMaximalLifetime n α N z ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top hs
      obtain ⟨t, ht, hval⟩ := ginibreDrivenMaximalLifetime_finite_hamiltonian_level
        hn α N hN hN0 z hz hfin R hR
      have htalive : (Real.toNNReal t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
        rw [← ENNReal.coe_toNNReal hfin]
        exact (ENNReal.ofReal_lt_coe_iff ht.1).mpr ht.2
      refine ⟨Real.toNNReal t, ⟨htalive, ?_⟩, ?_⟩
      · simpa only [ginibreDrivenMaximalPath] using hval.ge
      · exact ENNReal.coe_le_coe.mp (htalive.le.trans hs)
    · exact ⟨t, ⟨(ENNReal.coe_le_coe.mpr ht.2).trans_lt hs, hval⟩, ht.2⟩

end
end GinibrePoincare
