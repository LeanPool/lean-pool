/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLogRegularization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLogGenerator

/-! Globally smooth logarithmic center barriers and their actual generator
upper bound, suitable for the constructed Hamiltonian-stopped Itô martingales. -/

@[expose] public section
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The regularized logarithmic barrier `-log (ginibreCenterSquared n z + ε)` at a vanishing
center. -/
def ginibreCenterLogBarrier (n : ℕ) (ε : ℝ) (z : Configuration n) : ℝ :=
  -Real.log (ginibreCenterSquared n z+ε)

theorem ginibreCenterSquared_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ ginibreCenterSquared n z := Complex.normSq_nonneg _

theorem contDiff_ginibreCenterLogBarrier (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (ginibreCenterLogBarrier n ε) := by
  apply ContDiff.neg
  exact ((contDiff_ginibreCenterSquared n).add contDiff_const).log
    (fun z => (add_pos_of_nonneg_of_pos (ginibreCenterSquared_nonneg n z) hε).ne')

theorem ginibre_log_shift_derivatives {ε r : ℝ} (h : 0 < r + ε) :
    deriv (fun x => Real.log (x+ε)) r = (r+ε)⁻¹ ∧
      deriv (deriv (fun x => Real.log (x+ε))) r = -((r+ε)^2)⁻¹ := by
  have hd (x : ℝ) (hx : x+ε ≠ 0) : HasDerivAt (fun y => Real.log (y+ε)) (x+ε)⁻¹ x := by
    exact (Real.hasDerivAt_log hx).comp_add_const x ε
  refine ⟨(hd r h.ne').deriv,?_⟩
  have he : deriv (fun x => Real.log (x+ε)) =ᶠ[nhds r] (fun x => (x+ε)⁻¹) := by
    filter_upwards [((continuous_id.add continuous_const).continuousAt.eventually_ne h.ne')] with x
        hx
    exact (hd x hx).deriv
  simpa only [id_eq, one_div, neg_div, one_mul] using ((((hasDerivAt_id r).add_const ε).inv
      h.ne').congr_of_eventuallyEq he).deriv

theorem ginibreRealPaperSpeedGenerator_centerLogBarrier {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) {ε : ℝ} (hε : 0 < ε) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreCenterLogBarrier n ε) z =
      (4*α/(n : ℝ))*(ginibreCenterSquared n z/(ginibreCenterSquared n z+ε)-
        ε/(ginibreCenterSquared n z+ε)^2) := by
  let r := ginibreCenterSquared n z
  have hr : 0 < r+ε := add_pos_of_nonneg_of_pos (ginibreCenterSquared_nonneg n z) hε
  have hf : ContDiffAt ℝ 2 (ginibreCenterSquared n) z :=
    ((contDiff_ginibreCenterSquared n).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffAt
  have hφ : ContDiffAt ℝ 2 (fun x : ℝ => Real.log (x+ε)) r :=
    ((contDiffAt_id.add contDiffAt_const).log hr.ne')
  have hd := ginibre_log_shift_derivatives hr
  have hg := ginibreRealPaperSpeedGenerator_scalar_comp α (ginibreCenterSquared n)
    (fun x : ℝ => -Real.log (x+ε)) z hf hφ.neg
  change ginibreRealPaperSpeedGenerator n α ((-(fun x : ℝ => Real.log (x+ε))) ∘ ginibreCenterSquared
      n) z = _ at hg
  have hneg : (fun x : ℝ => -Real.log (x+ε)) = -(fun x : ℝ => Real.log (x+ε)) := rfl
  rw [hneg, deriv.neg'] at hg
  have hneg2 : (fun x : ℝ => -deriv (fun y => Real.log (y+ε)) x) =
      -(deriv (fun y : ℝ => Real.log (y+ε))) := rfl
  rw [hneg2, deriv.neg] at hg
  simp only [Pi.neg_apply] at hg
  rw [hd.1, hd.2, neg_neg] at hg
  rw [ginibreRealPaperSpeedGenerator_centerSquared hn α z hz,
    ginibre_centerSquared_gradient_normSq] at hg
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold ginibreCenterLogBarrier
  change ginibreRealPaperSpeedGenerator n α ((-(fun x : ℝ => Real.log (x+ε))) ∘ ginibreCenterSquared
      n) z = _
  rw [hg]
  change -(r+ε)⁻¹*((4*α/(n : ℝ))*(1-r)) +
    (α/(n : ℝ)^2)*((r+ε)^2)⁻¹*(4*(n : ℝ)*r) = _
  change _ = (4*α/(n : ℝ))*(r/(r+ε)-ε/(r+ε)^2)
  field_simp; ring

theorem ginibreRealPaperSpeedGenerator_centerLogBarrier_le {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ≥0) {ε : ℝ} (hε : 0 < ε) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreCenterLogBarrier n ε) z ≤ 4*(α : ℝ)/(n : ℝ) := by
  rw [ginibreRealPaperSpeedGenerator_centerLogBarrier hn α hε z hz]
  have hr := ginibreCenterSquared_nonneg n z
  have hp := add_pos_of_nonneg_of_pos hr hε
  have h1 : ginibreCenterSquared n z/(ginibreCenterSquared n z+ε) ≤ 1 :=
    (div_le_one hp).mpr (le_add_of_nonneg_right hε.le)
  have h2 : 0 ≤ ε/(ginibreCenterSquared n z+ε)^2 := div_nonneg hε.le (sq_nonneg _)
  exact (mul_le_mul_of_nonneg_left (sub_le_self _ h2 |>.trans h1)
    (div_nonneg (mul_nonneg (by norm_num) α.coe_nonneg) (Nat.cast_nonneg n))).trans_eq (mul_one _)
end
end GinibrePoincare
