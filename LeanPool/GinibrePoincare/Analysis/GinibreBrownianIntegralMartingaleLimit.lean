/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreBrownianIntegralMartingaleLimit.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralL2Completion

/-! Genuine strong L² limits preserve the martingale identity. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem realMartingale_of_actual_L2_limits {Ω τ : Type*} [MeasurableSpace Ω] [Preorder τ]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration τ (inferInstance : MeasurableSpace Ω))
    (S : ℕ → τ → Ω → ℝ) (hS : ∀ n, Martingale (S n) ℱ P)
    (hs : ∀ n t, MemLp (S n t) 2 P) (M : τ → Ω → ℝ)
    (hM : StronglyAdapted ℱ M) (hm : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ t, Tendsto (fun n => (hs n t).toLp (S n t)) atTop (𝓝 ((hm t).toLp (M t)))) :
    Martingale M ℱ P := by
  refine ⟨hM,?_⟩
  intro s t hst
  let A := fun u : Lp ℝ 2 P => (condExpL2 ℝ ℝ (ℱ.le s) u : Lp ℝ 2 P)
  have hA : Continuous A := continuous_subtype_val.comp (condExpL2 ℝ ℝ (ℱ.le s)).continuous
  have he (n : ℕ) : A ((hs n t).toLp (S n t)) = (hs n s).toLp (S n s) := by
    apply Lp.ext
    have hce := (hs n t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le s)
    have hmart := (hS n).condExp_ae_eq hst
    filter_upwards [hce, hmart, (hs n s).coeFn_toLp] with ω hc hb hsω
    exact hc.trans (hb.trans hsω.symm)
  have hleft := hA.tendsto ((hm t).toLp (M t)) |>.comp (hlim t)
  have hright : Tendsto (fun n => A ((hs n t).toLp (S n t))) atTop (𝓝 ((hm s).toLp (M s))) := by
    simpa only [he] using hlim s
  have hid : A ((hm t).toLp (M t)) = (hm s).toLp (M s) := tendsto_nhds_unique hleft hright
  have hce := (hm t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le s)
  have hae : (fun ω => A ((hm t).toLp (M t)) ω) =ᵐ[P] M s := by
    rw [hid]
    exact (hm s).coeFn_toLp
  exact hce.symm.trans hae

end
end GinibrePoincare
