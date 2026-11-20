/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexQuantileCalculus.lean.
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

public import LeanPool.GinibrePoincare.Analysis.StrongConvexCDF
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Actual smoothness of the cumulative-density inverse -/

@[expose] public section
open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem increasingCDFQuantileOn_contDiffOn_one
    (F p : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (hd : ∀ x ∈ s, HasDerivAt F (p x) x)
    (hn : ∀ x ∈ s, p x ≠ 0) (hp : ContinuousOn p s) :
    ContDiffOn ℝ 1 (increasingCDFQuantileOn F s hm hr) (Ioo 0 1) := by
  let q := increasingCDFQuantileOn F s hm hr
  have hq (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :=
    increasingCDFQuantileOn_hasDerivAt F p s hm hr hd hn u hu
  have hmapping : MapsTo q (Ioo 0 1) s :=
    fun u hu => increasingCDFQuantileOn_mem F s hm hr u hu
  have hpc : ContinuousOn (p ∘ q) (Ioo 0 1) :=
    hp.comp (increasingCDFQuantileOn_continuousOn F s hm hr) hmapping
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun u hu => (hq u hu).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  apply (hpc.inv₀ fun u hu => hn _ (hmapping hu)).congr
  intro u hu
  exact (hq u hu).deriv

theorem increasingCDFQuantileOn_contDiffOn_two
    (F p : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (hd : ∀ x ∈ s, HasDerivAt F (p x) x)
    (hn : ∀ x ∈ s, p x ≠ 0) (hp : ContDiffOn ℝ 1 p s) :
    ContDiffOn ℝ 2 (increasingCDFQuantileOn F s hm hr) (Ioo 0 1) := by
  let q := increasingCDFQuantileOn F s hm hr
  have hq (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :=
    increasingCDFQuantileOn_hasDerivAt F p s hm hr hd hn u hu
  have hmapping : MapsTo q (Ioo 0 1) s :=
    fun u hu => increasingCDFQuantileOn_mem F s hm hr u hu
  have hqc := increasingCDFQuantileOn_contDiffOn_one F p s hm hr hd hn hp.continuousOn
  have hpc : ContDiffOn ℝ 1 (p ∘ q) (Ioo 0 1) := hp.comp hqc hmapping
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun u hu => (hq u hu).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply (hpc.inv fun u hu => hn _ (hmapping hu)).congr
  intro u hu
  exact (hq u hu).deriv

/-- The density–quantile profile `u ↦ p (F⁻¹ u)` on `Ioo 0 1`, with `F⁻¹` the quantile function
`increasingCDFQuantileOn F s`, extended by `0` outside `Ioo 0 1`. -/
def densityQuantileProfile (F p : ℝ → ℝ) (s : Set ℝ)
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0 : ℝ) 1 then p (increasingCDFQuantileOn F s hm hr u) else 0

theorem densityQuantileProfile_eventually_eq (F p : ℝ → ℝ) (s : Set ℝ)
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    densityQuantileProfile F p s hm hr =ᶠ[𝓝 u]
      p ∘ increasingCDFQuantileOn F s hm hr := by
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  simp [densityQuantileProfile, hv]

theorem densityQuantileProfile_contDiffAt_two
    (F p : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (hd : ∀ x ∈ s, HasDerivAt F (p x) x)
    (hn : ∀ x ∈ s, p x ≠ 0) (hp : ContDiffOn ℝ 2 p s)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (densityQuantileProfile F p s hm hr) u := by
  have hqc := increasingCDFQuantileOn_contDiffOn_two F p s hm hr hd hn
    (hp.of_le (by norm_num))
  have hc : ContDiffOn ℝ 2 (p ∘ increasingCDFQuantileOn F s hm hr) (Ioo 0 1) :=
    hp.comp hqc fun v hv => increasingCDFQuantileOn_mem F s hm hr v hv
  apply (hc.contDiffAt (isOpen_Ioo.mem_nhds hu)).congr_of_eventuallyEq
  exact densityQuantileProfile_eventually_eq F p s hm hr u hu

theorem densityQuantileProfile_hasDerivAt
    (F p W : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (hd : ∀ x ∈ s, HasDerivAt F (p x) x)
    (hn : ∀ x ∈ s, p x ≠ 0)
    (hp : ∀ x ∈ s, HasDerivAt p (-deriv W x * p x) x)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (densityQuantileProfile F p s hm hr)
      (-deriv W (increasingCDFQuantileOn F s hm hr u)) u := by
  let q := increasingCDFQuantileOn F s hm hr
  have hmem := increasingCDFQuantileOn_mem F s hm hr u hu
  have hq := increasingCDFQuantileOn_hasDerivAt F p s hm hr hd hn u hu
  have h := (hp _ hmem).comp u hq
  have he : (-deriv W (q u) * p (q u)) * (p (q u))⁻¹ = -deriv W (q u) := by
    have hpn : p (q u) ≠ 0 := hn _ hmem
    field_simp [hpn]
  rw [he] at h
  exact h.congr_of_eventuallyEq (densityQuantileProfile_eventually_eq F p s hm hr u hu)

theorem densityQuantileProfile_second_derivative
    (F p W : ℝ → ℝ) (s : Set ℝ) [OrdConnected s]
    (hm : StrictMonoOn F s) (hr : F '' s = Ioo 0 1)
    (hd : ∀ x ∈ s, HasDerivAt F (p x) x)
    (hn : ∀ x ∈ s, p x ≠ 0)
    (hp : ∀ x ∈ s, HasDerivAt p (-deriv W x * p x) x)
    (hW : ∀ x ∈ s, ContDiffAt ℝ 2 W x)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv (densityQuantileProfile F p s hm hr)) u =
      -deriv (deriv W) (increasingCDFQuantileOn F s hm hr u) /
        densityQuantileProfile F p s hm hr u := by
  let q := increasingCDFQuantileOn F s hm hr
  have hmem := increasingCDFQuantileOn_mem F s hm hr u hu
  have hq := increasingCDFQuantileOn_hasDerivAt F p s hm hr hd hn u hu
  have hWd := (((hW _ hmem).derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have h := (hWd.comp u hq).neg
  have he : deriv (densityQuantileProfile F p s hm hr) =ᶠ[𝓝 u]
      fun v => -deriv W (q v) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    exact (densityQuantileProfile_hasDerivAt F p W s hm hr hd hn hp v hv).deriv
  have ht := (h.congr_of_eventuallyEq he).deriv
  simpa [densityQuantileProfile, hu, q, div_eq_mul_inv, neg_mul] using ht

end
end GinibrePoincare
