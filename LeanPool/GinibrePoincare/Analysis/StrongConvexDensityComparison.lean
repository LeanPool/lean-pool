/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/StrongConvexDensityComparison.lean.
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

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # The one-dimensional density-profile maximum principle -/

@[expose] public section
open Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem local_min_second_derivative_nonneg
    (f : ℝ → ℝ) (a b x : ℝ) (hx : x ∈ Ioo a b)
    (hf : ContinuousOn f (Ioo a b)) (hmin : IsLocalMin f x)
    (hdd : ContinuousAt (deriv (deriv f)) x) :
    0 ≤ deriv (deriv f) x := by
  by_contra h
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hn : ∀ᶠ y in 𝓝 x, deriv (deriv f) y < 0 :=
    hdd.eventually (gt_mem_nhds hneg)
  have hall : ∀ᶠ y in 𝓝 x,
      f x ≤ f y ∧ deriv (deriv f) y < 0 ∧ y ∈ Ioo a b :=
    hmin.and (hn.and (isOpen_Ioo.mem_nhds hx))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hall
  let l := x - ε / 2
  let r := x + ε / 2
  have hnear {y : ℝ} (hy : y ∈ Icc l r) : dist y x < ε := by
    rw [Real.dist_eq, abs_lt]
    dsimp [l, r] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hsub : Icc l r ⊆ Ioo a b := fun y hy => (he (y := y) (hnear hy)).2.2
  have hs : StrictConcaveOn ℝ (Icc l r) f := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc l r) (hf.mono hsub)
    intro y hy
    exact (he (y := y) (hnear (interior_subset hy))).2.1
  have hlr : l < r := by dsimp [l, r]; linarith
  have hc := hs.2 (left_mem_Icc.mpr hlr.le) (right_mem_Icc.mpr hlr.le)
    hlr.ne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hm : (1 / 2 : ℝ) • l + (1 / 2 : ℝ) • r = x := by
    dsimp [l, r]; ring
  rw [hm] at hc
  have hfl := (he (y := l) (hnear (left_mem_Icc.mpr hlr.le))).1
  have hfr := (he (y := r) (hnear (right_mem_Icc.mpr hlr.le))).1
  simp only [smul_eq_mul] at hc
  linarith

theorem interval_second_derivative_maximum_principle
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : 0 ≤ f a) (hb : 0 ≤ f b)
    (hdd : ∀ x ∈ Ioo a b, ContinuousAt (deriv (deriv f)) x)
    (hneg : ∀ x ∈ Ioo a b, f x < 0 → deriv (deriv f) x < 0) :
    ∀ x ∈ Icc a b, 0 ≤ f x := by
  intro x hx
  by_contra h
  have hfx : f x < 0 := lt_of_not_ge h
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab.le⟩ hf
  have hfm : f m < 0 := (hmin hx).trans_lt hfx
  have hma : a < m := by
    rcases hm.1.eq_or_lt with he | he
    · subst m; linarith
    · exact he
  have hmb : m < b := by
    rcases hm.2.eq_or_lt with he | he
    · subst m; linarith
    · exact he
  have hlocal := hmin.isLocalMin (Icc_mem_nhds hma hmb)
  have hn := local_min_second_derivative_nonneg f a b m ⟨hma, hmb⟩
    (hf.mono Ioo_subset_Icc_self) hlocal (hdd m ⟨hma, hmb⟩)
  exact (not_lt_of_ge hn) (hneg m ⟨hma, hmb⟩ hfm)

theorem positive_density_profile_comparison
    (h j : ℝ → ℝ) (a b κ : ℝ) (hab : a < b) (hκ : 0 < κ)
    (hh : ContinuousOn h (Icc a b)) (hj : ContinuousOn j (Icc a b))
    (ha : j a ≤ h a) (hb : j b ≤ h b)
    (hh₂ : ∀ x ∈ Ioo a b, ContDiffAt ℝ 2 h x)
    (hj₂ : ∀ x ∈ Ioo a b, ContDiffAt ℝ 2 j x)
    (hhpos : ∀ x ∈ Ioo a b, 0 < h x) (_ : ∀ x ∈ Ioo a b, 0 < j x)
    (hhdd : ∀ x ∈ Ioo a b, deriv (deriv h) x ≤ -κ / h x)
    (hjdd : ∀ x ∈ Ioo a b, deriv (deriv j) x = -κ / j x) :
    ∀ x ∈ Icc a b, j x ≤ h x := by
  have hdd (x : ℝ) (hx : x ∈ Ioo a b) :
      deriv (deriv (h - j)) x = deriv (deriv h) x - deriv (deriv j) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      iteratedDeriv_sub (hh₂ x hx) (hj₂ x hx)
  have hcont (x : ℝ) (hx : x ∈ Ioo a b) :
      ContinuousAt (deriv (deriv (h - j))) x := by
    have hc := (hh₂ x hx).sub (hj₂ x hx)
    exact ((hc.derivWithin (m := 1) (by norm_num)).derivWithin
      (m := 0) (by norm_num)).continuousAt
  have hneg (x : ℝ) (hx : x ∈ Ioo a b) (hn : (h - j) x < 0) :
      deriv (deriv (h - j)) x < 0 := by
    rw [hdd x hx, hjdd x hx]
    have hlt : h x < j x := by simpa using sub_neg.mp hn
    have hd : κ / j x < κ / h x := div_lt_div_of_pos_left hκ (hhpos x hx) hlt
    have he := hhdd x hx
    simp only [neg_div] at he ⊢
    linarith
  have H := interval_second_derivative_maximum_principle (h - j) a b hab
    (hh.sub hj) (sub_nonneg.mpr ha) (sub_nonneg.mpr hb) hcont hneg
  intro x hx
  exact sub_nonneg.mp (H x hx)

end
end GinibrePoincare
