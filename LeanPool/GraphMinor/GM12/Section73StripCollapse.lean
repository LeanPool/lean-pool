/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73CollapseRectangle
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Collapsing an axis interval in a surface strip

Paste the rectangle collapse into a strip chart and leave all other
points fixed. The map is continuous and onto. Its only non-singleton
fibre is the drawn axis interval, which maps to its first endpoint.
This is the local topological contraction used for radial edges in
XII (7.3), page 261.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface Complex

/-- A strip chart supports a continuous surjection contracting one
axis interval to its first endpoint and identifying no other points.
This is the local edge contraction for XII (7.3), page 261. -/
theorem exists_strip_interval_collapse
    {T : Type} [TopologicalSpace T] [T2Space T] {O : Set ℂ} {K : ℂ → T}
    (hK : StripChart O K) {l r ε : ℝ} (hlr : l < r) (hε : 0 < ε)
    (hRO : collapseRectangle l r ε ⊆ O) :
    ∃ f : C(T, T), Function.Surjective f ∧
      (∀ x ∉ K '' collapseRectangle l r ε, f x = x) ∧
      (∀ x ∈ K '' (Complex.ofReal '' Icc l r), f x = K (l : ℂ)) ∧
      (∀ t : ℝ, (t : ℂ) ∈ O → t ≤ l → f (K (t : ℂ)) = K (t : ℂ)) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ K '' (Complex.ofReal '' Icc l r) ∧ y ∈ K '' (Complex.ofReal '' Icc l r))) := by
  let R := collapseRectangle l r ε
  let A := Complex.ofReal '' Icc l r
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hΦR : MapsTo (collapseStrip l r ε) R R := collapseStrip_mapsTo hlr.le hε
  let Φ : Unit × ℂ → ℂ := fun p => collapseStrip l r ε p.2
  have hΦc : Continuous Φ := (continuous_collapseStrip l r ε).comp continuous_snd
  obtain ⟨c, hcc, hc1, hc2⟩ := exists_glue hK hRc hRO Φ hΦc.continuousOn
    (fun _ z hz => hΦR hz) (fun _ z hz => collapseStrip_frontier hlr.le hε hz)
  let f : C(T, T) := ⟨fun x => c ((), x), hcc.comp (by fun_prop)⟩
  have hAR : A ⊆ R := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · change 2 * l - r ≤ t ∧ t ≤ 2 * r - l
      constructor <;> linarith [ht.1, ht.2]
    · change -ε ≤ (t : ℂ).im ∧ (t : ℂ).im ≤ ε
      simp only [ofReal_im]
      exact ⟨neg_nonpos.mpr hε.le, hε.le⟩
  have hconst : ∀ x ∈ K '' A, f x = K (l : ℂ) := by
    rintro x ⟨z, ⟨t, ht, rfl⟩, rfl⟩
    change c ((), K (t : ℂ)) = _
    rw [hc1 () _ (hAR ⟨t, ht, rfl⟩)]
    change K (collapseStrip l r ε (t : ℂ)) = _
    rw [collapseStrip_ofReal, collapseInterval_of_mem ht]
  have hsurjR : ∀ w ∈ R, ∃ z ∈ R, collapseStrip l r ε z = w := by
    intro w hw
    let t := collapseWeight ε w
    let F : ℝ → ℝ := fun x => (1 - t) * x + t * collapseInterval l r x
    have hFc : Continuous F := by
      have hψ := continuous_collapseInterval l r
      fun_prop
    obtain ⟨hleft, hright⟩ := collapseInterval_interpolation_endpoints (t := t) hlr.le
    have ha : 2 * l - r ≤ 2 * r - l := by linarith
    obtain ⟨x, hx, hxe⟩ : w.re ∈ F '' Icc (2 * l - r) (2 * r - l) := by
      apply intermediate_value_Icc ha hFc.continuousOn
      change w.re ∈ Icc (F (2 * l - r)) (F (2 * r - l))
      dsimp only [F]
      rw [hleft, hright]
      exact hw.1
    let z : ℂ := (x : ℂ) + w.im * I
    have hzre : z.re = x := by simp [z]
    have hzim : z.im = w.im := by simp [z]
    have hzR : z ∈ R := ⟨by simpa only [mem_preimage, hzre] using hx,
      by simpa only [mem_preimage, hzim] using hw.2⟩
    refine ⟨z, hzR, Complex.ext ?_ ?_⟩
    · rw [collapseStrip_re, hzre]
      have hweight : collapseWeight ε z = t := by simp only [collapseWeight, hzim, t]
      rw [hweight]
      exact hxe
    · rw [collapseStrip_im, hzim]
  have hsurj : Function.Surjective f := by
    intro y
    by_cases hy : y ∈ K '' R
    · obtain ⟨w, hw, rfl⟩ := hy
      obtain ⟨z, hz, hzw⟩ := hsurjR w hw
      refine ⟨K z, ?_⟩
      change c ((), K z) = K w
      rw [hc1 () z hz]
      exact congrArg K hzw
    · exact ⟨y, hc2 () y hy⟩
  have hleftAxis : ∀ t : ℝ, (t : ℂ) ∈ O → t ≤ l → f (K (t : ℂ)) = K (t : ℂ) := by
    intro t ht htl
    by_cases hKt : K (t : ℂ) ∈ K '' R
    · obtain ⟨w, hw, heq⟩ := hKt
      have hwt : w = (t : ℂ) := hK.hi (hRO hw) ht heq
      subst w
      change c ((), K (t : ℂ)) = _
      rw [hc1 () _ hw]
      change K (collapseStrip l r ε (t : ℂ)) = _
      rw [collapseStrip_ofReal, collapseInterval_of_le hlr.le htl]
    · exact hc2 () _ hKt
  refine ⟨f, hsurj, fun x hx => hc2 () x hx, hconst, hleftAxis, ?_⟩
  intro x y
  constructor
  · intro heq
    by_cases hx : x ∈ K '' R <;> by_cases hy : y ∈ K '' R
    · obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      change c ((), K z) = c ((), K w) at heq
      rw [hc1 () z hz, hc1 () w hw] at heq
      have hΦ : collapseStrip l r ε z = collapseStrip l r ε w :=
        hK.hi (hRO (hΦR hz)) (hRO (hΦR hw)) heq
      rcases (collapseStrip_eq_iff hlr.le hε hz).mp hΦ with hzw | ⟨hzA, hwA⟩
      · exact Or.inl (congrArg K hzw)
      · exact Or.inr ⟨⟨z, hzA, rfl⟩, ⟨w, hwA, rfl⟩⟩
    · obtain ⟨z, hz, rfl⟩ := hx
      change c ((), K z) = c ((), y) at heq
      rw [hc1 () z hz, hc2 () y hy] at heq
      exact (hy ⟨collapseStrip l r ε z, hΦR hz, heq⟩).elim
    · obtain ⟨w, hw, rfl⟩ := hy
      change c ((), x) = c ((), K w) at heq
      rw [hc2 () x hx, hc1 () w hw] at heq
      exact (hx ⟨collapseStrip l r ε w, hΦR hw, heq.symm⟩).elim
    · exact Or.inl (by change c ((), x) = c ((), y) at heq; rwa [hc2 () x hx, hc2 () y hy] at heq)
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [hconst x hx, hconst y hy]

end GraphMinor.GM12
