/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import Mathlib.Topology.Path

/-!
# Constructing an entry curve from two paths

For the entry-edge definition of XII, page 243, concatenate the affine
approach to the vertex with a parametrization of the spoke. The joining
time is one half. This file checks the exact parametrization, including
injectivity and the image of the second half.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The normalized approach followed by a spoke path is an entry curve
in the exact sense of the definition on XII page 243. -/
theorem isEntryCurve_trans {S : Type*} [TopologicalSpace S]
    {f : ℝ → S} {h c : ℝ} {x v w : S} (p : Path x v) (q : Path v w)
    (hp : ∀ t : unitInterval, p t = f (h + t.val * (c - h)))
    (hq : Function.Injective q) {e : Set S}
    (hqe : q '' Ioo (0 : unitInterval) 1 = e) :
    IsEntryCurve f h c e w (p.trans q).toContinuousMap := by
  let s : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  refine ⟨s, by change (0 : ℝ) < 1 / 2; norm_num, by change (1 / 2 : ℝ) < 1; norm_num, ?_, ?_, ?_,
    ?_⟩
  · intro t ht
    change (p.trans q) t = _
    have ht' : (t : ℝ) ≤ 1 / 2 := ht
    rw [Path.trans_apply, dite_eq_left ht', hp]
    congr 1
    change h + (2 * t.val) * (c - h) = h + t.val / (1 / 2) * (c - h)
    ring
  · intro x hx y hy heq
    change (p.trans q) x = (p.trans q) y at heq
    have hx' : ¬ (x : ℝ) ≤ 1 / 2 := not_le.mpr hx.1
    have hy' : ¬ (y : ℝ) ≤ 1 / 2 := not_le.mpr hy.1
    simp only [Path.trans_apply, hx', hy', ↓reduceDIte] at heq
    have h := congrArg Subtype.val (hq heq)
    apply Subtype.ext
    dsimp only at h
    linarith
  · change (fun t => (p.trans q) t) '' Ioo s 1 = e
    rw [← hqe]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : ¬ (t : ℝ) ≤ 1 / 2 := not_le.mpr ht.1
      change (p.trans q) t ∈ q '' Ioo (0 : unitInterval) 1
      rw [Path.trans_apply, dite_eq_right ht']
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · change (0 : ℝ) < 2 * t.val - 1
        have hlt : (1 / 2 : ℝ) < t := ht.1
        linarith
      · change 2 * t.val - 1 < 1
        have hlt : (t : ℝ) < 1 := ht.2
        linarith
    · rintro ⟨t, ht, rfl⟩
      let u : unitInterval := ⟨(t.val + 1) / 2, by have := t.property.1; linarith,
        by have := t.property.2; linarith⟩
      have hu0 : s < u := by
        change (1 / 2 : ℝ) < (t.val + 1) / 2; have ht0 : (0 : ℝ) < t := ht.1; linarith
      have hu1 : u < 1 := by change (t.val + 1) / 2 < 1; have ht1 : (t : ℝ) < 1 := ht.2; linarith
      refine ⟨u, ⟨hu0, hu1⟩, ?_⟩
      change (p.trans q) u = q t
      rw [Path.trans_apply, dite_eq_right (not_le.mpr (show (1 / 2 : ℝ) < u from hu0))]
      apply congrArg q
      apply Subtype.ext
      change 2 * ((t.val + 1) / 2) - 1 = t.val
      ring
  · exact (p.trans q).target

end GraphMinor.GM12
