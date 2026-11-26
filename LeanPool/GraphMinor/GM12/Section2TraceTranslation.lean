/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceComposition

/-!
# Translating trace parameter intervals

The trace of XII, page 243, does not depend on the real origin used
to parameterize the circle. Translate entry witnesses and each region
interval by the same amount. For a periodic curve, this also permits
two successive copies of a closed trace to be read on one interval.
The latter avoids one-sided endpoints in the local restriction proof.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Translating the parameter origin preserves an entry witness. -/
theorem entersLike_translate
    {S : Type*} [TopologicalSpace S] {f g : ℝ → S} {δ : ℝ}
    (hfg : ∀ t, g (t + δ) = f t) {a c : ℝ} {e r : Set S} {v w : S}
    (hentry : EntersLike f a c e r v w) :
    EntersLike g (a + δ) (c + δ) e r v w := by
  obtain ⟨h, hh, ξ, ρ, hξ, hρ, hhom⟩ := hentry
  obtain ⟨s, hs, hs1, hprefix, hi, he, hw⟩ := hξ
  refine ⟨h + δ, ⟨by linarith [hh.1], by linarith [hh.2]⟩,
    ξ, ρ, ⟨s, hs, hs1, ?_, hi, he, hw⟩, hρ, hhom⟩
  intro t ht
  rw [hprefix t ht]
  have heq : h + δ + t.val / s.val * (c + δ - (h + δ)) =
      (h + t.val / s.val * (c - h)) + δ := by ring
  rw [heq, hfg]

/-- Translate every recorded region visit by the same amount. -/
theorem traceSteps_translate
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f g : ℝ → S} {δ : ℝ}
    (hfg : ∀ t, g (t + δ) = f t) {a b : ℝ} {u v : S}
    (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W) :
    TraceSteps Γ K g (a + δ) (b + δ) W := by
  cases hWcase : W with
  | nil hu =>
    rw [hWcase] at hW
    exact ⟨congrArg (fun t => t + δ) hW.1, (hfg a).trans hW.2.1, hW.2.2⟩
  | cons hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hu => rw [hrestcase] at hW; exact hW.elim
    | cons hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, hleave, henter, htail⟩ := hW
      refine ⟨c + δ, by linarith [hac], (hfg a).trans hfa, hu,
        (hfg c).trans hfc, hwK, r, hr, hwr, ?_, ?_, entersLike_translate hfg henter,
        traceSteps_translate hfg tail htail⟩
      · intro t ht
        have hval : g t = f (t - δ) := by simpa only [sub_add_cancel] using hfg (t - δ)
        rw [hval]
        exact hfr (t - δ) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · have hneg : ∀ t, g (-(t + -δ)) = f (-t) := by
          intro t
          have harg : -(t + -δ) = -t + δ := by ring
          rw [harg, hfg]
        have hle := entersLike_translate (g := fun t => g (-t)) (δ := -δ) hneg hleave
        simpa only [LeavesLike, neg_add_rev, add_comm] using hle
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- Two copies of a one-period closed trace give trace steps on two
periods of the same periodic curve. -/
theorem traceSteps_two_periods
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    (hper : Function.Periodic f 1) {a : ℝ} {u : S}
    (W : GraphWalk K.toGraph u u) (hW : TraceSteps Γ K f a (a + 1) W) :
    TraceSteps Γ K f a (a + 2) (W.append W) := by
  have hW' := traceSteps_translate hper W hW
  have hW'' : TraceSteps Γ K f (a + 1) (a + 2) W := by
    have heq : (a + 1) + 1 = a + 2 := by ring
    rw [heq] at hW'
    exact hW'
  exact traceSteps_append W W hW hW''

end GraphMinor.GM12
