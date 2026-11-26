/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.ArcDisc

/-!
# Straight coordinates for an arc in a surface chart

For the leaf-entry patch of XII, page 243, an incident edge is first
restricted to a chart. Straighten its plane image and use polar strip
coordinates around the unit circle. Composing with the surface chart
puts the original arc on a real interval. This version allows an
arbitrary universe for the ambient surface; the plane straightening
itself still takes place in the complex plane.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric Complex Surface

/-- An arc contained in a ball chart has open injective coordinates
in which it is an increasing real interval. -/
theorem exists_straight_arc_chart
    {S : Type*} [TopologicalSpace S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {R : ℝ} {U : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : BallChart R U h g) {a : unitInterval → S} (ha : IsArcMap a) (hU : range a ⊆ U) :
    ∃ (O : Set ℂ) (K : ℂ → S) (θ : unitInterval → ℝ),
      IsOpen O ∧ ContinuousOn K O ∧ InjOn K O ∧
      (∀ W : Set ℂ, IsOpen W → W ⊆ O → IsOpen (K '' W)) ∧
      Continuous θ ∧ StrictMono θ ∧ ∀ t, (θ t : ℂ) ∈ O ∧ K (θ t) = a t := by
  have hac : Continuous (fun t => h (a t)) :=
    c.hc.comp_continuous ha.1 (fun t => hU (mem_range_self t))
  have hai : Function.Injective (fun t => h (a t)) := by
    intro s t he
    apply ha.2
    have he' := congrArg g he
    simpa only [c.gh (hU (mem_range_self s)), c.gh (hU (mem_range_self t))] using he'
  obtain ⟨G, θ, hθc, hθm, hθr, hGa⟩ := exists_straight (a := fun t => h (a t)) ⟨hac, hai⟩
  let P : ℂ → ℂ := fun z => G.symm (((1 + z.im : ℝ) : ℂ) * exp ((z.re : ℂ) * I))
  have hPc : Continuous P := by
    dsimp [P]
    fun_prop
  let O : Set ℂ := {z | z.re ∈ Ioo (-Real.pi) Real.pi ∧ z.im ∈ Ioo (-1 : ℝ) 1 ∧ P z ∈ ball 0 R}
  have hOo : IsOpen O :=
    (isOpen_Ioo.preimage continuous_re).inter
      ((isOpen_Ioo.preimage continuous_im).inter (isOpen_ball.preimage hPc))
  have hKc : ContinuousOn (fun z => g (P z)) O :=
    c.gc.comp hPc.continuousOn (fun _ hz => hz.2.2)
  have hKi : InjOn (fun z => g (P z)) O := by
    intro z hz w hw he
    have h1 : P z = P w := by
      have he' := congrArg h he
      simpa only [c.hg hz.2.2, c.hg hw.2.2] using he'
    have h2 := exp_strip_inj hz.1 hw.1 (by linarith [hz.2.1.1])
      (by linarith [hw.2.1.1]) (G.symm.injective h1)
    exact Complex.ext h2.1 h2.2
  refine ⟨O, fun z => g (P z), θ, hOo, hKc, hKi, ?_, hθc, hθm, ?_⟩
  · intro W hW hWO
    exact isOpen_image_of_manifold hW (hKc.mono hWO) (hKi.mono hWO) (fun _ _ => hman _)
  · intro t
    have hP : P (θ t) = h (a t) := by
      simp only [P, ofReal_re, ofReal_im, add_zero, ofReal_one, one_mul]
      rw [← hGa, G.symm_apply_apply]
    refine ⟨⟨by simpa using hθr t, by simp, ?_⟩, ?_⟩
    · rw [hP]
      exact c.hm (hU (mem_range_self t))
    · simp only [hP]
      exact c.gh (hU (mem_range_self t))

end GraphMinor.GM12
