/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.CutoffProfiles
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.WeakGradientPairing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Basic

/-!
# The cut-off heat kernels of the backward windows

For a point `(x, s)` and a scale `ρ`, the backward window is `B_bar(x, ρ) × [s - ρ², s]`. The cutoff
`χ` is the ball cutoff times the time cutoff; the heat weight is `Ψ = Γ(x - ·, s - ·) χ`, and the
cutoff commutator kernel is `K₀ = Γ (∂ₜχ + Δχ) + 2 ∇Γ · ∇χ`. Before the time `s`, both kernels
and their spatial partials vanish off the window. These are the kernels of the heat
representation used for the interior estimates in the proof of `lem:aniso:annulus`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-- Backward parabolic cutoff at `(x, s)` of scale `ρ`. -/
@[expose] def serrinCutoff (x : Vec3) (s ρ : ℝ) (z : ParabolicPoint) : ℝ :=
  serrinBallCutoff x ρ z.1 * serrinTimeBump ((z.2 - s) / ρ ^ 2)

/-- The cut-off backward heat weight `Ψ(z) = Γ(x - z.1, s - z.2) χ(z)`. -/
@[expose] def serrinHeatWeight (x : Vec3) (s ρ : ℝ) (z : ParabolicPoint) : ℝ :=
  heatKernel (x - z.1) (s - z.2) * serrinCutoff x s ρ z

/-- The cutoff-commutator kernel `K₀ = Γ (∂ₜχ + Δχ) + 2 ∇_zΓ · ∇χ`. -/
@[expose] def serrinCutoffKernel (x : Vec3) (s ρ : ℝ) (z : ParabolicPoint) : ℝ :=
  heatKernel (x - z.1) (s - z.2) *
      (timePartial (serrinCutoff x s ρ) z +
        ∑ i, spatialSecondPartial (serrinCutoff x s ρ) i i z) +
    2 * ∑ i, spatialPartial (fun w : ParabolicPoint => heatKernel (x - w.1) (s - w.2)) i z *
      spatialPartial (serrinCutoff x s ρ) i z

/-- The time partial vanishes where the function vanishes on a neighbourhood. -/
theorem timePartial_eq_zero_of_eventually_eq_zero {F : Vec3 × ℝ → ℝ} {z : Vec3 × ℝ}
    (hF : ∀ᶠ w : Vec3 × ℝ in nhds z, F w = 0) : timePartial F z = 0 := by
  unfold timePartial
  have hcont : Continuous (fun t : ℝ => ((z.1, t) : Vec3 × ℝ)) := by fun_prop
  have h1 : (fun t : ℝ => F (z.1, t)) =ᶠ[nhds z.2] fun _ => (0 : ℝ) := by
    have := hcont.continuousAt (x := z.2) |>.tendsto
    exact this.eventually (by simpa using hF)
  rw [h1.fderiv_eq]
  simp

/-- The backward cutoff is smooth. -/
theorem contDiff_serrinCutoff (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinCutoff x s ρ z) := by
  have h1 := (serrinBallCutoff_support x hρ x).2.2
  have h2 := (serrinTimeBump_support (s := s) hρ s).2.2
  unfold serrinCutoff
  exact (h1.comp contDiff_fst).mul (h2.comp ((contDiff_snd.sub contDiff_const).div_const _))

/-- Before the time `s` and off the window, the backward cutoff vanishes on a neighbourhood. -/
theorem serrinCutoff_eventually_eq_zero (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) {z : Vec3 × ℝ}
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s)
    (hz : z.2 < s) :
    ∀ᶠ w : Vec3 × ℝ in nhds z, serrinCutoff x s ρ w = 0 := by
  have hn : Continuous (fun w : Vec3 × ℝ => vec3EuclideanNorm (w.1 - x)) := by
    unfold vec3EuclideanNorm; fun_prop
  by_cases hball : vec3EuclideanNorm (z.1 - x) ≤ ρ
  · have htime : z.2 < s - ρ ^ 2 := by
      by_contra h
      exact hout ⟨hball, le_of_not_gt h, hz.le⟩
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds htime] with w hw
    unfold serrinCutoff
    rw [(serrinTimeBump_support (s := s) hρ w.2).2.1 (le_of_lt hw), mul_zero]
  · filter_upwards [(isOpen_lt continuous_const hn).mem_nhds (lt_of_not_ge hball)] with w hw
    unfold serrinCutoff
    rw [(serrinBallCutoff_support x hρ w.1).2.1 (le_of_lt hw), zero_mul]

/-- Before the time `s`, the spatial partials of the heat weight and of the commutator kernel
vanish off the window. -/
theorem spatialPartial_serrinKernels_eq_zero (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) {z : Vec3 × ℝ}
    (hz : z.2 < s)
    (hout : z ∉ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s) (j : Fin 3) :
    spatialPartial (serrinHeatWeight x s ρ) j z = 0 ∧
      spatialPartial (serrinCutoffKernel x s ρ) j z = 0 := by
  have hev := serrinCutoff_eventually_eq_zero x hρ hout hz
  -- on a neighbourhood of `z` every partial of the cutoff vanishes
  have hev2 : ∀ᶠ w : Vec3 × ℝ in nhds z, ∀ᶠ w' : Vec3 × ℝ in nhds w, serrinCutoff x s ρ w' = 0
    := hev.eventually_nhds
  have hder : ∀ᶠ w : Vec3 × ℝ in nhds z, timePartial (serrinCutoff x s ρ) w = 0 ∧
      (∀ i, spatialPartial (serrinCutoff x s ρ) i w = 0) ∧
      ∀ i, spatialSecondPartial (serrinCutoff x s ρ) i i w = 0 := by
    have hev3 : ∀ᶠ w : Vec3 × ℝ in nhds z, ∀ᶠ w' : Vec3 × ℝ in nhds w, ∀ᶠ w'' : Vec3 × ℝ in nhds w',
        serrinCutoff x s ρ w'' = 0 := hev2.eventually_nhds
    filter_upwards [hev2, hev3] with w hw hw3
    refine ⟨timePartial_eq_zero_of_eventually_eq_zero hw, fun i =>
      spatialPartial_eq_zero_of_eventually_eq_zero hw i, fun i => ?_⟩
    exact spatialPartial_eq_zero_of_eventually_eq_zero
      (F := fun w' => spatialPartial (serrinCutoff x s ρ) i w')
      (hw3.mono (fun w' hw' => spatialPartial_eq_zero_of_eventually_eq_zero hw' i)) i
  refine ⟨spatialPartial_eq_zero_of_eventually_eq_zero ?_ j,
    spatialPartial_eq_zero_of_eventually_eq_zero ?_ j⟩
  · filter_upwards [hev] with w hw
    unfold serrinHeatWeight
    rw [hw, mul_zero]
  · filter_upwards [hder] with w ⟨h1, h2, h3⟩
    unfold serrinCutoffKernel
    simp only [h1, h2, h3, Finset.sum_const_zero, add_zero, mul_zero]

end CIV
