/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.CutoffEnstrophyBalanceAnnulusBound
public import LeanPool.CIVAxisymmetric.Closure.CutoffExistence

/-!
# The annulus-confined cutoff of `lem:aniso:closure`

The closure argument tests the vorticity equation against a cutoff `χ` that is `1` on an inner
ball `B(ρ)` and supported in `B(Rstar)`, so that `∇χ` is carried by the closed annulus
`{ρ ≤ |x| ≤ Rstar}`. Every consumer of the tested enstrophy balance `eq:aniso:closure:tested`
asks for a closed set `A` carrying `fderiv χ` and contained in the open annulus
`{Rlo < |x| < Rhi}` on which `lem:aniso:annulus` bounds the velocity; a cutoff that is `1` at
the origin can never have `A` be a ball, so the closed annulus is the only shape that fits.

`CKN.canonicalBallCutoff 0 ρ Rstar` is such a cutoff: its derivative vanishes on the inner ball,
where it is constantly `1`, and off `B(Rstar)`, where it vanishes on a neighbourhood of every
point; what is left is exactly the closed annulus. Since `χ 0 = 1`, the data below is not the
degenerate `χ ≡ 0`, which satisfies every clause about `fderiv χ`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- Outside the closed annulus `{ρ ≤ |x| ≤ Rstar}` the canonical ball cutoff has vanishing
derivative: on the inner ball it is constantly `1`, and beyond `B(Rstar)` it is constantly `0`
on a neighbourhood. -/
theorem fderiv_canonicalBallCutoff_eq_zero_of_notMem_closedAnnulus {ρ Rstar : ℝ} (hρ : 0 < ρ)
    (hρR : ρ < Rstar) {x : Vec3}
    (hx : x ∉ {y : Vec3 | ρ ≤ vec3EuclideanNorm y ∧ vec3EuclideanNorm y ≤ Rstar}) :
    fderiv ℝ (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x = 0 := by
  have hRpos : 0 < Rstar := lt_trans hρ hρR
  simp only [Set.mem_ofPred_eq, not_and_or, not_le] at hx
  rcases hx with hlt | hgt
  · have hxin : x ∈ vec3Ball (0 : Vec3) ρ := by
      rw [mem_vec3Ball, sub_zero]; exact hlt
    have hev : (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) =ᶠ[nhds x] fun _ => (1 : ℝ) :=
      Filter.eventuallyEq_of_mem ((isOpen_vec3Ball (0 : Vec3) ρ).mem_nhds hxin) fun y hy =>
        CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hρR (by
          rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hρ])
    rw [hev.fderiv_eq]
    simp
  · have hnts : x ∉ tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) := by
      intro hxts
      have hsub := CKN.canonicalBallCutoff_tsupport_subset_outer hρ.le hρR hxts
      rw [euclideanBall_eq_vec3Ball (0 : Vec3) hRpos, mem_vec3Ball, sub_zero] at hsub
      linarith only [hsub, hgt]
    have hev : (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) =ᶠ[nhds x] fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem
        ((isClosed_tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar)).isOpen_compl.mem_nhds
          hnts) fun y hy => image_eq_zero_of_notMem_tsupport hy
    rw [hev.fderiv_eq]
    simp

/-- The canonical ball cutoff takes the value `1` at the centre of its inner ball. -/
theorem canonicalBallCutoff_zero_eq_one {ρ Rstar : ℝ} (hρ : 0 < ρ) (hρR : ρ < Rstar) :
    CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar 0 = 1 := by
  refine CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hρR ?_
  rw [euclideanBall_eq_vec3Ball (0 : Vec3) hρ, mem_vec3Ball, sub_zero]
  simpa [vec3EuclideanNorm] using hρ

/-- The cutoff data of `lem:aniso:closure`'s energy setup, with `∇χ` confined to the closed
annulus `{ρ ≤ |x| ≤ Rstar}`: the canonical ball cutoff is smooth and compactly supported inside
`B(Rstar)`, equals `1` on the inner ball `B(ρ)` — hence at the origin, so it is not identically
zero — and its derivative vanishes off that closed annulus. -/
theorem canonicalBallCutoff_closedAnnulus_data {ρ Rstar : ℝ} (hρ : 0 < ρ) (hρR : ρ < Rstar) :
    ContDiff ℝ (⊤ : ℕ∞) (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar)
      ∧ HasCompactSupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar)
      ∧ tsupport (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) ⊆ vec3Ball (0 : Vec3) Rstar
      ∧ (∀ x ∈ vec3Ball (0 : Vec3) ρ, CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar x = 1)
      ∧ IsClosed {y : Vec3 | ρ ≤ vec3EuclideanNorm y ∧ vec3EuclideanNorm y ≤ Rstar}
      ∧ (∀ x : Vec3, x ∉ {y : Vec3 | ρ ≤ vec3EuclideanNorm y ∧ vec3EuclideanNorm y ≤ Rstar} →
          fderiv ℝ (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) x = 0)
      ∧ CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar 0 = 1 := by
  have hRpos : 0 < Rstar := lt_trans hρ hρR
  refine ⟨CKN.canonicalBallCutoff_smooth (0 : Vec3) hρ.le hρR,
    CKN.canonicalBallCutoff_hasCompactSupport hρ.le hρR, ?_, ?_, isClosed_closedAnnulus ρ Rstar,
    fun x hx => fderiv_canonicalBallCutoff_eq_zero_of_notMem_closedAnnulus hρ hρR hx,
    canonicalBallCutoff_zero_eq_one hρ hρR⟩
  · intro y hy
    have hsub := CKN.canonicalBallCutoff_tsupport_subset_outer hρ.le hρR hy
    rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hRpos] at hsub
  · intro x hx
    exact CKN.canonicalBallCutoff_eq_one_on_inner hρ.le hρR (by
      rwa [euclideanBall_eq_vec3Ball (0 : Vec3) hρ])

/-- **The tested enstrophy balance `eq:aniso:closure:tested` for the canonical ball cutoff.**
With radii `Rlo < ρ < Rstar < Rhi` and `Rstar ≤ 1`, the gradient of
`CKN.canonicalBallCutoff 0 ρ Rstar` is carried by the closed annulus `{ρ ≤ |x| ≤ Rstar}`, which
sits inside the open annulus `{Rlo < |x| < Rhi}` of `lem:aniso:annulus`. The order-`≤ 2`
velocity bound there therefore discharges the pointwise velocity and vorticity hypotheses of
`cutoff_enstrophy_balance`, and the balance holds for a cutoff that is `1` on `B(ρ)`. -/
theorem cutoff_enstrophy_balance_canonicalBallCutoff
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsClassicalSolutionOn u p f unitCylinder) (hMf : ForceC2Bounded f)
    {ρ Rstar Rlo Rhi M : ℝ} (hρ : 0 < ρ) (hρR : ρ < Rstar) (hR1 : Rstar ≤ 1)
    (hRlo : Rlo < ρ) (hRhi : Rstar < Rhi) (hM : 0 ≤ M)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (-1 : ℝ) 0)
    (hbound : ∀ x : Vec3, Rlo < vec3EuclideanNorm x → vec3EuclideanNorm x < Rhi →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (0 : ℝ),
      HasDerivAt (cutoffEnstrophy (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) u)
          (deriv (cutoffEnstrophy (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) u) t) t ∧
        (1 / 2) * deriv (cutoffEnstrophy (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) u) t
            + cutoffEnstrophyDissipation (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) u t
          ≤ cutoffStretching (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) u t
            + C * (cutoffEnstrophy (CKN.canonicalBallCutoff (0 : Vec3) ρ Rstar) u t + 1) := by
  obtain ⟨hχ, hχs, hχsupp, -, -, hχA, -⟩ := canonicalBallCutoff_closedAnnulus_data hρ hρR
  exact cutoff_enstrophy_balance_of_multiPartial_le_closedAnnulus hsol hMf hχ hχs
    (hχsupp.trans (vec3Ball_mono hR1)) ht₀ hM hRlo hRhi hχA hbound

end CIV
