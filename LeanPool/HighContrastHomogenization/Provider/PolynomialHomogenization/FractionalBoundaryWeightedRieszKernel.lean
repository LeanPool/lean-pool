/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalBoundaryWeightedFarKernel
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalBoundaryWeightedNearKernel

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.FractionalBoundaryWeightedRieszKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional Riesz kernel against a convex boundary weight
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The complete Riesz potential of `delta^(-p)` has homogeneous order
`delta^(s-p)` for `0<s<p<1`. -/
theorem exists_bound_lintegral_fractionalBoundaryRieszKernel
    (hd : 1 ≤ d) {rho Rad s p : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad) (hs : 0 < s)
    (hsp : s < p) (hp1 : p < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad → ∀ x ∈ U,
          (∫⁻ y in U,
            ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
              euclideanBoundaryWeight U p y ∂volume) ≤
            C * ENNReal.ofReal
              (euclideanBoundaryDistance U x ^ (s - p)) := by
  obtain ⟨Cnear, hCnearTop, hnear⟩ :=
    exists_bound_lintegral_near_fractionalBoundaryKernel
      hd hs (hs.trans hsp).le hsp hp1
  obtain ⟨Cfar, hCfarTop, hfar⟩ :=
    exists_bound_lintegral_far_fractionalBoundaryKernel
      hd hrho hRad hs hsp hp1
  let C := Cnear + Cfar
  refine ⟨C, ENNReal.add_ne_top.mpr ⟨hCnearTop, hCfarTop⟩, ?_⟩
  intro U hU hsand x hx
  let ball := euclideanBallAt x (euclideanBoundaryDistance U x / 2)
  let f : Vec d → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
      euclideanBoundaryWeight U p y
  have hcover : U ⊆ (U ∩ ball) ∪ (U \ ball) := by
    intro y hy
    by_cases hyball : y ∈ ball
    · exact Or.inl ⟨hy, hyball⟩
    · exact Or.inr ⟨hy, hyball⟩
  have hn := hnear U hU x hx
  have hf := hfar U hU hsand x hx
  change (∫⁻ y in U ∩ ball, f y ∂volume) ≤ _ at hn
  change (∫⁻ y in U \ ball, f y ∂volume) ≤ _ at hf
  calc
    (∫⁻ y in U,
        ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
          euclideanBoundaryWeight U p y ∂volume) ≤
        ∫⁻ y in (U ∩ ball) ∪ (U \ ball), f y ∂volume :=
      lintegral_mono_set hcover
    _ ≤ (∫⁻ y in U ∩ ball, f y ∂volume) +
        ∫⁻ y in U \ ball, f y ∂volume := lintegral_union_le _ _ _
    _ ≤ Cnear * ENNReal.ofReal
          (euclideanBoundaryDistance U x ^ (s - p)) +
        Cfar * ENNReal.ofReal
          (euclideanBoundaryDistance U x ^ (s - p)) := add_le_add hn hf
    _ = C * ENNReal.ofReal
        (euclideanBoundaryDistance U x ^ (s - p)) := by
      dsimp only [C]
      rw [add_mul]

end

end HighContrast
end HCPolySupport
