/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import Mathlib.Init



/-!
# FourNeighborLaplacianProperties

Shared facts adapted from Wesley Pegden's Apache-2.0 Trellis formalization of
Levine–Pegden–Smart, replacing repeated implementations at their common dependency level.
-/

@[expose] public section

namespace ApollonianSuperharmonic
namespace FourNeighborLaplacianProperties

/-- Shared differences identity for FourNeighborLaplacianProperties. -/
theorem differences :
    (by
      classical
      exact
        ∀ (g : IntegerLatticeFunction), ∀ (x : GaussianInt), FourNeighborLaplacian g x = g (x +
            (1 : GaussianInt)) - g x + (g (x - (1 : GaussianInt)) - g x) + (g (x + ⟨(0 : ℤ), (1 :
            ℤ)⟩) - g x) + (g (x - ⟨(0 : ℤ), (1 : ℤ)⟩) - g x) ) := by
  classical
  intro g x
  unfold FourNeighborLaplacian
  ring

/-- Affine perturbations and translation preserve the four-neighbor Laplacian. -/
theorem affineTranslate :
    ∀ (f : GaussianInt → ℤ), ∀ (f' : GaussianInt → ℤ), ∀ (x : GaussianInt), ∀ (t : GaussianInt),
        ∀ (A : ℤ), ∀ (B : ℤ), ∀ (C : ℤ), f x = f' (x - t) + A * x.re + B * x.im + C → f (x - (1 :
        GaussianInt)) = f' (x - t - (1 : GaussianInt)) + A * (x - (1 : GaussianInt)).re + B * (x
        - (1 : GaussianInt)).im + C → f (x + (1 : GaussianInt)) = f' (x - t + (1 : GaussianInt))
        + A * (x + (1 : GaussianInt)).re + B * (x + (1 : GaussianInt)).im + C → f (x - ⟨(0 : ℤ),
        (1 : ℤ)⟩) = f' (x - t - ⟨(0 : ℤ), (1 : ℤ)⟩) + A * (x - ⟨(0 : ℤ), (1 : ℤ)⟩).re + B * (x -
        ⟨(0 : ℤ), (1 : ℤ)⟩).im + C → f (x + ⟨(0 : ℤ), (1 : ℤ)⟩) = f' (x - t + ⟨(0 : ℤ), (1 : ℤ)⟩)
        + A * (x + ⟨(0 : ℤ), (1 : ℤ)⟩).re + B * (x + ⟨(0 : ℤ), (1 : ℤ)⟩).im + C →
        FourNeighborLaplacian f x = FourNeighborLaplacian f' (x - t) := by
  classical
  intro f f' x t A B C h0 hm hp hmi hpi
  rw [FourNeighborLaplacian, hm, hp, hmi, hpi, h0,
    FourNeighborLaplacian]
  rw [show x - t - 1 = (x - t) - 1 by abel,
    show x - t + 1 = (x - t) + 1 by abel,
    show x - t - ⟨0, 1⟩ = (x - t) - ⟨0, 1⟩ by rfl,
    show x - t + ⟨0, 1⟩ = (x - t) + ⟨0, 1⟩ by rfl]
  simp
  ring

/-- A rectangular affine identity supplies all five values of a lattice neighborhood. -/
theorem affineValuesOnRectangle (f g : IntegerLatticeFunction) (x t : GaussianInt)
    (A B C lowerReal upperReal lowerImaginary upperImaginary : ℤ)
    (hxr : lowerReal + 1 ≤ x.re) (hxr' : x.re ≤ upperReal - 1)
    (hxi : lowerImaginary + 1 ≤ x.im) (hxi' : x.im ≤ upperImaginary - 1)
    (values : ∀ z : GaussianInt, lowerReal ≤ z.re → z.re ≤ upperReal →
      lowerImaginary ≤ z.im → z.im ≤ upperImaginary →
        f z = g (z - t) + A * z.re + B * z.im + C) :
    f x = g (x - t) + A * x.re + B * x.im + C ∧
    f (x - 1) = g ((x - t) - 1) + A * (x - 1).re + B * (x - 1).im + C ∧
    f (x + 1) = g ((x - t) + 1) + A * (x + 1).re + B * (x + 1).im + C ∧
    f (x - ⟨0, 1⟩) = g ((x - t) - ⟨0, 1⟩) +
      A * (x - ⟨0, 1⟩).re + B * (x - ⟨0, 1⟩).im + C ∧
    f (x + ⟨0, 1⟩) = g ((x - t) + ⟨0, 1⟩) +
      A * (x + ⟨0, 1⟩).re + B * (x + ⟨0, 1⟩).im + C := by
  have point (d : GaussianInt)
      (hd : d = 0 ∨ d = -1 ∨ d = 1 ∨ d = -⟨0, 1⟩ ∨ d = ⟨0, 1⟩) :
      f (x + d) = g ((x - t) + d) + A * (x + d).re + B * (x + d).im + C := by
    have bounds : lowerReal ≤ (x + d).re ∧ (x + d).re ≤ upperReal ∧
        lowerImaginary ≤ (x + d).im ∧ (x + d).im ≤ upperImaginary := by
      rcases hd with rfl | rfl | rfl | rfl | rfl <;>
        simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_neg, Zsqrtd.im_neg,
          Zsqrtd.re_zero, Zsqrtd.im_zero, Zsqrtd.re_one, Zsqrtd.im_one] <;> omega
    have shift : (x + d) - t = (x - t) + d := by ring
    simpa only [shift] using values (x + d) bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using point 0 (Or.inl rfl)
  · simpa only [← sub_eq_add_neg] using point (-1) (Or.inr (Or.inl rfl))
  · exact point 1 (Or.inr (Or.inr (Or.inl rfl)))
  · simpa only [← sub_eq_add_neg] using point (-⟨0, 1⟩) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact point ⟨0, 1⟩ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end FourNeighborLaplacianProperties
end ApollonianSuperharmonic

end
