/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceConvergence
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakAELimit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Compactness Product Slices

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- Strong convergence on a product has a subsequence converging pointwise
almost everywhere on almost every spatial slice. -/
theorem exists_subsequence_ae_slices_of_strong_product_l2
    {K : Set Vec3} {J : Set ℝ}
    (f : ℕ → Vec3 × ℝ → L2Vec3) (g : Vec3 × ℝ → L2Vec3)
    (hf : ∀ n, MemLp (f n) 2
      ((volume.restrict K).prod (volume.restrict J)))
    (hg : MemLp g 2
      ((volume.restrict K).prod (volume.restrict J)))
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2
      ((volume.restrict K).prod (volume.restrict J))) atTop (nhds 0)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∀ᵐ t ∂(volume.restrict J), ∀ᵐ x ∂(volume.restrict K),
        Tendsto (fun k => f (τ k) (x,t)) atTop (nhds (g (x,t))) := by
  let μ : Measure Vec3 := volume.restrict K
  let ν : Measure ℝ := volume.restrict J
  have hconvSwap : Tendsto
      (fun n => eLpNorm
        ((fun z : ℝ × Vec3 => f n z.swap) -
          (fun z : ℝ × Vec3 => g z.swap)) 2 (ν.prod μ))
      atTop (nhds 0) := by
    have heq (n : ℕ) : eLpNorm
        ((fun z : ℝ × Vec3 => f n z.swap) -
          (fun z : ℝ × Vec3 => g z.swap)) 2 (ν.prod μ) =
        eLpNorm (f n - g) 2 (μ.prod ν) := by
      have h := eLpNorm_comp_measurePreserving (p := 2)
        ((hf n).sub hg).aestronglyMeasurable
        (Measure.measurePreserving_swap (μ := ν) (ν := μ))
      change eLpNorm (fun z : ℝ × Vec3 => f n z.swap - g z.swap) 2
        (ν.prod μ) = eLpNorm (f n - g) 2 (μ.prod ν)
      exact h
    simpa only [heq] using hconv
  obtain ⟨τ, hτ, hae⟩ :=
    CKN.stability_exists_subsequence_ae_slices_of_eLpNorm_tendsto
      μ ν 2 (by norm_num)
      (fun n (z : ℝ × Vec3) => f n z.swap)
      (fun z : ℝ × Vec3 => g z.swap) hconvSwap
  exact ⟨τ, hτ, hae⟩

end CKN.Leray
