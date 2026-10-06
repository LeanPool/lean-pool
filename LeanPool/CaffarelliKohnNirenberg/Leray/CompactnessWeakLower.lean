/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeak

/-!
# Compactness Weak Lower

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace CKN.Leray

/-- A finite uniform L² seminorm bound passes to a weak Hilbert-space
limit with the same constant. -/
theorem eLpNorm_le_of_weak_l2_bounded
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (f : ℕ → α → E) (g : Lp E 2 μ)
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hweak : ∀ w, Tendsto
      (fun k => inner ℝ ((hf k).toLp (f k)) w) atTop
      (nhds (inner ℝ g w)))
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hbound : ∀ k, eLpNorm (f k) 2 μ ≤ B) :
    eLpNorm (fun z => g z) 2 μ ≤ B := by
  have hnorm (k : ℕ) :
      ‖(hf k).toLp (f k)‖ ≤ B.toReal := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hB.ne (hbound k)
  have hlim := norm_le_of_weak_tendsto_of_uniform_bound
    ENNReal.toReal_nonneg hnorm hweak
  rw [Lp.norm_def] at hlim
  have hlim' : (eLpNorm (fun z => g z) 2 μ).toReal ≤ B.toReal := hlim
  exact (ENNReal.toReal_le_toReal
    (Lp.eLpNorm_ne_top g) hB.ne).1 hlim'

end CKN.Leray
