/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Step functions and their Lebesgue autoconvolution norm ratio
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Autoconvolutions

/-- On the cell `[j,j + 1)` use the real coefficient `p j`. Outside the
union of the cells the sum is zero. The indices range from zero through d. -/
noncomputable def step (d : ℕ) (p : Fin (d + 1) → ℝ) (x : ℝ) : ℝ :=
  ∑ j, (Set.Ico (j.val : ℝ) ((j.val : ℝ) + 1)).indicator (fun _ => p j) x

/-- The additive autoconvolution on the real line with Lebesgue measure. -/
noncomputable def auto (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, f t * f (x - t) ∂volume

/-- The square of the L² norm of the autoconvolution divided by the product
of its L¹ norm and its essential - supremum norm, all for Lebesgue measure. -/
noncomputable def ratio (f : ℝ → ℝ) : ℝ :=
  (eLpNorm (auto f) 2 volume).toReal ^ 2 /
    ((eLpNorm (auto f) 1 volume).toReal * (eLpNorm (auto f) ∞ volume).toReal)

end Autoconvolutions
