/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.TestFunction
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Is In J

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Smooth compactly supported approximants to the source space `J` in
`def:leray-hopf`, expressed as a convergent sequence. -/
@[expose]
def IsInJ (a : Vec3 → Vec3) : Prop :=
  MemLp a (2 : ℝ≥0∞) volume ∧
    ∃ aSeq : ℕ → Vec3 → Vec3,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (aSeq k)) ∧
      (∀ k, HasCompactSupport (aSeq k)) ∧
      (∀ k x, ∑ i : Fin 3, spatialDeriv (fun y => aSeq k y i) i x = 0) ∧
      Tendsto
        (fun k => eLpNorm (fun x => aSeq k x - a x) (2 : ℝ≥0∞) volume)
        atTop (nhds 0)

end CKN
