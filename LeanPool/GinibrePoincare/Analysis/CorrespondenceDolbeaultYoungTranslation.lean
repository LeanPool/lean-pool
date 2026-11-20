/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungTranslation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.GaussianClosedFormVolume
public import Mathlib.Topology.CompactOpen
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Correspondence Dolbeault Young translation

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultTranslateL2_norm`, `dolbeaultTranslateL2_continuous`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Complex `L²` with respect to Lebesgue measure on configurations. -/
abbrev dolbeaultOrdinaryL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (Configuration n))

/-- The translation `z ↦ z - Pi.single j y` of the `j`-th coordinate, as a continuous map. -/
def dolbeaultCoordinateTranslation {n : ℕ} (j : Fin n) (y : ℂ) :
    C(Configuration n, Configuration n) :=
  ⟨fun z => z-Pi.single j y, continuous_id.sub continuous_const⟩

theorem dolbeaultCoordinateTranslation_preserving {n : ℕ} (j : Fin n) (y : ℂ) :
    MeasurePreserving (dolbeaultCoordinateTranslation j y)
      (volume : Measure (Configuration n)) volume := by
  exact measurePreserving_sub_right (volume : Measure (Configuration n)) (Pi.single j y :
      Configuration n)

/-- Composition with `dolbeaultCoordinateTranslation j y`, as a linear isometry of ordinary
`L²`. -/
def dolbeaultTranslateL2 {n : ℕ} (j : Fin n) (y : ℂ) :
    dolbeaultOrdinaryL2 n →ₗᵢ[ℂ] dolbeaultOrdinaryL2 n :=
  Lp.compMeasurePreservingₗᵢ ℂ (dolbeaultCoordinateTranslation j y)
    (dolbeaultCoordinateTranslation_preserving j y)

theorem dolbeaultTranslateL2_norm {n : ℕ} (j : Fin n) (y : ℂ)
    (u : dolbeaultOrdinaryL2 n) : ‖dolbeaultTranslateL2 j y u‖=‖u‖ :=
  (dolbeaultTranslateL2 j y).norm_map u

theorem dolbeaultCoordinateTranslation_continuous {n : ℕ} (j : Fin n) :
    Continuous (dolbeaultCoordinateTranslation j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℂ × Configuration n => p.2-Pi.single j p.1)
  apply continuous_snd.sub
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simpa using continuous_fst
  · simpa [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : ℂ × Configuration n
      => (0 : ℂ)))

theorem dolbeaultTranslateL2_continuous {n : ℕ} (j : Fin n) (u : dolbeaultOrdinaryL2 n) :
    Continuous (fun y => dolbeaultTranslateL2 j y u) := by
  exact continuous_const.compMeasurePreservingLp (dolbeaultCoordinateTranslation_continuous j)
    (dolbeaultCoordinateTranslation_preserving j) (by norm_num)

end
end GinibrePoincare
