/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Domains
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Real-slice volume is the product Lebesgue measure on Fin n -> R. It is distinct from complex
ambient volume. The physical angle cell has side length 2 * pi; Fourier averaging uses unit cells.
Measures retain their extended nonnegative values until finiteness has been proved.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace KamProject.Arnold1963

/-- Product Lebesgue measure on real action coordinates. -/
def realLebesgue (n : ℕ) : MeasureTheory.Measure (RealSpace n) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ))

instance realLebesgue_sigmaFinite (n : ℕ) : MeasureTheory.SigmaFinite (realLebesgue n) :=
  inferInstanceAs (MeasureTheory.SigmaFinite
    (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ))))

/-- The Lebesgue measure of a complex action domain's real slice. -/
def realVolume {n : ℕ} (G : Set (ComplexSpace n)) : ℝ≥0∞ :=
  realLebesgue n (realSlice G)

theorem measurableSet_realSlice_of_isCompact {n : ℕ} {G : Set (ComplexSpace n)}
    (hG : IsCompact G) : MeasurableSet (realSlice G) :=
  (isCompact_realSlice hG).isClosed.measurableSet

theorem realVolume_mono {n : ℕ} {G H : Set (ComplexSpace n)} (hGH : G ⊆ H) :
    realVolume G ≤ realVolume H :=
  MeasureTheory.measure_mono (Set.preimage_mono hGH)

/-- A half-open fundamental angle cell of the specified period. -/
def realAngleCell (n : ℕ) (L : ℝ) : Set (RealSpace n) :=
  Set.pi Set.univ (fun _ => Set.Ioc 0 L)

/-- Product Lebesgue measure on real action and unwrapped angle coordinates. -/
def realPhaseLebesgue (n : ℕ) : MeasureTheory.Measure (RealSpace n × RealSpace n) :=
  (realLebesgue n).prod (realLebesgue n)

theorem realLebesgue_angleCell (n : ℕ) (L : ℝ) :
    realLebesgue n (realAngleCell n L) = ENNReal.ofReal L ^ n := by
  simp [realLebesgue, realAngleCell, MeasureTheory.Measure.pi_pi, Real.volume_Ioc]

theorem realPhaseLebesgue_cell {n : ℕ} (G : Set (ComplexSpace n)) (L : ℝ) :
    realPhaseLebesgue n (realSlice G ×ˢ realAngleCell n L) =
      realVolume G * ENNReal.ofReal L ^ n := by
  rw [realPhaseLebesgue, MeasureTheory.Measure.prod_prod, realLebesgue_angleCell]
  rfl

theorem realPhaseLebesgue_physicalCell {n : ℕ} (G : Set (ComplexSpace n)) :
    realPhaseLebesgue n (realSlice G ×ˢ realAngleCell n (2 * Real.pi)) =
      realVolume G * ENNReal.ofReal (2 * Real.pi) ^ n := realPhaseLebesgue_cell G _

theorem realPhaseLebesgue_unitCell {n : ℕ} (G : Set (ComplexSpace n)) :
    realPhaseLebesgue n (realSlice G ×ˢ realAngleCell n 1) = realVolume G := by
  simpa using realPhaseLebesgue_cell G 1

end KamProject.Arnold1963
