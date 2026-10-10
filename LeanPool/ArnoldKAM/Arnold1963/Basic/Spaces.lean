/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Isometry

/-!
The real and complex coordinate spaces use the maximum norm. Phase coordinates are ordered
(p, q). Fourier indices use the sum of absolute coordinates, separately from the ambient norm.
-/

@[expose] public section

noncomputable section

namespace KamProject.Arnold1963

/-- Real coordinate space with the supremum norm. -/
abbrev RealSpace (n : ℕ) := Fin n → ℝ
/-- Complex coordinate space with the supremum norm. -/
abbrev ComplexSpace (n : ℕ) := Fin n → ℂ
/-- Integer Fourier indices for the angle coordinates. -/
abbrev FourierIndex (n : ℕ) := Fin n → ℤ
/-- Complex action coordinates paired with complex angle coordinates. -/
abbrev ComplexPhaseSpace (n : ℕ) := ComplexSpace n × ComplexSpace n

/-- Coordinatewise embedding of real vectors into complex coordinate space. -/
def complexify {n : ℕ} (x : RealSpace n) : ComplexSpace n := fun j => (x j : ℂ)

@[simp] theorem complexify_zero {n : ℕ} : complexify (0 : RealSpace n) = 0 := by
  ext j
  simp [complexify]

theorem isometry_complexify (n : ℕ) : Isometry (complexify (n := n)) :=
  Isometry.piMap (fun _ : Fin n => ((↑) : ℝ → ℂ)) (fun _ => Complex.isometry_ofReal)

theorem continuous_complexify (n : ℕ) : Continuous (complexify (n := n)) :=
  (isometry_complexify n).continuous

/-- Coordinatewise complex conjugation of an action or angle vector. -/
def conjVec {n : ℕ} (z : ComplexSpace n) : ComplexSpace n := fun j => star (z j)

/-- Coordinatewise real part of a complex vector. -/
def realPart {n : ℕ} (z : ComplexSpace n) : RealSpace n := fun j => (z j).re
/-- Coordinatewise imaginary part of a complex vector. -/
def imagPart {n : ℕ} (z : ComplexSpace n) : RealSpace n := fun j => (z j).im

/-- Coordinatewise conjugation of both action and angle components. -/
def conjPhase {n : ℕ} (z : ComplexPhaseSpace n) : ComplexPhaseSpace n :=
  (conjVec z.1, conjVec z.2)

@[simp] theorem conjPhase_eq_star {n : ℕ} (x : ComplexPhaseSpace n) : conjPhase x = star x := rfl
@[simp] theorem conjVec_eq_star {n : ℕ} (x : ComplexSpace n) : conjVec x = star x := rfl

@[simp] theorem star_complexify {n : ℕ} (x : RealSpace n) :
    star (complexify x) = complexify x := by
  ext j
  simp [complexify]

/-- The real-valued sum of absolute Fourier coordinates. -/
def indexLength {n : ℕ} (k : FourierIndex n) : ℝ := ∑ j, |(k j : ℝ)|

/-- The bilinear pairing of an integer Fourier index with a complex vector. -/
def indexPairing {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) : ℂ :=
  ∑ j, (k j : ℂ) * z j

theorem complex_norm_le_iff {n : ℕ} (z : ComplexSpace n) {r : ℝ} (hr : 0 ≤ r) :
    ‖z‖ ≤ r ↔ ∀ j, ‖z j‖ ≤ r :=
  pi_norm_le_iff_of_nonneg hr

theorem real_norm_le_iff {n : ℕ} (x : RealSpace n) {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ ≤ r ↔ ∀ j, |x j| ≤ r := by
  simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hr (x := x))

@[simp] theorem norm_complexify {n : ℕ} (x : RealSpace n) : ‖complexify x‖ = ‖x‖ := by
  simpa only [complexify_zero, dist_zero_right] using (isometry_complexify n).dist_eq x 0

theorem complex_coordinate_norm_le {n : ℕ} (z : ComplexSpace n) (j : Fin n) :
    ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j

theorem phase_norm_eq {n : ℕ} (z : ComplexPhaseSpace n) :
    ‖z‖ = max ‖z.1‖ ‖z.2‖ := rfl

@[simp] theorem realPart_complexify {n : ℕ} (x : RealSpace n) :
    realPart (complexify x) = x := by
  funext j
  simp [realPart, complexify]

@[simp] theorem imagPart_complexify {n : ℕ} (x : RealSpace n) :
    imagPart (complexify x) = 0 := by
  funext j
  simp [imagPart, complexify]

theorem conjVec_complexify {n : ℕ} (x : RealSpace n) :
    conjVec (complexify x) = complexify x := by
  funext j
  simp [conjVec, complexify]

theorem conjVec_conjVec {n : ℕ} (z : ComplexSpace n) :
    conjVec (conjVec z) = z := by
  funext j
  simp [conjVec]

theorem indexLength_nonneg {n : ℕ} (k : FourierIndex n) : 0 ≤ indexLength k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem norm_indexPairing_le {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) :
    ‖indexPairing k z‖ ≤ indexLength k * ‖z‖ := by
  calc
    ‖indexPairing k z‖ ≤ ∑ j, ‖(k j : ℂ) * z j‖ := norm_sum_le _ _
    _ = ∑ j, |(k j : ℝ)| * ‖z j‖ := by simp [Complex.norm_intCast]
    _ ≤ ∑ j, |(k j : ℝ)| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (complex_coordinate_norm_le z j) (abs_nonneg _)
    _ = indexLength k * ‖z‖ := by rw [indexLength, Finset.sum_mul]

end KamProject.Arnold1963
