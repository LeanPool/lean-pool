/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Configuration

/-!
# Coulomb interactions

Electron and nuclear interactions, nearest-nucleus distances, and the electrostatic correction
in Baxter’s inequality.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Nonnegative Coulomb interaction, with infinite value at a collision. -/
@[expose] noncomputable def coulombKernel (x y : Position) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

/-- Sum the Coulomb interactions over each unordered pair of electrons. -/
@[expose] noncomputable def electronRepulsion {N : ℕ} (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    coulombKernel (particlePosition x i) (particlePosition x j)

/-- Sum electron–nucleus Coulomb interactions weighted by the nuclear charges. -/
@[expose] noncomputable def attraction {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel (particlePosition x i) (R k)

/-- Sum the charge-weighted Coulomb interactions over unordered pairs of nuclei. -/
@[expose] noncomputable def nuclearRepulsion {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  ∑ k : Fin M, ∑ l ∈ Finset.univ.filter (fun l : Fin M => k < l),
    ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l)

/-- The nearest nuclear distance, with infinite value when there are no nuclei. -/
@[expose] noncomputable def nearestNucleusDistance {M : ℕ}
    (R : Fin M → Position) (x : Position) : ℝ≥0∞ :=
  ⨅ k : Fin M, ENNReal.ofReal ‖x - R k‖

/-- The nearest distance to another nucleus, with infinite value for a single nucleus. -/
@[expose] noncomputable def nearestOtherNucleusDistance {M : ℕ}
    (R : Fin M → Position) (k : Fin M) : ℝ≥0∞ :=
  ⨅ l : {l : Fin M // l ≠ k}, ENNReal.ofReal ‖R k - R l‖

/-- Nearest-nucleus inverse-distance control with the electrostatic screening coefficient. -/
@[expose] noncomputable def nearestNucleusControl {N M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  (2 * (Z : ℝ≥0∞) + 1) *
    ∑ i : Fin N, (nearestNucleusDistance R (particlePosition x i))⁻¹

/-- The positive nearest-other-nucleus correction in Baxter’s inequality. -/
@[expose] noncomputable def baxterCorrection {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  (Z : ℝ≥0∞) ^ 2 / 4 * ∑ k : Fin M, (nearestOtherNucleusDistance R k)⁻¹

end LiebThirring

end
