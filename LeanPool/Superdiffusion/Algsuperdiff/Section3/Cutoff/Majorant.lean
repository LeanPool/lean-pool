/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Control
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicPartition
public import LeanPool.HighContrastHomogenization.Support.Geometry.TriadicCubeTranslation

/-!
# Majorant

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic lower-tail majorants

The probabilistic lower-tail argument uses a polynomially weighted geometric
majorant.  This module is deterministic: it contains neither a law nor an
almost-everywhere assertion.
-/

open scoped BigOperators

namespace Algsuperdiff.Section3.Cutoff

open HCPolySupport

noncomputable section

/-- The scale profile used to dominate the local control of the shell indexed
by `m - r` on the cube at scale `ell`. -/
def cubeMajorant (gamma : ℝ) (m ell : ℤ) (r : ℕ) : ℝ :=
  Real.sqrt (1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0) *
    Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ)))

theorem cubeMajorant_nonneg (gamma : ℝ) (m ell : ℤ) (r : ℕ) :
    0 ≤ cubeMajorant gamma m ell r := by
  unfold cubeMajorant
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _)

private theorem cubeMajorant_sqrt_le (m ell : ℤ) (r : ℕ) :
    Real.sqrt (1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0) ≤
      1 + |(ell : ℝ) - (m : ℝ)| + (r : ℝ) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have habs : 0 ≤ |(ell : ℝ) - (m : ℝ)| := abs_nonneg _
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hmax : max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0 ≤
        |(ell : ℝ) - (m : ℝ)| + (r : ℝ) := by
      rw [max_le_iff]
      constructor
      · have hle : (ell : ℝ) - (m : ℝ) ≤ |(ell : ℝ) - (m : ℝ)| :=
          le_abs_self _
        linarith
      · linarith
    have hone : 1 ≤ 1 + |(ell : ℝ) - (m : ℝ)| + (r : ℝ) := by
      linarith
    nlinarith

private theorem cubeMajorant_rpow_factor (gamma : ℝ) (m : ℤ) (r : ℕ) :
    Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))) =
      Real.rpow 3 (gamma * (m : ℝ)) * (Real.rpow 3 (-gamma)) ^ r := by
  calc
    Real.rpow 3 (gamma * ((m : ℝ) - (r : ℝ))) =
        Real.rpow 3 (gamma * (m : ℝ) + (-gamma) * (r : ℝ)) := by ring_nf
    _ = Real.rpow 3 (gamma * (m : ℝ)) *
        Real.rpow 3 ((-gamma) * (r : ℝ)) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    _ = Real.rpow 3 (gamma * (m : ℝ)) *
        (Real.rpow 3 (-gamma)) ^ r := by
      congr 1
      calc
        Real.rpow 3 ((-gamma) * (r : ℝ)) =
            (Real.rpow 3 (-gamma)) ^ (r : ℝ) := by
          exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (-gamma) (r : ℝ)
        _ = (Real.rpow 3 (-gamma)) ^ r := by
          rw [Real.rpow_natCast]

/-- Positive scaling exponents make the lower-half majorant summable. -/
theorem summable_cubeMajorant {gamma : ℝ} (hgamma : 0 < gamma)
    (m ell : ℤ) : Summable (cubeMajorant gamma m ell) := by
  let q : ℝ := Real.rpow 3 (-gamma)
  let C : ℝ := 1 + |(ell : ℝ) - (m : ℝ)|
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq_nonneg]
    exact hq_lt_one
  have hgeometric : Summable (fun r : ℕ => q ^ r) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hq_norm)
  have hlinear : Summable (fun r : ℕ => (r : ℝ) * q ^ r) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq_norm)
  have hpolynomial : Summable (fun r : ℕ => (C + (r : ℝ)) * q ^ r) := by
    have hsum := (hgeometric.mul_left C).add hlinear
    simpa only [Pi.add_apply, Pi.mul_apply, mul_add, add_mul] using hsum
  let A : ℝ := Real.rpow 3 (gamma * (m : ℝ))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdom : ∀ r : ℕ, cubeMajorant gamma m ell r ≤
      A * ((C + (r : ℝ)) * q ^ r) := by
    intro r
    rw [cubeMajorant, cubeMajorant_rpow_factor]
    have hsqrt := cubeMajorant_sqrt_le m ell r
    have hqpow : 0 ≤ q ^ r := pow_nonneg hq_nonneg _
    have hC : 0 ≤ C + (r : ℝ) := by
      dsimp [C]
      positivity
    calc
      Real.sqrt (1 + max ((ell : ℝ) - ((m : ℝ) - (r : ℝ))) 0) *
          (A * q ^ r) ≤ (C + (r : ℝ)) * (A * q ^ r) :=
        mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hA_nonneg hqpow)
      _ = A * ((C + (r : ℝ)) * q ^ r) := by ring
  exact Summable.of_nonneg_of_le
    (fun r => cubeMajorant_nonneg gamma m ell r)
    hdom
    (hpolynomial.mul_left A)

/-- The finite lattice of unit triadic descendants covers a nonnegative-scale
origin cube.  The half-open realization gives an exact cover, including the
internal partition boundaries. -/
theorem cubeSet_originCube_subset_iUnion_unitDescendants (d : ℕ) (q : ℤ)
    (hq : 0 ≤ q) :
    cubeSet (originCube d q) ⊆
      ⋃ R ∈ (descendantsAtScale (originCube d q) 0 : Set (TriadicCube d)),
        cubeSet R := by
  exact cubeSet_subset_iUnion_descendantsAtScale (originCube d q) hq

/-- The unit-descendant lattice has the expected finite cardinality. -/
theorem card_unitDescendants_originCube (d : ℕ) (q : ℤ) (hq : 0 ≤ q) :
    (descendantsAtScale (originCube d q) 0).card = (3 ^ d) ^ q.toNat := by
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d q) hq,
    descendantsAtDepth_card]
  simp [originCube]

end

end Algsuperdiff.Section3.Cutoff
