/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.AnnealedBlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.AnnealedSharpOrder
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioMonotone
public import LeanPool.HighContrastHomogenization.Geometry.AspectRatioOrder
public import LeanPool.HighContrastHomogenization.Geometry.BlockBridge
public import LeanPool.HighContrastHomogenization.Geometry.Canonical
public import LeanPool.HighContrastHomogenization.Geometry.CanonicalDeterminant
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Geometry.DetOrder
public import LeanPool.HighContrastHomogenization.Geometry.DeterminantLoss
public import LeanPool.HighContrastHomogenization.Geometry.GeometricMean
public import LeanPool.HighContrastHomogenization.Geometry.GeometricMeanToolkit
public import LeanPool.HighContrastHomogenization.Geometry.IntegralOrder
public import LeanPool.HighContrastHomogenization.Geometry.OperatorOrder
public import LeanPool.HighContrastHomogenization.Geometry.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceAspectRatio
public import LeanPool.HighContrastHomogenization.Geometry.ReferenceRadius
public import LeanPool.HighContrastHomogenization.Geometry.RelativeSize
public import LeanPool.HighContrastHomogenization.Geometry.SchurData
public import LeanPool.HighContrastHomogenization.Geometry.Sharp
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Geometry.SqrtOrder

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationSchur

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schur coordinates of the terminal response block

The first layer of the response-load calibration.  The printed calibration
writes the unrecentered terminal block in its unique Schur form

    E_t = (S + KᵗS_*⁻¹K, -KᵗS_*⁻¹; -S_*⁻¹K, S_*⁻¹),   S, S_* > 0,

and then works with the *response*, rather than canonical, coordinates
`h = ½(K - Kᵗ)`, `r = ½(K + Kᵗ)`, `B = S + rᵗS_*⁻¹r`, `m = B # S_*`, and the
response ratio `θ = |S_*^{-1/2}BS_*^{-1/2}|`.

This file supplies the two Schur orderings that the proof reads off the sharp
ordering `E_t^♯ ≤ E_t` and the imbalance ordering `E_t ≤ κ_t E_t^♯`, in a form
free of any vector manipulation: conjugating by the shear `G_{-Kᵗ}` sends both
`E_t` and `E_t^♯` to blocks whose upper-left corners are exactly the two sides
of the wanted scalar comparison.  Writing `𝐊 = K + Kᵗ = 2r`,

    G_{-Kᵗ}ᵗ E_t^♯ G_{-Kᵗ} = diag(S_*, S⁻¹),
    G_{-Kᵗ}ᵗ E_t  G_{-Kᵗ} = schurBlock S S_* 𝐊,

so the sharp ordering gives `S_* ≤ S` (through the lower-right corners, where
the two blocks are `S⁻¹` and `S_*⁻¹`) and the imbalance ordering gives
`S + 𝐊ᵗS_*⁻¹𝐊 ≤ κ_t S_*` (through the upper-left corners).  Since
`𝐊ᵗS_*⁻¹𝐊 = 4 rᵗS_*⁻¹r` this is a *fourfold* strengthening of `B ≤ κ_t S_*`,
which is the response-ratio bound `θ ≤ κ_t` of the printed chain
`1 ≤ θ ≤ (3κ_t-1)/2`.

**Route note.**  The printed derivation of `θ ≤ (3κ_t-1)/2` runs through
[Armstrong–Kuusi, (2.81)] and the upper half of [Armstrong–Kuusi, (2.82)], both of
which are false as printed (the counterexample at Schur
data `σ_* = 1, σ = 9, k = 4` exceeds both).  The route here does not use them:
it reads the imbalance ordering once, at the vector whose second Schur
coordinate vanishes, and yields the strictly stronger `θ ≤ κ_t`; the printed
`(3κ_t-1)/2` then follows from `1 ≤ κ_t`.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Shear conjugation of the Schur form -/

/-- **Conjugation by a shear translates the skew coordinate.**  The Schur form
is `G_{-k}ᵗ diag(s, s_*⁻¹) G_{-k}`, and shears compose additively. -/
theorem schurBlock_conj_shear (s sStar k c : Mat d) :
    (fullBlockShear c)ᴴ * schurBlock s sStar k * fullBlockShear c =
      schurBlock s sStar (k - c) := by
  have hmul : fullBlockShear (-(k - c)) = fullBlockShear (-k) * fullBlockShear c := by
    rw [fullBlockShear_mul]
    congr 1
    abel
  simp only [schurBlock, hmul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- The Schur form at a vanishing skew coordinate is the diagonal block. -/
theorem schurBlock_zero (s sStar : Mat d) :
    schurBlock s sStar 0 = Matrix.fromBlocks s 0 0 sStar⁻¹ := by
  rw [schurBlock_eq]
  simp

/-- Conjugation commutes with the scalar dilation. -/
theorem conj_smul (C X : Matrix (BlockCoord d) (BlockCoord d) ℝ) (c : ℝ) :
    Cᴴ * (c • X) * C = c • (Cᴴ * X * C) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ## The two Schur orderings -/

variable {S SStar K : Mat d}

/-- **The imbalance ordering in doubled Schur coordinates.** -/
theorem schurBlock_doubled_le_smul_diag (hS : S.PosDef) (hStar : SStar.PosDef) {c : ℝ}
    (h : schurBlock S SStar K ≤ c • fullBlockSharp (schurBlock S SStar K)) :
    schurBlock S SStar (K + Kᴴ) ≤
      c • (Matrix.fromBlocks SStar 0 0 S⁻¹ : FullBlockMat d) := by
  have h' := conj_le_conj (fullBlockShear (-Kᴴ)) h
  rw [conj_smul, fullBlockSharp_schurBlock hS hStar, schurBlock_conj_shear,
    schurBlock_conj_shear, show -Kᴴ - -Kᴴ = (0 : Mat d) by abel,
    show K - -Kᴴ = K + Kᴴ by abel, schurBlock_zero] at h'
  exact h'

/-! ## The two scalar consequences -/

/-- **The Schur ordering** `S_* ≤ S`, from the lower-right corners of the sharp
ordering: there they are `S⁻¹ ≤ S_*⁻¹`. -/
theorem schurStar_le_schur (hS : S.PosDef) (hStar : SStar.PosDef)
    (hsharp : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K) :
    SStar ≤ S := by
  have h22 := toBlocks₂₂_mono hsharp
  rw [fullBlockSharp_schurBlock hS hStar, toBlocks₂₂_schurBlock,
    toBlocks₂₂_schurBlock] at h22
  have h := inv_le_inv_of_le hS.inv hStar.inv h22
  rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStar),
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hS)] at h

/-- **The fourfold upper-left bound.**  From `E_t ≤ c E_t^♯` the upper-left
corners of the conjugated blocks give `S + 𝐊ᵗS_*⁻¹𝐊 ≤ c S_*`, with
`𝐊 = K + Kᵗ`. -/
theorem schur_doubled_bound (hS : S.PosDef) (hStar : SStar.PosDef) {c : ℝ}
    (h : schurBlock S SStar K ≤ c • fullBlockSharp (schurBlock S SStar K)) :
    S + (K + Kᴴ)ᴴ * SStar⁻¹ * (K + Kᴴ) ≤ c • SStar := by
  have h11 := toBlocks₁₁_mono (schurBlock_doubled_le_smul_diag hS hStar h)
  rw [toBlocks₁₁_schurBlock] at h11
  have hsm : (c • (Matrix.fromBlocks SStar 0 0 S⁻¹ : FullBlockMat d)).toBlocks₁₁ =
      c • SStar := by
    ext i j
    simp [Matrix.toBlocks₁₁]
  rwa [hsm] at h11

end

end Response
end HighContrast
end HCPolySupport
