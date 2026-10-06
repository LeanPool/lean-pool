/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationSchur
public import LeanPool.HighContrastHomogenization.Provider.SourceControl.ReferenceIntermediate

/-!
# High-contrast homogenization: Provider.Response.LoadCalibrationTheta

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response ratio against the canonical imbalance

The response-ratio calibration of the response loads, read through the canonical
imbalance `e.response.canonical.imbalance`:

    1 ≤ θ ≤ (3κ_t - 1)/2,      κ_t - 1 ≤ 6(θ - 1),

for `θ = |S_*^{-1/2}BS_*^{-1/2}|`, `B = S + rᵗS_*⁻¹r`, `r = ½(K + Kᵗ)`, and
`κ_t = 𝔡(E_t)` the canonical imbalance of the terminal block.

The two halves go in opposite directions and are proved by different routes.

* `θ ≤ κ_t` (hence `θ ≤ (3κ_t-1)/2`, since `1 ≤ κ_t`) is read directly off the
  imbalance ordering `E_t ≤ κ_t E_t^♯` at the vector whose second Schur
  coordinate vanishes: this is the fourfold bound
  `S + 𝐊ᵗS_*⁻¹𝐊 ≤ κ_t S_*` of `LoadCalibrationSchur`, and `B` is smaller than
  its left side because `𝐊ᵗS_*⁻¹𝐊 = 4rᵗS_*⁻¹r`.

* `κ_t ≤ 1 + 6(θ - 1)` is the repaired reference intermediate
  `Initialization.kappaRef_le_of_matLoewnerLE_skewCorrectedForm`, applied at the skew
  `h = ½(K - Kᵗ)`, for which the skew-corrected Schur form is exactly `B` and
  the admissible scaling is exactly `θ`.

**Route note.**  The printed proof obtains both halves
from [Armstrong–Kuusi, (2.81),(2.82)] through the *uncorrected* ratio
`θ̃ = |S_*^{-1/2}SS_*^{-1/2}|`.  Both of those displays are false as printed —
the counterexample `σ_* = 1, σ = 9, k = 4` gives `64 > 16` in (2.81) and
`80 > 48` in the upper half of (2.82) — and neither is used here.  The
conclusions of the printed lemma are unchanged; only the route is.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## A norm identity above the identity -/

/-- **`‖X - I‖ = ‖X‖ - 1` above the identity.**  If `X` is positive
semidefinite and `I ≤ X`, then subtracting the identity subtracts one from the
spectral norm.  This is the display `|S_*^{-1/2}BS_*^{-1/2} - Id| = θ - 1`. -/
theorem norm_sub_one_eq_norm_sub_one {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {X : Matrix n n ℝ} (hX : X.PosSemidef) (h1 : (1 : Matrix n n ℝ) ≤ X) :
    ‖X - 1‖ = ‖X‖ - 1 := by
  have hsub : (X - 1).PosSemidef := Matrix.le_iff.mp h1
  have hone : (1 : ℝ) ≤ ‖X‖ := by
    have := norm_le_norm_of_le (Matrix.PosSemidef.one) hX h1
    rwa [norm_one] at this
  refine le_antisymm ?_ ?_
  · refine norm_le_of_le_smul_one hsub (by linarith only [hone]) ?_
    have hXle : X ≤ ‖X‖ • (1 : Matrix n n ℝ) := le_norm_smul_one hX
    have hrw : (‖X‖ - 1) • (1 : Matrix n n ℝ) = ‖X‖ • (1 : Matrix n n ℝ) - 1 := by
      rw [sub_smul, one_smul]
    rw [hrw]
    exact sub_le_sub_right hXle 1
  · have hXle : X ≤ (‖X - 1‖ + 1) • (1 : Matrix n n ℝ) := by
      have hsuble : X - 1 ≤ ‖X - 1‖ • (1 : Matrix n n ℝ) := le_norm_smul_one hsub
      have h2 := add_le_add hsuble (le_refl (1 : Matrix n n ℝ))
      have h3 : X - 1 + 1 = X := by abel
      rw [h3] at h2
      rw [add_smul, one_smul]
      exact h2
    have := norm_le_of_le_smul_one hX (by positivity) hXle
    linarith only [this]

/-- On real data the ambient transpose is mathlib's conjugate transpose. -/
theorem conjTranspose_eq_matTranspose (A : Mat d) : Aᴴ = matTranspose A :=
  HCPolySupport.HighContrast.conjTranspose_eq_matTranspose A

/-! ## The response coordinates -/

variable {S SStar K r B : Mat d}

/-- The symmetric response coordinate `r = ½(K + Kᵗ)` is symmetric. -/
theorem conjTranspose_response_sym (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) : rᴴ = r := by
  rw [hr, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]
  simp

/-- The doubled skew coordinate against `S_*⁻¹` is four times the response one:
`𝐊ᵗS_*⁻¹𝐊 = 4 rᵗS_*⁻¹r`. -/
theorem doubled_eq_four_smul (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) :
    (K + Kᴴ)ᴴ * SStar⁻¹ * (K + Kᴴ) = (4 : ℝ) • (rᴴ * SStar⁻¹ * r) := by
  have hK : K + Kᴴ = (2 : ℝ) • r := by
    rw [hr, smul_smul]
    norm_num
  rw [hK]
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  norm_num

/-- The response block `B = S + rᵗS_*⁻¹r` is positive semidefinite. -/
theorem posSemidef_responseBlock (hS : S.PosDef) (hStar : SStar.PosDef)
    (hB : B = S + rᴴ * SStar⁻¹ * r) : B.PosSemidef := by
  rw [hB]
  exact hS.posSemidef.add (hStar.inv.posSemidef.conjTranspose_mul_mul_same r)

/-- `S_* ≤ B`: the response block dominates the Schur block it corrects. -/
theorem schurStar_le_responseBlock (hS : S.PosDef) (hStar : SStar.PosDef)
    (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hsharp : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K) :
    SStar ≤ B := by
  have hstep : S ≤ B := by
    rw [hB]
    have := (hStar.inv.posSemidef.conjTranspose_mul_mul_same r)
    have h0 : (0 : Mat d) ≤ rᴴ * SStar⁻¹ * r := Matrix.le_iff.mpr (by simpa using this)
    simpa using add_le_add_left h0 S
  exact (schurStar_le_schur hS hStar hsharp).trans hstep

/-! ## The response ratio is at least one -/

/-- **`1 ≤ θ`** in the response-load calibration: the printed step
`B ≥ S ≥ S_*`. -/
theorem one_le_response_ratio [NeZero d] (hS : S.PosDef) (hStar : SStar.PosDef)
    (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hsharp : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K) :
    1 ≤ relSize B SStar := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have h := relSize_mono_left hStar.posSemidef
    (posSemidef_responseBlock hS hStar hB) hStar
    (schurStar_le_responseBlock hS hStar hB hsharp)
  rwa [relSize_self_eq_one hStar] at h

/-! ## The response ratio against the imbalance -/

/-- **`B ≤ c S_*` from `E_t ≤ c E_t^♯`.**  The fourfold Schur bound with three
of its four parts discarded. -/
theorem responseBlock_le_smul (hS : S.PosDef) (hStar : SStar.PosDef)
    (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) (hB : B = S + rᴴ * SStar⁻¹ * r) {c : ℝ}
    (h : schurBlock S SStar K ≤ c • fullBlockSharp (schurBlock S SStar K)) :
    B ≤ c • SStar := by
  have h4 := schur_doubled_bound hS hStar h
  rw [doubled_eq_four_smul hr] at h4
  have hpsd : (rᴴ * SStar⁻¹ * r).PosSemidef :=
    hStar.inv.posSemidef.conjTranspose_mul_mul_same r
  have hgap : rᴴ * SStar⁻¹ * r ≤ (4 : ℝ) • (rᴴ * SStar⁻¹ * r) := by
    refine Matrix.le_iff.mpr ?_
    have hrw : (4 : ℝ) • (rᴴ * SStar⁻¹ * r) - rᴴ * SStar⁻¹ * r =
        (3 : ℝ) • (rᴴ * SStar⁻¹ * r) := by
      rw [show (4 : ℝ) = 3 + 1 by norm_num, add_smul, one_smul]
      abel
    rw [hrw]
    exact hpsd.smul (by norm_num)
  rw [hB]
  exact (add_le_add (le_refl S) hgap).trans h4

/-- **`θ ≤ κ_t`** — the strengthened form of the printed
`θ ≤ (3κ_t - 1)/2`. -/
theorem response_ratio_le_canonImbalance (hS : S.PosDef) (hStar : SStar.PosDef)
    (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) (hB : B = S + rᴴ * SStar⁻¹ * r) :
    relSize B SStar ≤ canonImbalance (schurBlock S SStar K) := by
  have hEt : (schurBlock S SStar K).PosDef := posDef_schurBlock hS hStar
  have hsharpPd : (fullBlockSharp (schurBlock S SStar K)).PosDef := posDef_fullBlockSharp hEt
  have hle : schurBlock S SStar K ≤
      canonImbalance (schurBlock S SStar K) • fullBlockSharp (schurBlock S SStar K) := by
    rw [canonImbalance_eq hEt]
    exact le_relSize_smul hEt.posSemidef hsharpPd
  exact (relSize_le_iff (posSemidef_responseBlock hS hStar hB) hStar
    (canonImbalance_nonneg _)).mpr (responseBlock_le_smul hS hStar hr hB hle)

/-- **The printed upper bound** `θ ≤ (3κ_t - 1)/2` of the response-load
calibration, from `θ ≤ κ_t` and `1 ≤ κ_t`. -/
theorem response_ratio_le_printed [NeZero d] (hS : S.PosDef) (hStar : SStar.PosDef)
    (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ)) (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hsharp : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K) :
    relSize B SStar ≤ (3 * canonImbalance (schurBlock S SStar K) - 1) / 2 := by
  have hθκ := response_ratio_le_canonImbalance hS hStar hr hB
  have hone := one_le_response_ratio hS hStar hB hsharp
  linarith only [hθκ, hone]

/-! ## The imbalance against the response ratio -/

/-- **`κ_t ≤ 1 + 6(θ - 1)`**, through the repaired reference
intermediate at the skew `h = ½(K - Kᵗ)`. -/
theorem canonImbalance_le_one_add_six_mul_sub_one [NeZero d] (hS : S.PosDef)
    (hStar : SStar.PosDef) (hr : r = (2 : ℝ)⁻¹ • (K + Kᴴ))
    (hB : B = S + rᴴ * SStar⁻¹ * r)
    (hsharp : fullBlockSharp (schurBlock S SStar K) ≤ schurBlock S SStar K) :
    canonImbalance (schurBlock S SStar K) ≤ 1 + 6 * (relSize B SStar - 1) := by
  set Et : FullBlockMat d := schurBlock S SStar K with hEtdef
  have hEt : Et.PosDef := posDef_schurBlock hS hStar
  have hsharpPd : (fullBlockSharp Et).PosDef := posDef_fullBlockSharp hEt
  set E : BlockMat d := ofFullBlockMat Et with hEdef
  have hEfull : toFullBlockMat E = Et := toFullBlockMat_ofFullBlockMat Et
  have hsymm : IsSymmetricBlockMat E :=
    isSymmetricBlockMat_of_isSymm (isSymm_of_isHermitian hEt.isHermitian)
  have hEpd : (toFullBlockMat E).PosDef := by rw [hEfull]; exact hEt
  have hpos : Book.Ch02.BlockPosDef E := (blockPosDef_iff_posDef hsymm).mpr hEpd
  -- the sharp ordering in the structural dialect
  have hsharpFull : toFullBlockMat (blockSharp E) = fullBlockSharp Et := by
    rw [toFullBlockMat_blockSharp, hEfull]
  have hsharpSymm : IsSymmetricBlockMat (blockSharp E) := by
    refine isSymmetricBlockMat_of_posSemidef ?_
    rw [hsharpFull]
    exact hsharpPd.posSemidef
  have hsharpBlock : BlockMatLoewnerLE (blockSharp E) E := by
    refine blockMatLoewnerLE_of_le ?_
    rw [hsharpFull, hEfull]
    exact hsharp
  -- the Schur data of the structural block
  have hlowerRight : E.lowerRight = SStar⁻¹ := by
    have : E.lowerRight = Et.toBlocks₂₂ := rfl
    rw [this, hEtdef, toBlocks₂₂_schurBlock]
  have hstar : schurSigmaStar E = SStar := by
    rw [schurSigmaStar, hlowerRight,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStar)]
  have hskew : schurSkew E = K := by
    have hlowerLeft : E.lowerLeft = -(SStar⁻¹ * K) := by
      have : E.lowerLeft = Et.toBlocks₂₁ := rfl
      rw [this, hEtdef, toBlocks₂₁_schurBlock]
    rw [schurSkew, hlowerRight, hlowerLeft]
    rw [show SStar⁻¹⁻¹ = SStar from
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_posDef hStar)]
    rw [Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hStar), Matrix.one_mul, neg_neg]
  have hsigma : schurSigma E = S := by
    have hupperLeft : E.upperLeft = S + Kᴴ * SStar⁻¹ * K := by
      have : E.upperLeft = Et.toBlocks₁₁ := rfl
      rw [this, hEtdef, toBlocks₁₁_schurBlock]
    rw [schurSigma, hupperLeft, hlowerRight, hskew, ← conjTranspose_eq_matTranspose]
    abel
  -- the skew parameter and the corrected form
  have hskewMat : IsSkewMat ((2 : ℝ)⁻¹ • (K - Kᴴ)) := by
    rw [IsSkewMat, ← conjTranspose_eq_matTranspose, Matrix.conjTranspose_smul,
      star_trivial, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show Kᴴ - K = -(K - Kᴴ) by abel, smul_neg]
  have hcorr : skewCorrectedForm E ((2 : ℝ)⁻¹ • (K - Kᴴ)) = B := by
    have hdiff : schurSkew E - (2 : ℝ)⁻¹ • (K - Kᴴ) = r := by
      rw [hskew, hr]
      module
    rw [skewCorrectedForm, hdiff, hsigma, hlowerRight, hB,
      ← conjTranspose_eq_matTranspose]
  have hchain : MatLoewnerLE (skewCorrectedForm E ((2 : ℝ)⁻¹ • (K - Kᴴ)))
      (relSize B SStar • schurSigmaStar E) := by
    rw [hcorr, hstar]
    exact Initialization.matLoewnerLE_of_le
      (le_relSize_smul (posSemidef_responseBlock hS hStar hB) hStar)
  have hkappa := Initialization.kappaRef_le_of_matLoewnerLE_skewCorrectedForm hsymm hpos hsharpBlock
    hskewMat hchain
  rwa [kappaRef, blockSize_eq_relSize hsymm hsharpSymm
    ((blockPosDef_iff_posDef hsharpSymm).mpr (by rw [hsharpFull]; exact hsharpPd)) hEpd.posSemidef,
    hsharpFull, hEfull, ← canonImbalance_eq hEt] at hkappa

end

end Response
end HighContrast
end HCPolySupport
