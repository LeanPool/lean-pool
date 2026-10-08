/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.LoadCalibrationTheta
public import LeanPool.HighContrastHomogenization.Provider.Persistence.AdaptedPersistence
public import LeanPool.HighContrastHomogenization.Annealed.Contrast
public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange

/-!
# High-contrast homogenization: Provider.Entry.ContrastBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The entry contrast against the Euclidean imbalance

The last display of the proof of `t.polynomial.entry` converts
the imbalance of the Euclidean annealed block at the entry generation into the
annealed contrast there,

`Θ_m - 1 ≤ 3(𝔡(F_m) - 1)`,

with `Θ_m` the intrinsic annealed contrast of `e.Theta.m` and
`𝔡` the canonical imbalance of `e.scale.selection.canonical.metric`, both read
on `F_m = 𝐀_bar(□_m)`.

Two things are proved.

*Definedness.*  The printed argument obtains the finiteness and positive
definiteness of `F_m` from the Euclidean mean comparison
`e.initial.source.bounds`, which is available at generations at or
above the source burn.  Both are in fact consequences of
`e.coarse.ellipticity` alone, at every generation: the coarse response of a
centered cube is integrable and its expectation is positive definite, and
the annealed primal-adjoint order then puts the block above its own sharp.  The
generation hypothesis is carried below for the shape of the entry argument and
is not needed.

*The comparison.*  The bridge itself is `Θ ≤ 𝔡` on any symmetric positive
doubled block — one factor of three stronger than the printed display, which is
recovered from it because `𝔡 ≥ 1`.

The printed route to the display passes through the *uncorrected* Schur ratio
`Θ_tilde = |σ_*^{-1/2} σ σ_*^{-1/2}|`, in two steps: a factor-three comparison
`Θ - 1 ≤ 3(Θ_tilde - 1)`, and then `Θ_tilde - 1 ≤ 𝔡 - 1` read off the sharp ordering.  The
second step's source, the lower block inequality of [Armstrong–Kuusi, Lemma 2.6, (2.82)], is false
as printed: at Schur data `σ_* = 1, σ = 9, k = 4` in
one dimension the printed bounds are exceeded, both being linear in `Θ_tilde - 1`
where the extremal configurations grow quadratically.  Neither step is used
here.

The route taken instead is the intrinsic minimum itself.  `Θ` minimizes the
normalized skew-corrected Schur form over the skew matrices, so *any* skew
matrix bounds it; the choice `h = ½(k - kᵗ)` leaves the symmetric coordinate
`r = ½(k + kᵗ)` and the corrected form `B = σ + rᵗσ_*⁻¹r`, and the fourfold
Schur bound of `e.response.canonical.imbalance` — the imbalance ordering
`F ≤ 𝔡 F^♯` read at the vector whose second Schur coordinate vanishes — gives
`σ + 4rᵗσ_*⁻¹r ≤ 𝔡 σ_*`, hence `B ≤ 𝔡 σ_*`.  So `𝔡` is admissible for the
infimum defining `Θ`, which is exactly `Θ ≤ 𝔡`.  The uncorrected ratio never
appears.

There are no definitions in this file.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The bridge -/

/-- **The intrinsic contrast is below the canonical imbalance**, `Θ ≤ 𝔡`, on
every symmetric positive definite doubled block.

The skew matrix `h = ½(k - kᵗ)` corrects the Schur skew coordinate to its
symmetric part `r = ½(k + kᵗ)`, and the imbalance ordering `F ≤ 𝔡 F^♯` of
`e.scale.selection.canonical.metric`, read on the doubled coordinate whose second
Schur component vanishes, bounds `σ + rᵗσ_*⁻¹r` by `𝔡 σ_*`.  That is an
admissible Loewner scaling for the infimum defining the intrinsic contrast, so
the infimum is at most `𝔡`. -/
theorem blockContrast_le_blockImbalance {F : BlockMat d}
    (hsymm : IsSymmetricBlockMat F) (hpos : Book.Ch02.BlockPosDef F) :
    blockContrast F ≤ blockImbalance F := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hsymm hpos
  have hdet : IsUnit F.lowerRight.det := isUnit_det_lowerRight hpos
  have hTpd : (F.lowerRight).PosDef :=
    posDef_of_posSemidef_of_isUnit (posSemidef_lowerRight hsymm hpos)
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  have hstarPd : (schurSigmaStar F).PosDef := hTpd.inv
  have hstarInv : (schurSigmaStar F)⁻¹ = F.lowerRight := schurSigmaStar_inv F hdet
  have hform : toFullBlockMat F =
      schurBlock (schurSigma F) (schurSigmaStar F) (schurSkew F) :=
    Initialization.toFullBlockMat_eq_schurBlock hsymm hpos
  have hFschur :
      (schurBlock (schurSigma F) (schurSigmaStar F) (schurSkew F)).PosDef := by
    rw [← hform]; exact hFfull
  have hsPd : (schurSigma F).PosDef := posDef_of_posDef_schurBlock hstarPd hFschur
  -- the imbalance is an admissible Loewner scaling against the sharp
  have himb : toFullBlockMat F ≤
      blockImbalance F • fullBlockSharp (toFullBlockMat F) := by
    have hrw : blockImbalance F = canonImbalance (toFullBlockMat F) := rfl
    rw [hrw, canonImbalance_eq hFfull]
    exact le_relSize_smul hFfull.posSemidef (posDef_fullBlockSharp hFfull)
  rw [hform] at himb
  -- the fourfold Schur bound, with three of its four parts discarded
  have hB := Response.responseBlock_le_smul (K := schurSkew F) hsPd hstarPd rfl rfl himb
  refine blockContrast_le (canonImbalance_nonneg _)
    (h := (2 : ℝ)⁻¹ • (schurSkew F - (schurSkew F)ᴴ)) ?_ ?_
  · rw [IsSkewMat, ← Response.conjTranspose_eq_matTranspose, Matrix.conjTranspose_smul,
      star_trivial, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show (schurSkew F)ᴴ - schurSkew F = -(schurSkew F - (schurSkew F)ᴴ) by abel,
      smul_neg]
  · have hdiff : schurSkew F - (2 : ℝ)⁻¹ • (schurSkew F - (schurSkew F)ᴴ) =
        (2 : ℝ)⁻¹ • (schurSkew F + (schurSkew F)ᴴ) := by module
    rw [hdiff, ← Response.conjTranspose_eq_matTranspose, ← hstarInv]
    exact Initialization.matLoewnerLE_of_le hB

/-! ## The Euclidean block at a generation of the entry argument -/

/-- **The Euclidean annealed block dominates its own sharp** under
`e.coarse.ellipticity`.  Integrability of the coarse response of a centered
cube and positivity of its expectation are consequences of the assumption at
every generation, and the annealed primal-adjoint order applies on the cube. -/
theorem blockSharp_annealedBlock_centeredCube_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    BlockMatLoewnerLE (blockSharp (annealedBlock P (centeredCube d m)))
      (annealedBlock P (centeredCube d m)) :=
  Sharp.blockSharp_annealedBlock_le_centeredCube m
    (hasIntegrableCoarseBlock_of_coarseEllipticityDagger hdag m)

/-- **The Euclidean imbalance is at least one** under
`e.coarse.ellipticity`: the determinant clause for the canonical metric on a
block above its own sharp. -/
theorem one_le_blockImbalance_annealedBlock_centeredCube [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    1 ≤ blockImbalance (annealedBlock P (centeredCube d m)) := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hsymm : IsSymmetricBlockMat (annealedBlock P (centeredCube d m)) :=
    isSymmetricBlockMat_annealedBlock P _
  have hpos : Book.Ch02.BlockPosDef (annealedBlock P (centeredCube d m)) :=
    blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m
  exact Persistence.one_le_canonImbalance (posDef_toFullBlockMat hsymm hpos)
    (fullBlockSharp_le_of_blockMatLoewnerLE hsymm hpos
      (blockSharp_annealedBlock_centeredCube_le hdag m))

/-! ## The entry conversion -/

/-- **The entry contrast conversion** of `t.polynomial.entry`:
at every generation the annealed contrast of the centered cube is converted into
the imbalance of the Euclidean annealed block there,

`Θ_m - 1 ≤ 3(𝔡(F_m) - 1)`.

The comparison `Θ_m ≤ 𝔡(F_m)` is one factor of three stronger; the printed
display follows because the imbalance is at least one.  The source-burn
hypothesis, which the printed definedness step consumes, is not needed: the
definedness of `F_m` is available from `e.coarse.ellipticity` at every
generation. -/
theorem entry_contrast (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (_hg : g ∈ Set.Ico (0 : ℝ) 1) (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (_hstat : HCPoly.Frozen.IsStationaryLaw P)
    (_hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (m : ℤ) (_hm : sourceBurn d (initExpQ d g : ℝ) K ≤ m) :
    annealedContrast P m - 1 ≤
      3 * (blockImbalance (annealedBlock P (centeredCube d m)) - 1) := by
  have : NeZero d := ⟨by omega⟩
  have hone : 1 ≤ blockImbalance (annealedBlock P (centeredCube d m)) :=
    one_le_blockImbalance_annealedBlock_centeredCube hdag m
  have hbridge :
      annealedContrast P m ≤ blockImbalance (annealedBlock P (centeredCube d m)) :=
    blockContrast_le_blockImbalance (isSymmetricBlockMat_annealedBlock P _)
      (blockPosDef_annealedBlock_of_coarseEllipticityDagger hdag m)
  linarith only [hone, hbridge]

end

end Entry
end HighContrast
end HCPolySupport
