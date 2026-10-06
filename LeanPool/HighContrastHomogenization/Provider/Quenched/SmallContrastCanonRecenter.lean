/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewNormalization
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Setup.TransportObjects

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCanonRecenter

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The one-time recentering of the reference: canonical data under a shear

Section 2.5 of HC records that
subtracting a constant skew matrix `h` from the coefficient field leaves the
solution space unchanged and conjugates every coarse block by the shear
`G_h`, leaving the two diagonal Schur coordinates untouched and subtracting
`h` from the Schur skew coordinate (HC (2.65)).  The paper uses this
to assume, without loss of generality, that the relevant homogenized skew
vanishes.

This file records what the same recentering does to the *canonical* data of
the reference block: the canonical metric `m(E)` is invariant and the
canonical shear `g(E)` drops by the recentering skew,

  `m(G_h^t E G_h) = m(E)`,   `g(G_h^t E G_h) = g(E) - h`.

Consequently the one-time recentering by `h := g(E)` produces a reference
whose canonical shear vanishes, which is the normalization under which the
weak-norm metric factor of the small-contrast estimate is controlled by the
reference's imbalance alone.

The proof is the congruence equivariance of the geometric mean together with
the shear covariance of the sharp involution (`fullBlockSharp_shear_conj`),
which is available exactly because the recentering matrix is skew.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The canonical metric block under a skew shear congruence -/

/-- **The canonical metric block is shear-covariant.**  For a skew `h`,
`M(G_h^t E G_h) = G_h^t M(E) G_h`.  This is `matGeomMean_conj` composed with
the recentering identity `fullBlockSharp_shear_conj`, the covariance of the
primal-adjoint involution under a constant skew shear. -/
theorem canonBlock_shear_conj {E : FullBlockMat d} (hE : E.PosDef)
    {h : Mat d} (hskew : hᴴ = -h) :
    canonBlock ((fullBlockShear h)ᴴ * E * fullBlockShear h) =
      (fullBlockShear h)ᴴ * canonBlock E * fullBlockShear h := by
  have hS : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  rw [canonBlock, fullBlockSharp_shear_conj hE hskew, canonBlock]
  exact matGeomMean_conj hE hS (isUnit_fullBlockShear h)

/-- The shear congruence of a Schur form re-brackets to a Schur form whose
skew coordinate has dropped by the shear. -/
private theorem shear_conj_schurBlock (s sStar k h : Mat d) :
    (fullBlockShear h)ᴴ * schurBlock s sStar k * fullBlockShear h =
      schurBlock s sStar (k - h) := by
  rw [schurBlock, schurBlock]
  have hcompose :
      fullBlockShear (-k) * fullBlockShear h = fullBlockShear (-(k - h)) := by
    rw [fullBlockShear_mul]
    congr 1
    abel
  calc
    (fullBlockShear h)ᴴ *
        ((fullBlockShear (-k))ᴴ * Matrix.fromBlocks s 0 0 sStar⁻¹ *
          fullBlockShear (-k)) * fullBlockShear h =
        (fullBlockShear (-k) * fullBlockShear h)ᴴ *
          Matrix.fromBlocks s 0 0 sStar⁻¹ *
            (fullBlockShear (-k) * fullBlockShear h) := by
      rw [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = (fullBlockShear (-(k - h)))ᴴ * Matrix.fromBlocks s 0 0 sStar⁻¹ *
          fullBlockShear (-(k - h)) := by rw [hcompose]

/-- **The canonical pair under a skew shear congruence**: the canonical metric
is unchanged and the canonical shear drops by the recentering skew. -/
theorem canonFactor_shear_conj {E : FullBlockMat d} (hE : E.PosDef)
    {h : Mat d} (hskew : hᴴ = -h) :
    canonMetric ((fullBlockShear h)ᴴ * E * fullBlockShear h) = canonMetric E ∧
      canonShear ((fullBlockShear h)ᴴ * E * fullBlockShear h) =
        canonShear E - h := by
  obtain ⟨hm, hg, hfac⟩ := canonFactor_spec hE
  have hEc : ((fullBlockShear h)ᴴ * E * fullBlockShear h).PosDef :=
    hE.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit (isUnit_fullBlockShear h))
  have hgh : (canonShear E - h)ᴴ = -(canonShear E - h) := by
    rw [Matrix.conjTranspose_sub, hg, hskew]
    abel
  have hfac' : canonBlock ((fullBlockShear h)ᴴ * E * fullBlockShear h) =
      schurBlock (canonMetric E) (canonMetric E) (canonShear E - h) := by
    rw [canonBlock_shear_conj hE hskew, hfac, shear_conj_schurBlock]
  obtain ⟨h1, h2⟩ := canonFactor_eq hEc hm hgh hfac'
  exact ⟨h1.symm, h2.symm⟩

/-! ## The block-level statements -/

/-- The flattened skew congruence is the shear congruence of the flattening. -/
private theorem toFullBlockMat_skewBlockCongr' (h : Mat d) (A : BlockMat d) :
    toFullBlockMat (Response.skewBlockCongr h A) =
      (fullBlockShear h)ᴴ * toFullBlockMat A * fullBlockShear h :=
  Response.toFullBlockMat_skewBlockCongr h A

/-- **The canonical metric of the recentered reference** is the canonical
metric of the reference. -/
theorem canonicalMetric_skewBlockCongr {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {h : Mat d} (hskew : IsSkewMat h) :
    canonicalMetric (Response.skewBlockCongr h E) = canonicalMetric E := by
  have hskew' : hᴴ = -h := by
    rw [conjTranspose_eq_transpose']
    exact hskew
  rw [canonicalMetric, canonicalMetric, toFullBlockMat_skewBlockCongr']
  exact (canonFactor_shear_conj hE hskew').1

/-- **The canonical shear of the recentered reference** drops by the
recentering skew — the canonical-data form of HC (2.65). -/
theorem canonicalShear_skewBlockCongr {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) {h : Mat d} (hskew : IsSkewMat h) :
    canonicalShear (Response.skewBlockCongr h E) = canonicalShear E - h := by
  have hskew' : hᴴ = -h := by
    rw [conjTranspose_eq_transpose']
    exact hskew
  rw [canonicalShear, canonicalShear, toFullBlockMat_skewBlockCongr']
  exact (canonFactor_shear_conj hE hskew').2

/-- The canonical shear of a positive block is skew. -/
theorem isSkewMat_canonicalShear {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) : IsSkewMat (canonicalShear E) := by
  have h := (canonFactor_spec hE).2.1
  rw [IsSkewMat, matTranspose, ← conjTranspose_eq_transpose']
  exact h

/-- **The one-time global recentering.**  Recentering the reference by its own
canonical shear produces a reference whose canonical shear vanishes, while its
canonical metric — the matrix defining the adapted cubes — is unchanged.  This
is the normalization the printed proof installs once and for all. -/
theorem canonicalShear_recentered_eq_zero {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) :
    canonicalShear (Response.skewBlockCongr (canonicalShear E) E) = 0 ∧
      canonicalMetric (Response.skewBlockCongr (canonicalShear E) E) =
        canonicalMetric E := by
  refine ⟨?_, canonicalMetric_skewBlockCongr hE (isSkewMat_canonicalShear hE)⟩
  rw [canonicalShear_skewBlockCongr hE (isSkewMat_canonicalShear hE), sub_self]

/-! ## The canonical block as a sheared diagonal -/

/-- **The canonical metric block is the shear congruence of the split metric**
`diag(m(E), m(E)^{-1})` by the canonical shear.  This is the factorization
`e.scale.selection.canonical.metric` written structurally. -/
theorem canonicalBlock_eq_skewBlockCongr {E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) :
    canonicalBlock E =
      Response.skewBlockCongr (-canonicalShear E)
        (blockDiag (canonicalMetric E) (canonicalMetric E)⁻¹) := by
  apply toFullBlockMat_injective
  rw [canonicalBlock, toFullBlockMat_ofFullBlockMat,
    toFullBlockMat_skewBlockCongr', toFullBlockMat_blockDiag]
  have hfac := (canonFactor_spec hE).2.2
  rw [hfac, schurBlock]
  rfl

end

end HCPolySupport.HighContrast.Quenched
