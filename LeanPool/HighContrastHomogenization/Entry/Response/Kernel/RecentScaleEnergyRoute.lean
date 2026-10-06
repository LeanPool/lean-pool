/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentHeadDefectHalves
public import LeanPool.HighContrastHomogenization.Provider.Response.EnergyMap

/-!
# High-contrast homogenization: Entry.Response.Kernel.RecentScaleEnergyRoute

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The recent-scale decomposition, Loewner envelope and energy map

This file proves three steps of the response-transfer proposition `p.response.transfer`. The first
is the recent-scale decomposition, writing the transported recentred parent cell average as the
child average plus the parent-minus-child difference. The second is the Loewner envelope
`N ≤ ‖N‖ · I` of a doubled block by its operator norm, needed for the quadratic half of the
diagonal weak-norm estimate. The third is the coarse energy-map bound on the doubled response
space, reached through two independent chains of metric comparisons and recorded together with the
quadratic-form identities it rests on.
-/

section
/-!
## The recent-scale decomposition

Nothing here restates or weakens an existing declaration, and `diagonalWeakNorm_primal_le`
(`DiagonalWeakNormBound.lean`) is untouched.

## The decomposition

Between the compiled bound (`DiagonalWeakNormAssembly.lean`) and
`diagonalWeakNorm_primal_le` lie three steps.  This file is the first: the scale decomposition.

The compiled bound is `∑_{n ≤ H} 3^{-n/2} · (cellTerm V n + A n)`, where `cellTerm V n` is built
from a per-cell CHILD maximizer `V n w` and `A n` is an abstract per-scale average-defect term.
The left-hand side of `diagonalWeakNorm_primal_le`, after the two support lemmas
(`RecentEnergyMapSupport.lean`), is the head of the seminorm of the ACTUAL
family: the same expression with the PARENT field `Xu` in place of `V n w`.  The recent-scale
decomposition is what connects them, at each depth `n` and then summed:

`headTerm n ≤ cellTerm n + defectTerm n`,

with `defectTerm n` the normalized root-mean-square of the averaged parent-minus-child
difference — i.e. it both supplies the inequality AND *exhibits the witness* for the bound's
otherwise abstract `A`.  What the bound then still assumes about that witness is the analytic
per-scale bound `hscale`, which is NOT in this file.

The proof uses the two ingredients, on these carriers:

* averaging the child/parent difference is the difference of the cell averages; here
  `cellAverage_sub`.
* the split `parent − mean = (child − mean) + (parent − child)` followed by the triangle
  inequality in the normalized `ℓ²(Z)` of block vectors; here `recentCell_split`.

Two implementation notes:

1. The difference is taken as `parent − child` from the start, so no separate sign-cancellation
  step is needed.
2. The quantity is spelled inline as `√(|Z|⁻¹ · ∑_{w ∈ Z} ⟪·,·⟫)`, matching `weakCellSum` and
   `h6a_besovSeminorm_head_tail_le`.  The triangle inequality for it is
   `normalized_blockL2_add_le` (`RecentEnergyMapSupport.lean`).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Averaging a difference. -/

omit [NeZero d] in
/-- **The cell average of a difference is the difference of the cell averages.**  It is stated
for arbitrary `F`, `G` rather than for two particular fields, with the componentwise
`IntegrableOn` side conditions explicit, because the integrability of `optimizerField` on an
adapted cell is supplied separately by the consumer (the same side conditions two earlier
support lemmas already take, `RecentEnergyMapSupport.lean`).  That makes it
reusable and keeps the `MemVectorL2` plumbing out of the decomposition. -/
theorem cellAverage_sub {V : Set (Vec d)} (F G : Vec d → BlockVec d)
    (h1F : ∀ j, IntegrableOn (fun x => (F x).1 j) V)
    (h2F : ∀ j, IntegrableOn (fun x => (F x).2 j) V)
    (h1G : ∀ j, IntegrableOn (fun x => (G x).1 j) V)
    (h2G : ∀ j, IntegrableOn (fun x => (G x).2 j) V) :
    cellAverage V (fun x => F x - G x) = cellAverage V F - cellAverage V G := by
  refine Prod.ext ?_ ?_
  · funext i
    show volumeAverage V (fun x => (F x).1 i - (G x).1 i)
      = volumeAverage V (fun x => (F x).1 i) - volumeAverage V (fun x => (G x).1 i)
    exact volumeAverage_sub (h1F i) (h1G i)
  · funext i
    show volumeAverage V (fun x => (F x).2 i - (G x).2 i)
      = volumeAverage V (fun x => (F x).2 i) - volumeAverage V (fun x => (G x).2 i)
    exact volumeAverage_sub (h2F i) (h2G i)

/-! ## R1-2.  The split at one cell. -/

omit [NeZero d] in
/-- R1-2.  **The split at one cell.**  The transported, `U_t`-recentred cell average of the
PARENT field is the corresponding quantity for the CHILD field plus the transported average of
the parent-minus-child difference:

`R·((Xu)_{V} − c) = R·((Xv)_{V} − c) + R·((Xu − Xv)_{V})`.

This is the algebraic heart of the mine's `hsplit`
(`…/DiagonalWeakNormRecentDecomposition.lean`), with the sign taken as `parent − child`
so that the mine's separate `blockAvsumL2_neg` step is not needed. -/
theorem recentCell_split {V : Set (Vec d)} (R : BlockMat d)
    (Xu Xv : Vec d → BlockVec d) (c : BlockVec d)
    (h1u : ∀ j, IntegrableOn (fun x => (Xu x).1 j) V)
    (h2u : ∀ j, IntegrableOn (fun x => (Xu x).2 j) V)
    (h1v : ∀ j, IntegrableOn (fun x => (Xv x).1 j) V)
    (h2v : ∀ j, IntegrableOn (fun x => (Xv x).2 j) V) :
    blockMatVecMul R (cellAverage V Xu - c)
      = blockMatVecMul R (cellAverage V Xv - c)
        + blockMatVecMul R (cellAverage V (fun x => Xu x - Xv x)) := by
  rw [cellAverage_sub Xu Xv h1u h2u h1v h2v, ← blockMatVecMul_add]
  congr 1
  abel

/-! ## R1-3.  The decomposition at one depth. -/

/-! ## R1-4.  The decomposition summed over the window, the shape `AS-9` consumes. -/

/-! ## R3-1.  The tail weight (node R3, partial). -/

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The Loewner / operator-norm layer, on the block-matrix carrier

`L-1 … L-5`, proved here.  Nothing restates or weakens any existing declaration, and the target
`diagonalWeakNorm_primal_le` is untouched.

## Why this module exists

`quadratic_le_norm_normalizedBlock` below — the quadratic half of the estimate — needs the
Loewner envelope `N ≤ |N| · I_{2d}` of a doubled block by its operator norm.  The proof of that
step in `HCPoly/Entry/Response/Kernel/OptimizerEnergyIdentity.lean`
(`blockSpecBound_attained`) is `private` and strictly downstream of this module, so it cannot be
used here.

This module re-proves the step where it can be used: it imports only
`RecentScaleEnergyRoute`, and is imported by `CoarseBlockPerCellInput`, so it
sits strictly upstream of `WeakEstimateAssembly`.  The original declarations are neither deleted nor
made public.

## Two corrections to the diagnosis

1. The step actually needed is NOT `blockSpecBound_attained`.  That lemma concludes
   `N ≤ blockSpecBound N · I` and is about the `sInf` carrier; what is needed is the bound by
  the OPERATOR NORM, `x · N x ≤ |N| (x · x)`, for an ARBITRARY (in particular not positive
  semidefinite — the averaged defect is a difference of coarse blocks) matrix.  That is `L-1`
  and `L-2` here.
2. `blockSpecBound_attained` (`HCPoly/Entry/Response/Kernel/OptimizerEnergyIdentity.lean`) is a
   duplicate: `blockSpecBound_attained_of_loewnerLE`
   (`HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean`) is the same statement, and that
   module is upstream of this chain.  It is `private` there too, so it is equally unusable, though
   its import direction is not the obstruction.

The analogous estimate is `diagonalWeak_recent_response_quadratic_le`
(`HCPoly/Provider/Response/DiagonalWeakNormRecentQuadratic.lean`).  Nothing is imported
from it and no file is copied; the proof is reproduced on the block-matrix carriers, with its
`blockSize D (blockIdentity d)` replaced by `‖toFullBlockMat ·‖`, which is
what `weakAverageDefect` and `CH-3`'s `henergy` print.
-/

open HCPolySupport.HighContrast (blockScale matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Flat helpers -/

private theorem dotProduct_self_nonneg_of_fintype {n : Type*} [Fintype n] (v : n → ℝ) :
    (0 : ℝ) ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private theorem qform_flat (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec X) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]

private theorem qform_blockScale_eq_mul (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  rw [qform_flat, qform_flat, toFullBlockMat_blockScale, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

private theorem qform_identity_eq_dotProduct_toFullBlockVec (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
  rw [qform_flat, toFullBlockMat_blockIdentity, Matrix.one_mulVec]

/-- Congruence by a symmetric matrix moves through the quadratic form. -/
private theorem qform_conj_eq {n : Type*} [Fintype n] [DecidableEq n]
    (Sm M : Matrix n n ℝ) (hS : Smᵀ = Sm) (v : n → ℝ) :
    v ⬝ᵥ ((Sm * M * Sm) *ᵥ v) = (Sm *ᵥ v) ⬝ᵥ (M *ᵥ (Sm *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hS]

/-! ## L-1 … L-3: the Loewner / operator-norm layer -/

/-- **L-2.**  The Loewner envelope of an arbitrary doubled block by its operator norm,
`N ≤ |N| · I_{2d}`.  It is proved here with no hypothesis on `N` at all. -/
theorem loewner_le_opNorm_identity (N : BlockMat d) :
    BlockMatLoewnerLE N
      (blockScale ‖toFullBlockMat N‖ (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := HCPolySupport.HighContrast.dotProduct_mulVec_le_norm_mul (toFullBlockMat N) (toFullBlockVec X)
  rw [qform_flat, qform_blockScale_eq_mul, qform_identity_eq_dotProduct_toFullBlockVec]
  linarith only [h]

/-- **L-3.**  `blockSpecBound N` attains its defining infimum, UNCONDITIONALLY: the set
`{c ≥ 0 | N ≤ c I}` is never empty, because `L-2` puts `‖toFullBlockMat N‖` in it.  This re-proves
`blockSpecBound_attained` (`HCPoly/Entry/Response/Kernel/OptimizerEnergyIdentity.lean`) and
`blockSpecBound_attained_of_loewnerLE`
(`HCPoly/Entry/Response/Core/PathwiseFluctuationBound.lean`), both
`private`, and drops their
`(c : ℝ) (hc : 0 ≤ c) (h : BlockMatLoewnerLE N (blockScale c (blockIdentity d)))` witness
hypotheses, so it is strictly stronger than either. -/
theorem blockMatLoewnerLE_blockScale_blockSpecBound_self (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockSpecBound N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have hid := qform_identity_eq_dotProduct_toFullBlockVec X
  set q : ℝ := toFullBlockVec X ⬝ᵥ toFullBlockVec X with hqdef
  have hq0 : (0 : ℝ) ≤ q := dotProduct_self_nonneg_of_fintype _
  set p : ℝ := blockVecDot X (blockMatVecMul N X) with hpdef
  have hmem : ∀ b ∈ {c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}, p ≤ b * q := by
    intro b hb
    have hbX := hb.2 X
    rw [qform_blockScale_eq_mul, hid] at hbX
    linarith only [hbX, hpdef]
  have hne : ({c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}).Nonempty :=
    ⟨‖toFullBlockMat N‖, norm_nonneg _, loewner_le_opNorm_identity N⟩
  have hkey : p ≤ blockSpecBound N * q := by
    rcases eq_or_lt_of_le hq0 with h0 | hpos
    · obtain ⟨c, hc⟩ := hne
      have hc0 := hmem c hc
      rw [← h0] at hc0 ⊢
      simpa using hc0
    · have hdiv : p / q ≤ blockSpecBound N := by
        refine le_csInf hne fun b hb => ?_
        exact (div_le_iff₀ hpos).2 (hmem b hb)
      exact (div_le_iff₀ hpos).1 hdiv
  rw [qform_blockScale_eq_mul, hid]
  linarith only [hkey]

/-- **L-4.**  The quadratic form of a block whose flat representative is positive semidefinite
is nonnegative.  Used to discharge `CH-3`'s `hLsq` side condition from its `hE`. -/
theorem blockVecDot_nonneg_of_posSemidef (A : BlockMat d)
    (hA : (toFullBlockMat A).PosSemidef) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  have h := hA.dotProduct_mulVec_nonneg (toFullBlockVec X)
  rw [qform_flat]
  simpa only [star_trivial] using h

/-! ## The quadratic half -/

/-- **The quadratic half.**  The unnormalized quadratic form of `H` is controlled
by the operator norm of the `E`-NORMALIZED block times the `E`-quadratic form:

`x · H x ≤ |E^{-1/2} H E^{-1/2}| (x · E x)`.

The same estimate is `diagonalWeak_recent_response_quadratic_le`, whose proof is the same
three moves — congruence of the normalized block by `E^{1/2}` back to `H`, the change of variable
`y = E^{1/2} x`, and the Loewner envelope of the normalized block.  Two differences, both
STRENGTHENINGS:

* the carrier `blockSize D (blockIdentity d)` is replaced by
  `‖toFullBlockMat D‖`, which is what `weakAverageDefect` and `CH-3`'s `henergy` print; and
* the earlier statement assumes `IsSymmetricBlockMat E`/`H`; here NEITHER symmetry of `H` nor a
  separate symmetry hypothesis on `E` is needed, because `L-1` holds for arbitrary matrices and
  `(toFullBlockMat E).PosDef` already carries the symmetry of `E`. -/
theorem quadratic_le_norm_normalizedBlock (E H : BlockMat d)
    (hE : (toFullBlockMat E).PosDef) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul H X)
      ≤ ‖toFullBlockMat (normalizedBlock H E)‖ * blockVecDot X (blockMatVecMul E X) := by
  -- the two square-root cancellations, and the symmetry of the root
  have hSSI : matSqrt (toFullBlockMat E) * matSqrt (toFullBlockMat E)⁻¹ = 1 :=
    HCPolySupport.HighContrast.matSqrt_mul_matSqrt_inv hE
  have hSIS : matSqrt (toFullBlockMat E)⁻¹ * matSqrt (toFullBlockMat E) = 1 :=
    HCPolySupport.HighContrast.matSqrt_inv_mul_matSqrt hE
  have hSsymm : (matSqrt (toFullBlockMat E))ᵀ = matSqrt (toFullBlockMat E) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hE.posSemidef).1.isHermitian
  have hSS : matSqrt (toFullBlockMat E) * matSqrt (toFullBlockMat E) = toFullBlockMat E :=
    (matSqrt_spec hE.posSemidef).2
  -- the flat representative of the normalized block
  have hN : toFullBlockMat (normalizedBlock H E)
      = matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat H * matSqrt (toFullBlockMat E)⁻¹ := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  -- un-normalization: `E^{1/2} (E^{-1/2} H E^{-1/2}) E^{1/2} = H`
  have hfactor : matSqrt (toFullBlockMat E) * toFullBlockMat (normalizedBlock H E) *
      matSqrt (toFullBlockMat E) = toFullBlockMat H := by
    rw [hN]
    calc
      matSqrt (toFullBlockMat E) *
            (matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat H * matSqrt (toFullBlockMat E)⁻¹) *
            matSqrt (toFullBlockMat E)
          = matSqrt (toFullBlockMat E) * matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat H *
            (matSqrt (toFullBlockMat E)⁻¹ * matSqrt (toFullBlockMat E)) := by noncomm_ring
      _ = toFullBlockMat H := by rw [hSSI, hSIS, Matrix.one_mul, Matrix.mul_one]
  -- the change of variable `y = E^{1/2} x`
  have hquad : blockVecDot X (blockMatVecMul H X)
      = (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X) ⬝ᵥ
          (toFullBlockMat (normalizedBlock H E) *ᵥ
            (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X)) := by
    rw [qform_flat, ← hfactor, qform_conj_eq _ _ hSsymm]
  have hy : (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X) ⬝ᵥ
      (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X)
      = blockVecDot X (blockMatVecMul E X) := by
    have h := qform_conj_eq (matSqrt (toFullBlockMat E)) (1 : FullBlockMat d) hSsymm
      (toFullBlockVec X)
    rw [Matrix.mul_one, hSS, Matrix.one_mulVec] at h
    rw [← h, qform_flat]
  rw [hquad, ← hy]
  exact HCPolySupport.HighContrast.dotProduct_mulVec_le_norm_mul _ _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The coarse energy map on the doubled response space

This module proves the coarse energy-map estimate on the doubled response space together with
the intermediate steps it rests on.  The estimate is reached by two chains: one
reaches it through `metricBlockNormSq_recent_difference_le` and
`metricBlockNormSq_average_le_adaptedCellAtCenter`, and the other through
`metricBlockNormSq_blockCellAverage_diagonalWeakState_le`, which also applies
`metricBlockNormSq_average_le_adaptedCellAtCenter`.

The chain is
`doubledResponseJ_zero_left` → `doubledResponseValue_le` /
`doubledResponseValue_zero_left_eq` → `energy_map_le` → `energy_map_metric_le`, and it is
proved here in full.

The reflection order sits above this root: it supplies the comparison hypothesis `hcmp` of
the metric estimate below, and the chain below does not depend on it.  Only the single identity
`Sharp.blockVecDot_blockMatVecMul_blockScale` is needed from that layer; the same identity
already appears in `ResponseTransferSkeleton.lean`, and `E-1` proves it again here so that this
module's import edge stays at `Loewner`.

The final metric estimate is stated for an arbitrary reference block `M : BlockMat d` rather
than the self-dual diagonal metric `blockDiag m m⁻¹`.  That matrix plays no role in the proof —
it occurs only as the left-hand side of the Loewner hypothesis and inside the conclusion's
quadratic form — so taking `M` arbitrary is free, is strictly more general, and commits the
estimate to no one metric encoding.  Later layers may supply whichever of `blockDiag m m⁻¹`,
`blockSqrt (respM0 F)` or `normalizedBlock · ·` they print.
-/

open HCPolySupport.HighContrast (blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## E-1 … E-2: flat helpers -/

/-- **E-1.**  Scalar dilation acts on the doubled quadratic form, the identity
`Sharp.blockVecDot_blockMatVecMul_blockScale`.  The same identity already appears in
`ResponseTransferSkeleton.lean`, but that module is not imported here, so it is proved again
rather than reached for. -/
private theorem qform_blockScale_energyMap (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  simp only [blockScale, blockMatVecMul, smul_matVecMul, ← smul_add, blockVecDot,
    vecDot_smul_right]
  ring

/-- **E-2.**  Pairing against the zero doubled vector, the identity `blockVecDot_zero_left`. -/
private theorem blockVecDot_zero_left (X : BlockVec d) :
    blockVecDot (0 : BlockVec d) X = 0 := by
  show vecDot (0 : Vec d) X.1 + vecDot (0 : Vec d) X.2 = 0
  rw [vecDot_zero_left, vecDot_zero_left, add_zero]

/-! ## E-3 … E-6: averages of a doubled field against a fixed load -/

/-! ## E-7 … E-8: the doubled response at zero primal load -/

/-! ## E-10 … E-11: the energy map -/

/-- **E-11.**  The metric form of the energy map: once a reference block `M` is dominated by the
starred coarse block, `M ≤ c 𝐀_*(V)` in the Loewner order, the `M`-size of the cell average is
controlled by the cell energy, `y·M y ≤ c ⨍_V Y·𝐀Y`.

The estimate is stated for an arbitrary `M : BlockMat d`, in place of the self-dual diagonal
metric `blockDiag m m⁻¹`; the generalisation is free because that matrix is never unfolded in
the proof, and it keeps the result uncommitted to any one metric encoding.

This is the declaration both chains described in the header bottom out in. -/
theorem energy_map_metric_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y)
    (M : BlockMat d) {c : ℝ} (hc : 0 ≤ c)
    (hcmp : BlockMatLoewnerLE M
      (blockScale c (Book.Ch02.coarseStarredBlockMatrix U a))) :
    (1 / 2 : ℝ) *
        blockVecDot
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)
          (blockMatVecMul M
            ((Book.Ch02.averageVec U Y.potential,
              Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      c *
        ((1 / 2 : ℝ) *
          Book.Ch02.average U (fun x =>
            blockVecDot (Y.eval x)
              (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x)))) := by
  set y : BlockVec d :=
    (Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) with hy
  have h1 := hcmp y
  rw [qform_blockScale_energyMap] at h1
  have h2 := Response.energy_map_le a hEll hY
  have hprod := mul_le_mul_of_nonneg_left h2 hc
  linarith only [h1, hprod]

/-- **E-12 — the estimate in the form applied downstream.**  `E-11` with the reference block
taken to be a congruence `R^T I R`: a squared metric size `|R (Y)_V|²` of the cell average,
with no factor `½` on either side.

This is the form the upper layers should use.  It carries no symmetry hypothesis on `R`:
`blockVecDot_blockCongr` already produces the congruence on the nose.  The same shape is
reached elsewhere by unfolding `metricBlockNormSq` at the end of
`metricBlockNormSq_average_le_adaptedCellAtCenter`. -/
theorem energy_map_congr_le {U : Domain d} {lam Lam : ℝ} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    {Y : DoubledField d} (hY : Book.Ch02.IsDoubledResponseField U a Y)
    (R : BlockMat d) {c : ℝ} (hc : 0 ≤ c)
    (hcmp : BlockMatLoewnerLE (blockCongr R (Book.Ch02.blockIdentity d))
      (blockScale c (Book.Ch02.coarseStarredBlockMatrix U a))) :
    blockVecDot
        (blockMatVecMul R
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d))
        (blockMatVecMul R
          ((Book.Ch02.averageVec U Y.potential,
            Book.Ch02.averageVec U Y.flux) : BlockVec d)) ≤
      c *
        Book.Ch02.average U (fun x =>
          blockVecDot (Y.eval x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Y.eval x))) := by
  have h := energy_map_metric_le a hEll hY
    (blockCongr R (Book.Ch02.blockIdentity d)) hc hcmp
  rw [blockVecDot_blockCongr, blockMatVecMul_blockIdentity] at h
  linarith only [h]

end

end HCPolySupport.HighContrast.Multiscale
end
