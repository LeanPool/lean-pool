/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.TransportObjects

/-!
# High-contrast homogenization: Setup.SelectionObjects

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Carriers for the terminal selection, the adapted response, and the transfer

The objects the selection-and-response section names and the earlier layers do
not already carry: the contained-cell family of a terminal cell, the coupled
execution burn, the windowed source collection the selector returns, the source
gauge of the adapted-to-Euclidean comparison, and the deterministic comparison
size that fixes the two transfer gaps.

Two conventions carry over and are used again.  Scalar sizes are Loewner, and
the sharp adjoint of a reference block is its block reflection, so the dual
reference block `𝐄_*^{-1}` is `blockReflect 𝐄` and `𝐄_*` is `blockSharp 𝐄`.
Every quantity whose finiteness is asserted is extended-real valued.

The contained-cell family is displayed twice in the reference text, once as the
family of aligned centers whose own cell is contained in the terminal cell and
once as the intersection of the aligned lattice with the terminal cell, and the
two are proved equal there by the parity of the triadic ratio.  The intersection
form is taken here, because it is the form in which the fixed-grid layer's
histories and the source-control row already read their index sets.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-! ## The contained cells of a terminal cell -/

/-- The contained-cell family `𝒵_{k,v}^q = 3^k 𝕃_q ∩ ⋄_v^q` of the terminal cell
at scale `v`, in the intersection form the reference text proves equal to the
containment form. -/
@[expose]
def containedCenters (q : Mat d) (k v : ℤ) : Set (Vec d) :=
  {z | (∃ w : Fin d → ℤ, z = adaptedCellCenter q k w) ∧ z ∈ adaptedCell q v}

/-! ## The coupled execution burn -/

/-- The coupled execution burn `j_†` of the terminal selection
(`e.global.selection.lower.scale`): the larger of the uniform source burn and
the ceiling that makes the pair `(j_†, j_† + ⌈C_exec Λ⌉)` a coupled window
pair. -/
@[expose]
def coupledExecBurn (d : ℕ) (Q K Cexec Lam : ℝ) : ℤ :=
  max (sourceBurn d Q K)
    ⌈((d : ℝ) * (⌈Cexec * Lam⌉ : ℤ) +
        16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) / (4 * (d : ℝ) + 3)⌉

/-! ## The windowed source collection -/

/-- The windowed source fields `S_sansr_sansc_sans^S_{q,j_*}(s,t;P,Y_P)` read at the two
endpoints of a terminal window: the primal and adjoint bounded-window localized
rows on every contained cell below the alignment, the two all-earlier annealed
rows at the weight `λ_resp = 3/2`, and the reference comparisons at both
endpoints together with their adjoint congruences.

The localized rows hold for one and the same realization of the multiplier,
simultaneously over every scale below the alignment and every contained cell,
which is why the almost-everywhere quantifier stands outside them.

The two annealed rows are read in partial-sum form over a lower cutoff, as the
source-control proposition produces them: the printed row is the limit of those
partial sums, and the partial-sum family is the form a consumer destructures.

The normalization of the two rows and of the reference comparisons is the
selector's own `𝒰 = 2`, the uniform multiplier cap of the window; the
source-control proposition produces them with `E[Y_P]`, which is at most `𝒰`.

The two rows are the only fields written as quadratic forms rather than as
Loewner comparisons, because a partial sum of matrices has no Loewner carrier
here; the two readings agree, since the Loewner order on doubled blocks is
itself defined by the comparison of the quadratic forms.  The average over a
row's index set is written with the reciprocal of its cardinality, which is zero
on an empty set and would make the row trivial; no row is empty, because the
zero index always lies in it — the centre of the cell at the zero index is the
origin, and the origin lies in every adapted cell. -/
structure IsWindowedSourceFields (P : Measure (CoeffSpace d)) (g Cd : ℝ)
    (E : BlockMat d) (jStar : ℤ) (mu : Mat d) (s t : ℤ)
    (Y : CoeffSpace d → ℝ) : Prop where
  localized : ∀ᵐ a ∂P, ∀ k : ℤ, k < jStar → ∀ v : ℤ, v = s ∨ v = t →
    ∀ z ∈ containedCenters (roundedGrid jStar mu) k v,
      BlockMatLoewnerLE
          (coarseBlock (adaptedCellTranslate (roundedGrid jStar mu) k z) a)
          (blockScale (boundaryConst Cd g mu * Y a * burnDiscount g jStar k) E) ∧
        BlockMatLoewnerLE
          (coarseStarInv (adaptedCellTranslate (roundedGrid jStar mu) k z) a)
          (blockScale (boundaryConst Cd g mu * Y a * burnDiscount g jStar k)
            (blockReflect E))
  rows : ∀ Ctr : ℤ → Finset (Fin d → ℤ),
    (∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
      w ∈ Ctr k ↔
        adaptedCellCenter (roundedGrid jStar mu) k w ∈
          adaptedCell (roundedGrid jStar mu) s) →
    ∀ Klo : ℤ, Klo < jStar → ∀ X : BlockVec d,
      ∑ k ∈ Finset.Ico Klo jStar,
          (3 : ℝ) ^ (3 / 2 * ((k : ℝ) - (s : ℝ))) *
            (((Ctr k).card : ℝ)⁻¹ *
              ∑ w ∈ Ctr k,
                blockVecDot X
                  (blockMatVecMul
                    (annealedBlock P
                      (adaptedCellAt (roundedGrid jStar mu) k w)) X)) ≤
        boundaryConst Cd g mu * 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
            (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) *
          blockVecDot X (blockMatVecMul E X) ∧
      ∑ k ∈ Finset.Ico Klo jStar,
          (3 : ℝ) ^ (3 / 2 * ((k : ℝ) - (s : ℝ))) *
            (((Ctr k).card : ℝ)⁻¹ *
              ∑ w ∈ Ctr k,
                blockVecDot X
                  (blockMatVecMul
                    (annealedStarInv P
                      (adaptedCellAt (roundedGrid jStar mu) k w)) X)) ≤
        boundaryConst Cd g mu * 2 / ((3 : ℝ) ^ (3 / 2 - g) - 1) *
            (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) *
          blockVecDot X (blockMatVecMul (blockReflect E) X)
  reference : ∀ v : ℤ, v = s ∨ v = t →
    BlockMatLoewnerLE
        (blockScale (boundaryConst Cd g mu * 2)⁻¹ (blockSharp E))
        (adaptedMean P (roundedGrid jStar mu) v) ∧
      BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar mu) v)
        (blockScale (boundaryConst Cd g mu * 2) E) ∧
      BlockMatLoewnerLE
        (blockScale (boundaryConst Cd g mu * 2)⁻¹ (blockReflect (blockSharp E)))
        (blockReflect (adaptedMean P (roundedGrid jStar mu) v)) ∧
      BlockMatLoewnerLE (blockReflect (adaptedMean P (roundedGrid jStar mu) v))
        (blockScale (boundaryConst Cd g mu * 2) (blockReflect E))
  refContrast_le : BlockMatLoewnerLE E (blockScale (kappaRef E) (blockSharp E))
  kappaRef_le : kappaRef E ≤ 6 * aspectRatio E

/-! ## The transfer gauge and the comparison sizes -/

/-- The source gauge `Γ_{g,S}(j) = (1-g)^{-1}(1 + K_{Ψ_S}^2 3^{-j})^g` of the
adapted-to-Euclidean comparison. -/
@[expose]
def transferGauge (g K : ℝ) (j : ℤ) : ℝ :=
  (1 - g)⁻¹ * (1 + K ^ 2 * (3 : ℝ) ^ (-j)) ^ g

/-- The deterministic comparison size
`𝒯_bar_{q,S}(j) = U C_AE(d) C_src(d) κ_𝐄 𝔢_q² ζ_g Γ_{g,S}(j)`.  It involves the
mean of the window multiplier only through the deterministic normalization
constant `U`. -/
@[expose]
def transferSizeBar (U CAE Cd g K : ℝ) (E : BlockMat d) (mu : Mat d) (j : ℤ) :
    ℝ :=
  U * CAE * Cd * kappaRef E * witnessEccentricity mu ^ 2 * zetaG g *
    transferGauge g K j

end

end HighContrast
end HCPolySupport
