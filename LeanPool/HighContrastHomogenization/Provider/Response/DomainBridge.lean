/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellDomain
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Existence
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.BasicVariationalIdentities
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.FirstVariation
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Quadraticity
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.GradientLinearity
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.GradientUniqueness
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.MagicIdentities
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.BlockCoarseMatrix
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.BlockMatrixField
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.DoubledMu
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.DoubledResponse
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.CoarseGrainingEstimates
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.SymmetricDirichletNeumann
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.SubadditivityScaling

/-!
# High-contrast homogenization: Provider.Response.DomainBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The adapted cell as a variational domain

The variational layer of Armstrong–Kuusi Chapter 2 — existence and uniqueness of the
response maximizer, the first and second variation, the average identities, the
energy identity, quadraticity, the block matrix formula and its row-swapped
inverse, the doubled splitting and the doubled response space, the coarse
graining estimates, and the scaling identities — is stated over an arbitrary
nonempty bounded open convex domain.  The adapted cells `⋄_k^q = q□_k` and
`z + ⋄_k^q` of a rounded geometry (`s.scale.selection`) are such domains, so the
whole layer is available on them with no adaptation at all.

This file records that.  It packages an adapted cell as a Chapter 2 domain and
transports each of the fourteen theory bundles to the two adapted cells the
response argument uses: the parent cell `U_t = q□_t` and the aligned child cell
`U_k(z) = z + q□_k`, `z ∈ 3^k𝕃_q`.  Downstream files quote the specializations
below and never rebuild the domain.

Two clauses inside those bundles do not survive the move, and neither is used
here.  `BlockCoarseMatrixTheory.block_matrix_subadditive`,
`BlockCoarseMatrixTheory.starred_inverse_subadditive` and
`ResponseSubadditivityAndScalingTheory.responseJ_subadditive` quantify over a
`Book.Ch02.DomainPartition`, whose realization clause forces the parent to be an
open triadic cube subdivided into triadic descendants; over an adapted cell of a
general grid `q` there is no such partition and the three clauses carry no
content.  The subadditivity the paper uses is instead the arbitrary almost
everywhere partition into convex cells, `Recurrence.blockQuadratic_le_sum_weight_of_-
aePartition`, and its instance at the aligned subdivision,
`Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ} {q : Mat d}

/-! ## The two adapted domains -/

/-- The adapted cell `⋄_k^q = q□_k` of a rounded geometry, as a Chapter 2
domain: it is open, bounded, convex and nonempty because `q` is positive
definite. -/
@[expose]
def adaptedDomain (hq : q.PosDef) (k : ℤ) : Domain d where
  carrier := adaptedCell q k
  isDomain := Recurrence.isOpenBoundedConvexDomain_adaptedCell hq k
  nonempty := Recurrence.adaptedCell_nonempty q k

@[simp] theorem adaptedDomain_carrier (hq : q.PosDef) (k : ℤ) :
    (adaptedDomain hq k : Set (Vec d)) = adaptedCell q k := rfl

/-- The aligned adapted cell `z + ⋄_k^q` with `z = 3^kqw ∈ 3^k𝕃_q`, as a
Chapter 2 domain. -/
@[expose]
def adaptedDomainAt (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ) : Domain d where
  carrier := adaptedCellAt q k w
  isDomain := Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w
  nonempty := Recurrence.adaptedCellAt_nonempty q k w

@[simp] theorem adaptedDomainAt_carrier (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ) :
    (adaptedDomainAt hq k w : Set (Vec d)) = adaptedCellAt q k w := rfl

/-- An aligned cell of the subdivision sits inside the parent cell, as domains:
the containment of the adapted cells at the level of Chapter 2 domains. -/
theorem adaptedDomainAt_subset (hq : q.PosDef) {j p : ℤ} (hjp : j ≤ p)
    {w : Fin d → ℤ} (hmem : adaptedCellCenter q j w ∈ adaptedCell q p) :
    (adaptedDomainAt hq j w : Set (Vec d)) ⊆ (adaptedDomain hq p : Set (Vec d)) :=
  Recurrence.adaptedCellAt_subset_adaptedCell hq hjp hmem

/-! ## The fourteen theories on the parent cell `q□_k` -/

/-! ## The fourteen theories on an aligned cell `z + q□_k` -/

end

end Response
end HighContrast
end HCPolySupport
