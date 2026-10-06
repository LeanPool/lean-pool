/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.CellMuMeasurability

/-!
# High-contrast homogenization: Provider.Recurrence.CellLocalMeasurability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The response of a cell is measurable for the sigma-field of that cell

The first of the coarse-block properties taken from HC asks for
`F(U)`-measurability of `𝐀(U)`, not merely measurability: the coarse response
of a cell must be a function of the coefficient field *inside* that cell.  This
file proves the clause in that form, on every bounded open cell of positive
volume, hence on
every adapted cell.

Only one step separates it from the measurability already proved.  The
representative map from the coefficient space into the exact coarse source
carries the generating linear statistics of `F(U)` to the generating bilinear
tests of the source's own sigma-field of `U` — the two families of test
functions are the same, and the representative agrees with the field almost
everywhere — so the map is measurable for the local sigma-fields and not only
for the global ones.  The coarse-grained energy of the cell is already known to
be local on the source, and the entries of the response are its polarizations.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The local sigma-fields of the coefficient space are monotone -/

/-- The sigma-fields `F(U)` grow with the cell: a test function supported in `U`
is one supported in any larger set. -/
theorem coeffSigma_mono {U V : Set (Vec d)} (hUV : U ⊆ V) :
    coeffSigma d U ≤ coeffSigma d V := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨e, e', φ, hφ, t, ht, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, ⟨hφ.contDiff, hφ.hasCompactSupport, hφ.tsupport_subset.trans hUV⟩, t, ht, rfl⟩

/-! ## The representative map is local -/

/-- **The representative map is measurable for the sigma-fields of a cell**: it
pulls each generator of the source's sigma-field of `U` back to a generator of
`F(U)`, the test functions of the two families being the same and the
representative agreeing with the field almost everywhere. -/
theorem measurable_sourceRepresentative_local (U : Set (Vec d)) (hU : MeasurableSet U) :
    @Measurable (CoeffSpace d) (Source.Coarse.Carrier d) (coeffSigma d U)
      (Source.Coarse.localSigma U hU) sourceRepresentative := by
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d U
  refine measurable_generateFrom ?_
  rintro s ⟨e, e', φ, hφ, hsupp, t, ht, rfl⟩
  have hset : sourceRepresentative (d := d) ⁻¹'
      (Source.Coarse.bilinearTest e e' φ ⁻¹' t) = coeffPairing e e' φ ⁻¹' t := by
    ext a
    change Source.Coarse.bilinearTest e e' φ (sourceRepresentative a) ∈ t ↔ _
    rw [bilinearTest_sourceRepresentative]
    rfl
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, ⟨hφ.smooth, hφ.compact, hsupp⟩, t, ht, rfl⟩

/-! ## The response of a cell is measurable for the sigma-field of the cell -/

/-- **The coarse-grained energy of a bounded open cell of positive volume is
`F(U)`-measurable.** -/
theorem measurable_Mu_coeffSigma {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUbdd : IsBoundedDomain U) (hvol : 0 < (volume U).toReal) (Q : BlockVec d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) _
      fun a : CoeffSpace d => Mu U Q (⇑a.1 : CoeffField d) := by
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d U
  let : MeasurableSpace (Source.Coarse.Carrier d) :=
    Source.Coarse.localSigma U hUopen.measurableSet
  have hEq : (fun a : CoeffSpace d => Mu U Q (⇑a.1 : CoeffField d))
      = (fun b : Source.Coarse.Carrier d => Mu U Q (b.1 : CoeffField d)) ∘
        sourceRepresentative := by
    funext a
    exact Mu_congr_of_ae_eq (ae_restrict_of_ae (sourceRepresentative_ae_eq a)) Q
  rw [hEq]
  exact (measurable_Mu_carrier_local hUopen hUbdd hvol Q).comp
    (measurable_sourceRepresentative_local U hUopen.measurableSet)

/-- **The measurability of the variational coarse block in its printed
form**: every entry of the coarse block response of a bounded open cell of
positive volume is measurable for the sigma-field of that cell. -/
theorem measurable_blockMatEntry_coarseBlock_coeffSigma {U : Set (Vec d)}
    (hUopen : IsOpen U) (hUbdd : IsBoundedDomain U) (hvol : 0 < (volume U).toReal)
    (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) _
      fun a : CoeffSpace d => blockMatEntry (coarseBlock U a) α β :=
  measurable_blockMatEntry_coarseBlock_of_measurable_Mu
    (fun Q => measurable_Mu_coeffSigma hUopen hUbdd hvol Q) α β

/-! ## The clause on the adapted cells -/

/-- **The coarse response of an aligned adapted cell is measurable for the
sigma-field of that cell.** -/
theorem measurable_blockMatEntry_coarseBlock_adaptedCellAt {q : Mat d} (hq : q.PosDef)
    (j : ℤ) (w : Fin d → ℤ) (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d (adaptedCellAt q j w)) _
      fun a : CoeffSpace d => blockMatEntry (coarseBlock (adaptedCellAt q j w) a) α β := by
  have hpos : 0 < volume (adaptedCellAt q j w) := volume_adaptedCellAt_pos hq j w
  have hfin : volume (adaptedCellAt q j w) ≠ ⊤ :=
    ne_of_lt (isOpenBoundedConvexDomain_adaptedCellAt hq j w).volume_lt_top
  exact measurable_blockMatEntry_coarseBlock_coeffSigma
    (isOpenBoundedConvexDomain_adaptedCellAt hq j w).isOpen
    (isOpenBoundedConvexDomain_adaptedCellAt hq j w).isBoundedDomain
    (ENNReal.toReal_pos hpos.ne' hfin) α β

end

end Recurrence
end HighContrast
end HCPolySupport
