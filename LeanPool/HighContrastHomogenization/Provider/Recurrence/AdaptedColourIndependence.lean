/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.ColourIndependence
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.ColourSeparation

/-!
# High-contrast homogenization: Provider.Recurrence.AdaptedColourIndependence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Independence of the responses of one colour class

Putting the colour separation together with the grouping induction gives the
second step of `l.fixed.geometry.matrix.averaging`: the coarse responses of a
same-colour family of aligned adapted cells form a jointly independent family.

The random variables are recorded in the two forms the averaging step uses.  The
first is the bare entry `𝐀(z + ⋄_j^𝐪)_{αβ}` of the coarse response.  The second
is the entry of the normalized centred block `R^{-1/2}(𝐀 - E)R^{-1/2}`, which is
the variable the printed proof calls `X_i`; normalization and centring by
deterministic blocks are a fixed affine map of the entries, so they preserve both
locality and independence.  Since the moment inequality applied to the family
asks for measurability against the global structure of the coefficient space,
that consequence of locality is recorded as well.

The index type is left arbitrary and the colour condition is carried as a
hypothesis, so a colour class of any concrete family can be used; the
specialization to the class `{w ∈ Z : w ≡ c}` of a finite family `Z` of aligned
indices is stated last, in the subtype form a finite-sum moment inequality
consumes.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The adapted cells are Borel -/

/-- An aligned adapted cell is a Borel set, being open. -/
theorem measurableSet_adaptedCellAt {q : Mat d} (hq : q.PosDef) (j : ℤ)
    (w : Fin d → ℤ) : MeasurableSet (adaptedCellAt q j w) :=
  (isOpenBoundedConvexDomain_adaptedCellAt hq j w).isOpen.measurableSet

/-! ## Independence of the coarse responses -/

/-! ## The normalized centred block -/

/-- **The entries of the normalized centred block of a cell are measurable for
the sigma-field of that cell.**  Normalization and centring by deterministic
blocks are a fixed real-linear map of the entries of the coarse response. -/
theorem measurable_toFullBlockMat_normalizedBlock_coeffSigma {U : Set (Vec d)}
    (hU : ∀ α β : BlockCoord d, @Measurable (CoeffSpace d) ℝ (coeffSigma d U) _
      fun a => blockMatEntry (coarseBlock U a) α β)
    (E F : BlockMat d) (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d U) _
      fun a => toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β := by
  let : MeasurableSpace (CoeffSpace d) := coeffSigma d U
  have hfun : (fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β) =
      fun a : CoeffSpace d => ∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
        matSqrt ((toFullBlockMat F)⁻¹) α δ *
            (blockMatEntry (coarseBlock U a) δ γ - blockMatEntry E δ γ) *
          matSqrt ((toFullBlockMat F)⁻¹) γ β := by
    funext a
    rw [toFullBlockMat_normalizedBlock_apply]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by
      rw [toFullBlockMat_blockSub_apply, toFullBlockMat_eq_blockMatEntry,
        toFullBlockMat_eq_blockMatEntry]
  rw [hfun]
  exact Finset.measurable_sum _ fun γ _ => Finset.measurable_sum _ fun δ _ =>
    (((hU δ γ).sub measurable_const).const_mul _).mul_const _

/-- The entries of the normalized centred block of an aligned adapted cell are
measurable for the sigma-field of that cell. -/
theorem measurable_toFullBlockMat_normalizedBlock_adaptedCellAt_coeffSigma
    {q : Mat d} (hq : q.PosDef) (j : ℤ) (w : Fin d → ℤ) (E F : BlockMat d)
    (α β : BlockCoord d) :
    @Measurable (CoeffSpace d) ℝ (coeffSigma d (adaptedCellAt q j w)) _
      fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) α β :=
  measurable_toFullBlockMat_normalizedBlock_coeffSigma
    (fun α' β' => measurable_blockMatEntry_coarseBlock_adaptedCellAt hq j w α' β') E F α β

/-- The entries of the normalized centred block of an aligned adapted cell are
measurable for the global structure of the coefficient space. -/
theorem measurable_toFullBlockMat_normalizedBlock_adaptedCellAt {q : Mat d}
    (hq : q.PosDef) (j : ℤ) (w : Fin d → ℤ) (E F : BlockMat d) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) α β :=
  measurable_of_measurable_coeffSigma
    (measurable_toFullBlockMat_normalizedBlock_adaptedCellAt_coeffSigma hq j w E F α β)

/-- **The normalized centred responses of a same-colour family of distinct
aligned adapted cells are jointly independent**, entry by entry.  These are the
variables `X_i` of `l.fixed.geometry.matrix.averaging`. -/
theorem iIndepFun_toFullBlockMat_normalizedBlock_adaptedCellAt {ι : Type*}
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) {z : ι → Fin d → ℤ}
    (hinj : Function.Injective z)
    (hcol : ∀ n n' : ι, (fun i => ((z n i : ZMod 3))) = fun i => ((z n' i : ZMod 3)))
    (E F : BlockMat d) (α β : BlockCoord d) :
    ProbabilityTheory.iIndepFun
      (fun n : ι => fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCellAt q j (z n)) a) E) F) α β) P :=
  iIndepFun_of_measurable_coeffSigma P hP
    (fun n => measurableSet_adaptedCellAt (posDef_of_isRoundedGrid hq) j (z n))
    (fun n => measurable_toFullBlockMat_normalizedBlock_adaptedCellAt_coeffSigma
      (posDef_of_isRoundedGrid hq) j (z n) E F α β)
    (pairwise_unitSeparated_adaptedCellAt hq hj hinj hcol)

/-! ## One colour class of a finite family -/

/-- **The normalized centred responses of one colour class of a finite family of
aligned adapted cells are jointly independent.**  This is the specialization the
finite-sum moment inequality is applied to: the index type is the colour class
`{w ∈ Z : w ≡ c mod 3}`, and the family is centred and normalized by the
deterministic blocks `E` and `R`. -/
theorem iIndepFun_toFullBlockMat_normalizedBlock_colourClass
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) (Z : Finset (Fin d → ℤ))
    (c : Fin d → ZMod 3) (E F : BlockMat d) (α β : BlockCoord d) :
    ProbabilityTheory.iIndepFun
      (fun v : {w : Fin d → ℤ //
          w ∈ Z.filter fun v => (fun i => ((v i : ZMod 3))) = c} =>
        fun a : CoeffSpace d =>
          toFullBlockMat (normalizedBlock
            (blockSub (coarseBlock (adaptedCellAt q j v.1) a) E) F) α β) P :=
  iIndepFun_toFullBlockMat_normalizedBlock_adaptedCellAt P hP hq hj
    Subtype.val_injective (fun v v' => intCast_eq_of_mem_filter v.2 v'.2) E F α β

end

end Recurrence
end HighContrast
end HCPolySupport
