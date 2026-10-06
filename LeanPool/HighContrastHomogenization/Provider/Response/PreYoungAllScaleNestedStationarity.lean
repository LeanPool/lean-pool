/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRowPartialDischarge

/-!
# High-contrast homogenization: Provider.Response.PreYoungAllScaleNestedStationarity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Stationarity along nested cells below the alignment scale

Although a fine-scale cell need not itself have an integral center, moving
between two copies of that cell inside aligned parent cells is an integer
translation.  This is the stationarity relation needed by finite projection
arguments whose child depth tends to infinity.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A nested fine cell is an integer translate of the reference fine cell
whenever the parent scale is aligned.  No alignment assumption is needed at
the fine scale. -/
theorem exists_translateSet_adaptedCellAt_nestedLabel_of_parent_aligned
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {k s : ℤ} (hks : k ≤ s) (hls : l ≤ s)
    (z w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ,
      adaptedCellAt q k (nestedLabel k s z w) =
        translateSet (Source.AKL.intTranslation v) (adaptedCellAt q k w) := by
  obtain ⟨v, hv⟩ := Recurrence.exists_intVec_adaptedCellCenter hgrid hls z
  refine ⟨v, ?_⟩
  rw [Recurrence.adaptedCellAt_eq_translateSet, Recurrence.adaptedCellAt_eq_translateSet,
    translateSet_translateSet]
  have hsplit :
      adaptedCellCenter q k (nestedLabel k s z w) =
        adaptedCellCenter q s z + adaptedCellCenter q k w := by
    apply PortableHistory.adaptedCellCenter_split q hks
    intro i
    simp only [nestedLabel]
    ring
  rw [hsplit, hv]
  congr 1
  exact add_comm _ _

/-- The annealed block is unchanged between nested copies of a fine cell when
the displacement comes from an aligned parent scale. -/
theorem annealedBlock_adaptedCellAt_nestedLabel_eq_of_parent_aligned
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {k s : ℤ} (hks : k ≤ s) (hls : l ≤ s)
    (z w : Fin d → ℤ)
    (hmeas : HasMeasurableCoarseBlock P (adaptedCellAt q k w)) :
    annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)) =
      annealedBlock P (adaptedCellAt q k w) := by
  obtain ⟨v, hv⟩ :=
    exists_translateSet_adaptedCellAt_nestedLabel_of_parent_aligned
      hgrid hks hls z w
  rw [hv]
  exact Recurrence.annealedBlock_translateSet hstat hmeas v

/-- Parent alignment preserves the primal flux load between nested copies of
a fine cell. -/
theorem profileSchurLoadFlux_nestedLabel_eq_of_parent_aligned
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {k s : ℤ} (hks : k ≤ s) (hls : l ≤ s)
    (z w : Fin d → ℤ)
    (hmeas : HasMeasurableCoarseBlock P (adaptedCellAt q k w))
    (h : Mat d) (Qcen : Vec d) :
    profileSchurLoadFlux
        (profileHattedBlock h
          (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Qcen =
      profileSchurLoadFlux
        (profileHattedBlock h (annealedBlock P (adaptedCellAt q k w))) Qcen :=
  congrArg (fun H ↦ profileSchurLoadFlux (profileHattedBlock h H) Qcen)
    (annealedBlock_adaptedCellAt_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeas)

/-- Parent alignment preserves the primal gradient load between nested copies
of a fine cell. -/
theorem profileSchurLoadGradient_nestedLabel_eq_of_parent_aligned
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {k s : ℤ} (hks : k ≤ s) (hls : l ≤ s)
    (z w : Fin d → ℤ)
    (hmeas : HasMeasurableCoarseBlock P (adaptedCellAt q k w))
    (h : Mat d) (Pcen : Vec d) :
    profileSchurLoadGradient
        (profileHattedBlock h
          (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Pcen =
      profileSchurLoadGradient
        (profileHattedBlock h (annealedBlock P (adaptedCellAt q k w))) Pcen :=
  congrArg (fun H ↦ profileSchurLoadGradient (profileHattedBlock h H) Pcen)
    (annealedBlock_adaptedCellAt_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeas)

/-- Parent alignment preserves the adjoint flux load between nested copies of
a fine cell. -/
theorem profileSchurLoadFlux_adjoint_nestedLabel_eq_of_parent_aligned
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {k s : ℤ} (hks : k ≤ s) (hls : l ≤ s)
    (z w : Fin d → ℤ)
    (hmeas : HasMeasurableCoarseBlock P (adaptedCellAt q k w))
    (h : Mat d) (Qcen : Vec d) :
    profileSchurLoadFlux
        (profileHattedAdjointBlock h
          (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Qcen =
      profileSchurLoadFlux
        (profileHattedAdjointBlock h
          (annealedBlock P (adaptedCellAt q k w))) Qcen :=
  congrArg (fun H ↦ profileSchurLoadFlux (profileHattedAdjointBlock h H) Qcen)
    (annealedBlock_adaptedCellAt_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeas)

/-- Parent alignment preserves the adjoint gradient load between nested copies
of a fine cell. -/
theorem profileSchurLoadGradient_adjoint_nestedLabel_eq_of_parent_aligned
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    {k s : ℤ} (hks : k ≤ s) (hls : l ≤ s)
    (z w : Fin d → ℤ)
    (hmeas : HasMeasurableCoarseBlock P (adaptedCellAt q k w))
    (h : Mat d) (Pcen : Vec d) :
    profileSchurLoadGradient
        (profileHattedAdjointBlock h
          (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Pcen =
      profileSchurLoadGradient
        (profileHattedAdjointBlock h
          (annealedBlock P (adaptedCellAt q k w))) Pcen :=
  congrArg (fun H ↦ profileSchurLoadGradient (profileHattedAdjointBlock h H) Pcen)
    (annealedBlock_adaptedCellAt_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hls z w hmeas)

end

end HCPolySupport.HighContrast.Response
