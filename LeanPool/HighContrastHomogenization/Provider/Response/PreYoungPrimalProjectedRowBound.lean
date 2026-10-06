/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungAllScaleNestedStationarity
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectionGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalProjectionMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPartialConstants
public import LeanPool.HighContrastHomogenization.Provider.Response.SplitReadoutIntegrability

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalProjectedRowBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory _root_.Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-!
# Finite projected primal rows

The finite cube projections of the primal potential pairing are integrable,
and their annealed absolute values obey a depth-independent bound by the
all-earlier hatted row.
-/

/-- Finiteness of the primal weak quantity makes every absolute potential-slot
cell pairing integrable over the coefficient law. -/
theorem integrable_abs_primal_cell_pairing_of_weak
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {k t : ℤ} (hkt : k ≤ t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    Integrable (fun a : CoeffSpace d ↦
      |vecDot Qcen (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1|) P := by
  have hread :=
    (integrable_primal_adaptedFiveTermSplit_readouts
      hq hm0 hkt g hg p r hweak).1
  have hsum : Integrable (fun a : CoeffSpace d ↦
      ∑ i, Qcen i * (blockCellAverage (adaptedCellAt q k w)
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1 i) P :=
    integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦ by
      simpa only [toFullBlockVec] using
        (hread w hw (Sum.inl i)).const_mul (Qcen i)
  simpa only [vecDot, Real.norm_eq_abs] using hsum.norm

/-- The sharp cutoff decay at projection depth `j` is the corresponding
fine-scale row weight, including the factor from the half-energy convention. -/
theorem sharp_depth_term_eq_scale_term
    (C R : ℝ) (s t : ℤ) (j : ℕ) :
    C * ((3 : ℝ) ^ (-((t - s) + (j : ℤ)) : ℤ)) * (2 * R) =
      6 * C * (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
        ((3 : ℝ) ^ (((s - ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ) - (s : ℝ)) * R) := by
  rw [← Real.rpow_intCast (3 : ℝ) (-((t - s) + (j : ℤ)))]
  have hpow :
      (3 : ℝ) ^ (((-((t - s) + (j : ℤ)) : ℤ) : ℤ) : ℝ) =
        (3 : ℝ) ^ (1 : ℝ) *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
            (3 : ℝ) ^ (((s - ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ) - (s : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [hpow]
  norm_num
  ring

/-- Reindexing projection depths by fine scales and enlarging to a closed
integer interval is absorbed by the common cutoff derivative coefficient. -/
theorem sum_sharp_depth_rows_le_scale_rows
    [NeZero d] (s t : ℤ) (N : ℕ) (row : ℤ → ℝ)
    (hrow : ∀ k, 0 ≤ row k) :
    (∑ j ∈ Finset.range N,
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
        (3 : ℝ) ^ (-((t - s) + (j : ℤ)) : ℤ) *
          (2 * row (s - ((j + 1 : ℕ) : ℤ)))) ≤
      adaptedCutoffDerivativeCoeff d *
        (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
          ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
            (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * row k := by
  let Csharp : ℝ :=
    32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound
  let scale : ℤ → ℝ := fun k ↦
    (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * row k
  have hscale : ∀ k, 0 ≤ scale k := fun k ↦
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hrow k)
  have heq :
      (∑ j ∈ Finset.range N,
          Csharp * (3 : ℝ) ^ (-((t - s) + (j : ℤ)) : ℤ) *
            (2 * row (s - ((j + 1 : ℕ) : ℤ)))) =
        6 * Csharp * (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
          ∑ k ∈ Finset.Ico (s - (N : ℤ)) s, scale k := by
    calc
      _ = ∑ j ∈ Finset.range N,
          6 * Csharp * (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
            scale (s - ((j + 1 : ℕ) : ℤ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [scale] using
          sharp_depth_term_eq_scale_term Csharp
            (row (s - ((j + 1 : ℕ) : ℤ))) s t j
      _ = 6 * Csharp * (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
          ∑ j ∈ Finset.range N, scale (s - ((j + 1 : ℕ) : ℤ)) := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [sum_range_eq_sum_Ico_descending]
  rw [show (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound) =
      Csharp by rfl, heq]
  have hsubset : Finset.Ico (s - (N : ℤ)) s ⊆
      Finset.Icc (s - (N : ℤ)) s := by
    intro k hk
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.le⟩
  have hsum :
      ∑ k ∈ Finset.Ico (s - (N : ℤ)) s, scale k ≤
        ∑ k ∈ Finset.Icc (s - (N : ℤ)) s, scale k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun k hk hnot ↦ hscale k
  have hCsharp : 0 ≤ Csharp := by
    dsimp only [Csharp]
    exact mul_nonneg (by positivity)
      smoothTransitionProfile.derivBound_nonneg
  have hscalePow : 0 ≤ (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsumNonneg :
      0 ≤ ∑ k ∈ Finset.Icc (s - (N : ℤ)) s, scale k :=
    Finset.sum_nonneg fun k hk ↦ hscale k
  calc
    6 * Csharp * (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
        ∑ k ∈ Finset.Ico (s - (N : ℤ)) s, scale k ≤
      6 * Csharp * (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
        ∑ k ∈ Finset.Icc (s - (N : ℤ)) s, scale k :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (mul_nonneg (by positivity) hCsharp) hscalePow)
    _ ≤ adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
        ∑ k ∈ Finset.Icc (s - (N : ℤ)) s, scale k := by
      apply mul_le_mul_of_nonneg_right _ hsumNonneg
      exact mul_le_mul_of_nonneg_right
        six_mul_sharpCutoffCoefficient_le_adaptedCutoffDerivativeCoeff
        hscalePow
    _ = _ := by rfl

/-- Every finite projected primal oscillation is almost-everywhere strongly
measurable under the coefficient law. -/
theorem aestrongly_measurable_primal_projected_oscillation
    [NeZero d] {P : Measure (CoeffSpace d)}
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d) (N : ℕ) :
    AEStronglyMeasurable
      (primal_projected_oscillation hq s t g hg p r Qcen N) P := by
  apply (aemeasurable_avsum (alignedIndex q s t) _ ?_).aestronglyMeasurable
  intro z hz
  exact (aestronglyMeasurable_cutoff_projected_primal_pairing_subSkew
    hq hst hz g hg p r Qcen N).aemeasurable

end

end HCPolySupport.HighContrast.Response
