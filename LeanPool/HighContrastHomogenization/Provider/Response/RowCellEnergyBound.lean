/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCellEnergy
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum

/-!
# High-contrast homogenization: Provider.Response.RowCellEnergyBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The per-scale cell-energy bound of a cutoff-defect mean row

The scale sums of a cutoff-defect mean row weigh each aligned cell by the
terminal optimizer's energy on that cell.  Because the aligned cells of one
scale partition their parent with equal volume, the normalized average of those
cell energies is exactly the terminal response value; after annealing, the
normalized average of the annealed cell energies is exactly the annealed
terminal response.

The row is written on the cells of the reference scale-`s` cell, so each row
cell carries the annealed energy averaged over the scale-`s` parents in which it
sits; the parent average and the within-parent average then compose to the
single average over the terminal cell.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The pathwise cell energy -/

/-- The pathwise quarter energy of the terminal optimizer state on an aligned
cell.  The quarter normalizes the doubled energy density to the response value:
the normalized average over one aligned subdivision is exactly the terminal
response. -/
@[expose]
def cellQuarterEnergy {q : Mat d} (hq : q.PosDef) (k t : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) (p r : Vec d) : ℝ :=
  (1 / 4 : ℝ) * Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
    blockVecDot (diagonalWeakState hq t a p r x)
      (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
        (diagonalWeakState hq t a p r x)))

/-- **The equal-volume parent-energy partition.**  The normalized average of the
pathwise quarter cell energies over one aligned subdivision of the terminal cell
is exactly the terminal response value. -/
theorem avsum_cellQuarterEnergy_eq_responseJ {q : Mat d}
    (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t) (a : CoeffSpace d) (p r : Vec d) :
    avsum (alignedIndex q k t) (fun w ↦ cellQuarterEnergy hq k t w a p r) =
      responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p r := by
  simp only [cellQuarterEnergy]
  rw [avsum_const_mul, avsum_diagonalWeakState_energy_eq hq hkt a p r,
    responseJ_eq_sq_diagonalWeakEnergy]
  ring

/-! ## The annealed cell energy -/

/-- The annealed quarter energy of the terminal optimizer state on an aligned
cell. -/
@[expose]
def profileAnnealedCellEnergySq (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (k t : ℤ) (w : Fin d → ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) : ℝ :=
  ∫ a, cellQuarterEnergy hq k t w (sample a) p r ∂P

/-- **The annealed parent-energy partition.**  The normalized average of the
annealed quarter cell energies over one aligned subdivision of the terminal cell
is exactly the annealed terminal response. -/
theorem avsum_profileAnnealedCellEnergySq_eq
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) {k t : ℤ}
    (hkt : k ≤ t) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hint : ∀ w ∈ alignedIndex q k t,
      Integrable (fun a ↦ cellQuarterEnergy hq k t w (sample a) p r) P) :
    avsum (alignedIndex q k t)
        (fun w ↦ profileAnnealedCellEnergySq P hq k t w sample p r) =
      ∫ a, responseJ (adaptedDomain hq t)
        ((sample a).coeffOn (adaptedDomain hq t)) p r ∂P := by
  classical
  rw [avsum_eq]
  simp only [profileAnnealedCellEnergySq]
  rw [← MeasureTheory.integral_finsetSum _ hint,
    ← MeasureTheory.integral_const_mul]
  have hpt : ∀ a : CoeffSpace d,
      ((alignedIndex q k t).card : ℝ)⁻¹ *
          ∑ i ∈ alignedIndex q k t, cellQuarterEnergy hq k t i (sample a) p r =
        responseJ (adaptedDomain hq t)
          ((sample a).coeffOn (adaptedDomain hq t)) p r := by
    intro a
    rw [← avsum_eq]
    exact avsum_cellQuarterEnergy_eq_responseJ hq hkt (sample a) p r
  exact MeasureTheory.integral_congr_ae (_root_.Filter.Eventually.of_forall hpt)

/-! ## The row cell energy -/

/-- The label of the scale-`k` cell sitting at relative position `w` inside the
scale-`s` cell of label `z`. -/
@[expose]
def nestedLabel (k s : ℤ) (z w : Fin d → ℤ) : Fin d → ℤ :=
  fun i ↦ 3 ^ (s - k).toNat * z i + w i

/-- The annealed row cell energy: the energy the row closers weigh each
reference cell by, averaged over the scale-`s` parents that carry a copy of that
cell. -/
@[expose]
def profileRowCellEnergy (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (k s t : ℤ) (w : Fin d → ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) : ℝ :=
  Real.sqrt (avsum (alignedIndex q s t) (fun z ↦
    profileAnnealedCellEnergySq P hq k t (nestedLabel k s z w) sample p r))

theorem profileRowCellEnergy_nonneg (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (k s t : ℤ) (w : Fin d → ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) :
    0 ≤ profileRowCellEnergy P hq k s t w sample p r := Real.sqrt_nonneg _

/-- **The per-scale row energy identity.**  Under the nested reindexing of the
aligned cells and the cellwise law integrability, the normalized average of the
squared row cell energies at one scale is exactly the annealed terminal
response. -/
theorem avsum_sq_profileRowCellEnergy_eq
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) {k s t : ℤ}
    (hks : k ≤ s) (hst : s ≤ t) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d)
    (hnonneg : ∀ w ∈ alignedIndex q k t,
      0 ≤ profileAnnealedCellEnergySq P hq k t w sample p r)
    (hnestMem : ∀ w ∈ alignedIndex q k s, ∀ z ∈ alignedIndex q s t,
      nestedLabel k s z w ∈ alignedIndex q k t)
    (hnest : ∀ f : (Fin d → ℤ) → ℝ,
      avsum (alignedIndex q k s) (fun w ↦
          avsum (alignedIndex q s t) (fun z ↦ f (nestedLabel k s z w))) =
        avsum (alignedIndex q k t) f)
    (hint : ∀ w ∈ alignedIndex q k t,
      Integrable (fun a ↦ cellQuarterEnergy hq k t w (sample a) p r) P) :
    avsum (alignedIndex q k s)
        (fun w ↦ profileRowCellEnergy P hq k s t w sample p r ^ 2) =
      ∫ a, responseJ (adaptedDomain hq t)
        ((sample a).coeffOn (adaptedDomain hq t)) p r ∂P := by
  classical
  have hsq : ∀ w ∈ alignedIndex q k s,
      profileRowCellEnergy P hq k s t w sample p r ^ 2 =
        avsum (alignedIndex q s t) (fun z ↦
          profileAnnealedCellEnergySq P hq k t
            (nestedLabel k s z w) sample p r) := by
    intro w hw
    rw [profileRowCellEnergy]
    refine Real.sq_sqrt (avsum_nonneg fun z hz ↦ ?_)
    exact hnonneg _ (hnestMem w hw z hz)
  have hcongr :
      avsum (alignedIndex q k s)
          (fun w ↦ profileRowCellEnergy P hq k s t w sample p r ^ 2) =
        avsum (alignedIndex q k s) (fun w ↦
          avsum (alignedIndex q s t) (fun z ↦
            profileAnnealedCellEnergySq P hq k t
              (nestedLabel k s z w) sample p r)) := by
    rw [avsum_eq, avsum_eq]
    exact congrArg _ (Finset.sum_congr rfl hsq)
  rw [hcongr,
    hnest (fun v ↦ profileAnnealedCellEnergySq P hq k t v sample p r)]
  exact avsum_profileAnnealedCellEnergySq_eq P hq (hks.trans hst) sample p r hint

/-! ## The row closers' per-scale energy premise -/

/-- **The per-scale energy premise of the row closers.**  At the annealed row
cell energies the premise holds with equality at the annealed terminal response
root. -/
theorem sqrt_avsum_sq_profileRowCellEnergy_le
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) (Klo s t : ℤ)
    (hst : s ≤ t) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hnonneg : ∀ k ∈ Finset.Icc Klo s, ∀ w ∈ alignedIndex q k t,
      0 ≤ profileAnnealedCellEnergySq P hq k t w sample p r)
    (hnestMem : ∀ k ∈ Finset.Icc Klo s, ∀ w ∈ alignedIndex q k s,
      ∀ z ∈ alignedIndex q s t, nestedLabel k s z w ∈ alignedIndex q k t)
    (hnest : ∀ k ∈ Finset.Icc Klo s, ∀ f : (Fin d → ℤ) → ℝ,
      avsum (alignedIndex q k s) (fun w ↦
          avsum (alignedIndex q s t) (fun z ↦ f (nestedLabel k s z w))) =
        avsum (alignedIndex q k t) f)
    (hint : ∀ k ∈ Finset.Icc Klo s, ∀ w ∈ alignedIndex q k t,
      Integrable (fun a ↦ cellQuarterEnergy hq k t w (sample a) p r) P) :
    ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦
          profileRowCellEnergy P hq k s t w sample p r ^ 2)) ≤
        Real.sqrt (∫ a, responseJ (adaptedDomain hq t)
          ((sample a).coeffOn (adaptedDomain hq t)) p r ∂P) := by
  intro k hk
  have hks : k ≤ s := (Finset.mem_Icc.mp hk).2
  rw [avsum_sq_profileRowCellEnergy_eq P hq hks hst sample p r
    (hnonneg k hk) (hnestMem k hk) (hnest k hk) (hint k hk)]

/-- The coefficient-transpose form of the per-scale energy premise: the
transposed sample carries the adjoint optimizer state and the adjoint terminal
response. -/
theorem sqrt_avsum_sq_profileRowCellEnergy_adjoint_le
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) (Klo s t : ℤ)
    (hst : s ≤ t) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hnonneg : ∀ k ∈ Finset.Icc Klo s, ∀ w ∈ alignedIndex q k t,
      0 ≤ profileAnnealedCellEnergySq P hq k t w
        (fun a ↦ (sample a).transpose) p r)
    (hnestMem : ∀ k ∈ Finset.Icc Klo s, ∀ w ∈ alignedIndex q k s,
      ∀ z ∈ alignedIndex q s t, nestedLabel k s z w ∈ alignedIndex q k t)
    (hnest : ∀ k ∈ Finset.Icc Klo s, ∀ f : (Fin d → ℤ) → ℝ,
      avsum (alignedIndex q k s) (fun w ↦
          avsum (alignedIndex q s t) (fun z ↦ f (nestedLabel k s z w))) =
        avsum (alignedIndex q k t) f)
    (hint : ∀ k ∈ Finset.Icc Klo s, ∀ w ∈ alignedIndex q k t,
      Integrable (fun a ↦ cellQuarterEnergy hq k t w
        ((sample a).transpose) p r) P) :
    ∀ k ∈ Finset.Icc Klo s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦
          profileRowCellEnergy P hq k s t w
            (fun a ↦ (sample a).transpose) p r ^ 2)) ≤
        Real.sqrt (∫ a, responseJ (adaptedDomain hq t)
          ((sample a).transpose.coeffOn (adaptedDomain hq t)) p r ∂P) :=
  sqrt_avsum_sq_profileRowCellEnergy_le P hq Klo s t hst
    (fun a ↦ (sample a).transpose) p r hnonneg hnestMem hnest hint

end

end HCPolySupport.HighContrast.Response
