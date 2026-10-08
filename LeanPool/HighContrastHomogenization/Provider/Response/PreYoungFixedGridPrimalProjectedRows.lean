/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungPrimalFluxProjectedRowBound
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridNestedRows

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridPrimalProjectedRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite projected primal rows, fixed grid

Fixed-rounded-grid sibling of `HCPoly.Provider.Response.PreYoungPrimalProjectedRowBound`,
`HCPoly.Provider.Response.PreYoungPrimalFluxProjectedRowBound`: the grid stays rounded at the
fixed
alignment `l` while the generation window `{s, t}` moves, the aligned-cell
integrability coming from the `AlignedCellsIntegrable` carrier instead of the
window multiplier's carrier equality.  The proof is unchanged apart from the
window bundle replaced by the carrier.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory _root_.Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A finite projected primal oscillation is integrable, and its expected
absolute value is bounded by the corresponding finite weighted row. -/
theorem integrable_primal_projected_oscillation_and_integral_abs_le_scale_rows
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (N : ℕ) :
    Integrable (primalProjectedOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Qcen N) P ∧
    (∫ a, |primalProjectedOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Qcen N a| ∂P) ≤
      adaptedCutoffDerivativeCoeff d *
        (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
          ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
            (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
              avsum (alignedIndex q k s) (fun w ↦
                profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid)
                    k s t w (fun a ↦ a.subSkew g hg) p r *
                  profileSchurLoadFlux
                    (profileHattedBlock g
                      (annealedBlock P (adaptedCellAt q k w))) Qcen) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let kOf : ℕ → ℤ := fun j ↦ s - ((j + 1 : ℕ) : ℤ)
  let energy : ℤ → (Fin d → ℤ) → ℝ := fun k w ↦
    profileRowCellEnergy P hq k s t w (fun a ↦ a.subSkew g hg) p r
  let load : ℤ → (Fin d → ℤ) → ℝ := fun k w ↦
    profileSchurLoadFlux
      (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Qcen
  let row : ℤ → ℝ := fun k ↦
    avsum (alignedIndex q k s) (fun w ↦ energy k w * load k w)
  let pair : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → CoeffSpace d → ℝ :=
    fun j z w a ↦ |vecDot Qcen
      (blockCellAverage (adaptedCellAt q (kOf j)
        (nestedLabel (kOf j) s z w))
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1|
  let depth : ℕ → CoeffSpace d → ℝ := fun j a ↦
    avsum Z (fun z ↦
      avsum (alignedIndex q (kOf j) s) (fun w ↦ pair j z w a))
  let coeff : ℕ → ℝ := fun j ↦
    32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
      (3 : ℝ) ^ (-((t - s) + (j : ℤ)))
  let rhs : CoeffSpace d → ℝ := fun a ↦
    ∑ j ∈ Finset.range N, coeff j * depth j a
  let projected : CoeffSpace d → ℝ :=
    primalProjectedOscillation hq s t g hg p r Qcen N
  have hkOfs : ∀ j, kOf j ≤ s := fun j ↦ by
    dsimp only [kOf]
    omega
  have hmem : ∀ j, ∀ z ∈ Z, ∀ w ∈ alignedIndex q (kOf j) s,
      nestedLabel (kOf j) s z w ∈ alignedIndex q (kOf j) t := by
    intro j z hz w hw
    exact nestedLabel_mem_alignedIndex hq (hkOfs j) hst hw hz
  have hintPair : ∀ j, ∀ z ∈ Z, ∀ w ∈ alignedIndex q (kOf j) s,
      Integrable (pair j z w) P := by
    intro j z hz w hw
    simpa only [pair] using
      integrable_abs_primal_cell_pairing_of_weak
        hq hm0 ((hkOfs j).trans hst) (hmem j z hz w hw)
          g hg p r Qcen hweak
  have hintDepth : ∀ j, Integrable (depth j) P := by
    intro j
    dsimp only [depth]
    exact (integrable_finsetSum Z fun z hz ↦
      (integrable_finsetSum (alignedIndex q (kOf j) s) fun w hw ↦
        hintPair j z hz w hw).const_mul _).const_mul _
  have hcoeff : ∀ j, 0 ≤ coeff j := by
    intro j
    dsimp only [coeff]
    exact mul_nonneg
      (mul_nonneg (by positivity) smoothTransitionProfile.derivBound_nonneg)
      (zpow_nonneg (by norm_num) _)
  have hdepth : ∀ j a, 0 ≤ depth j a := by
    intro j a
    dsimp only [depth]
    exact avsum_nonneg fun z hz ↦
      avsum_nonneg fun w hw ↦ abs_nonneg _
  have hrhs : ∀ a, 0 ≤ rhs a := by
    intro a
    dsimp only [rhs]
    exact Finset.sum_nonneg fun j hj ↦ mul_nonneg (hcoeff j) (hdepth j a)
  have hintRhs : Integrable rhs P := by
    dsimp only [rhs]
    exact integrable_finsetSum (Finset.range N) fun j hj ↦
      (hintDepth j).const_mul (coeff j)
  have hpath : ∀ a, |projected a| ≤ rhs a := by
    intro a
    simpa only [projected, rhs, coeff, depth, pair, Z, kOf, hq] using
      abs_primal_projected_oscillation_le_nested_depth_sum
        hq hst g hg p r Qcen N a
  have hprojectedMeas : AEStronglyMeasurable projected P := by
    simpa only [projected] using
      aestrongly_measurable_primal_projected_oscillation
        (P := P) hq hst g hg p r Qcen N
  have hintProjected : Integrable projected P := by
    refine Integrable.mono' hintRhs hprojectedMeas
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hrhs a)] using hpath a
  have hmono : (∫ a, |projected a| ∂P) ≤ ∫ a, rhs a ∂P :=
    integral_mono hintProjected.norm hintRhs hpath
  have hrowBound : ∀ j,
      (∫ a, depth j a ∂P) ≤ 2 * row (kOf j) := by
    intro j
    simpa only [depth, pair, row, energy, load, Z, kOf, hq] using
      integral_double_avsum_le_of_half_integral_row_bounds
        Z (alignedIndex q (kOf j) s) (pair j)
        (energy (kOf j)) (load (kOf j))
        (hintPair j) (fun w hw ↦
          (nestedAnnealedCellPairings_primal_le_of_cells
            hstat hgrid hls hst hcells hblocks
              (hkOfs j) hw g hg p r Pcen Qcen).1)
  have hrhsIntegral : (∫ a, rhs a ∂P) ≤
      ∑ j ∈ Finset.range N, coeff j * (2 * row (kOf j)) := by
    calc
      (∫ a, rhs a ∂P) =
          ∑ j ∈ Finset.range N, ∫ a, coeff j * depth j a ∂P := by
        dsimp only [rhs]
        rw [integral_finsetSum]
        exact fun j hj ↦ (hintDepth j).const_mul (coeff j)
      _ = ∑ j ∈ Finset.range N,
          coeff j * ∫ a, depth j a ∂P := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      _ ≤ ∑ j ∈ Finset.range N, coeff j * (2 * row (kOf j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hrowBound j) (hcoeff j)
  have hreindex := sum_sharp_depth_rows_le_scale_rows
    (d := d) s t N row (fun k ↦ avsum_nonneg fun w hw ↦
      mul_nonneg (profileRowCellEnergy_nonneg P hq k s t w
        (fun a ↦ a.subSkew g hg) p r) (profileSchurLoadFlux_nonneg _ _))
  constructor
  · simpa only [projected] using hintProjected
  · calc
      (∫ a, |primalProjectedOscillation hq s t g hg p r Qcen N a| ∂P) =
          ∫ a, |projected a| ∂P := by rfl
      _ ≤ ∫ a, rhs a ∂P := hmono
      _ ≤ ∑ j ∈ Finset.range N, coeff j * (2 * row (kOf j)) := hrhsIntegral
      _ ≤ adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
            ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
              (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * row k := by
        simpa only [coeff, kOf] using hreindex
      _ = _ := by rfl

/-- The absolute lower integral of every finite primal projection has a common
bound by the all-earlier hatted row. -/
theorem lintegral_primal_projected_oscillation_le_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (N : ℕ) :
    (∫⁻ a, ENNReal.ofReal |primalProjectedOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Qcen N a| ∂P) ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let sample : CoeffSpace d → CoeffSpace d := fun a ↦ a.subSkew g hg
  let energy : ℤ → (Fin d → ℤ) → ℝ := fun k w ↦
    profileRowCellEnergy P hq k s t w sample p r
  let EJ : ℝ := ∫ a, responseJ (adaptedDomain hq t)
    ((sample a).coeffOn (adaptedDomain hq t)) p r ∂P
  let projected : CoeffSpace d → ℝ :=
    primalProjectedOscillation hq s t g hg p r Qcen N
  have hbase :=
    integrable_primal_projected_oscillation_and_integral_abs_le_scale_rows
      hstat hm0 hgrid hls hst hcells hblocks
        g hg p r Pcen Qcen hweak N
  have hintt : HasFiniteAdaptedMean P q t :=
    (hblocks t (hls.trans hst) le_rfl).1
  have henergyBound : ∀ k ∈ Finset.Icc (s - (N : ℤ)) s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤
        Real.sqrt EJ := by
    simpa only [energy, EJ, sample] using
      sqrt_avsum_sq_profileRowCellEnergy_le P hq (s - (N : ℤ)) s t hst
        sample p r
        (fun k hk w hw ↦
          profileAnnealedCellEnergySq_nonneg P hq k t w sample p r)
        (fun k hk w hw z hz ↦
          nestedLabel_mem_alignedIndex hq (Finset.mem_Icc.mp hk).2 hst hw hz)
        (fun k hk f ↦
          avsum_nestedLabel_alignedIndex hq (Finset.mem_Icc.mp hk).2 hst f)
        (fun k hk w hw ↦
          integrable_cellQuarterEnergy_subSkew_of_finiteAdaptedMean
            hq ((Finset.mem_Icc.mp hk).2.trans hst) hw hintt g hg p r)
  have hCd : 0 ≤ adaptedCutoffDerivativeCoeff d *
      (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) :=
    mul_nonneg (adaptedCutoffDerivativeCoeff_nonneg d)
      (Real.rpow_nonneg (by norm_num) _)
  have hT : |∫ a, |projected a| ∂P| ≤
      (adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ)))) *
        ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
          (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
            avsum (alignedIndex q k s) (fun w ↦ energy k w *
              profileSchurLoadFlux
                (profileHattedBlock g
                  (annealedBlock P (adaptedCellAt q k w))) Qcen) := by
    rw [abs_of_nonneg (integral_nonneg fun a ↦ abs_nonneg (projected a))]
    simpa only [projected, energy, sample, hq] using hbase.2
  have hraw := ofReal_abs_scaleSum_flux_le_mul_profilePrimalHattedEarlierRow_rpow
    P q g (s - (N : ℤ)) s Pcen Qcen energy
    (hSE := Real.sqrt_nonneg EJ) hCd henergyBound hT
  have hcoef :
      adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
        Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * Real.sqrt EJ =
      preYoungRowCoefficient d *
        (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) * Real.sqrt EJ := by
    rw [preYoungRowCoefficient]
    ring
  rw [abs_of_nonneg (integral_nonneg fun a ↦ abs_nonneg (projected a)),
    hcoef] at hraw
  calc
    (∫⁻ a, ENNReal.ofReal |primalProjectedOscillation
        hq s t g hg p r Qcen N a| ∂P) =
      ENNReal.ofReal (∫ a, |projected a| ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hbase.1.norm
          (_root_.Filter.Eventually.of_forall fun a ↦ abs_nonneg (projected a))
    _ ≤ ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) * Real.sqrt EJ) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := hraw
    _ = _ := by rfl

/-- A finite projected primal flux oscillation is integrable, and its expected
absolute value is bounded by the corresponding finite weighted row. -/
theorem integrable_primal_flux_projected_oscillation_and_integral_abs_le_scale_rows
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (N : ℕ) :
    Integrable (primalFluxProjectedOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Pcen N) P ∧
    (∫ a, |primalFluxProjectedOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Pcen N a| ∂P) ≤
      adaptedCutoffDerivativeCoeff d *
        (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
          ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
            (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
              avsum (alignedIndex q k s) (fun w ↦
                profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid)
                    k s t w (fun a ↦ a.subSkew g hg) p r *
                  profileSchurLoadGradient
                    (profileHattedBlock g
                      (annealedBlock P (adaptedCellAt q k w))) Pcen) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let kOf : ℕ → ℤ := fun j ↦ s - ((j + 1 : ℕ) : ℤ)
  let energy : ℤ → (Fin d → ℤ) → ℝ := fun k w ↦
    profileRowCellEnergy P hq k s t w (fun a ↦ a.subSkew g hg) p r
  let load : ℤ → (Fin d → ℤ) → ℝ := fun k w ↦
    profileSchurLoadGradient
      (profileHattedBlock g (annealedBlock P (adaptedCellAt q k w))) Pcen
  let row : ℤ → ℝ := fun k ↦
    avsum (alignedIndex q k s) (fun w ↦ energy k w * load k w)
  let pair : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → CoeffSpace d → ℝ :=
    fun j z w a ↦ |vecDot Pcen
      (blockCellAverage (adaptedCellAt q (kOf j)
        (nestedLabel (kOf j) s z w))
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2|
  let depth : ℕ → CoeffSpace d → ℝ := fun j a ↦
    avsum Z (fun z ↦
      avsum (alignedIndex q (kOf j) s) (fun w ↦ pair j z w a))
  let coeff : ℕ → ℝ := fun j ↦
    32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
      (3 : ℝ) ^ (-((t - s) + (j : ℤ)))
  let rhs : CoeffSpace d → ℝ := fun a ↦
    ∑ j ∈ Finset.range N, coeff j * depth j a
  let projected : CoeffSpace d → ℝ :=
    primalFluxProjectedOscillation hq s t g hg p r Pcen N
  have hkOfs : ∀ j, kOf j ≤ s := fun j ↦ by
    dsimp only [kOf]
    omega
  have hmem : ∀ j, ∀ z ∈ Z, ∀ w ∈ alignedIndex q (kOf j) s,
      nestedLabel (kOf j) s z w ∈ alignedIndex q (kOf j) t := by
    intro j z hz w hw
    exact nestedLabel_mem_alignedIndex hq (hkOfs j) hst hw hz
  have hintPair : ∀ j, ∀ z ∈ Z, ∀ w ∈ alignedIndex q (kOf j) s,
      Integrable (pair j z w) P := by
    intro j z hz w hw
    simpa only [pair] using
      integrable_abs_primal_flux_cell_pairing_of_weak
        hq hm0 ((hkOfs j).trans hst) (hmem j z hz w hw)
          g hg p r Pcen hweak
  have hintDepth : ∀ j, Integrable (depth j) P := by
    intro j
    dsimp only [depth]
    exact (integrable_finsetSum Z fun z hz ↦
      (integrable_finsetSum (alignedIndex q (kOf j) s) fun w hw ↦
        hintPair j z hz w hw).const_mul _).const_mul _
  have hcoeff : ∀ j, 0 ≤ coeff j := by
    intro j
    dsimp only [coeff]
    exact mul_nonneg
      (mul_nonneg (by positivity) smoothTransitionProfile.derivBound_nonneg)
      (zpow_nonneg (by norm_num) _)
  have hdepth : ∀ j a, 0 ≤ depth j a := by
    intro j a
    dsimp only [depth]
    exact avsum_nonneg fun z hz ↦
      avsum_nonneg fun w hw ↦ abs_nonneg _
  have hrhs : ∀ a, 0 ≤ rhs a := by
    intro a
    dsimp only [rhs]
    exact Finset.sum_nonneg fun j hj ↦ mul_nonneg (hcoeff j) (hdepth j a)
  have hintRhs : Integrable rhs P := by
    dsimp only [rhs]
    exact integrable_finsetSum (Finset.range N) fun j hj ↦
      (hintDepth j).const_mul (coeff j)
  have hpath : ∀ a, |projected a| ≤ rhs a := by
    intro a
    simpa only [projected, rhs, coeff, depth, pair, Z, kOf, hq] using
      abs_primal_flux_projected_oscillation_le_nested_depth_sum
        hq hst g hg p r Pcen N a
  have hprojectedMeas : AEStronglyMeasurable projected P := by
    simpa only [projected] using
      aestrongly_measurable_primal_flux_projected_oscillation
        (P := P) hq hst g hg p r Pcen N
  have hintProjected : Integrable projected P := by
    refine Integrable.mono' hintRhs hprojectedMeas
      (_root_.Filter.Eventually.of_forall fun a ↦ ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hrhs a)] using hpath a
  have hmono : (∫ a, |projected a| ∂P) ≤ ∫ a, rhs a ∂P :=
    integral_mono hintProjected.norm hintRhs hpath
  have hrowBound : ∀ j,
      (∫ a, depth j a ∂P) ≤ 2 * row (kOf j) := by
    intro j
    simpa only [depth, pair, row, energy, load, Z, kOf, hq] using
      integral_double_avsum_le_of_half_integral_row_bounds
        Z (alignedIndex q (kOf j) s) (pair j)
        (energy (kOf j)) (load (kOf j))
        (hintPair j) (fun w hw ↦
          (nestedAnnealedCellPairings_primal_le_of_cells
            hstat hgrid hls hst hcells hblocks
              (hkOfs j) hw g hg p r Pcen Qcen).2)
  have hrhsIntegral : (∫ a, rhs a ∂P) ≤
      ∑ j ∈ Finset.range N, coeff j * (2 * row (kOf j)) := by
    calc
      (∫ a, rhs a ∂P) =
          ∑ j ∈ Finset.range N, ∫ a, coeff j * depth j a ∂P := by
        dsimp only [rhs]
        rw [integral_finsetSum]
        exact fun j hj ↦ (hintDepth j).const_mul (coeff j)
      _ = ∑ j ∈ Finset.range N,
          coeff j * ∫ a, depth j a ∂P := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      _ ≤ ∑ j ∈ Finset.range N, coeff j * (2 * row (kOf j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hrowBound j) (hcoeff j)
  have hreindex := sum_sharp_depth_rows_le_scale_rows
    (d := d) s t N row (fun k ↦ avsum_nonneg fun w hw ↦
      mul_nonneg (profileRowCellEnergy_nonneg P hq k s t w
        (fun a ↦ a.subSkew g hg) p r) (profileSchurLoadGradient_nonneg _ _))
  constructor
  · simpa only [projected] using hintProjected
  · calc
      (∫ a, |primalFluxProjectedOscillation
          hq s t g hg p r Pcen N a| ∂P) =
          ∫ a, |projected a| ∂P := by rfl
      _ ≤ ∫ a, rhs a ∂P := hmono
      _ ≤ ∑ j ∈ Finset.range N, coeff j * (2 * row (kOf j)) := hrhsIntegral
      _ ≤ adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
            ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
              (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) * row k := by
        simpa only [coeff, kOf] using hreindex
      _ = _ := by rfl

/-- The absolute lower integral of every finite primal flux projection has a
common bound by the all-earlier hatted row. -/
theorem lintegral_primal_flux_projected_oscillation_le_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤)
    (N : ℕ) :
    (∫⁻ a, ENNReal.ofReal |primalFluxProjectedOscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Pcen N a| ∂P) ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let sample : CoeffSpace d → CoeffSpace d := fun a ↦ a.subSkew g hg
  let energy : ℤ → (Fin d → ℤ) → ℝ := fun k w ↦
    profileRowCellEnergy P hq k s t w sample p r
  let EJ : ℝ := ∫ a, responseJ (adaptedDomain hq t)
    ((sample a).coeffOn (adaptedDomain hq t)) p r ∂P
  let projected : CoeffSpace d → ℝ :=
    primalFluxProjectedOscillation hq s t g hg p r Pcen N
  have hbase :=
    integrable_primal_flux_projected_oscillation_and_integral_abs_le_scale_rows
      hstat hm0 hgrid hls hst hcells hblocks
        g hg p r Pcen Qcen hweak N
  have hintt : HasFiniteAdaptedMean P q t :=
    (hblocks t (hls.trans hst) le_rfl).1
  have henergyBound : ∀ k ∈ Finset.Icc (s - (N : ℤ)) s,
      Real.sqrt (avsum (alignedIndex q k s) (fun w ↦ energy k w ^ 2)) ≤
        Real.sqrt EJ := by
    simpa only [energy, EJ, sample] using
      sqrt_avsum_sq_profileRowCellEnergy_le P hq (s - (N : ℤ)) s t hst
        sample p r
        (fun k hk w hw ↦
          profileAnnealedCellEnergySq_nonneg P hq k t w sample p r)
        (fun k hk w hw z hz ↦
          nestedLabel_mem_alignedIndex hq (Finset.mem_Icc.mp hk).2 hst hw hz)
        (fun k hk f ↦
          avsum_nestedLabel_alignedIndex hq (Finset.mem_Icc.mp hk).2 hst f)
        (fun k hk w hw ↦
          integrable_cellQuarterEnergy_subSkew_of_finiteAdaptedMean
            hq ((Finset.mem_Icc.mp hk).2.trans hst) hw hintt g hg p r)
  have hCd : 0 ≤ adaptedCutoffDerivativeCoeff d *
      (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) :=
    mul_nonneg (adaptedCutoffDerivativeCoeff_nonneg d)
      (Real.rpow_nonneg (by norm_num) _)
  have hT : |∫ a, |projected a| ∂P| ≤
      (adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ)))) *
        ∑ k ∈ Finset.Icc (s - (N : ℤ)) s,
          (3 : ℝ) ^ ((k : ℝ) - (s : ℝ)) *
            avsum (alignedIndex q k s) (fun w ↦ energy k w *
              profileSchurLoadGradient
                (profileHattedBlock g
                  (annealedBlock P (adaptedCellAt q k w))) Pcen) := by
    rw [abs_of_nonneg (integral_nonneg fun a ↦ abs_nonneg (projected a))]
    simpa only [projected, energy, sample, hq] using hbase.2
  have hraw :=
    ofReal_abs_scaleSum_gradient_le_mul_profilePrimalHattedEarlierRow_rpow
      P q g (s - (N : ℤ)) s Pcen Qcen energy
      (hSE := Real.sqrt_nonneg EJ) hCd henergyBound hT
  have hcoef :
      adaptedCutoffDerivativeCoeff d *
          (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
        Real.sqrt (1 / (1 - (3 : ℝ) ^ (-(1 / 2) : ℝ))) * Real.sqrt EJ =
      preYoungRowCoefficient d *
        (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) * Real.sqrt EJ := by
    rw [preYoungRowCoefficient]
    ring
  rw [abs_of_nonneg (integral_nonneg fun a ↦ abs_nonneg (projected a)),
    hcoef] at hraw
  calc
    (∫⁻ a, ENNReal.ofReal |primalFluxProjectedOscillation
        hq s t g hg p r Pcen N a| ∂P) =
      ENNReal.ofReal (∫ a, |projected a| ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hbase.1.norm
          (_root_.Filter.Eventually.of_forall fun a ↦ abs_nonneg (projected a))
    _ ≤ ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) * Real.sqrt EJ) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := hraw
    _ = _ := by rfl

end

end HCPolySupport.HighContrast.Response.FixedGrid
