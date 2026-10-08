/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoarseExcessMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.PhysicalScaleBlockRow
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGridCount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedBadEvent
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.BlockExcessHomogenizationError
public import LeanPool.HighContrastHomogenization.Provider.Quenched.RowTailSumConstruction

/-!
# High-contrast homogenization: Provider.Quenched.EndpointRelativeBlockRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Structural properties of the endpoint-relative block row

The quenched replay uses the same spatial row after changing to the units of
the annealed endpoint.  This file supplies the structural facts about that row:
measurability, nonnegativity, pointwise summability, and a measurable weighted
tail representative.  The quantitative decay is kept separate.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory
open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- Flooring the source scale at one does not change a row indexed by a
natural generation. -/
theorem quenched_block_row_max_one_source
    (rho : ℝ) (F : BlockMat d) (sourceScale : ℝ)
    (a : CoeffSpace d) (m : ℕ) :
    quenchedBlockRow rho F (max 1 sourceScale) a m =
      quenchedBlockRow rho F sourceScale a m := by
  unfold quenchedBlockRow
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  rw [if_congr (max_le_iff.trans (and_iff_right hone)) rfl rfl]

/-- Excess values over standard cells at relative generation `m - n` whose centers lie in the
centered cube of generation `m`. -/
@[expose]
public def endpointCellExcessSet (m n : ℕ) (a : CoeffSpace d)
    (F : BlockMat d) : Set ℝ :=
  {r : ℝ | ∃ w : Fin d → ℤ,
    standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) ∧
    r = blockExcess
      (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F}

/-- Supremum of the excess values in `endpointCellExcessSet m n a F`. -/
@[expose]
public def endpointCellExcessSup (m n : ℕ) (a : CoeffSpace d)
    (F : BlockMat d) : ℝ :=
  sSup (endpointCellExcessSet m n a F)

private theorem endpointCellExcessSup_eq_finsetSupReal
    (m n : ℕ) (a : CoeffSpace d) (F : BlockMat d) :
    endpointCellExcessSup m n a F =
      finsetSupReal (centredIndexFinset d ((m : ℤ) - (n : ℤ)) (m : ℤ))
        (fun w => blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F) := by
  unfold endpointCellExcessSup endpointCellExcessSet finsetSupReal
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    exact (mem_centredIndexFinset_iff (by omega)).2 hw
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, ?_, rfl⟩
    exact (mem_centredIndexFinset_iff (by omega)).1 hw

private theorem finsetSupReal_eq_sup' {I : Type*} (s : Finset I)
    (hs : s.Nonempty) (f : I → ℝ) :
    finsetSupReal s f = s.sup' hs f := by
  apply le_antisymm
  · exact finsetSupReal_le s hs (fun x hx => Finset.le_sup' f hx)
  · refine Finset.sup'_le hs f ?_
    intro x hx
    unfold finsetSupReal
    exact le_csSup (((Set.toFinite _).image f).bddAbove) ⟨x, hx, rfl⟩

private theorem measurable_endpointCellExcessSup [NeZero d]
    {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : BlockPosDef F) (m n : ℕ) :
    Measurable fun a : CoeffSpace d => endpointCellExcessSup m n a F := by
  let Z := centredIndexFinset d ((m : ℤ) - (n : ℤ)) (m : ℤ)
  have hZ : Z.Nonempty := centredIndexFinset_nonempty d
    ((m : ℤ) - (n : ℤ)) (m : ℤ)
  rw [show (fun a : CoeffSpace d => endpointCellExcessSup m n a F) =
      fun a => finsetSupReal Z (fun w => blockExcess
        (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F) by
    funext a
    exact endpointCellExcessSup_eq_finsetSupReal m n a F]
  rw [show (fun a : CoeffSpace d => finsetSupReal Z (fun w => blockExcess
      (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F)) =
      Z.sup' hZ (fun w a => blockExcess
        (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F) by
    funext a
    simpa only [Finset.sup'_apply] using
      finsetSupReal_eq_sup' Z hZ (fun w => blockExcess
        (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F)]
  exact Finset.measurable_sup' hZ fun w _ => by
    have hU : IsOpenBoundedConvexDomain
        (standardCell d ((m : ℤ) - (n : ℤ)) w) :=
      isOpenBoundedConvexDomain_openCubeSet _
    have hvol : 0 <
        (volume (standardCell d ((m : ℤ) - (n : ℤ)) w)).toReal := by
      change 0 < (volume (openCubeSet
        (translateCube w (originCube d ((m : ℤ) - (n : ℤ)))))).toReal
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos _
    exact measurable_blockExcess_coarseBlock hU hvol hF hFpd

private theorem exists_uniform_endpointCellExcess_bound [NeZero d]
    (a : CoeffSpace d) {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : BlockPosDef F) {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℤ) (w : Fin d → ℤ),
      standardCell d k w ⊆ S →
        blockExcess (coarseBlock (standardCell d k w) a) F ≤ C := by
  classical
  have honeSymm : symmPart (1 : Mat d) = 1 := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp [symmPart]
    · simp [symmPart, hij, Ne.symm hij]
  obtain ⟨C₀, hC₀, hcell₀⟩ :=
    exists_uniform_standardCell_blockExcess_bound a (1 : Mat d) (by
      simpa only [honeSymm] using Matrix.PosDef.one) hS
  let I : BlockMat d := Book.Ch02.constantBlockMatrix (1 : Mat d)
  let c : ℝ := blockSize I F
  let C : ℝ := (1 + C₀) * c
  have hIsymm : IsSymmetricBlockMat I := by
    simpa only [I, Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff] using
      isSymmetricBlockMat_blockMatrixOfCoeff (1 : Mat d)
  have hIpd : BlockPosDef I := by
    simpa only [I] using
      blockPosDef_constantBlockMatrix_of_posDef_symmPart
        (by simpa only [honeSymm] using Matrix.PosDef.one)
  have hc : 0 ≤ c := PortableHistory.blockSize_nonneg hIsymm hF hFpd
  have hC : 0 ≤ C := mul_nonneg (by linarith only [hC₀]) hc
  refine ⟨C, hC, ?_⟩
  intro k w hsub
  let H := coarseBlock (standardCell d k w) a
  have hHsymm : IsSymmetricBlockMat H := isSymmetricBlockMat_coarseBlock _ a
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have hvol : 0 < (volume (standardCell d k w)).toReal := by
    change 0 < (volume (openCubeSet (translateCube w (originCube d k)))).toReal
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos _
  have hvol0 : volume (standardCell d k w) ≠ 0 := by
    intro hz
    rw [hz] at hvol
    simp at hvol
  have hHps : (toFullBlockMat H).PosSemidef :=
    Transport.posSemidef_toFullBlockMat_coarseBlock hU hvol0 a
  have hsizeI : blockSize H I ≤ 1 + C₀ :=
    (Response.blockSize_le_one_add_blockExcess hHsymm hHps hIsymm hIpd).trans
      (add_le_add_right (hcell₀ k w hsub) 1)
  have hHsize : BlockMatLoewnerLE H (blockScale (blockSize H I) I) := by
    apply blockMatLoewnerLE_of_le
    rw [toFullBlockMat_blockScale]
    exact (PortableHistory.blockSize_sandwich hHsymm hIsymm hIpd).1
  have hHI : BlockMatLoewnerLE H (blockScale (1 + C₀) I) :=
    hHsize.trans (blockMatLoewnerLE_blockScale_mono hsizeI hIpd)
  have hIF : BlockMatLoewnerLE I (blockScale c F) := by
    apply blockMatLoewnerLE_of_le
    rw [toFullBlockMat_blockScale]
    exact (PortableHistory.blockSize_sandwich hIsymm hF hFpd).1
  have hchain : BlockMatLoewnerLE H (blockScale C F) := by
    have hscaled := blockMatLoewnerLE_blockScale_of_le
      (by linarith only [hC₀] : 0 ≤ 1 + C₀) hIF
    have h := hHI.trans hscaled
    simpa only [blockScale_blockScale, C] using h
  have hsize := Transport.blockSize_le_of_blockMatLoewnerLE_blockScale
    hHsymm hHps hF hFpd hC hchain
  exact (Transport.blockExcess_le_blockSize hHsymm hHps hF hFpd).trans hsize

private theorem endpointCellExcessSup_data [NeZero d]
    (m : ℕ) (a : CoeffSpace d) {F : BlockMat d}
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      0 ≤ endpointCellExcessSup m n a F ∧
      endpointCellExcessSup m n a F ≤ C := by
  obtain ⟨C, hC, hcell⟩ := exists_uniform_endpointCellExcess_bound a hF hFpd
    (isBounded_centeredCube d ((m : ℤ) + 1))
  refine ⟨C, hC, ?_⟩
  intro n
  rw [endpointCellExcessSup_eq_finsetSupReal]
  have hZ := centredIndexFinset_nonempty d
    ((m : ℤ) - (n : ℤ)) (m : ℤ)
  constructor
  · exact finsetSupReal_nonneg _ _ fun w _ =>
      standardCell_blockExcess_nonneg a hF hFpd _ w
  · refine finsetSupReal_le _ hZ fun w hw => hcell _ w ?_
    exact standardCell_subset_centeredCube_succ
      ((mem_centredIndexFinset_iff (by omega)).1 hw) (by omega)

/-- Every endpoint-relative block row is nonnegative. -/
theorem quenched_block_row_nonneg [NeZero d]
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    (rho sourceScale : ℝ) (a : CoeffSpace d) (m : ℕ) :
    0 ≤ quenchedBlockRow rho F sourceScale a m := by
  unfold quenchedBlockRow
  split_ifs
  · exact tsum_nonneg fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (endpointCellExcessSup_data m a hF hFpd |>.choose_spec.2 n |>.1)
  · exact le_rfl

/-- The inner spatial series defining an endpoint-relative block row is
summable for every coefficient sample. -/
theorem summable_endpoint_block_row [NeZero d]
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    {rho : ℝ} (hrho : 0 < rho) (a : CoeffSpace d) (m : ℕ) :
    Summable fun n : ℕ => (3 : ℝ) ^ (-rho * (n : ℝ)) *
      sSup {r : ℝ | ∃ w : Fin d → ℤ,
        standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) ∧
        r = blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F} := by
  obtain ⟨C, hC, hdata⟩ := endpointCellExcessSup_data m a hF hFpd
  let r : ℝ := (3 : ℝ) ^ (-rho)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hrho)
  have hfactor : ∀ n : ℕ, (3 : ℝ) ^ (-rho * (n : ℝ)) = r ^ n := by
    intro n
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => C * r ^ n) ?_ ?_
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
  · intro n
    simpa only [endpointCellExcessSup, endpointCellExcessSet] using
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hdata n).1
  · intro n
    rw [hfactor n]
    simpa only [endpointCellExcessSup, endpointCellExcessSet, mul_comm C] using
      mul_le_mul_of_nonneg_left (hdata n).2 (pow_nonneg hr0 n)

/-- A Loewner comparison by a factor at least one bounds the normalized
positive excess by that factor minus one. -/
theorem blockExcess_le_sub_one_of_blockMatLoewnerLE
    {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hHps : (toFullBlockMat H).PosSemidef)
    (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    {s : ℝ} (hs : 1 ≤ s)
    (hHF : BlockMatLoewnerLE H (blockScale s F)) :
    blockExcess H F ≤ s - 1 := by
  have hsize : blockSize H F ≤ s :=
    Transport.blockSize_le_of_blockMatLoewnerLE_blockScale hH hHps hF hFpd
      (zero_le_one.trans hs) hHF
  rw [blockExcess_eq_max_blockSize_sub_one hH hF hFpd hHps]
  exact max_le (by linarith only [hsize]) (by linarith only [hs])

/-- A uniform geometric bound on every cell excess sums to the corresponding
bound for the endpoint-relative block row. -/
theorem quenched_block_row_le_of_cellExcess [NeZero d]
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    {rho gamma D decay sourceScale : ℝ} (hgamma : 0 ≤ gamma)
    (hgap : gamma < rho)
    (hD : 0 ≤ D) (hdecay : 0 ≤ decay) (a : CoeffSpace d) (m : ℕ)
    (hcell : ∀ n : ℕ, ∀ w : Fin d → ℤ,
      standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) →
      blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) F ≤
        D * (3 : ℝ) ^ (gamma * (n : ℝ)) * decay) :
    quenchedBlockRow rho F sourceScale a m ≤
      D * decay * (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹ := by
  let q : ℝ := (3 : ℝ) ^ (-(rho - gamma))
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) by norm_num]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).2 (by linarith only [hgap])
  have hsup : ∀ n : ℕ, endpointCellExcessSup m n a F ≤
      D * (3 : ℝ) ^ (gamma * (n : ℝ)) * decay := by
    intro n
    rw [endpointCellExcessSup_eq_finsetSupReal]
    exact finsetSupReal_le _
      (centredIndexFinset_nonempty d ((m : ℤ) - (n : ℤ)) (m : ℤ))
      fun w hw => hcell n w ((mem_centredIndexFinset_iff (by omega)).1 hw)
  have hterm : ∀ n : ℕ,
      (3 : ℝ) ^ (-rho * (n : ℝ)) * endpointCellExcessSup m n a F ≤
        D * decay * q ^ n := by
    intro n
    have hmul : (3 : ℝ) ^ (-rho * (n : ℝ)) * endpointCellExcessSup m n a F ≤
        (3 : ℝ) ^ (-rho * (n : ℝ)) *
          (D * (3 : ℝ) ^ (gamma * (n : ℝ)) * decay) :=
      mul_le_mul_of_nonneg_left (hsup n) (Real.rpow_nonneg (by norm_num) _)
    refine hmul.trans_eq ?_
    dsimp only [q]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(rho - gamma))) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (3 : ℝ) ^ (-rho * (n : ℝ)) *
          (D * (3 : ℝ) ^ (gamma * (n : ℝ)) * decay) =
        D * decay * ((3 : ℝ) ^ (-rho * (n : ℝ)) *
          (3 : ℝ) ^ (gamma * (n : ℝ))) := by ring_nf
      _ = D * decay * (3 : ℝ) ^
          (-rho * (n : ℝ) + gamma * (n : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = D * decay * (3 : ℝ) ^ (-(rho - gamma) * (n : ℝ)) := by
        congr 2
        ring_nf
  have hleft : Summable fun n : ℕ =>
      (3 : ℝ) ^ (-rho * (n : ℝ)) * endpointCellExcessSup m n a F :=
    summable_endpoint_block_row hF hFpd
      (by linarith only [hgamma, hgap] : 0 < rho) a m
  have hright : Summable fun n : ℕ => D * decay * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hsum := hleft.tsum_le_tsum hterm hright
  have hgeom : ∑' n : ℕ, D * decay * q ^ n = D * decay * (1 - q)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  unfold quenchedBlockRow
  split_ifs
  · simpa only [endpointCellExcessSup, endpointCellExcessSet, hgeom, q] using hsum
  · have hinv0 : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (by linarith only [hq1])
    exact mul_nonneg (mul_nonneg hD hdecay) hinv0

/-- The endpoint-relative block row is measurable in the coefficient sample. -/
theorem measurable_quenched_block_row [NeZero d]
    {F : BlockMat d} (hF : IsSymmetricBlockMat F) (hFpd : BlockPosDef F)
    {sourceScale : CoeffSpace d → ℝ} (hsource : Measurable sourceScale)
    {rho : ℝ} (hrho : 0 < rho) (m : ℕ) :
    Measurable fun a => quenchedBlockRow rho F (sourceScale a) a m := by
  let term : ℕ → CoeffSpace d → ℝ := fun n a =>
    (3 : ℝ) ^ (-rho * (n : ℝ)) * endpointCellExcessSup m n a F
  have hterm : ∀ n, Measurable (term n) := fun n =>
    (measurable_endpointCellExcessSup hF hFpd m n).const_mul _
  have hterm0 : ∀ n a, 0 ≤ term n a := by
    intro n a
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (endpointCellExcessSup_data m a hF hFpd |>.choose_spec.2 n |>.1)
  have hsum : ∀ a, Summable fun n => term n a := by
    intro a
    simpa only [term, endpointCellExcessSup, endpointCellExcessSet] using
      summable_endpoint_block_row hF hFpd hrho a m
  have henn : Measurable fun a => ∑' n, ENNReal.ofReal (term n a) :=
    Measurable.tsum fun n => ENNReal.measurable_ofReal.comp (hterm n)
  have hreal : Measurable fun a => ∑' n, term n a := by
    have heq : (fun a => ∑' n, term n a) =
        fun a => ENNReal.toReal (∑' n, ENNReal.ofReal (term n a)) := by
      funext a
      rw [ENNReal.tsum_toReal_eq (fun n => by
        exact ENNReal.ofReal_ne_top)]
      simp only [ENNReal.toReal_ofReal (hterm0 _ _)]
    rw [heq]
    exact ENNReal.measurable_toReal.comp henn
  have hrow : (fun a => quenchedBlockRow rho F (sourceScale a) a m) =
      fun a => if sourceScale a ≤ (3 : ℝ) ^ m then ∑' n, term n a else 0 := by
    funext a
    unfold quenchedBlockRow
    congr 1
  rw [hrow]
  exact Measurable.ite (measurableSet_le hsource measurable_const) hreal measurable_const

end

end HCPolySupport.HighContrast.Quenched
