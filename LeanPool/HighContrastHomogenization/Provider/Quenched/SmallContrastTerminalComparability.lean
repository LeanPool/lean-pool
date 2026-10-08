/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Reference
public import LeanPool.HighContrastHomogenization.Provider.Sharp.CoarseBlockPositivity

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastTerminalComparability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The terminal reference comparability

The deterministic comparability consumed by the caps: the Dagger reference
is dominated by the terminal adapted mean with the factor
`κ_𝐄 · C(K) · boundaryConst · 3^{gG}`.  The chain is window-free: the
annealed envelope bounds the terminal mean by the scaled reference, the
sharp reverses the order, the annealed block dominates its own sharp, and
the reference is dominated by `κ_𝐄` times its sharp.  This is the
formalizable content of the printed `𝐄`-preliminaries at the terminal
scale.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The zero-aligned cell is the adapted cell itself. -/
theorem adaptedCellAt_zero (q : Mat d) (t : ℤ) :
    adaptedCellAt q t (0 : Fin d → ℤ) = adaptedCell q t := by
  rw [adaptedCellAt]
  have hzero : (3 : ℝ) ^ t •
      matVecMul q (fun i => ((0 : Fin d → ℤ) i : ℝ)) = 0 := by
    have h : (fun i => ((0 : Fin d → ℤ) i : ℝ)) = (0 : Vec d) := by
      funext i
      simp
    rw [h, matVecMul_zero, smul_zero]
  rw [hzero]
  ext x
  simp

/-- **The terminal reference comparability.**  The reference quadratic form
is dominated by `κ_𝐄 · C(K) · boundaryConst · 3^{gG}` times the terminal
mean's quadratic form. -/
theorem terminal_reference_comparability [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (t : ℤ) {G : ℕ} (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hsub : adaptedCell (roundedGrid l n) t ⊆
      centeredCube d (t + (G : ℤ)))
    (hint : HasFiniteAdaptedMean P (roundedGrid l n) t) :
    (1 : ℝ) ≤ kappaRef E *
        (sourceMomentOne K * boundaryConst Cd g n *
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ)))) ∧
    ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kappaRef E *
            (sourceMomentOne K * boundaryConst Cd g n *
              (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ)))) *
          blockVecDot X
            (blockMatVecMul (adaptedMean P (roundedGrid l n) t) X) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g n :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  have hbC1 : 1 ≤ boundaryConst Cd g n :=
    Initialization.one_le_boundaryConst hCd1 hg hn
  have hCK1 : (1 : ℝ) ≤ sourceMomentOne K := one_le_sourceMomentOne
  have h3pos : (0 : ℝ) <
      (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h31 : (1 : ℝ) ≤
      (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ))) := by
    have hG0 : (0 : ℝ) ≤ (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ)) := by
      have hG0' : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg G
      push_cast
      linarith only [hG0']
    exact Real.one_le_rpow (by norm_num) (mul_nonneg hg.1 hG0)
  set c1 : ℝ := sourceMomentOne K * boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ))) with hc1
  have hc11 : 1 ≤ c1 := by
    rw [hc1]
    have h1 : 1 * 1 * 1 ≤ sourceMomentOne K * boundaryConst Cd g n *
        (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (t : ℝ))) := by
      refine mul_le_mul (mul_le_mul hCK1 hbC1 (by norm_num)
        (by linarith only [hCK1])) h31 (by norm_num) ?_
      have := mul_le_mul hCK1 hbC1 (by norm_num : (0:ℝ) ≤ 1)
        (by linarith only [hCK1] : (0:ℝ) ≤ sourceMomentOne K)
      linarith only [this]
    linarith only [h1]
  have hc1pos : 0 < c1 := lt_of_lt_of_le zero_lt_one hc11
  -- the terminal envelope at the zero-aligned cell
  have hcell0 := adaptedCellAt_zero (roundedGrid l n) t
  have hint0 : HasIntegrableCoarseBlock P
      (adaptedCellAt (roundedGrid l n) t (0 : Fin d → ℤ)) := by
    rw [hcell0]
    exact hint
  have hsub0 : adaptedCellAt (roundedGrid l n) t (0 : Fin d → ℤ) ⊆
      centeredCube d (t + (G : ℤ)) := by
    rw [hcell0]
    exact hsub
  have henv := annealedBlock_adaptedCell_le_scaled hd hg hdag hl hCd hn
    hsK t hDelta hsub0 hint0
  rw [hcell0] at henv
  have hmean_env : BlockMatLoewnerLE (adaptedMean P (roundedGrid l n) t)
      (blockScale c1 E) := by
    rw [hc1]
    simpa only [adaptedMean] using henv
  -- symmetry and positivity of the two sides
  have hEsymm := hdag.refBlock_isSymm
  have hEpd := hdag.refBlock_posDef
  have hmeanSymm : IsSymmetricBlockMat (adaptedMean P (roundedGrid l n) t) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P _ t
  have hmeanPd : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid l n) t) :=
    Recurrence.blockPosDef_adaptedMean hq t hint
  have hscaleSymm : IsSymmetricBlockMat (blockScale c1 E) :=
    isSymmetricBlockMat_blockScale c1 hEsymm
  have hscalePd : Book.Ch02.BlockPosDef (blockScale c1 E) :=
    Transport.blockPosDef_blockScale hc1pos hEpd
  -- the sharp chain
  have hanti := blockMatLoewnerLE_blockSharp_of_le hmeanSymm hscaleSymm
    hmeanPd hscalePd hmean_env
  rw [blockSharp_blockScale hEsymm hEpd hc1pos] at hanti
  have hself : BlockMatLoewnerLE
      (blockSharp (adaptedMean P (roundedGrid l n) t))
      (adaptedMean P (roundedGrid l n) t) := by
    simpa only [adaptedMean] using
      Sharp.blockSharp_annealedBlock_le_of_nonempty
        (Recurrence.isOpenBoundedConvexDomain_adaptedCell hq t)
        (Recurrence.adaptedCell_nonempty (roundedGrid l n) t) hint
  have hkR := Initialization.blockMatLoewnerLE_reference_kappaRef_blockSharp hEsymm hEpd
  have hkR1 : 1 ≤ kappaRef E :=
    Initialization.one_le_kappaRef hEsymm hEpd
      (Initialization.blockMatLoewnerLE_blockSharp_reference hdag)
  have hkap1 : (1 : ℝ) ≤ kappaRef E * c1 := by
    have h := mul_le_mul hkR1 hc11 (by norm_num)
      (by linarith only [hkR1])
    linarith only [h]
  refine ⟨hkap1, ?_⟩
  intro X
  have h1 := hkR X
  have h2 := hanti X
  have h3 := hself X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at h1 h2
  have hb : blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
      c1 * blockVecDot X (blockMatVecMul
        (blockSharp (adaptedMean P (roundedGrid l n) t)) X) := by
    have h2' : c1⁻¹ * blockVecDot X (blockMatVecMul (blockSharp E) X) ≤
        blockVecDot X (blockMatVecMul
          (blockSharp (adaptedMean P (roundedGrid l n) t)) X) := by
      linarith only [h2]
    have hmul := mul_le_mul_of_nonneg_left h2' hc1pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc1pos.ne', one_mul] at hmul
  have hkR0 : (0 : ℝ) ≤ kappaRef E := by linarith only [hkR1]
  have hchain : blockVecDot X (blockMatVecMul E X) ≤
      kappaRef E * (c1 * blockVecDot X (blockMatVecMul
        (blockSharp (adaptedMean P (roundedGrid l n) t)) X)) := by
    have h1' : blockVecDot X (blockMatVecMul E X) ≤
        kappaRef E * blockVecDot X (blockMatVecMul (blockSharp E) X) := by
      linarith only [h1]
    exact le_trans h1' (mul_le_mul_of_nonneg_left hb hkR0)
  have hlast : kappaRef E * (c1 * blockVecDot X (blockMatVecMul
      (blockSharp (adaptedMean P (roundedGrid l n) t)) X)) ≤
      kappaRef E * c1 * blockVecDot X
        (blockMatVecMul (adaptedMean P (roundedGrid l n) t) X) := by
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg hkR0 hc1pos.le)
    linarith only [h3]
  exact le_trans hchain hlast

end

end HCPolySupport.HighContrast.Quenched
