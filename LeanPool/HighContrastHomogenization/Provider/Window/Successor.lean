/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellPositivity
public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

/-!
# High-contrast homogenization: Provider.Window.Successor

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The strict successor gives the improved window discount

If the strict successor of the bad scales is at most `3^m`, then scale `m`
itself cannot be bad: otherwise its contribution, multiplied by the strict
factor three, would already exceed `3^m`.  Every entry in the defining
supremum is consequently at most one, which is exactly the printed Loewner
bound after undoing its triadic weight.
-/

namespace HCPolySupport
namespace HighContrast
namespace Window

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- A bound on the strict successor closes the pathwise improved-discount
clause of `e.source.multiplier`. -/
theorem improved_discount_of_successorScale_le
    {P : MeasureTheory.Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M m : ℤ} {a : CoeffSpace d}
    (hsucc : successorScale g E (M - jStar) a ≤ ENNReal.ofReal ((3 : ℝ) ^ m)) :
    ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^
              (g * max ((m : ℝ) - ((M : ℝ) - (jStar : ℝ)) - (k : ℝ)) 0)) E) := by
  have hmpos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hnotbad : ¬badScaleEvent g E (M - jStar) m a := by
    intro hbad
    have hterm : ENNReal.ofReal ((3 : ℝ) ^ m) ≤
        ⨆ (n : ℤ) (_ : badScaleEvent g E (M - jStar) n a),
          ENNReal.ofReal ((3 : ℝ) ^ n) :=
      le_iSup_of_le m (le_iSup_of_le hbad le_rfl)
    have hlarge : (3 : ℝ≥0∞) * ENNReal.ofReal ((3 : ℝ) ^ m) ≤
        successorScale g E (M - jStar) a := by
      simpa only [successorScale] using
        mul_le_mul_of_nonneg_left hterm (by positivity : (0 : ℝ≥0∞) ≤ 3)
    have hcontra : ENNReal.ofReal (3 * (3 : ℝ) ^ m) ≤
        ENNReal.ofReal ((3 : ℝ) ^ m) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      exact hlarge.trans hsucc
    have hreal : 3 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ m :=
      (ENNReal.ofReal_le_ofReal_iff hmpos.le).mp hcontra
    linarith only [hmpos, hreal]
  let F : ℤ → (Fin d → ℤ) → ℝ≥0∞ := fun k w =>
    ENNReal.ofReal
      ((3 : ℝ) ^
          (-g * max ((m : ℝ) - (((M - jStar : ℤ) : ℝ)) - (k : ℝ)) 0) *
        blockSize (coarseBlock (standardCell d k w) a) E)
  have hsup :
      (⨆ (k : ℤ) (_ : k ≤ m) (w : Fin d → ℤ)
          (_ : standardCellCenter k w ∈ centeredCube d m), F k w) ≤ 1 := by
    rw [badScaleEvent] at hnotbad
    simpa only [F] using le_of_not_gt hnotbad
  intro k hk w hw
  have hentryF : F k w ≤ 1 := by
    calc
      F k w ≤ ⨆ (_ : standardCellCenter k w ∈ centeredCube d m), F k w :=
        le_iSup (fun _ : standardCellCenter k w ∈ centeredCube d m => F k w) hw
      _ ≤ ⨆ (w' : Fin d → ℤ)
          (_ : standardCellCenter k w' ∈ centeredCube d m), F k w' :=
        le_iSup (fun w' : Fin d → ℤ =>
          ⨆ (_ : standardCellCenter k w' ∈ centeredCube d m), F k w') w
      _ ≤ ⨆ (_ : k ≤ m) (w' : Fin d → ℤ)
          (_ : standardCellCenter k w' ∈ centeredCube d m), F k w' :=
        le_iSup (fun _ : k ≤ m => ⨆ (w' : Fin d → ℤ)
          (_ : standardCellCenter k w' ∈ centeredCube d m), F k w') hk
      _ ≤ ⨆ (k' : ℤ) (_ : k' ≤ m) (w' : Fin d → ℤ)
          (_ : standardCellCenter k' w' ∈ centeredCube d m), F k' w' :=
        le_iSup (fun k' : ℤ => ⨆ (_ : k' ≤ m) (w' : Fin d → ℤ)
          (_ : standardCellCenter k' w' ∈ centeredCube d m), F k' w') k
      _ ≤ 1 := hsup
  have hentry :
      ENNReal.ofReal
          ((3 : ℝ) ^
              (-g * max ((m : ℝ) - (((M - jStar : ℤ) : ℝ)) - (k : ℝ)) 0) *
            blockSize (coarseBlock (standardCell d k w) a) E) ≤ 1 := by
    simpa only [F] using hentryF
  have hU : IsOpenBoundedConvexDomain (standardCell d k w) :=
    isOpenBoundedConvexDomain_openCubeSet (translateCube w (originCube d k))
  have hne : (standardCell d k w).Nonempty :=
    ⟨standardCellCenter k w, Recurrence.standardCellCenter_mem_standardCell k w⟩
  have hApd : Book.Ch02.BlockPosDef (coarseBlock (standardCell d k w) a) :=
    Recurrence.blockPosDef_coarseBlock_of_isOpenBoundedConvexDomain hU hne a
  have hAsymm : IsSymmetricBlockMat (coarseBlock (standardCell d k w) a) :=
    isSymmetricBlockMat_coarseBlockMatrix _ _
  have hAfull : (toFullBlockMat (coarseBlock (standardCell d k w) a)).PosDef :=
    posDef_toFullBlockMat hAsymm hApd
  have hEfull : (toFullBlockMat E).PosDef :=
    posDef_toFullBlockMat hdag.refBlock_isSymm hdag.refBlock_posDef
  have hsize : blockSize (coarseBlock (standardCell d k w) a) E =
      relSize (toFullBlockMat (coarseBlock (standardCell d k w) a))
        (toFullBlockMat E) :=
    blockSize_eq_relSize hAsymm hdag.refBlock_isSymm hdag.refBlock_posDef
      hAfull.posSemidef
  have hsize0 : 0 ≤ blockSize (coarseBlock (standardCell d k w) a) E := by
    rw [hsize]
    exact relSize_nonneg _ _
  set x : ℝ := g * max
    ((m : ℝ) - (((M - jStar : ℤ) : ℝ)) - (k : ℝ)) 0
  have hfactor : (0 : ℝ) < (3 : ℝ) ^ (-x) := by positivity
  have hweighted : (3 : ℝ) ^ (-x) *
      blockSize (coarseBlock (standardCell d k w) a) E ≤ 1 := by
    apply ENNReal.ofReal_le_one.mp
    simpa only [x, neg_mul] using hentry
  have hcancel : (3 : ℝ) ^ (-x) * (3 : ℝ) ^ x = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    simp
  have hsize_le : blockSize (coarseBlock (standardCell d k w) a) E ≤
      (3 : ℝ) ^ x := by
    calc
      blockSize (coarseBlock (standardCell d k w) a) E
          ≤ 1 / (3 : ℝ) ^ (-x) :=
            (le_div_iff₀ hfactor).2 (by simpa [mul_comm] using hweighted)
      _ = (3 : ℝ) ^ x :=
        ((eq_div_iff hfactor.ne').2 (by simpa [mul_comm] using hcancel)).symm
  have hraw : BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
      (blockScale (blockSize (coarseBlock (standardCell d k w) a) E) E) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, hsize]
    exact le_relSize_smul hAfull.posSemidef hEfull
  have hscale : BlockMatLoewnerLE
      (blockScale (blockSize (coarseBlock (standardCell d k w) a) E) E)
      (blockScale ((3 : ℝ) ^ x) E) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale, toFullBlockMat_blockScale]
    refine Matrix.le_iff.mpr ?_
    have hps := hEfull.posSemidef.smul (sub_nonneg.mpr hsize_le)
    simpa [sub_smul] using hps
  have hfinal := hraw.trans hscale
  simpa only [x, Int.cast_sub] using hfinal

end

end Window
end HighContrast
end HCPolySupport
