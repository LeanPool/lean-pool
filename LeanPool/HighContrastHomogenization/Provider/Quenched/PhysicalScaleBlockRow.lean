/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.PhysicalScaleTransport

/-!
# High-contrast homogenization: Provider.Quenched.PhysicalScaleBlockRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical-scale covariance of the quenched block row

The weighted row of normalized coarse-block excesses is unchanged when the
hatted coefficient and restored source scale are pulled back to the original
sample.  Every inner generation and the outer containing cube shift by the
same restoration depth.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The weighted spatial row of normalized coarse-block excesses at a natural
outer generation.  The source scale is a pointwise scalar so the same row can
be evaluated before or after a change of coefficient coordinates. -/
@[expose]
def quenchedBlockRow (rho : ℝ) (Abar : BlockMat d) (sourceScale : ℝ)
    (a : CoeffSpace d) (m : ℕ) : ℝ :=
  if sourceScale ≤ (3 : ℝ) ^ m then
    ∑' n : ℕ, (3 : ℝ) ^ (-rho * n) *
      sSup {r : ℝ | ∃ w : Fin d → ℤ,
        standardCellCenter ((m : ℤ) - (n : ℤ)) w ∈ centeredCube d (m : ℤ) ∧
        r = blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (n : ℤ)) w) a) Abar}
  else 0

private theorem standardCellCenter_add_nat_mem_centeredCube_add_nat_iff
    (N : ℕ) (k m : ℤ) (w : Fin d → ℤ) :
    standardCellCenter ((N : ℤ) + k) w ∈ centeredCube d ((N : ℤ) + m) ↔
      standardCellCenter k w ∈ centeredCube d m := by
  have hcenter :
      dilateVec (N : ℤ) (standardCellCenter k w) =
        standardCellCenter ((N : ℤ) + k) w := by
    funext i
    simp only [dilateVec, triadicDilationFactor, standardCellCenter,
      Pi.smul_apply, smul_eq_mul]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hcube : dilateCube (N : ℤ) (originCube d m) =
      originCube d ((N : ℤ) + m) := by
    apply congrArg₂ TriadicCube.mk
    · simp [originCube, add_comm]
    · funext i
      simp [originCube]
  constructor
  · intro h
    have hback := dilateVec_mem_openCubeSet_dilateCube (-(N : ℤ)) h
    have hcenterBack :
        dilateVec (-(N : ℤ)) (standardCellCenter ((N : ℤ) + k) w) =
          standardCellCenter k w := by
      rw [← hcenter]
      exact dilateVec_neg_dilateVec (N : ℤ) _
    have hcubeBack :
        dilateCube (-(N : ℤ)) (originCube d ((N : ℤ) + m)) =
          originCube d m := by
      rw [← hcube]
      exact dilateCube_neg_dilateCube (N : ℤ) _
    simpa [centeredCube, hcenterBack, hcubeBack] using hback
  · intro h
    have hforward := dilateVec_mem_openCubeSet_dilateCube (N : ℤ) h
    simpa [centeredCube, hcenter, hcube] using hforward

private theorem restored_source_cutoff_iff
    (N m : ℕ) (sourceScale : ℝ) :
    max 1 (sourceScale / (3 : ℝ) ^ N) ≤ (3 : ℝ) ^ m ↔
      sourceScale ≤ (3 : ℝ) ^ (N + m) := by
  have hN : 0 < (3 : ℝ) ^ N := by positivity
  have hm : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  constructor
  · intro h
    have hdiv : sourceScale / (3 : ℝ) ^ N ≤ (3 : ℝ) ^ m :=
      (le_max_right _ _).trans h
    have hmul := (div_le_iff₀ hN).mp hdiv
    simpa [pow_add, mul_comm] using hmul
  · intro h
    apply max_le hm
    apply (div_le_iff₀ hN).2
    simpa [pow_add, mul_comm] using h

/-- Pulling the hatted row back to the original sample shifts every coarse
generation by `N` and restores the unfloored source scale exactly. -/
theorem quenched_block_row_physical_scale_coeff
    (rho : ℝ) (Abar : BlockMat d) (sourceScale : ℝ)
    (N m : ℕ) (a : CoeffSpace d) :
    quenchedBlockRow rho Abar
        (max 1 (sourceScale / (3 : ℝ) ^ N))
        (physicalScaleCoefficient N a) m =
      quenchedBlockRow rho Abar sourceScale a (N + m) := by
  unfold quenchedBlockRow
  rw [if_congr (restored_source_cutoff_iff N m sourceScale) rfl rfl]
  split_ifs with hcutoff
  · apply tsum_congr
    intro n
    congr 1
    apply congrArg sSup
    ext r
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, ?_, ?_⟩
      · have hmem :=
          (standardCellCenter_add_nat_mem_centeredCube_add_nat_iff
            (d := d) N ((m : ℤ) - (n : ℤ)) (m : ℤ) w).2 hw
        have hscale : ((N + m : ℕ) : ℤ) - (n : ℤ) =
            (N : ℤ) + ((m : ℤ) - (n : ℤ)) := by omega
        have houter : ((N + m : ℕ) : ℤ) = (N : ℤ) + (m : ℤ) := by omega
        rw [hscale, houter]
        exact hmem
      · rw [show ((N + m : ℕ) : ℤ) - (n : ℤ) =
          (N : ℤ) + ((m : ℤ) - (n : ℤ)) by omega]
        exact blockExcess_coarseBlock_standardCell_physical_scale_coeff
          N ((m : ℤ) - (n : ℤ)) w a Abar
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, ?_, ?_⟩
      · apply
          (standardCellCenter_add_nat_mem_centeredCube_add_nat_iff
            (d := d) N ((m : ℤ) - (n : ℤ)) (m : ℤ) w).1
        have hscale : ((N + m : ℕ) : ℤ) - (n : ℤ) =
            (N : ℤ) + ((m : ℤ) - (n : ℤ)) := by omega
        have houter : ((N + m : ℕ) : ℤ) = (N : ℤ) + (m : ℤ) := by omega
        rw [← hscale, ← houter]
        exact hw
      · have hscale : ((N + m : ℕ) : ℤ) - (n : ℤ) =
            (N : ℤ) + ((m : ℤ) - (n : ℤ)) := by omega
        rw [hscale, coarseBlock_standardCell_physical_scale_coeff]
  · rfl

end

end HCPolySupport.HighContrast.Quenched
