/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay
public import LeanPool.HighContrastHomogenization.Provider.Quenched.PhysicalScaleBlockRow

/-!
# High-contrast homogenization: Provider.Quenched.CoupledPhysicalBlockDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical block decay from a coupled mixing scale

The common replay scale uses the selected mixing scale and restored source
from the same sample.  The quotient-dilation identity then turns decay of the
hatted row at generation `m` into decay of the original coefficient at
generation `N + m`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Filter MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The common normalized scale before restoring the annealed dilation. -/
@[expose]
def coupled_normalized_scale
    {P : Measure (CoeffSpace d)} {selectedRow : ℕ → CoeffSpace d → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    (Ssrc : CoeffSpace d → ℝ) (a : CoeffSpace d) : ℝ :=
  W.normalization * max 1 (max (W.scale a) (Ssrc a))

/-- The physical replay length obtained by undoing `N` triadic dilations. -/
@[expose]
def coupled_physical_length
    {P : Measure (CoeffSpace d)} {selectedRow : ℕ → CoeffSpace d → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (N : ℕ)
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta) : ℝ :=
  (3 : ℝ) ^ N * W.normalization

/-- The physical random scale obtained by undoing `N` triadic dilations. -/
@[expose]
def coupled_physical_scale
    {P : Measure (CoeffSpace d)} {selectedRow : ℕ → CoeffSpace d → ℝ}
    {cMix cd eta kappa delta : ℝ}
    (N : ℕ)
    (W : CoupledMixingScaleWitness
      P selectedRow cMix cd eta kappa delta)
    (Ssrc : CoeffSpace d → ℝ) (a : CoeffSpace d) : ℝ :=
  (3 : ℝ) ^ N * coupled_normalized_scale W Ssrc a

/-- Every natural generation above the restored annealed scale has the
source-restricted block-row decay. -/
@[expose]
def HasAllLaterPhysicalBlockRowFromAnnealedScale
    (rho kappa C : ℝ) (Abar : BlockMat d)
    (S : CoeffSpace d → ℝ) (N : ℕ)
    (X : CoeffSpace d → ℝ) (a : CoeffSpace d) : Prop :=
  ∀ m : ℕ, X a ≤ (3 : ℝ) ^ (N + m) →
    quenched_block_row rho Abar (S a) a (N + m) ≤
      C * (((3 : ℝ) ^ (N + m)) / X a) ^ (-kappa)

/-- The physical block row at an integer generation.  Negative generations
are represented by generation zero; when the random scale is at least one,
the defining scale premise makes that branch impossible. -/
@[expose]
def physical_block_row_at_int
    (rho : ℝ) (Abar : BlockMat d) (S : CoeffSpace d → ℝ)
    (a : CoeffSpace d) (m : ℤ) : ℝ :=
  quenched_block_row rho Abar (S a) a m.toNat

/-- Block-row decay at every admissible integer physical generation. -/
@[expose]
def HasAllLaterPhysicalBlockRow
    (rho kappa C : ℝ) (Abar : BlockMat d)
    (S X : CoeffSpace d → ℝ) (a : CoeffSpace d) : Prop :=
  ∀ m : ℤ, X a ≤ (3 : ℝ) ^ m →
    physical_block_row_at_int rho Abar S a m ≤
      C * (((3 : ℝ) ^ m) / X a) ^ (-kappa)

private theorem physical_ratio_eq_normalized_ratio
    (N m : ℕ) {Y : ℝ} (hY : 0 < Y) :
    ((3 : ℝ) ^ (N + m)) / ((3 : ℝ) ^ N * Y) =
      ((3 : ℝ) ^ m) / Y := by
  rw [pow_add]
  field_simp

/-- The a.e. same-witness certificate gives physical all-later block decay.
No decay implication is assumed as part of the coupled witness. -/
theorem CoupledMixingScaleWitness.eventually_hasAllLaterPhysicalBlockRowFromAnnealedScale
    {P : Measure (CoeffSpace d)}
    {cMix cd eta kappa delta rho C : ℝ}
    {Abar : BlockMat d} {S : CoeffSpace d → ℝ} {N : ℕ}
    (W : CoupledMixingScaleWitness P
      (fun m a => quenched_block_row rho Abar
        (max 1 (S a / (3 : ℝ) ^ N)) (physical_scale_coeff N a) m)
      cMix cd eta kappa delta)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (hdeltaC : delta ≤ C) :
    ∀ᵐ a ∂P,
      HasAllLaterPhysicalBlockRowFromAnnealedScale rho kappa C Abar S N
        (coupled_physical_scale N W
          (fun a => max 1 (S a / (3 : ℝ) ^ N))) a := by
  let commonScale : CoeffSpace d → ℝ :=
    fun a => max 1 (max (W.scale a) (max 1 (S a / (3 : ℝ) ^ N)))
  have hone : ∀ a, 1 ≤ commonScale a := fun a => le_max_left _ _
  have hscale : ∀ a, W.scale a ≤ commonScale a := by
    intro a
    exact (le_max_left _ _).trans (le_max_right _ _)
  filter_upwards [W.eventually_row_le_scaled_rpow hkappa hdelta hone hscale]
    with a hrow
  intro m hm
  have hthreeN : 0 < (3 : ℝ) ^ N := by positivity
  have hcommon : 0 < commonScale a :=
    lt_of_lt_of_le zero_lt_one (hone a)
  have hnormalization : 0 < W.normalization :=
    lt_of_lt_of_le zero_lt_one W.one_le_normalization
  have hnormalized : 0 < W.normalization * commonScale a :=
    mul_pos hnormalization hcommon
  have hnormalized_m :
      W.normalization * commonScale a ≤ (3 : ℝ) ^ m := by
    apply le_of_mul_le_mul_left _ hthreeN
    simpa only [coupled_physical_scale, coupled_normalized_scale,
      commonScale, pow_add, mul_assoc] using hm
  have hrowBound := hrow m hnormalized_m
  have hcoefficient :
      delta *
          (((3 : ℝ) ^ m) / (W.normalization * commonScale a)) ^ (-kappa) ≤
        C *
          (((3 : ℝ) ^ m) / (W.normalization * commonScale a)) ^ (-kappa) :=
    mul_le_mul_of_nonneg_right hdeltaC (Real.rpow_nonneg (by positivity) _)
  calc
    quenched_block_row rho Abar (S a) a (N + m) =
        quenched_block_row rho Abar
          (max 1 (S a / (3 : ℝ) ^ N)) (physical_scale_coeff N a) m :=
      (quenched_block_row_physical_scale_coeff rho Abar (S a) N m a).symm
    _ = W.row m a :=
      (W.row_eq_selected m a).symm
    _ ≤ delta *
        (((3 : ℝ) ^ m) / (W.normalization * commonScale a)) ^ (-kappa) :=
      hrowBound
    _ ≤ C *
        (((3 : ℝ) ^ m) / (W.normalization * commonScale a)) ^ (-kappa) :=
      hcoefficient
    _ = C *
        (((3 : ℝ) ^ (N + m)) /
          coupled_physical_scale N W
            (fun x => max 1 (S x / (3 : ℝ) ^ N)) a) ^ (-kappa) := by
      rw [coupled_physical_scale, coupled_normalized_scale]
      rw [physical_ratio_eq_normalized_ratio N m hnormalized]

/-- The natural offset estimate extends to every integer physical generation:
the scale lower bound first forces that generation to lie above `N`. -/
theorem CoupledMixingScaleWitness.eventually_hasAllLaterPhysicalBlockRow
    {P : Measure (CoeffSpace d)}
    {cMix cd eta kappa delta rho C : ℝ}
    {Abar : BlockMat d} {S : CoeffSpace d → ℝ} {N : ℕ}
    (W : CoupledMixingScaleWitness P
      (fun m a => quenched_block_row rho Abar
        (max 1 (S a / (3 : ℝ) ^ N)) (physical_scale_coeff N a) m)
      cMix cd eta kappa delta)
    (hkappa : 0 < kappa) (hdelta : 0 < delta) (hdeltaC : delta ≤ C) :
    ∀ᵐ a ∂P,
      HasAllLaterPhysicalBlockRow rho kappa C Abar S
        (coupled_physical_scale N W
          (fun a => max 1 (S a / (3 : ℝ) ^ N))) a := by
  filter_upwards
    [W.eventually_hasAllLaterPhysicalBlockRowFromAnnealedScale
      hkappa hdelta hdeltaC]
    with a hnatural
  intro M hM
  let Ssrc : CoeffSpace d → ℝ :=
    fun x => max 1 (S x / (3 : ℝ) ^ N)
  have hcommon_one :
      1 ≤ max 1 (max (W.scale a) (Ssrc a)) := le_max_left _ _
  have hnormalized_one :
      1 ≤ coupled_normalized_scale W Ssrc a := by
    exact one_le_mul_of_one_le_of_one_le W.one_le_normalization hcommon_one
  have hX_one : 1 ≤ coupled_physical_scale N W Ssrc a := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      hnormalized_one
  have hN_le_X :
      (3 : ℝ) ^ N ≤ coupled_physical_scale N W Ssrc a := by
    calc
      (3 : ℝ) ^ N = (3 : ℝ) ^ N * 1 := by ring
      _ ≤ (3 : ℝ) ^ N * coupled_normalized_scale W Ssrc a :=
        mul_le_mul_of_nonneg_left hnormalized_one (by positivity)
      _ = coupled_physical_scale N W Ssrc a := rfl
  have hM_nonneg : 0 ≤ M := by
    by_contra hnegative
    have hpow_lt_one : (3 : ℝ) ^ M < 1 :=
      zpow_lt_one_of_neg₀ (by norm_num) (lt_of_not_ge hnegative)
    exact (not_lt_of_ge (hX_one.trans hM)) hpow_lt_one
  have hNMpow : (3 : ℝ) ^ (N : ℤ) ≤ (3 : ℝ) ^ M := by
    simpa only [zpow_natCast] using hN_le_X.trans hM
  have hNM : (N : ℤ) ≤ M :=
    (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hNMpow
  let m : ℕ := (M - (N : ℤ)).toNat
  have hdiff : 0 ≤ M - (N : ℤ) := sub_nonneg.mpr hNM
  have hm_cast : (m : ℤ) = M - (N : ℤ) := by
    simpa only [m] using Int.toNat_of_nonneg hdiff
  have hgeneration : ((N + m : ℕ) : ℤ) = M := by
    push_cast
    omega
  have hpow_generation :
      (3 : ℝ) ^ (N + m) = (3 : ℝ) ^ M := by
    rw [← zpow_natCast]
    rw [hgeneration]
  have hnatural_at_m := hnatural m (hM.trans_eq hpow_generation.symm)
  have hM_toNat : M.toNat = N + m := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg hM_nonneg]
    exact hgeneration.symm
  simpa only [HasAllLaterPhysicalBlockRow,
    physical_block_row_at_int, Ssrc, hM_toNat, hpow_generation] using
    hnatural_at_m

end

end HCPolySupport.HighContrast.Quenched
