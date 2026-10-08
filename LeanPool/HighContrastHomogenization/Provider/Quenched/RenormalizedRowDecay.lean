/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.EndpointRelativeBlockRow
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeReferenceComparison

/-!
# High-contrast homogenization: Provider.Quenched.RenormalizedRowDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Block-row decay below a renormalized stopping radius

The renormalized radius controls the recent cells by an additive comparison.
The original coarse-ellipticity datum controls the older cells, where the
growing window absorbs the reference loss.  Keeping these two cases separate
preserves the small factor that is lost when they are bundled into a new
coarse-ellipticity datum.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A single renormalized window gives a geometrically summable block-row
bound.  The small parameters are kept additive in the conclusion. -/
theorem quenched_block_row_le_of_renormRadius_le [NeZero d]
    {g gamma rho delta eps : ℝ} {E Ahat Abar : BlockMat d}
    {S : CoeffSpace d → ℝ} {n h m : ℕ} {a : CoeffSpace d}
    (hgamma0 : 0 ≤ gamma) (hgr : g ≤ gamma) (hgammaRho : gamma < rho)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1)
    (heps : eps ∈ Set.Icc (0 : ℝ) 1)
    (hAhat : Book.Ch02.BlockPosDef Ahat)
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hAbar : Book.Ch02.BlockPosDef Abar)
    (href : BlockMatLoewnerLE E (blockScale (2 * kappaRef E) Ahat))
    (hcomp : BlockMatLoewnerLE Ahat (blockScale (1 + eps) Abar))
    (hburn : 2 * kappaRef E ≤
      delta * (3 : ℝ) ^ ((gamma - g) * (h : ℝ)))
    (hcoarse : ∀ M : ℤ, S a ≤ (3 : ℝ) ^ M →
      ∀ k : ℤ, k ≤ M → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d M →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale ((3 : ℝ) ^ (g * ((M : ℝ) - (k : ℝ)))) E))
    (hfin : renormScale S Ahat delta gamma h n a ≠ ⊤)
    (hnm : n ≤ m)
    (hradius : renormRadius S Ahat delta gamma h n a ≤ (3 : ℝ) ^ m)
    (hsource : S a ≤ (3 : ℝ) ^ m) :
    quenchedBlockRow rho Abar (S a) a m ≤
      2 * (delta + eps) *
        (1 - (3 : ℝ) ^ (-(rho - gamma)))⁻¹ := by
  have hcell : ∀ r : ℕ, ∀ w : Fin d → ℤ,
      standardCellCenter ((m : ℤ) - (r : ℤ)) w ∈ centeredCube d (m : ℤ) →
      blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (r : ℤ)) w) a) Abar ≤
        2 * (3 : ℝ) ^ (gamma * (r : ℝ)) * (delta + eps) := by
    intro r w hw
    let H := coarseBlock (standardCell d ((m : ℤ) - (r : ℤ)) w) a
    have hHsymm : IsSymmetricBlockMat H := isSymmetricBlockMat_coarseBlock _ a
    have hU : IsOpenBoundedConvexDomain
        (standardCell d ((m : ℤ) - (r : ℤ)) w) :=
      isOpenBoundedConvexDomain_openCubeSet _
    have hvol : 0 <
        (volume (standardCell d ((m : ℤ) - (r : ℤ)) w)).toReal := by
      change 0 < (volume (openCubeSet
        (translateCube w (originCube d ((m : ℤ) - (r : ℤ)))))).toReal
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos _
    have hvol0 : volume (standardCell d ((m : ℤ) - (r : ℤ)) w) ≠ 0 := by
      intro hz
      rw [hz] at hvol
      simp at hvol
    have hHps : (toFullBlockMat H).PosSemidef :=
      Transport.posSemidef_toFullBlockMat_coarseBlock hU hvol0 a
    have hp : 1 ≤ (3 : ℝ) ^ (gamma * (r : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg hgamma0 (Nat.cast_nonneg r))
    by_cases hrecent : (m : ℤ) - (h : ℤ) + 1 ≤ (m : ℤ) - (r : ℤ)
    · have hrow := blockMatLoewnerLE_of_renormRadius_le hfin
        (by exact_mod_cast hnm) hradius hsource ((m : ℤ) - (r : ℤ))
        hrecent (by omega) w hw
      simp only [Int.cast_sub, Int.cast_natCast] at hrow
      have hrCast : (m : ℝ) - ((m : ℝ) - (r : ℝ)) = (r : ℝ) := by ring
      rw [hrCast] at hrow
      have hscaled := blockMatLoewnerLE_blockScale_of_le
        (add_nonneg zero_le_one
          (mul_nonneg hdelta.1 (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3)
            (gamma * (r : ℝ))))) hcomp
      have hchain : BlockMatLoewnerLE H
          (blockScale ((1 + delta * (3 : ℝ) ^ (gamma * (r : ℝ))) *
            (1 + eps)) Abar) := by
        have := hrow.trans hscaled
        simpa only [H, blockScale_blockScale] using this
      have hsone : 1 ≤
          (1 + delta * (3 : ℝ) ^ (gamma * (r : ℝ))) * (1 + eps) := by
        nlinarith only [hp, hdelta.1, heps.1,
          mul_nonneg hdelta.1 (le_trans zero_le_one hp)]
      have hexcess := blockExcess_le_sub_one_of_blockMatLoewnerLE
        hHsymm hHps hAbarSymm hAbar hsone hchain
      have hsmall :
          (1 + delta * (3 : ℝ) ^ (gamma * (r : ℝ))) * (1 + eps) - 1 ≤
            2 * (3 : ℝ) ^ (gamma * (r : ℝ)) * (delta + eps) := by
        have hpn := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3)
          (gamma * (r : ℝ))
        have hde := mul_nonneg hdelta.1 heps.1
        have hdp : 0 ≤ delta * (3 : ℝ) ^ (gamma * (r : ℝ)) :=
          mul_nonneg hdelta.1 hpn
        have hdpe : delta * (3 : ℝ) ^ (gamma * (r : ℝ)) * eps ≤
            delta * (3 : ℝ) ^ (gamma * (r : ℝ)) :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left heps.2 hdp
        nlinarith only [hp, hdelta.1, heps.1, hpn, hde, hdpe]
      exact hexcess.trans hsmall
    · have hrh : (h : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast (show h ≤ r by omega)
      have hold := hcoarse (m : ℤ) hsource ((m : ℤ) - (r : ℤ))
        (by omega) w hw
      simp only [Int.cast_sub, Int.cast_natCast] at hold
      have hrCast : (m : ℝ) - ((m : ℝ) - (r : ℝ)) = (r : ℝ) := by ring
      rw [hrCast] at hold
      have hscaleE := blockMatLoewnerLE_blockScale_of_le
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (g * (r : ℝ))) href
      have hEA : BlockMatLoewnerLE H
          (blockScale ((3 : ℝ) ^ (g * (r : ℝ)) * (2 * kappaRef E)) Ahat) := by
        have := hold.trans hscaleE
        simpa only [H, blockScale_blockScale] using this
      have hgapPow : (3 : ℝ) ^ ((gamma - g) * (h : ℝ)) ≤
          (3 : ℝ) ^ ((gamma - g) * (r : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
          (mul_le_mul_of_nonneg_left hrh (sub_nonneg.mpr hgr))
      have hscalar : (3 : ℝ) ^ (g * (r : ℝ)) * (2 * kappaRef E) ≤
          delta * (3 : ℝ) ^ (gamma * (r : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hburn
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (g * (r : ℝ)))
        calc
          (3 : ℝ) ^ (g * (r : ℝ)) * (2 * kappaRef E)
              ≤ (3 : ℝ) ^ (g * (r : ℝ)) *
                (delta * (3 : ℝ) ^ ((gamma - g) * (h : ℝ))) := hmul
          _ ≤ (3 : ℝ) ^ (g * (r : ℝ)) *
                (delta * (3 : ℝ) ^ ((gamma - g) * (r : ℝ))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hgapPow hdelta.1)
                (Real.rpow_nonneg (by norm_num) _)
          _ = delta * (3 : ℝ) ^ (gamma * (r : ℝ)) := by
              rw [show gamma * (r : ℝ) = g * (r : ℝ) +
                (gamma - g) * (r : ℝ) by ring,
                Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
              ring
      have hHA : BlockMatLoewnerLE H
          (blockScale (delta * (3 : ℝ) ^ (gamma * (r : ℝ))) Ahat) :=
        hEA.trans (blockMatLoewnerLE_blockScale_mono hscalar hAhat)
      have holdExcess := blockExcess_le_of_blockMatLoewnerLE hHsymm hHps
        hAbarSymm hAbar (mul_nonneg hdelta.1 (Real.rpow_nonneg (by norm_num) _))
        (by linarith only [heps.1]) hHA hcomp
      have hsmall : delta * (3 : ℝ) ^ (gamma * (r : ℝ)) * (1 + eps) ≤
          2 * (3 : ℝ) ^ (gamma * (r : ℝ)) * (delta + eps) := by
        have hp0 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3)
          (gamma * (r : ℝ))
        have hdp : 0 ≤ delta * (3 : ℝ) ^ (gamma * (r : ℝ)) :=
          mul_nonneg hdelta.1 hp0
        have honeps : 1 + eps ≤ 2 := by linarith only [heps.2]
        have hfirst : delta * (3 : ℝ) ^ (gamma * (r : ℝ)) * (1 + eps) ≤
            delta * (3 : ℝ) ^ (gamma * (r : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left honeps hdp
        have hde : delta ≤ delta + eps := by linarith only [heps.1]
        have hsecond : 2 * (3 : ℝ) ^ (gamma * (r : ℝ)) * delta ≤
            2 * (3 : ℝ) ^ (gamma * (r : ℝ)) * (delta + eps) :=
          mul_le_mul_of_nonneg_left hde (mul_nonneg (by norm_num) hp0)
        nlinarith only [hfirst, hsecond]
      exact holdExcess.trans hsmall
  simpa only [mul_assoc] using
    quenched_block_row_le_of_cellExcess hAbarSymm hAbar hgamma0 hgammaRho
      (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg hdelta.1 heps.1) a m hcell

/-- The original coarse-ellipticity estimate gives a uniform fallback row
bound whenever the source cutoff is active. -/
theorem quenched_block_row_le_fallback [NeZero d]
    {g rho eps : ℝ} {E Ahat Abar : BlockMat d}
    {S : CoeffSpace d → ℝ} {a : CoeffSpace d} {m : ℕ}
    (hg : 0 ≤ g) (hgrho : g < rho) (heps : eps ∈ Set.Icc (0 : ℝ) 1)
    (hAbarSymm : IsSymmetricBlockMat Abar)
    (hAbar : Book.Ch02.BlockPosDef Abar)
    (hkappa : 0 ≤ kappaRef E)
    (href : BlockMatLoewnerLE E (blockScale (2 * kappaRef E) Ahat))
    (hcomp : BlockMatLoewnerLE Ahat (blockScale (1 + eps) Abar))
    (hcoarse : ∀ M : ℤ, S a ≤ (3 : ℝ) ^ M →
      ∀ k : ℤ, k ≤ M → ∀ w : Fin d → ℤ,
        standardCellCenter k w ∈ centeredCube d M →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale ((3 : ℝ) ^ (g * ((M : ℝ) - (k : ℝ)))) E))
    (hsource : S a ≤ (3 : ℝ) ^ m) :
    quenchedBlockRow rho Abar (S a) a m ≤
      4 * kappaRef E * (1 - (3 : ℝ) ^ (-(rho - g)))⁻¹ := by
  have hcell : ∀ r : ℕ, ∀ w : Fin d → ℤ,
      standardCellCenter ((m : ℤ) - (r : ℤ)) w ∈ centeredCube d (m : ℤ) →
      blockExcess
          (coarseBlock (standardCell d ((m : ℤ) - (r : ℤ)) w) a) Abar ≤
        (4 * kappaRef E) * (3 : ℝ) ^ (g * (r : ℝ)) * 1 := by
    intro r w hw
    let H := coarseBlock (standardCell d ((m : ℤ) - (r : ℤ)) w) a
    have hHsymm : IsSymmetricBlockMat H := isSymmetricBlockMat_coarseBlock _ a
    have hU : IsOpenBoundedConvexDomain
        (standardCell d ((m : ℤ) - (r : ℤ)) w) :=
      isOpenBoundedConvexDomain_openCubeSet _
    have hvol : 0 <
        (volume (standardCell d ((m : ℤ) - (r : ℤ)) w)).toReal := by
      change 0 < (volume (openCubeSet
        (translateCube w (originCube d ((m : ℤ) - (r : ℤ)))))).toReal
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos _
    have hvol0 : volume (standardCell d ((m : ℤ) - (r : ℤ)) w) ≠ 0 := by
      intro hz
      rw [hz] at hvol
      simp at hvol
    have hHps : (toFullBlockMat H).PosSemidef :=
      Transport.posSemidef_toFullBlockMat_coarseBlock hU hvol0 a
    have hraw := hcoarse (m : ℤ) hsource ((m : ℤ) - (r : ℤ))
      (by omega) w hw
    simp only [Int.cast_sub, Int.cast_natCast] at hraw
    have hrCast : (m : ℝ) - ((m : ℝ) - (r : ℝ)) = (r : ℝ) := by ring
    rw [hrCast] at hraw
    have hscaled := blockMatLoewnerLE_blockScale_of_le
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (g * (r : ℝ))) href
    have hHA : BlockMatLoewnerLE H
        (blockScale ((3 : ℝ) ^ (g * (r : ℝ)) * (2 * kappaRef E)) Ahat) := by
      have := hraw.trans hscaled
      simpa only [H, blockScale_blockScale] using this
    have hexcess := blockExcess_le_of_blockMatLoewnerLE hHsymm hHps
      hAbarSymm hAbar
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (by norm_num) hkappa))
      (by linarith only [heps.1]) hHA hcomp
    have hp : 0 ≤ (3 : ℝ) ^ (g * (r : ℝ)) := by positivity
    have hsmall : (3 : ℝ) ^ (g * (r : ℝ)) * (2 * kappaRef E) *
          (1 + eps) ≤ 4 * kappaRef E * (3 : ℝ) ^ (g * (r : ℝ)) := by
      have honeps : 1 + eps ≤ 2 := by linarith only [heps.2]
      have hkp : 0 ≤ (3 : ℝ) ^ (g * (r : ℝ)) * (2 * kappaRef E) :=
        mul_nonneg hp (mul_nonneg (by norm_num) hkappa)
      have := mul_le_mul_of_nonneg_left honeps hkp
      nlinarith only [this]
    simpa only [mul_one] using hexcess.trans hsmall
  simpa only [mul_one, mul_assoc] using
    quenched_block_row_le_of_cellExcess hAbarSymm hAbar hg hgrho
      (mul_nonneg (by norm_num) hkappa) (by norm_num) a m hcell

end

end HCPolySupport.HighContrast.Quenched
