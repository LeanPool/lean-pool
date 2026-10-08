/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitMaximumEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupplyFree

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBurnSplitNssEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn-split pathwise envelope in normalized-source form

The mesoscale (burn-split) adapted-cell ceiling, converted to the
normalized-source-scale form the abstract single-cell variance consumes:
at window top `k + D` the ceiling is the **dimensional** constant `2`
times `NSS_{S'}(k+D-1)^g` — no boundary constant, no grid-norm power.
This is the print's frame discipline (the printed argument): the geometry is
absorbed into the burn depth `D`, which rides only in scale thresholds.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

/-- **The burn-split pathwise envelope, normalized-source form.** -/
theorem coarseBlock_adaptedCell_burnsplit_nss
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} {E : BlockMat d}
    (hE : Book.Ch02.BlockPosDef E)
    {Sh : CoeffSpace d → ℝ} {D : ℕ}
    (hmeso : ∀ᵐ a ∂P, ∀ m : ℤ, Sh a ≤ (3 : ℝ) ^ m → ∀ k : ℤ, k ≤ m →
      ∀ w : Fin d → ℤ, standardCellCenter k w ∈ centeredCube d m →
        BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
          (blockScale
            ((3 : ℝ) ^ (g * max ((m : ℝ) - 2 * (D : ℝ) - (k : ℝ)) 0)) E))
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    (hD : boundaryConst Cd g n ≤ (3 : ℝ) ^ D)
    (k : ℤ) :
    ∀ᵐ a ∂P,
      adaptedCell (roundedGrid l n) k ⊆
          centeredCube d (k + (D : ℤ)) →
        BlockMatLoewnerLE
          (coarseBlock (adaptedCell (roundedGrid l n) k) a)
          (blockScale
            (2 * normalizedSourceScale Sh (k + (D : ℤ) - 1) a ^ g) E) := by
  have hquadE : ∀ X : BlockVec d,
      0 ≤ blockVecDot X (blockMatVecMul E X) := by
    intro X
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact (hE X hX).le
  have hcoef2 : 1 + Cd * witnessEccentricity n * zetaG g *
      (3 : ℝ) ^ (-(D : ℤ)) ≤ 2 := by
    have h3D : (0 : ℝ) < (3 : ℝ) ^ (-(D : ℤ)) := zpow_pos (by norm_num) _
    have hstep := mul_le_mul_of_nonneg_right hD h3D.le
    rw [← zpow_natCast (3 : ℝ) D,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)] at hstep
    rw [boundaryConst] at hstep
    have h1 : Cd * witnessEccentricity n * zetaG g *
        (3 : ℝ) ^ (-(D : ℤ)) ≤ 1 := by
      simpa using hstep
    linarith only [h1]
  filter_upwards [coarseBlock_adaptedCell_burnsplit_le_of_mesoEnvelope
    hd hg hE hmeso hl hCd hn] with a hbound
  intro hsub
  have hsub0 : adaptedCellAt (roundedGrid l n) k (0 : Fin d → ℤ) ⊆
      centeredCube d (k + (D : ℤ)) := by
    rw [adaptedCellAt_zero]
    exact hsub
  have hnss1 : 1 ≤ normalizedSourceScale Sh (k + (D : ℤ) - 1) a :=
    one_le_normalizedSourceScale Sh _ a
  have hnssg1 : 1 ≤ normalizedSourceScale Sh (k + (D : ℤ) - 1) a ^ g :=
    Real.one_le_rpow hnss1 hg.1
  by_cases hS : Sh a ≤ (3 : ℝ) ^ (k + (D : ℤ))
  · -- the good event: the ceiling collapses to the dimensional constant
    have hcell := hbound (k + (D : ℤ)) hS k (0 : Fin d → ℤ) hsub0
    rw [adaptedCellAt_zero] at hcell
    have hmax0 : max (((k + (D : ℤ) : ℤ) : ℝ) - (D : ℝ) - (k : ℝ)) 0 =
        0 := by
      have : ((k + (D : ℤ) : ℤ) : ℝ) - (D : ℝ) - (k : ℝ) = 0 := by
        push_cast
        ring
      rw [this, max_self]
    rw [hmax0, mul_zero, Real.rpow_zero, mul_one] at hcell
    refine fun X => le_trans (hcell X) ?_
    have hcoefle : 1 + Cd * witnessEccentricity n * zetaG g *
        (3 : ℝ) ^ (-(D : ℤ)) ≤
        2 * normalizedSourceScale Sh (k + (D : ℤ) - 1) a ^ g := by
      nlinarith only [hcoef2, hnssg1]
    exact blockScale_loewner_mono hquadE hcoefle X
  · -- the tail event: the ceiling is paid by the normalized source scale
    push Not at hS
    have hSa0 : (0 : ℝ) < Sh a :=
      lt_trans (zpow_pos (by norm_num) _) hS
    set m : ℤ := ⌈Real.logb 3 (Sh a)⌉ with hmdef
    have hm1 : k + (D : ℤ) ≤ m := by
      have hlog : ((k + (D : ℤ) : ℤ) : ℝ) < Real.logb 3 (Sh a) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) hSa0]
        rw [← Real.rpow_intCast (3 : ℝ) (k + (D : ℤ))] at hS
        exact hS
      have h := le_trans hlog.le (Int.le_ceil (Real.logb 3 (Sh a)))
      exact_mod_cast h
    have hm2 : Sh a ≤ (3 : ℝ) ^ m := by
      have h1 : Sh a = (3 : ℝ) ^ Real.logb 3 (Sh a) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hSa0).symm
      rw [h1, ← Real.rpow_intCast (3 : ℝ) m]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
    have hsub' : adaptedCellAt (roundedGrid l n) k (0 : Fin d → ℤ) ⊆
        centeredCube d m :=
      hsub0.trans (Window.centeredCube_mono hm1)
    have hcell := hbound m hm2 k (0 : Fin d → ℤ) hsub'
    rw [adaptedCellAt_zero] at hcell
    have hup : (m : ℝ) ≤ Real.logb 3 (Sh a) + 1 := by
      have := Int.ceil_lt_add_one (Real.logb 3 (Sh a))
      exact_mod_cast this.le
    have hmaxpos : max ((m : ℝ) - (D : ℝ) - (k : ℝ)) 0 =
        (m : ℝ) - (D : ℝ) - (k : ℝ) := by
      refine max_eq_left ?_
      have hcast : ((k + (D : ℤ) : ℤ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hm1
      push_cast at hcast ⊢
      linarith only [hcast]
    rw [hmaxpos] at hcell
    have hceil : (3 : ℝ) ^ (g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) ≤
        normalizedSourceScale Sh (k + (D : ℤ) - 1) a ^ g := by
      have hbase : (3 : ℝ) ^ ((m : ℝ) - (D : ℝ) - (k : ℝ)) ≤
          normalizedSourceScale Sh (k + (D : ℤ) - 1) a := by
        have h1 : (3 : ℝ) ^ ((m : ℝ) - (D : ℝ) - (k : ℝ)) ≤
            (3 : ℝ) ^ (Real.logb 3 (Sh a) + 1 - (D : ℝ) - (k : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          linarith only [hup]
        refine h1.trans ?_
        have h2 : (3 : ℝ) ^ (Real.logb 3 (Sh a) + 1 - (D : ℝ) - (k : ℝ)) =
            Sh a * (3 : ℝ) ^ (1 - (D : ℝ) - (k : ℝ)) := by
          rw [show Real.logb 3 (Sh a) + 1 - (D : ℝ) - (k : ℝ) =
              Real.logb 3 (Sh a) + (1 - (D : ℝ) - (k : ℝ)) from by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 3),
            Real.rpow_logb (by norm_num) (by norm_num) hSa0]
        rw [h2]
        refine le_trans (le_of_eq ?_) (le_max_right _ _)
        congr 1
        rw [← Real.rpow_intCast (3 : ℝ) (-(k + (D : ℤ) - 1))]
        congr 1
        push_cast
        ring
      calc
        (3 : ℝ) ^ (g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) =
            ((3 : ℝ) ^ ((m : ℝ) - (D : ℝ) - (k : ℝ))) ^ g := by
          rw [mul_comm g, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        _ ≤ normalizedSourceScale Sh (k + (D : ℤ) - 1) a ^ g :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
            hbase hg.1
    refine fun X => le_trans (hcell X) ?_
    have hcoefle : (1 + Cd * witnessEccentricity n * zetaG g *
        (3 : ℝ) ^ (-(D : ℤ))) *
        (3 : ℝ) ^ (g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) ≤
        2 * normalizedSourceScale Sh (k + (D : ℤ) - 1) a ^ g := by
      have h3g0 : (0 : ℝ) ≤
          (3 : ℝ) ^ (g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) :=
        Real.rpow_nonneg (by norm_num) _
      have hstep : (1 + Cd * witnessEccentricity n * zetaG g *
          (3 : ℝ) ^ (-(D : ℤ))) *
          (3 : ℝ) ^ (g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) ≤
          2 * (3 : ℝ) ^ (g * ((m : ℝ) - (D : ℝ) - (k : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef2 h3g0
      refine hstep.trans ?_
      exact mul_le_mul_of_nonneg_left hceil (by norm_num)
    exact blockScale_loewner_mono hquadE hcoefle X

end

end HCPolySupport.HighContrast.Quenched
