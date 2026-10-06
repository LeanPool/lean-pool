/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowCapIsotropyAdjoint
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowValueIsotropy

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastCapsBundleRowIsotropy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The caps bundle's row half, at the split row caps

The part of the row caps that is independent of the block parametrization.

`profile_caps_bundle_entry_of_block_at_level` (the cited theorem) delivers six
clauses: two rows, two weak quantities, two centering caps.  Only the **rows**
call the row caps (the corresponding proof step, the corresponding proof step); the weak
quantities go through
`profilePrimalWeakQuantity_le_weakValueSharp_of_block_at_level`, whose statement names
the inflated reference and therefore belongs to the family of modules built on
the block parametrization.

So the honest split of work is: the row half can be repointed to the corresponding argument split
caps **now**, and that is what this file does; the weak half is repointed by the
wave.  Duplicating the bundle's unchanged weak and centering clauses here would
produce a module that the wave immediately obsoletes, so it is not done.

The isotropic entry caps bundle is assembled from
`caps_bundle_entry_rows_isotropy` below plus the family's `_of_block` siblings, with
no new mathematics.

**What is `Π`-free here and what is not.**  The first summand of
`rowSplitConstant` is dimension-only.  The second, `capsDeepConstant`, still
carries `boundaryConst · 3^{g((t+G)-s)}` — but multiplied by
`3^{(3/2-g)((k₀-1)-s)}`, which the gap `s - k₀` drives below any prescribed
tolerance at rate `3/2 - g > 1/2`, for every `g` in the frozen range (the corresponding argument).
Choosing that gap is the caller's `tiltGap`-shaped threshold.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The deep-leg constant of the split row cap, as it appears at the bundle's
window `(s, t)` and split scale `k₀`. -/
@[expose]
def capsDeepConstant (Cd g : ℝ) (mAl : Mat d) (G : ℕ) (k0 s t : ℤ) : ℝ :=
  2 * (2 * boundaryConst Cd g mAl *
      (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ)))) *
    ((3 : ℝ) ^ ((3 / 2 - g) * (((k0 - 1 : ℤ) : ℝ) - (s : ℝ))) *
      (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g)))))

theorem capsDeepConstant_nonneg [Nonempty (Fin d)] {Cd g : ℝ} (hCd : 1 ≤ Cd)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {mAl : Mat d} (hn : mAl.PosDef) (G : ℕ)
    (k0 s t : ℤ) : 0 ≤ capsDeepConstant Cd g mAl G k0 s t := by
  have hbC : (1 : ℝ) ≤ boundaryConst Cd g mAl := Initialization.one_le_boundaryConst hCd hg hn
  have hbC0 : (0 : ℝ) ≤ boundaryConst Cd g mAl := by linarith only [hbC]
  have hgeo : (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g))) := by
    have hlt : (3 : ℝ) ^ (-(3 / 2 - g)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hg.2])
    exact div_pos one_pos (by linarith only [hlt])
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤
      (3 : ℝ) ^ ((3 / 2 - g) * (((k0 - 1 : ℤ) : ℝ) - (s : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  rw [capsDeepConstant]
  have hgeo0 := hgeo.le
  positivity

/-- **The bundle's two row clauses, at the split row caps.**  The row constant is
`rowSplitConstant cIso (capsDeepConstant …)`: a dimension-only head plus a
geometrically discounted deep leg. -/
theorem caps_bundle_entry_rows_isotropy [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {lAl : ℤ} (hl : (kZero d : ℤ) ≤ lAl)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {mAl : Mat d} (hn : mAl.PosDef)
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl mAl))
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (t : ℤ) {G : ℕ} (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (t + (G : ℤ) - sK))
    {s : ℤ} (hst : s ≤ t)
    (hgeomS : ∀ k : ℤ, k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k s,
        adaptedCellAt (roundedGrid lAl mAl) k w ⊆
          centeredCube d (t + (G : ℤ)))
    {k0 : ℤ} {cIso : ℝ} (hcIso : 0 ≤ cIso)
    (hiso : ∀ k : ℤ, k0 ≤ k → k ≤ s →
      ∀ w ∈ Response.alignedIndex (roundedGrid lAl mAl) k s,
        BlockMatLoewnerLE
          (annealedBlock P (adaptedCellAt (roundedGrid lAl mAl) k w))
          (blockScale (1 + cIso) E))
    (hint : HasFiniteAdaptedMean P (roundedGrid lAl mAl) t)
    {S0 SStar0 K0 : Mat d} (hS0 : S0.PosDef) (hStar0 : SStar0.PosDef)
    (hform : toFullBlockMat (adaptedMean P (roundedGrid lAl mAl) t) =
      schurBlock S0 SStar0 K0)
    {eps : ℝ} (hpos : 0 < eps) (heps1 : eps ≤ 1)
    (htr : (d : ℝ) * (schurHattedContrast S0 SStar0 - 1) ≤ eps)
    {kap : ℝ} (hkap0 : 0 ≤ kap)
    (hcomp : ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul E X) ≤
        kap * blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid lAl mAl) t) X)) :
    ∀ e : Vec d, e ⬝ᵥ e = 1 →
      Response.profilePrimalHattedEarlierRow P (roundedGrid lAl mAl)
          (Response.responseSkew K0) s
          (Response.profilePrimalCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).1
          (Response.profilePrimalCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).2 ≤
        ENNReal.ofReal (rowValue2Isotropy d
          (rowSplitConstant cIso (capsDeepConstant Cd g mAl G k0 s t))
          kap eps) ∧
      Response.profileAdjointHattedEarlierRow P (roundedGrid lAl mAl)
          (Response.responseSkew K0) s
          (Response.profileAdjointCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).1
          (Response.profileAdjointCenter P
            (Recurrence.posDef_of_isRoundedGrid hgrid) t
            (fun a ↦ a.subSkew (Response.responseSkew K0)
              (Response.is_skew_mat_response_skew K0))
            (Response.centeredResponseLoadP S0 SStar0 K0 e)
            (Response.centeredResponseLoadQ S0 SStar0 K0 e)).2 ≤
        ENNReal.ofReal (rowValue2Isotropy d
          (rowSplitConstant cIso (capsDeepConstant Cd g mAl G k0 s t))
          kap eps) := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hq : (roundedGrid lAl mAl).PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hcrow0 : 0 ≤
      rowSplitConstant cIso (capsDeepConstant Cd g mAl G k0 s t) :=
    rowSplitConstant_nonneg hcIso
      (capsDeepConstant_nonneg hCd1 hg hn G k0 s t)
  intro e he
  have hQm := profileQuadraticLoad_hatted_primal_center_le hq t hint hS0
    hStar0 hform hpos heps1 htr hkap0 hcomp e he
  have hQp := profileQuadraticLoad_hatted_adjoint_center_le hq t hint hS0
    hStar0 hform hpos heps1 htr hkap0 hcomp e he
  have hrowm := profilePrimalHattedEarlierRow_le_isotropy_split hd hg hdag hl
    hCd hn hsK t hDelta hentry hst hgeomS hcIso hiso (Response.responseSkew K0)
    (Response.profilePrimalCenter P hq t
      (fun a ↦ a.subSkew (Response.responseSkew K0)
        (Response.is_skew_mat_response_skew K0))
      (Response.centeredResponseLoadP S0 SStar0 K0 e)
      (Response.centeredResponseLoadQ S0 SStar0 K0 e)).1
    (Response.profilePrimalCenter P hq t
      (fun a ↦ a.subSkew (Response.responseSkew K0)
        (Response.is_skew_mat_response_skew K0))
      (Response.centeredResponseLoadP S0 SStar0 K0 e)
      (Response.centeredResponseLoadQ S0 SStar0 K0 e)).2
  have hrowp := profileAdjointHattedEarlierRow_le_isotropy_split hd hg hdag hl
    hCd hn hsK t hDelta hentry hst hgeomS hcIso hiso (Response.responseSkew K0)
    (Response.profileAdjointCenter P hq t
      (fun a ↦ a.subSkew (Response.responseSkew K0)
        (Response.is_skew_mat_response_skew K0))
      (Response.centeredResponseLoadP S0 SStar0 K0 e)
      (Response.centeredResponseLoadQ S0 SStar0 K0 e)).1
    (Response.profileAdjointCenter P hq t
      (fun a ↦ a.subSkew (Response.responseSkew K0)
        (Response.is_skew_mat_response_skew K0))
      (Response.centeredResponseLoadP S0 SStar0 K0 e)
      (Response.centeredResponseLoadQ S0 SStar0 K0 e)).2
  have hA0 : (0 : ℝ) ≤ 2 * (1 + cIso) * (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    have hgeo := one_le_row_head_geometric
    nlinarith only [hcIso, hgeo]
  have hB0 : (0 : ℝ) ≤ 2 * (2 * boundaryConst Cd g mAl *
      (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (s : ℝ)))) *
    ((3 : ℝ) ^ ((3 / 2 - g) * (((k0 - 1 : ℤ) : ℝ) - (s : ℝ))) *
      (1 / (1 - (3 : ℝ) ^ (-(3 / 2 - g))))) := by
    have h := capsDeepConstant_nonneg (Cd := Cd) hCd1 hg hn G k0 s t
    rwa [capsDeepConstant] at h
  constructor
  · refine le_trans hrowm (ENNReal.ofReal_le_ofReal ?_)
    rw [rowValue2Isotropy, rowSplitConstant, capsDeepConstant]
    have h1 := mul_le_mul_of_nonneg_left hQm hA0
    have h2 := mul_le_mul_of_nonneg_left hQm hB0
    nlinarith only [h1, h2]
  · refine le_trans hrowp (ENNReal.ofReal_le_ofReal ?_)
    rw [rowValue2Isotropy, rowSplitConstant, capsDeepConstant]
    have h1 := mul_le_mul_of_nonneg_left hQp hA0
    have h2 := mul_le_mul_of_nonneg_left hQp hB0
    nlinarith only [h1, h2]

end

end HCPolySupport.HighContrast.Quenched
