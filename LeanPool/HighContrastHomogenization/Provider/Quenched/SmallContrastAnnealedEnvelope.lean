/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMaximumEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMoment
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeReferenceComparison

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAnnealedEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed scaled envelope

Integrating the pathwise scale-adapted source envelope over the law bounds
every annealed aligned cell by the reference block with the deterministic
factor `C(K) · boundaryConst · 3^{g(t+G−k)}`: the random burn overshoot has
a first moment bounded by the crude-moment constant.  This is the
deterministic envelope that makes the deep legs of the hatted rows summable
against the `3^{(3/2)(k−s)}` weights.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The crude-moment constant of order one. -/
@[expose]
def sourceMomentOne (K : ℝ) : ℝ :=
  1 + 2 * (1 + Real.log (growthBar K)) *
    growthBar K ^ IndependentSums.natTriangular 1

theorem one_le_sourceMomentOne {K : ℝ} : 1 ≤ sourceMomentOne K := by
  have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hlog : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [h2])
  have hpow : (0 : ℝ) ≤ growthBar K ^ IndependentSums.natTriangular 1 := by
    positivity
  rw [sourceMomentOne]
  nlinarith only [hlog, hpow]

/-- The first moment of the normalized source scale. -/
theorem integral_normalizedSourceScale_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK) :
    ∫ a, normalizedSourceScale S sK a ∂P ≤ sourceMomentOne K := by
  have hmeas : Measurable (normalizedSourceScale S sK) :=
    Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  have h0 : ∀ a, 0 ≤ normalizedSourceScale S sK a := fun a =>
    le_trans zero_le_one (one_le_normalizedSourceScale S sK a)
  have hlint := lintegral_normalizedSourceScale_pow_le hdag hsK 1 le_rfl
  have hone : ∀ a, normalizedSourceScale S sK a ^ ((1 : ℕ) : ℝ) =
      normalizedSourceScale S sK a := fun a => by
    norm_num
  rw [lintegral_congr fun a => congrArg ENNReal.ofReal (hone a)] at hlint
  have hCK : sourceMomentOne K =
      1 + 2 * ((1 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular 1 := by
    rw [sourceMomentOne]
    push_cast
    ring
  rw [integral_eq_lintegral_of_nonneg_ae
    (_root_.Filter.Eventually.of_forall h0) hmeas.aestronglyMeasurable]
  rw [hCK]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hlint
  have h1 : (1 : ℝ) ≤ 1 + 2 * ((1 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
      growthBar K ^ IndependentSums.natTriangular 1 := by
    have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
    have hlog : 0 ≤ Real.log (growthBar K) :=
      Real.log_nonneg (by linarith only [h2])
    have hpow : (0 : ℝ) ≤
        growthBar K ^ IndependentSums.natTriangular 1 := by positivity
    push_cast
    nlinarith only [hlog, hpow]
  linarith only [h1]

/-- The normalized source scale is integrable. -/
theorem integrable_normalizedSourceScale
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK) :
    Integrable (normalizedSourceScale S sK) P := by
  have hmeas : Measurable (normalizedSourceScale S sK) :=
    Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hlint := lintegral_normalizedSourceScale_pow_le hdag hsK 1 le_rfl
  have hone : ∀ a, normalizedSourceScale S sK a ^ ((1 : ℕ) : ℝ) =
      normalizedSourceScale S sK a := fun a => by norm_num
  rw [lintegral_congr fun a => congrArg ENNReal.ofReal (hone a)] at hlint
  refine lt_of_le_of_lt (le_trans (lintegral_mono fun a => ?_) hlint)
    ENNReal.ofReal_lt_top
  rw [Real.enorm_eq_ofReal
    (le_trans zero_le_one (one_le_normalizedSourceScale S sK a))]

/-- **The annealed scaled envelope**: every annealed aligned cell contained
in the generation cube is dominated by the reference with the deterministic
scale-adapted factor. -/
theorem annealedBlock_adaptedCell_le_scaled [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    {k : ℤ} {w : Fin d → ℤ} (t : ℤ) {G : ℕ}
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hsub : adaptedCellAt (roundedGrid l n) k w ⊆
      centeredCube d (t + (G : ℤ)))
    (hint : HasIntegrableCoarseBlock P
      (adaptedCellAt (roundedGrid l n) k w)) :
    BlockMatLoewnerLE
      (annealedBlock P (adaptedCellAt (roundedGrid l n) k w))
      (blockScale
        (sourceMomentOne K * boundaryConst Cd g n *
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ)))) E) := by
  classical
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g n :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  set c0 : ℝ := boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) with hc0
  have hc00 : 0 ≤ c0 :=
    mul_nonneg hbC0.le (Real.rpow_nonneg (by norm_num) _)
  -- the pathwise scalar envelope
  have hscalar : ∀ᵐ a ∂P,
      ∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ≤
        c0 * normalizedSourceScale S sK a *
          blockVecDot X (blockMatVecMul E X) := by
    filter_upwards [coarseBlock_adaptedCell_scaled_le_of_source_burned
      hd hg hdag hl hCd hn] with a henv
    intro X
    -- choose the burn scale
    by_cases hS : S a ≤ (3 : ℝ) ^ (t + (G : ℤ))
    · have hcell := henv (t + (G : ℤ)) hS k w hsub X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
      have hVS1 := one_le_normalizedSourceScale S sK a
      have hquad : 0 ≤ blockVecDot X (blockMatVecMul E X) := by
        by_cases hX : X = 0
        · subst X
          simp [blockMatVecMul, blockVecDot, vecDot]
        · exact (hdag.refBlock_posDef X hX).le
      have hc0' : 0 ≤ boundaryConst Cd g n *
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) :=
        mul_nonneg hbC0.le (Real.rpow_nonneg (by norm_num) _)
      have hprod : 0 ≤ (normalizedSourceScale S sK a - 1) *
          (boundaryConst Cd g n *
            (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
            blockVecDot X (blockMatVecMul E X)) :=
        mul_nonneg (by linarith only [hVS1]) (mul_nonneg hc0' hquad)
      rw [hc0]
      nlinarith only [hcell, hprod]
    · push Not at hS
      have hS0 : 0 < S a := lt_trans (zpow_pos (by norm_num) _) hS
      set m : ℤ := ⌈Real.logb 3 (S a)⌉ with hmdef
      have hlogS : ((t + (G : ℤ) : ℤ) : ℝ) < Real.logb 3 (S a) := by
        rw [Real.lt_logb_iff_rpow_lt (by norm_num) hS0]
        rw [← Real.rpow_intCast (3 : ℝ) (t + (G : ℤ))] at hS
        exact hS
      have hm1 : t + (G : ℤ) ≤ m := by
        have h := le_trans hlogS.le (Int.le_ceil (Real.logb 3 (S a)))
        exact_mod_cast h
      have hm2 : S a ≤ (3 : ℝ) ^ m := by
        have h1 : S a = (3 : ℝ) ^ Real.logb 3 (S a) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hS0).symm
        rw [h1, ← Real.rpow_intCast (3 : ℝ) m]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.le_ceil _)
      have hsub' : adaptedCellAt (roundedGrid l n) k w ⊆
          centeredCube d m :=
        hsub.trans (Window.centeredCube_mono hm1)
      have hcell2 := henv m hm2 k w hsub' X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell2
      have hquad : 0 ≤ blockVecDot X (blockMatVecMul E X) := by
        by_cases hX : X = 0
        · subst X
          simp [blockMatVecMul, blockVecDot, vecDot]
        · exact (hdag.refBlock_posDef X hX).le
      have hcell : blockVecDot X (blockMatVecMul
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ≤
          boundaryConst Cd g n *
            (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) *
            blockVecDot X (blockMatVecMul E X) := by
        linarith only [hcell2]
      refine le_trans hcell ?_
      refine mul_le_mul_of_nonneg_right ?_ hquad
      -- `bC·3^{g(m−k)} ≤ c0 · VS`
      have hchain : (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) ≤
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
            normalizedSourceScale S sK a := by
        have hup : (m : ℝ) ≤ Real.logb 3 (S a) + 1 := by
          have := Int.ceil_lt_add_one (Real.logb 3 (S a))
          exact_mod_cast this.le
        have hstep1 : (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) ≤
            (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
              (3 : ℝ) ^ (g * ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (le_of_eq ?_)
          ring
        refine hstep1.trans ?_
        refine mul_le_mul_of_nonneg_left ?_
          (Real.rpow_nonneg (by norm_num) _)
        -- `3^{g(m−(t+G))} ≤ VS`
        have hmS : (3 : ℝ) ^ ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ)) ≤
            normalizedSourceScale S sK a := by
          have h1 : (3 : ℝ) ^ ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ)) ≤
              (3 : ℝ) ^ (Real.logb 3 (S a) + 1 -
                ((t + (G : ℤ) : ℤ) : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            linarith only [hup]
          refine h1.trans ?_
          have h2 : (3 : ℝ) ^ (Real.logb 3 (S a) + 1 -
              ((t + (G : ℤ) : ℤ) : ℝ)) =
              S a * (3 : ℝ) ^ (1 - ((t + (G : ℤ) : ℤ) : ℝ)) := by
            rw [show Real.logb 3 (S a) + 1 - ((t + (G : ℤ) : ℤ) : ℝ) =
                Real.logb 3 (S a) + (1 - ((t + (G : ℤ) : ℤ) : ℝ)) from by
              ring, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
              Real.rpow_logb (by norm_num) (by norm_num) hS0]
          rw [h2]
          have h3 : S a * (3 : ℝ) ^ (1 - ((t + (G : ℤ) : ℤ) : ℝ)) ≤
              S a * (3 : ℝ) ^ (-(sK : ℝ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hS0.le
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            have : (0 : ℝ) ≤ ((t + (G : ℤ) - 1 - sK : ℤ) : ℝ) := by
              exact_mod_cast hDelta
            push_cast at this ⊢
            linarith only [this]
          refine h3.trans ?_
          rw [show (3 : ℝ) ^ (-(sK : ℝ)) = (3 : ℝ) ^ (-sK : ℤ) from by
            rw [← Real.rpow_intCast (3 : ℝ) (-sK)]
            norm_num]
          exact le_max_right _ _
        -- raise to the power `g`
        calc
          (3 : ℝ) ^ (g * ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ))) =
              ((3 : ℝ) ^ ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ))) ^ g := by
            rw [mul_comm g, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ ≤ normalizedSourceScale S sK a ^ g := by
            refine Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
              hmS hg.1
          _ ≤ normalizedSourceScale S sK a ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le
              (one_le_normalizedSourceScale S sK a) hg.2.le
          _ = normalizedSourceScale S sK a := Real.rpow_one _
      calc
        boundaryConst Cd g n * (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) ≤
            boundaryConst Cd g n *
              ((3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
                normalizedSourceScale S sK a) :=
          mul_le_mul_of_nonneg_left hchain hbC0.le
        _ = c0 * normalizedSourceScale S sK a := by
          rw [hc0]
          ring
  -- integrate
  intro X
  have hid := blockVecDot_blockMatVecMul_annealedBlock hint X
  rw [hid, Sharp.blockVecDot_blockMatVecMul_blockScale]
  have hquadE : 0 ≤ blockVecDot X (blockMatVecMul E X) := by
    by_cases hX : X = 0
    · subst X
      simp [blockMatVecMul, blockVecDot, vecDot]
    · exact (hdag.refBlock_posDef X hX).le
  have hint1 : Integrable
      (fun a => blockVecDot X (blockMatVecMul
        (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X)) P :=
    integrable_blockVecDot_coarseBlock hint X
  have hint2 : Integrable (fun a => c0 * normalizedSourceScale S sK a *
      blockVecDot X (blockMatVecMul E X)) P := by
    have h := ((integrable_normalizedSourceScale hdag hsK).const_mul
      c0).mul_const (blockVecDot X (blockMatVecMul E X))
    refine h.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
    ring
  have hmono := integral_mono_ae hint1 hint2 (by
    filter_upwards [hscalar] with a ha using ha X)
  have hsplit : ∫ a, c0 * normalizedSourceScale S sK a *
      blockVecDot X (blockMatVecMul E X) ∂P =
      c0 * (∫ a, normalizedSourceScale S sK a ∂P) *
        blockVecDot X (blockMatVecMul E X) := by
    rw [show (fun a => c0 * normalizedSourceScale S sK a *
        blockVecDot X (blockMatVecMul E X)) =
        fun a => c0 * (normalizedSourceScale S sK a *
          blockVecDot X (blockMatVecMul E X)) from by
      funext a
      ring]
    rw [integral_const_mul, integral_mul_const]
    ring
  have hVSle := integral_normalizedSourceScale_le hdag hsK
  have hbound : ∫ a, blockVecDot X (blockMatVecMul
      (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ∂P ≤
      sourceMomentOne K * boundaryConst Cd g n *
        (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
        blockVecDot X (blockMatVecMul E X) := by
    refine le_trans hmono ?_
    rw [hsplit]
    calc
      c0 * (∫ a, normalizedSourceScale S sK a ∂P) *
          blockVecDot X (blockMatVecMul E X) ≤
          c0 * sourceMomentOne K * blockVecDot X (blockMatVecMul E X) := by
        refine mul_le_mul_of_nonneg_right ?_ hquadE
        exact mul_le_mul_of_nonneg_left hVSle hc00
      _ = sourceMomentOne K * boundaryConst Cd g n *
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
          blockVecDot X (blockMatVecMul E X) := by
        rw [hc0]
        ring
  linarith only [hbound]

end

end HCPolySupport.HighContrast.Quenched
