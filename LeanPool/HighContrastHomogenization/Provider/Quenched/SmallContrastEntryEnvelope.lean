/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEntryEnvelope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The entry-collapsed annealed envelope

Past the source burn-in — once the generation cube exceeds the burn scale
by the logarithm of the second source moment — the annealed envelope's
gauge cost collapses to a factor `2`: the good event contributes the
deterministic dagger envelope, and the bad event's first moment is
dominated by the second moment divided by the (geometrically large)
threshold.  This is the formalized counterpart of the printed entry step
(HC (4.18) and the mesoscale choice `h' ~ log Π`): every
excess-multiplying constant of the recursion becomes dimensional after a
polynomial entry delay, while the source-moment constants retreat into
decaying terms and the delay itself.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- The second moment of the normalized source scale. -/
theorem integral_sq_normalizedSourceScale_le
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK) :
    ∫ a, normalizedSourceScale S sK a ^ 2 ∂P ≤ sourceMomentTwo K := by
  have hmeas : Measurable (normalizedSourceScale S sK) :=
    Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  have h0 : ∀ a, 0 ≤ normalizedSourceScale S sK a ^ 2 := fun a =>
    sq_nonneg _
  have hlint := lintegral_normalizedSourceScale_pow_le hdag hsK 2
    (by norm_num)
  have htwo : ∀ a, normalizedSourceScale S sK a ^ ((2 : ℕ) : ℝ) =
      normalizedSourceScale S sK a ^ 2 := fun a => by
    rw [← Real.rpow_natCast (normalizedSourceScale S sK a) 2]
  rw [lintegral_congr fun a => congrArg ENNReal.ofReal (htwo a)] at hlint
  have hCK : sourceMomentTwo K =
      1 + 2 * ((2 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
        growthBar K ^ IndependentSums.natTriangular 2 := by
    rw [sourceMomentTwo]
  rw [integral_eq_lintegral_of_nonneg_ae
    (_root_.Filter.Eventually.of_forall h0)
    ((hmeas.pow_const 2).aestronglyMeasurable)]
  rw [hCK]
  refine ENNReal.toReal_le_of_le_ofReal ?_ hlint
  have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hlog : 0 ≤ Real.log (growthBar K) :=
    Real.log_nonneg (by linarith only [h2])
  have hpow : (0 : ℝ) ≤
      growthBar K ^ IndependentSums.natTriangular 2 := by positivity
  push_cast
  nlinarith only [hlog, hpow]

/-- The square of the normalized source scale is integrable. -/
theorem integrable_sq_normalizedSourceScale
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK) :
    Integrable (fun a => normalizedSourceScale S sK a ^ 2) P := by
  have hmeas : Measurable (normalizedSourceScale S sK) :=
    Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hlint := lintegral_normalizedSourceScale_pow_le hdag hsK 2
    (by norm_num)
  have htwo : ∀ a, normalizedSourceScale S sK a ^ ((2 : ℕ) : ℝ) =
      normalizedSourceScale S sK a ^ 2 := fun a => by
    rw [← Real.rpow_natCast (normalizedSourceScale S sK a) 2]
  rw [lintegral_congr fun a => congrArg ENNReal.ofReal (htwo a)] at hlint
  refine lt_of_le_of_lt (le_trans (lintegral_mono fun a => ?_) hlint)
    ENNReal.ofReal_lt_top
  rw [Real.enorm_eq_ofReal (sq_nonneg _)]


private theorem adapted_cell_pathwise_source_envelope [NeZero d]
    (hd : 2 ≤ d) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {Cd : ℝ} (hCd : max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd)
    {n : Mat d} (hn : n.PosDef)
    {sK : ℤ}
    {k : ℤ} {w : Fin d → ℤ} (t : ℤ) {G : ℕ}
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    (hsub : adaptedCellAt (roundedGrid l n) k w ⊆
      centeredCube d (t + (G : ℤ)))
    (hbC0 : 0 < boundaryConst Cd g n)
    (hc00 : 0 ≤ (boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ)))))
    (hnss1 : ∀ a, 1 ≤ (normalizedSourceScale S sK) a)
    : (∀ᵐ a ∂P,
      ∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ≤
        (boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ)))) * (1 + ({a | (3 : ℝ) ^ (t + (G : ℤ)) < S
      a}).indicator (normalizedSourceScale S sK) a) *
          blockVecDot X (blockMatVecMul E X)) := by
  classical
  set c0 : ℝ := boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) with hc0
  set bad : Set (CoeffSpace d) :=
    {a | (3 : ℝ) ^ (t + (G : ℤ)) < S a} with hbaddef
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  have hscalar : ∀ᵐ a ∂P,
      ∀ X : BlockVec d,
        blockVecDot X (blockMatVecMul
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ≤
        c0 * (1 + bad.indicator nss a) *
          blockVecDot X (blockMatVecMul E X) := by
    filter_upwards [coarseBlock_adaptedCell_scaled_le_of_source_burned
      hd hg hdag hl hCd hn] with a henv
    intro X
    have hquad : 0 ≤ blockVecDot X (blockMatVecMul E X) := by
      by_cases hX : X = 0
      · subst X
        simp [blockMatVecMul, blockVecDot, vecDot]
      · exact (hdag.refBlock_posDef X hX).le
    by_cases hS : S a ≤ (3 : ℝ) ^ (t + (G : ℤ))
    · -- good event
      have hcell := henv (t + (G : ℤ)) hS k w hsub X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell
      have hind : bad.indicator nss a = 0 := by
        refine Set.indicator_of_notMem ?_ nss
        rw [hbaddef, Set.mem_ofPred_eq]
        exact not_lt.mpr hS
      rw [hind, hc0]
      nlinarith only [hcell, hquad, hbC0]
    · -- bad event: run the crude branch of the established envelope
      push Not at hS
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
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Int.le_ceil _)
      have hsub' : adaptedCellAt (roundedGrid l n) k w ⊆
          centeredCube d m :=
        hsub.trans (Window.centeredCube_mono hm1)
      have hcell2 := henv m hm2 k w hsub' X
      rw [Sharp.blockVecDot_blockMatVecMul_blockScale] at hcell2
      have hcell : blockVecDot X (blockMatVecMul
          (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ≤
          boundaryConst Cd g n *
            (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) *
            blockVecDot X (blockMatVecMul E X) := by
        linarith only [hcell2]
      refine le_trans hcell ?_
      refine mul_le_mul_of_nonneg_right ?_ hquad
      have hchain : (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) ≤
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
            nss a := by
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
        have hmS : (3 : ℝ) ^ ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ)) ≤
            nss a := by
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
          rw [hnssdef, normalizedSourceScale]
          exact le_max_right _ _
        calc
          (3 : ℝ) ^ (g * ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ))) =
              ((3 : ℝ) ^ ((m : ℝ) - ((t + (G : ℤ) : ℤ) : ℝ))) ^ g := by
            rw [mul_comm g, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
          _ ≤ nss a ^ g := by
            refine Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
              hmS hg.1
          _ ≤ nss a ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (hnss1 a) hg.2.le
          _ = nss a := Real.rpow_one _
      have hind : bad.indicator nss a = nss a := by
        refine Set.indicator_of_mem ?_ nss
        rw [hbaddef, Set.mem_ofPred_eq]
        exact hS
      calc
        boundaryConst Cd g n * (3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ))) ≤
            boundaryConst Cd g n *
              ((3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
                nss a) :=
          mul_le_mul_of_nonneg_left hchain hbC0.le
        _ ≤ c0 * (1 + bad.indicator nss a) := by
          rw [hc0, hind]
          have hnss0 : 0 ≤ nss a := le_trans zero_le_one (hnss1 a)
          nlinarith only [hnss0, hc00, hbC0,
            Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3)
              (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ)))]
  -- the indicator's first moment
  exact hscalar
/-- **The entry-collapsed annealed envelope**: past the burn-in by the
logarithm of the second source moment, the annealed aligned cell is
dominated by the reference with the deterministic scale-adapted factor and
the absolute constant `2`. -/
theorem annealedBlock_adaptedCell_le_scaled_entry [NeZero d]
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
    (hentry : sourceMomentTwo K ≤ (3 : ℝ) ^ (t + (G : ℤ) - sK))
    (hsub : adaptedCellAt (roundedGrid l n) k w ⊆
      centeredCube d (t + (G : ℤ)))
    (hint : HasIntegrableCoarseBlock P
      (adaptedCellAt (roundedGrid l n) k w)) :
    BlockMatLoewnerLE
      (annealedBlock P (adaptedCellAt (roundedGrid l n) k w))
      (blockScale
        (2 * boundaryConst Cd g n *
          (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ)))) E) := by
  classical
  have hCd1 : (1 : ℝ) ≤ Cd := (le_max_left _ _).trans hCd
  have hbC0 : 0 < boundaryConst Cd g n :=
    Transport.zero_lt_boundaryConst (by linarith only [hCd1]) hg.2 hn
  set c0 : ℝ := boundaryConst Cd g n *
    (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) with hc0
  have hc00 : 0 ≤ c0 :=
    mul_nonneg hbC0.le (Real.rpow_nonneg (by norm_num) _)
  set tau : ℝ := (3 : ℝ) ^ (t + (G : ℤ) - sK) with htaudef
  have htau0 : 0 < tau := zpow_pos (by norm_num) _
  set bad : Set (CoeffSpace d) :=
    {a | (3 : ℝ) ^ (t + (G : ℤ)) < S a} with hbaddef
  have hbadmeas : MeasurableSet bad :=
    measurableSet_lt measurable_const hdag.source_measurable
  set nss : CoeffSpace d → ℝ := normalizedSourceScale S sK with hnssdef
  have hnss1 : ∀ a, 1 ≤ nss a := fun a =>
    one_le_normalizedSourceScale S sK a
  have hnssmeas : Measurable nss :=
    Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  -- on the bad event the normalized scale exceeds the threshold
  have hnss_tau : ∀ a ∈ bad, tau ≤ nss a := by
    intro a ha
    rw [hbaddef, Set.mem_ofPred_eq] at ha
    have h3sK : (0 : ℝ) < (3 : ℝ) ^ sK :=
      lt_of_lt_of_le (by norm_num) ((le_max_left 2 K).trans hsK)
    have h1 : tau * (3 : ℝ) ^ sK ≤ S a := by
      rw [htaudef, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      have heq : t + (G : ℤ) - sK + sK = t + (G : ℤ) := by ring
      rw [heq]
      exact ha.le
    have h2 : tau ≤ S a * (3 : ℝ) ^ (-sK) := by
      calc tau = tau * (3 : ℝ) ^ sK * (3 : ℝ) ^ (-sK) := by
            rw [mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            simp
        _ ≤ S a * (3 : ℝ) ^ (-sK) := by
          refine mul_le_mul_of_nonneg_right h1 ?_
          positivity
    refine le_trans h2 ?_
    rw [hnssdef, normalizedSourceScale]
    exact le_max_right _ _
  -- the pathwise majorant
  have hscalar :=
    adapted_cell_pathwise_source_envelope hd hg hdag hl hCd hn t
      hDelta hsub hbC0 hc00 hnss1
  have hindsq : ∀ a, bad.indicator nss a ≤ tau⁻¹ * nss a ^ 2 := by
    intro a
    by_cases ha : a ∈ bad
    · rw [Set.indicator_of_mem ha]
      have h1 := hnss_tau a ha
      have hnss0 : 0 ≤ nss a := le_trans zero_le_one (hnss1 a)
      rw [← sub_nonneg] at h1
      rw [← sub_nonneg]
      have hkey : tau⁻¹ * nss a ^ 2 - nss a =
          tau⁻¹ * (nss a * (nss a - tau)) := by
        field_simp
      rw [hkey]
      exact mul_nonneg (inv_nonneg.mpr htau0.le)
        (mul_nonneg hnss0 (by linarith only [h1]))
    · rw [Set.indicator_of_notMem ha]
      positivity
  have hindint : Integrable (fun a => bad.indicator nss a) P := by
    refine (Integrable.indicator ?_ hbadmeas).congr
      (_root_.Filter.Eventually.of_forall fun a => rfl)
    exact integrable_normalizedSourceScale hdag hsK
  have hindmom : ∫ a, bad.indicator nss a ∂P ≤ 1 := by
    have h1 : ∫ a, bad.indicator nss a ∂P ≤
        ∫ a, tau⁻¹ * nss a ^ 2 ∂P := by
      refine integral_mono hindint ?_ hindsq
      exact (integrable_sq_normalizedSourceScale hdag hsK).const_mul _
    refine le_trans h1 ?_
    rw [integral_const_mul]
    have h2 := integral_sq_normalizedSourceScale_le hdag hsK
    have h3 : tau⁻¹ * (∫ a, nss a ^ 2 ∂P) ≤ tau⁻¹ * sourceMomentTwo K :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr htau0.le)
    refine le_trans h3 ?_
    rw [inv_mul_le_iff₀ htau0, mul_one]
    rw [htaudef]
    exact hentry
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
  have hint2 : Integrable (fun a => c0 * (1 + bad.indicator nss a) *
      blockVecDot X (blockMatVecMul E X)) P := by
    have h := (((integrable_const (1 : ℝ)).add hindint).const_mul
      c0).mul_const (blockVecDot X (blockMatVecMul E X))
    refine h.congr (_root_.Filter.Eventually.of_forall fun a => ?_)
    simp only [Pi.add_apply]
  have hmono := integral_mono_ae hint1 hint2 (by
    filter_upwards [hscalar] with a ha using ha X)
  have hsplit : ∫ a, c0 * (1 + bad.indicator nss a) *
      blockVecDot X (blockMatVecMul E X) ∂P =
      c0 * (1 + ∫ a, bad.indicator nss a ∂P) *
        blockVecDot X (blockMatVecMul E X) := by
    rw [show (fun a => c0 * (1 + bad.indicator nss a) *
        blockVecDot X (blockMatVecMul E X)) =
        fun a => c0 * blockVecDot X (blockMatVecMul E X) +
          (c0 * blockVecDot X (blockMatVecMul E X)) *
            bad.indicator nss a from by
      funext a
      ring]
    rw [integral_add (integrable_const _) (hindint.const_mul _),
      integral_const, probReal_univ, one_smul, integral_const_mul]
    ring
  have hco : c0 * (1 + ∫ a, bad.indicator nss a ∂P) ≤
      2 * boundaryConst Cd g n *
        (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) := by
    have h1 : c0 * (1 + ∫ a, bad.indicator nss a ∂P) ≤ c0 * 2 := by
      refine mul_le_mul_of_nonneg_left ?_ hc00
      linarith only [hindmom]
    refine h1.trans (le_of_eq ?_)
    rw [hc0]
    ring
  have hfinal : ∫ a, blockVecDot X (blockMatVecMul
      (coarseBlock (adaptedCellAt (roundedGrid l n) k w) a) X) ∂P ≤
      2 * boundaryConst Cd g n *
        (3 : ℝ) ^ (g * (((t + (G : ℤ) : ℤ) : ℝ) - (k : ℝ))) *
        blockVecDot X (blockMatVecMul E X) := by
    refine le_trans hmono ?_
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hco hquadE
  linarith only [hfinal]

end

end HCPolySupport.HighContrast.Quenched
