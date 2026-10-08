/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBadLevelResidue
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyLpBadAtLevel

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakEnergyTailAtLevel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The moment package at the matched threshold, and the bad energy it produces

The maximal function's almost-sure envelope is `R · (max 1 x) ^ g / 2`.  The
fixed-level package takes the excess above `1 / 2`, which is strictly below the
envelope's own value on the good set, so a generation-independent constant
survives the good part of the moment split.

Here the excess is taken above `R / 2`, the envelope's value on the good set.
The good part of the split then contributes nothing at all, and the fourth
moment is the bad part alone — `R ^ 4` times the source's crude moment, with no
additive term.  The bad-event level stays free: the majorant's small-drift
branch is guarded by `beta < lev`, and the matched threshold `beta = R / 2`
needs a level above it.

Everything else in the argument is the fixed-level one, term for term: the
scale identity, the bad-event envelope for the excess, and the source's crude
moment are all read at the same places.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

private theorem source_scale_delay_identity
    (S : CoeffSpace d → ℝ) (t sK Delta : ℤ) (G : ℕ)
    (hDeltadef : Delta = t + (G : ℤ) - 1 - sK) :
    ∀ a, 3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))) =
      S a * (3 : ℝ) ^ (-sK) * (3 : ℝ) ^ (-Delta) := by
  classical
  have hXeq : ∀ a, 3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))) =
      S a * (3 : ℝ) ^ (-sK) * (3 : ℝ) ^ (-Delta) := by
    intro a
    rw [← Real.rpow_intCast (3 : ℝ) (-sK),
      ← Real.rpow_intCast (3 : ℝ) (-Delta)]
    rw [show (3 : ℝ) * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))) =
        S a * ((3 : ℝ) ^ (1 : ℝ) * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ)))) from by
      rw [Real.rpow_one]
      ring]
    rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [hDeltadef]
    push_cast
    ring_nf
  exact hXeq

/-- **The moment package at the matched threshold.**  The excess above `R / 2`,
its fourth moment against `R ^ 4` times the crude moment — with no residue —
and the maximum's own `L⁴` norm. -/
theorem weakMaximum_moment_package_at
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    {rho : ℝ} (t : ℤ) {G : ℕ}
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {R : ℝ} (hR1 : 1 ≤ R)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    :
    ∃ W : CoeffSpace d → ℝ≥0∞, AEMeasurable W P ∧
      (∀ a, Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        W a + ENNReal.ofReal (R / 2)) ∧
      eLpNorm (Response.diagonalWeakMaximum rho (roundedGrid l n) t F)
          (ENNReal.ofReal 4) P ≤
        ENNReal.ofReal
          ((R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) ^
              ((4 : ℝ)⁻¹) + R / 2) ∧
      ∫⁻ a, W a ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK)) := by
  classical
  set Delta : ℤ := t + (G : ℤ) - 1 - sK with hDeltadef
  have hq : (roundedGrid l n).PosDef := Recurrence.posDef_roundedGrid hl hn
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR1]
  set M : CoeffSpace d → ℝ≥0∞ := fun a =>
    Response.diagonalWeakMaximum rho (roundedGrid l n) t F a with hM
  set W : CoeffSpace d → ℝ≥0∞ := fun a =>
    M a - ENNReal.ofReal (R / 2) with hW
  have hMmeas : AEMeasurable M P := by
    rw [hM]
    exact Response.aemeasurable_diagonalWeakMaximum hq hFsym hFpd
  have hWmeas : AEMeasurable W P := by
    rw [hW]
    exact hMmeas.sub aemeasurable_const
  have hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal (R / 2) := by
    intro a
    change M a ≤ M a - ENNReal.ofReal (R / 2) + ENNReal.ofReal (R / 2)
    exact le_tsub_add
  have hmeasSet : MeasurableSet
      {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a} := by
    refine measurableSet_lt measurable_const ?_
    exact Measurable.max measurable_const (hdag.source_measurable.mul_const _)
  -- the scale identity `3·S·3^{-(t+G)} = (S·3^{-s_K})·3^{-Δ}`
  have hXeq := source_scale_delay_identity S t sK Delta G hDeltadef
  have h3D1 : (1 : ℝ) ≤ (3 : ℝ) ^ Delta := by
    rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) from by norm_num]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  -- the bad-event envelope for the excess
  have hWbad : ∀ᵐ a ∂P,
      a ∈ {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a} →
      W a ≤ ENNReal.ofReal
        ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^ g * (R / 2)) := by
    filter_upwards [henvMax] with a hMa hcase
    have hVS : normalizedSourceScale S sK a = S a * (3 : ℝ) ^ (-sK) := by
      rw [normalizedSourceScale]
      refine max_eq_right ?_
      have hcase' := hcase
      rw [normalizedSourceScale] at hcase'
      rcases lt_max_iff.mp hcase' with h1 | h2
      · linarith only [h1, h3D1]
      · linarith only [h2, h3D1]
    have hmax : max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ)))) =
        normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta) := by
      rw [hXeq a, ← hVS]
      refine max_eq_right ?_
      rw [show (1 : ℝ) = (3 : ℝ) ^ Delta * (3 : ℝ) ^ (-Delta) from by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        simp]
      exact mul_le_mul_of_nonneg_right (le_of_lt hcase) (by positivity)
    change M a - ENNReal.ofReal (R / 2) ≤ _
    refine le_trans tsub_le_self (le_trans hMa (le_of_eq ?_))
    rw [hmax]
    congr 1
    ring
  -- the good event: the matched threshold leaves nothing behind
  have hMgood : ∀ᵐ a ∂P,
      a ∉ {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a} →
      M a ≤ ENNReal.ofReal (R / 2) := by
    filter_upwards [henvMax] with a hMa hcase
    push Not at hcase
    have hle1 : 3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))) ≤ 1 := by
      rw [hXeq a]
      have hS3 : S a * (3 : ℝ) ^ (-sK) ≤ (3 : ℝ) ^ Delta :=
        le_trans (le_max_right 1 _) hcase
      calc
        S a * (3 : ℝ) ^ (-sK) * (3 : ℝ) ^ (-Delta) ≤
            (3 : ℝ) ^ Delta * (3 : ℝ) ^ (-Delta) :=
          mul_le_mul_of_nonneg_right hS3 (by positivity)
        _ = 1 := by
          rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
    refine le_trans hMa (le_of_eq ?_)
    rw [max_eq_left hle1, Real.one_rpow]
    congr 1
    ring
  -- the fourth moment of the excess is the bad part alone
  have hmom : ∫⁻ a, W a ^ (4 : ℝ) ∂P ≤
      ENNReal.ofReal (R ^ 4 * badMomentMajorant K Delta) := by
    have hrestrict : ∫⁻ a, W a ^ (4 : ℝ) ∂P =
        ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
          W a ^ (4 : ℝ) ∂P :=
      lintegral_pow_eq_setLIntegral_of_matched_threshold (P := P)
        (Q := (4 : ℝ)) (beta := R / 2) (by norm_num) hmeasSet
        (fun a => rfl) hMgood
    have hbadpow : ∀ᵐ a ∂P,
        a ∈ {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a} →
        W a ^ (4 : ℝ) ≤ ENNReal.ofReal (R ^ 4 / 16) *
          ENNReal.ofReal
            ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
              ((4 : ℕ) : ℝ)) := by
      filter_upwards [hWbad] with a hWa hcase
      have hcase' := hcase
      have hbase1 : (1 : ℝ) ≤ normalizedSourceScale S sK a *
          (3 : ℝ) ^ (-Delta) := by
        rw [show (1 : ℝ) = (3 : ℝ) ^ Delta * (3 : ℝ) ^ (-Delta) from by
          rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp]
        exact mul_le_mul_of_nonneg_right (le_of_lt hcase') (by positivity)
      have hxnn : (0 : ℝ) ≤ normalizedSourceScale S sK a *
          (3 : ℝ) ^ (-Delta) := by linarith only [hbase1]
      calc
        W a ^ (4 : ℝ) ≤
            (ENNReal.ofReal
              ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^ g *
                (R / 2))) ^ (4 : ℝ) :=
          ENNReal.rpow_le_rpow (hWa hcase) (by norm_num)
        _ = ENNReal.ofReal
            (((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^ g *
              (R / 2)) ^ (4 : ℝ)) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        _ ≤ ENNReal.ofReal (R ^ 4 / 16) *
            ENNReal.ofReal
              ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
                ((4 : ℕ) : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hR4 : (R / 2) ^ (4 : ℝ) = R ^ 4 / 16 := by
            rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num,
              Real.rpow_natCast]
            ring
          rw [Real.mul_rpow (Real.rpow_nonneg hxnn _) (by positivity), hR4,
            ← Real.rpow_mul hxnn]
          have hexp : (normalizedSourceScale S sK a *
              (3 : ℝ) ^ (-Delta)) ^ (g * 4) ≤
              (normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
                ((4 : ℕ) : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hbase1 ?_
            have hg1 : g < 1 := hg.2
            push_cast
            linarith only [hg1]
          have hR40 : (0 : ℝ) ≤ R ^ 4 / 16 := by positivity
          have := mul_le_mul_of_nonneg_right hexp hR40
          linarith only [this]
    have hbad : ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
        W a ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (R ^ 4) * ENNReal.ofReal (badMomentMajorant K Delta) := by
      calc
        ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
            W a ^ (4 : ℝ) ∂P ≤
            ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
              ENNReal.ofReal (R ^ 4 / 16) *
                ENNReal.ofReal
                  ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
                    ((4 : ℕ) : ℝ)) ∂P := by
          refine lintegral_mono_ae ((ae_restrict_iff' hmeasSet).mpr ?_)
          filter_upwards [hbadpow] with a ha hmem
          exact ha hmem
        _ = ENNReal.ofReal (R ^ 4 / 16) *
            ∫⁻ a in {a | (3 : ℝ) ^ Delta < normalizedSourceScale S sK a},
              ENNReal.ofReal
                ((normalizedSourceScale S sK a * (3 : ℝ) ^ (-Delta)) ^
                  ((4 : ℕ) : ℝ)) ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (R ^ 4 / 16) *
            (ENNReal.ofReal ((3 : ℝ) ^ (-((2 : ℕ) * (Delta : ℝ)))) *
              ENNReal.ofReal
                (1 + 2 * ((4 + 2 : ℕ) : ℝ) *
                  (1 + Real.log (growthBar K)) *
                  growthBar K ^ IndependentSums.natTriangular (4 + 2))) :=
          mul_le_mul' le_rfl
            (setLintegral_normalizedSourceScale_pow_le hdag hsK 4 2
              (by norm_num) hDelta)
        _ = ENNReal.ofReal (R ^ 4) *
            ENNReal.ofReal (badMomentMajorant K Delta) := by
          rw [← ENNReal.ofReal_mul
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ R ^ 4 / 16),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ R ^ 4)]
          congr 1
          rw [badMomentMajorant, sourceMomentSix]
          push_cast
          ring
    have hbm0 : (0 : ℝ) ≤ badMomentMajorant K Delta := badMomentMajorant_nonneg K Delta
    rw [hrestrict, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ R ^ 4)]
    exact hbad
  -- the moment norm
  have hnorm : eLpNorm M (ENNReal.ofReal 4) P ≤
      ENNReal.ofReal
        ((R ^ 4 * badMomentMajorant K Delta) ^ ((4 : ℝ)⁻¹) + R / 2) := by
    have h1 : eLpNorm M (ENNReal.ofReal 4) P ≤
        eLpNorm (fun a => W a + ENNReal.ofReal (R / 2))
          (ENNReal.ofReal 4) P := by
      refine eLpNorm_mono_enorm hMmeas.aestronglyMeasurable fun a => ?_
      simp only [enorm_eq_self]
      exact hpoint a
    refine le_trans h1 ?_
    refine le_trans (eLpNorm_add_le (by
        rw [show ((1 : ℝ≥0∞)) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
        exact ENNReal.ofReal_le_ofReal (by norm_num))) ?_
    rw [eLpNorm_const_four]
    have hh0 : (0 : ℝ) ≤ R ^ 4 * badMomentMajorant K Delta := by
      have := badMomentMajorant_nonneg K Delta
      positivity
    refine le_trans
      (add_le_add (eLpNorm_four_le_of_lintegral_le hh0 hmom hWmeas) le_rfl) ?_
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg hh0 _) (by positivity)]
  exact ⟨W, hWmeas, hpoint, hnorm, hmom⟩

/-! ## The bad energies at the matched threshold -/

/-- **The primal bad-event energy at the matched threshold and a free level.**
The residue-free majorant `R ^ 4 · badMomentMajorant` in place of the scaled
one, at the threshold pair `(R / 2, lev)`. -/
theorem profileBadEnergyAt_of_maximum_envelope
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    {rho : ℝ} (t : ℤ) {G : ℕ}
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    (p r : Vec d) :
    Response.profileBadEnergyAt P (ENNReal.ofReal lev)
      (Response.diagonalWeakMaximum rho (roundedGrid l n) t F)
      (fun a => Response.diagonalWeakEnergy
        (Recurrence.posDef_roundedGrid hl hn) t a p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        Response.profileEnergyLoad (Response.diagonalWeakLoadMinus F p r) p r *
        Response.profileBadMajorantAt 4
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK))
          (R / 2) lev) := by
  obtain ⟨W, hWmeas, hpoint, hnorm, hmom⟩ :=
    weakMaximum_moment_package_at hg hdag hl hn t hsK hDelta hFsym hFpd hR1
      henvMax
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR1]
  have hh0 : (0 : ℝ) ≤ R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK) := by
    have := badMomentMajorant_nonneg K (t + (G : ℤ) - 1 - sK)
    positivity
  exact Response.profileBadEnergyAt_diagonalWeakEnergy_le
    (by norm_num : (2 : ℝ) < 4) hh0 (by linarith only [hR0]) hlev
    (Recurrence.posDef_roundedGrid hl hn) hFsym hFpd hWmeas hpoint hnorm hmom p r

/-- **The adjoint bad-event energy at the matched threshold and a free
level.**  The same package, the mirrored load. -/
theorem profileBadEnergyAt_adjoint_of_maximum_envelope
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} (hl : (kZero d : ℤ) ≤ l)
    {n : Mat d} (hn : n.PosDef)
    {rho : ℝ} (t : ℤ) {G : ℕ}
    {sK : ℤ} (hsK : growthBar K ≤ (3 : ℝ) ^ sK)
    (hDelta : 0 ≤ t + (G : ℤ) - 1 - sK)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {R lev : ℝ} (hR1 : 1 ≤ R) (hlev : 1 ≤ lev)
    (henvMax : ∀ᵐ a ∂P,
      Response.diagonalWeakMaximum rho (roundedGrid l n) t F a ≤
        ENNReal.ofReal (R *
          ((max 1 (3 * S a * (3 : ℝ) ^ (-((t : ℝ) + (G : ℝ))))) ^ g / 2)))
    (p r : Vec d) :
    Response.profileBadEnergyAt P (ENNReal.ofReal lev)
      (Response.diagonalWeakMaximum rho (roundedGrid l n) t F)
      (fun a => Response.diagonalWeakAdjointEnergy
        (Recurrence.posDef_roundedGrid hl hn) t a p r) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        Response.profileEnergyLoad (Response.diagonalWeakLoadPlus F p r) p r *
        Response.profileBadMajorantAt 4
          (R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK))
          (R / 2) lev) := by
  obtain ⟨W, hWmeas, hpoint, hnorm, hmom⟩ :=
    weakMaximum_moment_package_at hg hdag hl hn t hsK hDelta hFsym hFpd hR1
      henvMax
  have hR0 : (0 : ℝ) ≤ R := by linarith only [hR1]
  have hh0 : (0 : ℝ) ≤ R ^ 4 * badMomentMajorant K (t + (G : ℤ) - 1 - sK) := by
    have := badMomentMajorant_nonneg K (t + (G : ℤ) - 1 - sK)
    positivity
  exact Response.profileBadEnergyAt_diagonalWeakAdjointEnergy_le
    (by norm_num : (2 : ℝ) < 4) hh0 (by linarith only [hR0]) hlev
    (Recurrence.posDef_roundedGrid hl hn) hFsym hFpd hWmeas hpoint hnorm hmom p r

end

end HCPolySupport.HighContrast.Quenched
