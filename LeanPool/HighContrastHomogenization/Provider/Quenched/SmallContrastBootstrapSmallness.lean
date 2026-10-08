/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapReference
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapTilt
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedContrastAntitone
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterAssembly

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBootstrapSmallness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bootstrap smallness of the hatted carrier

The recursion of the small-contrast argument runs on `F(n) = d(hatΘ_n − 1)`
and needs a *uniform* smallness `F ≤ δ` over the whole range it iterates on.
The only smallness the proposition assumes is Euclidean and at generation
zero: `Θ_0 − 1 ≤ c_*`.

The transfer is the adapted-to-Euclidean adapter run in the descending
direction: at generation `n` compare the adapted mean with the annealed block
of the centered cube a fixed `gap` of scales earlier.  The comparison error
carries `3^{−gap}` and is absorbed multiplicatively; the Euclidean hatted
defect at the earlier cube is below `c_*` because the annealed intrinsic
contrast is antitone and dominates the hatted carrier.  The absorbed size is
`c·|𝐄 : 𝐀(□_k)|`, and the second factor is the generation-free Euclidean
reference ratio, so a single `gap` — logarithmic in the law constants —
serves every generation past the source burn.

Nothing in this file is a window estimate: the account, the coupled window and
the profile caps play no role.  What is used is the two-sided
Euclidean adapter, the Dagger envelope through the reference ratio, the tilt
scalarization, and the annealed antitone comparison.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The source gauge of the adapted-to-Euclidean adapter is bounded, at every
nonnegative scale, by its value at scale zero. -/
theorem transferGauge_le_bar {g K : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1)
    {j : ℤ} (hj : 0 ≤ j) :
    transferGauge g K j ≤ (1 - g)⁻¹ * (1 + K ^ 2) ^ g := by
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg.2]
  have h3 : (3 : ℝ) ^ (-j) ≤ 1 := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega : -j ≤ (0 : ℤ))
    simpa using h
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ (-j) := by positivity
  have hbase : 1 + K ^ 2 * (3 : ℝ) ^ (-j) ≤ 1 + K ^ 2 := by
    nlinarith only [h3, h3pos, sq_nonneg K]
  have hbase0 : (0 : ℝ) ≤ 1 + K ^ 2 * (3 : ℝ) ^ (-j) := by positivity
  rw [transferGauge]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase0 hbase hg.1)
    (inv_nonneg.mpr hgpos.le)

/-- The law-side factor of the bootstrap adapter error: the grid eccentricity,
the source-gauge cap and the Euclidean reference ratio. -/
@[expose]
def bootstrapAdapterFactor (Cd g K : ℝ) (E : BlockMat d) (mAl : Mat d) : ℝ :=
  witnessEccentricity mAl *
    ((1 + K ^ 2) ^ g * euclideanReferenceRatio Cd g K E)

/-- **The bootstrap tilt bound.**  With the alignment-free triadic gap chosen
so that the absorbed adapter error is below `σ`, the hatted defect of the
adapted mean at every generation past the source burn plus the gap is bounded
by the tilt polynomial at `σ` and `d c_*`. -/
theorem exists_bootstrap_tilt_bound (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ Cd : ℝ, max 1 (12 * (d : ℝ) * Real.sqrt d) ≤ Cd →
          ∀ sK : ℤ, 0 ≤ sK → growthBar K ≤ (3 : ℝ) ^ sK →
            ∀ lq : ℤ, (kZero d : ℤ) ≤ lq → ∀ mAl : Mat d, mAl.PosDef →
              ∀ sigma cStar : ℝ, annealedContrast P 0 - 1 ≤ cStar →
                ∀ gap : ℤ, 1 ≤ gap →
                  CB * bootstrapAdapterFactor Cd g K E mAl *
                      (3 : ℝ) ^ (-(gap : ℝ)) ≤ sigma →
                  ∀ n : ℤ, sK + 1 + gap ≤ n →
                    (d : ℝ) *
                        (adaptedHattedContrast P (roundedGrid lq mAl) n - 1) ≤
                      (d : ℝ) *
                        bootstrapTiltPolynomial sigma ((d : ℝ) * cStar) := by
  classical
  obtain ⟨CAE, hCAE0, hCAE⟩ := Entry.exists_euclidean_adapter d hd g hg
  have hgpos : (0 : ℝ) < 1 - g := by linarith only [hg.2]
  refine ⟨CAE * (1 - g)⁻¹, mul_pos hCAE0 (inv_pos.mpr hgpos), ?_⟩
  intro P E Ψ K S hP hstat hunit hdag Cd hCd sK hsK0 hsK lq hlq mAl hmAl sigma
    cStar hsmall gap hgap hsigma n hn
  have : NeZero d := ⟨by omega⟩
  have := hP
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set k : ℤ := n - gap with hkdef
  have hk0 : 0 ≤ k := by omega
  have hkn : k < n := by omega
  have hkburn : sK + 1 ≤ k := by omega
  obtain ⟨hfwd, -⟩ := hCAE P E Ψ K S hP hstat hunit hdag lq hlq mAl hmAl
    k n (n + 1) hk0 hkn (by omega)
  -- the two constant inputs
  obtain ⟨hone, -⟩ :=
    reference_le_annealedBlock_centeredCube hd hg hdag hCd hsK hkburn
  have hsize := blockSize_reference_adaptedMean_one_le hd hg hdag hCd hsK hkburn
  have hecc1 : (1 : ℝ) ≤ witnessEccentricity mAl :=
    Initialization.one_le_witnessEccentricity hmAl
  have hecc0 : (0 : ℝ) ≤ witnessEccentricity mAl := by linarith only [hecc1]
  have hR0 : (0 : ℝ) ≤ euclideanReferenceRatio Cd g K E := by
    linarith only [hone]
  have hTG0 : (0 : ℝ) < transferGauge g K k := by
    rw [transferGauge]
    have hb : (0 : ℝ) < 1 + K ^ 2 * (3 : ℝ) ^ (-k) := by positivity
    exact mul_pos (inv_pos.mpr hgpos) (Real.rpow_pos_of_pos hb g)
  have hgauge := transferGauge_le_bar (K := K) hg hk0
  have hpexp : -((n : ℝ) - (k : ℝ)) = -(gap : ℝ) := by
    rw [hkdef]
    push_cast
    ring
  have hp0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hc0 : (0 : ℝ) ≤
      CAE * witnessEccentricity mAl * transferGauge g K k *
        (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCAE0.le hecc0) hTG0.le) hp0
  have hae0 : (0 : ℝ) ≤ CAE * witnessEccentricity mAl :=
    mul_nonneg hCAE0.le hecc0
  -- the absorbed adapter size is below the tolerance
  have hstep1 : CAE * witnessEccentricity mAl * transferGauge g K k ≤
      CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) :=
    mul_le_mul_of_nonneg_left hgauge hae0
  have hstep2 :
      CAE * witnessEccentricity mAl * transferGauge g K k *
          (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) ≤
        CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) *
          (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) :=
    mul_le_mul_of_nonneg_right hstep1 hp0
  have hstep3 :
      CAE * witnessEccentricity mAl * transferGauge g K k *
            (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) *
          euclideanReferenceRatio Cd g K E ≤
        CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) *
            (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) *
          euclideanReferenceRatio Cd g K E :=
    mul_le_mul_of_nonneg_right hstep2 hR0
  have hid :
      CAE * witnessEccentricity mAl * ((1 - g)⁻¹ * (1 + K ^ 2) ^ g) *
            (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) *
          euclideanReferenceRatio Cd g K E =
        CAE * (1 - g)⁻¹ * bootstrapAdapterFactor Cd g K E mAl *
          (3 : ℝ) ^ (-(gap : ℝ)) := by
    rw [bootstrapAdapterFactor, hpexp]
    ring
  have heta :
      CAE * witnessEccentricity mAl * transferGauge g K k *
          (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ))) *
        blockSize E (adaptedMean P (1 : Mat d) k) ≤ sigma := by
    have hleft := mul_le_mul_of_nonneg_left hsize hc0
    rw [hid] at hstep3
    linarith only [hleft, hstep3, hsigma]
  -- the Euclidean hatted defect at the earlier cube
  have hann : annealedContrast P k ≤ annealedContrast P 0 :=
    annealedContrast_le_of_nonneg_of_le hstat hdag le_rfl hk0
  have hhatk : adaptedHattedContrast P (1 : Mat d) k - 1 ≤ cStar :=
    adaptedHattedContrast_one_sub_one_le_of_annealedContrast_sub_one_le hdag k
      (by linarith only [hann, hsmall])
  have hxk : (d : ℝ) * (adaptedHattedContrast P (1 : Mat d) k - 1) ≤
      (d : ℝ) * cStar :=
    mul_le_mul_of_nonneg_left hhatk (Nat.cast_nonneg d)
  -- finiteness of the two adapted means
  have hfin1 : HasFiniteAdaptedMean P (1 : Mat d) k :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag Matrix.PosDef.one k).1
  have hfinq : HasFiniteAdaptedMean P (roundedGrid lq mAl) n :=
    (finite_adaptedMean_of_coarseEllipticityDagger hdag
      (Recurrence.posDef_roundedGrid hlq hmAl) n).1
  exact adaptedHattedContrast_sub_one_le_of_euclidean_adapter
    hdag.refBlock_isSymm hdag.refBlock_posDef
    (⟨hlq, mAl, hmAl, rfl⟩ : IsRoundedGrid lq (roundedGrid lq mAl))
    hfinq hfin1 hc0 hfwd heta hxk

end

end HCPolySupport.HighContrast.Quenched
