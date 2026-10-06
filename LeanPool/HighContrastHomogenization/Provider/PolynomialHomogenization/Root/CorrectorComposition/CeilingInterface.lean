/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RootInterface.ProviderSurface

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CeilingInterface

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the ceiling-exporting smallness interface The ceiling-exporting corrector-smallness interface

The root's single exported length forces a single corrector smallness `c`, and
the certificate is *increasing* in `c` (so no uniform downward choice exists).
The fix is a **ceiling-exporting** interface:

* `GoodScale : ℝ → ℝ → ℝ → Mat d → CoeffSpace d → ℝ → Prop`, read
  `GoodScale g c κ abar a x`;
* each hole exports `∃ cMax ∈ Ioo 0 1, ∀ c ∈ Ioo 0 1, c ≤ cMax → …`;
* the assembly instantiates at the minimum of the five ceilings;
* `hhomogenized` gains `∀ c ∈ Ioo 0 1 →` before its `∃ kappaRate Lcert pCert`,
  with `Lcert` allowed to depend on `c` — and it must, because `Lcert` contains
  `certAmplitudeBase … / correctorTargetAmplitude c κ`.

This module implements that interface.  `rootGoodScaleAt` is the
`c`-parameterised certificate; `exists_rootGoodScaleAt_of_quenchedRow` is the
`c`-parameterised `hhomogenized`, obtained from the `RootInterface` proof by
replacing its fixed `c := 1/2` with the bound variable; and
`minCeiling_mem` / `le_minCeiling_*` are the arithmetic the assembly needs to
instantiate at the minimum of five ceilings.

The body of `exists_rootGoodScaleAt_of_quenchedRow` is the fixed-threshold
argument with `1 / 2` generalised to a leading binder.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory
open RootInterface
open RowSupply (eccentricityFoldFactor one_le_eccentricityFoldFactor
  witnessEccentricity_nonneg)

noncomputable section

variable {d : ℕ}

/-- **The `c`-parameterised root certificate.**  Identical to
`RootInterface.RootGoodScale` except that the corrector smallness is a binder
rather than an existential, so a consumer can demand its own ceiling. -/
@[expose]
def rootGoodScaleAt (d : ℕ) [NeZero d] (g c kappaRate : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop :=
  ∃ h : RowSupply.RowRetainingPrintOrderGoodScale d g c kappaRate abar a x,
    c ∈ Set.Ioo (0 : ℝ) 1 ∧ h.delta ∈ Set.Ioo (0 : ℝ) 1

/-- Forgetting the smallness parameter recovers the `RootInterface` certificate,
so every consumer of the unparameterised interface still applies. -/
theorem rootGoodScale_of_rootGoodScaleAt [NeZero d] {g c kappaRate : ℝ}
    {abar : Mat d} {a : CoeffSpace d} {x : ℝ}
    (h : rootGoodScaleAt d g c kappaRate abar a x) :
    RootInterface.RootGoodScale d g kappaRate abar a x := by
  obtain ⟨hh, hc, hdelta⟩ := h
  exact ⟨c, hh, hc, hdelta⟩

/-- **`hhomogenized`, at every corrector smallness.**  The exported length
factor `Lcert` depends on `c`; the exported exponent `pCert` does not. -/
theorem exists_rootGoodScaleAt_of_quenchedRow (d : ℕ) [NeZero d]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {c kappa delta : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hkappa : 0 < kappa) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ kappaRate Lcert pCert : ℝ,
      0 < kappaRate ∧ kappaRate ≤ (1 + g) / 4 ∧
      1 ≤ Lcert ∧ 0 ≤ pCert ∧
      ∀ (abar : Mat d), (symmPart abar).PosDef →
        ∀ (S X : CoeffSpace d → ℝ) (a : CoeffSpace d),
          Quenched.HasAllLaterPhysicalBlockRow ((1 + 3 * g) / 4)
              kappa delta (Book.Ch02.constantBlockMatrix abar) S X a →
          1 ≤ X a → S a ≤ X a →
          rootGoodScaleAt d g c kappaRate abar a
            (X a * (Lcert * eccentricityFoldFactor abar pCert)) := by
  classical
  set kR : ℝ := rootCertificateRate g kappa with hkRdef
  have hkR : 0 < kR := rootCertificateRate_pos hg hkappa
  have hkRle : kR ≤ (1 + g) / 4 := rootCertificateRate_le
  have hkRhalf : kR ≤ kappa / 2 := min_le_left _ _
  set target : ℝ := correctorTargetAmplitude c kR with htargetDef
  have htarget : 0 < target := correctorTargetAmplitude_pos hc.1 hkR
  have hmargins := printOrder_margins hg
  set s : ℝ := printCertificateOrder g with hsdef
  set rho : ℝ := printRowOrder g with hrhodef
  refine ⟨kR, rootCertAmplitude d s rho target kR, 2 * kR⁻¹, hkR, hkRle,
    one_le_rootCertAmplitude d hkR, by positivity, ?_⟩
  intro abar hS S X a hrow hXone hburn
  have hXpos : (0 : ℝ) < X a := lt_of_lt_of_le zero_lt_one hXone
  have hecc0 : 0 ≤ witnessEccentricity (symmPart abar) :=
    witnessEccentricity_nonneg _
  obtain ⟨G, hGlo, hGhi⟩ := Entry.exists_pow_three_bracket
    (x := witnessEccentricity (symmPart abar) * Real.sqrt d)
    (mul_nonneg hecc0 (Real.sqrt_nonneg d))
  set amp : ℝ := normalizedReferencePowerAmplitude d s rho delta G with hampdef
  have hampNonneg : 0 ≤ amp := by
    rw [hampdef]
    unfold normalizedReferencePowerAmplitude
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrowOrder : Quenched.HasAllLaterPhysicalBlockRow rho kappa delta
      (Book.Ch02.constantBlockMatrix abar) S X a := hrow
  obtain ⟨aRef, haRef, htail⟩ :=
    exists_normalizedReferencePowerTail_of_hasAllLaterPhysicalBlockRow
      a abar hS s rho kappa delta S X G hGlo hmargins.2.2.1 hmargins.2.2.2.1
      hmargins.2.2.2.2.2.2.1 hkappa hdelta.1.le hrowOrder hXone hburn
  have hcert : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amp (kappa / 2) (X a) a :=
    ⟨hS, aRef, hmargins.1, hmargins.2.1, hampNonneg, by positivity, hXone,
      haRef, htail⟩
  set M : ℝ := commonAffineMultiplier d amp target kR abar with hMdef
  have hM0 : 0 < M := commonAffineMultiplier_pos d hkR abar
  have hMbound : M ≤
      rootCertAmplitude d s rho target kR *
        eccentricityFoldFactor abar (2 * kR⁻¹) :=
    commonAffineMultiplier_le_fold hkR hmargins.2.2.1 hmargins.2.2.2.1
      hmargins.2.2.2.2.2.2.1 hdelta htarget hGhi
  set T : ℝ := X a * (rootCertAmplitude d s rho target kR *
    eccentricityFoldFactor abar (2 * kR⁻¹)) with hTdef
  have hTM : X a * M ≤ T := by
    rw [hTdef]
    exact mul_le_mul_of_nonneg_left hMbound hXpos.le
  have hy : X a ≤ T / M := by
    rw [le_div_iff₀ hM0]
    exact hTM
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hTM
  have hcert' : PrintOrderQuantitativeNormalizedReferenceCertificate
      abar g amp kR (T / M) a :=
    PrintOrderQuantitativeNormalizedReferenceCertificate.mono hcert hkR
      hkRhalf hy
  have hscale : T = commonQuantitativeAffineScale amp target kR
      (Transport.roundedOuterResponseAffineConstant d)
      (specBound (symmPart abar) * specBound (symmPart abar)⁻¹) kR
      (fun _ => T / M) a := by
    rw [commonQuantitativeAffineScale_eq_multiplier_mul, ← hMdef]
    field_simp
  have hgood : PrintOrderRateBearingCommonAffineGoodScale d g c kR
      abar a T := ⟨amp, fun _ => T / M, hcert', hscale⟩
  have hrowRate : (2 : ℝ) * kR ≤ kappa := by
    have := hkRhalf
    linarith only [this]
  have hrowRetained : Quenched.HasAllLaterPhysicalBlockRow
      (Certificate.printRowOrder g) (2 * kR) delta
      (Book.Ch02.constantBlockMatrix abar) S X a :=
    hasAllLaterPhysicalBlockRow_mono_rate hrowOrder hdelta.1.le hXpos hrowRate
  have hactivation : X a ≤ T := by
    rw [hTdef]
    exact le_mul_of_one_le_right hXpos.le
      (one_le_mul_of_one_le_of_one_le (one_le_rootCertAmplitude d hkR)
        (one_le_eccentricityFoldFactor abar (2 * kR⁻¹)))
  exact ⟨{ good := hgood
           delta := delta
           sourceScale := S
           activationScale := X
           delta_nonneg := hdelta.1.le
           activation_one := hXone
           source_le_activation := hburn
           activation_le_common := hactivation
           row := hrowRetained },
    hc, hdelta⟩

/-! ## The five-ceiling minimum -/

/-- The minimum of five ceilings is a ceiling. -/
theorem minCeiling_mem {c₁ c₂ c₃ c₄ c₅ : ℝ}
    (h₁ : c₁ ∈ Set.Ioo (0 : ℝ) 1) (h₂ : c₂ ∈ Set.Ioo (0 : ℝ) 1)
    (h₃ : c₃ ∈ Set.Ioo (0 : ℝ) 1) (h₄ : c₄ ∈ Set.Ioo (0 : ℝ) 1)
    (h₅ : c₅ ∈ Set.Ioo (0 : ℝ) 1) :
    min c₁ (min c₂ (min c₃ (min c₄ c₅))) ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨lt_min h₁.1 (lt_min h₂.1 (lt_min h₃.1 (lt_min h₄.1 h₅.1))),
    (min_le_left _ _).trans_lt h₁.2⟩

theorem minCeiling_le_one {c₁ c₂ c₃ c₄ c₅ : ℝ} :
    min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c₁ := min_le_left _ _

theorem minCeiling_le_two {c₁ c₂ c₃ c₄ c₅ : ℝ} :
    min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c₂ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem minCeiling_le_three {c₁ c₂ c₃ c₄ c₅ : ℝ} :
    min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c₃ :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem minCeiling_le_four {c₁ c₂ c₃ c₄ c₅ : ℝ} :
    min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c₄ :=
  (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))

theorem minCeiling_le_five {c₁ c₂ c₃ c₄ c₅ : ℝ} :
    min c₁ (min c₂ (min c₃ (min c₄ c₅))) ≤ c₅ :=
  (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))

end

end CorrectorComposition
end HighContrast
end HCPolySupport
