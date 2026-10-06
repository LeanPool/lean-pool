/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.IntegratedWeakEnergyBound

/-!
# High-contrast homogenization: Entry.Response.Kernel.WeakEstimateAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak-norm estimate, assembled over both signs

The weak-norm estimate `response_weak_estimate` - `e.response.weak.estimate`, part 4 of the
decomposition `adapted_response_core` of R1 - bounds, for each sign of the recentring, the
supremum over families of response maximizers of the per-family weak energy by
`(C(3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2})^2`. It is obtained from the two per-family bounds by
taking the larger of the two constants, using the scale-average seminorm of the cell-average
lemma on the selected grid rather than the compact-test dual norm of the theorem statements.
Bundled with this assembly are two cutoff-argument facts: the integrated centred cutoff
decomposition of AK.HC (3.45)-(3.54), and the defining properties of the response cutoff class
`IsResponseCutoff`.
-/

section
/-!
## The weak-norm estimate, assembled over the two signs

`response_weak_estimate_of_route` is `e.response.weak.estimate`: the supremum over families of
response maximizers of the per-family weak energy is bounded by
`(C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2})^2` for each sign.  It is obtained from the two
per-family bounds by taking the larger of the two constants and reading the supremum off
through the two conjuncts of the definition of `W^±`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- **`e.response.weak.estimate`.**  For each sign, `W^± ≥ 0` and
`(W^±)^{1/2} ≤ C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2}`.

`W^±` is a supremum over all families of response maximizers, so the bound follows from the
per-family bounds `respWeakEnergyOf_minus_le` and `respWeakEnergyOf_plus_le` once the two
constants are replaced by their maxima; the supremum is then bounded because every member of
the defining set is. -/
theorem response_weak_estimate_of_route (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl Cm Cs : ℝ) (hCc : 0 < Cc)
    (hCe : 0 < Ce) (hCl : 0 < Cl) (hCm : 0 < Cm) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ (C : ℝ) (CH : ℕ → ℝ), 0 < C ∧ (∀ n : ℕ, 0 < CH n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
              ∀ e : Vec d, vecDot e e = 1 →
                RespEnergyDefect Ce P jStar F s t e →
                RespLoadMean Cl P jStar F s t e →
                RespWeakBound C CH d γ P jStar F H η s t e := by
  obtain ⟨Csrc₁, hCsrc₁, C₁, CH₁, hC₁, hCH₁, h₁⟩ :=
    respWeakEnergyOf_minus_le d hd γ hγ S hS Cc Ce Cl Cm Cs hCc hCe hCl hCm hCs
  obtain ⟨Csrc₂, hCsrc₂, C₂, CH₂, hC₂, hCH₂, h₂⟩ :=
    respWeakEnergyOf_plus_le d hd γ hγ S hS Cc Ce Cl Cm Cs hCc hCe hCl hCm hCs
  refine ⟨max Csrc₁ Csrc₂, lt_max_of_lt_left hCsrc₁, max C₁ C₂,
    fun n => max (CH₁ n) (CH₂ n), lt_max_of_lt_left hC₁,
    fun n => lt_max_of_lt_left (hCH₁ n), ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hraw hcal η hη hprof
    hsrc hM e he hdef hload
  have hraw₁ := RawOutput.of_le_csrc hraw (le_max_left Csrc₁ Csrc₂)
  have hraw₂ := RawOutput.of_le_csrc hraw (le_max_right Csrc₁ Csrc₂)
  have hR0 : 0 ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) := Real.rpow_nonneg (by
    norm_num) _
  have hZ0 : 0 ≤ η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) := Real.rpow_nonneg hη.1.le _
  have hκ0 : 0 ≤ Real.sqrt (respKappa P jStar F s) := Real.sqrt_nonneg _
  set R : ℝ := (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) with hR
  set Z : ℝ := η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) with hZ
  set κ : ℝ := Real.sqrt (respKappa P jStar F s) with hκ
  have hC : 0 < max C₁ C₂ := lt_max_of_lt_left hC₁
  have hCH : 0 < max (CH₁ H) (CH₂ H) := lt_max_of_lt_left (hCH₁ H)
  have hB0 : 0 ≤ max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ := by positivity
  have hmono₁ : (C₁ * (R + CH₁ H * Z) * κ) ^ 2 ≤
      (max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ) ^ 2 := by
    have h1 : 0 ≤ C₁ * (R + CH₁ H * Z) * κ := by
      have := (hCH₁ H).le
      positivity
    have h2 : C₁ * (R + CH₁ H * Z) * κ ≤ max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ := by
      have hCle : C₁ ≤ max C₁ C₂ := le_max_left _ _
      have hCHle : CH₁ H ≤ max (CH₁ H) (CH₂ H) := le_max_left _ _
      have hsum_nonneg : 0 ≤ R + CH₁ H * Z := add_nonneg hR0 (mul_nonneg (hCH₁ H).le hZ0)
      have hmax_nonneg : 0 ≤ max C₁ C₂ := hC₁.le.trans hCle
      have hsum_le : R + CH₁ H * Z ≤ R + max (CH₁ H) (CH₂ H) * Z := by
        have h := mul_le_mul_of_nonneg_right hCHle hZ0
        linarith only [h]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hCle hsum_le hsum_nonneg hmax_nonneg) hκ0
    exact pow_le_pow_left₀ h1 h2 2
  have hmono₂ : (C₂ * (R + CH₂ H * Z) * κ) ^ 2 ≤
      (max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ) ^ 2 := by
    have h1 : 0 ≤ C₂ * (R + CH₂ H * Z) * κ := by
      have := (hCH₂ H).le
      positivity
    have h2 : C₂ * (R + CH₂ H * Z) * κ ≤ max C₁ C₂ * (R + max (CH₁ H) (CH₂ H) * Z) * κ := by
      have hCle : C₂ ≤ max C₁ C₂ := le_max_right _ _
      have hCHle : CH₂ H ≤ max (CH₁ H) (CH₂ H) := le_max_right _ _
      have hsum_nonneg : 0 ≤ R + CH₂ H * Z := add_nonneg hR0 (mul_nonneg (hCH₂ H).le hZ0)
      have hmax_nonneg : 0 ≤ max C₁ C₂ := hC₂.le.trans hCle
      have hsum_le : R + CH₂ H * Z ≤ R + max (CH₁ H) (CH₂ H) * Z := by
        have h := mul_le_mul_of_nonneg_right hCHle hZ0
        linarith only [h]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hCle hsum_le hsum_nonneg hmax_nonneg) hκ0
    exact pow_le_pow_left₀ h1 h2 2
  unfold RespWeakBound respWMinus
  rw [respWPlus_eq]
  refine ⟨respWeakEnergy_nonneg _ _ _ _ _ _ _ _, respWeakEnergy_nonneg _ _ _ _ _ _ _ _, ?_, ?_⟩
  · refine sqrt_respWeakEnergy_le _ _ _ _ _ _ _ _ _ hB0 ?_
    intro u hu
    exact (h₁ ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hraw₁ hcal η hη
      hprof hsrc hM e he hdef hload u hu).trans hmono₁
  · refine sqrt_respWeakEnergy_le _ _ _ _ _ _ _ _ _ hB0 ?_
    intro u hu
    exact (h₂ ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t hraw₂ hcal η hη
      hprof hsrc hM e he hdef hload u hu).trans hmono₂

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## R1 decomposition, part 4: the weak-norm estimate

The weak-norm estimate of the decomposition of R1 `adapted_response_core` is
`e.response.weak.estimate`.

The concrete scale-average seminorm used here is the one of the cell-average lemma of the
high-contrast reference, on the selected grid, not the compact-test dual norm of the theorem
statements.  The estimate splits as `3^{-αH}` from the scales older than the response window
plus `C_H η^{1/(2Q)}` from the recent cell fluctuations, the mean differences, and the
correction from random to annealed centering.  This is where the histories retained through
the iteration enter the response argument: small fluctuations at the terminal scale alone
would not control the cell averages in this seminorm.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## The weak-norm estimate -/

/-- **The weak-norm estimate** `e.response.weak.estimate`:
`(W^±)^{1/2} ≤ C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2}`, with `α = (1-γ)/4`.

`K_0 = |M_0^{-1/2} Ê_t^± M_0^{-1/2}|^{1/2} ≤ C κ_s^{1/4}`, and the variational bound on the
mean of a gradient–solenoidal field holds on every Lipschitz cell, so the cell-average
argument applies on the selected grid with exponent `1/2`, decay exponent `ρ`, cutoff `1` and
window `H`.  The recent-cell differences contribute `C_H K_0 L^± η^{1/(2Q)}` through the mean
penalty; the energy split at the cutoff `1` contributes `C K_0 L^± (η^{1/2} + 3^{-αH})` using
`E[M^Q] ≤ C η`; the random-to-annealed recentering costs the same order.  Finally
`K_0 L^± ≤ C κ_s^{1/2}` by the calibrated-block and load bounds. -/
theorem response_weak_estimate (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl Cm Cs : ℝ) (hCc : 0 < Cc)
    (hCe : 0 < Ce) (hCl : 0 < Cl) (hCm : 0 < Cm) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ (C : ℝ) (CH : ℕ → ℝ), 0 < C ∧ (∀ n : ℕ, 0 < CH n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
              ∀ e : Vec d, vecDot e e = 1 →
                RespEnergyDefect Ce P jStar F s t e →
                RespLoadMean Cl P jStar F s t e →
                RespWeakBound C CH d γ P jStar F H η s t e :=
  response_weak_estimate_of_route d hd γ hγ S hS Cc Ce Cl Cm Cs hCc hCe hCl hCm hCs

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The integrated centred cutoff decomposition (AK.HC (3.45)-(3.54))

The cutoff pairing `cutoffPairingOnCellAux U φ Y b v` tests the optimizer state
`X = (∇v, b ∇v)` against the annealed mean `Y` of AK.HC (2.32), weighted by the cutoff `φ`.
Its pathwise expansion exhibits the half-pairing as the cutoff-weighted half-energy
`cutoffHalfEnergyAux` minus the two mean pairings plus half the self-pairing of `Y`.

Integrating that expansion against the law `P` and applying the triangle inequality exhibits the
centred response as the sum of the absolute cutoff pairing, the absolute energy defect
`cutoffHalfEnergyAux - J`, and the two integrated cutoff-mean terms.  This is the first step of the
variational calculation of `e.response.cutoff.estimate` (AK.HC (3.45)-(3.54)), taken before the
products are separated by Young's inequality.

The statement is the integrated form of `cutoff_halfPairing_eq_sub`.  The cell `U` and the
coefficient `b` are arbitrary: no ellipticity of `b`, no boundedness of `U`, and no positivity
of `φ` enter, only the integrabilities of the sample functions and of the coordinates of the
optimizer state.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing term on the cell `U`: the cutoff-weighted recentred pairing
`(φ (X₁ - Y₁) · (X₂ - Y₂))_U` of the optimizer state `X = (∇v, b ∇v)` at the annealed mean `Y`
of AK.HC (2.32).  This is the local spelling of the pairing consumed by the cutoff estimate of
AK.HC (3.45)-(3.54). -/
@[expose]
def cutoffPairingOnCellAux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) (Y : BlockVec d)
    (b : CoeffField d) (v : AHarmonicFunction b U) : ℝ :=
  volumeAverage U fun x =>
    φ x * vecDot ((optimizerField b v x).1 - Y.1) ((optimizerField b v x).2 - Y.2)

/-- The cutoff-weighted mean of the doubled optimizer state `X = (∇v, b ∇v)` on the cell `U`:
the pair whose coordinates are the cutoff averages of the coordinates of `X`.  Its two
components are the mean pairings appearing in the centred decomposition of AK.HC (3.45)-(3.54). -/
@[expose]
def cutoffStateMeanAux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) (b : CoeffField d)
    (v : AHarmonicFunction b U) : BlockVec d :=
  (fun i => volumeAverage U fun x => φ x * (optimizerField b v x).1 i,
   fun i => volumeAverage U fun x => φ x * (optimizerField b v x).2 i)

/-- The cutoff-weighted half-energy of the optimizer state `X = (∇v, b ∇v)`: one half of the
cutoff average of `φ (X₁ · X₂)`.  This is the energy term subtracted from the response on the
right-hand side of the centred decomposition of AK.HC (3.45)-(3.54). -/
@[expose]
def cutoffHalfEnergyAux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) (b : CoeffField d)
    (v : AHarmonicFunction b U) : ℝ :=
  (1 / 2 : ℝ) * volumeAverage U
    (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The defining properties of the response cutoff class

`IsResponseCutoff qq t φ` is the class of cutoffs used by the cutoff estimate
`e.response.cutoff.estimate`: a function supported in the adapted cell `HighContrast.adaptedCell
qq t`,
bounded between `0` and `2`, of volume average one there, and carrying the first- and
second-derivative bounds at the scale `3 ^ t` in `qq`-coordinates.  Each defining property is
exposed here as a named theorem, so that consumers can refer to a property by name rather than by
a positional projection.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` is nonnegative
everywhere. -/
theorem IsResponseCutoff.nonneg {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (x : Vec d) : 0 ≤ φ x :=
  h.1 x

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` is bounded above
by `2` everywhere. -/
theorem IsResponseCutoff.le_two {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) (x : Vec d) : φ x ≤ 2 :=
  h.2.1 x

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` vanishes at every
point outside the adapted cell `HighContrast.adaptedCell qq t`. -/
theorem IsResponseCutoff.zero_of_notMem {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : ∀ x, x ∉ HighContrast.adaptedCell qq t → φ x = 0 :=
  h.2.2.1

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` has volume
average one on the adapted cell `HighContrast.adaptedCell qq t`. -/
theorem IsResponseCutoff.volumeAverage_eq_one {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) :
    volumeAverage (HighContrast.adaptedCell qq t) φ = 1 :=
  h.2.2.2.1

/-- The pullback `y ↦ φ (qq y)` of a cutoff `φ` of the class of the cutoff estimate
`e.response.cutoff.estimate` is Lipschitz with constant
`32 * d ^ 2 * responseCutoffProfileConst * 3 ^ (-t)`. -/
theorem IsResponseCutoff.lipschitz {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) :
    LipschitzWith
      (Real.toNNReal
        (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)))
      (fun y : Vec d => φ (matVecMul qq y)) :=
  h.2.2.2.2.1

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` is smooth, i.e.
`C^∞`. -/
theorem IsResponseCutoff.contDiff {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : ContDiff ℝ (⊤ : ℕ∞) φ :=
  h.2.2.2.2.2.1

/-- A cutoff `φ` of the class of the cutoff estimate `e.response.cutoff.estimate` has compact
support. -/
theorem IsResponseCutoff.hasCompactSupport {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : HasCompactSupport φ :=
  h.2.2.2.2.2.2.1

/-- The topological support of a cutoff `φ` of the class of the cutoff estimate
`e.response.cutoff.estimate` is contained in the adapted cell `HighContrast.adaptedCell qq t`. -/
theorem IsResponseCutoff.tsupport_subset {d : ℕ} {qq : Mat d} {t : ℤ} {φ : Vec d → ℝ}
    (h : IsResponseCutoff qq t φ) : tsupport φ ⊆ HighContrast.adaptedCell qq t :=
  h.2.2.2.2.2.2.2.1

end

end HCPolySupport.HighContrast.Multiscale
end
