/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ScaleSelection.Alternatives

/-!
# High-contrast homogenization: Entry.Multiscale.ScaleSelection.BridgeApplication

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The short bridge, old-grid smallness and scale separation

Group D of the printed proof (`p.scale.selection`), second part: the short
bridge applied at tolerance `√ε σ` with the chosen length, the smallness of the old-grid
profile at the doubled length, and the scale separation
`C_tr (L + log₃((2+Π)(‖m‖‖m⁻¹‖))) ≤ n - j_*` that the transport step consumes
(the condition actually proved below and supplied to `TransportBody`; `C(L+1) ≤ n - j_*`
concerns the choice of `B₀`, not the transport hypothesis).

Part of the proof of
`HCPoly/Entry/Statements/ScaleSelection.lean`.  Conventions of the group: `q = 𝒬(𝔪)` is
`Geometry.explicitRoundedGrid jStar m`; the printed data are `h = 2Q`, `c = c₀`,
`L(ε,σ) = selectionLength L₀ σ` and
`B₀(ε,σ) = max 1 (max (B₀^bridge (√ε σ) L) (2 C_tr (L+1)))`; `√ε` is the printed
`ε^{1/2}`; the source lower scale `e.source.lower.scale` is carried wherever
`j_*` appears with the law, and no integrability, finiteness or
measurability premise is added anywhere.  Unused hypothesis binders of a statement are
underscore-prefixed; the tree compiles with `-DwarningAsError=true`.

The declaration text of this file is the closed skeleton's, copied unchanged; only this
header, the imports and the namespace frame are new.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- `p.scale.selection`: in the change-of-geometry case the short bridge applies at tolerance
`ε^{1/2}σ` with the chosen length, giving the two Loewner comparisons. -/
theorem bridge_application (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (Csrc : ℝ) (L₀ : ℕ) (hL₀ : 1 ≤ L₀) (c₀ : ℝ) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1)
    (B₀ : ℝ → ℕ → ℝ) (hbr : BridgeBody d γ L₀ c₀ Csrc B₀)
    (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hεc : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (hB : B₀ (Real.sqrt ε * σ) (selectionLength L₀ σ) ≤ B)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (m : Mat d) (hm : m.PosDef) (k n : ℤ) (hjk : (jStar : ℤ) ≤ k) (hkn : k ≤ n)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
      ε / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (hin2 : k < n → k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n)
    (hcont : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m)
          (n + 2 * (selectionLength L₀ σ : ℤ)) ∪
        HighContrast.adaptedCell
          (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric
                (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                  (n + 2 * (selectionLength L₀ σ : ℤ))))))
          (n + (selectionLength L₀ σ : ℤ)) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (hk : k < n)
    (hη : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ c₀ * ε * σ)
    (hlong : (d : ℝ)⁻¹ *
        detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (selectionLength L₀ σ :
          ℤ)) ≤
      ε * σ) :
    BlockMatLoewnerLE
        (blockScale (1 - Real.sqrt ε * σ)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (selectionLength L₀ σ :
            ℤ))))
        (adaptedMean P
          (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric
                (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                  (n + 2 * (selectionLength L₀ σ : ℤ))))))
          (n + (selectionLength L₀ σ : ℤ))) ∧
      BlockMatLoewnerLE
        (adaptedMean P
          (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric
                (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                  (n + 2 * (selectionLength L₀ σ : ℤ))))))
          (n + (selectionLength L₀ σ : ℤ)))
        (blockScale (1 + Real.sqrt ε * σ)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
            (n + 2 * (selectionLength L₀ σ : ℤ)))) := by
  let : NeZero d := ⟨by omega⟩
  let : IsProbabilityMeasure P := hP
  have _hγ : γ ∈ Set.Ico (0 : ℝ) 1 := hγ
  obtain ⟨hc₀0, hc₀1⟩ := hc₀
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : (0 : ℝ) < (d : ℝ) + 1 := by linarith only [hdR]
  -- `2ε ≤ c₀` from `ε ≤ (c₀/(d+1))²`, `d ≥ 2` and `c₀ < 1` (`p.scale.selection`)
  have h2ε : 2 * ε ≤ c₀ := by
    have ht : c₀ / ((d : ℝ) + 1) * ((d : ℝ) + 1) = c₀ := div_mul_cancel₀ c₀ hden.ne'
    have ht0 : 0 ≤ c₀ / ((d : ℝ) + 1) := div_nonneg hc₀0.le hden.le
    have h3t : 3 * (c₀ / ((d : ℝ) + 1)) ≤ c₀ := by nlinarith only [ht, ht0, hdR]
    have hhalf : (c₀ / ((d : ℝ) + 1)) ^ 2 ≤ c₀ / 2 := by
      nlinarith only [h3t, ht0, hc₀0, hc₀1]
    linarith only [hεc, hhalf]
  -- the bridge at tolerance `√ε σ` and the chosen length
  have hσtol : Real.sqrt ε * σ ∈ Set.Ioc (0 : ℝ) 1 := bridge_tolerance_mem ε σ hε hσ
  have hlen : (L₀ : ℤ) + ⌈Real.logb 3 (Real.sqrt ε * σ)⁻¹⌉ ≤ (selectionLength L₀ σ : ℤ) :=
    selectionLength_bridge_condition L₀ ε σ hε hσ
  obtain ⟨_, hbody⟩ := hbr (Real.sqrt ε * σ) hσtol (selectionLength L₀ σ) hlen
  -- the updated geometry
  have hStar : (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
      (n + 2 * (selectionLength L₀ σ : ℤ)))).PosDef :=
    Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm _
  have hPlus : (geometryUpdate ε m (explicitCanonicalMetric (adaptedMean P
      (Geometry.explicitRoundedGrid jStar m) (n + 2 * (selectionLength L₀ σ : ℤ))))).PosDef :=
    Geometry.geometryUpdate_posDef hm hStar ε
  -- the five hypotheses of the bridge
  have hLpos : (0 : ℝ) < (selectionLength L₀ σ : ℝ) := by
    have h1 : 1 ≤ selectionLength L₀ σ := one_le_selectionLength L₀ hL₀ σ
    have h2 : (1 : ℝ) ≤ (selectionLength L₀ σ : ℝ) := by exact_mod_cast h1
    linarith only [h2]
  have heccBridge : Real.log (‖m‖ * ‖m⁻¹‖) ≤
      c₀ / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) -
          (⌈B₀ (Real.sqrt ε * σ) (selectionLength L₀ σ) *
            Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) :=
    bridge_eccentricity_arith (Real.log (‖m‖ * ‖m⁻¹‖)) ε c₀ (selectionLength L₀ σ : ℝ)
      (k : ℝ) (jStar : ℝ) (Real.logb 3 (2 + aspectRatio E))
      (B₀ (Real.sqrt ε * σ) (selectionLength L₀ σ)) B
      (Geometry.log_norm_mul_norm_inv_nonneg hm) hε.1 h2ε hLpos
      (logb_two_add_aspectRatio_nonneg E) hB hecc
  have hgap : k + 2 * (bigQ d γ : ℤ) ≤ n := by
    have h := hin2 hk
    push_cast at h
    omega
  have hproj : projectiveDistance m (geometryUpdate ε m (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
        (n + 2 * (selectionLength L₀ σ : ℤ))))) ≤ 1 :=
    (Geometry.projectiveDistance_geometryUpdate_le hm hStar hε.1).trans hε.2
  have hsmall : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
        detIncrement P (Geometry.explicitRoundedGrid jStar m) n
          (n + 2 * (selectionLength L₀ σ : ℤ)) ≤ c₀ * (Real.sqrt ε * σ) :=
    bridge_smallness_arith d hd c₀ c₀ ε σ _ _ _ ⟨hc₀0, hc₀1⟩ ⟨hc₀0, hc₀1⟩ hε.1 hεc hσ.1 hη hlong
  exact hbody P E Ψ K S hP hstat hunit hdag jStar hj hsrc m _ hm hPlus k n hjk hkn hcont
    heccBridge hgap hproj hsmall

/-- `p.scale.selection`: the old-grid smallness `𝒫_q(n+2L;k)+D(n+2L) ≤ 3^{−½(1−γ)L}ρ` from the
one-grid fixed-span propagation at span `2L`, the determinant bound and the smallness of `ε`. -/
theorem old_grid_smallness (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (Csrc C₁ : ℝ) (hC₁ : 0 < C₁) (hone : OneGridBody d γ Csrc C₁)
    (L₀ : ℕ) (hL₀ : 1 ≤ L₀) (c₀ : ℝ) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1) (ε₁ : ℝ)
    (hsmall : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) ε₁ → σ ∈ Set.Ioc (0 : ℝ) ε →
      2 * C₁ * (1 + 2 * (bigQ d γ : ℝ) * (d : ℝ)) * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ≤
        (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (selectionLength L₀ σ : ℝ)) * σ ^ ((1 - γ) / 8))
    (ε σ : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) ε₁) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (hQε : (bigQ d γ : ℝ) * (d : ℝ) * ε ≤ Real.log 2)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (m : Mat d) (hm : m.PosDef) (k n : ℤ) (hjk : (jStar : ℤ) ≤ k) (hkn : k ≤ n)
    (hin2 : k < n → k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n)
    (hk : k < n)
    (hη : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ c₀ * ε * σ)
    (hlong : (d : ℝ)⁻¹ *
        detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (selectionLength L₀ σ :
          ℤ)) ≤
      ε * σ) :
    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (selectionLength L₀ σ :
      ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
          (n + 2 * (selectionLength L₀ σ : ℤ)) ≤
      (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (selectionLength L₀ σ : ℝ)) * σ ^ ((1 - γ) / 8) := by
  let : IsProbabilityMeasure P := hP
  have arith : ∀ a br X Cc Lr : ℝ, 0 ≤ Cc → 1 ≤ Lr → br ≤ X → 0 ≤ X →
      a ≤ Cc * (2 * Lr) * br → a ≤ Cc * (2 * (1 + Lr)) * X := by
    intro a br X Cc Lr hCc hLr hbrX hX h
    have h1 : Cc * (2 * Lr) * br ≤ Cc * (2 * Lr) * X :=
      mul_le_mul_of_nonneg_left hbrX (mul_nonneg hCc (by linarith only [hLr]))
    have h2 : Cc * (2 * Lr) * X ≤ Cc * (2 * (1 + Lr)) * X :=
      mul_le_mul_of_nonneg_right (by linarith only [hCc]) hX
    linarith only [h1, h2, h]
  obtain ⟨hε0, hεle⟩ := hε
  obtain ⟨hσ0, hσε⟩ := hσ
  obtain ⟨hc₀0, hc₀1⟩ := hc₀
  have hQR : (0 : ℝ) < (bigQ d γ : ℝ) := bigQ_real_pos d γ hγ
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hQd4 : (4 : ℝ) ≤ (bigQ d γ : ℝ) * (d : ℝ) := by
    have h1 : (2 : ℝ) ≤ (bigQ d γ : ℝ) := by exact_mod_cast bigQ_two_le d γ hγ
    have h2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    nlinarith only [h1, h2]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  have hε1 : ε ≤ 1 := by nlinarith only [hQε, hQd4, hε0, hlog2]
  have hσ1 : σ ≤ 1 := hσε.trans hε1
  have hεσ0 : (0 : ℝ) < ε * σ := mul_pos hε0 hσ0
  have hεσ1 : ε * σ ≤ 1 := (mul_le_of_le_one_left hσ0.le hε1).trans hσ1
  have hp3 : c₀ * (ε * σ) ≤ ε * σ := mul_le_of_le_one_left hεσ0.le hc₀1.le
  have hc₀εσ : c₀ * (ε * σ) ≤ 1 := hp3.trans hεσ1
  have hdεσ : (d : ℝ) * (ε * σ) ≤ (d : ℝ) * ε :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hε0.le hσ1) hdR.le
  have hLnat : 1 ≤ selectionLength L₀ σ := one_le_selectionLength L₀ hL₀ σ
  have hLr1 : (1 : ℝ) ≤ (selectionLength L₀ σ : ℝ) := by exact_mod_cast hLnat
  have hLint : (1 : ℤ) ≤ 2 * (selectionLength L₀ σ : ℤ) := by
    have h : (1 : ℤ) ≤ (selectionLength L₀ σ : ℤ) := by exact_mod_cast hLnat
    omega
  have hcast : ((2 * (selectionLength L₀ σ : ℤ) : ℤ) : ℝ) = 2 * (selectionLength L₀ σ : ℝ) := by
    push_cast; ring
  -- the determinant increment is small
  have hΔ0 : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar m) n
      (n + 2 * (selectionLength L₀ σ : ℤ)) :=
    HCPolySupport.HighContrast.Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm
      n (n + 2 * (selectionLength L₀ σ : ℤ)) (hjk.trans hkn) (by omega)
  have hΔle : detIncrement P (Geometry.explicitRoundedGrid jStar m) n
      (n + 2 * (selectionLength L₀ σ : ℤ)) ≤ (d : ℝ) * (ε * σ) :=
    (inv_mul_le_iff₀ hdR).mp hlong
  have hx0 : 0 ≤ (bigQ d γ : ℝ) * detIncrement P (Geometry.explicitRoundedGrid jStar m) n
      (n + 2 * (selectionLength L₀ σ : ℤ)) := mul_nonneg hQR.le hΔ0
  have hp1 := mul_le_mul_of_nonneg_left hΔle hQR.le
  have hxlog : (bigQ d γ : ℝ) * detIncrement P (Geometry.explicitRoundedGrid jStar m) n
      (n + 2 * (selectionLength L₀ σ : ℤ)) ≤ Real.log 2 := by
    have hp2 := mul_le_mul_of_nonneg_left (hΔle.trans hdεσ) hQR.le
    linarith only [hp2, hQε]
  have hexp := exp_sub_one_le_two_mul _ hx0 hxlog
  have hXnn : (0 : ℝ) ≤ (1 + 2 * (bigQ d γ : ℝ) * (d : ℝ)) * (ε * σ) :=
    mul_nonneg (by positivity) hεσ0.le
  -- the eighth conjunct of the one-grid body at span `2L`
  obtain ⟨_, _, _, _, _, _, _, hlong8⟩ :=
    hone P E Ψ K S hP hstat hunit hdag (2 * bigQ d γ) le_rfl
      (2 * (selectionLength L₀ σ : ℤ)) hLint jStar hj hsrc m hm k n hjk hkn
  have hPD1 : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ 1 := by
    linarith only [hη, hc₀εσ]
  have hstep := hlong8 (Or.inr (hin2 hk)) hPD1
  rw [hcast] at hstep
  have hbr : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
        Real.exp ((bigQ d γ : ℝ) * detIncrement P (Geometry.explicitRoundedGrid jStar m) n
          (n + 2 * (selectionLength L₀ σ : ℤ))) - 1 ≤
      (1 + 2 * (bigQ d γ : ℝ) * (d : ℝ)) * (ε * σ) := by
    linarith only [hexp, hη, hp1, hp3]
  have hmain := arith _ _ _ _ _ hC₁.le hLr1 hbr hXnn hstep
  refine hmain.trans ?_
  linarith only [hsmall ε σ ⟨hε0, hεle⟩ ⟨hσ0, hσε⟩]

/-- `p.scale.selection`: the transport scale separation at the chosen data. -/
theorem scale_separation (d : ℕ) (hd : 2 ≤ d) (Ctr : ℝ) (hCtr : 1 ≤ Ctr) (L₀ : ℕ) (hL₀ : 1 ≤ L₀)
    (ε σ B : ℝ) (hε : 0 < ε) (hLε : 2 * Ctr * ε ≤ (L₀ : ℝ) * Real.log 3)
    (hB : 2 * Ctr * ((selectionLength L₀ σ : ℝ) + 1) ≤ B)
    (E : BlockMat d) (jStar : ℕ) (m : Mat d) (hm : m.PosDef) (k n : ℤ) (hkn : k ≤ n)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
      ε / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ))) :
    Ctr * ((selectionLength L₀ σ : ℝ) +
        Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤
      (n : ℝ) - (jStar : ℝ) := by
  let : NeZero d := ⟨by omega⟩
  have hX : 1 ≤ ‖m‖ * ‖m⁻¹‖ := by
    let v : Vec d := fun i => if i = (⟨0, by omega⟩ : Fin d) then (1 : ℝ) else 0
    have hv : v ≠ 0 := by
      intro h
      have hv0 := congrFun h (⟨0, by omega⟩ : Fin d)
      simp [v] at hv0
    exact HCPolySupport.HighContrast.Geometry.one_le_opNorm_mul_opNorm_inv hm hv
  have hPi : 0 ≤ aspectRatio E :=
    HCPolySupport.HighContrast.aspectRatio_nonneg E
  have hCtr_pos : 0 < Ctr :=
    lt_of_lt_of_le zero_lt_one hCtr
  have hlog3 : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have hL0len_nat : L₀ ≤ selectionLength L₀ σ := by
    unfold selectionLength
    omega
  have hL0len : (L₀ : ℝ) ≤ (selectionLength L₀ σ : ℝ) := by
    exact_mod_cast hL0len_nat
  have hL : 1 ≤ (selectionLength L₀ σ : ℝ) := by
    exact_mod_cast le_trans hL₀ hL0len_nat
  have hkn' : (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hkn
  have hLε' :
      2 * Ctr * ε ≤ (selectionLength L₀ σ : ℝ) * Real.log 3 :=
    le_trans hLε (mul_le_mul_of_nonneg_right hL0len hlog3.le)
  exact scale_separation_arith (C := Ctr) (L := (selectionLength L₀ σ : ℝ))
    (X := ‖m‖ * ‖m⁻¹‖) (Pi := aspectRatio E) (k := (k : ℝ))
    (n := (n : ℝ)) (j := (jStar : ℝ)) (hC := hCtr_pos) (hL := hL)
    (hε := hε) (hX := hX) (hPi := hPi) (hkn := hkn') (hLε := hLε')
    (hB := hB) (hecc := hecc)

end

end HCPolySupport.HighContrast.Multiscale
