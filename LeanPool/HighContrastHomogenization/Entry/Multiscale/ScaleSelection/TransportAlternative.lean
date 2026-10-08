/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ScaleSelection.BridgeApplication

/-!
# High-contrast homogenization: Entry.Multiscale.ScaleSelection.TransportAlternative

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The transport application and the change-of-geometry alternative

Group D of the printed proof (`p.scale.selection`), third part: the two-grid
transport applied to the updated geometry, and alternative 2 with its output
profile bound `C σ^{(1-γ)/8}`, its output eccentricity and its two output conditions.

Part of the proof of the statement in
`HCPoly/Entry/Statements/ScaleSelection.lean`.  Conventions of the entire group: `q = 𝒬(𝔪)` is
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

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- `p.scale.selection`: the two-grid transport applies with `δ = ε^{1/2}σ`, `ρ = σ^{(1−γ)/8}`. -/
theorem transport_application (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (Csrc C₁ : ℝ) (hC₁ : 0 < C₁) (hone : OneGridBody d γ Csrc C₁)
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) (htr : TransportBody d γ Ctr Csrc)
    (L₀ : ℕ) (hL₀ : 1 ≤ L₀) (hCtrL₀ : Ctr ≤ L₀) (c₀ : ℝ) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1)
    (B₀ : ℝ → ℕ → ℝ) (hbr : BridgeBody d γ L₀ c₀ Csrc B₀) (ε₁ : ℝ)
    (hsmall : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) ε₁ → σ ∈ Set.Ioc (0 : ℝ) ε →
      2 * C₁ * (1 + 2 * (bigQ d γ : ℝ) * (d : ℝ)) * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ≤
        (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (selectionLength L₀ σ : ℝ)) * σ ^ ((1 - γ) / 8))
    (ε σ B : ℝ) (hε4 : ε ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hεc : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2)
    (hε₁ : ε ≤ ε₁) (hQε : (bigQ d γ : ℝ) * (d : ℝ) * ε ≤ Real.log 2)
    (hLε : 2 * Ctr * ε ≤ (L₀ : ℝ) * Real.log 3) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (hB1 : B₀ (Real.sqrt ε * σ) (selectionLength L₀ σ) ≤ B)
    (hB2 : 2 * Ctr * ((selectionLength L₀ σ : ℝ) + 1) ≤ B)
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
    profile P γ
          (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric
                (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                  (n + 2 * (selectionLength L₀ σ : ℤ))))))
          jStar (n + (selectionLength L₀ σ : ℤ)) (n + (selectionLength L₀ σ : ℤ)) +
        determinantDrift P γ
          (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric
                (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                  (n + 2 * (selectionLength L₀ σ : ℤ))))))
          jStar (n + (selectionLength L₀ σ : ℤ)) ≤
      Ctr * (Real.sqrt ε * σ + σ ^ ((1 - γ) / 8)) := by
  let : NeZero d := ⟨by omega⟩
  let : IsProbabilityMeasure P := hP
  have hε1 : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε4.1, by linarith only [hε4.2]⟩
  have hσ1 : σ ∈ Set.Ioc (0 : ℝ) 1 := ⟨hσ.1, hσ.2.trans hε1.2⟩
  -- the transport parameters
  have hρ : σ ^ ((1 - γ) / 8) ∈ Set.Ioc (0 : ℝ) 1 := transport_rho_mem σ γ hσ1 hγ
  have hδ : Real.sqrt ε * σ ∈ Set.Icc (0 : ℝ) (1 / 4) := bridge_tolerance_le_quarter ε σ hε4 hσ
  -- the updated geometry
  have hStar : (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
      (n + 2 * (selectionLength L₀ σ : ℤ)))).PosDef :=
    Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm _
  have hPlus : (geometryUpdate ε m (explicitCanonicalMetric (adaptedMean P
      (Geometry.explicitRoundedGrid jStar m) (n + 2 * (selectionLength L₀ σ : ℤ))))).PosDef :=
    Geometry.geometryUpdate_posDef hm hStar ε
  -- the scale separation, the projective step, the length condition
  have hsep : Ctr * ((selectionLength L₀ σ : ℝ) +
      Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤ (n : ℝ) - (jStar : ℝ) :=
    scale_separation d hd Ctr hCtr L₀ hL₀ ε σ B hε4.1 hLε hB2 E jStar m hm k n hkn hecc
  have hproj : projectiveDistance m (geometryUpdate ε m (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
        (n + 2 * (selectionLength L₀ σ : ℤ))))) ≤ 1 :=
    (Geometry.projectiveDistance_geometryUpdate_le hm hStar hε4.1).trans hε1.2
  have hlen : Ctr + Real.logb 3 (σ ^ ((1 - γ) / 8))⁻¹ ≤ (selectionLength L₀ σ : ℝ) :=
    selectionLength_transport_condition Ctr L₀ hCtrL₀ σ γ hσ1 hγ
  -- the old-grid smallness and the two Loewner comparisons
  have hold := old_grid_smallness d hd γ hγ Csrc C₁ hC₁ hone L₀ hL₀ c₀ hc₀ ε₁ hsmall ε σ
    ⟨hε4.1, hε₁⟩ hσ hQε P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm k n hjk hkn hin2 hk
    hη hlong
  obtain ⟨hlow, hup⟩ := bridge_application d hd γ hγ Csrc L₀ hL₀ c₀ hc₀ B₀ hbr ε σ B hε1 hεc hσ
    hB1 P E Ψ K S hP hstat hunit hdag jStar hj hsrc m hm k n hjk hkn hecc hin2 hcont hk hη hlong
  exact htr (σ ^ ((1 - γ) / 8)) hρ (Real.sqrt ε * σ) hδ P E Ψ K S hP hstat hunit hdag
    jStar hj hsrc m _ hm hPlus k n hjk hkn (selectionLength L₀ σ) hcont hsep hproj hlen
    hold hlow hup

/-- Alternative 2, change of geometry (`p.scale.selection`): the transport output
`≤ Cσ^{(1−γ)/8} ≤ 1`, the output eccentricity from `l.projective.step`, and the vacuous clause. -/
theorem transport_alternative (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (Csrc C₁ : ℝ) (hC₁ : 0 < C₁) (hone : OneGridBody d γ Csrc C₁)
    (Ctr : ℝ) (hCtr : 1 ≤ Ctr) (htr : TransportBody d γ Ctr Csrc)
    (C : ℝ) (hC : 2 * Ctr ≤ C)
    (L₀ : ℕ) (hL₀ : 1 ≤ L₀) (hCtrL₀ : Ctr ≤ L₀) (c₀ : ℝ) (hc₀ : c₀ ∈ Set.Ioo (0 : ℝ) 1)
    (B₀ : ℝ → ℕ → ℝ) (hbr : BridgeBody d γ L₀ c₀ Csrc B₀) (ε₁ : ℝ)
    (hsmall : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) ε₁ → σ ∈ Set.Ioc (0 : ℝ) ε →
      2 * C₁ * (1 + 2 * (bigQ d γ : ℝ) * (d : ℝ)) * (1 + (selectionLength L₀ σ : ℝ)) * ε * σ ≤
        (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (selectionLength L₀ σ : ℝ)) * σ ^ ((1 - γ) / 8))
    (ε σ B : ℝ) (hε4 : ε ∈ Set.Ioc (0 : ℝ) (1 / 4)) (hεc : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2)
    (hε₁ : ε ≤ ε₁) (hQε : (bigQ d γ : ℝ) * (d : ℝ) * ε ≤ Real.log 2)
    (hCε : C * ε ^ ((1 - γ) / 8) ≤ 1)
    (hLε : 2 * Ctr * ε ≤ (L₀ : ℝ) * Real.log 3) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (hB1 : B₀ (Real.sqrt ε * σ) (selectionLength L₀ σ) ≤ B)
    (hB2 : 2 * Ctr * ((selectionLength L₀ σ : ℝ) + 1) ≤ B)
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
    (k < n ∧
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ c₀ * ε * σ ∧
        (d : ℝ)⁻¹ *
            detIncrement P (Geometry.explicitRoundedGrid jStar m) n
              (n + 2 * (selectionLength L₀ σ : ℤ)) ≤ ε * σ ∧
        profile P γ
              (Geometry.explicitRoundedGrid jStar
                (geometryUpdate ε m
                  (explicitCanonicalMetric
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                      (n + 2 * (selectionLength L₀ σ : ℤ))))))
              jStar (n + (selectionLength L₀ σ : ℤ)) (n + (selectionLength L₀ σ : ℤ)) +
            determinantDrift P γ
              (Geometry.explicitRoundedGrid jStar
                (geometryUpdate ε m
                  (explicitCanonicalMetric
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                      (n + 2 * (selectionLength L₀ σ : ℤ))))))
              jStar (n + (selectionLength L₀ σ : ℤ)) ≤
          C * σ ^ ((1 - γ) / 8)) ∧
      1 / 2 *
          Real.log
            (‖geometryUpdate ε m
                (explicitCanonicalMetric
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                    (n + 2 * (selectionLength L₀ σ : ℤ))))‖ *
              ‖(geometryUpdate ε m
                  (explicitCanonicalMetric
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                      (n + 2 * (selectionLength L₀ σ : ℤ)))))⁻¹‖) ≤
        ε / (selectionLength L₀ σ : ℝ) *
          (((n : ℝ) + (selectionLength L₀ σ : ℝ)) - (jStar : ℝ) -
            (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
      (n + (selectionLength L₀ σ : ℤ) = n + (selectionLength L₀ σ : ℤ) →
        profile P γ
              (Geometry.explicitRoundedGrid jStar
                (geometryUpdate ε m
                  (explicitCanonicalMetric
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                      (n + 2 * (selectionLength L₀ σ : ℤ))))))
              jStar (n + (selectionLength L₀ σ : ℤ)) (n + (selectionLength L₀ σ : ℤ)) +
            determinantDrift P γ
              (Geometry.explicitRoundedGrid jStar
                (geometryUpdate ε m
                  (explicitCanonicalMetric
                    (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                      (n + 2 * (selectionLength L₀ σ : ℤ))))))
              jStar (n + (selectionLength L₀ σ : ℤ)) ≤ 1) ∧
      (n + (selectionLength L₀ σ : ℤ) < n + (selectionLength L₀ σ : ℤ) →
        n + (selectionLength L₀ σ : ℤ) + ((2 * bigQ d γ : ℕ) : ℤ) ≤
          n + (selectionLength L₀ σ : ℤ)) := by
  let : NeZero d := ⟨by omega⟩
  let : IsProbabilityMeasure P := hP
  have hε1 : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε4.1, by linarith only [hε4.2]⟩
  have hρpos : (0 : ℝ) < σ ^ ((1 - γ) / 8) := Real.rpow_pos_of_pos hσ.1 _
  have hCpos : (0 : ℝ) < C := by linarith only [hC, hCtr]
  have hLnat : 1 ≤ selectionLength L₀ σ := one_le_selectionLength L₀ hL₀ σ
  have hLr1 : (1 : ℝ) ≤ (selectionLength L₀ σ : ℝ) := by exact_mod_cast hLnat
  have hStar : (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
      (n + 2 * (selectionLength L₀ σ : ℤ)))).PosDef :=
    Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm _
  -- the transport output, `p.scale.selection`
  have hout := transport_application d hd γ hγ Csrc C₁ hC₁ hone Ctr hCtr htr L₀ hL₀ hCtrL₀
    c₀ hc₀ B₀ hbr ε₁ hsmall ε σ B hε4 hεc hε₁ hQε hLε hσ hB1 hB2 P E Ψ K S hP hstat hunit
    hdag jStar hj hsrc m hm k n hjk hkn hecc hin2 hcont hk hη hlong
  have hδρ : Real.sqrt ε * σ ≤ σ ^ ((1 - γ) / 8) := bridge_tolerance_le_rho ε σ γ hε1 hσ hγ
  have hCtr0 : (0 : ℝ) ≤ Ctr := by linarith only [hCtr]
  have hfin : profile P γ
        (Geometry.explicitRoundedGrid jStar
          (geometryUpdate ε m
            (explicitCanonicalMetric
              (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                (n + 2 * (selectionLength L₀ σ : ℤ))))))
        jStar (n + (selectionLength L₀ σ : ℤ)) (n + (selectionLength L₀ σ : ℤ)) +
      determinantDrift P γ
        (Geometry.explicitRoundedGrid jStar
          (geometryUpdate ε m
            (explicitCanonicalMetric
              (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                (n + 2 * (selectionLength L₀ σ : ℤ))))))
        jStar (n + (selectionLength L₀ σ : ℤ)) ≤ C * σ ^ ((1 - γ) / 8) := by
    have h1 : Ctr * (Real.sqrt ε * σ + σ ^ ((1 - γ) / 8)) ≤ Ctr * (2 * σ ^ ((1 - γ) / 8)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hδρ]) hCtr0
    have h2 := mul_le_mul_of_nonneg_right hC hρpos.le
    linarith only [hout, h1, h2]
  -- `Cρ ≤ 1`, `p.scale.selection`
  have hone_bound : C * σ ^ ((1 - γ) / 8) ≤ 1 := by
    have hσα : σ ^ ((1 - γ) / 8) ≤ ε ^ ((1 - γ) / 8) :=
      Real.rpow_le_rpow hσ.1.le hσ.2 (by linarith only [hγ.2])
    have h3 := mul_le_mul_of_nonneg_left hσα hCpos.le
    linarith only [h3, hCε]
  refine ⟨⟨hk, hη, hlong, hfin⟩, ?_, fun _ => hfin.trans hone_bound,
    fun h => absurd h (lt_irrefl _)⟩
  -- the output eccentricity, `p.scale.selection`
  have hecc2 := Geometry.log_eccentricity_geometryUpdate_le hm hStar hε4.1
  have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  exact geometry_eccentricity_output_arith _ _ _ _ _ _ _ _ hecc2 hε4.1 hLr1 hknR hecc

end

end HCPolySupport.HighContrast.Multiscale
