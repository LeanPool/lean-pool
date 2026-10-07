/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUHalfSpaceFixedSobolev
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCarlemanAdmissible
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightCompact
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfSpaceProof
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfWeightsBounds

/-!
# Uniform half-space Carleman constant for short-time cutoffs

The smooth half-space estimate supplies one threshold and one constant for
every compact short-time cutoff, independently of its radius and initial
time transition.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- One half-space Carleman threshold and constant work for all short-time
cutoffs of a field satisfying the weak derivative assumptions. -/
theorem bu_short_cutoff_carleman_uniform :
    ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ (scale R ε : ℝ) (_hscale : 0 < scale) (_hscale1 : scale ≤ 1)
        (hR : 0 < R) (_hε : 0 < ε)
        (w : ParabolicPoint → Vec3)
        (Dw : ParabolicPoint → Fin 3 → Vec3)
        (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
        (Dtw : ParabolicPoint → Vec3),
        ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1) →
        HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
          w Dw D2w Dtw →
        (∀ S : Set ParabolicPoint,
          S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
          Bornology.IsBounded S →
          (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
            ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) →
        ∀ a : ℝ, a₀ < a →
          let κ := buShortFullCutoff scale R hR ε
          let v := buAffineField (-scale ^ 2 / 2) scale w
          let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
          let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
          let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
          let W := buCutField κ v
          let DW := buCutDw κ v Dv
          let D2W := buCutD2 κ v Dv D2v
          let DtW := buCutDt κ v Dtv
          (∫ z in halfSpaceDomain,
            buShortCarlemanWeight a z *
              (a * vec3EuclideanNorm (W z) ^ 2 / z.2 ^ 2 +
                spatialGradientSq W DW z / z.2)) ≤
          c * (∫ z in halfSpaceDomain,
            buShortCarlemanWeight a z *
              vec3EuclideanNorm (ucWeakHeatVector D2W DtW z) ^ 2) := by
  have hpoint : ∀ (α : ℝ), 1 / 2 < α → α < 1 →
      ∀ (a : ℝ), 2 ≤ a → ∀ (q : ParabolicPoint → ℝ),
        ∀ z ∈ halfSpaceDomain,
          (a * (2 * α - 1) * ESS.Main.halfSpaceMassFactor α z +
            ESS.Main.halfSpaceNormalEnergy a α z) * q z ^ 2 ≤
              carlemanCommutatorDensity (halfSpacePhase a α) q z := by
    intro α hα hα1 a ha q z hz
    have hb := halfSpacePhase_commutatorDensity_lower
      a α q hz ha hα hα1
    calc
      _ = a * (2 * α - 1) * z.1 2 ^ (2 * α) / z.2 ^ α * q z ^ 2 +
          z.2 * halfSpaceGradientTwo a α z ^ 2 * q z ^ 2 := by
            dsimp [ESS.Main.halfSpaceMassFactor,
              ESS.Main.halfSpaceNormalEnergy]
            ring
      _ ≤ _ := hb
  obtain ⟨a₀, c, ha₀, hc, hSmooth⟩ :=
    ESS.Main.halfSpace_estimate_of_pointwise_bound hpoint
      (3 / 4) (by norm_num) (by norm_num)
  refine ⟨a₀, c, ha₀, hc, ?_⟩
  intro scale R ε hscale hscale1 hR hε w Dw D2w Dtw
    hcont hweak hL2 a ha
  obtain ⟨hderiv, hcompact, hts, hL2cut⟩ :=
    bu_short_cutoff_carleman_admissible scale R ε hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  exact bu_carleman_sobolev_halfspace_fixed
    (3 / 4) a₀ c _ _ _ _ hderiv hcompact hts hL2cut hSmooth a ha

end ESS
