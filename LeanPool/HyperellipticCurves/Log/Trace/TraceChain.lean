/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Charts.PhiChart
public import LeanPool.HyperellipticCurves.Log.Trace.TracePipeline

/-!
# Where the per-disk avoidance conditions come from

`ChabautyColeman.IsPipelineAvoid` — Weierstrass avoidance at the two reduced data of a Cantor
pipeline — is the one genericity condition the trace-form route needs beyond `IsUnit y_Q`
(see `LeanPool.HyperellipticCurves.Log.Trace.TraceAvoid`).  The condition is not new: avoidance
descends
along any base change reflecting coprimality of monic polynomials
(`ChabautyColeman.isCoprime_two_mul_of_map`), and `O⟦z⟧` is local with the residue field of
`O`, so the reflection is Nakayama: the per-disk conditions
(`ChabautyColeman.isCoprime_phiStage₂_of_residue`,
`ChabautyColeman.isCoprime_phiPipeline_of_residue`, bundled as
`ChabautyColeman.isPipelineAvoid_phi_of_residue`) reduce to conditions on the
reduced configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]` over the residue field.  The
stage
identifications on the disk side are `ChabautyColeman.phiU₁_map_seriesResidue` and
`_phiV₁_map_seriesResidue`.  (The corresponding descent for the `F_τ` pipeline lives at the
fold, `LeanPool.HyperellipticCurves.Log.Fold.FoldTrace`.)

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section PhiAvoid

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] {f uτ vτ : O[X]} {a b xQ yQ m₀ : O}
  {m : O⟦X⟧} {d : CantorCertData O⟦X⟧} {n : ℕ} (huτ : uτ.Monic)
  (hcerts : IsPipelineCerts (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d n)

include huτ hcerts

/-- **Per-disk Weierstrass avoidance at the first reduced datum is a residue-field
condition** on the reduced configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]`. -/
theorem isCoprime_phiStage₂_of_residue
    (h : IsCoprime (cantorStage₂ (f.map (residue O))
        ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).1
      (2 * (cantorStage₂ (f.map (residue O))
        ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).2)) :
    IsCoprime (cantorStage₂ (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d).1
      (2 * (cantorStage₂ (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d).2) := by
  refine isCoprime_cantorStage₂_of_map (reflectsCoprime_of_ker_le_jacobson
    (seriesResidue_surjective O) (ker_seriesResidue_le_jacobson O))
    ((monic_X_sub_C _).mul (monic_X_sub_C _)) (huτ.map _) hcerts.hc₁ ?_
  rwa [map_C_map_seriesResidue, phiConfig_map_seriesResidue]

/-- **Per-disk Weierstrass avoidance at the pipeline output is a residue-field
condition.** -/
theorem isCoprime_phiPipeline_of_residue
    (h : IsCoprime (cantorPipeline (f.map (residue O))
        ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).1
      (2 * (cantorPipeline (f.map (residue O))
        ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
          (d.map (seriesResidue O))).2)) :
    IsCoprime (cantorPipeline (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d).1
      (2 * (cantorPipeline (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d).2) := by
  refine isCoprime_cantorPipeline_of_map (reflectsCoprime_of_ker_le_jacobson
    (seriesResidue_surjective O) (ker_seriesResidue_le_jacobson O))
    ((monic_X_sub_C _).mul (monic_X_sub_C _)) (huτ.map _)
    (((monic_X_sub_C _).mul (monic_X_sub_C _)).map _) hcerts ?_
  rwa [map_C_map_seriesResidue, phiConfig_map_seriesResidue]

/-- **Per-disk Weierstrass avoidance is a residue-field condition** on the reduced
configuration `[P_bar₀ + ι Q_bar] + τ_bar + [Q_bar + ι P_bar₀]`. -/
theorem isPipelineAvoid_phi_of_residue
    (h : IsPipelineAvoid (f.map (residue O))
      ((diskCenterConfig a b xQ yQ (PowerSeries.constantCoeff m) m₀ uτ vτ).map (residue O))
        (d.map (seriesResidue O))) :
    IsPipelineAvoid (f.map PowerSeries.C) (phiConfig f a b xQ yQ m m₀ uτ vτ) d :=
  ⟨isCoprime_phiStage₂_of_residue huτ hcerts h.hcop₁,
    isCoprime_phiPipeline_of_residue huτ hcerts h.hcop₂⟩

end PhiAvoid

end ChabautyColeman

end
