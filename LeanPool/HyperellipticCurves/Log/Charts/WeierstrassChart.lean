/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Witness.DiskPoint

/-!
# The Weierstrass disk pipeline and its chart coordinates (chart coverage)

The analogue of `LeanPool.HyperellipticCurves.Log.Charts.PhiChart`'s disk pipeline for a Weierstrass
residue
disk: the moving point is `P_z = (W(z), z)` with `W` the Weierstrass disk series (`f(W(z)) = z²`,
`W(0) = ω`), the disk centre is the 2-torsion point `P₀ = (ω, 0)`, and the pipeline computes
`[P_z + ι Q - 2∞] + τ + [Q + ι P₀ - 2∞] = [P_z] - [P₀] + τ` over `O⟦z⟧`, steered by a
certificate pack from `ChabautyColeman.exists_auxiliary_point_phi_weierstrass`.

* `ChabautyColeman.wU₁`/`wV₁`: the moving pair datum through `P_z` and `ι Q`;
* `ChabautyColeman.wConfig`: the three-block configuration it heads (the constant blocks
  are those of `LeanPool.HyperellipticCurves.Log.Charts.PhiChart` at `a := ω`, `b := 0`);
* `ChabautyColeman.wPipeline`: the pipeline on that configuration;
* `ChabautyColeman.wZeta`: its chart coordinates relative to the `τ`-centre;
* `ChabautyColeman.wPipeline_map_constantCoeff` / `ChabautyColeman.constantCoeff_wZeta`:
  at `z = 0` the pipeline returns the `τ`-datum exactly — the two pair blocks are the
  involute pair through the 2-torsion centre, so their classes cancel — hence `ζ(0) = 0`.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section WeierstrassData

variable {O : Type*} [CommRing O]

variable {f : O[X]} (hf : f.Monic) (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0)
  (hωu : IsUnit (f.derivative.eval ω))

/-- The `u`-polynomial of the moving pair datum of the Weierstrass disk pipeline: the
divisor `(P_z) + (ι Q)` with `P_z = (W(z), z)` the moving disk point. -/
noncomputable def wU₁ (xQ : O) : (O⟦X⟧)[X] :=
  (X - C (weierstrassSeries hf hdeg hω hωu)) * (X - C (PowerSeries.C xQ))

/-- The `v`-polynomial of the moving pair datum of the Weierstrass disk pipeline (slope
certificate `m`). -/
noncomputable def wV₁ (m : O⟦X⟧) : (O⟦X⟧)[X] :=
  pairV (weierstrassSeries hf hdeg hω hωu) PowerSeries.X m

variable (xQ yQ : O) (m : O⟦X⟧) (m₀ : O) (uτ vτ : O[X]) (d : CantorCertData O⟦X⟧)

/-- **The Weierstrass three-block configuration**: the moving pair block through the
Weierstrass disk point `P_z = (W(z), z)` and `ι Q`, with the `τ`-block and the constant
pair block at the 2-torsion centre `(ω, 0)` — the `ChabautyColeman.diskConfig` of the
Weierstrass chart. -/
@[simps!] noncomputable def wConfig (xQ yQ m₀ : O) (m : O⟦X⟧) (uτ vτ : O[X]) : PipelineData O⟦X⟧ :=
  diskConfig (wU₁ hf hdeg hω hωu xQ) (wV₁ hf hdeg hω hωu m) ω xQ yQ m₀ uτ vτ

/-- **The Weierstrass disk pipeline**: the Cantor pipeline computing
`[P_z + ι Q - 2∞] + τ + [Q + ι P₀ - 2∞] = [P_z] - [P₀] + τ` over `O⟦z⟧` for the moving
point `P_z = (W(z), z)` and the 2-torsion centre `P₀ = (ω, 0)`, steered by the certificate
pack `d`. -/
noncomputable def wPipeline : (O⟦X⟧)[X] × (O⟦X⟧)[X] :=
  cantorPipeline (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d

/-- **The Weierstrass disk chart coordinates `ζ(z)`**: the coefficients of the perturbation
of the pipeline's `u`-part relative to the `τ`-centre. -/
noncomputable def wZeta (j : Fin uτ.natDegree) : O⟦X⟧ :=
  chartCoords PowerSeries.C uτ (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1 j

end WeierstrassData

section WeierstrassCenterZero

variable {O : Type*} [CommRing O] [IsDomain O] {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧}
  {m₀ : O} {uτ vτ : O[X]} {d : CantorCertData O⟦X⟧}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The centre of the Weierstrass disk pipeline is the `τ`-datum**: evaluating the
pipeline at `z = 0` returns `(uτ, vτ)` exactly. At `z = 0` the two pair data are
`[P₀ + ι Q - 2∞]` and `[Q + ι P₀ - 2∞]` with `P₀ = (ω, 0)` the 2-torsion centre, whose
classes cancel, so over the fraction field the pipeline output and the `τ`-datum are
reduced representatives of the same class; the identification descends to `O` by
injectivity. -/
theorem wPipeline_map_constantCoeff (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hvτ : vτ.degree < uτ.degree) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree) :
    (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.map PowerSeries.constantCoeff = uτ
      ∧ (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2.map PowerSeries.constantCoeff
        = vτ := by
  refine cantorPipeline_map_constantCoeff_of_pair (m := m) hf
    ((monic_X_sub_C _).mul (monic_X_sub_C _))
    (movingPair_dvd_weierstrass hf hdeg hω hωu hsep hm hyQ) ?_ ?_ hsep ?_ hm₀
    (by rw [zero_pow two_ne_zero]; exact hω.symm) hyQ huτ hvτ hdvdτ hgτ hcerts
  · simp only [wU₁, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, map_C,
      RingHom.comp_apply, PowerSeries.constantCoeff_C, constantCoeff_weierstrassSeries]
  · rw [wV₁, pairV_map]
    simp only [RingHom.comp_apply, PowerSeries.constantCoeff_X, constantCoeff_weierstrassSeries,
      map_zero]
  · have h := congrArg PowerSeries.constantCoeff hm
    simpa only [map_mul, map_sub, map_neg, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, constantCoeff_weierstrassSeries, neg_zero, zero_sub] using h

/-- **`ζ(0) = 0` at a Weierstrass centre**: the disk chart coordinates vanish at `z = 0`. -/
theorem constantCoeff_wZeta (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hvτ : vτ.degree < uτ.degree) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree) (j : Fin uτ.natDegree) :
    PowerSeries.constantCoeff (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) = 0 := by
  have h := (wPipeline_map_constantCoeff hf hdeg hω hωu hsep hm hm₀ hyQ huτ hvτ hdvdτ hgτ hcerts).1
  rw [wZeta, map_chartCoords, PowerSeries.constantCoeff_comp_C, h, chartCoords,
    Polynomial.map_id, sub_self, coeff_zero]

end WeierstrassCenterZero

section WeierstrassSeriesEval

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {f : O[X]} {ω : O}

/-- The value of the Weierstrass disk series is congruent to the centre. -/
theorem eval_weierstrassSeries_sub_mem (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu) - ω ∈ maximalIdeal O := by
  have h := PSeries.eval_sub_constantCoeff_mem hz₀ (weierstrassSeries hf hdeg hω hωu)
  rwa [constantCoeff_weierstrassSeries] at h

end WeierstrassSeriesEval

section WeierstrassPointwiseClass

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]}
  {d : CantorCertData O⟦X⟧}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The Weierstrass disk pipeline computes `[P_z] - [P₀] + τ` pointwise**: evaluating the
pipeline at a point `z₀` of the maximal ideal produces a reduced Mumford datum representing
the class `(P_{z₀}) + (ι P₀) - 2∞ + [τ]` over the fraction field, where
`P_{z₀} = (W(z₀), z₀)` is the disk point and `P₀ = (ω, 0)` the 2-torsion centre. -/
theorem mk0_wPipeline_eval (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hDm : (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.Monic)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
        (((wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.map (PSeries.evalRingHom hz₀)).map
          (algebraMap O (FractionRing O)))
        (((wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2.map (PSeries.evalRingHom hz₀)).map
          (algebraMap O (FractionRing O))),
        mumfordIdeal_mem_nonZeroDivisors _ (((hDm.map _).map _).ne_zero) _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (algebraMap O (FractionRing O)
              (PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu))))
            (C (algebraMap O (FractionRing O) z₀)),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (algebraMap O (FractionRing O) ω))
            (C (-algebraMap O (FractionRing O) (0 : O))),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
        * ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (uτ.map (algebraMap O (FractionRing O)))
            (vτ.map (algebraMap O (FractionRing O))),
            mumfordIdeal_mem_nonZeroDivisors _ ((huτ.map _).ne_zero) _⟩ := by
  have hxzc := eval_weierstrassSeries_sub_mem hf hdeg hω hωu hz₀
  refine mk0_cantorPipeline_eval_of_pair (m := m) ((monic_X_sub_C _).mul (monic_X_sub_C _))
    (movingPair_dvd_weierstrass hf hdeg hω hωu hsep hm hyQ) hz₀ ?_ ?_ hxzc hsep ?_ hyQ
    (by rw [zero_pow two_ne_zero]; exact hω.symm) ?_ hm₀ huτ hdvdτ hcerts rfl hDm
  · simp [PSeries.evalRingHom_apply, PSeries.eval_C]
  · rw [pairV_map]
    simp only [RingHom.comp_apply, PSeries.evalRingHom_apply, PSeries.eval_X]
  · have h := congrArg (PSeries.evalRingHom hz₀)
      (show (f.map (PowerSeries.C : O →+* O⟦X⟧)).eval (weierstrassSeries hf hdeg hω hωu)
        = PowerSeries.X ^ 2 by
      rw [eval_map, ← PowerSeries.algebraMap_eq, ← aeval_def, weierstrassSeries_eval])
    rw [eval_map, Polynomial.hom_eval₂, PSeries.evalRingHom_comp_C, eval₂_id, map_pow] at h
    simpa only [PSeries.evalRingHom_apply, PSeries.eval_X] using h.symm
  · have h := congrArg (PSeries.evalRingHom hz₀) hm
    simp only [map_mul, map_sub, PSeries.evalRingHom_apply, PSeries.eval_C, PSeries.eval_X] at h ⊢
    linear_combination h

end WeierstrassPointwiseClass

end ChabautyColeman

end
