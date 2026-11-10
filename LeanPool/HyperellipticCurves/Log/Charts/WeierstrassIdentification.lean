/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Charts.DiskIdentification
public import LeanPool.HyperellipticCurves.Log.Charts.WeierstrassChart

/-!
# Pointwise identification of the Weierstrass disk pipeline (chart coverage)

The mirrors of `LeanPool.HyperellipticCurves.Log.Charts.DiskIdentification` at a Weierstrass residue
disk,
with the moving point `P_z = (W(z), z)` and the 2-torsion centre `P₀ = (ω, 0)`:

* `ChabautyColeman.redJ_diskPointDiff_eq_one_weierstrass`: the same-disk difference
  `[P_{z₀}] · [ιP₀]` lies in the kernel of reduction — both points reduce to `(ω_bar, 0)`,
  and the reduced centre class is its own inverse;
* `ChabautyColeman.wPipeline_monic_dvd_degree_lt`: the pipeline is a reduced datum, so its
  evaluation at `z₀ ∈ 𝔪` is the chart datum at the coordinates `ζ(z₀)`;
* `ChabautyColeman.chartClass_eq_diskPointDiff_mul_tauClass_weierstrass`: hence the chart
  class at `ζ(z₀)` is `([P_{z₀}] + [ιP₀]) · [τ]`;
* `ChabautyColeman.J1_equiv_polydisk_diskPointDiff_weierstrass`: under `thm:J1-index`'s
  bijection the kernel class corresponds to the polydisk point `ζ(z₀)`.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped PowerSeries

namespace ChabautyColeman

section WeierstrassSeriesEval

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O]
  {f : O[X]} {ω : O}

/-- The value of the Weierstrass disk series lies on the curve: `f(W(z₀)) = z₀²`. -/
theorem eval_eval_weierstrassSeries (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    f.eval (PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu)) = z₀ ^ 2 := by
  have hcrv : (f.map (PowerSeries.C : O →+* O⟦X⟧)).eval (weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.X ^ 2 := by
    rw [eval_map, ← PowerSeries.algebraMap_eq, ← aeval_def, weierstrassSeries_eval]
  have h := congrArg (PSeries.evalRingHom hz₀) hcrv
  rw [map_pow, show (PSeries.evalRingHom hz₀) PowerSeries.X = z₀ by
    rw [PSeries.evalRingHom_apply]; exact PSeries.eval_X z₀] at h
  rw [← PSeries.evalRingHom_apply hz₀]
  calc f.eval ((PSeries.evalRingHom hz₀) (weierstrassSeries hf hdeg hω hωu))
      = ((f.map PowerSeries.C).map (PSeries.evalRingHom hz₀)).eval
          ((PSeries.evalRingHom hz₀) (weierstrassSeries hf hdeg hω hωu)) := by
        rw [Polynomial.map_map, PSeries.evalRingHom_comp_C, Polynomial.map_id]
    _ = (PSeries.evalRingHom hz₀) ((f.map PowerSeries.C).eval
          (weierstrassSeries hf hdeg hω hωu)) := eval_map_apply _ _
    _ = z₀ ^ 2 := h

variable [IsAdicComplete (maximalIdeal O) O]

/-- **The two Weierstrass disk parametrizations agree**: the Hensel root at parameter `y`
is the value of the Weierstrass disk series, by uniqueness of the Hensel root. -/
theorem weierstrassRoot_eq_eval_weierstrassSeries (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    {y : O} (hy : y ∈ maximalIdeal O) :
    weierstrassRoot hf hdeg hω hωu hy = PSeries.eval y (weierstrassSeries hf hdeg hω hωu) := by
  refine hensel_unique ?_
    (isUnit_eval_of_sub_mem hωu (eval_weierstrassSeries_sub_mem hf hdeg hω hωu hy)) ?_
  · simpa using sub_mem (weierstrassRoot_sub hf hdeg hω hωu hy)
      (eval_weierstrassSeries_sub_mem hf hdeg hω hωu hy)
  · rw [weierstrassRoot_eval hf hdeg hω hωu hy, eval_eval_weierstrassSeries hf hdeg hω hωu hy]

end WeierstrassSeriesEval

section WeierstrassDiskIdent

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [CharZero (FractionRing O)] [IsAlgClosed (ResidueField O)]
  [NeZero (2 : ResidueField O)] [NeZero (2 : FractionRing O)]
  {f : O[X]} {ω : O}
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The same-disk point difference at a Weierstrass centre is in the kernel of
reduction**: the class `[P_{z₀}] · [ιP₀]` — with `P_{z₀} = (W(z₀), z₀)` the disk point and
`ιP₀ = (ω, -0) = P₀` the 2-torsion centre — reduces to `1`, because both points reduce to
`(ω_bar, 0)`. -/
theorem redJ_diskPointDiff_eq_one_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    redJ (aj (f.map (algebraMap O (FractionRing O)))
          (algebraMap O (FractionRing O) (PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu)))
          (algebraMap O (FractionRing O) z₀)
        * aj (f.map (algebraMap O (FractionRing O)))
          (algebraMap O (FractionRing O) ω)
          (algebraMap O (FractionRing O) (-(0 : O)))) = 1 := by
  set φ := algebraMap O (FractionRing O)
  set xz := PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu) with hxz
  have hcrv : (f.map (PowerSeries.C : O →+* O⟦X⟧)).eval (weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.X ^ 2 := by
    rw [eval_map, ← PowerSeries.algebraMap_eq, ← aeval_def, weierstrassSeries_eval]
  have hxzcrv : f.eval xz = z₀ ^ 2 := by
    have h := congrArg (PSeries.evalRingHom hz₀) hcrv
    rw [map_pow, show (PSeries.evalRingHom hz₀) PowerSeries.X = z₀ by
      rw [PSeries.evalRingHom_apply]; exact PSeries.eval_X z₀] at h
    rw [hxz, ← PSeries.evalRingHom_apply hz₀]
    calc f.eval ((PSeries.evalRingHom hz₀) (weierstrassSeries hf hdeg hω hωu))
        = ((f.map PowerSeries.C).map (PSeries.evalRingHom hz₀)).eval
            ((PSeries.evalRingHom hz₀) (weierstrassSeries hf hdeg hω hωu)) := by
          rw [Polynomial.map_map, PSeries.evalRingHom_comp_C, Polynomial.map_id]
      _ = (PSeries.evalRingHom hz₀) ((f.map PowerSeries.C).eval
            (weierstrassSeries hf hdeg hω hωu)) := eval_map_apply _ _
      _ = z₀ ^ 2 := h
  have hab1 : φ z₀ ^ 2 = (f.map φ).eval (φ xz) := by rw [← map_pow, ← hxzcrv, eval_map_apply]
  have hab2 : φ (-(0 : O)) ^ 2 = (f.map φ).eval (φ ω) := by
    rw [map_neg, map_zero, neg_zero, zero_pow two_ne_zero, eval_map_apply,
      ← map_zero φ, ← hω]
  rw [redJ_mul hf hdeg, redJ_aj hf hdeg hab1, redJ_aj hf hdeg hab2]
  have hxzres : residue O xz = residue O ω := by
    have h0 : residue O (xz - ω) = 0 :=
      (residue_eq_zero_iff _).mpr (eval_weierstrassSeries_sub_mem hf hdeg hω hωu hz₀)
    rwa [map_sub, sub_eq_zero] at h0
  rw [hxzres, show residue O z₀ = 0 from (residue_eq_zero_iff _).mpr hz₀, map_neg, map_zero,
    neg_zero]
  have hbar : (0 : ResidueField O) ^ 2 = (f.map (residue O)).eval (residue O ω) := by
    rw [zero_pow two_ne_zero, eval_map_apply, ← map_zero (residue O), ← hω]
  have h := aj_inv (f.map (residue O)) hbar
  rw [neg_zero] at h
  nth_rw 2 [h]
  exact mul_inv_cancel _

end WeierstrassDiskIdent

section WeierstrassPipelineChart

open scoped PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O]
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ : O[X]}
  {d : CantorCertData O⟦X⟧}

/-- The Weierstrass disk pipeline over `O⟦z⟧` returns a reduced datum. -/
theorem wPipeline_monic_dvd_degree_lt (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ) (huτ : uτ.Monic) (hdvdτ : uτ ∣ vτ ^ 2 - f)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree) :
    (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.Monic
      ∧ (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1
        ∣ (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2 ^ 2 - f.map PowerSeries.C
      ∧ (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2.degree
        < (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.degree := by
  have hu₁ : (wU₁ hf hdeg hω hωu xQ).Monic := (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hu₂ : (uτ.map (PowerSeries.C : O →+* O⟦X⟧)).Monic := huτ.map _
  have hu₃ : (phiU₃ ω xQ (O := O)).Monic := ((monic_X_sub_C _).mul (monic_X_sub_C _)).map _
  have hd₁ : wU₁ hf hdeg hω hωu xQ ∣ wV₁ hf hdeg hω hωu m ^ 2 - f.map PowerSeries.C :=
    movingPair_dvd_weierstrass hf hdeg hω hωu hsep hm hyQ
  have hd₂ : uτ.map (PowerSeries.C : O →+* O⟦X⟧)
      ∣ (vτ.map PowerSeries.C) ^ 2 - f.map PowerSeries.C := map_dvd_sq_sub _ hdvdτ
  have hsep' : IsUnit (ω - xQ) := by rw [← neg_sub]; exact hsep.neg
  have hd₃ : phiU₃ ω xQ ∣ phiV₃ xQ yQ m₀ ^ 2 - f.map PowerSeries.C :=
    map_dvd_sq_sub _ (pair_dvd hsep' hm₀ hyQ
      (by rw [neg_zero, zero_pow two_ne_zero]; exact hω.symm))
  exact cantorPipeline_monic_dvd_degree_lt hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts

variable [IsDiscreteValuationRing O] [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]

variable {w c₁ c₂ : O[X]} [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The disk chart class at `ζ(z₀)` is the same-disk difference class, Weierstrass
centre**: evaluating the chart at the coordinates `ζ(z₀)_j = eval z₀ (wZeta j)` gives the
class `([P_{z₀}] + [ιP₀]) · [τ]`. -/
theorem chartClass_eq_diskPointDiff_mul_tauClass_weierstrass (hf : f.Monic)
    (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) ∈ maximalIdeal O) :
    chartClass hu rfl hv hw hbez hζ
      = aj (f.map (algebraMap O (FractionRing O)))
          (algebraMap O (FractionRing O) (PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu)))
          (algebraMap O (FractionRing O) z₀)
        * aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) ω)
          (algebraMap O (FractionRing O) (-(0 : O)))
        * tauClass (f := f) (v := vτ) hu := by
  set φ := algebraMap O (FractionRing O)
  have hdvdτ : uτ ∣ vτ ^ 2 - f := ⟨w, hw⟩
  obtain ⟨hPmonic, hPdvd, hPdeg⟩ :=
    wPipeline_monic_dvd_degree_lt hf hdeg hω hωu hsep hm hm₀ hyQ hu hdvdτ hcerts
  have hUeq' : (chartU uτ uτ.natDegree).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ))
      = (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).1.map (PSeries.evalRingHom hz₀) := by
    rw [chartU_map_evalRingHom hζ,
      map_evalRingHom_eq_add_chartCoords hu hPmonic hcerts.hdeg hz₀]
    rfl
  have hVeq' : (chartV hu (le_refl uτ.natDegree) hv hw hbez).map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hζ))
      = (wPipeline hf hdeg hω hωu xQ yQ m m₀ uτ vτ d).2.map (PSeries.evalRingHom hz₀) :=
    (map_evalRingHom_eq_chartV_map hu hv hw hbez hPmonic hcerts.hdeg hPdvd hPdeg
      (wPipeline_map_constantCoeff hf hdeg hω hωu hsep hm hm₀ hyQ hu hv hdvdτ hgτ hcerts).2
      hz₀ hζ).symm
  rw [chartClass_eq hu rfl hv hw hbez hζ (congrArg (Polynomial.map φ) hUeq')
      (congrArg (Polynomial.map φ) hVeq') ((hPmonic.map _).map _).ne_zero,
    mk0_wPipeline_eval hf hdeg hω hωu hsep hm hm₀ hyQ hu hdvdτ hcerts hPmonic hz₀,
    aj_eq_mk0_mumfordIdeal, aj_eq_mk0_mumfordIdeal]
  simp only [map_neg, tauClass]

end WeierstrassPipelineChart

section WeierstrassJ1

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))]
  [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  {f : O[X]} {ω xQ yQ : O} {m : O⟦X⟧} {m₀ : O} {uτ vτ w c₁ c₂ : O[X]}
  {d : CantorCertData O⟦X⟧}
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  [IsAdicComplete (maximalIdeal O) O] [CharZero (FractionRing O)]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]

/-- **The polydisk coordinates of the same-disk difference class at a Weierstrass centre
are `ζ(z₀)`**: under `thm:J1-index`'s bijection, the kernel class `[P_{z₀}] + [ιP₀]` — with
`P_{z₀} = (W(z₀), z₀)` and `P₀ = (ω, 0)` — corresponds to the polydisk point
`ζ(z₀)_j = eval z₀ (wZeta j)`. -/
theorem J1_equiv_polydisk_diskPointDiff_weierstrass (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hω : f.eval ω = 0) (hωu : IsUnit (f.derivative.eval ω)) (hsep : IsUnit (xQ - ω))
    (hm : m * (PowerSeries.C xQ - weierstrassSeries hf hdeg hω hωu)
      = PowerSeries.C (-yQ) - PowerSeries.X)
    (hm₀ : m₀ * (ω - xQ) = -0 - yQ)
    (hyQ : yQ ^ 2 = f.eval xQ)
    (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) (hw : vτ ^ 2 - f = uτ * w)
    (hbez : c₁ * uτ + c₂ * (2 * vτ) = 1) (hgτ : 2 * uτ.natDegree < f.natDegree)
    (hcerts : IsPipelineCerts (f.map PowerSeries.C) (wConfig hf hdeg hω hωu xQ yQ m₀ m uτ vτ) d
      uτ.natDegree)
    (hfdeg : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * uτ.natDegree + 1)
    (hsq : Squarefree (uτ.map (residue O)))
    {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O)
    (hζ : ∀ j : Fin uτ.natDegree,
      PSeries.eval z₀ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) ∈ maximalIdeal O) :
    (J1_equiv_polydisk hu rfl hv hw hbez hf hdeg hfdeg hsq
        ⟨aj (f.map (algebraMap O (FractionRing O)))
            (algebraMap O (FractionRing O) (PSeries.eval z₀ (weierstrassSeries hf hdeg hω hωu)))
            (algebraMap O (FractionRing O) z₀)
          * aj (f.map (algebraMap O (FractionRing O))) (algebraMap O (FractionRing O) ω)
            (algebraMap O (FractionRing O) (-(0 : O))),
          MonoidHom.mem_ker.mpr
            (redJ_diskPointDiff_eq_one_weierstrass hf hdeg hω hωu hz₀)⟩).1
      = fun j ↦ PSeries.eval z₀ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j) := by
  suffices h : J1_equiv_polydisk hu rfl hv hw hbez hf hdeg hfdeg hsq _
      = ⟨fun j ↦ PSeries.eval z₀ (wZeta hf hdeg hω hωu xQ yQ m m₀ uτ vτ d j), hζ⟩ from
    congrArg Subtype.val h
  rw [J1_equiv_polydisk, Equiv.symm_apply_eq, Equiv.ofBijective_apply]
  refine Subtype.ext ?_
  change _ = chartClass hu rfl hv hw hbez hζ * (tauClass (f := f) (v := vτ) hu)⁻¹
  rw [chartClass_eq_diskPointDiff_mul_tauClass_weierstrass hf hdeg hω hωu hsep hm hm₀ hyQ
    hu hv hw hbez hgτ hcerts hz₀ hζ, mul_inv_cancel_right]

end WeierstrassJ1

end ChabautyColeman

end
