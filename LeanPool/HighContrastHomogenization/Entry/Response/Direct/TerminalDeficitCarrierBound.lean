/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback

/-!
# High-contrast homogenization: Entry.Response.Direct.TerminalDeficitCarrierBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sign Facts and the Carrier Form of the Subcell Deficit Bound

Continuing the terminal-optimizer replacement engine, this file records the two signs the
argument needs: restricting the terminal optimizer to a subcell gives an admissible competitor
there, so the subcell's own response dominates the restricted response, and the response of a
maximizer is itself nonnegative. It instantiates the pathwise deficit bound `|½ ⨍_V ⟨∇u,
symmPart(a) ∇u⟩ - J(V)| ≤ D + 2√(J(V) · D)` on the aligned subcells of the adapted grid,
and transports it, with the nonnegativity of both sides, to the almost-everywhere elliptic
response coefficients `respCoeff∓ F a`. It also records the pathwise `L^1(P)` integrability of
the two coordinates of the weighted optimizer field that the cutoff-mean row's comparison
integrates.  These are the sign and carrier facts consumed by the terminal-optimizer
replacement of `p.response.transfer`.
-/

section
/-!
## Nonnegativity of the subcell deficit and of the subcell response

The terminal-optimizer replacement of `p.response.transfer` needs two signs.  First, restricting the
terminal optimizer to a subcell gives an admissible competitor there, so its response value on the
subcell is at most the subcell's own response: the deficit is nonnegative.  Second, the response of
a cell is nonnegative, because at a maximizer it is half the volume average of the nonnegative
variation-energy density of that maximizer.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit is nonnegative.**  Let `V ⊆ U` be open sets, `a` a coefficient elliptic
on `V`, and `v` a response maximizer on `V` for the load `(p, r)`.  Any `a`-harmonic function `u`
on `U`, restricted to the subcell `V`, is an admissible competitor there, so its response value on
`V` is at most the subcell response `J(V; p, r; a)`.  The restriction leaves the scalar response
integrand unchanged, so the deficit `J(V) - ⨍_V g_V(u)` is nonnegative.  This is the sign input of
the terminal-optimizer replacement of `p.response.transfer`. -/
theorem volumeAverage_scalarResponseIntegrand_le_responseJ {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (p r : Vec d) (u : AHarmonicFunction a U) (v : AHarmonicFunction a V)
    (hmax : IsResponseMaximizer V p r a v) :
    volumeAverage V (scalarResponseIntegrand U a p r u) ≤ ResponseJ V p r a := by
  have hcongr : volumeAverage V (scalarResponseIntegrand U a p r u)
      = volumeAverage V (scalarResponseIntegrand V a p r
          (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)) := by
    rw [scalarResponseIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll p r u]
  calc
    volumeAverage V (scalarResponseIntegrand U a p r u)
        = volumeAverage V (scalarResponseIntegrand V a p r
            (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)) := hcongr
    _ ≤ volumeAverage V (scalarResponseIntegrand V a p r v) :=
          hmax (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)
    _ = ResponseJ V p r a :=
          (responseJ_eq_of_isResponseMaximizer V p r a hmax).symm

/-- **The subcell response is nonnegative.**  Let `a` be a coefficient elliptic on `V` and `v` a
response maximizer on `V` for the load `(p, r)`.  At a maximizer the response equals half the
volume average of the variation-energy density of `v`, and that density is nonnegative for an
elliptic coefficient, so `J(V; p, r; a) ≥ 0`.  The side conditions are the integrability
hypotheses of the energy--response identity at the maximizer.  This is the sign input of the
terminal-optimizer replacement of `p.response.transfer`. -/
theorem responseJ_nonneg_of_isResponseMaximizer {d : ℕ} {V : Set (Vec d)}
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (p r : Vec d) (v : AHarmonicFunction a V) (hmax : IsResponseMaximizer V p r a v)
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : MeasureTheory.IntegrableOn (scalarResponseIntegrand V a p r v) V)
    (hlin_self : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand V a p r v v) V)
    (henergy : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a v) V) :
    0 ≤ ResponseJ V p r a := by
  rw [responseJ_energy_of_isResponseMaximizer V a p r v hmax hv_int hresp_v hlin_self henergy]
  exact mul_nonneg (by norm_num)
    (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V a hEll v)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell deficit bound on the aligned cells of the adapted grid

`TerminalEnergyDeficitBound` proves, for an abstract pair of open sets `V ⊆ U`, that the energy of
the
restricted optimizer of `U` on `V` is controlled by the response of `V` through the deficit of the
restricted optimizer there:

  `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J(V)| ≤ J(V) - ⨍_V g_U(u) + 2 √(J(V) · (J(V) - ⨍_V g_U(u)))`.

The terminal-optimizer replacement of `p.response.transfer` consumes this estimate on the concrete
pair consisting of an aligned subcell `adaptedCellAtCenter q (t - n) w` of the coarse scale
sitting inside
the terminal cell `HighContrast.adaptedCell q t`.  This module records that instance: the subcell
is an
open bounded convex domain, it is contained in the terminal cell, and the ellipticity of `b` on the
terminal cell transfers to the subcell.  The maximizer on the subcell and the finite-measure
instance are supplied by the caller, so the bound holds for whatever subcell maximizer is at hand.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit controls the terminal optimizer's energy on an aligned adapted
subcell.**  Let `b` be elliptic on the terminal cell `HighContrast.adaptedCell q t`, let `u` be
`b`-harmonic there, and let `w ∈ triadicIndexBox d n`, so that the depth-`n` subcell
`adaptedCellAtCenter q (t - n) w` is an open bounded convex domain contained in the terminal cell.
For
any response maximizer `v` on that subcell — with the subcell response and the deficit of the
restricted parent `u` — the terminal optimizer's energy on the subcell is controlled by

  `|½ ⨍ ⟨∇u, symmPart(b) ∇u⟩ - J| ≤ D + 2 √(J · D)`

with `J = J(adaptedCellAtCenter q (t - n) w; p, r; b)` and
`D = J - ⨍ g_{adaptedCell q t}(u)`.  The caller supplies both the finite-measure instance and the
subcell maximizer together with the inequality relating them. -/
theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le {d : ℕ} [NeZero d] {q : Mat d}
    (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n)
    (hside : ∀ (_hfin : MeasureTheory.IsFiniteMeasure
          (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)))
        (v : AHarmonicFunction b (adaptedCellAtCenter q (t - (n : ℤ)) w)),
      IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b v →
      |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand b u)
          - ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b|
        ≤ (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))
          + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b *
              (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
                - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u)))) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand b u)
        - ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b|
      ≤ (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
          - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))
        + 2 * Real.sqrt (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b *
            (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
              - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                  (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))) := by
  have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVopen : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w
  have hne : (adaptedCellAtCenter q (t - (n : ℤ)) w).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hpos := volume_adaptedCellAtCenter_toReal_pos q hq (t - (n : ℤ)) w
    rw [h] at hpos
    simp at hpos
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) b :=
    hEll.mono hVopen.measurableSet hVU
  obtain ⟨v⟩ :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEllV p r
  exact hside ⟨by simpa [volumeMeasureOn] using hVfin.lt_top⟩
    (v : AHarmonicFunction b (adaptedCellAtCenter q (t - (n : ℤ)) w)) v.isResponseMaximizer

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell comparison at an almost-everywhere elliptic coefficient

`TerminalDeficitCarrierBound.abs_half_energy_adaptedCellAtCenter_sub_responseJ_le` proves, for a
pointwise
elliptic coefficient `b` on the terminal cell and any `b`-harmonic `u` there, the subcell comparison

  `|½ ⨍_V g_b(u) − J(V)| ≤ D + 2√(J(V)·D)`,  `D = J(V) − ⨍_V g_U(u)`,

on each aligned subcell `V = adaptedCellAtCenter q (t−n) w`.  The response coefficients
`respCoeff∓ F a` are elliptic only almost everywhere, so this module runs that estimate at a
pointwise elliptic representative and transports every quantity back across the a.e. replacement,
which leaves each of them invariant.  It also records the two nonnegativities the row assembly
needs: `0 ≤ J(V)` and `0 ≤ D`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The transport core of the subcell comparison: given a pointwise elliptic representative `f`
of a coefficient `b` on the terminal cell, the comparison holds for `b` itself. -/
private theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_of_aeRep {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand b u)
        - ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b|
      ≤ (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
          - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
              (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))
        + 2 * Real.sqrt
            (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
              * (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
                - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))) := by
  have hU : IsOpen (HighContrast.adaptedCell q t) := isOpen_adaptedCell_of_isUnit hq t
  have hV : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    hEll.mono hV.measurableSet hVU
  set v : AHarmonicFunction f (HighContrast.adaptedCell q t) := Response.aHarmonicOfAEEq hae u
    with hv
  have hmain := abs_half_energy_adaptedCellAtCenter_sub_responseJ_le hq t n hEll p r v hw (by
    intro hfin vv' hvv'max
    have : MeasureTheory.IsFiniteMeasure
        (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := hfin
    have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
    have huV_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
        (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV) :=
      hdata.weakFlux (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
    have hv_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f vv' :=
      hdata.weakFlux vv'
    have henergy_u : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand f v)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
      rw [← scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEllV v]
      exact hdata.energy (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
    have hgradpar :
        (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV).toH1.grad = v.toH1.grad := by
      rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
      simp only [H1Function.restrict]
    have hcross : MeasureTheory.IntegrableOn
        (fun x => vecDot (vv'.toH1.grad x)
          (matVecMul (symmPart (f x)) (v.toH1.grad x - vv'.toH1.grad x)))
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
      have h1 := hdata.cross (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV) vv'
      have h2 := hdata.cross vv' vv'
      refine (h1.sub h2).congr ?_
      filter_upwards with x
      rw [hgradpar]
      simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right,
        vecDot_neg_right, Pi.add_apply, Pi.neg_apply]
    exact abs_half_energy_sub_responseJ_le_deficit hU hV hVU hEllV v vv' hvv'max
      huV_int hv_int (hdata.response p r vv') (hdata.firstVariation p r vv' vv')
      (hdata.energy vv')
      (hdata.firstVariation p r vv'
        (AHarmonicFunction.addSMulOfIntegrable (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
          vv' huV_int hv_int (-1)))
      (hdata.energy
        (AHarmonicFunction.addSMulOfIntegrable (v.restrictOfIsEllipticFieldOn hU hV hVU hEllV)
          vv' huV_int hv_int (-1)))
      henergy_u hcross)
  have hEnergy : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarVariationEnergyIntegrand f v)
      = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarVariationEnergyIntegrand b u) := by
    rw [hv]
    exact volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff hVU hae u
  have hResp : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r v)
      = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) := by
    rw [hv]
    exact volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae p r u
  have hJ : ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
      = ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b :=
    (responseJ_congr_of_ae_eq_subset hVU hae p r).symm
  simpa only [hEnergy, hJ, hResp] using hmain

/-- The transport core of the two signs: given a pointwise elliptic representative `f` of a
coefficient `b` on the terminal cell, the subcell response and the subcell deficit for `b` are
nonnegative. -/
private theorem responseJ_nonneg_and_deficit_nonneg_of_aeRep {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    0 ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
      ∧ 0 ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) := by
  have hU : IsOpen (HighContrast.adaptedCell q t) := isOpen_adaptedCell_of_isUnit hq t
  have hV : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w
  have hne : (adaptedCellAtCenter q (t - (n : ℤ)) w).Nonempty := by
    obtain ⟨z, hz⟩ := Recurrence.adaptedCell_nonempty q (t - (n : ℤ))
    exact ⟨adaptedCellCenter q (t - (n : ℤ)) w + z, z, hz, rfl⟩
  have : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using hdom.isFiniteMeasure_restrict_volume
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    hEll.mono hV.measurableSet hVU
  set v : AHarmonicFunction f (HighContrast.adaptedCell q t) := Response.aHarmonicOfAEEq hae u
    with hv
  obtain ⟨vmax⟩ :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hdom hEllV p r
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  have hJf : 0 ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f :=
    responseJ_nonneg_of_isResponseMaximizer hEllV p r
      (vmax : AHarmonicFunction f (adaptedCellAtCenter q (t - (n : ℤ)) w)) vmax.isResponseMaximizer
      (hdata.weakFlux vmax) (hdata.response p r vmax)
      (hdata.firstVariation p r vmax vmax) (hdata.energy vmax)
  have hlef : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) f p r v)
      ≤ ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f :=
    volumeAverage_scalarResponseIntegrand_le_responseJ hU hV hVU hEllV p r v
      (vmax : AHarmonicFunction f (adaptedCellAtCenter q (t - (n : ℤ)) w)) vmax.isResponseMaximizer
  constructor
  · rw [responseJ_congr_of_ae_eq_subset hVU hae p r]
    exact hJf
  · rw [responseJ_congr_of_ae_eq_subset hVU hae p r,
      ← volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae p r u]
    rw [hv] at hlef
    linarith only [hlef]

/-- The subcell comparison on an aligned adapted subcell, for the minus family, with no
pointwise ellipticity hypothesis. -/
theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffMinus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) u)
        - ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
            (respCoeffMinus F a)|
      ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r u))
        + 2 * Real.sqrt
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                (respCoeffMinus F a)
              * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                    (respCoeffMinus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r u)))
                      := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

/-- The subcell comparison on an aligned adapted subcell, for the plus family, with no pointwise
ellipticity hypothesis. -/
theorem abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_respCoeffPlus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    |(1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) u)
        - ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
            (respCoeffPlus F a)|
      ≤ (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r u))
        + 2 * Real.sqrt
            (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                (respCoeffPlus F a)
              * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
                    (respCoeffPlus F a)
                - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                    (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r u))) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact abs_half_energy_adaptedCellAtCenter_sub_responseJ_le_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

/-- Nonnegativity of the subcell response and of the subcell deficit, minus family. -/
theorem responseJ_nonneg_and_deficit_nonneg_respCoeffMinus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffMinus F a)
      ∧ 0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
              (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r u) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  exact responseJ_nonneg_and_deficit_nonneg_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

/-- Nonnegativity of the subcell response and of the subcell deficit, plus family. -/
theorem responseJ_nonneg_and_deficit_nonneg_respCoeffPlus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ) (p r : Vec d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) :
    0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r (respCoeffPlus F a)
      ∧ 0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) p r
              (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r u) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  exact responseJ_nonneg_and_deficit_nonneg_of_aeRep
    (q := respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t n hEll hae p r u hw

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Pathwise integrability of the weighted optimizer coordinates of the cutoff-mean split

The cutoff-mean comparison of `p.response.transfer` integrates a coordinate of the doubled
optimizer state of the terminal optimizer against a bounded weight over a measurable subset of
the terminal cell.  This module records the two pathwise integrability facts that step needs for
the recentred response coefficient `respCoeffMinus F a` and for its transposed twin
`respCoeffPlus F a`: the weighted first coordinate `η · ∇v` and the weighted second coordinate
`η · (b ∇v)`, on any measurable `V` contained in the terminal cell.

The coefficient of the carrier is elliptic only almost everywhere, so the argument runs at the
pointwise elliptic representative supplied by
`exists_elliptic_representative_respCell_respCoeffMinus` / `…Plus`, extracts the coordinate
integrabilities of the representative through `ResponseLinearIntegrabilityData`, transports them
back across the almost-everywhere equality, restricts to `V`, and multiplies by the bounded
continuous weight.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Weighted optimizer coordinates for the minus response coefficient.**  For a terminal
maximizer `uM a` of the recentred coefficient `respCoeffMinus F a` on the terminal cell, and any
measurable `V` contained in that cell, both coordinates of the doubled optimizer state weighted by
a continuous `η` are integrable on `V`: the weighted gradient coordinate `η · ∇v` and the weighted
flux coordinate `η · (b ∇v)`.  The coefficient is transported from its almost-everywhere elliptic
representative, so the statement carries no pointwise ellipticity hypothesis. -/
theorem integrableOn_weighted_optimizerField_respCell_respCoeffMinus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta) (a : CoeffSpace d) (i : Fin d) :
    MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i) V
    ∧ MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) V := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    hconv.isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hgradC : MeasureTheory.IntegrableOn
      (fun x => (uM a).toH1.grad x i) (respCell jStar F t) := by
    have h := hdata.grad (Pi.single i 1) (Response.aHarmonicOfAEEq hae (uM a))
    simpa [vecDot_single_left, Response.aHarmonicOfAEEq_grad] using h
  have hfluxC : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uM a).toH1.grad x) i) (respCell jStar F t) := by
    have h := hdata.flux (Pi.single i 1) (Response.aHarmonicOfAEEq hae (uM a))
    simpa [vecDot_single_left, Response.aHarmonicOfAEEq_grad] using h
  have hgradV : MeasureTheory.IntegrableOn (fun x => (uM a).toH1.grad x i) V :=
    hgradC.mono_set hVU
  have hfluxV : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uM a).toH1.grad x) i) V := hfluxC.mono_set hVU
  have hfluxCoord : MeasureTheory.IntegrableOn
      (fun x => matVecMul ((respCoeffMinus F a) x) ((uM a).toH1.grad x) i) V := by
    refine hfluxV.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae.symm] with x hx
    rw [hx]
  have hK : IsCompact (closure (respCell jStar F t)) :=
    hconv.isBoundedDomain.isBounded.isCompact_closure
  have hVK : V ⊆ closure (respCell jStar F t) := fun x hx => subset_closure (hVU hx)
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hgradV hK hV hVK
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hfluxCoord hK hV hVK

/-- **Weighted optimizer coordinates for the plus response coefficient.**  The transposed twin of
`integrableOn_weighted_optimizerField_respCell_respCoeffMinus`: for a terminal maximizer `uP a` of
`respCoeffPlus F a` on the terminal cell and any measurable `V` contained in that cell, the
continuous-weight products `η · ∇v` and `η · (b ∇v)` are integrable on `V`. -/
theorem integrableOn_weighted_optimizerField_respCell_respCoeffPlus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ respCell jStar F t)
    {eta : Vec d → ℝ} (hetac : Continuous eta) (a : CoeffSpace d) (i : Fin d) :
    MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i) V
    ∧ MeasureTheory.IntegrableOn
      (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) V := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    hconv.isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hgradC : MeasureTheory.IntegrableOn
      (fun x => (uP a).toH1.grad x i) (respCell jStar F t) := by
    have h := hdata.grad (Pi.single i 1) (Response.aHarmonicOfAEEq hae (uP a))
    simpa [vecDot_single_left, Response.aHarmonicOfAEEq_grad] using h
  have hfluxC : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uP a).toH1.grad x) i) (respCell jStar F t) := by
    have h := hdata.flux (Pi.single i 1) (Response.aHarmonicOfAEEq hae (uP a))
    simpa [vecDot_single_left, Response.aHarmonicOfAEEq_grad] using h
  have hgradV : MeasureTheory.IntegrableOn (fun x => (uP a).toH1.grad x i) V :=
    hgradC.mono_set hVU
  have hfluxV : MeasureTheory.IntegrableOn
      (fun x => matVecMul (f x) ((uP a).toH1.grad x) i) V := hfluxC.mono_set hVU
  have hfluxCoord : MeasureTheory.IntegrableOn
      (fun x => matVecMul ((respCoeffPlus F a) x) ((uP a).toH1.grad x) i) V := by
    refine hfluxV.congr_fun_ae ?_
    filter_upwards [MeasureTheory.ae_mono
      (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae.symm] with x hx
    rw [hx]
  have hK : IsCompact (closure (respCell jStar F t)) :=
    hconv.isBoundedDomain.isBounded.isCompact_closure
  have hVK : V ⊆ closure (respCell jStar F t) := fun x hx => subset_closure (hVU hx)
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hgradV hK hV hVK
  · simpa [optimizerField] using
      IntegrableOn.continuousOn_mul_of_subset hetac.continuousOn hfluxCoord hK hV hVK

end

end HCPolySupport.HighContrast.Multiscale
end
