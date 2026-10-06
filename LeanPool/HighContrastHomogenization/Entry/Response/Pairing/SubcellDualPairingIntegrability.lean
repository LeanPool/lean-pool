/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SubcellCoefficientGluing
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalDeficitCarrierBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.QuadraticResponseRecombination
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalHalfEnergyIntegrability

/-!
# High-contrast homogenization: Entry.Response.Pairing.SubcellDualPairingIntegrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Subcell Dual Pairing and Its Integrability

Applying the direct full-dual Fenchel pairing of AK.HC, (A.4) to the difference between the
terminal optimizer restricted to a scale-`s` cell and that cell's own optimizer bounds the
pairing of a state `Y = (P, Q)` against the cell-average difference by the subcell's coarse-block
energy of `Y` times the square root of twice the subcell's response deficit; transported to an
almost-everywhere elliptic representative, this is the subcell dual pairing consumed by the cell
half of the cutoff-mean row. The pairing needs, coordinatewise in `L^1(P)`, the integrability of
the terminal optimizer's doubled cell mean on an aligned subcell — obtained from the Fenchel
probe at a single basis direction, since it is not a functional of the pathwise coarse block —
together with that of the subcell maximizer's own cell mean. The module serves the cell half of the
cutoff-mean row of `p.response.transfer`.
-/

section
/-!
## The full-dual pairing of the subcell difference field

The direct full-dual pairing AK.HC, display (A.4), applied to the field that the cutoff-mean rows
produce: the difference between the terminal optimizer restricted to a scale-`s` cell and that
cell's own optimizer.  The state `Y = (P, Q)` is paired with the two slots of the cell-average
difference.  The right-hand side is the cell's own coarse-block energy of `Y` — read through the
two diagonal blocks from which the source load is built — times the square root of the scalar cell
deficit.  Because the difference energy of the two states is twice the response deficit, no
subcell optimizer survives in the statement, so no measurable selection is needed downstream.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cell average of the difference between the terminal optimizer field restricted to the
cell `V` and the cell's own optimizer obeys the direct full-dual pairing bound: paired against a
state `Y = (P, Q)`, it is controlled by the total of the square roots of the two diagonal
coarse-block forms of `Y` times the square root of twice the scalar response deficit of the
restricted terminal field. -/
theorem abs_dualPairing_diff_cellAverage_le {d : ℕ} [NeZero d] {U V : Set (Vec d)} (hVU : V ⊆ U)
    (hU : IsOpen U) (hV : IsOpen V) (hConv : IsOpenBoundedConvexDomain V)
    [IsFiniteMeasure (volumeMeasureOn V)]
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam V a)
    (hvol : 0 < (volume V).toReal)
    {p q : Vec d} {u : AHarmonicFunction a U} {v : AHarmonicFunction a V}
    (hmaxV : IsResponseMaximizer V p q a v)
    (huV_int : weakFluxIntegrable V a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : IntegrableOn (scalarResponseIntegrand V a p q v) V)
    (hlin : IntegrableOn (scalarFirstVariationIntegrand V a p q v
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy : IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (Y : BlockVec d) :
    |vecDot Y.2 ((cellAverage V
            (optimizerField a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))).1
          - (cellAverage V (optimizerField a v)).1)
        + vecDot Y.1 ((cellAverage V
            (optimizerField a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))).2
          - (cellAverage V (optimizerField a v)).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V a).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V a).lowerRight Y.2)))
        * Real.sqrt (2 * (ResponseJ V p q a
            - volumeAverage V (scalarResponseIntegrand V a p q
                (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)))) := by
  let uV : AHarmonicFunction a V := u.restrictOfIsEllipticFieldOn hU hV hVU hEll
  let w : AHarmonicFunction a V :=
    AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)
  have hwgrad : ∀ x, w.toH1.grad x = uV.toH1.grad x - v.toH1.grad x := by
    intro x
    change (AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)).toH1.grad x =
      uV.toH1.grad x - v.toH1.grad x
    rw [AHarmonicFunction.grad_addSMulOfIntegrable]
    simp [sub_eq_add_neg]
  have hcell : cellAverage V (optimizerField a w) =
      cellAverage V (optimizerField a uV) - cellAverage V (optimizerField a v) := by
    refine Prod.ext ?_ ?_
    · funext i
      change volumeAverage V (fun x => w.toH1.grad x i) =
        volumeAverage V (fun x => uV.toH1.grad x i)
          - volumeAverage V (fun x => v.toH1.grad x i)
      have hf : IntegrableOn (fun x => uV.toH1.grad x i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2 uV.toH1.grad_memVectorL2 i
      have hg : IntegrableOn (fun x => v.toH1.grad x i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2 v.toH1.grad_memVectorL2 i
      have hsub : volumeAverage V (fun x => uV.toH1.grad x i - v.toH1.grad x i) =
          volumeAverage V (fun x => uV.toH1.grad x i)
            - volumeAverage V (fun x => v.toH1.grad x i) :=
        volumeAverage_sub hf hg
      calc volumeAverage V (fun x => w.toH1.grad x i)
          = volumeAverage V (fun x => uV.toH1.grad x i - v.toH1.grad x i) := by
            apply congrArg (volumeAverage V)
            funext x
            simp [hwgrad x]
        _ = volumeAverage V (fun x => uV.toH1.grad x i)
              - volumeAverage V (fun x => v.toH1.grad x i) := hsub
    · funext i
      change volumeAverage V (fun x => matVecMul (a x) (w.toH1.grad x) i) =
        volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i)
          - volumeAverage V (fun x => matVecMul (a x) (v.toH1.grad x) i)
      have hf : IntegrableOn (fun x => matVecMul (a x) (uV.toH1.grad x) i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll uV.toH1.grad_memVectorL2) i
      have hg : IntegrableOn (fun x => matVecMul (a x) (v.toH1.grad x) i) V :=
        CorrectionFieldData.integrableOn_coord_of_memVectorL2
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.toH1.grad_memVectorL2) i
      have hsub : volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i
            - matVecMul (a x) (v.toH1.grad x) i) =
          volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i)
            - volumeAverage V (fun x => matVecMul (a x) (v.toH1.grad x) i) :=
        volumeAverage_sub hf hg
      calc volumeAverage V (fun x => matVecMul (a x) (w.toH1.grad x) i)
          = volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i
              - matVecMul (a x) (v.toH1.grad x) i) := by
            apply congrArg (volumeAverage V)
            funext x
            simp [hwgrad x, matVecMul_sub_vec]
        _ = volumeAverage V (fun x => matVecMul (a x) (uV.toH1.grad x) i)
              - volumeAverage V (fun x => matVecMul (a x) (v.toH1.grad x) i) := hsub
  have henergyeq : volumeAverage V (scalarVariationEnergyIntegrand a w) =
      2 * (ResponseJ V p q a - volumeAverage V (scalarResponseIntegrand V a p q uV)) := by
    have h := difference_energy_eq_response_deficit hVU hU hV hEll hmaxV huV_int hv_int
      hresp_v hlin henergy
    have hfun : scalarVariationEnergyIntegrand a w =
        fun x => vecDot (uV.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (uV.toH1.grad x - v.toH1.grad x)) := by
      funext x
      simp only [scalarVariationEnergyIntegrand, hwgrad]
    rw [hfun]
    exact h
  have hmain := abs_dualPairing_cellAverage_le (b := a) hConv hEll hvol w Y
    (zero_le_vecDot_coarseBlockMatrix_upperLeft hConv hEll hvol Y.1)
    (zero_le_vecDot_coarseBlockMatrix_lowerRight hConv hEll hvol Y.2)
  rw [hcell, henergyeq] at hmain
  exact hmain

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell dual pairing at an almost-everywhere elliptic coefficient

The cell half of the cutoff-mean row of `p.response.transfer` pairs, on each coarse subcell of the
terminal cell, the dual variable `Y` against the difference between the cell mean of the terminal
optimizer's doubled state and the cell mean of that subcell's own optimizer.  The direct full-dual
pairing of AK.HC (A.4) bounds it by the subcell's two-term head times the square root of twice the
subcell deficit.  That estimate is stated for a pointwise elliptic coefficient; the response
coefficients `respCoeff∓ F a` are elliptic only almost everywhere, so this module runs it at a
pointwise elliptic representative and transports every quantity back across the a.e. replacement,
which leaves each of them invariant.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cell average of the doubled optimizer field is unchanged when the coefficient field is
replaced by an a.e.-equal one carrying a solution with the same gradient.  The two gradient slots
coincide on the nose, and the two flux slots agree wherever the coefficients agree, so both volume
averages coincide. -/
private theorem cellAverage_optimizerField_congr_of_ae_eq {d : ℕ} {U U' V : Set (Vec d)}
    {b c : CoeffField d} (u : AHarmonicFunction b U) (v : AHarmonicFunction c U')
    (hgrad : v.toH1.grad = u.toH1.grad) (hae : b =ᵐ[volumeMeasureOn V] c) :
    cellAverage V (optimizerField b u) = cellAverage V (optimizerField c v) := by
  refine Prod.ext ?_ ?_ <;> funext i
  · simp only [cellAverage, optimizerField, hgrad]
  · simp only [cellAverage, optimizerField, hgrad, volumeAverage]
    exact congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z)
      (integral_congr_ae (hae.mono fun x hx => by simp [hx]))

/-- The cell half of the cutoff-mean row of `p.response.transfer`.  Let `f` be pointwise elliptic
on the terminal cell `HighContrast.adaptedCell q t` and let `b` agree with `f` almost everywhere
there.  For a `b`-harmonic `u` on the terminal cell, a subcell maximizer `v` on the aligned subcell
`adaptedCellAtCenter q (t - n) w`, and a state `Y = (P, Q)`, the pairing of `Y` with the
difference of
the two cell averages is bounded by the sum of the square roots of the two diagonal coarse-block
forms of `Y`, times the square root of twice the subcell response deficit of `u`.  The bound holds
for `b` itself although only the representative `f` is pointwise elliptic, because every quantity
in the estimate is invariant under the a.e. replacement. -/
theorem abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hae : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n)
    (v : AHarmonicFunction b (adaptedCellAtCenter q (t - (n : ℤ)) w))
    (hmaxV : IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b v)
    (Y : BlockVec d) :
    |vecDot Y.2 ((cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)).1
          - (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)).1)
        + vecDot Y.1 ((cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u)).2
          - (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v)).2)|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b).lowerRight Y.2)))
        * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b
            - volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
                (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u))) := by
  have hU : IsOpen (HighContrast.adaptedCell q t) := isOpen_adaptedCell_of_isUnit hq t
  have hV : IsOpen (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal :=
    volume_adaptedCellAtCenter_toReal_pos q hq (t - (n : ℤ)) w
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    isEllipticFieldOn_subset hEll hVU hV.measurableSet
  have haeV : b =ᵐ[volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  have hmaxV' : IsResponseMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
      (Response.aHarmonicOfAEEq haeV v) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff haeV p r hmaxV
  have huV_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV) :=
    hdata.weakFlux
      ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV)
  have hv_int : weakFluxIntegrable (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      (Response.aHarmonicOfAEEq haeV v) :=
    hdata.weakFlux (Response.aHarmonicOfAEEq haeV v)
  have hmain := abs_dualPairing_diff_cellAverage_le (U := HighContrast.adaptedCell q t)
    (V := adaptedCellAtCenter q (t - (n : ℤ)) w)
    (u := Response.aHarmonicOfAEEq hae u) (v := Response.aHarmonicOfAEEq haeV v)
    hVU hU hV hConv hEllV hvol
    hmaxV' huV_int hv_int
    (hdata.response p r (Response.aHarmonicOfAEEq haeV v))
    (hdata.firstVariation p r (Response.aHarmonicOfAEEq haeV v)
      (AHarmonicFunction.addSMulOfIntegrable
        ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV)
        (Response.aHarmonicOfAEEq haeV v) huV_int hv_int (-1)))
    (hdata.energy (AHarmonicFunction.addSMulOfIntegrable
      ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV)
      (Response.aHarmonicOfAEEq haeV v) huV_int hv_int (-1))) Y
  have hA_u : cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField f
        ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV))
      = cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b u) :=
    cellAverage_optimizerField_congr_of_ae_eq
      ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV) u
      (Response.aHarmonicOfAEEq_grad hae u).symm haeV.symm
  have hA_v : cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (optimizerField f (Response.aHarmonicOfAEEq haeV v))
      = cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v) :=
    cellAverage_optimizerField_congr_of_ae_eq
      (Response.aHarmonicOfAEEq haeV v) v
      (Response.aHarmonicOfAEEq_grad haeV v).symm haeV.symm
  have hC : coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) f
      = coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b :=
    (coarseBlockMatrix_congr_of_ae_eq haeV).symm
  have hD : ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r f
      = ResponseJ (adaptedCellAtCenter q (t - (n : ℤ)) w) p r b :=
    (responseJ_congr_of_ae_eq_subset hVU hae p r).symm
  have hE : volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (adaptedCellAtCenter q (t - (n : ℤ)) w) f p r
          ((Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hV hVU hEllV))
      = volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
        (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r u) := by
    simpa only [scalarResponseIntegrand, AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn,
      H1Function.restrict] using!
      (volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae p r u)
  simpa only [hA_u, hA_v, hC, hD, hE] using hmain

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Sample integrability of the two optimizer cell means on an aligned subcell

The cell half of the cutoff-mean row of `p.response.transfer` pairs the deterministic dual variable
with the difference of two doubled optimizer cell means on each aligned subcell of the terminal
cell: the mean of the TERMINAL optimizer and the mean of the SUBCELL maximizer.  Both are needed
coordinatewise in `L^1` of the law.

The subcell maximizer mean is the block response mean of the pathwise coarse block, hence affine
in the entries of that block and integrable by `HasIntegrableCoarseBlock`.  The terminal optimizer
mean is not a functional of the block, but its difference from the subcell mean is controlled
coordinatewise by the Fenchel probe of AK Lemma A.1 read at a single basis direction: the probe
`Y = (0, δ_i)` bounds the `i`-th gradient coordinate by the square root of the `i`-th diagonal
entry of the lower-right sub-block times the square root of twice the subcell deficit, and the
probe `Y = (δ_i, 0)` bounds the `i`-th flux coordinate by the upper-left analogue.  Both envelopes
are integrable, and the terminal mean is measurable in the sample through the canonical selection,
so the terminal mean is integrable as well.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The gradient slot of the block response mean is affine in the entries of the block. -/
private theorem integrable_blockResponseMean_fst {d : ℕ} {α : Type*} [MeasurableSpace α]
    {P : Measure α} [IsFiniteMeasure P] (A : α → BlockMat d) (x : BlockVec d)
    (hA : ∀ κ l : BlockCoord d, Integrable (fun a => blockMatEntry (A a) κ l) P) (i : Fin d) :
    Integrable (fun a => (blockResponseMean (A a) x).1 i) P := by
  have hEq : (fun a => (blockResponseMean (A a) x).1 i)
      = fun a => x.1 i + ((∑ j : Fin d, blockMatEntry (A a) (Sum.inr i) (Sum.inl j) * x.1 j)
          + ∑ j : Fin d, blockMatEntry (A a) (Sum.inr i) (Sum.inr j) * x.2 j) := by
    funext a
    have h1 : (blockResponseMean (A a) x).1 i = x.1 i + (blockMatVecMul (A a) x).2 i := by
      simp only [blockResponseMean, Prod.fst_add, Pi.add_apply, blockMatVecMul_blockSwap_fst]
    rw [h1]
    simp only [blockMatVecMul, Pi.add_apply, matVecMul, blockMatEntry]
  rw [hEq]
  refine (integrable_const _).add (Integrable.add ?_ ?_)
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inr i) (Sum.inl j)).mul_const _
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inr i) (Sum.inr j)).mul_const _

/-- The flux slot of the block response mean is affine in the entries of the block. -/
private theorem integrable_blockResponseMean_snd {d : ℕ} {α : Type*} [MeasurableSpace α]
    {P : Measure α} [IsFiniteMeasure P] (A : α → BlockMat d) (x : BlockVec d)
    (hA : ∀ κ l : BlockCoord d, Integrable (fun a => blockMatEntry (A a) κ l) P) (i : Fin d) :
    Integrable (fun a => (blockResponseMean (A a) x).2 i) P := by
  have hEq : (fun a => (blockResponseMean (A a) x).2 i)
      = fun a => x.2 i + ((∑ j : Fin d, blockMatEntry (A a) (Sum.inl i) (Sum.inl j) * x.1 j)
          + ∑ j : Fin d, blockMatEntry (A a) (Sum.inl i) (Sum.inr j) * x.2 j) := by
    funext a
    have h1 : (blockResponseMean (A a) x).2 i = x.2 i + (blockMatVecMul (A a) x).1 i := by
      simp only [blockResponseMean, Prod.snd_add, Pi.add_apply, blockMatVecMul_blockSwap_snd]
    rw [h1]
    simp only [blockMatVecMul, Pi.add_apply, matVecMul, blockMatEntry]
  rw [hEq]
  refine (integrable_const _).add (Integrable.add ?_ ?_)
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inl i) (Sum.inl j)).mul_const _
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inl i) (Sum.inr j)).mul_const _

/-- **The subcell maximizer cell mean is integrable, minus sign.**  On an aligned adapted cell the
doubled optimizer cell mean of a response maximizer for the recentred coefficient `a_- = a - g` is
the block response mean of the pathwise coarse block at the load `(-p, r)`, hence affine in the
entries of that block; `HasIntegrableCoarseBlock` on the cell makes every coordinate
`P`-integrable. -/
theorem integrable_cellAverage_subcellOptimizer_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (v : (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) j w))
    (hv : ∀ a, IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) j w) p r
      (respCoeffMinus F a) (v a))
    (hblk : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffMinus F a) (v a))).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffMinus F a) (v a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hent := integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq j w F hblk
  have hid : ∀ a : CoeffSpace d,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
          (optimizerField (respCoeffMinus F a) (v a))
        = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
            (respCoeffMinus F a)) (-p, r) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCoeffMinusAt (respGrid jStar F) hq j w F a
    exact cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean hq j w hEll hae p r
      (v a) (hv a)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine (integrable_blockResponseMean_fst
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]
  · refine (integrable_blockResponseMean_snd
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]

/-- **The subcell maximizer cell mean is integrable, plus sign.**  The adjoint twin of
`integrable_cellAverage_subcellOptimizer_respCoeffMinus`, for `a_+ = aᵀ + g`. -/
theorem integrable_cellAverage_subcellOptimizer_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (v : (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) j w))
    (hv : ∀ a, IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) j w) p r
      (respCoeffPlus F a) (v a))
    (hblk : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffPlus F a) (v a))).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffPlus F a) (v a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hent := integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq j w F hblk
  have hid : ∀ a : CoeffSpace d,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
          (optimizerField (respCoeffPlus F a) (v a))
        = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
            (respCoeffPlus F a)) (-p, r) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCoeffPlusAt (respGrid jStar F) hq j w F a
    exact cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean hq j w hEll hae p r
      (v a) (hv a)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine (integrable_blockResponseMean_fst
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]
  · refine (integrable_blockResponseMean_snd
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Sample integrability of the terminal optimizer cell mean on an aligned subcell

The doubled optimizer cell mean of the TERMINAL maximizer, read on an aligned subcell of the
terminal cell, is not a functional of the pathwise coarse block, so its `P`-integrability cannot be
read off `HasIntegrableCoarseBlock`.  It follows instead from the Fenchel probe of AK Lemma A.1,
read at a single basis direction: the probe `Y = (0, δ_i)` bounds the `i`-th gradient coordinate of
the difference between the terminal mean and the subcell maximizer mean by
`√(σ_{*,V}^{-1})_{ii} √(2 D_V)`, and the probe `Y = (δ_i, 0)` bounds the `i`-th flux coordinate by
`√(𝐛_{V,ii}) √(2 D_V)`.  Both envelopes are integrable — the first factor by the entrywise
integrability of the block, the second by the integrability of the subcell deficit — and the
terminal mean is measurable in the sample through the canonical selection, so the difference, and
with the subcell mean also the terminal mean, is integrable.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal optimizer cell mean is integrable on every aligned subcell, minus sign.**  With
the subcell maximizer family `v` and the integrability of the subcell deficits, every coordinate of
the cell mean of the doubled optimizer field of the terminal maximizer family `uM` for
`a_- = a - g` is `P`-integrable on every depth-`H` aligned subcell of the terminal cell. -/
theorem integrable_cellAverage_terminalOptimizer_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hmaxV : ∀ w ∈ triadicIndexBox d H, ∀ a,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hD : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P) :
    (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i) P)
      ∧ (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by rw [ht]; ring
  subst hs
  set p : Vec d := respP (respMean P jStar F t) e with hp
  set r : Vec d := respqMinus P jStar F t e with hr
  have hkey : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i) P
        ∧ Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i) P := by
    intro w hw i
    have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (H : ℤ)) w).measurableSet
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    have hNs := integrable_cellAverage_subcellOptimizer_respCoeffMinus P jStar hjStar F hm
      (t - (H : ℤ)) w p r (v w) (hmaxV w hw) (hblk w)
    have hent := integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq (t - (H : ℤ)) w F
      (hblk w)
    have hDw := (hD w hw).const_mul (2 : ℝ)
    have hmeasM1 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffMinus P jStar hjStar F hm t e
        (Sum.inl i) uM hmax hVmeas hVU).aestronglyMeasurable
    have hmeasM2 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffMinus P jStar hjStar F hm t e
        (Sum.inr i) uM hmax hVmeas hVU).aestronglyMeasurable
    constructor
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).1 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffMinus F a)).lowerRight i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r
                    (uM a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uM a) hw (v w a) (hmaxV w hw a)
          (((0 : Vec d), Pi.single i (1 : ℝ)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).1 i) P :=
        integrable_of_abs_le (hmeasM1.sub (hNs.1 i).1)
          (integrable_sqrt_mul_sqrt_of_integrable (hent (Sum.inr i) (Sum.inr i)) hDw) hbd
      refine (hdiff.add (hNs.1 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).2 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffMinus F a)).upperLeft i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r
                    (uM a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uM a) hw (v w a) (hmaxV w hw a)
          ((Pi.single i (1 : ℝ), (0 : Vec d)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).2 i) P :=
        integrable_of_abs_le (hmeasM2.sub (hNs.2 i).1)
          (integrable_sqrt_mul_sqrt_of_integrable (hent (Sum.inl i) (Sum.inl i)) hDw) hbd
      refine (hdiff.add (hNs.2 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
  exact ⟨fun w hw i => (hkey w hw i).1, fun w hw i => (hkey w hw i).2⟩

/-- **The terminal optimizer cell mean is integrable on every aligned subcell, plus sign.**  The
adjoint twin of `integrable_cellAverage_terminalOptimizer_respCoeffMinus`, for the adjoint
recentred coefficient `a_+ = aᵀ + g`, the dual load `q^+` and the terminal maximizer family
`uP`. -/
theorem integrable_cellAverage_terminalOptimizer_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hmaxV : ∀ w ∈ triadicIndexBox d H, ∀ a,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) (v w a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hD : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P) :
    (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i) P)
      ∧ (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by rw [ht]; ring
  subst hs
  set p : Vec d := respP (respMean P jStar F t) e with hp
  set r : Vec d := respqPlus P jStar F t e with hr
  have hkey : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i) P
        ∧ Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i) P := by
    intro w hw i
    have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (H : ℤ)) w).measurableSet
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    have hNs := integrable_cellAverage_subcellOptimizer_respCoeffPlus P jStar hjStar F hm
      (t - (H : ℤ)) w p r (v w) (hmaxV w hw) (hblk w)
    have hent := integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq (t - (H : ℤ)) w F
      (hblk w)
    have hDw := (hD w hw).const_mul (2 : ℝ)
    have hmeasM1 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffPlus P jStar hjStar F hm t e
        (Sum.inl i) uP hmax hVmeas hVU).aestronglyMeasurable
    have hmeasM2 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffPlus P jStar hjStar F hm t e
        (Sum.inr i) uP hmax hVmeas hVU).aestronglyMeasurable
    constructor
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).1 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffPlus F a)).lowerRight i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r
                    (uP a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uP a) hw (v w a) (hmaxV w hw a)
          (((0 : Vec d), Pi.single i (1 : ℝ)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).1 i) P :=
        integrable_of_abs_le (hmeasM1.sub (hNs.1 i).1)
          (integrable_sqrt_mul_sqrt_of_integrable (hent (Sum.inr i) (Sum.inr i)) hDw) hbd
      refine (hdiff.add (hNs.1 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).2 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffPlus F a)).upperLeft i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r
                    (uP a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uP a) hw (v w a) (hmaxV w hw a)
          ((Pi.single i (1 : ℝ), (0 : Vec d)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).2 i) P :=
        integrable_of_abs_le (hmeasM2.sub (hNs.2 i).1)
          (integrable_sqrt_mul_sqrt_of_integrable (hent (Sum.inl i) (Sum.inl i)) hDw) hbd
      refine (hdiff.add (hNs.2 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
  exact ⟨fun w hw i => (hkey w hw i).1, fun w hw i => (hkey w hw i).2⟩

end

end HCPolySupport.HighContrast.Multiscale
end
