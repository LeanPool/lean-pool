/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.WeakTesting
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.IntegratedCoercivity

/-!
# ZerothOrderTesting

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Harmonic comparison with an additional scalar functional
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport HCPolySupport.Book.Ch02
open HCPolySupport.Book.Ch05.Section53.JUpperBoundWeakNorms

noncomputable section

variable {d : ℕ}

/-- Integral linearity for the first slot of the Euclidean pairing. -/
private theorem integral_vecDot_sub_left'
    {W : Set (Vec d)} {F G H : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) (hH : MemVectorL2 W H) :
    ∫ x in W, vecDot (F x - G x) (H x) ∂volume =
      (∫ x in W, vecDot (F x) (H x) ∂volume) -
        ∫ x in W, vecDot (G x) (H x) ∂volume := by
  have hFH := integrableOn_vecDot_of_memVectorL2 hF hH
  have hGH := integrableOn_vecDot_of_memVectorL2 hG hH
  have heq : (fun x => vecDot (F x - G x) (H x)) =
      fun x => vecDot (F x) (H x) - vecDot (G x) (H x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  rw [heq, integral_sub hFH hGH]

/-- Harmonic comparison when the tested equation contains one additional
scalar functional, quantified by `Z` times the comparison-gradient energy. -/
theorem harmonicComparison_gradientEnergy_with_test
    {W : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    {a : CoeffField d} {u h : H1Function W} {rho : H10Function W}
    {f : Vec d → Vec d} {delta alpha : ℝ}
    (hmeas : Measurable a)
    (ha : CoefficientIdentityDistanceLE W a delta)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    {zeroth Z : ℝ}
    (htest : ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
        (rho.toH1Function.grad x) ∂volume =
      zeroth - ∫ x in W, vecDot (f x) (rho.toH1Function.grad x) ∂volume)
    (hzeroth : |zeroth| ≤ Z * Real.sqrt
      (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume))
    (hZ : 0 ≤ Z)
    (hf : MemVectorL2 W f)
    (hh : IsUnitWeaklyHarmonicOn W h)
    (hgrad : ∀ x, h.grad x = u.grad x + rho.toH1Function.grad x) :
    Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) ≤
      2 * delta * Real.sqrt (∫ x in W, vecNormSq (h.grad x) ∂volume) +
        2 * Real.sqrt (∫ x in W, vecNormSq (f x) ∂volume) + 2 * Z := by
  let R : Vec d → Vec d := fun x => rho.toH1Function.grad x
  let H : Vec d → Vec d := fun x => h.grad x
  let U : Vec d → Vec d := fun x => u.grad x
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (H x)
  have hR : MemVectorL2 W R := by
    simpa only [R] using rho.toH1Function.grad_memVectorL2
  have hH : MemVectorL2 W H := by
    simpa only [H] using h.grad_memVectorL2
  have hU : MemVectorL2 W U := by
    simpa only [U] using u.grad_memVectorL2
  have haR : MemVectorL2 W (fun x => matVecMul (a x) (R x)) :=
    memVectorL2_coefficient_mul hmeas.aemeasurable ha hR
  have haH : MemVectorL2 W (fun x => matVecMul (a x) (H x)) :=
    memVectorL2_coefficient_mul hmeas.aemeasurable ha hH
  have hP : MemVectorL2 W P := by
    have heq : P = fun x => matVecMul (a x) (H x) - H x := by
      funext x
      classical
      dsimp [P]
      change (a x - 1).mulVec (H x) = (a x).mulVec (H x) - H x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [heq]
    exact haH.sub hH
  let E : ℝ := ∫ x in W, vecNormSq (R x) ∂volume
  let HH : ℝ := ∫ x in W, vecNormSq (H x) ∂volume
  let FF : ℝ := ∫ x in W, vecNormSq (f x) ∂volume
  let I : ℝ := ∫ x in W, vecDot (R x) (matVecMul (a x) (R x)) ∂volume
  let perturb : ℝ := ∫ x in W, vecDot (P x) (R x) ∂volume
  let forcing : ℝ := ∫ x in W, vecDot (f x) (R x) ∂volume
  have hE0 : 0 ≤ E := by
    exact integral_nonneg fun x => vecNormSq_nonneg (R x)
  have hHH0 : 0 ≤ HH := by
    exact integral_nonneg fun x => vecNormSq_nonneg (H x)
  have hFF0 : 0 ≤ FF := by
    exact integral_nonneg fun x => vecNormSq_nonneg (f x)
  have hcoercive : E / 2 ≤ I := by
    have haThreshold :
        CoefficientIdentityDistanceLE W a (smallContrastThreshold d alpha) := by
      filter_upwards [ha] with x hx
      exact hx.trans hdelta
    have hleft : IntegrableOn (fun x => (1 / 2 : ℝ) * vecNormSq (R x)) W :=
      (integrableOn_vecNormSq_of_memVectorL2 hR).const_mul _
    have hright : IntegrableOn
        (fun x => vecDot (R x) (matVecMul (a x) (R x))) W :=
      integrableOn_vecDot_of_memVectorL2 hR haR
    have hc := integral_half_vecNormSq_le_coefficientEnergy
      halpha0 halpha1 haThreshold hleft hright
    dsimp [E, I]
    calc
      (∫ x in W, vecNormSq (R x) ∂volume) / 2 =
          ∫ x in W, (1 / 2 : ℝ) * vecNormSq (R x) ∂volume := by
        rw [integral_const_mul]
        ring
      _ ≤ ∫ x in W, vecDot (R x) (matVecMul (a x) (R x)) ∂volume := hc
  have hunit : ∫ x in W, vecDot (H x) (R x) ∂volume = 0 := by
    simpa only [H, R] using hh rho
  have hUeq : ∀ x, U x = H x - R x := by
    intro x
    dsimp [U, H, R]
    exact (eq_sub_iff_add_eq).2 (hgrad x).symm
  have hsplitA :
      ∫ x in W, vecDot (matVecMul (a x) (U x)) (R x) ∂volume =
        (∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume) - I := by
    calc
      ∫ x in W, vecDot (matVecMul (a x) (U x)) (R x) ∂volume =
          ∫ x in W,
            vecDot (matVecMul (a x) (H x) - matVecMul (a x) (R x)) (R x)
              ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [hUeq x]
        exact congrArg (fun v => vecDot v (R x))
          (Matrix.mulVec_sub (a x) (H x) (R x))
      _ = (∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume) - I := by
        have hbase := integral_vecDot_sub_left' haH haR hR
        have hcomm :
            ∫ x in W, vecDot (matVecMul (a x) (R x)) (R x) ∂volume = I := by
          dsimp [I]
          apply integral_congr_ae
          filter_upwards with x
          exact vecDot_comm _ _
        rw [hcomm] at hbase
        exact hbase
  have hsplitPerturb :
      ∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume = perturb := by
    have hHR := integrableOn_vecDot_of_memVectorL2 hH hR
    have hPR := integrableOn_vecDot_of_memVectorL2 hP hR
    have hadd :
        ∫ x in W, vecDot (H x + P x) (R x) ∂volume =
          (∫ x in W, vecDot (H x) (R x) ∂volume) +
            ∫ x in W, vecDot (P x) (R x) ∂volume := by
      have hfun : (fun x => vecDot (H x + P x) (R x)) =
          fun x => vecDot (H x) (R x) + vecDot (P x) (R x) := by
        funext x
        rw [vecDot_add_left]
      rw [hfun, integral_add hHR hPR]
    calc
      ∫ x in W, vecDot (matVecMul (a x) (H x)) (R x) ∂volume =
          ∫ x in W, vecDot (H x + P x) (R x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        apply congrArg (fun v => vecDot v (R x))
        classical
        dsimp [P]
        change (a x).mulVec (H x) = H x + (a x - 1).mulVec (H x)
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      _ = perturb := by
        rw [hadd, hunit, zero_add]
  have hidentity : I = perturb - zeroth + forcing := by
    have hw :
        ∫ x in W, vecDot (matVecMul (a x) (U x)) (R x) ∂volume =
          zeroth - forcing := by
      simpa only [U, R, forcing] using htest
    rw [hsplitA, hsplitPerturb] at hw
    linarith only [hw]
  have hperturb : |-perturb| ≤ delta * Real.sqrt E * Real.sqrt HH := by
    rw [abs_neg]
    have hcs := abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy hP hR
    have hPbound :=
      sqrt_integral_vecNormSq_coefficientSubIdentity_mul_le_of_measurable
        hmeas ha hdelta0 hH
    dsimp [perturb, P, R, H, E, HH] at hcs hPbound ⊢
    calc
      _ ≤ (delta * Real.sqrt (∫ x in W, vecNormSq (h.grad x) ∂volume)) *
          Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) :=
        hcs.trans (mul_le_mul_of_nonneg_right hPbound (Real.sqrt_nonneg _))
      _ = delta * Real.sqrt (∫ x in W, vecNormSq (rho.toH1Function.grad x) ∂volume) *
          Real.sqrt (∫ x in W, vecNormSq (h.grad x) ∂volume) := by ring
  have hforcing : |-forcing| ≤ Real.sqrt FF * Real.sqrt E := by
    rw [abs_neg]
    have hcs := abs_integral_vecDot_le_sqrt_energy_mul_sqrt_energy hf hR
    simpa only [forcing, FF, E, R, mul_comm] using hcs
  have hI : I ≤ |-perturb| + |-forcing| + |zeroth| := by
    rw [hidentity]
    have hp := le_abs_self perturb
    have hf' := le_abs_self forcing
    have hz := neg_le_abs zeroth
    calc
      perturb - zeroth + forcing ≤ |perturb| + |zeroth| + |forcing| :=
        add_le_add (add_le_add hp hz) hf'
      _ = |perturb| + |forcing| + |zeroth| := by ring
      _ = |-perturb| + |-forcing| + |zeroth| := by rw [abs_neg, abs_neg]
  have hmain : E / 2 ≤
      delta * Real.sqrt E * Real.sqrt HH +
        Real.sqrt FF * Real.sqrt E + Z * Real.sqrt E := by
    exact hcoercive.trans <| hI.trans
      (add_le_add (add_le_add hperturb hforcing) hzeroth)
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hsHH : 0 ≤ Real.sqrt HH := Real.sqrt_nonneg HH
  have hsFF : 0 ≤ Real.sqrt FF := Real.sqrt_nonneg FF
  have hsqE : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE0
  by_cases hzE : Real.sqrt E = 0
  · rw [hzE]
    positivity
  · have hsEpos : 0 < Real.sqrt E := lt_of_le_of_ne hsE (Ne.symm hzE)
    let e := Real.sqrt E
    let hh := Real.sqrt HH
    let ff := Real.sqrt FF
    have hmain' : e ^ 2 / 2 ≤ delta * e * hh + ff * e + Z * e := by
      dsimp only [e, hh, ff]
      rw [hsqE]
      exact hmain
    have hepos : 0 < e := by exact hsEpos
    have hhalf : e / 2 ≤ delta * hh + ff + Z := by
      apply le_of_mul_le_mul_right _ hepos
      calc
        (e / 2) * e = e ^ 2 / 2 := by ring
        _ ≤ delta * e * hh + ff * e + Z * e := hmain'
        _ = (delta * hh + ff + Z) * e := by ring
    have habstract : e ≤ 2 * delta * hh + 2 * ff + 2 * Z := by
      linarith only [hhalf]
    simpa only [E, HH, FF, R, H] using habstract


end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
