/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PrintFaithfulPost109CapSurface
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidal

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.DomainDualityFromHodge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two printed negative rows from the domain Hodge estimate

The domain Hodge estimate prices the zero-trace potential part of a solenoidal
sum by the complementary part, in the negative fractional norm.  Given it, the
two rows of `PrintFaithfulDomainFluxDefectDuality` follow from the field
identity `a ∇u − ∇h = (∇u − ∇h) + (a − 1) ∇u` and subadditivity of the dual
norm, with

  `Cdual = 2 * Chodge + 1`.

No coefficient-law dependence enters that constant.  This is the last algebraic
step between the domain statement and the printed consumer surface.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The dual pairing is subadditive in the paired field. -/
private theorem dualPairing_add_le (V : Set (Vec d)) (F G psi : Vec d → Vec d) :
    dualPairing V (fun x => F x + G x) psi ≤
      dualPairing V F psi + dualPairing V G psi := by
  have hfun : (fun x => vecDot (F x + G x) (psi x)) =
      fun x => vecDot (F x) (psi x) + vecDot (G x) (psi x) := by
    funext x
    exact vecDot_add_left (F x) (G x) (psi x)
  by_cases hF : IntegrableOn (fun x => vecDot (F x) (psi x)) V volume
  · by_cases hG : IntegrableOn (fun x => vecDot (G x) (psi x)) V volume
    · have hsum : IntegrableOn (fun x => vecDot (F x + G x) (psi x)) V volume := by
        rw [hfun]
        exact hF.add hG
      have hval : volumeAverage V (fun x => vecDot (F x + G x) (psi x)) =
          volumeAverage V (fun x => vecDot (F x) (psi x)) +
            volumeAverage V (fun x => vecDot (G x) (psi x)) := by
        simp only [volumeAverage, hfun]
        rw [integral_add hF hG, mul_add]
      unfold dualPairing
      rw [ite_eq_left hsum, ite_eq_left hF, ite_eq_left hG, hval]
      exact ENNReal.ofReal_add_le
    · have htop : dualPairing V G psi = ⊤ := by
        unfold dualPairing
        rw [ite_eq_right hG]
      rw [htop]
      simp
  · have htop : dualPairing V F psi = ⊤ := by
      unfold dualPairing
      rw [ite_eq_right hF]
    rw [htop]
    simp

/-- The negative fractional norm is subadditive. -/
theorem negSobolevNorm_add_le (V : Set (Vec d)) (s : ℝ) (F G : Vec d → Vec d) :
    negSobolevNorm V s (fun x => F x + G x) ≤
      negSobolevNorm V s F + negSobolevNorm V s G := by
  unfold negSobolevNorm
  refine iSup_le fun psi => ?_
  refine (dualPairing_add_le V F G psi.1).trans ?_
  exact add_le_add (le_iSup (fun t : {ψ : Vec d → Vec d //
      IsLocalVecTest V ψ ∧ hsNormSq V s ψ ≤ 1} => dualPairing V F t.1) psi)
    (le_iSup (fun t : {ψ : Vec d → Vec d //
      IsLocalVecTest V ψ ∧ hsNormSq V s ψ ≤ 1} => dualPairing V G t.1) psi)

/-- The physical comparison flux is the sum of the gradient difference and the
identity-reference flux defect. -/
theorem domainFluxComparison_eq_add
    {U : Set (Vec d)} (aPhysical : CoeffField d) (u h : H1Function U) :
    (fun x => matVecMul (aPhysical x) (u.grad x) - h.grad x) =
      fun x => (u.grad x - h.grad x) +
        matVecMul (aPhysical x - 1) (u.grad x) := by
  funext x
  rw [sub_matVecMul, matVecMul_one]
  abel

/-- Affine zero-trace membership supplies the potential field of the duality
argument. -/
theorem isPotentialZeroTraceOn_gradSub_of_memAffineH10
    {U : Set (Vec d)} (u h : H1Function U) (haff : MemAffineH10 U h u) :
    IsPotentialZeroTraceOn U (fun x => u.grad x - h.grad x) := by
  obtain ⟨w, -, hw⟩ := haff
  exact IsPotentialZeroTraceOn.congr_ae hw w.isPotentialZeroTraceOn

/-- **The printed two-row duality from the domain Hodge estimate.**  The
constant is `2 * Chodge + 1`: the first row is one Hodge application, the second
adds the defect itself through subadditivity of the dual norm. -/
theorem printFaithfulDomainFluxDefectDuality_of_hodgeBound_of_potential
    {U : Set (Vec d)} {s Chodge : ℝ} (hChodge : 0 ≤ Chodge)
    (aPhysical : CoeffField d) (u h : H1Function U)
    (hF : MemVectorL2 U (fun x => matVecMul (aPhysical x - 1) (u.grad x)))
    (hpot : IsPotentialZeroTraceOn U (fun x => u.grad x - h.grad x))
    (hsol : IsSolenoidalOn U
      (fun x => matVecMul (aPhysical x) (u.grad x) - h.grad x))
    (hodge : ∀ w F : Vec d → Vec d, MemVectorL2 U F →
      IsPotentialZeroTraceOn U w →
      IsSolenoidalOn U (fun x => w x + F x) →
      negSobolevNorm U s w ≤ ENNReal.ofReal Chodge * negSobolevNorm U s F) :
    PrintFaithfulDomainFluxDefectDuality U s aPhysical u h (2 * Chodge + 1) := by
  have hsum : IsSolenoidalOn U (fun x => (u.grad x - h.grad x) +
      matVecMul (aPhysical x - 1) (u.grad x)) := by
    rw [← domainFluxComparison_eq_add aPhysical u h]
    exact hsol
  have hrow1 : negSobolevNorm U s (fun x => u.grad x - h.grad x) ≤
      ENNReal.ofReal Chodge *
        negSobolevNorm U s (fun x => matVecMul (aPhysical x - 1) (u.grad x)) :=
    hodge _ _ hF hpot hsum
  have hrow2 : negSobolevNorm U s
      (fun x => matVecMul (aPhysical x) (u.grad x) - h.grad x) ≤
      ENNReal.ofReal Chodge *
          negSobolevNorm U s (fun x => matVecMul (aPhysical x - 1) (u.grad x)) +
        negSobolevNorm U s (fun x => matVecMul (aPhysical x - 1) (u.grad x)) := by
    rw [domainFluxComparison_eq_add aPhysical u h]
    exact (negSobolevNorm_add_le U s (fun x => u.grad x - h.grad x)
      (fun x => matVecMul (aPhysical x - 1) (u.grad x))).trans
      (add_le_add hrow1 le_rfl)
  have h2 : ENNReal.ofReal (2 * Chodge) = 2 * ENNReal.ofReal Chodge := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hC : ENNReal.ofReal (2 * Chodge + 1) =
      2 * ENNReal.ofReal Chodge + 1 := by
    rw [ENNReal.ofReal_add (by linarith only [hChodge]) (by norm_num), h2,
      ENNReal.ofReal_one]
  refine ⟨by linarith only [hChodge], ?_⟩
  rw [hC]
  calc
    negSobolevNorm U s (fun x => u.grad x - h.grad x) +
        negSobolevNorm U s
          (fun x => matVecMul (aPhysical x) (u.grad x) - h.grad x) ≤
        ENNReal.ofReal Chodge *
            negSobolevNorm U s
              (fun x => matVecMul (aPhysical x - 1) (u.grad x)) +
          (ENNReal.ofReal Chodge *
              negSobolevNorm U s
                (fun x => matVecMul (aPhysical x - 1) (u.grad x)) +
            negSobolevNorm U s
              (fun x => matVecMul (aPhysical x - 1) (u.grad x))) :=
      add_le_add hrow1 hrow2
    _ = (2 * ENNReal.ofReal Chodge + 1) *
        negSobolevNorm U s
          (fun x => matVecMul (aPhysical x - 1) (u.grad x)) := by
      ring

end

end RowSupply
end HighContrast
end HCPolySupport
