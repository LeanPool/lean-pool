/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NegativeSobolevCubeDuality
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.HodgeProjectionL2

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Duality.CubeHodgeByDuality

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cube Hodge estimate in the negative norm, by duality

On a triadic cube the Hodge system `w` zero-trace potential, `w + F`
solenoidal, says exactly that `w` is the (negative of the) orthogonal
projection of `F` onto the zero-trace potentials.  Against a test `psi` the
projection moves to the other slot — the projector is self-adjoint for the
`L²` pairing — so the negative fractional norm of `w` is priced by the
**positive** `H^s` stability of that projection.

The step that makes this legal is the
`ofReal_abs_volumeAverage_le_sqrt_hsNormSq_mul_negSobolevNorm`: on a cube and
below the trace threshold the normalized pairing against `negSobolevNorm`
extends from compact smooth tests to every square-integrable field of finite
fractional norm.  The projected test is such a field, so no density or Besov
bridge is needed.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem vecDot_sub_left' (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]

/-- **Positive `H^s` stability of the zero-trace gradient projection on a
cube.**  Every admissible test splits into a zero-trace potential part and a
solenoidal remainder, with the potential part bounded in `H^s` by the test.
This is the positive-direction input; everything below is duality. -/
@[expose]
def CubeGradientProjectionHsStability (d : ℕ) (Q : TriadicCube d)
    (s Cproj : ℝ) : Prop :=
  0 ≤ Cproj ∧
    ∀ psi : Vec d → Vec d, IsLocalVecTest (openCubeSet Q) psi →
      ∃ P : Vec d → Vec d,
        IsPotentialZeroTraceOn (openCubeSet Q) P ∧
        IsSolenoidalOn (openCubeSet Q) (fun x => psi x - P x) ∧
        hsNormSq (openCubeSet Q) s P ≤
          ENNReal.ofReal (Cproj ^ 2) * hsNormSq (openCubeSet Q) s psi

/-- **The cube Hodge estimate in the negative fractional norm**, obtained from
the positive stability of the projection by duality. -/
theorem negSobolevNorm_le_of_cubeGradientProjectionHsStability [NeZero d]
    (Q : TriadicCube d) {s Cproj : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (hproj : CubeGradientProjectionHsStability d Q s Cproj)
    {w F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F)
    (hw : IsPotentialZeroTraceOn (openCubeSet Q) w)
    (hsol : IsSolenoidalOn (openCubeSet Q) (fun x => w x + F x)) :
    negSobolevNorm (openCubeSet Q) s w ≤
      ENNReal.ofReal Cproj * negSobolevNorm (openCubeSet Q) s F := by
  obtain ⟨hCproj, hstab⟩ := hproj
  have hwMem : MemVectorL2 (openCubeSet Q) w :=
    _root_.HCPolySupport.Book.Ch01.IsPotentialZeroTraceOn.memVectorL2 hw
  obtain ⟨v, hv⟩ := hw
  unfold negSobolevNorm
  refine iSup_le ?_
  rintro ⟨psi, htest, hnorm⟩
  obtain ⟨P, hPpot, hPsol, hPbound⟩ := hstab psi htest
  have hPmem : MemVectorL2 (openCubeSet Q) P :=
    _root_.HCPolySupport.Book.Ch01.IsPotentialZeroTraceOn.memVectorL2 hPpot
  have hpsiMem : MemVectorL2 (openCubeSet Q) psi :=
    (htest.contDiff.continuous.memLp_of_hasCompactSupport
      htest.hasCompactSupport).restrict _
  have hInt1 : IntegrableOn (fun x => vecDot (psi x) (w x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hpsiMem hwMem
  have hInt2 : IntegrableOn (fun x => vecDot (P x) (w x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hPmem hwMem
  have hInt3 : IntegrableOn (fun x => vecDot (w x) (P x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hwMem hPmem
  have hInt4 : IntegrableOn (fun x => vecDot (F x) (P x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hF hPmem
  have hIntW : IntegrableOn (fun x => vecDot (w x) (psi x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 hwMem hpsiMem
  -- the solenoidal remainder is annihilated by the zero-trace potential `w`
  have hA : ∫ x in openCubeSet Q, vecDot (psi x) (w x) ∂volume =
      ∫ x in openCubeSet Q, vecDot (P x) (w x) ∂volume := by
    have h0 := hPsol v
    rw [hv] at h0
    have hsplit : (fun x => vecDot (psi x - P x) (w x)) =
        fun x => vecDot (psi x) (w x) - vecDot (P x) (w x) := by
      funext x
      exact vecDot_sub_left' (psi x) (P x) (w x)
    rw [hsplit, integral_sub hInt1 hInt2] at h0
    linarith only [h0]
  -- the solenoidal sum is annihilated by the projected test
  obtain ⟨zPot, hz⟩ := hPpot
  have hB : ∫ x in openCubeSet Q, vecDot (w x) (P x) ∂volume =
      -∫ x in openCubeSet Q, vecDot (F x) (P x) ∂volume := by
    have h0 := hsol zPot
    rw [hz] at h0
    have hsplit : (fun x => vecDot (w x + F x) (P x)) =
        fun x => vecDot (w x) (P x) + vecDot (F x) (P x) := by
      funext x
      exact vecDot_add_left (w x) (F x) (P x)
    rw [hsplit, integral_add hInt3 hInt4] at h0
    linarith only [h0]
  have hkey : volumeAverage (openCubeSet Q) (fun x => vecDot (w x) (psi x)) =
      -volumeAverage (openCubeSet Q) (fun x => vecDot (F x) (P x)) := by
    have hcomm1 : ∫ x in openCubeSet Q, vecDot (w x) (psi x) ∂volume =
        ∫ x in openCubeSet Q, vecDot (psi x) (w x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact vecDot_comm (w x) (psi x)
    have hcomm2 : ∫ x in openCubeSet Q, vecDot (P x) (w x) ∂volume =
        ∫ x in openCubeSet Q, vecDot (w x) (P x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact vecDot_comm (P x) (w x)
    unfold volumeAverage
    rw [hcomm1, hA, hcomm2, hB, mul_neg]
  -- the fractional size of the projected test
  have hPle : hsNormSq (openCubeSet Q) s P ≤ ENNReal.ofReal (Cproj ^ 2) := by
    refine hPbound.trans ?_
    calc ENNReal.ofReal (Cproj ^ 2) * hsNormSq (openCubeSet Q) s psi ≤
        ENNReal.ofReal (Cproj ^ 2) * 1 := by gcongr
      _ = ENNReal.ofReal (Cproj ^ 2) := mul_one _
  have hPtop : hsNormSq (openCubeSet Q) s P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPle
  have hsq : ((ENNReal.ofReal Cproj) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal Cproj := by
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal Cproj) 2, ← ENNReal.rpow_mul]
    norm_num
  have hfinal : (hsNormSq (openCubeSet Q) s P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal Cproj := by
    have hstep : (hsNormSq (openCubeSet Q) s P) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal (Cproj ^ 2)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hPle (by norm_num)
    rw [ENNReal.ofReal_pow hCproj 2, hsq] at hstep
    exact hstep
  rw [dualPairing_eq_ofReal (openCubeSet Q) w psi hIntW]
  calc
    ENNReal.ofReal
        (volumeAverage (openCubeSet Q) fun x => vecDot (w x) (psi x)) ≤
        ENNReal.ofReal
          |volumeAverage (openCubeSet Q) fun x => vecDot (w x) (psi x)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal
          |volumeAverage (openCubeSet Q) fun x => vecDot (F x) (P x)| := by
        rw [hkey, abs_neg]
    _ ≤ (hsNormSq (openCubeSet Q) s P) ^ (1 / 2 : ℝ) *
          negSobolevNorm (openCubeSet Q) s F :=
      ofReal_abs_volumeAverage_le_sqrt_hsNormSq_mul_negSobolevNorm Q hs hsHalf
        F P hF hPmem.aestronglyMeasurable hPtop
    _ ≤ ENNReal.ofReal Cproj * negSobolevNorm (openCubeSet Q) s F := by
        gcongr

end

end RowSupply
end HighContrast
end HCPolySupport
