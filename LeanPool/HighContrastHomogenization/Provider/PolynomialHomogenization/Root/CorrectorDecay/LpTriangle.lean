/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientIterationGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.CorrectorDecay.LpTriangle

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The normalized cube `L²` triangle inequality in subtraction form. -/
theorem cubeLpNorm_sub_le
    {d : ℕ} (Q : TriadicCube d) (f h : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hh : MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ f x - h x) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) f +
        cubeLpNorm Q (2 : ℝ≥0∞) h := by
  have hadd := cubeLpNorm_add_le Q (2 : ℝ≥0∞)
    f (-h) hf hh.neg (by norm_num)
  have hneg : cubeLpNorm Q (2 : ℝ≥0∞) (-h) =
      cubeLpNorm Q (2 : ℝ≥0∞) h := by
    unfold cubeLpNorm
    rw [MeasureTheory.eLpNorm_neg]
  have hfun : (fun x ↦ f x - h x) = f + -h := by
    funext x
    simp only [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  rw [hneg] at hadd
  rw [hfun]
  change cubeLpNorm Q (2 : ℝ≥0∞) (fun x ↦ f x + (-h) x) ≤
    cubeLpNorm Q (2 : ℝ≥0∞) f + cubeLpNorm Q (2 : ℝ≥0∞) h
  exact hadd

/-- Restriction from a centered cube to its central child preserves `L²`
integrability for the normalized measures. -/
theorem memLp_originCube_pred
    {d : ℕ} (m : ℤ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))) :
    MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (m - 1))) := by
  have hmem := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
    (Q := originCube d m) 1 hf
  have hsub : m - ((1 : ℕ) : ℤ) = m - 1 := by norm_num
  simpa only [centralDescendant_originCube_eq_originCube_sub, hsub] using hmem

/-- The normalized child `L²` norm costs at most the child count. -/
theorem cubeLpNorm_originCube_pred_le
    {d : ℕ} (m : ℤ) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))) :
    cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f ≤
      ((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f := by
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d m) 1 FiniteLpExponent.two f
  rw [centralDescendant_originCube_eq_originCube_sub] at hraw
  have hraw' : eLpNorm f 2
        (normalizedCubeMeasure (originCube d (m - 1))) ≤
      ENNReal.ofReal ((3 ^ d : ℕ) : ℝ) *
        eLpNorm f 2 (normalizedCubeMeasure (originCube d m)) := by
    simpa using hraw
  have htop : ENNReal.ofReal ((3 ^ d : ℕ) : ℝ) *
      eLpNorm f 2 (normalizedCubeMeasure (originCube d m)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hraw'
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal

/-- The same child restriction after multiplication by a nonnegative scale
weight. -/
theorem weightedCubeLpNorm_originCube_pred_le
    {d : ℕ} (m : ℤ) (f : Vec d → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hf : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m))) :
    W * cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f ≤
      ((3 ^ d : ℕ) : ℝ) *
        (W * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f) := by
  calc
    _ ≤ W * (((3 ^ d : ℕ) : ℝ) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f) :=
      mul_le_mul_of_nonneg_left (cubeLpNorm_originCube_pred_le m f hf) hW
    _ = _ := by ring

/-- Abstract weighted bookkeeping for a successor represented as a
difference of two consecutive fields. -/
theorem weightedSuccessorPrice_le
    {d : ℕ} (m : ℤ) (f0 f1 w : Vec d → ℝ)
    (Wpred Wmid Wsucc B0 B1 : ℝ)
    (hw : w = fun x ↦ f1 x - f0 x)
    (hf0 : MemLp f0 (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hf1 : MemLp f1 (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)))
    (hWpred : 0 ≤ Wpred)
    (hpredMid : Wpred = 3 * Wmid)
    (hmidSucc : Wmid = 3 * Wsucc)
    (h0 : Wmid * cubeLpNorm (originCube d (m - 1))
      (2 : ℝ≥0∞) f0 ≤ B0)
    (h1 : Wsucc * cubeLpNorm (originCube d m)
      (2 : ℝ≥0∞) f1 ≤ B1) :
    Wpred * cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) w ≤
      3 * ((3 * ((3 ^ d : ℕ) : ℝ)) * B1 + B0) := by
  have hf0pred := memLp_originCube_pred m f0 hf0
  have hf1pred := memLp_originCube_pred m f1 hf1
  have htri := cubeLpNorm_sub_le (originCube d (m - 1))
    f1 f0 hf1pred hf0pred
  have htri' : cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) w ≤
      cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f1 +
        cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f0 := by
    rw [hw]
    exact htri
  have hrestrict := weightedCubeLpNorm_originCube_pred_le
    m f1 Wpred hWpred hf1
  have hnext : Wpred * cubeLpNorm (originCube d (m - 1))
      (2 : ℝ≥0∞) f1 ≤ 9 * ((3 ^ d : ℕ) : ℝ) * B1 := by
    calc
      _ ≤ ((3 ^ d : ℕ) : ℝ) *
          (Wpred * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f1) :=
        hrestrict
      _ = (9 * ((3 ^ d : ℕ) : ℝ)) *
          (Wsucc * cubeLpNorm (originCube d m) (2 : ℝ≥0∞) f1) := by
        rw [hpredMid, hmidSucc]
        ring
      _ ≤ (9 * ((3 ^ d : ℕ) : ℝ)) * B1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 9 * ((3 ^ d : ℕ) : ℝ) * B1 := by ring
  have hcurrent : Wpred * cubeLpNorm (originCube d (m - 1))
      (2 : ℝ≥0∞) f0 ≤ 3 * B0 := by
    calc
      _ = 3 * (Wmid * cubeLpNorm (originCube d (m - 1))
          (2 : ℝ≥0∞) f0) := by rw [hpredMid]; ring
      _ ≤ 3 * B0 := mul_le_mul_of_nonneg_left h0 (by norm_num)
  calc
    _ ≤ Wpred * (cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f1 +
        cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f0) :=
      mul_le_mul_of_nonneg_left htri' hWpred
    _ = Wpred * cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f1 +
        Wpred * cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞) f0 := by ring
    _ ≤ 9 * ((3 ^ d : ℕ) : ℝ) * B1 + 3 * B0 :=
      add_le_add hnext hcurrent
    _ = 3 * ((3 * ((3 ^ d : ℕ) : ℝ)) * B1 + B0) := by ring

/-- Pure scalar composition of a terminal recurrence estimate and its local
top-energy price. -/
theorem terminal_bound_of_top
    {Dq Dtop H Clocal Crec E0 E1 N : ℝ}
    (hCrec : 1 ≤ Crec)
    (hterminal : Dq ≤ 2 * Crec * Dtop)
    (htop : Dtop = H)
    (hlocal : H ≤ Clocal * (E0 + E1) * N) :
    Dq ≤ (2 * Crec * Clocal) * (E0 + E1) * N := by
  calc
    Dq ≤ 2 * Crec * Dtop := hterminal
    _ = 2 * Crec * H := by rw [htop]
    _ ≤ 2 * Crec * (Clocal * (E0 + E1) * N) :=
      mul_le_mul_of_nonneg_left hlocal
        (mul_nonneg (by norm_num) (zero_le_one.trans hCrec))
    _ = (2 * Crec * Clocal) * (E0 + E1) * N := by ring

end

end HighContrast
end HCPolySupport
