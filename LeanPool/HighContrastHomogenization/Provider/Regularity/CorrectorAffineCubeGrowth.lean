/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorRealRadiusGrowth
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalAffineH1sLoc
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorCoarseOscillationGrowth

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorAffineCubeGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Affine-plus-corrector cube growth

The forward Liouville inclusion concerns an affine function plus its anchored
corrector and an arbitrary constant.  This module adds the elementary affine
and constant pieces to the correction-only cube-growth estimate.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Adding an affine function and a constant preserves scale-linear
centered-cube growth. -/
theorem
  NormalizedLocalH1Carrier.exists_affineAdd_cubeLpNorm_le_three_pow
    {d : ℕ} [NeZero d] (z : NormalizedLocalH1Carrier d)
    (q₀ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcube : ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2 z.globalValueRepresentative ≤
        C * (3 : ℝ) ^ q)
    (e : Vec d) (c : ℝ) :
    ∃ Cfull : ℝ, 0 ≤ Cfull ∧ ∀ q : ℕ, q₀ ≤ q →
      cubeLpNorm (originCube d (q : ℤ)) 2
          (fun x => vecDot e x + z.globalValueRepresentative x + c) ≤
        Cfull * (3 : ℝ) ^ q := by
  let E : ℝ := (∑ i : Fin d, |e i|) / 2
  let Cfull : ℝ := C + E + |c|
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hCfull : 0 ≤ Cfull := by dsimp only [Cfull]; positivity
  refine ⟨Cfull, hCfull, ?_⟩
  intro q hq
  let Q : TriadicCube d := originCube d (q : ℤ)
  have haffineMem : MemLp (fun x => vecDot e x) 2 (normalizedCubeMeasure Q) := by
    let u : H1Function (openCubeSet Q) := by
      simpa only [Q, Book.Ch02.cubeDomain_coe] using
        finiteAffineBoundaryH1 (q : ℤ) e
    have hfun : u.toFun = fun x => vecDot e x := by
      simpa only [u] using! finiteAffineBoundaryH1_toFun (m := (q : ℤ)) e
    rw [← hfun]
    exact u.memL2_normalizedCubeMeasure
  have hcorrectorMem : MemLp z.globalValueRepresentative 2
      (normalizedCubeMeasure Q) := by
    simpa only [Q] using
      z.memLp_globalValueRepresentative_normalizedCubeMeasure q
  have hpairs := cubeLpNorm_add_le Q 2
    (fun x => vecDot e x) z.globalValueRepresentative
    haffineMem hcorrectorMem (by norm_num)
  have hpairMem := haffineMem.add hcorrectorMem
  have hconstMem : MemLp (fun _ : Vec d => c) 2 (normalizedCubeMeasure Q) :=
    memLp_const c
  have htotal := cubeLpNorm_add_le Q 2
    (fun x => vecDot e x + z.globalValueRepresentative x) (fun _ => c)
    hpairMem hconstMem (by norm_num)
  have haffine := cubeLpNorm_originCube_vecDot_le q e
  have hcorrector : cubeLpNorm Q 2 z.globalValueRepresentative ≤
      C * (3 : ℝ) ^ q := by
    simpa only [Q] using hcube q hq
  have hone : 1 ≤ (3 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  calc
    cubeLpNorm Q 2 (fun x => vecDot e x + z.globalValueRepresentative x + c) ≤
        cubeLpNorm Q 2 (fun x => vecDot e x + z.globalValueRepresentative x) +
          cubeLpNorm Q 2 (fun _ : Vec d => c) := htotal
    _ ≤ (cubeLpNorm Q 2 (fun x => vecDot e x) +
          cubeLpNorm Q 2 z.globalValueRepresentative) + ‖c‖ := by
      rw [cubeLpNorm_const Q 2 c (by norm_num)]
      exact add_le_add hpairs le_rfl
    _ ≤ (E * (3 : ℝ) ^ q + C * (3 : ℝ) ^ q) + |c| := by
      rw [Real.norm_eq_abs]
      exact add_le_add (add_le_add (by simpa only [E, Q] using haffine) hcorrector) le_rfl
    _ ≤ Cfull * (3 : ℝ) ^ q := by
      have hcscale : |c| ≤ |c| * (3 : ℝ) ^ q := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (abs_nonneg c)
      dsimp only [Cfull]
      linarith only [hcscale]

end

end HighContrast
end HCPolySupport
