/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# The smooth theta-PSH criterion

For a smooth real function on a complex manifold, the local-potential
definition of theta-plurisubharmonicity is equivalent to semipositivity of
`theta + dd^c u` on every complex line.  Both directions use the genuine
smooth Levi criterion.  In the reverse direction a bump-supported global
representative is chosen for each smooth germ before applying the global
Levi-to-PSH theorem.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- For a form with smooth local potentials and a smooth real function, the
local theta-PSH definition is exactly diagonal semipositivity of
`theta + dd^c u` in holomorphic coordinates. -/
theorem thetaPlurisubharmonic_smooth_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (θ : SmoothRealForm n M 2)
    (hθ : HasSmoothLocalPotentials θ) (u : M → ℝ) (hu : ChartSmooth (n := n) u) :
    ThetaPlurisubharmonic θ (fun x => (u x : EReal)) ↔
      ∀ (e : ComplexChart n M) z, z ∈ e.val.target → ∀ v : ComplexModel n,
        0 ≤ θ.coeff e z ![v, Complex.I • v] +
          smoothDDC (fun y => u (e.val.symm y)) z ![v, Complex.I • v] := by
  constructor
  · intro hpsh e z hz v
    obtain ⟨W, ρ, hzW, hρ, hcorrected⟩ := hpsh e z hz
    let f : ComplexModel n → ℝ := fun y => u (e.val.symm y) + ρ y
    have huchart : ContDiffOn ℝ ∞ (fun y => u (e.val.symm y)) W :=
      (hu e).mono hρ.2.1
    have hf : ContDiffOn ℝ ∞ f W := huchart.add hρ.2.2.1
    let Wopen : Opens (ComplexModel n) := ⟨W, hρ.1⟩
    have hfOpen : ContDiffOn ℝ ∞ f Wopen := by
      change ContDiffOn ℝ ∞ f W
      exact hf
    have hcorrectedReal :
        PlurisubharmonicOn (fun y => (f y : EReal)) Wopen := by
      change PlurisubharmonicOn (fun y => (f y : EReal)) W
      simpa only [f, chartFunction, EReal.coe_add] using hcorrected
    have hzOpen : z ∈ Wopen := hzW
    have hlevi : 0 ≤ leviForm f z v :=
      leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
        (U := Wopen) hfOpen hcorrectedReal hzOpen v
    have hf2 : ContDiffAt ℝ 2 f z :=
      ((hf z hzW).contDiffAt (hρ.1.mem_nhds hzW)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hdiag : 0 ≤ smoothDDC f z ![v, Complex.I • v] := by
      rw [smoothDDC_complexDiagonal_eq_leviForm hf2 v]
      exact div_nonneg hlevi Real.pi_pos.le
    dsimp only [f] at hdiag
    rw [smoothDDC_add hρ.1 huchart hρ.2.2.1 hzW,
      hρ.2.2.2 hzW] at hdiag
    simpa only [ContinuousAlternatingMap.add_apply, add_comm] using hdiag
  · intro hdiag e z hz
    obtain ⟨W, ρ, hzW, hρ⟩ := hθ e z hz
    refine ⟨W, ρ, hzW, hρ, ?_⟩
    let f : ComplexModel n → ℝ := fun y => u (e.val.symm y) + ρ y
    have huchart : ContDiffOn ℝ ∞ (fun y => u (e.val.symm y)) W :=
      (hu e).mono hρ.2.1
    have hf : ContDiffOn ℝ ∞ f W := huchart.add hρ.2.2.1
    have hpshReal : PlurisubharmonicOn (fun y => (f y : EReal)) W := by
      refine plurisubharmonicOn_of_contDiffOn_levi_nonneg hρ.1 hf ?_
      intro y hy v
      have hf2 : ContDiffAt ℝ 2 f y := ((hf y hy).contDiffAt (hρ.1.mem_nhds hy)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have hddc : 0 ≤ smoothDDC f y ![v, Complex.I • v] := by
        have hbase := hdiag e y (hρ.2.1 hy) v
        dsimp only [f]
        rw [smoothDDC_add hρ.1 huchart hρ.2.2.1 hy, hρ.2.2.2 hy]
        simpa only [ContinuousAlternatingMap.add_apply, add_comm] using hbase
      rw [smoothDDC_complexDiagonal_eq_leviForm hf2 v] at hddc
      have hmul := mul_nonneg hddc Real.pi_pos.le
      rwa [div_mul_cancel₀ _ Real.pi_ne_zero] at hmul
    simpa only [f, chartFunction, EReal.coe_add] using hpshReal

end

end SGPT.Foundations.Analysis.FirstPass
