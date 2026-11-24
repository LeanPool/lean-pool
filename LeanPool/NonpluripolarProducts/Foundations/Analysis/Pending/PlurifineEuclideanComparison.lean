/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PlurifinePshTopology
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PluriharmonicLogNorm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence

/-! # Actual Euclidean refinement of the plurifine topology by real linear PSH coordinates -/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison

open FirstPass PlurifinePshTopology PluriharmonicLogNorm

noncomputable section

variable {n : ℕ}

/-- Actual constant derivatives and genuine zero-ddC PSH produce every actual real linear PSH
    coordinate. -/
theorem plurisubharmonicOn_realLinearMap (Ω : Opens (ComplexModel n))
    (L : ComplexModel n →L[ℝ] ℝ) :
    PlurisubharmonicOn (fun z => (L z : EReal)) Ω := by
  apply plurisubharmonicOn_coe_of_smoothDDC_eq_zero Ω.isOpen L.contDiff.contDiffOn
  intro z _
  exact smoothDDC_eq_zero_of_fderiv_const (L := L)
    (Eventually.of_forall fun y => L.fderiv)

/-- Genuine real and imaginary coordinate PSH evaluations produce actual plurifine-to-Euclidean
    inclusion continuity. -/
theorem continuous_subtype_val (Ω : Opens (ComplexModel n)) :
    @Continuous Ω (ComplexModel n) (topology Ω) inferInstance Subtype.val := by
  let : TopologicalSpace Ω := topology Ω
  have hcoord : ∀ j : Fin n, Continuous fun z : Ω => z.val j := by
    intro j
    let L := (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ
    let R := Complex.reCLM.comp L
    let I := Complex.imCLM.comp L
    have hR := continuous_realPsh (plurisubharmonicOn_realLinearMap Ω R)
    have hI := continuous_realPsh (plurisubharmonicOn_realLinearMap Ω I)
    have hc := (Complex.continuous_ofReal.comp hR).add
      ((Complex.continuous_ofReal.comp hI).mul (continuous_const (y := Complex.I)))
    change Continuous (fun z : Ω => ((z.val j).re : ℂ) + ((z.val j).im : ℂ) * Complex.I) at hc
    simpa only [Complex.re_add_im] using hc
  have h := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi hcoord)
  exact h

/-- The actual independently constructed initial PSH topology is finer than the actual ordinary
    subtype topology. -/
theorem topology_le_euclidean (Ω : Opens (ComplexModel n)) :
    topology Ω ≤ (inferInstance : TopologicalSpace Ω) :=
  continuous_iff_le_induced.mp (continuous_subtype_val Ω)

/-- Actual ordinary open sets pull back to actual plurifine open sets by the genuine coordinate
    inclusion. -/
theorem isOpen_euclidean {Ω : Opens (ComplexModel n)} {O : Set (ComplexModel n)}
    (hO : IsOpen O) : IsOpen[topology Ω] (Subtype.val ⁻¹' O) := by
  let : TopologicalSpace Ω := topology Ω
  exact hO.preimage (continuous_subtype_val Ω)

end

end SGPT.Foundations.Analysis.Pending.PlurifineEuclideanComparison
