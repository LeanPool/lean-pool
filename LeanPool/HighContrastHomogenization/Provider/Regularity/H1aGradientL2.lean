/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a

/-!
# High-contrast homogenization: Provider.Regularity.H1aGradientL2

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Vector-valued local `L²` control for `H¹_a` gradients

On a bounded domain, the class-honesty theorem gives integrability of
the Euclidean squared norm of the gradient slot of `MemH1a`.  This module
packages that fact as the vector-valued `L²` carrier used by finite-cube PDE
interfaces.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-- The gradient slot of a coefficient-weighted pair on a bounded domain has
an honest vector-valued `L²` realization. -/
theorem memVectorL2_grad_of_memH1a
    {d : ℕ} {V : Set (Vec d)} {b : CoeffField d}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (hVb : Bornology.IsBounded V)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemH1a b V u Du) :
    MemVectorL2 V Du := by
  have hsq : IntegrableOn (fun x => vecNormSq (Du x)) V volume :=
    integrableOn_vecNormSq_grad_of_memH1a_class hlam hell hVb hu
  have hcoord : ∀ i, MemScalarL2 V (fun x => Du x i) := by
    intro i
    apply (memLp_two_iff_integrable_sq (hu.1.2 i)).2
    refine hsq.mono' ((hu.1.2 i).pow 2) ?_
    filter_upwards with x
    have hi : 0 ≤ Du x i ^ 2 := sq_nonneg _
    have hvec : 0 ≤ vecNormSq (Du x) := vecNormSq_nonneg _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hi, abs_of_nonneg hvec] using
      sq_apply_le_vecNormSq (Du x) i
  simpa only [MemVectorL2, volumeMeasureOn] using
    (MemLp.of_eval hcoord : MemLp Du 2 (volumeMeasureOn V))

end

end HighContrast
end HCPolySupport
