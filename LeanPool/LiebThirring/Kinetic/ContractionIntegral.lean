/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.ContractionTensor
public import LeanPool.LiebThirring.Kinetic.CurryingProductMap
public import LeanPool.LiebThirring.Kinetic.CurryingTransport
public import LeanPool.LiebThirring.Kinetic.CurryingFinite
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integral formula for Hilbert-valued contraction

The adjoint definition of tensor contraction is identified with its literal
finite-spin integral formula after pairing against an arbitrary target vector.
For an L² target, the second theorem expands that target pairing as the nested
integral over its representatives.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal InnerProduct ComplexConjugate

namespace LiebThirring

variable {ι α H : Type*} [Fintype ι] [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {μ : Measure α}

/-- Weak integral formula for tensor contraction.  Since the test vector is arbitrary,
this identity uniquely determines the contracted Hilbert vector. -/
theorem inner_tensorContraction (f : Lp (EuclideanSpace ℂ ι) 2 μ)
    (ψ : Lp (PiLp 2 (fun _ : ι => H)) 2 μ) (v : H) :
    inner ℂ v (tensorContraction (ι := ι) (H := H) f ψ) =
      ∫ x, ∑ s : ι, conj (f x s) * inner ℂ v (ψ x s) ∂μ := by
  rw [tensorContraction, ContinuousLinearMap.adjoint_inner_right]
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensorInsertion_apply_ae (ι := ι) (H := H) f v] with x hx
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [hx s, inner_smul_left]

variable {β E : Type*} [MeasurableSpace β] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] {ν : Measure β}

section Joint

variable [SFinite μ] [SFinite ν]

end Joint

end LiebThirring

end
