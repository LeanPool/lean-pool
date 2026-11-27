/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Error
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Linear approximation from the first `n` elements of a sequence

For a sequence `e 0, e 1, e 2, …` in `X`, the scheme `ofSpan e` has

`A n = span {e 0, …, e (n - 1)}`,

the linear span of the first `n` elements (`A 0 = span ∅ = {0}`).  This is linear
approximation in a fixed order: Fourier partial sums, polynomials of degree `< n` in the
monomial basis, the first `n` elements of a wavelet basis.  The sets are finite-dimensional
subspaces, hence closed, so a best approximant exists.  Their union is the span of the whole
sequence, so `E_n(f) → 0` exactly when `f` lies in the closed span of `e`.
-/

@[expose] public section

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The scheme of **linear approximation from the first `n` elements** of a sequence `e`:
`A n = span {e i : i < n}`. -/
def ofSpan (e : ℕ → X) : ApproximationScheme X :=
  ofSubmodules (fun n => Submodule.span ℝ (e '' Set.Iio n)) (by simp)
    fun _ _ h => Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

variable (e : ℕ → X)

/-- `A_n = span {e_i : i < n}`. -/
theorem ofSpan_apply (n : ℕ) : ofSpan e n = (Submodule.span ℝ (e '' Set.Iio n) : Set X) := rfl

/-- The sets of `ofSpan e` are finite-dimensional. -/
instance finiteDimensional_span_ofSpan (n : ℕ) :
    FiniteDimensional ℝ (Submodule.span ℝ (e '' Set.Iio n)) :=
  FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio n).image e)

/-- The sets of `ofSpan e` are closed, being finite-dimensional subspaces. -/
theorem isClosed_ofSpan (n : ℕ) : IsClosed (ofSpan e n) :=
  Submodule.isClosed_of_finiteDimensional _

/-- The union of the sets of `ofSpan e` is the span of the whole sequence. -/
theorem iUnion_ofSpan : (⋃ n, ofSpan e n) = (Submodule.span ℝ (Set.range e) : Set X) := by
  have hdir : Directed (· ≤ ·) fun n : ℕ => Submodule.span ℝ (e '' Set.Iio n) :=
    Monotone.directed_le fun _ _ h => Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))
  have hrange : (⋃ n : ℕ, e '' Set.Iio n) = Set.range e := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_Iio, Set.mem_range]
    exact ⟨fun ⟨_, i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i + 1, i, Nat.lt_succ_self i, hi⟩⟩
  rw [← hrange, Submodule.span_iUnion, Submodule.coe_iSup_of_directed _ hdir]
  rfl

/-- For `ofSpan e`, the errors tend to zero exactly on the closed span of `e`. -/
theorem tendsto_approxError_ofSpan_iff (f : X) :
    Filter.Tendsto ((ofSpan e).approxError f) Filter.atTop (nhds 0) ↔
      f ∈ closure (Submodule.span ℝ (Set.range e) : Set X) := by
  rw [tendsto_approxError_zero_iff, iUnion_ofSpan]

end ApproximationScheme
