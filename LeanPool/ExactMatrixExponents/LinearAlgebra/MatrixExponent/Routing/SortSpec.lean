/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Tagged.Tags
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Radix.Defs
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Permute

/-! # The tagged-permutation and stable-sort tensors of Theorem 3.1 -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Routing

/-- Select any ordered subsequence of distinct bit positions, in order
from most to least significant. -/
def key {w k : ℕ} (e : slots (word k) ↪ slots (word w)) (x : Val (word w)) : Val (word k) :=
  (bits (word k)).symm (fun i => bits (word w) x (e i))

open Classical in
/-- Returns `1` when `Radix.Stable (key e) (flatten h x) (flatten h y)` holds, and `0`
otherwise. -/
noncomputable def stableTensor (F : Type) [Field F] (h w k : ℕ)
    (e : slots (word k) ↪ slots (word w))
    (x y : Val (tree h (word w))) : F :=
  if Radix.Stable (key e) (flatten h x) (flatten h y) then 1 else 0

/-- In the tag predicate the untagged rows are the proposed outputs,
and the tagged rows are inputs bearing their destination addresses.
Both bounds count vertices plus all exterior positions. -/
def SortingBound (F : Type) [Field F] (h w : ℕ) (M : ℝ) : Prop :=
  (∃ v, Net F (Tagged.inputs h (word w)) .unit (Tagged.tag F h (word w)) v ∧
    (v + 2 ^ h * (h + 2 * w) : ℕ) ≤ M) ∧
  ∀ k (e : slots (word k) ↪ slots (word w)),
    ∃ v, Net F (tree h (word w)) (tree h (word w)) (stableTensor F h w k e) v ∧
      (v + 2 ^ h * (2 * w) : ℕ) ≤ M

end MatrixMultiplicationAllFields.MatrixExponent.Routing
