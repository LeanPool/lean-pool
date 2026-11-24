/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs

/-!
# Graph Minors XII, Section 2: trace length

The first assertion of (2.1) follows from the definition of a trace: its length is twice
the number of crossings of the original drawing. Restricting traces to simple closed curves
is the topological step needed for the next part of the paper's proof.
-/

@[expose] public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
/-- The first assertion of Graph Minors XII, (2.1), page 243: `ins(W)` is defined,
since the trace has length less than twice the tangle order. -/
theorem theorem_2_1_length {Γ K : Drawing S} {φ : C(Circle, S)} {u : S}
    {W : GraphWalk K.toGraph u u} (hW : IsTrace Γ K φ W)
    {θ : ℕ} (hφ : curveLength Γ φ < θ) : W.length < 2 * θ := by
  rcases hW.2 with ⟨_, hlen, _⟩ | ⟨_, hlen, _⟩
  · omega
  · omega

end GraphMinor.GM12
