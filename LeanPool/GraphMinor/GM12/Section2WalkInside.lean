/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Walks

/-!
# Passing from a smaller trace to a larger trace

The restriction and induction steps of XII (2.1), pages 243--244, use
that the inside of a trace subdrawing is contained in the inside of
the original trace. Both insides contain their supports and the selected
insides of their circuits. A circuit of the smaller subdrawing is a
circuit of the larger one, which gives the inclusion directly.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The inside operation is monotone under inclusion of drawings,
since its definition takes the union over their circuits. -/
theorem insOf_mono {S : Type*} [TopologicalSpace S]
    (ins : Drawing S → Set S) {H K : Drawing S} (hsub : H.IsSubdrawing K) :
    insOf ins H ⊆ insOf ins K := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (hsub.U_subset hx)
  · obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC.1, hC.2.trans hsub⟩, hxC⟩)

/-- The inside of a trace whose underlying drawing is a subdrawing of
another trace is contained in the latter's inside. This is the last
inclusion in the restriction and induction steps of XII (2.1). -/
theorem insWalk_mono {S : Type*} [TopologicalSpace S] [T1Space S]
    (ins : Drawing S → Set S) (K : Drawing S) {u v : S}
    (W : GraphWalk K.toGraph u u) (W' : GraphWalk K.toGraph v v)
    (hsub : (walkDrawing K W').IsSubdrawing (walkDrawing K W)) :
    insWalk ins K W' ⊆ insWalk ins K W := insOf_mono ins hsub

/-- An atom meeting the inside of a smaller trace also meets the inside
of the original trace, as used after induction in XII (2.1), Case 2. -/
theorem meets_insWalk_of_subdrawing {S : Type*} [TopologicalSpace S] [T1Space S]
    (ins : Drawing S → Set S) (K : Drawing S) {u v : S}
    (W : GraphWalk K.toGraph u u) (W' : GraphWalk K.toGraph v v)
    (hsub : (walkDrawing K W').IsSubdrawing (walkDrawing K W))
    {C : Set S} (hC : (C ∩ insWalk ins K W').Nonempty) :
    (C ∩ insWalk ins K W).Nonempty :=
  hC.mono (inter_subset_inter_right C (insWalk_mono ins K W W' hsub))

end GraphMinor.GM12
