/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.LocallyFinite

-- [TABLET NODE: P3832T1FiniteClosedCoverPasting]

/-!
# P3832T1FiniteClosedCoverPasting

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3832T1FiniteClosedCoverPasting {κ X Y : Type*}
    [Finite κ] [TopologicalSpace X] [TopologicalSpace Y]
    (S : κ → Set X) (hclosed : ∀ i, IsClosed (S i))
    (hcover : ∀ x : X, ∃ i, x ∈ S i)
    (φ : ∀ i, C(S i, Y))
    (hagree : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j),
      φ i ⟨x, hi⟩ = φ j ⟨x, hj⟩) :
    ∃ F : C(X, Y), ∀ i x (hi : x ∈ S i), F x = φ i ⟨x, hi⟩ := by
-- BODY
  classical
  let F : X→(Y) := fun x => φ (Classical.choose (hcover x))
    ⟨x,Classical.choose_spec (hcover x)⟩
  have hF (i : κ) (x : X) (hi : x ∈ S i) : F x=φ i ⟨x,hi⟩ := by
    unfold F
    exact hagree (Classical.choose (hcover x)) i x
      (Classical.choose_spec (hcover x)) hi
  have hcont (i : κ) : ContinuousOn F (S i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply Continuous.congr (φ i).continuous
    intro x
    exact (hF i x.1 x.2).symm
  have hunion : (⋃ i, S i)=Set.univ := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
    exact hcover x
  have hglobal : ContinuousOn F Set.univ := by
    rw [← hunion]
    exact (locallyFinite_of_finite S).continuousOn_iUnion hclosed hcont
  refine ⟨⟨F,continuousOn_univ.1 hglobal⟩,?_⟩
  exact hF

end ApollonianSuperharmonic

end
