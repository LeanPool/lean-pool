/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathEndpointPairUnique
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: ExactTileInterfaceDisjointCompanionEndpoints]

/-!
# ExactTileInterfaceDisjointCompanionEndpoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem ExactTileInterfaceDisjointCompanionEndpoints
    (A B C D : ProtoTile)
    (EC : ExactTileInterfaceTriple A B C)
    (ED : ExactTileInterfaceTriple A B D)
    (hA : LatticeTile A) (hB : LatticeTile B)
    (hC : LatticeTile C) (hD : LatticeTile D)
    (hABC : TouchingTriple A B C) (hABD : TouchingTriple A B D)
    (hAC : Disjoint A.cells C.cells) (hBC : Disjoint B.cells C.cells)
    (hCD : Disjoint C.cells D.cells) :
    EC.point ≠ ED.point /\
      ED.point = EC.otherAB /\ ED.otherAB = EC.point := by
-- BODY
  have hpC : EC.point ∈
      FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C :=
    (EC.unique_common EC.point).2 rfl
  have hpD : ED.point ∈
      FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices D :=
    (ED.unique_common ED.point).2 rfl
  have hne : EC.point ≠ ED.point := by
    intro heq
    have sectorsC :=
      LocalLatticeInterfaceSectors.1 A B C EC.point hA hB hC hABC hpC
    have sectorsD :=
      LocalLatticeInterfaceSectors.1 A B D ED.point hA hB hD hABD hpD
    obtain ⟨j, hjC⟩ := sectorsC.2.2.2.1
    have hjD := sectorsD.1 j
    rw [← heq] at hjD
    rcases hjD with hjA | hjB | hjD
    · exact Finset.disjoint_left.mp hAC hjA hjC
    · exact Finset.disjoint_left.mp hBC hjB hjC
    · exact Finset.disjoint_left.mp hCD hjC hjD
  have endpointPairs :=
    SimpleGridPathEndpointPairUnique EC.pathAB ED.pathAB
  have hEDne : ED.point ≠ ED.otherAB := by
    rcases ED.pathAB with ⟨p, hp, hlen, hhead, hlast, _⟩
    intro heq
    have hpne : p ≠ [] := by
      intro hpempty
      subst p
      simp at hlen
    have hh := List.head?_eq_some_head hpne
    have ht := List.getLast?_eq_some_getLast hpne
    rw [hh] at hhead
    rw [ht] at hlast
    have hheadval : p.head hpne = ED.point := by injection hhead
    have hlastval : p.getLast hpne = ED.otherAB := by injection hlast
    have hends : p.head hpne = p.getLast hpne :=
      hheadval.trans (heq.trans hlastval.symm)
    have hsingle : ∃ z, p = [z] :=
      (List.Nodup.head_eq_getLast_iff hpne hp).mp hends
    rcases hsingle with ⟨z, rfl⟩
    simp at hlen
  have hfirst : ED.point = EC.point ∨ ED.point = EC.otherAB := by
    have : ED.point ∈ ({EC.point, EC.otherAB} : Finset GaussianInt) := by
      rw [endpointPairs]
      simp
    simpa using this
  have hsecond : ED.otherAB = EC.point ∨ ED.otherAB = EC.otherAB := by
    have : ED.otherAB ∈ ({EC.point, EC.otherAB} : Finset GaussianInt) := by
      rw [endpointPairs]
      simp
    simpa using this
  rcases hfirst with hfirst | hfirst
  · exact False.elim (hne hfirst.symm)
  · rcases hsecond with hsecond | hsecond
    · exact ⟨hne, hfirst, hsecond⟩
    · exact False.elim (hEDne (hfirst.trans hsecond.symm))

end ApollonianSuperharmonic

end
