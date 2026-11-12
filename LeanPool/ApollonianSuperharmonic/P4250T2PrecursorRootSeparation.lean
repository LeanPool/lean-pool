/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralInteriorStarClassification
public import LeanPool.ApollonianSuperharmonic.P4339T1EmptyPrecursorRoots
public import LeanPool.ApollonianSuperharmonic.P4339T1PositivePrecursorRoots
public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorArcSeparation

-- [TABLET NODE: P4250T2PrecursorRootSeparation]

/-!
# P4250T2PrecursorRootSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4250T2PrecursorRootSeparation
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hT : BandPrototile (q 0) T) (hlat : LatticeTile T)
    (D P : Finset GaussianInt)
    (hD : ∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T)
    (hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s))
    (hattach : ∀ i s, ∃ e : Finset GaussianInt,
      e ∈ BoundaryFootprintEdges (cert.P i s) ∧
        e ∈ BoundaryFootprintEdges T) :
    let W := D \ P
    let R : Finset GaussianInt := {cert.precursor_boundary.a, cert.precursor_boundary.b}
    R ⊆ W ∧
    (∀ x ∈ W, x ∈ FootprintVertices cert.O ↔ x ∈ R) ∧
    (∀ x ∈ R,
      Nat.card {is : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 ∧
      (GaussianRealPoint x = TileCentroid T ↔ cert.O.cells = ∅)) ∧
    (∀ x ∈ W,
      Nat.card {is : Fin 3 × Bool //
        x ∈ BoundaryFootprintVertices (cert.P is.1 is.2)} = 2 →
      GaussianRealPoint x = TileCentroid T → x ∈ R) ∧
    (∀ a ∈ R, ∀ b ∈ R, ∀ V E,
      SimpleGridPathBetween V E a b → V ⊆ (W : Set GaussianInt) → a = b) := by
-- BODY
  classical
  dsimp only
  have realPoint_injective : Function.Injective GaussianRealPoint := by
    intro u v huv
    apply Zsqrtd.ext
    · have hr := congrArg Prod.fst huv
      change (u.re : Real) = (v.re : Real) at hr
      exact_mod_cast hr
    · have hi := congrArg Prod.snd huv
      change (u.im : Real) = (v.im : Real) at hi
      exact_mod_cast hi
  by_cases hO : cert.O.cells = ∅
  · obtain ⟨hRW, hroots, hcount⟩ :=
      P4339T1EmptyPrecursorRoots C q cfg T cert D P hD hP hO
    refine ⟨hRW, hroots, ?_, ?_, ?_⟩
    · intro x hx
      exact ⟨(hcount x hx).1, iff_of_true (hcount x hx).2 hO⟩
    · intro x _ _ hcentral
      have ha : cert.precursor_boundary.a ∈
          ({cert.precursor_boundary.a, cert.precursor_boundary.b} :
            Finset GaussianInt) := by simp
      have hxa := realPoint_injective (hcentral.trans (hcount _ ha).2.symm)
      simpa only [hxa] using ha
    · intro a ha b hb V E _ _
      exact realPoint_injective ((hcount a ha).2.trans (hcount b hb).2.symm)
  · have hnonempty : cert.O.cells.Nonempty := Finset.nonempty_iff_ne_empty.mpr hO
    obtain ⟨hRW, hroots, hcount⟩ :=
      P4339T1PositivePrecursorRoots C q cfg T cert hlat D P hD hP hnonempty
    refine ⟨hRW, hroots, ?_, ?_, ?_⟩
    · intro x hx
      refine ⟨(hcount x hx).1, ?_⟩
      exact ⟨fun hc => ((hcount x hx).2 hc).elim, fun he => (hO he).elim⟩
    · intro x hx hk hcentral
      have hxT := (hD x).mp (Finset.mem_sdiff.mp hx).1
      have hzero := (BandOrderedGeneralInteriorStarClassification
        q cfg C T cert hlat x hxT.1 hxT.2).2.2.2 hk hcentral
      have hsupport := P4339T1PrecursorSupportGeometry C q cfg T cert
      exact (hO (hsupport.2.1.mpr hzero)).elim
    · exact P4339T1PrecursorArcSeparation
        C q cfg T cert hT hlat D P hD hP hattach hnonempty hroots

end ApollonianSuperharmonic

end
