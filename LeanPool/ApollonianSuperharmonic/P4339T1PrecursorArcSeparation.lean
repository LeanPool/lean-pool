/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4339T1PrecursorSupportGeometry
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndexAdjacentCell
public import LeanPool.ApollonianSuperharmonic.TopologicalDiskGridRayCrossingIndexZero
public import LeanPool.ApollonianSuperharmonic.P4366T1RemainderOuterAttachments
public import LeanPool.ApollonianSuperharmonic.P4366T1PrecursorPathLoop
public import LeanPool.ApollonianSuperharmonic.P4366T1AttachedRemainderIndexZero

-- [TABLET NODE: P4339T1PrecursorArcSeparation]

/-!
# P4339T1PrecursorArcSeparation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4339T1PrecursorArcSeparation :
    ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg :
        BandOrderedGeneralConfiguration q), ∀ (T : ProtoTile), ∀ (cert :
        BandOrderedGeneralLayoutCertificate q cfg C T), (BandPrototile (q 0) T) → ((LatticeTile
        T) → (∀ (D : Finset GaussianInt), ∀ (P : Finset GaussianInt), (∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T) → ((∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s)) → ((∀ i, ∀ s, ∃ e : Finset GaussianInt,
      e ∈ BoundaryFootprintEdges (cert.P i s) ∧
        e ∈ BoundaryFootprintEdges T) → ((cert.O.cells.Nonempty) → ((∀ x ∈ D \ P,
      x ∈ FootprintVertices cert.O ↔
        x ∈ ({cert.precursor_boundary.a, cert.precursor_boundary.b} :
          Finset GaussianInt)) → (
    let W := D \ P
    let R : Finset GaussianInt := {cert.precursor_boundary.a, cert.precursor_boundary.b}
    ∀ a ∈ R, ∀ b ∈ R, ∀ V, ∀ E, SimpleGridPathBetween V E a b → V ⊆ (W : Set GaussianInt) → a =
        b))))))) := by
  intro C q cfg T cert hT hlat D P hD hP hattach hO hroots
-- BODY
  classical
  dsimp only
  intro a ha b hb V E hpath hV
  by_contra hab
  have hsupport := P4339T1PrecursorSupportGeometry C q cfg T cert
  obtain ⟨hFdisk, hcover, hFattach⟩ :=
    P4366T1RemainderOuterAttachments C q cfg T cert hO (hsupport.2.2.2.1 hO) hattach
  obtain ⟨p, x, y, hnodup, hlen, hhead, hlast, hadj, hclose,
    hsegments, havoid, hnoncross, z, hcross⟩ :=
    P4366T1PrecursorPathLoop C q cfg T cert D P hD hP hO hsupport.2.2.1
      hroots a b ha hb hab V E hpath hV
  have adjacent_mem_zip (u v : GaussianInt) (l₁ l₂ : List GaussianInt) :
      (u, v) ∈ (l₁ ++ u :: v :: l₂).zip (l₁ ++ u :: v :: l₂).tail := by
    induction l₁ with
    | nil => simp
    | cons c l ih =>
        cases l with
        | nil => simp
        | cons d l =>
            simp only [List.cons_append, List.tail_cons, List.zip_cons_cons,
              List.mem_cons]
            exact Or.inr ih
  have houtside (c : GaussianInt) (hc : c ∉ T.cells) :
      GridRayCrossingIndex c p = 0 := by
    have hcenter : ((c.re : Real) + (1 / 2 : Real),
        (c.im : Real) + (1 / 2 : Real)) ∉ TileRealization T := by
      intro hm
      simp only [TileRealization, Set.mem_iUnion] at hm
      obtain ⟨d, hd, hsquare⟩ := hm
      change ((d.re : Real) ≤ (c.re : Real) + 1 / 2 ∧
          (d.im : Real) ≤ (c.im : Real) + 1 / 2) ∧
        ((c.re : Real) + 1 / 2 ≤ (d.re : Real) + 1 ∧
          (c.im : Real) + 1 / 2 ≤ (d.im : Real) + 1) at hsquare
      have hr₁ : d.re < c.re + 1 := by
        have : (d.re : Real) < ((c.re + 1 : Int) : Real) := by
          push_cast
          linarith [hsquare.1.1]
        exact_mod_cast this
      have hr₂ : c.re < d.re + 1 := by
        have : (c.re : Real) < ((d.re + 1 : Int) : Real) := by
          push_cast
          linarith [hsquare.2.1]
        exact_mod_cast this
      have hi₁ : d.im < c.im + 1 := by
        have : (d.im : Real) < ((c.im + 1 : Int) : Real) := by
          push_cast
          linarith [hsquare.1.2]
        exact_mod_cast this
      have hi₂ : c.im < d.im + 1 := by
        have : (c.im : Real) < ((d.im + 1 : Int) : Real) := by
          push_cast
          linarith [hsquare.2.2]
        exact_mod_cast this
      have hdc : d = c := Zsqrtd.ext (by omega) (by omega)
      exact hc (hdc ▸ hd)
    apply TopologicalDiskGridRayCrossingIndexZero (TileRealization T) hlat c hcenter
      p x y hhead hlast ?_ hclose ?_
    · intro u v l₁ l₂ heq
      apply hadj u v
      rw [heq]
      exact adjacent_mem_zip u v l₁ l₂
    · intro u v huv t
      apply hsegments u v ?_ t
      rcases huv with ⟨l₁, l₂, heq⟩ | huv
      · left
        rw [heq]
        exact adjacent_mem_zip u v l₁ l₂
      · exact Or.inr huv
  have hinside : ∀ i s,
      (P4366T1PrecursorRemainderFamily cert.P cert.O i s).cells ⊆ T.cells := by
    intro i s c hc
    exact ((hcover c).mpr ⟨i, s, hc⟩).1
  have hzero := P4366T1AttachedRemainderIndexZero T
    (P4366T1PrecursorRemainderFamily cert.P cert.O) hFdisk hinside hFattach
    p x y hhead hlast hnodup hlen hadj hclose havoid hnoncross houtside
  have hremaining (c : GaussianInt) (hc : c ∈ T.cells ∧ c ∉ cert.O.cells) :
      GridRayCrossingIndex c p = 0 := by
    obtain ⟨i, s, hi⟩ := (hcover c).mp hc
    exact hzero i s c hi
  have hjump := GridRayCrossingIndexAdjacentCell p x y hhead hlast hnodup hlen
    hadj hclose z
  rcases hcross with ⟨hz, hz', hedge⟩ | ⟨hz, hz', hedge⟩
  · have hunit := hjump.2.1 hedge
    rw [hremaining z hz, hremaining (z + 1) hz'] at hunit
    norm_num at hunit
  · have hunit := hjump.2.2.2 hedge
    rw [hremaining z hz, hremaining (z + ⟨0, 1⟩) hz'] at hunit
    norm_num at hunit

end ApollonianSuperharmonic

end
