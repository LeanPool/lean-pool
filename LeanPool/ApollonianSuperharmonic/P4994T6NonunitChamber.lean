/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4994T6NonunitBirth
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws
public import LeanPool.ApollonianSuperharmonic.P4994T6ChamberAdditions
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

-- [TABLET NODE: P4994T6NonunitChamber]

/-!
# P4994T6NonunitChamber

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4994T6NonunitChamber
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (C : BandCircle) (i : Fin 3) (hC : q i.succ = C.1.1)
    (hnonunit : C.1.1.1 ≠ 1)
    (base : ProtoTile) (hbase : BandPrototile C.1.1 base)
    (e f : GaussianInt) (hdet : 0 < e.re * f.im - e.im * f.re)
    (he : e ∈ TilingLattice C) (hf : f ∈ TilingLattice C)
    (hcoord : ∀ w : TilingLattice C, ∃! z : Int × Int,
      (z.1 : GaussianInt) * e + (z.2 : GaussianInt) * f = (w : GaussianInt))
    (hadj : ∀ x y : Int × Int,
      TileTouching
        (TileTranslation base ((x.1 : GaussianInt) * e + (x.2 : GaussianInt) * f))
        (TileTranslation base ((y.1 : GaussianInt) * e + (y.2 : GaussianInt) * f)) ↔
      TriangularLatticeAdjacent x y)
    (p r : Int × Int)
    (hp : (p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f =
      BandVectors.1 (q ((i + 1).succ)) (q i.succ))
    (hr : (r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f =
      (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q ((i + 2).succ))) :
    ∃ n < 6, P4994T6Chamber n p ∧ P4994T6Chamber n r := by
-- BODY
  induction hq.1 generalizing i C p r with
  | base z =>
      have positive := C.2
      have occurrence := congrArg (fun x : CircleCoordinates => x.1) hC
      fin_cases i <;> simp at occurrence
      · exact (hnonunit occurrence.symm).elim
      · omega
      · omega
  | @rotate a ha ih =>
      have previous : ProperBandQuadruple a := by
        refine ⟨ha, ?_⟩
        intro k
        fin_cases k
        · simpa using hq.2 (2 : Fin 3)
        · simpa using hq.2 (0 : Fin 3)
        · simpa using hq.2 (1 : Fin 3)
      fin_cases i
      · exact ih previous C 1 (by simpa using hC) hnonunit hbase he hf hcoord
          p r (by simpa using hp) (by simpa using hr)
      · exact ih previous C 2 (by simpa using hC) hnonunit hbase he hf hcoord
          p r (by simpa using hp) (by simpa using hr)
      · exact ih previous C 0 (by simpa using hC) hnonunit hbase he hf hcoord
          p r (by simpa using hp) (by simpa using hr)
  | @successor a ha ih =>
      rcases SemiProperForestClassification a ha with ⟨_, cases⟩
      rcases cases with root | root | root | proper
      · obtain ⟨z, rfl⟩ := root
        have positive := C.2
        have occurrence := congrArg (fun x : CircleCoordinates => x.1) hC
        fin_cases i <;> simp at occurrence
        · exact (hnonunit occurrence.symm).elim
        · omega
        · omega
      · obtain ⟨z, rfl⟩ := root
        have positive := C.2
        have occurrence := congrArg (fun x : CircleCoordinates => x.1) hC
        fin_cases i <;> simp at occurrence
        · exact (hnonunit occurrence.symm).elim
        · omega
        · exact (hnonunit occurrence.symm).elim
      · obtain ⟨z, rfl⟩ := root
        have positive := C.2
        have occurrence := congrArg (fun x : CircleCoordinates => x.1) hC
        fin_cases i <;> simp at occurrence
        · exact (hnonunit occurrence.symm).elim
        · exact (hnonunit occurrence.symm).elim
        · omega
      · fin_cases i
        · have haC : a 0 = C.1.1 := by simpa using hC
          have second : (r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f =
              -BandVectors.1 (a 3) (a 0) := by
            have flip := ((VectorRecursionLaws a ha).2.2.2.2 proper 2).1
            change BandVectors.1 (a 0) (a 3) =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 0) at flip
            change (r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 0) (a 3) at hr
            rw [hr, flip]
            ext <;> simp
          exact P4994T6NonunitBirth a proper C haC hnonunit base hbase
            e f hdet he hf hcoord hadj p r (by simpa using hp) second
        · have old_first : (p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f =
              BandVectors.1 (a 3) (a 2) := by simpa using hp
          have second_recursion := (VectorRecursionLaws ![a 0, a 2, a 3, a 1]
            (SemiProperQuadruple.rotate ha)).2.2.1
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three] at second_recursion
          have second_addition : (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 0) =
              BandVectors.1 (a 3) (a 2) +
                (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 1) := by
            rw [second_recursion]
            ext <;> simp <;> ring
          have current : (r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 0) := by simpa using hr
          have old_second : ((r - p).1 : GaussianInt) * e +
              ((r - p).2 : GaussianInt) * f =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 2) (a 1) := by
            simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
            calc
              _ = ((r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f) -
                  ((p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f) := by ring
              _ = _ := by rw [current, old_first, second_addition]; ring
          obtain ⟨n, hn, first, second⟩ := ih proper C 1 (by simpa using hC)
            hnonunit hbase he hf hcoord p (r - p) old_first old_second
          have eqsum : p + (r - p) = r := by ext <;> simp
          exact ⟨n, hn, first, by
            simpa only [eqsum] using (P4994T6ChamberAdditions n p (r - p) first second).1⟩
        · have current : (p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f =
              BandVectors.1 (a 0) (a 3) := by simpa using hp
          have third_recursion := (VectorRecursionLaws ![a 0, a 3, a 1, a 2]
            (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate ha))).2.2.1
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.cons_val_three] at third_recursion
          have flip : BandVectors.1 (a 0) (a 3) =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 0) := by
            simpa using ((VectorRecursionLaws a ha).2.2.2.2 proper 2).1
          have third_addition : BandVectors.1 (a 0) (a 3) =
              BandVectors.1 (a 1) (a 3) +
                (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 2) := by
            rw [flip, third_recursion]
            ext <;> simp <;> ring
          have old_second : (r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f =
              (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (a 3) (a 2) := by simpa using hr
          have old_first : ((p - r).1 : GaussianInt) * e +
              ((p - r).2 : GaussianInt) * f = BandVectors.1 (a 1) (a 3) := by
            simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
            calc
              _ = ((p.1 : GaussianInt) * e + (p.2 : GaussianInt) * f) -
                  ((r.1 : GaussianInt) * e + (r.2 : GaussianInt) * f) := by ring
              _ = _ := by rw [current, old_second, third_addition]; ring
          obtain ⟨n, hn, first, second⟩ := ih proper C 2 (by simpa using hC)
            hnonunit hbase he hf hcoord (p - r) r old_first old_second
          exact ⟨n, hn, by
            simpa only [sub_add_cancel] using
              (P4994T6ChamberAdditions n (p - r) r first second).1, second⟩

end ApollonianSuperharmonic

end
