/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: TileOdometerReindexedDecomposition]

/-!
# TileOdometerReindexedDecomposition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TileOdometerReindexedDecomposition
    (q : Fin 4 -> CircleCoordinates) (hq : ProperBandQuadruple q)
    (T : ProtoTile) (h : PartialOdometer)
    (hroot : 1 < (q 0).1) (hO : TileOdometer (q 0) T h) :
    exists S : Fin 3 -> Bool -> ProtoTile,
    exists hs : Fin 3 -> Bool -> PartialOdometer,
      BandPrototile (q 0) T /\
      (forall i s, TileOdometer (q i.succ) (S i s) (hs i s)) /\
      (forall x, x ∈ T.cells <-> exists i s, x ∈ (S i s).cells) /\
      (forall i s, FootprintVertices (S i s) ⊆ FootprintVertices T) /\
      (forall i s,
        TileCentroid (S i s) - TileCentroid T =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint
                  (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-((GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q ((i + 2).succ))
                      (q ((i + 1).succ)))).1)))) /\
      (forall x, x ∈ h.domain <-> exists i s, x ∈ (hs i s).domain) /\
      (forall i s x, x ∈ (hs i s).domain -> h.value x = (hs i s).value x) /\
      (forall i s j t, OdometerCompatibility (hs i s) (hs j t)) /\
      forall i s, (q i.succ).1 = 0 \/
        exists p p_i : Real × Real,
          PartialOdometerSlope h = some p /\
          PartialOdometerSlope (hs i s) = some p_i /\
          p_i.1 - p.1 =
            (if s = true then (1 : Real) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).re : Int) -
               ((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).im : Int)) /\
          p_i.2 - p.2 =
            (if s = true then (1 : Real) else -1) * (1 / 2) *
              (((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).im : Int) +
               ((BandVectors.2 (q ((i + 2).succ))
                (q ((i + 1).succ))).re : Int)) := by
-- BODY
  generalize hc : q 0 = c at hO hroot
  cases hO with
  | line w x hw h hdom =>
      have hbad : ¬ (1 < (0 : Real)) := by norm_num
      exact False.elim (hbad (by simp [] at hroot))
  | unit z x T h hT hdom htrans =>
      have hbad : ¬ (1 < (1 : Real)) := by norm_num
      exact False.elim (hbad (by simp [] at hroot))
  | @decompose q' hq' S' T' hs' h' hT' hsub' hcells' hfoot'
      hcentroid' hdom' hvalue' hcompat' hslope' =>
      obtain ⟨r, hr, hru⟩ := BandPredecessorNoCollision q q' hq hq' (by simp [hc])
      let slot : Fin 3 → Fin 3 := fun i => i - r
      have reindex (i k : Fin 3) :
          q' (slot i + k).succ = q (i + k).succ := by
        calc
          q' (slot i + k).succ = q ((slot i + k + r).succ) := hr _
          _ = q (i + k).succ := by
            congr 1
            fin_cases r <;> fin_cases i <;> fin_cases k <;> simp [slot]
      have child (i : Fin 3) : q' (slot i).succ = q i.succ := by
        calc
          q' (slot i).succ = q ((slot i + r).succ) := hr _
          _ = q i.succ := by
            congr 1
            fin_cases r <;> fin_cases i <;> simp [slot]
      refine ⟨(fun i s => S' (slot i) s),
        (fun i s => hs' (slot i) s), hT', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i s
        simpa only [child i] using hsub' (slot i) s
      · intro x
        constructor
        · intro hx
          obtain ⟨j, s, hj⟩ := (hcells' x).mp hx
          exact ⟨j + r, s, by simpa [slot] using hj⟩
        · rintro ⟨i, s, hi⟩
          exact (hcells' x).mpr ⟨slot i, s, hi⟩
      · intro i s
        exact hfoot' (slot i) s
      · intro i s
        simpa only [reindex i 2, reindex i 1] using hcentroid' (slot i) s
      · intro x
        constructor
        · intro hx
          obtain ⟨j, s, hj⟩ := (hdom' x).mp hx
          exact ⟨j + r, s, by simpa [slot] using hj⟩
        · rintro ⟨i, s, hi⟩
          exact (hdom' x).mpr ⟨slot i, s, hi⟩
      · intro i s x hx
        exact hvalue' (slot i) s x hx
      · intro i s j t
        exact hcompat' (slot i) s (slot j) t
      · intro i s
        rcases hslope' (slot i) s with hz | hz
        · left
          simpa only [child i] using hz
        · right
          simpa only [reindex i 2, reindex i 1] using hz

end ApollonianSuperharmonic

end
