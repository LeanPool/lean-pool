/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3161T1BlockTreeReachability

-- [TABLET NODE: P3161T1AggregateInducedConnectivity]

/-!
# P3161T1AggregateInducedConnectivity

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3161T1AggregateInducedConnectivity
    (τ σ : Finset (Int × Int))
    (hτ : τ ∈ ({
      {(0, 0), (1, 0), (0, -1)},
      {(0, 0), (0, 1), (1, 1)},
      {(0, 0), (-1, -1), (-1, 0)}
    } : Finset (Finset (Int × Int))))
    (hσ : σ ⊆ τ)
    (a b : PeriodicSubtileIndex)
    (ha : (a.first, a.second) ∈ σ) (hb : (b.first, b.second) ∈ σ) :
    Relation.ReflTransGen
      (fun x y : PeriodicSubtileIndex ↦
        AllowedSubtileIncidence x y ∧ (x.first, x.second) ∈ σ ∧
          (y.first, y.second) ∈ σ) a b := by
-- BODY
  let r := fun x y : PeriodicSubtileIndex ↦
    AllowedSubtileIncidence x y ∧ (x.first, x.second) ∈ σ ∧
      (y.first, y.second) ∈ σ
  have rev {x y} (hxy : Relation.ReflTransGen r x y) :
      Relation.ReflTransGen r y x := by
    induction hxy with
    | refl => exact .refl
    | tail h e ih => exact (Relation.ReflTransGen.single
        ⟨e.1.symm, e.2.2, e.2.1⟩).trans ih
  have block (z : Int × Int) (hz : z ∈ σ) (c d : SixSubtileLabel) :
      Relation.ReflTransGen r ⟨c, z.1, z.2⟩ ⟨d, z.1, z.2⟩ :=
    P3161T1BlockTreeReachability (fun z ↦ z ∈ σ) z.1 z.2 hz c d
  have cross (z w : Int × Int) (hz : z ∈ σ) (hw : w ∈ σ)
      (c d : SixSubtileLabel)
      (e : AllowedSubtileIncidence ⟨c, z.1, z.2⟩ ⟨d, w.1, w.2⟩) :
      Relation.ReflTransGen r ⟨.A, z.1, z.2⟩ ⟨.A, w.1, w.2⟩ :=
    (block z hz .A c).trans ((Relation.ReflTransGen.single ⟨e, hz, hw⟩).trans
      (block w hw d .A))
  have bridge (z w : Int × Int) (hz : z ∈ σ) (hw : w ∈ σ) :
      Relation.ReflTransGen r ⟨.A, z.1, z.2⟩ ⟨.A, w.1, w.2⟩ := by
    have zτ := hσ hz
    have wτ := hσ hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl
    all_goals
      simp only [Finset.mem_insert, Finset.mem_singleton] at zτ wτ
      rcases zτ with rfl | rfl | rfl
      all_goals rcases wτ with rfl | rfl | rfl
    all_goals first
      | exact .refl
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.AE01 0 (-1))
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.AE01 0 (-1)))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.AC11 0 (-1))
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.AC11 0 (-1)))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.CEm10 1 0)
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.CEm10 1 0))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.AE01 0 0)
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.AE01 0 0))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.AC11 0 0)
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.AC11 0 0))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.CEm10 1 1)
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.CEm10 1 1))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.AE01 (-1) (-1))
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.AE01 (-1) (-1)))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.AC11 (-1) (-1))
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.AC11 (-1) (-1)))
      | exact cross _ _ hz hw _ _ (AllowedSubtileIncidence.CEm10 0 0)
      | exact rev (cross _ _ hw hz _ _ (AllowedSubtileIncidence.CEm10 0 0))
  cases a with | mk ca ma na =>
    cases b with | mk cb mb nb =>
      exact (block (ma, na) ha ca .A).trans
        ((bridge (ma, na) (mb, nb) ha hb).trans (block (mb, nb) hb .A cb))

end ApollonianSuperharmonic

end
