/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification

-- [TABLET NODE: BandPrototileReindexedDecomposition]

/-!
# BandPrototileReindexedDecomposition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPrototileReindexedDecomposition (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (T : ProtoTile)
    (hT : BandPrototile (q 0) T) :
    ∃ S : Fin 3 → Bool → ProtoTile,
      (∀ i s, BandSubtileOccurrence q T i s (S i s)) ∧
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) := by
-- BODY
  have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 :=
    fun r hr => (SemiProperForestClassification r hr).1
  have noUnit : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → (r 0).1 = 1 → ¬ ProperBandQuadruple r := by
    intro r hr
    induction hr with
    | base z =>
        intro h hp
        have bad := hp.2 0
        simp at h bad
    | rotate hr ih =>
        intro h hp
        apply ih h
        refine ⟨hr, ?_⟩
        intro j
        fin_cases j
        · simpa using hp.2 2
        · simpa using hp.2 0
        · simpa using hp.2 1
    | @successor r hr ih =>
        intro h hp
        have b := nonnegative r hr 1
        have h1 := hp.2 0
        have h2 := hp.2 1
        have h3 := hp.2 2
        dsimp at h h1 h2 h3
        omega
  let property : CircleCoordinates → ProtoTile → Prop := fun C U =>
    ∀ q, ProperBandQuadruple q → C = q 0 →
      ∃ S : Fin 3 → Bool → ProtoTile,
        (∀ i s, BandSubtileOccurrence q U i s (S i s)) ∧
        (∀ x, x ∈ U.cells ↔ ∃ i s, x ∈ (S i s).cells)
  refine (BandPrototile.rec (motive := fun C U _ => property C U)
    ?_ ?_ ?_ hT) q hq rfl
  · intro w x hw q hq hC
    have bad := hq.2 0
    have non := nonnegative q hq.1 1
    change (q (0 : Fin 3).succ).1 < (q 0).1 at bad
    change 0 ≤ (q (0 : Fin 3).succ).1 at non
    have zero : (q 0).1 = 0 := by
      simpa using (congrArg (fun p : CircleCoordinates => p.1) hC).symm
    rw [zero] at bad
    omega
  · intro z x anchor q hq hC
    have one : (q 0).1 = 1 := by
      have hp := congrArg (fun p : CircleCoordinates => p.1) hC
      simpa using hp.symm
    exact (noUnit q hq.1 one hq).elim
  · intro q' hq' child parent hS hcells hfoot hcentroid ih q hq hC
    obtain ⟨r, matchParents, unique⟩ :=
      BandPredecessorNoCollision q' q hq' hq hC
    let reindexed : Fin 3 → Bool → ProtoTile :=
      fun i s => child (i + r) s
    refine ⟨reindexed, ?_, ?_⟩
    · intro i s
      refine ⟨?_, ?_, ?_⟩
      · have hp := hS (i + r) s
        rw [← matchParents i] at hp
        simpa [reindexed] using hp
      · exact hfoot (i + r) s
      · have hd := hcentroid (i + r) s
        have hv :
            BandVectors.1 (q' ((i + r + 2).succ))
                (q' ((i + r + 1).succ)) =
              BandVectors.1 (q ((i + 2).succ))
                (q ((i + 1).succ)) := by
          rw [matchParents (i + 2), matchParents (i + 1)]
          fin_cases i <;> fin_cases r <;> rfl
        rw [hv] at hd
        simpa [reindexed] using hd
    · intro x
      constructor
      · intro hx
        rcases (hcells x).1 hx with ⟨j, s, hj⟩
        refine ⟨j - r, s, ?_⟩
        simpa [reindexed]
      · intro hx
        rcases hx with ⟨i, s, hi⟩
        apply (hcells x).2
        refine ⟨i + r, s, ?_⟩
        simpa [reindexed] using hi

end ApollonianSuperharmonic

end
