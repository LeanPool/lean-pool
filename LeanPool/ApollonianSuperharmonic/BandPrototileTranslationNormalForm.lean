/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.BandPredecessorNoCollision
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: BandPrototileTranslationNormalForm]

/-!
# BandPrototileTranslationNormalForm

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TranslationNormalFormProof

private theorem nonnegative :
    ∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 := by
  classical
  intro r hr
  induction hr with
  | base z => intro k; fin_cases k <;> simp
  | rotate hr ih =>
      intro k
      fin_cases k <;> simp_all
  | @successor r hr ih =>
      intro k
      have classification := BandSuccessorClassification r hr
      rcases classification with special | proper
      · fin_cases k <;> simp_all
      · rcases proper with ⟨_, h0, h2, h3⟩
        fin_cases k
        · exact (ih 0).trans h0.le
        · exact ih 0
        · exact ih 2
        · exact ih 3

private theorem noProperUnit :
    (∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1) → (∀ r :
        Fin 4 → CircleCoordinates, SemiProperQuadruple r → (r 0).1 = 1 → ¬ ProperBandQuadruple r)
        := by
  classical
  intro nonnegative r hr
  induction hr with
  | base z =>
      intro h hp
      have bad := hp.2 0
      simp at bad
  | @rotate r hr ih =>
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
      have a := nonnegative r hr 0
      have b := nonnegative r hr 1
      have c := nonnegative r hr 2
      have d := nonnegative r hr 3
      have h1 := hp.2 0
      have h2 := hp.2 1
      have h3 := hp.2 2
      dsimp at h h1 h2 h3
      omega

private theorem positiveChild :
    (∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1) → (∀ r :
        Fin 4 → CircleCoordinates, SemiProperQuadruple r → 0 < (r 0).1 → ∃ j : Fin 3, 0 < (r
        j.succ).1) := by
  classical
  intro nonnegative r hr
  induction hr with
  | base z =>
      intro h
      exact ⟨0, by simp⟩
  | @rotate r hr ih =>
      intro h
      rcases ih h with ⟨j, hj⟩
      fin_cases j
      · exact ⟨2, by simpa using hj⟩
      · exact ⟨0, by simpa using hj⟩
      · exact ⟨1, by simpa using hj⟩
  | @successor r hr ih =>
      intro h
      have a := nonnegative r hr 0
      have b := nonnegative r hr 1
      have c := nonnegative r hr 2
      have d := nonnegative r hr 3
      by_contra hn
      push Not at hn
      have e := hn 0
      have f := hn 1
      have g := hn 2
      dsimp at h e f g
      omega

private theorem positiveCells :
    (∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → 0 < (r 0).1 → ∃ j : Fin 3, 0 < (r
        j.succ).1) → (∀ (C : CircleCoordinates), ∀ (P : ProtoTile), 0 < C.1 → BandPrototile C P →
        P.cells.Nonempty) := by
  classical
  intro positiveChild C P hC hP
  induction hP with
  | line w x hw =>
      simp at hC
  | unit z x anchor =>
      simp
  | @decompose q hq S V hS hcells hfoot hcentroid ih =>
      rcases positiveChild q hq.1 (by simpa using hC) with ⟨j, hj⟩
      have hp := ih j false hj
      rcases hp with ⟨a, ha⟩
      exact ⟨a, (hcells a).mpr ⟨j, false, ha⟩⟩

private theorem vectorMatch :
    ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (q' : Fin
        (4 : ℕ) → CircleCoordinates), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (r : Fin (3 :
        ℕ)), (∀ (j : Fin (3 : ℕ)), q' j.succ = q (j + r).succ) → ((∀ (y : Fin (3 : ℕ)), (fun (r :
        Fin (3 : ℕ)) => ∀ (j : Fin (3 : ℕ)), q' j.succ = q (j + r).succ) y → y = r) → (∀ (k : Fin
        (3 : ℕ)), ((0 : ℤ) < (q k.succ).1) → (
    let i : Fin 3 := k - r
    (q' i.succ = q k.succ) → (∀ (u : GaussianInt), ((S k true).cells = (TileTranslation (S' i
        true) u).cells) → (((S k true).cells = ∅ → (S k true).anchor = (TileTranslation (S' i
        true) u).anchor) → (((S k true).cells.Nonempty) → (((TileTranslation (S' i true)
        u).cells.Nonempty) → ((TileCentroid (S k true) = TileCentroid (TileTranslation (S' i
        true) u)) → (BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ)) = BandVectors.1 (q ((k
        + 2).succ)) (q ((k + 1).succ))))))))))) := by
  classical
  intro q S q' S' r hrotation hunique k hk i hi u hcellsParent hemptyParent nonemptyParent
      translatedNonempty parentCentroid
  have idxA : (i + 2 + r : Fin 3) = k + 2 := by
    fin_cases k <;> fin_cases r <;> simp [i]
  have idxB : (i + 1 + r : Fin 3) = k + 1 := by
    fin_cases k <;> fin_cases r <;> simp [i]
  have ha := hrotation (i + 2)
  have hb := hrotation (i + 1)
  rw [idxA] at ha
  rw [idxB] at hb
  rw [ha, hb]

private theorem childCentroid :
    ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (V : ProtoTile), ∀ (S' : Fin (3 : ℕ) → Bool →
        ProtoTile), ∀ (W : ProtoTile), ∀ (r : Fin (3 : ℕ)), ∀ (k : Fin (3 : ℕ)),
    let i : Fin 3 := k - r
    ∀ (u : GaussianInt), (TileCentroid (S k true) = TileCentroid (TileTranslation (S' i true) u))
        → ((TileCentroid (S k true) - TileCentroid V = TileCentroid (S' i true) - TileCentroid W)
        → (TileCentroid V = TileCentroid (TileTranslation W u))) := by
  classical
  intro S V S' W r k i u parentCentroid differenceMatch
  rw [(TileTranslationFormulas W u).2.2.2.2.1]
  apply Prod.ext
  · have hp := congrArg Prod.fst parentCentroid
    have hd := congrArg Prod.fst differenceMatch
    rw [(TileTranslationFormulas (S' i true) u).2.2.2.2.1] at hp
    dsimp at hp hd ⊢
    linarith
  · have hp := congrArg Prod.snd parentCentroid
    have hd := congrArg Prod.snd differenceMatch
    rw [(TileTranslationFormulas (S' i true) u).2.2.2.2.1] at hp
    dsimp at hp hd ⊢
    linarith

end TranslationNormalFormProof

theorem BandPrototileTranslationNormalForm (C : CircleCoordinates)
    (T U : ProtoTile) (hT : BandPrototile C T) (hU : BandPrototile C U) :
    ∃ u : GaussianInt,
      T.cells = (TileTranslation U u).cells ∧
      (T.cells = ∅ → T.anchor = (TileTranslation U u).anchor) := by
-- BODY
  have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 := TranslationNormalFormProof.nonnegative
  have noProperUnit : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → (r 0).1 = 1 → ¬ ProperBandQuadruple r :=
          TranslationNormalFormProof.noProperUnit nonnegative
  have positiveChild : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → 0 < (r 0).1 →
      ∃ j : Fin 3, 0 < (r j.succ).1 := TranslationNormalFormProof.positiveChild nonnegative
  have positiveCells : ∀ (C : CircleCoordinates) (P : ProtoTile),
      0 < C.1 → BandPrototile C P → P.cells.Nonempty := TranslationNormalFormProof.positiveCells
          positiveChild
  refine BandPrototile.rec (motive := fun C T _ =>
    ∀ U, BandPrototile C U →
      ∃ u : GaussianInt, T.cells = (TileTranslation U u).cells ∧
        (T.cells = ∅ → T.anchor = (TileTranslation U u).anchor)) ?_ ?_ ?_ hT U hU
  · intro w x hw U hU
    refine BandPrototile.rec (motive := fun C U _ =>
      C = (0, w) → ∃ u : GaussianInt, ({cells := ∅, anchor := x} : ProtoTile).cells =
        (TileTranslation U u).cells ∧
        (({cells := ∅, anchor := x} : ProtoTile).cells = ∅ →
          ({cells := ∅, anchor := x} : ProtoTile).anchor = (TileTranslation U u).anchor))
      ?_ ?_ ?_ hU rfl
    · intro w' y hw' hC
      refine ⟨x - y, ?_, ?_⟩ <;> simp [TileTranslation, GaussianTranslation]
    · intro z' y anchor hC
      simp at hC
    · intro q' hq' S' V' hS' hcells' hfoot' hcentroid' ih' hC
      have hbad := hq'.2 0
      have hnon := nonnegative q' hq'.1 1
      have hnon' : 0 ≤ (q' 1).1 := by simpa using hnon
      rw [hC] at hbad
      have hbad' : (q' 1).1 < 0 := by simpa using hbad
      have : False := by omega
      exact this.elim
  · intro z x anchor U hU
    refine BandPrototile.rec (motive := fun C U _ =>
      C = (1, 1 + 2*z) → ∃ u : GaussianInt, ({cells := {x}, anchor := anchor} : ProtoTile).cells =
        (TileTranslation U u).cells ∧
        (({cells := {x}, anchor := anchor} : ProtoTile).cells = ∅ →
          ({cells := {x}, anchor := anchor} : ProtoTile).anchor = (TileTranslation U u).anchor))
      ?_ ?_ ?_ hU rfl
    · intro w' y hw' hC
      have hz := congrArg (fun p : CircleCoordinates => p.1) hC
      simp at hz
    · intro z' y anchor' hC
      refine ⟨x-y, ?_, ?_⟩ <;> simp [TileTranslation, GaussianTranslation]
    · intro q' hq' S' V' hS' hcells' hfoot' hcentroid' ih' hC
      exact (noProperUnit q' hq'.1
        (by simpa using congrArg (fun p : CircleCoordinates => p.1) hC) hq').elim
  · intro q hq S V hS hcells hfoot hcentroid ih U hU
    have qpos : 0 < (q 0).1 :=
      lt_of_le_of_lt (nonnegative q hq.1 1) (hq.2 0)
    refine BandPrototile.rec (motive := fun C U _ =>
      q 0 = C → ∃ u : GaussianInt, V.cells = (TileTranslation U u).cells ∧
        (V.cells = ∅ → V.anchor = (TileTranslation U u).anchor))
      ?_ ?_ ?_ hU rfl
    · intro w y hw hC
      have bad : (q 0).1 = 0 := by simpa using congrArg (fun p : CircleCoordinates => p.1) hC
      omega
    · intro z y anchor hC
      have hone : (q 0).1 = 1 := by
        simpa using congrArg (fun p : CircleCoordinates => p.1) hC
      exact (noProperUnit q hq.1 hone hq).elim
    · intro q' hq' S' W hS' hcells' hfoot' hcentroid' ih' hC
      have rotation := BandPredecessorNoCollision q q' hq hq' hC
      rcases rotation with ⟨r, hrotation, hunique⟩
      rcases positiveChild q hq.1 qpos with ⟨k, hk⟩
      let i : Fin 3 := k - r
      have hi : q' i.succ = q k.succ := by
        have hm := hrotation i
        convert hm using 1
        fin_cases k <;> fin_cases r <;> simp [i]
      have parent := ih k true (S' i true) (by simpa [hi] using hS' i true)
      rcases parent with ⟨u, hcellsParent, hemptyParent⟩
      have nonemptyParent : (S k true).cells.Nonempty :=
        positiveCells (q k.succ) (S k true) hk (hS k true)
      have translatedNonempty : (TileTranslation (S' i true) u).cells.Nonempty := by
        rw [← hcellsParent]
        exact nonemptyParent
      have parentCentroid :
          TileCentroid (S k true) =
            TileCentroid (TileTranslation (S' i true) u) := by
        rw [TileCentroid, TileCentroid]
        simp [hcellsParent, translatedNonempty]
      have vectorMatch :
          BandVectors.1 (q' ((i + 2).succ)) (q' ((i + 1).succ)) =
            BandVectors.1 (q ((k + 2).succ)) (q ((k + 1).succ)) :=
                TranslationNormalFormProof.vectorMatch q S q' S' r hrotation hunique k hk hi u
                hcellsParent hemptyParent nonemptyParent translatedNonempty parentCentroid
      have differenceMatch :
          TileCentroid (S k true) - TileCentroid V =
            TileCentroid (S' i true) - TileCentroid W := by
        rw [hcentroid k true, hcentroid' i true, vectorMatch]
      have childCentroid :
          TileCentroid V = TileCentroid (TileTranslation W u) :=
              TranslationNormalFormProof.childCentroid S V S' W r k u parentCentroid differenceMatch
      have translated : BandPrototile (q 0) (TileTranslation W u) :=
        BandPrototileTranslation (q 0) W u (by
          have hw : BandPrototile (q' 0) W :=
            @BandPrototile.decompose q' hq' S' W hS' hcells' hfoot' hcentroid'
          simpa [hC] using hw)
      have unique := BandPrototileCentroidUnique (q 0) V
        (TileTranslation W u) (BandPrototile.decompose hq hS hcells hfoot hcentroid)
        translated childCentroid
      exact ⟨u, unique.1, unique.2⟩

end ApollonianSuperharmonic

end
