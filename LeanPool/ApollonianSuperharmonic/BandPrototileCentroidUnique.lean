/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification

public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification

-- [TABLET NODE: BandPrototileCentroidUnique]

/-!
# BandPrototileCentroidUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandPrototileCentroidUnique (C : CircleCoordinates) (T U : ProtoTile)
    (hT : BandPrototile C T) (hU : BandPrototile C U)
    (hcent : TileCentroid T = TileCentroid U) :
    T.cells = U.cells ∧ (T.cells = ∅ → T.anchor = U.anchor) := by
-- BODY
  revert hcent
  revert hU
  revert U
  have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 :=
    fun r hr => (SemiProperForestClassification r hr).1
  have no_unit : ∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r →
      (r 0).1 = 1 → ¬ ProperBandQuadruple r := by
    intro r hr
    induction hr with
    | base z =>
        intro h hp
        have bad := hp.2 0
        simp at h bad
    | rotate hr ih =>
        intro h hp
        apply ih h
        exact ⟨hr, by
          intro j
          fin_cases j
          · simpa using hp.2 2
          · simpa using hp.2 0
          · simpa using hp.2 1⟩
    | @successor r hr ih =>
        intro h hp
        have child0 := hp.2 0
        have child1 := hp.2 1
        have child2 := hp.2 2
        have non1 := nonnegative r hr 1
        dsimp at h child0 child1 child2
        omega
  let property : CircleCoordinates → ProtoTile → Prop := fun D V =>
    ∀ W, BandPrototile D W → TileCentroid V = TileCentroid W →
      V.cells = W.cells ∧ (V.cells = ∅ → V.anchor = W.anchor)
  change property C T
  induction hT with
  | line w x hw =>
      intro U hU hcent
      generalize coordinate : ((0 : ℤ), w) = D at hU ⊢
      cases hU with
      | line w' y hw' =>
          simp only [TileCentroid, Finset.not_nonempty_empty, ↓reduceIte, Int.reduceNeg,
              GaussianInt.intCast_re, GaussianInt.intCast_im, Prod.mk.injEq, forall_const,
              true_and] at hcent ⊢
          apply GaussianInt.toComplex_injective
          apply Complex.ext
          · exact hcent.1
          · exact hcent.2
      | unit z' y => simp_all []
      | decompose hq' hS' hcells' hfoot' hcentroid' =>
          rename_i qcoord schild
          have below := hq'.2 0
          have above := nonnegative qcoord hq'.1 1
          change (qcoord (0 : Fin 3).succ).1 < (qcoord 0).1 at below
          change 0 ≤ (qcoord (0 : Fin 3).succ).1 at above
          have curv := congrArg Prod.fst coordinate
          dsimp at curv
          have qzero : (qcoord 0).1 = 0 := by simpa using curv.symm
          rw [qzero] at below
          exfalso
          omega
  | unit z x =>
      intro U hU hcent
      generalize coordinate : ((1 : ℤ), 1 + 2 * z) = D at hU ⊢
      cases hU with
      | line w' y hw' => simp_all []
      | unit z' y =>
          simp only [TileCentroid, Finset.singleton_nonempty, ↓reduceIte, Int.reduceNeg,
              Finset.sum_singleton, GaussianInt.intCast_re, Finset.card_singleton,
              Nat.cast_one, div_one, one_div, GaussianInt.intCast_im, Prod.mk.injEq,
              add_left_inj, Finset.singleton_inj, Finset.singleton_ne_empty,
              IsEmpty.forall_iff, and_true] at hcent ⊢
          have equal : x = y := by
            apply GaussianInt.toComplex_injective
            apply Complex.ext
            · exact hcent.1
            · exact hcent.2
          subst y
          simp
      | decompose hq' hS' hcells' hfoot' hcentroid' =>
          rename_i qcoord schild
          have below := hq'.2 0
          have above := nonnegative qcoord hq'.1 1
          change (qcoord (0 : Fin 3).succ).1 < (qcoord 0).1 at below
          change 0 ≤ (qcoord (0 : Fin 3).succ).1 at above
          have curv := congrArg Prod.fst coordinate
          dsimp at curv
          have qone : (qcoord 0).1 = 1 := by simpa using curv.symm
          rw [qone] at below
          exfalso
          exact (no_unit qcoord hq'.1 qone) hq'
  | @decompose q hq S T hS hcells hfoot hcentroid ih =>
      intro U hU hcent
      generalize coordinate : q 0 = D at hU ⊢
      cases hU with
      | line w x hw =>
          have below := hq.2 0
          have above := nonnegative q hq.1 1
          change (q (0 : Fin 3).succ).1 < (q 0).1 at below
          change 0 ≤ (q (0 : Fin 3).succ).1 at above
          have curv := congrArg Prod.fst coordinate
          dsimp at curv
          have qzero : (q 0).1 = 0 := by simpa using curv
          rw [qzero] at below
          omega
      | unit z x =>
          have below := hq.2 0
          have above := nonnegative q hq.1 1
          change (q (0 : Fin 3).succ).1 < (q 0).1 at below
          change 0 ≤ (q (0 : Fin 3).succ).1 at above
          have curv := congrArg Prod.fst coordinate
          dsimp at curv
          have qone : (q 0).1 = 1 := by simpa using curv
          rw [qone] at below
          exact False.elim ((no_unit q hq.1 qone) hq)
      | decompose hq' hS' hcells' hfoot' hcentroid' =>
          rename_i qcoord schild
          obtain ⟨r, matching, unique⟩ :=
            BandPredecessorNoCollision q qcoord hq hq' coordinate
          have centroid_match : ∀ i : Fin 3, ∀ s : Bool,
              TileCentroid (schild i s) = TileCentroid (S (i + r) s) := by
            intro i s
            have left := hcentroid' i s
            have right := hcentroid (i + r) s
            have vector_match :
                BandVectors.1 (qcoord ((i + 2).succ)) (qcoord ((i + 1).succ)) =
                  BandVectors.1 (q ((i + r + 2).succ)) (q ((i + r + 1).succ)) := by
              rw [matching (i + 2), matching (i + 1)]
              fin_cases r <;> fin_cases i <;> rfl
            rw [vector_match] at left
            have displacement := left.trans right.symm
            calc
              TileCentroid (schild i s) =
                  (TileCentroid (schild i s) - TileCentroid U) + TileCentroid U := by
                    ext <;> simp [sub_eq_add_neg, add_comm]
              _ = (TileCentroid (S (i + r) s) - TileCentroid T) + TileCentroid U := by
                    rw [displacement]
              _ = (TileCentroid (S (i + r) s) - TileCentroid T) + TileCentroid T := by
                    rw [hcent]
              _ = TileCentroid (S (i + r) s) := by
                    ext <;> simp [sub_eq_add_neg, add_comm]
          have child_equal : ∀ i : Fin 3, ∀ s : Bool,
              (schild i s).cells = (S (i + r) s).cells := by
            intro i s
            have hs := hS' i s
            rw [matching i] at hs
            exact (ih (i + r) s (schild i s) hs (centroid_match i s).symm).1.symm
          have index_preimage : ∀ k : Fin 3, ∃ i : Fin 3, i + r = k := by
            intro k
            fin_cases r <;> fin_cases k <;> first | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ |
                exact ⟨2, by decide⟩
          have cells_equal : T.cells = U.cells := by
            ext a
            constructor
            · intro ha
              rcases (hcells a).1 ha with ⟨k, s, ha⟩
              rcases index_preimage k with ⟨i, hi⟩
              apply (hcells' a).2
              refine ⟨i, s, ?_⟩
              rw [child_equal i s]
              simpa [hi] using ha
            · intro ha
              rcases (hcells' a).1 ha with ⟨i, s, ha⟩
              apply (hcells a).2
              refine ⟨i + r, s, ?_⟩
              rw [← child_equal i s]
              exact ha
          refine ⟨cells_equal, ?_⟩
          intro hempty
          have centered := hcent
          have uempty : U.cells = ∅ := by rw [← cells_equal]; exact hempty
          simp only [TileCentroid, hempty, Finset.not_nonempty_empty, ↓reduceIte,
              Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im, uempty,
              Prod.mk.injEq] at centered
          apply GaussianInt.toComplex_injective
          apply Complex.ext
          · exact centered.1
          · exact centered.2

end ApollonianSuperharmonic

end
