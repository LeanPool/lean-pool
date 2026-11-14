/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandVectorParentSums

public import LeanPool.ApollonianSuperharmonic.TilingLatticeIndex

-- [TABLET NODE: TilingLatticeBasis]

/-!
# TilingLatticeBasis

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TilingBasisProof

private abbrev relation := ApollonianSuperharmonic.BandVectorIncomingSum

private theorem flipA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (BandVectors.1 (q 0) (q 1) =
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 0)) ) := by
  classical
  intro q hq
  simpa using (VectorRecursionLaws q hq.1).2.2.2.2 hq ⟨0, by decide⟩ |>.1

private theorem flipB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (BandVectors.1 (q 0) (q 2) =
            (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 2) (q 0)) ) := by
  classical
  intro q hq
  simpa using (VectorRecursionLaws q hq.1).2.2.2.2 hq ⟨1, by decide⟩ |>.1

private theorem nonnegative :
    (by
      classical
      exact
        ∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 ) := by
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
      dsimp at classification
      rcases classification with special | proper
      · fin_cases k
        · simp [special]
        · exact ih 0
        · exact ih 2
        · exact ih 3
      · rcases proper with ⟨_, larger0, larger2, larger3⟩
        fin_cases k
        · exact (ih 0).trans larger0.le
        · exact ih 0
        · exact ih 2
        · exact ih 3

private theorem impossible :
    (by
      classical
      exact
        (∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1) → (∀
            r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → (r 0).1 = 1 → (∀ j : Fin 3, (r
            j.succ).1 = 0) → False) ) := by
  classical
  intro nonnegative r hr
  induction hr with
  | base z =>
      intro h0 hz
      have h := hz ⟨0, by decide⟩
      simp at h0 h
  | rotate hr ih =>
      intro h0 hz
      apply ih h0
      intro j
      fin_cases j
      · simpa using hz ⟨2, by decide⟩
      · simpa using hz ⟨0, by decide⟩
      · simpa using hz ⟨1, by decide⟩
  | @successor r hr ih =>
      intro h0 hz
      have hq0 : (r 0).1 = 0 := by simpa using hz ⟨0, by decide⟩
      have hq2 : (r 2).1 = 0 := by simpa using hz ⟨1, by decide⟩
      have hq3 : (r 3).1 = 0 := by simpa using hz ⟨2, by decide⟩
      have hq1 := nonnegative r hr 1
      have hnew := h0
      dsimp at hnew
      omega

private theorem hc :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((q (0 :
            Fin (4 : ℕ)) = C.1.1) → ((∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r → ∀
            k : Fin 4, 0 ≤ (r k).1) → ((∀ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r →
            (r 0).1 = 1 → (∀ j : Fin 3, (r j.succ).1 = 0) → False) → (C.1.1.1 ≠ 1)))) ) := by
  classical
  intro C q hq hC nonnegative impossible heq
  apply impossible q hq.1
  · simpa [hC] using heq
  intro j
  have hlt := hq.2 j
  have hn := nonnegative q hq.1 j.succ
  have he := heq
  rw [← hC] at he
  omega

private theorem generator_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((q (0 :
            Fin (4 : ℕ)) = C.1.1) → ((BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
            BandVectors.1 (q 3) (q 0) = 0) → (∀ (p : Fin (4 : ℕ) → CircleCoordinates), (∀ (q' :
            Fin (4 : ℕ) → CircleCoordinates), SemiProperQuadruple q' → q' (0 : Fin (4 : ℕ)) =
            C.1.1 → (∀ (j : Fin (3 : ℕ)), (q' j.succ).1 < C.1.1.1) → ∀ (D : CircleCoordinates),
            (∃ (j : Fin (3 : ℕ)), p j.succ = D) ↔ ∃ (j : Fin (3 : ℕ)), q' j.succ = D) → (
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        ∀ x : GaussianInt, (∃ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r ∧ r 0 = C.1.1
            ∧ (∀ j : Fin 3, (r j.succ).1 < C.1.1.1) ∧ ∃ j : Fin 3, x = BandVectors.1 (r j.succ)
            (r 0)) → x ∈ K)))) ) := by
  classical
  intro C q hq hC relation p huniq K x hx
  rcases hx with ⟨r, hr, hr0, hrt, j, hx⟩
  have hs : ∀ k : Fin 3, (r k.succ).1 < C.1.1.1 := hrt
  have child := (huniq r hr hr0 hs (r j.succ)).mpr ⟨j, rfl⟩
  rcases child with ⟨k, hk⟩
  have child' := (huniq q hq.1 hC (by simpa [hC] using hq.2) (p k.succ)).mp ⟨k, rfl⟩
  rcases child' with ⟨l, hl⟩
  fin_cases l
  · rw [hx, ← hk, ← hl, hr0, ← hC]
    exact AddSubgroup.subset_closure (by simp)
  · rw [hx, ← hk, ← hl, hr0, ← hC]
    exact AddSubgroup.subset_closure (by simp)
  · rw [hx, ← hk, ← hl, hr0, ← hC]
    simp only [Fin.reduceFinMk, Fin.reduceSucc, Fin.isValue] at hl ⊢
    have cneg : BandVectors.1 (q 3) (q 0) =
        -(BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_left_comm, add_comm] using relation
    rw [cneg]
    exact K.neg_mem (K.add_mem
      (AddSubgroup.subset_closure (by simp))
      (AddSubgroup.subset_closure (by simp)))

private theorem lattice_le :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (C.1.1.1 ≠ 1) → (
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        (∀ x : GaussianInt, (∃ r : Fin 4 → CircleCoordinates, SemiProperQuadruple r ∧ r 0 = C.1.1
            ∧ (∀ j : Fin 3, (r j.succ).1 < C.1.1.1) ∧ ∃ j : Fin 3, x = BandVectors.1 (r j.succ)
            (r 0)) → x ∈ K) → (TilingLattice C ≤ K)) ) := by
  classical
  intro C q hc K generator_mem
  unfold TilingLattice
  simp only [ite_eq_right hc]
  rw [AddSubgroup.closure_le]
  intro x hx
  exact generator_mem x hx

private theorem first_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((q (0 :
            Fin (4 : ℕ)) = C.1.1) → ((C.1.1.1 ≠ 1) → (BandVectors.1 (q 1) (q 0) ∈ TilingLattice
            C))) ) := by
  classical
  intro C q hq hC hc
  unfold TilingLattice
  simp only [ite_eq_right hc]
  exact AddSubgroup.subset_closure ⟨q, hq.1, hC, by simpa [hC] using hq.2,
    ⟨0, by simp⟩⟩

private theorem second_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → ((q (0 :
            Fin (4 : ℕ)) = C.1.1) → ((C.1.1.1 ≠ 1) → (BandVectors.1 (q 2) (q 0) ∈ TilingLattice
            C))) ) := by
  classical
  intro C q hq hC hc
  unfold TilingLattice
  simp only [ite_eq_right hc]
  exact AddSubgroup.subset_closure ⟨q, hq.1, hC, by simpa [hC] using hq.2,
    ⟨1, by simp⟩⟩

private theorem lattice_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates),
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        (TilingLattice C ≤ K) → ((BandVectors.1 (q 1) (q 0) ∈ TilingLattice C) → ((BandVectors.1
            (q 2) (q 0) ∈ TilingLattice C) → (TilingLattice C = K))) ) := by
  classical
  intro C q K lattice_le first_mem second_mem
  apply le_antisymm lattice_le
  change AddSubgroup.closure
    ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt) ≤
    TilingLattice C
  rw [AddSubgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact first_mem
  · exact second_mem

private theorem positive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (q (0 : Fin (4 : ℕ)) = C.1.1) → (0
            < (q 0).1) ) := by
  classical
  intro C q hC
  rw [hC]
  exact C.2

private theorem determinant_value :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let successorQuad : Fin 4 → CircleCoordinates :=
          ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
            2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2), q 0, q 2, q 3]
        (star (BandVectors.1 (successorQuad (1 : Fin (4 : ℕ))) (successorQuad (3 : Fin (4 : ℕ))))
            * BandVectors.1 (successorQuad (2 : Fin (4 : ℕ))) (successorQuad (1 : Fin (4 : ℕ))) +
            BandVectors.1 (successorQuad (1 : Fin (4 : ℕ))) (successorQuad (3 : Fin (4 : ℕ))) *
            star (BandVectors.1 (successorQuad (2 : Fin (4 : ℕ))) (successorQuad (1 : Fin (4 :
            ℕ)))) = (↑((-2 : ℤ) * (successorQuad (1 : Fin (4 : ℕ))).1) : GaussianInt) ∧
            ((BandVectors.1 (successorQuad (3 : Fin (4 : ℕ))) (successorQuad (1 : Fin (4 :
            ℕ)))).re * (BandVectors.1 (successorQuad (2 : Fin (4 : ℕ))) (successorQuad (1 : Fin
            (4 : ℕ)))).im - (BandVectors.1 (successorQuad (3 : Fin (4 : ℕ))) (successorQuad (1 :
            Fin (4 : ℕ)))).im * (BandVectors.1 (successorQuad (2 : Fin (4 : ℕ))) (successorQuad
            (1 : Fin (4 : ℕ)))).re).natAbs = (successorQuad (1 : Fin (4 : ℕ))).1.natAbs) →
            (Int.natAbs ((BandVectors.1 (q 3) (q 0)).re * (BandVectors.1 (q 2) (q 0)).im -
            (BandVectors.1 (q 3) (q 0)).im * (BandVectors.1 (q 2) (q 0)).re) = (q 0).1.natAbs) )
            := by
  classical
  intro q successorQuad determinant
  simpa [successorQuad] using determinant.2

private theorem determinant_nonzero :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)
            + BandVectors.1 (q 3) (q 0) = 0) → ((0 < (q 0).1) → ((Int.natAbs ((BandVectors.1 (q
            3) (q 0)).re * (BandVectors.1 (q 2) (q 0)).im - (BandVectors.1 (q 3) (q 0)).im *
            (BandVectors.1 (q 2) (q 0)).re) = (q 0).1.natAbs) → (
        let determinantNumber : Int :=
            (BandVectors.1 (q 1) (q 0)).re * (BandVectors.1 (q 2) (q 0)).im -
              (BandVectors.1 (q 1) (q 0)).im * (BandVectors.1 (q 2) (q 0)).re
        determinantNumber ≠ 0))) ) := by
  classical
  intro q relation positive determinant_value determinantNumber zero
  have opposite :
      (BandVectors.1 (q 3) (q 0)).re * (BandVectors.1 (q 2) (q 0)).im -
      (BandVectors.1 (q 3) (q 0)).im * (BandVectors.1 (q 2) (q 0)).re =
      -determinantNumber := by
    have cneg : BandVectors.1 (q 3) (q 0) =
        -(BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)) := by
      exact eq_neg_of_add_eq_zero_left
        (by simpa [add_assoc, add_left_comm, add_comm] using relation)
    rw [cneg]
    dsimp [determinantNumber]
    simp
    ring
  have zeroOpposite :
      (BandVectors.1 (q 3) (q 0)).re * (BandVectors.1 (q 2) (q 0)).im -
        (BandVectors.1 (q 3) (q 0)).im * (BandVectors.1 (q 2) (q 0)).re = 0 := by
    rw [opposite, zero]
    simp
  have vanish := determinant_value
  rw [zeroOpposite] at vanish
  have qzero : (q 0).1.natAbs = 0 := by simpa using vanish.symm
  have : (q 0).1 = 0 := Int.natAbs_eq_zero.mp qzero
  omega

private theorem coordinate_for :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        ∀ x : GaussianInt, x ∈ K → ∃ mn : Int × Int, (mn.1 : GaussianInt) * BandVectors.1 (q 1)
            (q 0) + (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = x ) := by
  classical
  intro q K x hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨(1, 0), by simp⟩
      · exact ⟨(0, 1), by simp⟩
  | zero => exact ⟨(0, 0), by simp⟩
  | add x y hx hy ix iy =>
      rcases ix with ⟨mx, hx⟩
      rcases iy with ⟨my, hy⟩
      refine ⟨(mx.1 + my.1, mx.2 + my.2), ?_⟩
      calc
        _ = (↑mx.1 * BandVectors.1 (q 1) (q 0) +
            ↑mx.2 * BandVectors.1 (q 2) (q 0)) +
            (↑my.1 * BandVectors.1 (q 1) (q 0) +
            ↑my.2 * BandVectors.1 (q 2) (q 0)) := by
              rw [Int.cast_add, Int.cast_add]
              ring
        _ = x + y := by rw [hx, hy]
  | neg x hx ix =>
      rcases ix with ⟨m, hm⟩
      refine ⟨(-m.1, -m.2), ?_⟩
      calc
        _ = -(↑m.1 * BandVectors.1 (q 1) (q 0) +
            ↑m.2 * BandVectors.1 (q 2) (q 0)) := by
              rw [Int.cast_neg, Int.cast_neg]
              simp
              ring
        _ = -x := by rw [hm]

private theorem coordinates :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates),
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        (TilingLattice C = K) → ((∀ x : GaussianInt, x ∈ K → ∃ mn : Int × Int, (mn.1 :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 : GaussianInt) * BandVectors.1 (q 2)
            (q 0) = x) → (∀ w : TilingLattice C, ∃ mn : Int × Int, (mn.1 : GaussianInt) *
            BandVectors.1 (q 1) (q 0) + (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (w :
            GaussianInt))) ) := by
  classical
  intro C q K lattice_eq coordinate_for w
  apply coordinate_for
  rw [← lattice_eq]
  exact w.property

private theorem unique_coordinates :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let determinantNumber : Int :=
            (BandVectors.1 (q 1) (q 0)).re * (BandVectors.1 (q 2) (q 0)).im -
              (BandVectors.1 (q 1) (q 0)).im * (BandVectors.1 (q 2) (q 0)).re
        (determinantNumber ≠ 0) → (∀ m n : Int × Int, (m.1 : GaussianInt) * BandVectors.1 (q 1)
            (q 0) + (m.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) = (n.1 : GaussianInt) *
            BandVectors.1 (q 1) (q 0) + (n.2 : GaussianInt) * BandVectors.1 (q 2) (q 0) → m = n)
            ) := by
  classical
  intro q determinantNumber determinant_nonzero m n h
  have realpart := congrArg (fun z : GaussianInt => z.re) h
  have imagpart := congrArg (fun z : GaussianInt => z.im) h
  simp only [Int.reduceNeg, Fin.isValue, Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero, Zsqrtd.im_add, Zsqrtd.im_mul]
      at realpart imagpart
  have realzero :
      (m.1 - n.1) * (BandVectors.1 (q 1) (q 0)).re +
        (m.2 - n.2) * (BandVectors.1 (q 2) (q 0)).re = 0 := by
    linarith
  have imagzero :
      (m.1 - n.1) * (BandVectors.1 (q 1) (q 0)).im +
        (m.2 - n.2) * (BandVectors.1 (q 2) (q 0)).im = 0 := by
    linarith
  have first_difference : determinantNumber * (m.1 - n.1) = 0 := by
    dsimp [determinantNumber]
    calc
      _ = (BandVectors.1 (q 2) (q 0)).im *
            ((m.1 - n.1) * (BandVectors.1 (q 1) (q 0)).re +
              (m.2 - n.2) * (BandVectors.1 (q 2) (q 0)).re) -
          (BandVectors.1 (q 2) (q 0)).re *
            ((m.1 - n.1) * (BandVectors.1 (q 1) (q 0)).im +
              (m.2 - n.2) * (BandVectors.1 (q 2) (q 0)).im) := by ring
      _ = 0 := by rw [realzero, imagzero]; ring
  have second_difference : determinantNumber * (m.2 - n.2) = 0 := by
    dsimp [determinantNumber]
    calc
      _ = (BandVectors.1 (q 1) (q 0)).re *
            ((m.1 - n.1) * (BandVectors.1 (q 1) (q 0)).im +
              (m.2 - n.2) * (BandVectors.1 (q 2) (q 0)).im) -
          (BandVectors.1 (q 1) (q 0)).im *
            ((m.1 - n.1) * (BandVectors.1 (q 1) (q 0)).re +
              (m.2 - n.2) * (BandVectors.1 (q 2) (q 0)).re) := by ring
      _ = 0 := by rw [realzero, imagzero]; ring
  have first_equal : m.1 = n.1 := by
    have := (mul_eq_zero.mp first_difference).resolve_left determinant_nonzero
    omega
  have second_equal : m.2 = n.2 := by
    have := (mul_eq_zero.mp second_difference).resolve_left determinant_nonzero
    omega
  exact Prod.ext first_equal second_equal

private theorem incoming_unique :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (∀ w : TilingLattice C, ∃ mn : Int
            × Int, (mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 : GaussianInt) *
            BandVectors.1 (q 2) (q 0) = (w : GaussianInt)) → ((∀ m n : Int × Int, (m.1 :
            GaussianInt) * BandVectors.1 (q 1) (q 0) + (m.2 : GaussianInt) * BandVectors.1 (q 2)
            (q 0) = (n.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (n.2 : GaussianInt) *
            BandVectors.1 (q 2) (q 0) → m = n) → (∀ w : TilingLattice C, ∃! mn : Int × Int, (mn.1
            : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 : GaussianInt) * BandVectors.1 (q
            2) (q 0) = (w : GaussianInt))) ) := by
  classical
  intro C q coordinates unique_coordinates w
  rcases coordinates w with ⟨mn, hmn⟩
  refine ⟨mn, hmn, ?_⟩
  intro other hother
  exact unique_coordinates other mn (hother.trans hmn.symm)

private theorem image_mem :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 0) (q 1) = (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q 1) (q 0)) → ((BandVectors.1 (q 0) (q 2) = (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q 2) (q 0)) → (
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        (BandVectors.1 (q 0) (q 1) ∈ AddSubgroup.closure ({BandVectors.1 (q 0) (q 1),
            BandVectors.1 (q 0) (q 2)} : Set GaussianInt)) → ((BandVectors.1 (q 0) (q 2) ∈
            AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
            GaussianInt)) → (∀ x : GaussianInt, x ∈ K → (⟨0, 1⟩ : GaussianInt) * x ∈
            AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
            GaussianInt))))) ) := by
  classical
  intro q flipA flipB K first_layout second_layout x hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · simpa [flipA] using first_layout
      · simpa [flipB] using second_layout
  | zero => simp
  | add x y hx hy ix iy =>
      rw [mul_add]
      exact (AddSubgroup.closure _).add_mem ix iy
  | neg x hx ix =>
      rw [mul_neg]
      exact (AddSubgroup.closure _).neg_mem ix

private theorem layout_coordinate_for :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ x : GaussianInt, x ∈ AddSubgroup.closure
            ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set GaussianInt) → ∃ mn :
            Int × Int, (mn.1 : GaussianInt) * BandVectors.1 (q 0) (q 1) + (mn.2 : GaussianInt) *
            BandVectors.1 (q 0) (q 2) = x ) := by
  classical
  intro q x hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨(1, 0), by simp⟩
      · exact ⟨(0, 1), by simp⟩
  | zero => exact ⟨(0, 0), by simp⟩
  | add x y hx hy ix iy =>
      rcases ix with ⟨mx, hx⟩
      rcases iy with ⟨my, hy⟩
      refine ⟨(mx.1 + my.1, mx.2 + my.2), ?_⟩
      calc
        _ = (↑mx.1 * BandVectors.1 (q 0) (q 1) + ↑mx.2 * BandVectors.1 (q 0) (q 2)) +
            (↑my.1 * BandVectors.1 (q 0) (q 1) + ↑my.2 * BandVectors.1 (q 0) (q 2)) := by
              rw [Int.cast_add, Int.cast_add]
              ring
        _ = x + y := by rw [hx, hy]
  | neg x hx ix =>
      rcases ix with ⟨m, hm⟩
      refine ⟨(-m.1, -m.2), ?_⟩
      calc
        _ = -(↑m.1 * BandVectors.1 (q 0) (q 1) + ↑m.2 * BandVectors.1 (q 0) (q 2)) := by
              rw [Int.cast_neg, Int.cast_neg]
              simp
              ring
        _ = -x := by rw [hm]

private theorem incoming :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 0) (q 1) = (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q 1) (q 0)) → ((BandVectors.1 (q 0) (q 2) = (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 (q 2) (q 0)) → (∀ (mn : ℤ × ℤ), ∀ (other : ℤ × ℤ), (-(⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * ((↑other.1 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ)))
            (q (1 : Fin (4 : ℕ))) + (↑other.2 : GaussianInt) * BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q (2 : Fin (4 : ℕ)))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * ((↑mn.1 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (1 : Fin (4 : ℕ))) + (↑mn.2 :
            GaussianInt) * BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (2 : Fin (4 : ℕ))))) →
            ((other.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (other.2 : GaussianInt) *
            BandVectors.1 (q 2) (q 0) = (mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2
            : GaussianInt) * BandVectors.1 (q 2) (q 0)))) ) := by
  classical
  intro q flipA flipB mn other transformed
  rw [mul_add, mul_add, flipA, flipB] at transformed
  have iiSquare : ({ re := 0, im := 1 } : GaussianInt) ^ 2 = -1 := by
    apply Zsqrtd.ext_iff.mpr
    simp [pow_two]
  have hunit : -({ re := 0, im := 1 } : GaussianInt) *
      ({ re := 0, im := 1 } : GaussianInt) = 1 := by
    rw [show -({ re := 0, im := 1 } : GaussianInt) *
      ({ re := 0, im := 1 } : GaussianInt) = -
        (({ re := 0, im := 1 } : GaussianInt) ^ 2) by ring, iiSquare]
    simp
  have scalar (n : Int) (z : GaussianInt) :
      -({ re := 0, im := 1 } : GaussianInt) *
          ((n : GaussianInt) * (({ re := 0, im := 1 } : GaussianInt) * z)) =
        (n : GaussianInt) * z := by
    calc
      _ = ((-({ re := 0, im := 1 } : GaussianInt)) *
          ({ re := 0, im := 1 } : GaussianInt)) * ((n : GaussianInt) * z) := by ring
      _ = (n : GaussianInt) * z := by rw [hunit]; simp
  rw [scalar, scalar, scalar, scalar] at transformed
  exact transformed

private theorem iiSquareAt530 :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        ii ^ 2 = -1 ) := by
  classical
  intro ii
  dsimp [ii]
  norm_num [pow_two, Zsqrtd.ext_iff]

private theorem hunitAt533 :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → (-ii * ii = 1) ) := by
  classical
  intro ii iiSquare
  calc
    -ii * ii = -(ii ^ 2) := by rw [pow_two]; ring
    _ = 1 := by rw [iiSquare]; simp

private theorem image_tiling :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 0) (q 1) = (⟨0,
            1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 0)) → ((BandVectors.1 (q 0) (q 2) = (⟨0,
            1⟩ : GaussianInt) * BandVectors.1 (q 2) (q 0)) → (
        let K : AddSubgroup GaussianInt := AddSubgroup.closure
          ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
        (TilingLattice C ≤ K) → ((TilingLattice C = K) → ((BandVectors.1 (q 0) (q 1) ∈
            AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
            GaussianInt)) → ((BandVectors.1 (q 0) (q 2) ∈ AddSubgroup.closure
            ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set GaussianInt)) → (
        let ii : GaussianInt := ⟨0, 1⟩
        ∀ y : GaussianInt, y ∈ TilingLattice C → ii * y ∈ AddSubgroup.closure
            ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set GaussianInt))))))) ) := by
  classical
  intro C q flipA flipB K lattice_le lattice_eq first_layout second_layout ii y hy
  have hk : y ∈ K := lattice_le hy
  induction hk using AddSubgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · simpa [ii, flipA] using first_layout
      · simpa [ii, flipB] using second_layout
  | zero => simp [ii]
  | add z t hz ht iz it =>
      rw [mul_add]
      exact (AddSubgroup.closure _).add_mem (iz (by rw [lattice_eq]; exact hz))
        (it (by rw [lattice_eq]; exact ht))
  | neg z hz iz =>
      rw [mul_neg]
      exact (AddSubgroup.closure _).neg_mem (iz (by rw [lattice_eq]; exact hz))

private theorem layout_preimage :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 0) (q 1) = (⟨0,
            1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 0)) → ((BandVectors.1 (q 0) (q 2) = (⟨0,
            1⟩ : GaussianInt) * BandVectors.1 (q 2) (q 0)) → ((BandVectors.1 (q 1) (q 0) ∈
            TilingLattice C) → ((BandVectors.1 (q 2) (q 0) ∈ TilingLattice C) → (
        let ii : GaussianInt := ⟨0, 1⟩
        (-ii * ii = 1) → (∀ y : GaussianInt, y ∈ AddSubgroup.closure ({BandVectors.1 (q 0) (q 1),
            BandVectors.1 (q 0) (q 2)} : Set GaussianInt) → (-ii) * y ∈ TilingLattice C))))) ) := by
  classical
  intro C q flipA flipB first_mem second_mem ii hunit y hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [flipA]
        rw [show -ii * (ii * BandVectors.1 (q 1) (q 0)) =
          BandVectors.1 (q 1) (q 0) by rw [← mul_assoc, hunit, one_mul]]
        exact first_mem
      · rw [flipB]
        rw [show -ii * (ii * BandVectors.1 (q 2) (q 0)) =
          BandVectors.1 (q 2) (q 0) by rw [← mul_assoc, hunit, one_mul]]
        exact second_mem
  | zero => simp [ii]
  | add z t hz ht iz it =>
      rw [mul_add]
      exact (TilingLattice C).add_mem iz it
  | neg z hz iz =>
      rw [mul_neg]
      exact (TilingLattice C).neg_mem iz

private theorem hcoset :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (R : Finset GaussianInt), ∀ (x :
            GaussianInt),
        let ii : GaussianInt := ⟨0, 1⟩
        (ii ^ 2 = -1) → ((∀ y : GaussianInt, y ∈ TilingLattice C → ii * y ∈ AddSubgroup.closure
            ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set GaussianInt)) → (∀ (r :
            GaussianInt), (r ∈ R ∧ -ii * x - r ∈ TilingLattice C) → (x - ii * r ∈
            AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
            GaussianInt)))) ) := by
  classical
  intro C q R x ii iiSquare image_tiling r hr
  have := image_tiling ((-ii) * x - r) hr.2
  convert this using 1; ring_nf; simp [iiSquare]

private theorem hpre' :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (x : GaussianInt),
        let ii : GaussianInt := ⟨0, 1⟩
        (-ii * ii = 1) → (∀ (t : GaussianInt), (-ii * (x - ii * t) ∈ TilingLattice C) → ((-ii) *
            x - t ∈ TilingLattice C)) ) := by
  classical
  intro C x ii hunit t hpre
  have identity : (-ii) * (x - ii * t) = (-ii) * x - t := by
    rw [mul_sub, ← mul_assoc, hunit, one_mul]
  rw [identity] at hpre
  exact hpre

end TilingBasisProof

theorem TilingLatticeBasis (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hC : q 0 = C.1.1) :
    let a := BandVectors.1 (q 1) (q 0)
    let b := BandVectors.1 (q 2) (q 0)
    let u := BandVectors.1 (q 0) (q 1)
    let v := BandVectors.1 (q 0) (q 2)
    let L := AddSubgroup.closure ({u, v} : Set GaussianInt)
    a ∈ TilingLattice C ∧ b ∈ TilingLattice C ∧
      (∀ w : TilingLattice C, ∃! mn : Int × Int,
        (mn.1 : GaussianInt) * a + (mn.2 : GaussianInt) * b =
          (w : GaussianInt)) ∧
      u ∈ L ∧ v ∈ L ∧
      (∀ z : GaussianInt, z ∈ L ↔
        ∃ w : GaussianInt, w ∈ TilingLattice C ∧
          z = (⟨0, 1⟩ : GaussianInt) * w) ∧
      (∀ w : L, ∃! mn : Int × Int,
        (mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v =
          (w : GaussianInt)) ∧
      ∃ R : Finset GaussianInt,
        LatticeFundamentalSet L R ∧ R.card = C.1.1.1.natAbs := by
-- BODY
  classical
  dsimp
  have relation := TilingBasisProof.relation q hq
  have flipA := TilingBasisProof.flipA q hq
  have flipB := TilingBasisProof.flipB q hq
  have nonnegative := TilingBasisProof.nonnegative
  have impossible := TilingBasisProof.impossible nonnegative
  have hc := TilingBasisProof.hc C q hq hC nonnegative impossible
  obtain ⟨p, hp, hp0, hsmall, huniq⟩ := Or.resolve_left (BandGenealogy C) hc
  let K : AddSubgroup GaussianInt := AddSubgroup.closure
    ({BandVectors.1 (q 1) (q 0), BandVectors.1 (q 2) (q 0)} : Set GaussianInt)
  have generator_mem := TilingBasisProof.generator_mem C q hq hC relation p huniq
  have lattice_le := TilingBasisProof.lattice_le C q hc generator_mem
  have first_mem := TilingBasisProof.first_mem C q hq hC hc
  have second_mem := TilingBasisProof.second_mem C q hq hC hc
  have lattice_eq : TilingLattice C = K := TilingBasisProof.lattice_eq C q lattice_le first_mem
      second_mem
  have positive : 0 < (q 0).1 := TilingBasisProof.positive C q hC
  let successorQuad : Fin 4 → CircleCoordinates :=
    ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
      2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2), q 0, q 2, q 3]
  have determinant := VectorDeterminant successorQuad
    (SemiProperQuadruple.successor hq.1) (by simpa [successorQuad] using positive)
  have determinant_value := TilingBasisProof.determinant_value q determinant
  have determinant_nonzero := TilingBasisProof.determinant_nonzero q relation positive
      determinant_value
  have coordinate_for := TilingBasisProof.coordinate_for q
  have coordinates := TilingBasisProof.coordinates C q lattice_eq coordinate_for
  have unique_coordinates := TilingBasisProof.unique_coordinates q determinant_nonzero
  have incoming_unique := TilingBasisProof.incoming_unique C q coordinates unique_coordinates
  have first_layout : BandVectors.1 (q 0) (q 1) ∈
      AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
          GaussianInt) :=
    AddSubgroup.subset_closure (by simp)
  have second_layout : BandVectors.1 (q 0) (q 2) ∈
      AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
          GaussianInt) :=
    AddSubgroup.subset_closure (by simp)
  obtain ⟨R, hR, hcard⟩ := TilingLatticeIndex C
  refine ⟨first_mem, second_mem, incoming_unique, first_layout, second_layout, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact ⟨BandVectors.1 (q 1) (q 0), first_mem, flipA⟩
          · exact ⟨BandVectors.1 (q 2) (q 0), second_mem, flipB⟩
      | zero => exact ⟨0, (TilingLattice C).zero_mem, by simp⟩
      | add x y hx hy ix iy =>
          rcases ix with ⟨wx, hwx, ex⟩
          rcases iy with ⟨wy, hwy, ey⟩
          refine ⟨wx + wy, (TilingLattice C).add_mem hwx hwy, ?_⟩
          rw [ex, ey]
          simp [mul_add]
      | neg x hx ix =>
          rcases ix with ⟨w, hw, ex⟩
          refine ⟨-w, (TilingLattice C).neg_mem hw, ?_⟩
          rw [ex]
          simp
    · rintro ⟨w, hw, rfl⟩
      have image_mem : ∀ x : GaussianInt, x ∈ K →
          (⟨0, 1⟩ : GaussianInt) * x ∈
            AddSubgroup.closure ({BandVectors.1 (q 0) (q 1), BandVectors.1 (q 0) (q 2)} : Set
                GaussianInt)  := TilingBasisProof.image_mem q flipA flipB first_layout second_layout
      apply image_mem (w : GaussianInt)
      rw [← lattice_eq]
      exact hw
  · intro w
    have layout_coordinate_for := TilingBasisProof.layout_coordinate_for q
    rcases layout_coordinate_for (w : GaussianInt) w.property with ⟨mn, hmn⟩
    refine ⟨mn, hmn, ?_⟩
    intro other hother
    have transformed := congrArg (fun z : GaussianInt =>
      (-({ re := 0, im := 1 } : GaussianInt)) * z) (hother.trans hmn.symm)
    have incoming := TilingBasisProof.incoming q flipA flipB mn other transformed
    exact unique_coordinates other mn incoming
  · refine ⟨Finset.image (fun x : GaussianInt => (⟨0, 1⟩ : GaussianInt) * x) R, ?_, ?_⟩
    · intro x
      let ii : GaussianInt := ⟨0, 1⟩
      have iiSquare := TilingBasisProof.iiSquareAt530
      have hunit : -ii * ii = 1 := TilingBasisProof.hunitAt533 iiSquare
      have image_tiling := TilingBasisProof.image_tiling C q flipA flipB lattice_le lattice_eq
          first_layout second_layout
      have layout_preimage := TilingBasisProof.layout_preimage C q flipA flipB first_mem
          second_mem hunit
      rcases hR ((-ii) * x) with ⟨r, hr, hdiff⟩
      have hrep : ii * r ∈ Finset.image (fun z : GaussianInt => ii * z) R :=
        Finset.mem_image.mpr ⟨r, hr.1, rfl⟩
      have hcoset := TilingBasisProof.hcoset C q R x iiSquare image_tiling r hr
      refine ⟨ii * r, ⟨hrep, hcoset⟩, ?_⟩
      intro s hs
      rcases Finset.mem_image.mp hs.1 with ⟨t, ht, rfl⟩
      have hpre := layout_preimage (x - ii * t) hs.2
      have hpre' := TilingBasisProof.hpre' C x hunit t hpre
      have equal_rep := (hR ((-ii) * x)).unique
        ⟨hr.1, hr.2⟩ ⟨ht, hpre'⟩
      rw [equal_rep]
    · rw [Finset.card_image_of_injective]
      · exact hcard
      · intro x y hxy
        have := congrArg (fun z : GaussianInt => (-({ re := 0, im := 1 } : GaussianInt)) * z) hxy
        apply_fun (fun z : GaussianInt => -({ re := 0, im := 1 } : GaussianInt) * z) at hxy
        simpa [Zsqrtd.ext_iff] using hxy

end ApollonianSuperharmonic

end
