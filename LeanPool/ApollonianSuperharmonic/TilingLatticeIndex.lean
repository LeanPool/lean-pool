/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.VectorDeterminant
public import LeanPool.ApollonianSuperharmonic.TilingLattice
public import LeanPool.ApollonianSuperharmonic.LatticeFundamentalSet
public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

-- [TABLET NODE: TilingLatticeIndex]

/-!
# TilingLatticeIndex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace TilingIndexProof

private theorem relation :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (SemiProperQuadruple q) → (BandVectors.1 (q 1)
            (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0) ) := by
  classical
  intro q hq
  let r : Fin 4 → CircleCoordinates := ![q 0, q 2, q 3, q 1]
  have hr : SemiProperQuadruple r := by
    simpa [r] using SemiProperQuadruple.rotate hq
  let s : Fin 4 → CircleCoordinates := ![r 0, r 2, r 3, r 1]
  have hs : SemiProperQuadruple s := by
    simpa [s] using SemiProperQuadruple.rotate hr
  have first := VectorRecursionLaws q hq
  have second := VectorRecursionLaws r hr
  have third := VectorRecursionLaws s hs
  have e0 := first.2.2.1
  have e1 := second.2.2.1
  have e2 := third.2.2.1
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Int.reduceNeg,
      Matrix.cons_val, r, s] at e1 e2
  rw [e0, e1, e2]
  calc
    _ = (1 - (⟨0, 1⟩ : GaussianInt)) *
        (BandVectors.1 (q 3) (q 2) + BandVectors.1 (q 1) (q 3) +
          BandVectors.1 (q 2) (q 1)) := by ring
    _ = 0 := by rw [first.1]; simp

private theorem first_mem :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        (BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) = 0) →
            (BandVectors.1 (q 1) (q 0) ∈ K) ) := by
  classical
  intro q a b K relation
  have hsum : BandVectors.1 (q 1) (q 0) = -(b + a) := by
    dsimp [a, b]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using relation)
  rw [hsum]
  exact K.neg_mem (K.add_mem
    (AddSubgroup.subset_closure (by simp []))
    (AddSubgroup.subset_closure (by simp [])))

private theorem generator_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q (0 : Fin (4 : ℕ)) =
            C.1.1) → ((∀ (q' : Fin (4 : ℕ) → CircleCoordinates), SemiProperQuadruple q' → q' (0 :
            Fin (4 : ℕ)) = C.1.1 → (∀ (j : Fin (3 : ℕ)), (q' j.succ).1 < C.1.1.1) → ∀ (D :
            CircleCoordinates), (∃ (j : Fin (3 : ℕ)), q j.succ = D) ↔ ∃ (j : Fin (3 : ℕ)), q'
            j.succ = D) → (
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        (BandVectors.1 (q 1) (q 0) ∈ K) → (∀ u : GaussianInt, (∃ q' : Fin 4 → CircleCoordinates,
            SemiProperQuadruple q' ∧ q' 0 = C.1.1 ∧ (∀ j : Fin 3, (q' j.succ).1 < C.1.1.1) ∧ ∃ j
            : Fin 3, u = BandVectors.1 (q' j.succ) (q' 0)) → u ∈ K))) ) := by
  classical
  intro C q hC huniq a b K first_mem u hu
  rcases hu with ⟨q', hq', hC', hless', j, rfl⟩
  obtain ⟨k, hk⟩ := (huniq q' hq' hC' hless' (q' j.succ)).2 ⟨j, rfl⟩
  rw [hC', ← hC, ← hk]
  fin_cases k
  · exact first_mem
  · exact AddSubgroup.subset_closure (by simp [b])
  · exact AddSubgroup.subset_closure (by simp [a])

private theorem lattice_le :
    (by
      classical
      exact
        ∀ (C : BandCircle), (¬C.1.1.1 = (1 : ℤ)) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        (∀ u : GaussianInt, (∃ q' : Fin 4 → CircleCoordinates, SemiProperQuadruple q' ∧ q' 0 =
            C.1.1 ∧ (∀ j : Fin 3, (q' j.succ).1 < C.1.1.1) ∧ ∃ j : Fin 3, u = BandVectors.1 (q'
            j.succ) (q' 0)) → u ∈ K) → (TilingLattice C ≤ K)) ) := by
  classical
  intro C hunit q a b K generator_mem
  unfold TilingLattice
  simp only [hunit, ↓reduceIte]
  rw [AddSubgroup.closure_le]
  exact generator_mem

private theorem a_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), (¬C.1.1.1 = (1 : ℤ)) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (SemiProperQuadruple q) → ((q (0 : Fin (4 : ℕ)) = C.1.1) → ((∀ (j : Fin (3 : ℕ)), (q
            j.succ).1 < C.1.1.1) → (
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        a ∈ TilingLattice C)))) ) := by
  classical
  intro C hunit q hq hC hless a
  unfold TilingLattice
  simp only [hunit, ↓reduceIte]
  exact AddSubgroup.subset_closure
    ⟨q, hq, hC, hless, ⟨2, by simp [a]⟩⟩

private theorem b_mem :
    (by
      classical
      exact
        ∀ (C : BandCircle), (¬C.1.1.1 = (1 : ℤ)) → (∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (SemiProperQuadruple q) → ((q (0 : Fin (4 : ℕ)) = C.1.1) → ((∀ (j : Fin (3 : ℕ)), (q
            j.succ).1 < C.1.1.1) → (
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        b ∈ TilingLattice C)))) ) := by
  classical
  intro C hunit q hq hC hless b
  unfold TilingLattice
  simp only [hunit, ↓reduceIte]
  exact AddSubgroup.subset_closure
    ⟨q, hq, hC, hless, ⟨1, by simp [b]⟩⟩

private theorem lattice_eq :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        (TilingLattice C ≤ K) → ((a ∈ TilingLattice C) → ((b ∈ TilingLattice C) → (TilingLattice
            C = K))) ) := by
  classical
  intro C q a b K lattice_le a_mem b_mem
  apply le_antisymm lattice_le
  dsimp [K]
  rw [AddSubgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact a_mem
  · exact b_mem

private theorem successor_positive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q (0 : Fin (4 : ℕ)) =
            C.1.1) → (
        let successor : Fin 4 → CircleCoordinates :=
          ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
              2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
            q 0, q 2, q 3]
        (successor 1 = q 0) → (0 < (successor 1).1)) ) := by
  classical
  intro C q hC successor successor_parent
  rw [successor_parent, hC]
  exact C.2

private theorem determinant_value :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (q (0 : Fin (4 : ℕ)) =
            C.1.1) → (
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let successor : Fin 4 → CircleCoordinates :=
          ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
              2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
            q 0, q 2, q 3]
        (SemiProperQuadruple successor) → ((0 < (successor 1).1) → (Int.natAbs (a.re * b.im -
            a.im * b.re) = C.1.1.1.natAbs))) ) := by
  classical
  intro C q hC a b successor successor_semi successor_positive
  have determinant :=
    (VectorDeterminant successor successor_semi successor_positive).2
  simpa [successor, a, b, hC] using determinant

private theorem determinant_positive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        (Int.natAbs (a.re * b.im - a.im * b.re) = C.1.1.1.natAbs) → (0 < Int.natAbs (a.re * b.im
            - a.im * b.re)) ) := by
  classical
  intro C q a b determinant_value
  rw [determinant_value, Int.natAbs_pos]
  exact C.2.ne'

private theorem f_injective :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        (0 < Int.natAbs (a.re * b.im - a.im * b.re)) → (
        let f : (Fin 2 → ℤ) →ₗ[ℤ] K :=
          { toFun := fun x => ⟨x 0 • a + x 1 • b,
              K.add_mem (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 0))
                (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 1))⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              simp [zsmul_eq_mul, Int.cast_add]
              ring
            map_smul' := by
              intro n x
              apply Subtype.ext
              simp [zsmul_eq_mul, Int.cast_mul]
              ring }
        Function.Injective f)) := by
  classical
  intro q a b K determinant_positive f x y hxy
  have hre := congrArg (fun z : GaussianInt => z.re) (congrArg Subtype.val hxy)
  have him := congrArg (fun z : GaussianInt => z.im) (congrArg Subtype.val hxy)
  simp only [Int.reduceNeg, Fin.isValue, zsmul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_mul,
      add_zero, Zsqrtd.im_add, Zsqrtd.im_mul, f] at hre him
  have h0 : (a.re * b.im - a.im * b.re) * (x 0 - y 0) = 0 := by
    calc
      _ = b.im * ((x 0 * a.re + x 1 * b.re) - (y 0 * a.re + y 1 * b.re)) -
          b.re * ((x 0 * a.im + x 1 * b.im) - (y 0 * a.im + y 1 * b.im)) := by ring
      _ = 0 := by rw [hre, him]; ring
  have h1 : (a.re * b.im - a.im * b.re) * (x 1 - y 1) = 0 := by
    calc
      _ = a.re * ((x 0 * a.im + x 1 * b.im) - (y 0 * a.im + y 1 * b.im)) -
          a.im * ((x 0 * a.re + x 1 * b.re) - (y 0 * a.re + y 1 * b.re)) := by ring
      _ = 0 := by rw [hre, him]; ring
  have determinant_ne : a.re * b.im - a.im * b.re ≠ 0 := by
    intro h
    simp [h] at determinant_positive
  funext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left determinant_ne)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left determinant_ne)

private theorem f_surjective :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        let f : (Fin 2 → ℤ) →ₗ[ℤ] K :=
          { toFun := fun x => ⟨x 0 • a + x 1 • b,
              K.add_mem (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 0))
                (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 1))⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              simp [zsmul_eq_mul, Int.cast_add]
              ring
            map_smul' := by
              intro n x
              apply Subtype.ext
              simp [zsmul_eq_mul, Int.cast_mul]
              ring }
        Function.Surjective f ) := by
  classical
  intro q a b K f y
  suffices ∃ x, (f x : GaussianInt) = y by
    rcases this with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let z : GaussianInt := y
  change ∃ x, (f x : GaussianInt) = z
  have hz : z ∈ K := y.property
  change z ∈ AddSubgroup.closure ({a, b} : Set GaussianInt) at hz
  refine AddSubgroup.closure_induction (p := fun z _ => ∃ x, (f x : GaussianInt) = z)
    ?_ ?_ ?_ ?_ hz
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨![1, 0], by simp [f]⟩
    · exact ⟨![0, 1], by simp [f]⟩
  · exact ⟨0, by simp [f]⟩
  · intro x y _ _ ix iy
    rcases ix with ⟨u, hu⟩
    rcases iy with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    calc
      (f (u + v) : GaussianInt) = (f u : GaussianInt) + (f v : GaussianInt) :=
        congrArg Subtype.val (f.map_add u v)
      _ = x + y := by rw [hu, hv]
  · intro x _ ix
    rcases ix with ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    calc
      (f (-u) : GaussianInt) = -(f u : GaussianInt) :=
        congrArg Subtype.val (f.map_neg u)
      _ = -x := by rw [hu]

private theorem index_value :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        let f : (Fin 2 → ℤ) →ₗ[ℤ] K :=
          { toFun := fun x => ⟨x 0 • a + x 1 • b,
              K.add_mem (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 0))
                (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 1))⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              simp [zsmul_eq_mul, Int.cast_add]
              ring
            map_smul' := by
              intro n x
              apply Subtype.ext
              simp [zsmul_eq_mul, Int.cast_mul]
              ring }
        (Function.Injective f) → ((Function.Surjective f) → (K.index = Int.natAbs (a.re * b.im -
            a.im * b.re)))) := by
  classical
  intro q a b K f f_injective f_surjective
  let coordinates : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    { toFun := fun z => ![z.re, z.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := by intro z; ext <;> simp
      right_inv := by intro x; funext i; fin_cases i <;> simp
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro n x; funext i; fin_cases i <;> simp }
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] K :=
    LinearEquiv.ofBijective f ⟨f_injective, f_surjective⟩
  let basisK : Module.Basis (Fin 2) ℤ K := (Pi.basisFun ℤ (Fin 2)).map e
  let basisG : Module.Basis (Fin 2) ℤ GaussianInt :=
    Module.Basis.ofEquivFun coordinates
  rw [AddSubgroup.index_eq_natAbs_det basisG K basisK]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, basisG, basisK, e, f, coordinates]
  ring

private theorem quotient_positive :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        (Nat.card (GaussianInt ⧸ K) = C.1.1.1.natAbs) → (0 < Nat.card (GaussianInt ⧸ K)) ) := by
  classical
  intro C q a b K quotient_card
  rw [quotient_card, Int.natAbs_pos]
  exact C.2.ne'

private theorem hzAt323 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
        let a : GaussianInt := BandVectors.1 (q 3) (q 0)
        let b : GaussianInt := BandVectors.1 (q 2) (q 0)
        let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
        ∀ [this : Fintype (GaussianInt ⧸ K)],
        let quotientMap : GaussianInt → GaussianInt ⧸ K := QuotientAddGroup.mk' K
        ∀ (quotient_surjective : Function.Surjective quotientMap),
        let representative : GaussianInt ⧸ K → GaussianInt :=
          Function.surjInv quotient_surjective
        ∀ (representative_injective : Function.Injective representative),
        let representativeEmbedding : (GaussianInt ⧸ K) ↪ GaussianInt :=
          ⟨representative, representative_injective⟩
        let R : Finset GaussianInt := Finset.univ.map representativeEmbedding
        ∀ (x : GaussianInt), ∀ (z : GaussianInt ⧸ K), ((representativeEmbedding : GaussianInt ⧸ K
            → GaussianInt) z ∈ R ∧ x - (representativeEmbedding : GaussianInt ⧸ K → GaussianInt)
            z ∈ K) → (quotientMap x = quotientMap (representative z)) ) := by
  classical
  intro q a b K this quotientMap quotient_surjective representative representative_injective
      representativeEmbedding R x z hs
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact hs.2

end TilingIndexProof

theorem TilingLatticeIndex (C : BandCircle) :
    ∃ R : Finset GaussianInt,
      LatticeFundamentalSet (TilingLattice C) R ∧ R.card = C.1.1.1.natAbs := by
-- BODY
  classical
  by_cases hunit : C.1.1.1 = 1
  · refine ⟨{0}, ?_, by simp [hunit]⟩
    simp [LatticeFundamentalSet, TilingLattice, hunit]
  rcases BandGenealogy C with unit | ⟨q, hq, hC, hless, huniq⟩
  · exact (hunit unit).elim
  let a : GaussianInt := BandVectors.1 (q 3) (q 0)
  let b : GaussianInt := BandVectors.1 (q 2) (q 0)
  let K : AddSubgroup GaussianInt := AddSubgroup.closure ({a, b} : Set GaussianInt)
  have relation := TilingIndexProof.relation q hq
  have first_mem := TilingIndexProof.first_mem q relation
  have generator_mem := TilingIndexProof.generator_mem C q hC huniq first_mem
  have lattice_le := TilingIndexProof.lattice_le C hunit q generator_mem
  have a_mem := TilingIndexProof.a_mem C hunit q hq hC hless
  have b_mem := TilingIndexProof.b_mem C hunit q hq hC hless
  have lattice_eq : TilingLattice C = K := TilingIndexProof.lattice_eq C q lattice_le a_mem b_mem
  let successor : Fin 4 → CircleCoordinates :=
    ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
        2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
      q 0, q 2, q 3]
  have successor_semi : SemiProperQuadruple successor := by
    simpa [successor] using SemiProperQuadruple.successor hq
  have successor_parent : successor 1 = q 0 := by simp [successor]
  have successor_positive := TilingIndexProof.successor_positive C q hC successor_parent
  have determinant_value : Int.natAbs (a.re * b.im - a.im * b.re) =
      C.1.1.1.natAbs := TilingIndexProof.determinant_value C q hC successor_semi successor_positive
  have determinant_positive := TilingIndexProof.determinant_positive C q determinant_value
  let f : (Fin 2 → ℤ) →ₗ[ℤ] K :=
    { toFun := fun x => ⟨x 0 • a + x 1 • b,
        K.add_mem (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 0))
          (K.zsmul_mem (AddSubgroup.subset_closure (by simp [])) (x 1))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp [zsmul_eq_mul, Int.cast_add]
        ring
      map_smul' := by
        intro n x
        apply Subtype.ext
        simp [zsmul_eq_mul, Int.cast_mul]
        ring }
  have f_injective := TilingIndexProof.f_injective q determinant_positive
  have f_surjective := TilingIndexProof.f_surjective q
  let coordinates : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    { toFun := fun z => ![z.re, z.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := by intro z; ext <;> simp
      right_inv := by intro x; funext i; fin_cases i <;> simp
      map_add' := by intro x y; funext i; fin_cases i <;> simp
      map_smul' := by intro n x; funext i; fin_cases i <;> simp }
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] K :=
    LinearEquiv.ofBijective f ⟨f_injective, f_surjective⟩
  let basisK : Module.Basis (Fin 2) ℤ K := (Pi.basisFun ℤ (Fin 2)).map e
  let basisG : Module.Basis (Fin 2) ℤ GaussianInt :=
    Module.Basis.ofEquivFun coordinates
  have index_value : K.index = Int.natAbs (a.re * b.im - a.im * b.re) :=
      TilingIndexProof.index_value q f_injective f_surjective
  have quotient_card : Nat.card (GaussianInt ⧸ K) = C.1.1.1.natAbs := by
    rw [← K.index_eq_card, index_value, determinant_value]
  have quotient_positive := TilingIndexProof.quotient_positive C q quotient_card
  have : Finite (GaussianInt ⧸ K) := (Nat.card_pos_iff.mp quotient_positive).2
  let : Fintype (GaussianInt ⧸ K) := Fintype.ofFinite _
  let quotientMap : GaussianInt → GaussianInt ⧸ K := QuotientAddGroup.mk' K
  have quotient_surjective : Function.Surjective quotientMap :=
    QuotientAddGroup.mk'_surjective K
  let representative : GaussianInt ⧸ K → GaussianInt :=
    Function.surjInv quotient_surjective
  have representative_spec : ∀ z, quotientMap (representative z) = z :=
    Function.surjInv_eq quotient_surjective
  have representative_injective : Function.Injective representative :=
    Function.injective_surjInv quotient_surjective
  let representativeEmbedding : (GaussianInt ⧸ K) ↪ GaussianInt :=
    ⟨representative, representative_injective⟩
  let R : Finset GaussianInt := Finset.univ.map representativeEmbedding
  refine ⟨R, ?_, ?_⟩
  · rw [lattice_eq]
    intro x
    let r := representative (quotientMap x)
    have hr : r ∈ R := by
      exact Finset.mem_map.mpr ⟨quotientMap x, Finset.mem_univ _, rfl⟩
    refine ⟨r, ⟨hr, ?_⟩, ?_⟩
    · apply QuotientAddGroup.eq_iff_sub_mem.mp
      exact (representative_spec (quotientMap x)).symm
    · intro s hs
      obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hs.1
      have hz : quotientMap x = quotientMap (representative z) := TilingIndexProof.hzAt323 q
          (this := this) quotient_surjective representative_injective x z hs
      have hz' : quotientMap x = z := hz.trans (representative_spec z)
      change representative z = representative (quotientMap x)
      rw [hz']
  · calc
      R.card = Fintype.card (GaussianInt ⧸ K) := by simp [R]
      _ = Nat.card (GaussianInt ⧸ K) := Nat.card_eq_fintype_card.symm
      _ = C.1.1.1.natAbs := quotient_card

end ApollonianSuperharmonic

end
