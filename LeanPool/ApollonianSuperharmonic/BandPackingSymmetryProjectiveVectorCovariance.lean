/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryProperCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryScopedPhase
public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing

-- [TABLET NODE: BandPackingSymmetryProjectiveVectorCovariance]

/-!
# BandPackingSymmetryProjectiveVectorCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ProjectiveCovarianceProof

private theorem linj :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        let L := BandPackingSymmetryVectorAction
        (ii ≠ 0) → ((∀ (z : GaussianInt), GaussianQuarterTurn z = ii * z) → ((∀ (z :
            GaussianInt), GaussianReflection z = star z) → (∀ (h : BandPackingSymmetry),
            Function.Injective (L h))))
    ) := by
  classical
  intro ii L ii_ne quarter reflection h
  induction h with
  | identity => exact fun _ _ h => h
  | negate =>
      intro x y hxy
      change GaussianQuarterTurn x = GaussianQuarterTurn y at hxy
      rw [quarter, quarter] at hxy
      exact mul_left_cancel₀ ii_ne hxy
  | conjugate =>
      intro x y hxy
      change -GaussianReflection x = -GaussianReflection y at hxy
      simpa [reflection] using congrArg (fun z : GaussianInt => -star z) hxy
  | shift w => exact fun _ _ h => h
  | comp h k ih ik => exact ih.comp ik

private theorem lquarter :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        let L := BandPackingSymmetryVectorAction
        let O := BandPackingSymmetryReversesOrientation
        (∀ (z : GaussianInt), GaussianQuarterTurn z = ii * z) → ((∀ (h : BandPackingSymmetry), ∀
            (x : GaussianInt), L h (-x) = -L h x) → (∀ (h : BandPackingSymmetry), ∀ (x :
            GaussianInt), L h (ii * x) = if O h = true then -ii * L h x else ii * L h x))
    ) := by
  classical
  intro ii L O quarter lneg h x
  induction h generalizing x with
  | identity => rfl
  | negate =>
      simp [L, O, BandPackingSymmetryVectorAction,
        BandPackingSymmetryReversesOrientation, quarter]
  | conjugate =>
      ext <;> simp [L, O, BandPackingSymmetryVectorAction,
        BandPackingSymmetryReversesOrientation, GaussianReflection, ii]
  | shift w => rfl
  | comp h k ih ik =>
      change L h (L k (ii * x)) =
        if xor (O h) (O k) then -ii * L h (L k x) else ii * L h (L k x)
      rw [ik]
      cases hh : O h <;> cases hk : O k <;>
        simp [hh, neg_mul, lneg, ih]

private theorem squareMap :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        let L := BandPackingSymmetryVectorAction
        let A := BandPackingSymmetryCircleAction
        (ii ^ 2 = -1) → ((∀ (z : GaussianInt), GaussianQuarterTurn z = ii * z) → ((∀ (z :
            GaussianInt), GaussianReflection z = star z) → (∀ (h : BandPackingSymmetry), ∀ (C :
            CircleCoordinates), ∀ (D : CircleCoordinates), ∀ (x : GaussianInt), x ^ (2 : ℕ) =
            (↑D.1 : GaussianInt) * C.2 - (↑C.1 : GaussianInt) * D.2 → L h x ^ (2 : ℕ) = (↑(A h
            D).1 : GaussianInt) * (A h C).2 - (↑(A h C).1 : GaussianInt) * (A h D).2)))
    ) := by
  classical
  intro ii L A ii_sq quarter reflection h C D x hx
  induction h generalizing C D x with
  | identity => exact hx
  | negate =>
      change GaussianQuarterTurn x ^ 2 =
        (D.1 : GaussianInt) * -C.2 - (C.1 : GaussianInt) * -D.2
      rw [quarter]
      calc
        (ii * x) ^ 2 = -(x ^ 2) := by rw [mul_pow, ii_sq]; ring
        _ = _ := by rw [hx]; ring
  | conjugate =>
      simpa [L, A, BandPackingSymmetryVectorAction, BandPackingSymmetryCircleAction,
        reflection] using congrArg star hx
  | shift w =>
      change x ^ 2 = (D.1 : GaussianInt) * (C.2 + 2 * (C.1 : GaussianInt) * w) -
        (C.1 : GaussianInt) * (D.2 + 2 * (D.1 : GaussianInt) * w)
      rw [hx]
      ring
  | comp h k ih ik => exact ih (A k C) (A k D) (L k x) (ik C D x hx)

private theorem parentNonzero :
    (by
      classical
      exact
        let v := BandVectors.1
        ∀ (p : Fin (4 : ℕ) → CircleCoordinates), ProperBandQuadruple p → ∀ (i : Fin (3 : ℕ)), ∀
            (j : Fin (3 : ℕ)), i ≠ j → v (p i.succ) (p j.succ) ≠ (0 : GaussianInt)
    ) := by
  classical
  intro v p hp i j hij
  have hc := ProperBandCurvatureStructure p hp
  have hpos : 0 < (p i.succ).1 ∨ 0 < (p j.succ).1 := by
    by_contra hn
    push Not at hn
    have hi : (p i.succ).1 = 0 := by have := hc.2.1 i; omega
    have hj : (p j.succ).1 = 0 := by have := hc.2.1 j; omega
    exact hij (hc.2.2 i j hi hj)
  exact VectorNonvanishing p hp.1 i.succ j.succ
    (fun h => hij (Fin.succ_injective _ h)) hpos

private theorem squareEdges :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        let L := BandPackingSymmetryVectorAction
        let A := BandPackingSymmetryCircleAction
        let T := BandPackingSymmetryQuadrupleAction
        let O := BandPackingSymmetryReversesOrientation
        let v := BandVectors.1
        (ii ^ 2 = -1) → ((∀ (h : BandPackingSymmetry), ∀ (C : CircleCoordinates), ∀ (D :
            CircleCoordinates), ∀ (x : GaussianInt), (x ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 :
            GaussianInt) * D.2) → (L h x ^ 2 = ((A h D).1 : GaussianInt) * (A h C).2 - ((A h C).1
            : GaussianInt) * (A h D).2)) → (
        let W (p : Fin 4 → CircleCoordinates) (i : Fin 3) :=
          v (p ((i + 2).succ)) (p ((i + 1).succ))
        (-(1 : Fin 3) = 2) → ((-(2 : Fin 3) = 1) → (∀ (h : BandPackingSymmetry), ∀ (p : Fin (4 :
            ℕ) → CircleCoordinates), ProperBandQuadruple p → ∀ (i : Fin (3 : ℕ)), W (T h p) (if O
            h = true then -i else i) ^ (2 : ℕ) = (if O h = true then ii * L h (W p i) else L h (W
            p i)) ^ (2 : ℕ)))))
    ) := by
  classical
  intro ii L A T O v ii_sq squareMap W neg1 neg2 h p hp i
  have ht := BandPackingSymmetryProperCovariance h p hp
  have hij : (i + 2).succ ≠ (i + 1).succ := by fin_cases i <;> decide
  have hs := squareMap h (p ((i + 2).succ)) (p ((i + 1).succ)) (W p i)
    (by simpa only [W, v, zsmul_eq_mul] using
      (VectorSquareProduct p hp.1 (i + 2).succ (i + 1).succ hij).1)
  let j : Fin 3 := if O h then -i else i
  have hj : (j + 2).succ ≠ (j + 1).succ := by
    have allDifferent : ∀ k : Fin 3, (k + 2).succ ≠ (k + 1).succ := by decide +kernel
    exact allDifferent j
  have hs' := (VectorSquareProduct (T h p) ht.1
    (j + 2).succ (j + 1).succ hj).1
  cases he : O h <;> fin_cases i
  all_goals
    simp only [he, Bool.false_eq_true, ↓reduceIte, Fin.mk_one, Fin.isValue, Fin.reduceAdd,
        Fin.succ_zero_eq_one, BandPackingSymmetryQuadrupleAction, Fin.succ_one_eq_two,
        Fin.reduceSucc, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
        zsmul_eq_mul, T, j, O, W, A, Fin.reduceFinMk, Fin.zero_eta, zero_add, neg1, neg_zero,
        neg2] at hs' hs ⊢
    first
    | exact hs'.trans hs.symm
    | rw [mul_pow, ii_sq, hs', hs]; ring

private theorem commonSign :
    (by
      classical
      exact
        ∀ (a : Fin (3 : ℕ) → GaussianInt), ∀ (b : Fin (3 : ℕ) → GaussianInt), a (0 : Fin (3 : ℕ))
            + a (1 : Fin (3 : ℕ)) + a (2 : Fin (3 : ℕ)) = (0 : GaussianInt) → b (0 : Fin (3 : ℕ))
            + b (1 : Fin (3 : ℕ)) + b (2 : Fin (3 : ℕ)) = (0 : GaussianInt) → (∀ (i : Fin (3 :
            ℕ)), b i ≠ (0 : GaussianInt)) → (∀ (i : Fin (3 : ℕ)), a i ^ (2 : ℕ) = b i ^ (2 : ℕ))
            → ∃ (d : Bool), ∀ (i : Fin (3 : ℕ)), a i = (if d = true then (-1 : GaussianInt) else
            (1 : GaussianInt)) * b i
    ) := by
  classical
  intro a b ha hb hn hs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs 0) with h0 | h0 <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs 1) with h1 | h1 <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs 2) with h2 | h2
  all_goals
    first
    | (refine ⟨false, ?_⟩; intro i; fin_cases i <;>
        simp only [Bool.false_eq_true, ite_false, one_mul] <;> assumption)
    | (refine ⟨true, ?_⟩; intro i; fin_cases i <;>
        simp only [ite_true, neg_one_mul] <;> assumption)
    | (rw [h0, h1, h2] at ha
       have ar := congrArg Zsqrtd.re ha
       have ai := congrArg Zsqrtd.im ha
       have br := congrArg Zsqrtd.re hb
       have bi := congrArg Zsqrtd.im hb
       simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_neg,
         Zsqrtd.im_neg, Zsqrtd.re_zero, Zsqrtd.im_zero] at ar ai br bi
       exfalso
       first
       | (apply hn 0; ext <;> simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] <;> omega)
       | (apply hn 1; ext <;> simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] <;> omega)
       | (apply hn 2; ext <;> simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] <;> omega))

private theorem phaseExists :
    (by
      classical
      exact
        let ii : GaussianInt := ⟨0, 1⟩
        let L := BandPackingSymmetryVectorAction
        let T := BandPackingSymmetryQuadrupleAction
        let O := BandPackingSymmetryReversesOrientation
        let v := BandVectors.1
        (ii ^ 2 = -1) → ((ii ≠ 0) → ((∀ (z : GaussianInt), GaussianQuarterTurn z = ii * z) → ((∀
            (h : BandPackingSymmetry), ∀ (x : GaussianInt), ∀ (y : GaussianInt), L h (x + y) = L
            h x + L h y) → ((∀ (h : BandPackingSymmetry), ∀ (x : GaussianInt), L h (-x) = -L h x)
            → ((∀ (h : BandPackingSymmetry), L h 0 = 0) → ((∀ (h : BandPackingSymmetry), ∀ (x :
            GaussianInt), (x ≠ 0) → (L h x ≠ 0)) → ((∀ (h : BandPackingSymmetry), ∀ (x :
            GaussianInt), L h (ii * x) = if O h then -ii * L h x else ii * L h x) → (
        let W (p : Fin 4 → CircleCoordinates) (i : Fin 3) :=
          v (p ((i + 2).succ)) (p ((i + 1).succ))
        (-(1 : Fin 3) = 2) → ((-(2 : Fin 3) = 1) → ((∀ (p : Fin 4 → CircleCoordinates),
            (ProperBandQuadruple p) → (∀ (i : Fin 3), W p i ≠ 0)) → ((∀ (h :
            BandPackingSymmetry), ∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (∀
            (i : Fin 3), W (T h p) (if O h then -i else i) ^ 2 = (if O h then ii * L h (W p i)
            else L h (W p i)) ^ 2)) → ((∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple
            p) → (W p 0 + W p 1 + W p 2 = 0)) → ((∀ (p : Fin 4 → CircleCoordinates),
            (ProperBandQuadruple p) → (∀ (i : Fin 3), v (p i.succ) (p 0) = W p (i + 1) - ii * W p
            (i + 2))) → ((∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (∀ (i :
            Fin 3), v (p 0) (p i.succ) = ii * v (p i.succ) (p 0))) → ((∀ (a : Fin 3 →
            GaussianInt), ∀ (b : Fin 3 → GaussianInt), (a 0 + a 1 + a 2 = 0) → ((b 0 + b 1 + b 2
            = 0) → ((∀ i, b i ≠ 0) → ((∀ i, a i ^ 2 = b i ^ 2) → (∃ d : Bool, ∀ i, a i = (if d
            then (-1 : GaussianInt) else 1) * b i))))) → (∀ (h : BandPackingSymmetry), ∀ (p : Fin
            (4 : ℕ) → CircleCoordinates), ProperBandQuadruple p → ∃ (d : Bool),
            BandPackingSymmetryScopedPhase h p d))))))))))))))))
    ) := by
  classical
  intro ii L T O v ii_sq ii_ne quarter ladd lneg lzero lnonzero lquarter W neg1 neg2 wnonzero
      squareEdges wsum rows flips commonSign h p hp
  let s : Fin 3 → Fin 3 := fun i => if O h then -i else i
  let b : Fin 3 → GaussianInt := fun i =>
    if O h then ii * L h (W p i) else L h (W p i)
  have hp' := BandPackingSymmetryProperCovariance h p hp
  have asum : W (T h p) (s 0) + W (T h p) (s 1) + W (T h p) (s 2) = 0 := by
    have hs := wsum (T h p) hp'
    cases he : O h <;>
      simpa [s, he, neg1, neg2, add_assoc, add_left_comm, add_comm] using hs
  have bsum : b 0 + b 1 + b 2 = 0 := by
    have hs : L h (W p 0) + L h (W p 1) + L h (W p 2) = 0 := by
      rw [← ladd, ← ladd, wsum p hp, lzero]
    cases he : O h
    · simpa [b, he] using hs
    · simpa [b, he, mul_add] using congrArg (fun x => ii * x) hs
  obtain ⟨d, hc⟩ := commonSign (fun i => W (T h p) (s i)) b asum bsum
    (by intro i; dsimp [b]; split
        · exact mul_ne_zero ii_ne (lnonzero h _ (wnonzero p hp i))
        · exact lnonzero h _ (wnonzero p hp i))
    (squareEdges h p hp)
  let e : GaussianInt := if d then -1 else 1
  -- The rotated successor rows propagate the cyclic sign to incoming edges.
  have incoming : ∀ i : Fin 3,
      v (T h p (s i).succ) (T h p 0) = e * L h (v (p i.succ) (p 0)) := by
    have c0 := hc 0
    have c1 := hc 1
    have c2 := hc 2
    intro i
    have row := rows (T h p) hp' (s i)
    rw [rows p hp i]
    simp only [sub_eq_add_neg, ladd, lneg, lquarter]
    cases he : O h <;> fin_cases i
    all_goals
      simp only [he, Bool.false_eq_true, ↓reduceIte, Fin.isValue, ite_mul, neg_mul, one_mul,
          Fin.mk_one, Fin.succ_one_eq_two, Fin.reduceAdd, neg_add_rev, neg_neg, s, b, e,
          Fin.reduceFinMk, Fin.reduceSucc, Fin.zero_eta, Fin.succ_zero_eq_one, zero_add,
          neg_zero, neg1, neg2] at c0 c1 c2 row ⊢
      rw [row]
      simp only [c0, c1, c2]
      cases d <;> simp <;> ring_nf <;> (try simp only [ii_sq]) <;> ring
  refine ⟨d, ?_⟩
  intro i
  simp only [quarter]
  change v (T h p (s i).succ) (T h p 0) = e * L h (v (p i.succ) (p 0)) ∧
    v (T h p 0) (T h p (s i).succ) = e *
      (if O h then -L h (v (p 0) (p i.succ)) else L h (v (p 0) (p i.succ))) ∧
    W (T h p) (s i) = e * b i
  refine ⟨incoming i, ?_, hc i⟩
  rw [flips (T h p) hp' (s i), incoming i, flips p hp i, lquarter]
  cases he : O h <;> simp [] <;> ring

private theorem pt :
    (by
      classical
      exact
        ∀ (g : BandPackingSymmetry), ∀ (q : Fin 4 → CircleCoordinates),
        let ii : GaussianInt := ⟨0, 1⟩
        let L := BandPackingSymmetryVectorAction
        let A := BandPackingSymmetryCircleAction
        let O := BandPackingSymmetryReversesOrientation
        let v := BandVectors.1
        (ii ≠ 0) → ((∀ (p : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (∀ (i : Fin 3),
            v (p 0) (p i.succ) = ii * v (p i.succ) (p 0))) → ((∀ (h : BandPackingSymmetry), ∀ (p
            : Fin 4 → CircleCoordinates), (ProperBandQuadruple p) → (∃ d,
            BandPackingSymmetryScopedPhase h p d)) → ((∀ (h : BandPackingSymmetry), ∀ (p : Fin 4
            → CircleCoordinates), ∀ (d : Bool), (BandPackingSymmetryScopedPhase h p d) → ((if O h
            then v (A h (p 2)) (A h (p 3)) else v (A h (p 3)) (A h (p 2))) = (if d then (-1 :
            GaussianInt) else 1) * (if O h then ii * L h (v (p 3) (p 2)) else L h (v (p 3) (p
            2))))) → ((∀ (h : BandPackingSymmetry), ∀ (p : Fin 4 → CircleCoordinates), ∀ (d :
            Bool), (BandPackingSymmetryScopedPhase h p d) → (v (A h (p 1)) (A h (p 0)) = (if d
            then (-1 : GaussianInt) else 1) * L h (v (p 1) (p 0)))) → ((∀ (d : Bool), ∀ (d' :
            Bool), ∀ (x : GaussianInt), (x ≠ 0) → (((if d then (-1 : GaussianInt) else 1) * x =
            (if d' then (-1 : GaussianInt) else 1) * x) → (d = d'))) → (∀ (d : Bool),
            (BandPackingSymmetryScopedPhase g q d) → (
        let w := v (q 3) (q 2)
        (L g w ≠ 0) → (∀ t : Fin 4 → CircleCoordinates, ProperBandQuadruple t → t 0 = q 2 → t 1 =
            q 3 → BandPackingSymmetryScopedPhase g t d))))))))
    ) := by
  classical
  intro g q ii L A O v ii_ne flips phaseExists cyclic0 incoming0 signUnique d pq w ln
  let T := BandPackingSymmetryQuadrupleAction
  intro t ht ht0 ht1
  obtain ⟨dt, pht⟩ := phaseExists g t ht
  have eqt := incoming0 g t dt pht
  rw [ht0, ht1] at eqt
  have eq0 := cyclic0 g q d pq
  have hd : d = dt := by
    cases ho : O g
    · simp only [ho, Bool.false_eq_true, ite_false] at eq0
      exact signUnique d dt _ ln (eq0.symm.trans eqt)
    · have flip := flips (T g t) (BandPackingSymmetryProperCovariance g t ht) 0
      have flip' : v (A g (q 2)) (A g (q 3)) =
          ii * v (A g (q 3)) (A g (q 2)) := by
        simpa [T, O, A, BandPackingSymmetryQuadrupleAction, ho, ht0, ht1] using flip
      simp only [ho, ite_true] at eq0
      have eqs : (if d then (-1 : GaussianInt) else 1) * (ii * L g w) =
          (if dt then (-1 : GaussianInt) else 1) * (ii * L g w) := by
        calc
          _ = v (A g (q 2)) (A g (q 3)) := eq0.symm
          _ = ii * v (A g (q 3)) (A g (q 2)) := flip'
          _ = _ := by rw [eqt]; ring
      exact signUnique d dt _ (mul_ne_zero ii_ne ln) eqs
  rwa [← hd] at pht

end ProjectiveCovarianceProof

theorem BandPackingSymmetryProjectiveVectorCovariance (g : BandPackingSymmetry)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) :
    let n : BandPackingSymmetry := .comp .negate .negate
    ∃ negative : Bool,
      BandPackingSymmetryScopedPhase g q negative ∧
      (∀ r : Fin 4 → CircleCoordinates, ProperBandQuadruple r →
        r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
        BandPackingSymmetryScopedPhase g r negative) ∧
      (∀ t : Fin 4 → CircleCoordinates, ProperBandQuadruple t →
        t 0 = q 2 → t 1 = q 3 →
        BandPackingSymmetryScopedPhase g t negative) ∧
      (∀ C, BandPackingSymmetryCircleAction (.comp n g) C =
        BandPackingSymmetryCircleAction g C) ∧
      BandPackingSymmetryReversesOrientation (.comp n g) =
        BandPackingSymmetryReversesOrientation g ∧
      (∀ p, BandPackingSymmetryQuadrupleAction (.comp n g) p =
        BandPackingSymmetryQuadrupleAction g p) ∧
      (∀ v, BandPackingSymmetryVectorAction (.comp n g) v =
        -BandPackingSymmetryVectorAction g v) ∧
      ∃ g' : BandPackingSymmetry,
        (g' = g ∨ g' = .comp n g) ∧
        (∀ C, BandPackingSymmetryCircleAction g' C =
          BandPackingSymmetryCircleAction g C) ∧
        BandPackingSymmetryReversesOrientation g' =
          BandPackingSymmetryReversesOrientation g ∧
        (∀ p, BandPackingSymmetryQuadrupleAction g' p =
          BandPackingSymmetryQuadrupleAction g p) ∧
        BandPackingSymmetryScopedPhase g' q false ∧
        (∀ r : Fin 4 → CircleCoordinates, ProperBandQuadruple r →
          r 0 = q 1 → r 2 = q 2 → r 3 = q 3 →
          BandPackingSymmetryScopedPhase g' r false) ∧
        (∀ t : Fin 4 → CircleCoordinates, ProperBandQuadruple t →
          t 0 = q 2 → t 1 = q 3 →
          BandPackingSymmetryScopedPhase g' t false) := by
-- BODY
  classical
  let ii : GaussianInt := ⟨0, 1⟩
  let L := BandPackingSymmetryVectorAction
  let A := BandPackingSymmetryCircleAction
  let T := BandPackingSymmetryQuadrupleAction
  let O := BandPackingSymmetryReversesOrientation
  let v := BandVectors.1
  have ii_sq : ii ^ 2 = -1 := by decide +kernel
  have ii_ne : ii ≠ 0 := by decide +kernel
  have quarter (z : GaussianInt) : GaussianQuarterTurn z = ii * z := by
    ext <;> simp [GaussianQuarterTurn, ii]
  have reflection (z : GaussianInt) : GaussianReflection z = star z := rfl
  -- Word-level algebra does not assert exact covariance of the canonical vectors.
  have ladd (h : BandPackingSymmetry) (x y : GaussianInt) :
      L h (x + y) = L h x + L h y := by
    induction h generalizing x y with
    | identity => rfl
    | negate => simp [L, BandPackingSymmetryVectorAction, quarter, mul_add]
    | conjugate => simp [L, BandPackingSymmetryVectorAction, reflection, add_comm]
    | shift w => rfl
    | comp h k ih ik => simp [L, BandPackingSymmetryVectorAction, ih, ik]
  have lneg (h : BandPackingSymmetry) (x : GaussianInt) : L h (-x) = -L h x := by
    induction h generalizing x with
    | identity => rfl
    | negate => simp [L, BandPackingSymmetryVectorAction, quarter]
    | conjugate => simp [L, BandPackingSymmetryVectorAction, reflection]
    | shift w => rfl
    | comp h k ih ik => simp [L, BandPackingSymmetryVectorAction, ih, ik]
  have lzero (h : BandPackingSymmetry) : L h 0 = 0 := by
    induction h with
    | identity => rfl
    | negate => simp [L, BandPackingSymmetryVectorAction, quarter]
    | conjugate => simp [L, BandPackingSymmetryVectorAction, reflection]
    | shift w => rfl
    | comp h k ih ik => simp [L, BandPackingSymmetryVectorAction, ih, ik]
  have linj (h : BandPackingSymmetry) : Function.Injective (L h) :=
      ProjectiveCovarianceProof.linj ii_ne quarter reflection h
  have lnonzero (h : BandPackingSymmetry) (x : GaussianInt) (hx : x ≠ 0) :
      L h x ≠ 0 := by
    intro hz
    exact hx (linj h (hz.trans (lzero h).symm))
  have lquarter (h : BandPackingSymmetry) (x : GaussianInt) :
      L h (ii * x) = if O h then -ii * L h x else ii * L h x :=
          ProjectiveCovarianceProof.lquarter quarter lneg h x
  have squareMap (h : BandPackingSymmetry) (C D : CircleCoordinates)
      (x : GaussianInt)
      (hx : x ^ 2 = (D.1 : GaussianInt) * C.2 - (C.1 : GaussianInt) * D.2) :
      L h x ^ 2 = ((A h D).1 : GaussianInt) * (A h C).2 -
        ((A h C).1 : GaussianInt) * (A h D).2 := ProjectiveCovarianceProof.squareMap ii_sq
            quarter reflection h C D x hx
  have parentNonzero (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (i j : Fin 3) (hij : i ≠ j) : v (p i.succ) (p j.succ) ≠ 0 :=
          ProjectiveCovarianceProof.parentNonzero p hp i j hij
  let W (p : Fin 4 → CircleCoordinates) (i : Fin 3) :=
    v (p ((i + 2).succ)) (p ((i + 1).succ))
  have neg1 : -(1 : Fin 3) = 2 := rfl
  have neg2 : -(2 : Fin 3) = 1 := rfl
  have wnonzero (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (i : Fin 3) : W p i ≠ 0 := by
    apply parentNonzero p hp (i + 2) (i + 1)
    fin_cases i <;> decide
  have squareEdges (h : BandPackingSymmetry) (p : Fin 4 → CircleCoordinates)
      (hp : ProperBandQuadruple p) (i : Fin 3) :
      W (T h p) (if O h then -i else i) ^ 2 =
        (if O h then ii * L h (W p i) else L h (W p i)) ^ 2 :=
            ProjectiveCovarianceProof.squareEdges ii_sq squareMap neg1 neg2 h p hp i
  have wsum (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p) :
      W p 0 + W p 1 + W p 2 = 0 := (VectorRecursionLaws p hp.1).1
  have rows (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (i : Fin 3) :
      v (p i.succ) (p 0) = W p (i + 1) - ii * W p (i + 2) := by
    fin_cases i
    · exact (VectorRecursionLaws p hp.1).2.2.1
    · exact (VectorRecursionLaws _ (SemiProperQuadruple.rotate hp.1)).2.2.1
    · exact (VectorRecursionLaws _
        (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hp.1))).2.2.1
  have flips (p : Fin 4 → CircleCoordinates) (hp : ProperBandQuadruple p)
      (i : Fin 3) : v (p 0) (p i.succ) = ii * v (p i.succ) (p 0) :=
    ((VectorRecursionLaws p hp.1).2.2.2.2 hp i).1
  -- A mixed choice of square roots would force one superbasis vector to vanish.
  have commonSign (a b : Fin 3 → GaussianInt)
      (ha : a 0 + a 1 + a 2 = 0) (hb : b 0 + b 1 + b 2 = 0)
      (hn : ∀ i, b i ≠ 0) (hs : ∀ i, a i ^ 2 = b i ^ 2) :
      ∃ d : Bool, ∀ i, a i = (if d then (-1 : GaussianInt) else 1) * b i :=
          ProjectiveCovarianceProof.commonSign a b ha hb hn hs
  have phaseExists (h : BandPackingSymmetry) (p : Fin 4 → CircleCoordinates)
      (hp : ProperBandQuadruple p) : ∃ d, BandPackingSymmetryScopedPhase h p d :=
          ProjectiveCovarianceProof.phaseExists ii_sq ii_ne quarter ladd lneg lzero lnonzero
          lquarter neg1 neg2 wnonzero squareEdges wsum rows flips commonSign h p hp
  have cyclic0 (h : BandPackingSymmetry) (p : Fin 4 → CircleCoordinates) (d : Bool)
      (hp : BandPackingSymmetryScopedPhase h p d) :
      (if O h then v (A h (p 2)) (A h (p 3)) else v (A h (p 3)) (A h (p 2))) =
        (if d then (-1 : GaussianInt) else 1) *
          (if O h then ii * L h (v (p 3) (p 2)) else L h (v (p 3) (p 2))) := by
    have he := (hp 0).2.2
    cases ho : O h <;>
      simpa [BandPackingSymmetryScopedPhase, T, O, A, v, L,
        BandPackingSymmetryQuadrupleAction, ho, neg1, neg2, quarter] using he
  have incoming0 (h : BandPackingSymmetry) (p : Fin 4 → CircleCoordinates) (d : Bool)
      (hp : BandPackingSymmetryScopedPhase h p d) :
      v (A h (p 1)) (A h (p 0)) =
        (if d then (-1 : GaussianInt) else 1) * L h (v (p 1) (p 0)) := by
    have he := (hp 0).1
    cases ho : O h <;>
      simpa [BandPackingSymmetryScopedPhase, T, O, A, v, L,
        BandPackingSymmetryQuadrupleAction, ho] using he
  have signUnique (d d' : Bool) (x : GaussianInt) (hx : x ≠ 0)
      (he : (if d then (-1 : GaussianInt) else 1) * x =
        (if d' then (-1 : GaussianInt) else 1) * x) : d = d' := by
    have hc := mul_right_cancel₀ hx he
    cases d <;> cases d'
    · rfl
    · have hr := congrArg Zsqrtd.re hc; norm_num at hr
    · have hr := congrArg Zsqrtd.re hc; norm_num at hr
    · rfl
  obtain ⟨d, pq⟩ := phaseExists g q hq
  let w := v (q 3) (q 2)
  have wn : w ≠ 0 := wnonzero q hq 0
  have ln : L g w ≠ 0 := lnonzero g w wn
  have cn : (if O g then ii * L g w else L g w) ≠ 0 := by
    split
    · exact mul_ne_zero ii_ne ln
    · exact ln
  -- Both predecessor families share the literal ordered edge v(q 3, q 2).
  have pr : ∀ r : Fin 4 → CircleCoordinates, ProperBandQuadruple r →
      r 0 = q 1 → r 2 = q 2 → r 3 = q 3 → BandPackingSymmetryScopedPhase g r d := by
    intro r hr _ hr2 hr3
    obtain ⟨dr, phr⟩ := phaseExists g r hr
    have eqr := cyclic0 g r dr phr
    rw [hr2, hr3] at eqr
    have hd : d = dr := signUnique d dr _ cn ((cyclic0 g q d pq).symm.trans eqr)
    rwa [← hd] at phr
  have pt : ∀ t : Fin 4 → CircleCoordinates, ProperBandQuadruple t →
      t 0 = q 2 → t 1 = q 3 → BandPackingSymmetryScopedPhase g t d :=
          ProjectiveCovarianceProof.pt g q ii_ne flips phaseExists cyclic0 incoming0 signUnique d
          pq ln
  let n : BandPackingSymmetry := .comp .negate .negate
  -- Double negation fixes the geometric actions and changes the vector phase.
  have centralCircle (h : BandPackingSymmetry) (C : CircleCoordinates) :
      BandPackingSymmetryCircleAction (.comp n h) C = BandPackingSymmetryCircleAction h C := by
    simp [n, BandPackingSymmetryCircleAction]
  have centralParity (h : BandPackingSymmetry) :
      BandPackingSymmetryReversesOrientation (.comp n h) =
        BandPackingSymmetryReversesOrientation h := by
    simp [n, BandPackingSymmetryReversesOrientation]
  have centralTuple (h : BandPackingSymmetry) (p : Fin 4 → CircleCoordinates) :
      BandPackingSymmetryQuadrupleAction (.comp n h) p =
        BandPackingSymmetryQuadrupleAction h p := by
    simp only [BandPackingSymmetryQuadrupleAction, centralParity, centralCircle]
  have centralVector (h : BandPackingSymmetry) (x : GaussianInt) :
      BandPackingSymmetryVectorAction (.comp n h) x = -BandPackingSymmetryVectorAction h x := by
    change GaussianQuarterTurn (GaussianQuarterTurn (L h x)) = -L h x
    rw [quarter, quarter]
    calc
      ii * (ii * L h x) = ii ^ 2 * L h x := by ring
      _ = -L h x := by rw [ii_sq]; simp
  have adaptPhase (h : BandPackingSymmetry) (p : Fin 4 → CircleCoordinates)
      (hp : BandPackingSymmetryScopedPhase h p true) :
      BandPackingSymmetryScopedPhase (.comp n h) p false := by
    unfold BandPackingSymmetryScopedPhase at hp ⊢
    cases ho : BandPackingSymmetryReversesOrientation h <;>
      simpa [centralParity, centralTuple, centralVector, ho, quarter] using hp
  refine ⟨d, pq, pr, pt, centralCircle g, centralParity g, centralTuple g,
    centralVector g, ?_⟩
  cases d
  · exact ⟨g, Or.inl rfl, (fun _ => rfl), rfl, (fun _ => rfl), pq, pr, pt⟩
  · refine ⟨.comp n g, Or.inr rfl, centralCircle g, centralParity g,
      centralTuple g, adaptPhase g q pq, ?_, ?_⟩
    · intro r hr hr0 hr2 hr3
      exact adaptPhase g r (pr r hr hr0 hr2 hr3)
    · intro t ht ht0 ht1
      exact adaptPhase g t (pt t ht ht0 ht1)

end ApollonianSuperharmonic

end
