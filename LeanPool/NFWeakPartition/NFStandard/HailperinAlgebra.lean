/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.CylinderCompiler
public import LeanPool.NFWeakPartition.NFStandard.HailperinUnitUnion

/-! NF weak partition development: NFStandard.HailperinAlgebra. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering

section Coding

variable {S : Fol.Structure LNF} (hH : Fol.allRealizeSentence S LiteralHailperinNF)

/-! #### Exact products, cylindrification, and sections -/


/-- Cartesian product of two set objects. -/
@[expose]
noncomputable def crossObj (A B : S) : S :=
  interObj hH (cnv hH (xp hH A)) (xp hH B)

@[simp]
theorem mem_crossObj (A B a b : S) :
    Mem S (kPair hH a b) (crossObj hH A B) ↔ Mem S a A ∧ Mem S b B := by
  rw [crossObj, mem_interObj, mem_cnv_xp_kPair, mem_xp_kPair]

@[simp]
theorem valuationCode_nil (cap : Int) (ty : Fin 0 → Int) :
    valuationCode hH cap ty DVec.nil = oneC hH :=
  rfl

@[simp]
theorem valuationCode_one (cap k : Int) (a : S) :
    valuationCode hH cap (Fin.cases k Fin.elim0) (DVec.cons a DVec.nil) =
      raise hH (capOffset cap k) a :=
  rfl

@[simp]
theorem valuationCode_cons_succ {n : Nat} (cap k : Int) (ty : Fin (n + 1) → Int) (a : S)
    (xs : DVec S (n + 1)) :
    valuationCode hH cap (Fin.cases k ty) (DVec.cons a xs) =
      kPair hH (raise hH (2 * n) (raise hH (capOffset cap k) a))
        (valuationCode hH cap ty xs) :=
  rfl

theorem valuationCode_cons {n : Nat} (cap : Int) (ty : Fin (n + 2) → Int) (a : S)
    (xs : DVec S (n + 1)) :
    valuationCode hH cap ty (DVec.cons a xs) =
      kPair hH (raise hH (2 * n) (raise hH (capOffset cap (ty 0)) a))
        (valuationCode hH cap (fun i => ty i.succ) xs) :=
  by
  have hty : Fin.cases (ty 0) (fun i => ty i.succ) = ty :=
    by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simpa only [hty] using (valuationCode_cons_succ hH cap (ty 0) (fun i => ty i.succ) a xs)

/-- Existentially discard the newest coordinate.  At positive output arity this
is the exact raised image of the input set.  At arity zero the result is a
truth flag observed at the fixed nullary tuple sentinel.
-/
@[expose]
noncomputable def existsSetObj : {n : Nat} → Int → (Fin n → Int) → Int → S → S
  | 0, cap, _, k, A =>
    imageObj hH
      (crossObj hH (interObj hH A (raisedUniversal hH (capOffset cap k)))
        (singleton hH (oneC hH)))
      (universalObj hH)
  | n + 1, cap, _, k, A =>
    raisedImageObj hH (2 * n) A (raisedUniversal hH (capOffset cap k))

@[simp]
theorem mem_existsSetObj {n : Nat} (cap : Int) (ty : Fin n → Int) (k : Int) (A : S)
    (xs : DVec S n) :
    Mem S (valuationCode hH cap ty xs) (existsSetObj hH cap ty k A) ↔
      ∃ a : S, Mem S (valuationCode hH cap (Fin.cases k ty) (DVec.cons a xs)) A :=
  by
  cases n with
  | zero =>
    have hxs : xs = DVec.nil := DVec.zero_eq xs
    subst xs
    simp only [existsSetObj, valuationCode_nil, mem_imageObj, mem_universalObj, true_and,
      mem_crossObj, mem_interObj, mem_singleton]
    constructor
    · rintro ⟨y, ⟨hyA, hyLevel⟩, _⟩
      rcases (mem_raisedUniversal hH (capOffset cap k) y).1 hyLevel with ⟨a, rfl⟩
      exact ⟨a, hyA⟩
    · rintro ⟨a, ha⟩
      exact
        ⟨raise hH (capOffset cap k) a, ⟨ha, (mem_raisedUniversal hH _ _).2 ⟨a, rfl⟩⟩,
          trivial⟩
  | succ n =>
    simp only [existsSetObj, mem_raisedImageObj]
    constructor
    · rintro ⟨y, hyLevel, hyA⟩
      rcases (mem_raisedUniversal hH (capOffset cap k) y).1 hyLevel with ⟨a, rfl⟩
      refine ⟨a, ?_⟩
      simpa [valuationCode_cons_succ] using hyA
    · rintro ⟨a, ha⟩
      refine ⟨raise hH (capOffset cap k) a, (mem_raisedUniversal hH _ _).2 ⟨a, rfl⟩, ?_⟩
      simpa [valuationCode_cons_succ] using ha

/-- Fix the tail coordinates and lower the normalized head back to a set. -/
@[expose]
noncomputable def sliceObj : {n : Nat} → Int → (Fin (n + 1) → Int) → S → DVec S n → S
  | 0, cap, ty, A, _ => unitUnionIter hH (capOffset cap (ty 0)) A
  | n + 1, cap, ty, A, xs =>
    unitUnionIter hH (2 * n + capOffset cap (ty 0))
      (imageObj hH (cnv hH A) (singleton hH (valuationCode hH cap (fun i => ty i.succ) xs)))

@[simp]
theorem mem_sliceObj {n : Nat} (cap : Int) (ty : Fin (n + 1) → Int) (A : S)
    (xs : DVec S n) (z : S) :
    Mem S z (sliceObj hH cap ty A xs) ↔
      Mem S (valuationCode hH cap ty (DVec.cons z xs)) A :=
  by
  cases n with
  | zero =>
    have hxs : xs = DVec.nil := DVec.zero_eq xs
    subst xs
    simp [sliceObj, valuationCode, normalizeVec]
  | succ n =>
    simp only [sliceObj, mem_unitUnionIter, mem_imageObj, mem_singleton]
    constructor
    · rintro ⟨y, rfl, hy⟩
      rw [mem_cnv] at hy
      simpa only [valuationCode_cons hH cap ty z xs, raise_add] using hy
    · intro ha
      refine ⟨valuationCode hH cap (fun i => ty i.succ) xs, rfl, ?_⟩
      rw [mem_cnv]
      simpa only [valuationCode_cons hH cap ty z xs, raise_add] using ha

/-! #### Coordinate selectors

`headRel j R` lifts a binary relation `R` to homogeneous tuple codes and
tests the head against coordinate `j`.  `Ins3` handles the next coordinate;
`Ins2` skips it and recurses.  This is precisely the purpose of the two
inserted-pair primitives in Hailperin's finite basis.
-/


/-- Test the head and coordinate `j` of a homogeneous tuple against `R`. -/
@[expose]
noncomputable def headRel : {n : Nat} → Fin n → S → S
  | 0, j, _ => Fin.elim0 j
  | 1, _, _ => universalObj hH
  | 2, j, R => Fin.cases (universalObj hH) (fun _ => R) j
  | n + 3, j, R =>
    Fin.cases (universalObj hH)
      (fun jt => Fin.cases (ins3 hH (siIter hH (2 * n) R))
          (fun jtt => ins2 hH (headRel (Fin.succ jtt) R)) jt)
      j

theorem mem_headRel_or_zero :
    ∀ {n : Nat} (j : Fin (n + 1)) (R : S) (xs : DVec S (n + 1)),
      j = 0 ∨
        (Mem S (htuple hH xs) (headRel hH j R) ↔ Mem S (kPair hH (lookup xs 0) (lookup xs j)) R)
  | 0, j, _, _ => Or.inl (Fin.eq_zero j)
  | 1, j, R, xs => by
    cases xs with
    | cons a xt =>
      cases xt with
      | cons b xnil =>
        cases xnil
        refine Fin.cases ?_ (fun jt => ?_) j
        · exact Or.inl rfl
        · have hjt : jt = 0 := Fin.eq_zero jt
          subst jt
          exact Or.inr Iff.rfl
  | n + 2, j, R, xs => by
    cases xs with
    | cons a xt =>
      cases xt with
      | cons b rest =>
        refine Fin.cases ?_ (fun jt => ?_) j
        · exact Or.inl rfl
        · right
          refine Fin.cases ?_ (fun jtt => ?_) jt
          · have hpad :
              raise hH (2 * (n + 1)) a =
                singleton hH (singleton hH (raise hH (2 * n) a)) :=
              by
              rw [show 2 * (n + 1) = 2 * n + 2 by omega]
              rfl
            change
              Mem S
                  (kPair hH (raise hH (2 * (n + 1)) a)
                    (kPair hH (raise hH (2 * n) b) (htuple hH rest)))
                  (ins3 hH (siIter hH (2 * n) R)) ↔
                Mem S (kPair hH a b) R
            rw [hpad, mem_ins3, mem_siIter]
          · have hpad :
              raise hH (2 * (n + 1)) a =
                singleton hH (singleton hH (raise hH (2 * n) a)) :=
              by
              rw [show 2 * (n + 1) = 2 * n + 2 by omega]
              rfl
            change
              Mem S
                  (kPair hH (raise hH (2 * (n + 1)) a)
                    (kPair hH (raise hH (2 * n) b) (htuple hH rest)))
                  (ins2 hH (headRel hH (Fin.succ jtt) R)) ↔
                Mem S (kPair hH a (lookup rest jtt)) R
            rw [hpad, mem_ins2]
            rcases mem_headRel_or_zero (Fin.succ jtt) R (DVec.cons a rest) with hzero |
              hrel
            · exact (Fin.succ_ne_zero jtt hzero).elim
            · exact hrel

theorem mem_headRel {n : Nat} (j : Fin (n + 1)) (hj : j ≠ 0) (R : S)
    (xs : DVec S (n + 1)) :
    Mem S (htuple hH xs) (headRel hH j R) ↔
      Mem S (kPair hH (lookup xs 0) (lookup xs j)) R :=
  by
  rcases mem_headRel_or_zero (hH := hH) j R xs with hzero | hrel
  · exact (hj hzero).elim
  · exact hrel

/-- Test arbitrary distinct coordinates of a homogeneous tuple against `R`. -/
@[expose]
noncomputable def coordinateRel : {n : Nat} → Fin n → Fin n → S → S
  | 0, i, _, _ => Fin.elim0 i
  | _n + 1, i, j, R =>
    Fin.cases (Fin.cases (universalObj hH) (fun jt => headRel hH (Fin.succ jt) R) j)
      (fun it => Fin.cases (headRel hH (Fin.succ it) (cnv hH R))
          (fun jt => xp hH (coordinateRel it jt R)) j)
      i

theorem mem_coordinateRel_or_eq :
    ∀ {n : Nat} (i j : Fin (n + 1)) (R : S) (xs : DVec S (n + 1)),
      i = j ∨
        (Mem S (htuple hH xs) (coordinateRel hH i j R) ↔
          Mem S (kPair hH (lookup xs i) (lookup xs j)) R)
  | 0, i, j, _, _ => Or.inl ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)
  | n + 1, i, j, R, xs => by
    cases xs with
    | cons a tail =>
      refine Fin.cases ?_ (fun it => ?_) i
      · refine Fin.cases ?_ (fun jt => ?_) j
        · exact Or.inl rfl
        · right
          exact mem_headRel hH (Fin.succ jt) (by simp) R (DVec.cons a tail)
      · refine Fin.cases ?_ (fun jt => ?_) j
        · right
          have hr := mem_headRel hH (Fin.succ it) (by simp) (cnv hH R) (DVec.cons a tail)
          change
            Mem S (htuple hH (DVec.cons a tail)) (headRel hH (Fin.succ it) (cnv hH R)) ↔
              Mem S (kPair hH (lookup tail it) a) R
          rw [hr, mem_cnv]
          simp
        · rcases mem_coordinateRel_or_eq it jt R tail with hij | hrel
          · exact Or.inl (congrArg Fin.succ hij)
          · right
            change
              Mem S (htuple hH (DVec.cons a tail)) (xp hH (coordinateRel hH it jt R)) ↔
                Mem S (kPair hH (lookup tail it) (lookup tail jt)) R
            rw [htuple_succ_succ, mem_xp_kPair]
            exact hrel

theorem mem_coordinateRel {n : Nat} (i j : Fin (n + 1)) (hij : i ≠ j) (R : S)
    (xs : DVec S (n + 1)) :
    Mem S (htuple hH xs) (coordinateRel hH i j R) ↔
      Mem S (kPair hH (lookup xs i) (lookup xs j)) R :=
  by
  rcases mem_coordinateRel_or_eq hH i j R xs with heq | hrel
  · exact (hij heq).elim
  · exact hrel

/-! #### Atomic relations on normalized valuation codes -/


/-- Equality atom at arbitrary coordinates. -/
@[expose]
noncomputable def eqSetObj {n : Nat} (cap : Int) (ty : Fin n → Int) (i j : Fin n) : S :=
  if _ : i = j then universalObj hH
  else coordinateRel hH i j (siIter hH (capOffset cap (ty i)) (identityRel hH))

@[simp]
theorem mem_eqSetObj {n : Nat} (cap : Int) (ty : Fin n → Int) (_hcap : ∀ i, ty i ≤ cap)
    (i j : Fin n) (h : ty i = ty j) (xs : DVec S n) :
    Mem S (valuationCode hH cap ty xs) (eqSetObj hH cap ty i j) ↔
      lookup xs i = lookup xs j :=
  by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    by_cases hij : i = j
    · subst j
      simp [eqSetObj]
    · rw [eqSetObj, dite_eq_right hij]
      change
        Mem S (htuple hH (normalizeVec hH (fun q => capOffset cap (ty q)) xs))
            (coordinateRel hH i j (siIter hH (capOffset cap (ty i)) (identityRel hH))) ↔
          _
      rw [mem_coordinateRel hH i j hij]
      simp [h]

/-- Membership atom at arbitrary coordinates. -/
@[expose]
noncomputable def memSetObj {n : Nat} (cap : Int) (ty : Fin n → Int) (i j : Fin n) : S :=
  coordinateRel hH i j (siIter hH (capOffset cap (ty j)) (sset hH))

@[simp]
theorem mem_memSetObj {n : Nat} (cap : Int) (ty : Fin n → Int) (hcap : ∀ i, ty i ≤ cap)
    (i j : Fin n) (h : ty j = ty i + 1) (xs : DVec S n) :
    Mem S (valuationCode hH cap ty xs) (memSetObj hH cap ty i j) ↔
      Mem S (lookup xs i) (lookup xs j) :=
  by
  cases n with
  | zero => exact Fin.elim0 i
  | succ
    n =>
    have hij : i ≠ j := by
      intro hij
      subst j
      omega
    have hi := capOffset_cast (cap := cap) (k := ty i) (hcap i)
    have hj := capOffset_cast (cap := cap) (k := ty j) (hcap j)
    have hoff : capOffset cap (ty i) = capOffset cap (ty j) + 1 := by omega
    rw [memSetObj]
    change
      Mem S (htuple hH (normalizeVec hH (fun q => capOffset cap (ty q)) xs))
          (coordinateRel hH i j (siIter hH (capOffset cap (ty j)) (sset hH))) ↔
        _
    rw [mem_coordinateRel hH i j hij]
    simpa [hoff] using
      mem_raisedMembership hH (capOffset cap (ty j)) (lookup xs i) (lookup xs j)

/-! #### The complete cap-aware cylinder algebra -/


/-- Hailperin's finite basis supplies the full uniform cylinder compiler. -/
@[expose]
noncomputable def hailperinCylinderAlgebra : CylinderAlgebra S
    where
  code := fun cap ty xs => valuationCode hH cap ty xs
  empty := fun _ _ => emptyObj hH
  compl := fun _ _ A => complement hH A
  inter := fun _ _ A B => interObj hH A B
  eqSet := fun cap ty i j => eqSetObj hH cap ty i j
  memSet := fun cap ty i j => memSetObj hH cap ty i j
  existsSet := fun cap ty k A => existsSetObj hH cap ty k A
  slice := fun cap ty A xs => sliceObj hH cap ty A xs
  mem_empty := fun _ _ _ xs => not_mem_emptyObj hH (valuationCode hH _ _ xs)
  mem_compl := fun _ _ _ A xs => mem_complement hH A (valuationCode hH _ _ xs)
  mem_inter := fun _ _ _ A B xs => mem_interObj hH A B (valuationCode hH _ _ xs)
  mem_eqSet := fun cap ty hcap i j h xs => mem_eqSetObj hH cap ty hcap i j h xs
  mem_memSet := fun cap ty hcap i j h xs => mem_memSetObj hH cap ty hcap i j h xs
  mem_existsSet := fun cap ty _ k _ A xs => mem_existsSetObj hH cap ty k A xs
  mem_slice := fun cap ty _ A xs z => mem_sliceObj hH cap ty A xs z


end Coding

end NFChoice.Foundation.NFStandard
