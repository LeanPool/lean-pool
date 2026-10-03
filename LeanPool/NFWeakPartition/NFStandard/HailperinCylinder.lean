/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.HailperinModel
public import LeanPool.NFWeakPartition.NFStandard.StratificationNormalize

/-! NF weak partition development: NFStandard.HailperinCylinder. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.ReplaySupport

/-! The hard-direction compiler uses one integer type ceiling (`cap`) for a whole
formula.  Every coordinate is first raised to that ceiling by iterated
singletons.  The resulting homogeneous coordinates are then encoded by
Hailperin's type-correct tuple convention: a head is padded by two singleton
levels for every ordered-pair layer below it.
-/


section Coding

variable {S : Fol.Structure LNF} (hH : Fol.all_realize_sentence S LiteralHailperinNF)

/-! #### Iterated singleton raising -/


/-- Raise a value by `m` singleton levels. -/
@[expose]
noncomputable def raise : Nat → S → S
  | 0, a => a
  | m + 1, a => singleton hH (raise m a)

@[simp]
theorem raise_zero (a : S) : raise hH 0 a = a :=
  rfl

@[simp]
theorem raise_succ (m : Nat) (a : S) : raise hH (m + 1) a = singleton hH (raise hH m a) :=
  rfl

@[simp]
theorem mem_raise_succ (m : Nat) (a z : S) :
    Mem S z (raise hH (m + 1) a) ↔ z = raise hH m a := by simp [raise]

theorem singleton_injective : Function.Injective (singleton hH) :=
  by
  intro a b hab
  have ha : Mem S a (singleton hH b) := by
    rw [← hab]
    simp
  simpa using ha

theorem raise_injective (m : Nat) : Function.Injective (raise hH m) := by
  induction m with
  | zero => exact Function.injective_id
  | succ m ih =>
    intro a b hab
    exact ih (singleton_injective hH hab)

@[simp]
theorem raise_eq_raise_iff (m : Nat) (a b : S) : raise hH m a = raise hH m b ↔ a = b :=
  (raise_injective hH m).eq_iff

theorem raise_add (m k : Nat) (a : S) : raise hH (m + k) a = raise hH m (raise hH k a) :=
  by
  induction m with
  | zero => simp
  | succ m ih => simp [Nat.succ_add, raise, ih]

/-! #### Kuratowski-pair injectivity -/


theorem unorderedPair_eq_iff (a b c d : S) :
    unorderedPair hH a b = unorderedPair hH c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  by
  constructor
  · intro h
    have hset : ({ a, b } : Set S) = { c, d } :=
      by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [← mem_unorderedPair hH a b z, ← mem_unorderedPair hH c d z, h]
    exact Set.pair_eq_pair_iff.mp hset
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · apply extensional_of_literal_model hH
      intro z
      simp [or_comm]

theorem singleton_eq_unorderedPair_iff (a b c : S) :
    singleton hH a = unorderedPair hH b c ↔ b = a ∧ c = a :=
  by
  constructor
  · intro h
    constructor
    · have hb : Mem S b (singleton hH a) := by rw [h]; simp
      simpa using hb
    · have hc : Mem S c (singleton hH a) := by rw [h]; simp
      simpa using hc
  · rintro ⟨rfl, rfl⟩
    apply extensional_of_literal_model hH
    intro z
    simp

theorem kPair_injective {a b c d : S} (h : kPair hH a b = kPair hH c d) : a = c ∧ b = d :=
  by
  have hout :=
    (unorderedPair_eq_iff hH (singleton hH a) (unorderedPair hH a b) (singleton hH c)
          (unorderedPair hH c d)).mp
      h
  rcases hout with hdirect | hcross
  · rcases hdirect with ⟨hs, hp⟩
    have hac : a = c := singleton_injective hH hs
    rcases (unorderedPair_eq_iff hH a b c d).mp hp with hp' | hp'
    · exact hp'
    · rcases hp' with ⟨had, hbc⟩
      exact ⟨hac, hbc.trans (hac.symm.trans had)⟩
  · rcases hcross with ⟨hs, hp⟩
    have hcd : c = a ∧ d = a := (singleton_eq_unorderedPair_iff hH a c d).mp hs
    have hab : a = c ∧ b = c := (singleton_eq_unorderedPair_iff hH c a b).mp hp.symm
    exact ⟨hab.1, hab.2.trans (hcd.1.trans hcd.2.symm)⟩

/-! #### Homogeneous tuple codes -/


/-- Encode a homogeneous tuple.  At arity one the code is its sole coordinate.
At each further layer, the head receives exactly the singleton padding needed
to have the same type as the already encoded tail.
-/
@[expose]
noncomputable def htuple : {n : Nat} → DVec S n → S
  | 0, .nil => oneC hH
  | 1, .cons a .nil => a
  | n + 2, .cons a xs => kPair hH (raise hH (2 * n) a) (htuple xs)

@[simp]
theorem htuple_nil : htuple hH (DVec.nil : DVec S 0) = oneC hH :=
  rfl

@[simp]
theorem htuple_one (a : S) : htuple hH (DVec.cons a DVec.nil) = a :=
  rfl

@[simp]
theorem htuple_two (a b : S) :
    htuple hH (DVec.cons a (DVec.cons b DVec.nil)) = kPair hH a b := by rfl

@[simp]
theorem htuple_succ_succ {n : Nat} (a : S) (xs : DVec S (n + 1)) :
    htuple hH (DVec.cons a xs) = kPair hH (raise hH (2 * n) a) (htuple hH xs) := by rfl

theorem htuple_injective : ∀ n : Nat, Function.Injective (@htuple S hH n)
  | 0 => fun xs ys _ => (DVec.zero_eq xs).trans (DVec.zero_eq ys).symm
  | 1 => by
    intro xs ys hxy
    cases xs with
    | cons x xt =>
      cases xt with
      | nil =>
        cases ys with
        | cons y yt =>
          cases yt with
          | nil =>
            simp only [htuple_one] at hxy
            subst y
            rfl
  | n + 2 => by
    intro xs ys hxy
    cases xs with
    | cons x xt =>
      cases ys with
      | cons y yt =>
        have hp := kPair_injective hH hxy
        have hhead : x = y := (raise_injective hH (2 * n)) hp.1
        have htail : xt = yt := htuple_injective (n + 1) hp.2
        subst y
        subst yt
        rfl

@[simp]
theorem htuple_eq_iff {n : Nat} (xs ys : DVec S n) :
    htuple hH xs = htuple hH ys ↔ xs = ys :=
  (htuple_injective hH n).eq_iff

theorem lookup_eq_of_htuple_eq {n : Nat} {xs ys : DVec S n}
    (h : htuple hH xs = htuple hH ys) (i : Fin n) : lookup xs i = lookup ys i :=
  by
  have hxy : xs = ys := (htuple_injective hH n) h
  subst ys
  rfl

/-! #### Fixed-cap normalization -/


/-- Singleton exponent which raises type `k` to the common cap. -/
@[expose]
def capOffset (cap k : Int) : Nat :=
  Int.toNat (cap - k)

theorem capOffset_cast {cap k : Int} (h : k ≤ cap) : (capOffset cap k : Int) = cap - k :=
  by
  rw [capOffset, Int.toNat_of_nonneg]
  omega

/-- Apply a coordinate-dependent singleton exponent to a dependent vector. -/
@[expose]
noncomputable def normalizeVec : ∀ {n : Nat}, (Fin n → Nat) → DVec S n → DVec S n
  | 0, _, .nil => .nil
  | _n + 1, e, .cons a xs =>
    .cons (raise hH (e 0) a) (normalizeVec (fun i => e (Fin.succ i)) xs)

@[simp]
theorem normalizeVec_nil (e : Fin 0 → Nat) :
    normalizeVec hH e (DVec.nil : DVec S 0) = DVec.nil :=
  rfl

@[simp]
theorem normalizeVec_cons {n : Nat} (e : Fin (n + 1) → Nat) (a : S) (xs : DVec S n) :
    normalizeVec hH e (DVec.cons a xs) =
      DVec.cons (raise hH (e 0) a) (normalizeVec hH (fun i => e (Fin.succ i)) xs) :=
  rfl

@[simp]
theorem lookup_normalizeVec {n : Nat} (e : Fin n → Nat) (xs : DVec S n) (i : Fin n) :
    lookup (normalizeVec hH e xs) i = raise hH (e i) (lookup xs i) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | @cons n a xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [ih]

theorem normalizeVec_injective {n : Nat} (e : Fin n → Nat) :
    Function.Injective (normalizeVec hH e) :=
  by
  intro xs ys h
  induction xs with
  | nil => exact (DVec.zero_eq ys).symm
  | @cons n x xt ih =>
    cases ys with
    | cons y yt =>
      simp only [normalizeVec_cons, DVec.cons.injEq] at h
      have hxy : x = y := (raise_injective hH (e 0)) h.1
      have htail : xt = yt := ih (fun i => e (Fin.succ i)) h.2
      subst y
      subst yt
      rfl

/-- Normalize every coordinate to `cap`, then encode the homogeneous tuple. -/
@[expose]
noncomputable def valuationCode {n : Nat} (cap : Int) (ty : Fin n → Int) (xs : DVec S n) :
    S :=
  htuple hH (normalizeVec hH (fun i => capOffset cap (ty i)) xs)

theorem raised_coordinate_eq_of_valuationCode_eq {n : Nat} (cap : Int) (ty : Fin n → Int)
    {xs ys : DVec S n} (h : valuationCode hH cap ty xs = valuationCode hH cap ty ys)
    (i : Fin n) :
    raise hH (capOffset cap (ty i)) (lookup xs i) =
      raise hH (capOffset cap (ty i)) (lookup ys i) :=
  by
  have hn :
    normalizeVec hH (fun j => capOffset cap (ty j)) xs =
      normalizeVec hH (fun j => capOffset cap (ty j)) ys :=
    (htuple_injective hH n) h
  have hi := congrArg (fun zs => lookup zs i) hn
  simpa using hi

theorem valuationCode_coordinate {n : Nat} (cap : Int) (ty : Fin n → Int)
    {xs ys : DVec S n} (h : valuationCode hH cap ty xs = valuationCode hH cap ty ys)
    (i : Fin n) : lookup xs i = lookup ys i :=
  (raise_injective hH (capOffset cap (ty i)))
    (raised_coordinate_eq_of_valuationCode_eq hH cap ty h i)

theorem valuationCode_injective {n : Nat} (cap : Int) (ty : Fin n → Int) :
    Function.Injective (valuationCode hH cap ty) :=
  by
  intro xs ys h
  have hn :
    normalizeVec hH (fun i => capOffset cap (ty i)) xs =
      normalizeVec hH (fun i => capOffset cap (ty i)) ys :=
    (htuple_injective hH n) h
  exact normalizeVec_injective hH (fun i => capOffset cap (ty i)) hn

/-! #### Boolean relation objects -/


/-- A universal set, built as the NAND of a set and its complement. -/
@[expose]
noncomputable def universalObj : S :=
  nin hH (complement hH (oneC hH)) (oneC hH)

@[simp]
theorem mem_universalObj (z : S) : Mem S z (universalObj hH) := by simp [universalObj]

/-- The empty set, derived as the complement of the universal set. -/
@[expose]
noncomputable def emptyObj : S :=
  complement hH (universalObj hH)

@[simp]
theorem not_mem_emptyObj (z : S) : ¬Mem S z (emptyObj hH) := by simp [emptyObj]

/-- Intersection, derived by complementing NAND. -/
@[expose]
noncomputable def interObj (A B : S) : S :=
  complement hH (nin hH A B)

@[simp]
theorem mem_interObj (A B z : S) : Mem S z (interObj hH A B) ↔ Mem S z A ∧ Mem S z B := by
  simp [interObj]

/-! #### Iteration of primitive relation transformers -/


/-- Iterate Hailperin's singleton-image transformer. -/
@[expose]
noncomputable def siIter : Nat → S → S
  | 0, A => A
  | m + 1, A => si hH (siIter m A)

@[simp]
theorem siIter_zero (A : S) : siIter hH 0 A = A :=
  rfl

@[simp]
theorem siIter_succ (m : Nat) (A : S) : siIter hH (m + 1) A = si hH (siIter hH m A) :=
  rfl

@[simp]
theorem mem_siIter (m : Nat) (A z w : S) :
    Mem S (kPair hH (raise hH m z) (raise hH m w)) (siIter hH m A) ↔
      Mem S (kPair hH z w) A :=
  by
  induction m with
  | zero => rfl
  | succ m ih => rw [siIter_succ, raise_succ, raise_succ, mem_si, ih]

/-- Identity relation, as mutual inclusion. -/
@[expose]
noncomputable def identityRel : S :=
  interObj hH (sset hH) (cnv hH (sset hH))

@[simp]
theorem mem_identityRel (a b : S) : Mem S (kPair hH a b) (identityRel hH) ↔ a = b :=
  by
  rw [identityRel, mem_interObj, mem_sset, mem_cnv, mem_sset]
  constructor
  · rintro ⟨hab, hba⟩
    exact extensional_of_literal_model hH a b (fun z => ⟨hab z, hba z⟩)
  · rintro rfl
    exact ⟨fun _ hz => hz, fun _ hz => hz⟩

/-- Inclusion of a singleton is ordinary membership. -/
@[simp]
theorem mem_sset_singleton (a b : S) :
    Mem S (kPair hH (singleton hH a) b) (sset hH) ↔ Mem S a b :=
  by
  rw [mem_sset]
  constructor
  · intro h
    exact h a ((mem_singleton hH a a).2 rfl)
  · intro hab z hz
    have hza : z = a := (mem_singleton hH a z).1 hz
    simpa [hza] using hab

/-- Equality relation after raising both inputs to the cap. -/
@[simp]
theorem mem_raisedIdentity (m : Nat) (a b : S) :
    Mem S (kPair hH (raise hH m a) (raise hH m b)) (siIter hH m (identityRel hH)) ↔
      a = b :=
  by rw [mem_siIter, mem_identityRel]

/-- Membership relation after normalizing source and target to one cap. -/
@[simp]
theorem mem_raisedMembership (m : Nat) (a b : S) :
    Mem S (kPair hH (raise hH (m + 1) a) (raise hH m b)) (siIter hH m (sset hH)) ↔
      Mem S a b :=
  by
  rw [raise_add hH m 1 a]
  simp

/-! #### Kuratowski image and composition

The apparently stronger image operation is already derivable from the
primitive Hailperin operators.  This is the semantic form of `dfimak2` in
`nf.mm`.  Isolating it here makes the later coordinate selectors independent
of the generated Metamath replay.
-/


/-- Membership in the primitive `V × B` constructor on a genuine pair. -/
@[simp]
theorem mem_xp_kPair (B a b : S) : Mem S (kPair hH a b) (xp hH B) ↔ Mem S b B :=
  by
  rw [mem_xp]
  constructor
  · rintro ⟨w, t, hwt, ht⟩
    have hp : a = w ∧ b = t := kPair_injective hH hwt
    simpa [hp.2] using ht
  · intro hb
    exact ⟨a, b, rfl, hb⟩

/-- Membership in `B × V`, obtained by conversing `V × B`. -/
@[simp]
theorem mem_cnv_xp_kPair (B a b : S) :
    Mem S (kPair hH a b) (cnv hH (xp hH B)) ↔ Mem S a B := by rw [mem_cnv, mem_xp_kPair]

/-- The chosen `1c` consists exactly of the selected singleton objects. -/
theorem mem_oneC_iff_eq_singleton (w : S) :
    Mem S w (oneC hH) ↔ ∃ y : S, w = singleton hH y :=
  by
  rw [mem_oneC]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, extensional_of_literal_model hH w (singleton hH y) ?_⟩
    intro z
    exact (hy z).trans (mem_singleton hH y z).symm
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun z => mem_singleton hH y z⟩

@[simp]
theorem mem_oneC_singleton (y : S) : Mem S (singleton hH y) (oneC hH) :=
  (mem_oneC_iff_eq_singleton hH (singleton hH y)).2 ⟨y, rfl⟩

/-- The relation used under `P6` in the standard construction of image. -/
@[expose]
noncomputable def imageKernel (A B : S) : S :=
  union hH (complement hH (cnv hH (xp hH (oneC hH))))
    (si hH (complement hH (interObj hH A (cnv hH (xp hH B)))))

theorem mem_imageKernel_all (A B z : S) :
    (∀ w : S, Mem S (kPair hH w (singleton hH z)) (imageKernel hH A B)) ↔
      ∀ y : S, ¬(Mem S y B ∧ Mem S (kPair hH y z) A) :=
  by
  constructor
  · intro hall y
    have hy := hall (singleton hH y)
    simp only [imageKernel, mem_union, mem_complement, mem_cnv_xp_kPair,
      mem_oneC_singleton, not_true_eq_false, false_or, mem_si, mem_interObj] at hy
    tauto
  · intro hall w
    rw [imageKernel, mem_union]
    by_cases hw : Mem S w (oneC hH)
    · rcases (mem_oneC_iff_eq_singleton hH w).1 hw with ⟨y, rfl⟩
      right
      rw [mem_si, mem_complement, mem_interObj, mem_cnv_xp_kPair]
      exact fun h => hall y ⟨h.2, h.1⟩
    · left
      rw [mem_complement, mem_cnv_xp_kPair]
      exact hw

/-- Image of a set under a Kuratowski relation. -/
@[expose]
noncomputable def imageObj (A B : S) : S :=
  complement hH (typeLower hH (imageKernel hH A B))

@[simp]
theorem mem_imageObj (A B z : S) :
    Mem S z (imageObj hH A B) ↔ ∃ y : S, Mem S y B ∧ Mem S (kPair hH y z) A :=
  by
  rw [imageObj, mem_complement, mem_typeLower, mem_imageKernel_all]
  push Not
  rfl

/-! A raised image is needed because `Ins2` and `Ins3` deliberately mark
their inserted coordinate by two singleton levels.  The following small
library constructs exact sets of iterated-singleton values, so the image
quantifier cannot see any unconstrained noncanonical inputs. -/


/-- The power set of `A`, built as an image of the converse subset relation. -/
@[expose]
noncomputable def powerObj (A : S) : S :=
  imageObj hH (cnv hH (sset hH)) (singleton hH A)

@[simp]
theorem mem_powerObj (A z : S) :
    Mem S z (powerObj hH A) ↔ ∀ w : S, Mem S w z → Mem S w A :=
  by
  rw [powerObj, mem_imageObj]
  constructor
  · rintro ⟨y, hy, hzy⟩
    have hyA : y = A := (mem_singleton hH A y).1 hy
    subst y
    simpa using hzy
  · intro hzA
    refine ⟨A, (mem_singleton hH A A).2 rfl, ?_⟩
    simpa using hzA

/-- Singleton subsets of `A`, i.e. the direct singleton image of `A`. -/
@[expose]
noncomputable def unitPowerObj (A : S) : S :=
  interObj hH (oneC hH) (powerObj hH A)

@[simp]
theorem mem_unitPowerObj (A z : S) :
    Mem S z (unitPowerObj hH A) ↔ ∃ x : S, Mem S x A ∧ z = singleton hH x :=
  by
  rw [unitPowerObj, mem_interObj]
  constructor
  · rintro ⟨hzOne, hzSub⟩
    rcases (mem_oneC_iff_eq_singleton hH z).1 hzOne with ⟨x, rfl⟩
    refine ⟨x, ?_, rfl⟩
    exact (mem_powerObj hH A (singleton hH x)).1 hzSub x ((mem_singleton hH x x).2 rfl)
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mem_oneC_singleton hH x, ?_⟩
    apply (mem_powerObj hH A (singleton hH x)).2
    intro w hw
    have hwx : w = x := (mem_singleton hH x w).1 hw
    simpa [hwx] using hx

/-- Direct image under `m` iterations of singleton. -/
@[expose]
noncomputable def raiseImage : Nat → S → S
  | 0, A => A
  | m + 1, A => unitPowerObj hH (raiseImage m A)

@[simp]
theorem raiseImage_zero (A : S) : raiseImage hH 0 A = A :=
  rfl

@[simp]
theorem raiseImage_succ (m : Nat) (A : S) :
    raiseImage hH (m + 1) A = unitPowerObj hH (raiseImage hH m A) :=
  rfl

@[simp]
theorem mem_raiseImage (m : Nat) (A z : S) :
    Mem S z (raiseImage hH m A) ↔ ∃ x : S, Mem S x A ∧ z = raise hH m x := by
  induction m generalizing z with
  | zero =>
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  | succ m ih =>
    rw [raiseImage_succ, mem_unitPowerObj]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (ih y).mp hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨raise hH m x, (ih (raise hH m x)).mpr ⟨x, hx, rfl⟩, rfl⟩

@[simp]
theorem mem_raiseImage_exact (m : Nat) (A x : S) :
    Mem S (raise hH m x) (raiseImage hH m A) ↔ Mem S x A :=
  by
  rw [mem_raiseImage]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : x = y := raise_injective hH m hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- All values at singleton level `m`. -/
@[expose]
noncomputable def raisedUniversal (m : Nat) : S :=
  raiseImage hH m (universalObj hH)

@[simp]
theorem mem_raisedUniversal (m : Nat) (z : S) :
    Mem S z (raisedUniversal hH m) ↔ ∃ x : S, z = raise hH m x := by
  simp [raisedUniversal]

/-- `dfimak2` with the quantified first coordinate raised by `m` levels. -/
@[expose]
noncomputable def raisedImageKernel (m : Nat) (A B : S) : S :=
  union hH (complement hH (cnv hH (xp hH (raisedUniversal hH (m + 1)))))
    (si hH (complement hH (interObj hH A (cnv hH (xp hH (raiseImage hH m B))))))

theorem mem_raisedImageKernel_all (m : Nat) (A B z : S) :
    (∀ w : S, Mem S (kPair hH w (singleton hH z)) (raisedImageKernel hH m A B)) ↔
      ∀ x : S, ¬(Mem S x B ∧ Mem S (kPair hH (raise hH m x) z) A) :=
  by
  constructor
  · intro hall x
    have hx := hall (raise hH (m + 1) x)
    rw [raise_succ] at hx
    simp only [raisedImageKernel, mem_union, mem_complement, mem_cnv_xp_kPair,
      mem_raisedUniversal, mem_si, mem_interObj, mem_raiseImage_exact] at hx
    tauto
  · intro hall w
    rw [raisedImageKernel, mem_union]
    by_cases hw : Mem S w (raisedUniversal hH (m + 1))
    · rcases (mem_raisedUniversal hH (m + 1) w).1 hw with ⟨x, rfl⟩
      rw [raise_succ]
      right
      rw [mem_si, mem_complement, mem_interObj, mem_cnv_xp_kPair, mem_raiseImage_exact]
      exact fun h => hall x ⟨h.2, h.1⟩
    · left
      rw [mem_complement, mem_cnv_xp_kPair]
      exact hw

/-- Raised-coordinate image: existentially quantify `raise m x` in a relation. -/
@[expose]
noncomputable def raisedImageObj (m : Nat) (A B : S) : S :=
  complement hH (typeLower hH (raisedImageKernel hH m A B))

@[simp]
theorem mem_raisedImageObj (m : Nat) (A B z : S) :
    Mem S z (raisedImageObj hH m A B) ↔
      ∃ x : S, Mem S x B ∧ Mem S (kPair hH (raise hH m x) z) A :=
  by
  rw [raisedImageObj, mem_complement, mem_typeLower, mem_raisedImageKernel_all]
  push Not
  rfl

/-- Relational composition, defined from insertion and image as in `df-cok`. -/
@[expose]
noncomputable def composeObj (A B : S) : S :=
  raisedImageObj hH 2 (interObj hH (ins2 hH A) (ins3 hH (cnv hH B))) (universalObj hH)

@[simp]
theorem mem_composeObj (A B a b : S) :
    Mem S (kPair hH a b) (composeObj hH A B) ↔
      ∃ x : S, Mem S (kPair hH a x) B ∧ Mem S (kPair hH x b) A :=
  by
  rw [composeObj, mem_raisedImageObj]
  constructor
  · rintro ⟨y, _hy, hpair⟩
    rw [mem_interObj] at hpair
    have hA : Mem S (kPair hH y b) A := by simpa [raise] using hpair.1
    have hB : Mem S (kPair hH a y) B :=
      by
      have : Mem S (kPair hH y a) (cnv hH B) := by simpa [raise] using hpair.2
      simpa using this
    exact ⟨y, hB, hA⟩
  · rintro ⟨y, hB, hA⟩
    refine ⟨y, mem_universalObj hH y, ?_⟩
    rw [mem_interObj]
    constructor
    · simpa [raise] using (mem_ins2 hH A y a b).2 hA
    · have hcnv : Mem S (kPair hH y a) (cnv hH B) := by simpa using hB
      simpa [raise] using (mem_ins3 hH (cnv hH B) y a b).2 hcnv

end Coding

end NFChoice.Foundation.NFStandard
