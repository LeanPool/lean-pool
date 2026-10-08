/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.FinalStage
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Log

/-!
The power-of-two padding, transposition, and first priority block from
Sections 2.3--2.4 of Matiyasevich (1995).  This file is deliberately
parameterized by the binary rule words; the preceding binary encoding stage
supplies those words and their common-length/code-language properties.
-/

@[expose] public section

namespace Undecidability
namespace Thue
namespace Matiyasevich1993
namespace Priority

/-- The three-letter alphabet used in the priority stage. -/
abbrev A₂ := Fin 3

/-- The first letter of the priority-stage alphabet. -/
def a : A₂ := 0
/-- The second letter of the priority-stage alphabet. -/
def b : A₂ := 1
/-- The separator letter of the priority-stage alphabet. -/
def e : A₂ := 2

/-- The exponent `u` for the least power `t = 2^u` not below `r`. -/
def exponent (r : ℕ) : ℕ := Nat.clog 2 r

/-- The number `t` of rows used in the transposed long relation. -/
def powerCount (r : ℕ) : ℕ := 2 ^ exponent r

theorem relationCount_le_powerCount (r : ℕ) : r ≤ powerCount r :=
  (Nat.clog_le_iff_le_pow (b := 2) (by omega)).mp le_rfl

theorem powerCount_pos (r : ℕ) : 0 < powerCount r :=
  pow_pos (by omega) _

/-- Repeat the first relation when the original list is extended to `2^u`
relations.  The paper repeats the last relation; either choice has the same
effect. -/
def paddedIndex {r : ℕ} (hr : 0 < r) (i : Fin (powerCount r)) : Fin r :=
  if h : i.val < r then ⟨i.val, h⟩ else ⟨0, hr⟩

/-- A rule-word family repeated to the least power-of-two row count. -/
def paddedSide {r : ℕ} (hr : 0 < r) {α : Type*}
    (W : Fin r → List α) (i : Fin (powerCount r)) : List α :=
  W (paddedIndex hr i)

/-- A column of a rectangular family of words. -/
def column {t : ℕ} (rows : Fin t → List (Fin 2)) (j : ℕ) : List (Fin 2) :=
  List.ofFn fun i => (rows i).getD j 0

/-- Consecutive columns, starting at column `j`. -/
def columnsFrom {t : ℕ} (rows : Fin t → List (Fin 2)) : ℕ → ℕ → List (Fin 2)
  | _, 0 => []
  | j, k + 1 => column rows j ++ columnsFrom rows (j + 1) k

/-- The column-major words `L` and `M` displayed at the bottom of page 48. -/
def transpose {t : ℕ} (width : ℕ)
    (rows : Fin t → List (Fin 2)) : List (Fin 2) :=
  columnsFrom rows 0 width

@[simp] theorem columnsFrom_succ {t : ℕ} (rows : Fin t → List (Fin 2))
    (j k : ℕ) :
    columnsFrom rows j (k + 1) =
      column rows j ++ columnsFrom rows (j + 1) k := rfl

theorem column_length {t : ℕ} (rows : Fin t → List (Fin 2)) (j : ℕ) :
    (column rows j).length = t := by
  simp [column]

theorem columnsFrom_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (start : ℕ) :
    (columnsFrom rows start width).length = width * t := by
  induction width generalizing start with
  | zero => simp [columnsFrom]
  | succ width ih =>
      simp [columnsFrom, column_length, ih, Nat.succ_mul, Nat.add_comm]

theorem transpose_length {t width : ℕ}
    (rows : Fin t → List (Fin 2)) :
    (transpose width rows).length = width * t :=
  columnsFrom_length rows 0

theorem column_zero_of_starts_aa {t : ℕ}
    (rows : Fin t → List (Fin 2))
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    column rows 0 = List.replicate t 0 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD 0 0) = fun _ => (0 : Fin 2) := by
    funext i
    obtain ⟨tail, hi⟩ := hrows i
    simp [hi]
  rw [hfun, List.ofFn_const]

theorem column_one_of_starts_aa {t : ℕ}
    (rows : Fin t → List (Fin 2))
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    column rows 1 = List.replicate t 0 := by
  unfold column
  have hfun :
      (fun i : Fin t => (rows i).getD 1 0) = fun _ => (0 : Fin 2) := by
    funext i
    obtain ⟨tail, hi⟩ := hrows i
    simp [hi]
  rw [hfun, List.ofFn_const]

/-- The long word begins with `2t` copies of `a`, the fact used on page 50. -/
theorem transpose_starts_two_columns {t width : ℕ}
    (rows : Fin t → List (Fin 2)) (hwidth : 2 ≤ width)
    (hrows : ∀ i, ∃ tail, rows i = (0 : Fin 2) :: 0 :: tail) :
    ∃ tail,
      transpose width rows = List.replicate (2 * t) 0 ++ tail := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  refine ⟨columnsFrom rows 2 k, ?_⟩
  simp only [transpose, Nat.add_comm 2 k, columnsFrom]
  rw [column_zero_of_starts_aa rows hrows,
    column_one_of_starts_aa rows hrows]
  change List.replicate t 0 ++
      (List.replicate t 0 ++ columnsFrom rows 2 k) =
    List.replicate (2 * t) 0 ++ columnsFrom rows 2 k
  rw [← List.append_assoc]
  rw [← List.replicate_add]
  congr 2
  omega

/-! ### The first priority block -/

/-- Move one `e` rightwards through pairs of binary letters.  On a binary
word this retains every second letter and leaves the `e` at the end. -/
def pushE : List A₂ → List A₂
  | x :: y :: rest =>
      if x ≠ e ∧ y ≠ e then y :: pushE rest else e :: x :: y :: rest
  | rest => e :: rest

/-- Canonical normalization for rules (20)--(23), processing from right to
left. -/
def firstNormal : List A₂ → List A₂
  | [] => []
  | x :: rest =>
      if x = e then pushE (firstNormal rest)
      else x :: firstNormal rest

@[simp] theorem firstNormal_a_cons (W : List A₂) :
    firstNormal (a :: W) = a :: firstNormal W := by
  simp [firstNormal, a, e]

@[simp] theorem firstNormal_b_cons (W : List A₂) :
    firstNormal (b :: W) = b :: firstNormal W := by
  simp [firstNormal, b, e]

@[simp] theorem firstNormal_e_cons (W : List A₂) :
    firstNormal (e :: W) = pushE (firstNormal W) := by
  simp [firstNormal]

@[simp] theorem pushE_aa (W : List A₂) :
    pushE (a :: a :: W) = a :: pushE W := by
  simp [pushE, a, e]

@[simp] theorem pushE_ab (W : List A₂) :
    pushE (a :: b :: W) = b :: pushE W := by
  simp [pushE, a, b, e]

@[simp] theorem pushE_ba (W : List A₂) :
    pushE (b :: a :: W) = a :: pushE W := by
  simp [pushE, a, b, e]

@[simp] theorem pushE_bb (W : List A₂) :
    pushE (b :: b :: W) = b :: pushE W := by
  simp [pushE, b, e]

theorem firstNormal_prefix_congr (l : List A₂) {X Y : List A₂}
    (h : firstNormal X = firstNormal Y) :
    firstNormal (l ++ X) = firstNormal (l ++ Y) := by
  induction l with
  | nil => simpa
  | cons x l ih =>
      rw [List.cons_append, List.cons_append]
      unfold firstNormal
      split <;> simp_all

/-- The four left sides (20)--(23), using the local names for `a,b,e`. -/
def housekeepingF : Fin 4 → List A₂ := ![
  [e, a, a], [e, a, b], [e, b, a], [e, b, b]
]

/-- The four right sides (20)--(23). -/
def housekeepingE : Fin 4 → List A₂ := ![
  [a, e], [b, e], [a, e], [b, e]
]

/-- One use of a housekeeping rule in any two-sided context preserves the
first priority normal form. -/
theorem firstNormal_housekeeping
    (l r : List A₂) (i : Fin 4) :
    firstNormal (l ++ housekeepingF i ++ r) =
      firstNormal (l ++ housekeepingE i ++ r) := by
  rw [List.append_assoc, List.append_assoc]
  apply firstNormal_prefix_congr l
  fin_cases i <;> simp [housekeepingF, housekeepingE]

/-- One directed rewrite from the first priority block. -/
def FirstStep (X Y : List A₂) : Prop :=
  ∃ l r i,
    X = l ++ housekeepingF i ++ r ∧
    Y = l ++ housekeepingE i ++ r

/-- The reflexive transitive closure of the first-stage housekeeping rewrite relation. -/
abbrev FirstEq := Relation.ReflTransGen FirstStep

private theorem firstStep_rule (i : Fin 4) (l r : List A₂) :
    FirstStep (l ++ housekeepingF i ++ r) (l ++ housekeepingE i ++ r) :=
  ⟨l, r, i, rfl, rfl⟩

theorem firstStep_prefix (l : List A₂) {X Y : List A₂}
    (h : FirstStep X Y) : FirstStep (l ++ X) (l ++ Y) := by
  rcases h with ⟨l', r, i, rfl, rfl⟩
  refine ⟨l ++ l', r, i, ?_, ?_⟩ <;> simp [List.append_assoc]

theorem firstEq_prefix (l : List A₂) {X Y : List A₂}
    (h : FirstEq X Y) : FirstEq (l ++ X) (l ++ Y) :=
  h.lift (l ++ ·) (fun _ _ hstep => firstStep_prefix l hstep)

/-- Greedily moving one `e` is itself a directed derivation. -/
theorem pushE_reachable (W : List A₂) : FirstEq (e :: W) (pushE W) := by
  induction W using List.twoStepInduction with
  | nil => exact Relation.ReflTransGen.refl
  | singleton x => exact Relation.ReflTransGen.refl
  | cons_cons x y rest ih _ =>
      fin_cases x <;> fin_cases y
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 0 [] rest)).trans (firstEq_prefix [a] ih)
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 1 [] rest)).trans (firstEq_prefix [b] ih)
      · exact Relation.ReflTransGen.refl
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 2 [] rest)).trans (firstEq_prefix [a] ih)
      · exact (Relation.ReflTransGen.single
          (firstStep_rule 3 [] rest)).trans (firstEq_prefix [b] ih)
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.refl

/-- Every word reduces to the canonical value computed by `firstNormal`. -/
theorem firstNormal_reachable (W : List A₂) : FirstEq W (firstNormal W) := by
  induction W with
  | nil => exact Relation.ReflTransGen.refl
  | cons x W ih =>
      have htail : FirstEq (x :: W) (x :: firstNormal W) := by
        simpa only [List.singleton_append] using firstEq_prefix [x] ih
      by_cases hx : x = e
      · subst x
        exact htail.trans (by simpa using pushE_reachable (firstNormal W))
      · simpa [firstNormal, hx] using htail

/-! ### The `e`-count and the final alignment argument -/

/-- The number of separator letters in a priority-stage word. -/
def eCount (W : List A₂) : ℕ := W.count e

@[simp] theorem eCount_nil : eCount [] = 0 := rfl

@[simp] theorem eCount_append (X Y : List A₂) :
    eCount (X ++ Y) = eCount X + eCount Y := by
  simp [eCount]

@[simp] theorem eCount_replicate_a (n : ℕ) :
    eCount (List.replicate n a) = 0 := by
  unfold eCount
  rw [List.count_eq_zero]
  simp [a, e]

@[simp] theorem eCount_ae : eCount [a, e] = 1 := by decide

theorem firstStep_eCount {X Y : List A₂} (h : FirstStep X Y) :
    eCount X = eCount Y := by
  rcases h with ⟨l, r, i, rfl, rfl⟩
  fin_cases i <;> simp [housekeepingF, housekeepingE, eCount, a, b, e]

theorem firstEq_eCount {X Y : List A₂} (h : FirstEq X Y) :
    eCount X = eCount Y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (firstStep_eCount hstep)

theorem firstNormal_eCount (W : List A₂) :
    eCount (firstNormal W) = eCount W :=
  (firstEq_eCount (firstNormal_reachable W)).symm

/-- Include a binary word into the alphabet `{a,b,e}`. -/
def liftBit (x : Fin 2) : A₂ := Fin.castLE (by omega) x

/-- The inclusion of a binary word into the three-letter priority alphabet. -/
def liftBinary (W : List (Fin 2)) : List A₂ := W.map liftBit

@[simp] theorem liftBinary_cons (x : Fin 2) (W : List (Fin 2)) :
    liftBinary (x :: W) = liftBit x :: liftBinary W := rfl

@[simp] theorem liftBinary_append (X Y : List (Fin 2)) :
    liftBinary (X ++ Y) = liftBinary X ++ liftBinary Y := by
  simp [liftBinary]

@[simp] theorem eCount_liftBinary (W : List (Fin 2)) :
    eCount (liftBinary W) = 0 := by
  unfold eCount
  rw [List.count_eq_zero]
  simp [liftBinary, liftBit, e]

theorem liftBit_injective : Function.Injective liftBit := by
  intro x y h
  apply Fin.ext
  exact congrArg (fun z : A₂ => z.val) h

theorem liftBinary_injective : Function.Injective liftBinary :=
  liftBit_injective.list_map

/-- Equation (11) for `i=1`: append `a e^u` to the binary encoding. -/
def encode (u : ℕ) (W : List (Fin 2)) : List A₂ :=
  liftBinary W ++ [a] ++ List.replicate u e

theorem encode_computable (u : ℕ) : Computable (encode u) := by
  have hlift : Primrec liftBinary :=
    Primrec.list_map Primrec.id
      ((Primrec.dom_finite liftBit).comp₂ Primrec₂.right)
  have hwithA : Primrec fun W : List (Fin 2) => liftBinary W ++ [a] :=
    Primrec.list_append.comp hlift (Primrec.const [a])
  exact (Primrec.list_append.comp hwithA
    (Primrec.const (List.replicate u e))).to_comp

theorem encode_ne_nil (u : ℕ) (W : List (Fin 2)) : encode u W ≠ [] := by
  simp [encode]

@[simp] theorem encode_eCount (u : ℕ) (W : List (Fin 2)) :
    eCount (encode u W) = u := by
  rw [show encode u W =
    liftBinary W ++ ([a] ++ List.replicate u e) by simp [encode]]
  rw [eCount_append, eCount_liftBinary]
  simp [eCount, a, e]

@[simp] theorem pushE_replicate_e (u : ℕ) :
    pushE (List.replicate u e) = e :: List.replicate u e := by
  cases u with
  | zero => rfl
  | succ u =>
      cases u with
      | zero => rfl
      | succ u =>
          rw [List.replicate_succ, List.replicate_succ]
          simp [pushE, e]

theorem firstNormal_replicate_e (u : ℕ) :
    firstNormal (List.replicate u e) = List.replicate u e := by
  induction u with
  | zero => rfl
  | succ u ih =>
      rw [List.replicate_succ, firstNormal_e_cons, ih]
      exact pushE_replicate_e u

theorem firstNormal_liftBinary_append (W : List (Fin 2)) (T : List A₂) :
    firstNormal (liftBinary W ++ T) =
      liftBinary W ++ firstNormal T := by
  induction W with
  | nil => rfl
  | cons x W ih =>
      rw [liftBinary_cons, List.cons_append]
      fin_cases x
      · change firstNormal (a :: (liftBinary W ++ T)) =
          a :: (liftBinary W ++ firstNormal T)
        rw [firstNormal_a_cons, ih]
      · change firstNormal (b :: (liftBinary W ++ T)) =
          b :: (liftBinary W ++ firstNormal T)
        rw [firstNormal_b_cons, ih]

@[simp] theorem firstNormal_encode (u : ℕ) (W : List (Fin 2)) :
    firstNormal (encode u W) = encode u W := by
  unfold encode
  rw [List.append_assoc]
  rw [firstNormal_liftBinary_append]
  simp only [List.singleton_append, firstNormal_a_cons,
    firstNormal_replicate_e]

theorem stage₂_side_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) (i : Fin 5) :
    eCount (stage₂F L i) = eCount (stage₂E M i) := by
  fin_cases i
  · change List.count (2 : Fin 3) [2, 0, 0] = List.count 2 [0, 2]
    decide
  · change List.count (2 : Fin 3) [2, 0, 1] = List.count 2 [1, 2]
    decide
  · change List.count (2 : Fin 3) [2, 1, 0] = List.count 2 [0, 2]
    decide
  · change List.count (2 : Fin 3) [2, 1, 1] = List.count 2 [1, 2]
    decide
  · change eCount L = eCount M
    exact hLM

theorem stage₂Step_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) {X Y : List A₂}
    (h : ThueStep (stage₂System L M) X Y) : eCount X = eCount Y := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  have hsides := stage₂_side_eCount L M hLM i
  rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [eCount, Nat.add_assoc] using
      congrArg (fun n => eCount l + n + eCount r) hsides
  · simpa [eCount, Nat.add_assoc] using
      (congrArg (fun n => eCount l + n + eCount r) hsides).symm

theorem stage₂Eq_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) {X Y : List A₂}
    (h : ThueEq (stage₂System L M) X Y) : eCount X = eCount Y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (stage₂Step_eCount L M hLM hstep)

/-- Absence of a run `aaa`. -/
def NoAAA (W : List A₂) : Prop :=
  ¬ ∃ l r, W = l ++ [a, a, a] ++ r

/-- A word contains `k` consecutive copies of `a`. -/
def HasARun (k : ℕ) (W : List A₂) : Prop :=
  ∃ l r, W = l ++ List.replicate k a ++ r

theorem hasARun_prefix (p : List A₂) {k : ℕ} {W : List A₂}
    (h : HasARun k W) : HasARun k (p ++ W) := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨p ++ l, r, ?_⟩
  simp only [List.append_assoc]

theorem hasARun_of_le {m n : ℕ} {W : List A₂} (hmn : m ≤ n)
    (h : HasARun n W) : HasARun m W := by
  obtain ⟨l, r, rfl⟩ := h
  refine ⟨l, List.replicate (n - m) a ++ r, ?_⟩
  calc
    l ++ List.replicate n a ++ r =
        l ++ List.replicate (m + (n - m)) a ++ r := by
          rw [Nat.add_sub_of_le hmn]
    _ = l ++ List.replicate m a ++
        (List.replicate (n - m) a ++ r) := by
          simp only [List.replicate_add, List.append_assoc]

/-- On a binary run, `pushE` keeps every second letter. -/
theorem pushE_replicate_even (k : ℕ) (W : List A₂) :
    pushE (List.replicate (2 * k) a ++ W) =
      List.replicate k a ++ pushE W := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega,
        List.replicate_add]
      change pushE (a :: a :: (List.replicate (2 * k) a ++ W)) =
        a :: (List.replicate k a ++ pushE W)
      rw [pushE_aa, ih]

/-- A possible one-letter parity offset before an even run does not affect
the sharp halving estimate. -/
theorem pushE_singleton_hasARun (x : A₂) (k : ℕ) (W : List A₂) :
    HasARun k (pushE (x :: List.replicate (2 * k) a ++ W)) := by
  cases k with
  | zero =>
      exact ⟨[], pushE (x :: W), by simp⟩
  | succ k =>
      have hrep :
          List.replicate (2 * (k + 1)) a ++ W =
            a :: (List.replicate (2 * k) a ++ (a :: W)) := by
        rw [show 2 * (k + 1) = 1 + 2 * k + 1 by omega,
          List.replicate_add, List.replicate_add]
        simp only [List.replicate_one,
          List.append_assoc, List.cons_append, List.nil_append]
      change HasARun (k + 1)
        (pushE (x :: (List.replicate (2 * (k + 1)) a ++ W)))
      by_cases hx : x = e
      · subst x
        apply hasARun_of_le (by omega : k + 1 ≤ 2 * (k + 1))
        refine ⟨[e, e], W, ?_⟩
        calc
          pushE (e :: (List.replicate (2 * (k + 1)) a ++ W)) =
              e :: e :: (List.replicate (2 * (k + 1)) a ++ W) := by
                rw [hrep]
                simp [pushE, a, e]
          _ = [e, e] ++ List.replicate (2 * (k + 1)) a ++ W := by
                simp
      · rw [hrep]
        have hpush : ∀ Z : List A₂,
            pushE (x :: a :: Z) = a :: pushE Z := by
          intro Z
          have hxe : x ≠ (2 : A₂) := by simpa [e] using hx
          simp [pushE, hxe, a, e]
        rw [hpush, pushE_replicate_even]
        refine ⟨[], pushE (a :: W), ?_⟩
        simp only [List.nil_append]
        rw [show k + 1 = Nat.succ k by omega, List.replicate_succ]
        simp only [List.cons_append]

/-- The sharp run estimate for one first-priority normalization step: one
`e` can at most halve the length of an `a`-run. -/
theorem pushE_hasARun_half {k : ℕ} {W : List A₂}
    (h : HasARun (2 * k) W) : HasARun k (pushE W) := by
  obtain ⟨l, r, rfl⟩ := h
  induction l using List.twoStepInduction with
  | nil =>
      simp only [List.nil_append]
      rw [pushE_replicate_even]
      exact ⟨[], pushE r, by simp⟩
  | singleton x =>
      exact pushE_singleton_hasARun x k r
  | cons_cons x y l ih _ =>
      by_cases hxy : x ≠ e ∧ y ≠ e
      · rw [show x :: y :: l ++ List.replicate (2 * k) a ++ r =
            x :: y :: (l ++ List.replicate (2 * k) a ++ r) by simp]
        change HasARun k (if x ≠ e ∧ y ≠ e then
          y :: pushE (l ++ List.replicate (2 * k) a ++ r)
          else e :: x :: y :: (l ++ List.replicate (2 * k) a ++ r))
        rw [ite_eq_left hxy]
        exact hasARun_prefix [y] ih
      · rw [show x :: y :: l ++ List.replicate (2 * k) a ++ r =
            x :: y :: (l ++ List.replicate (2 * k) a ++ r) by simp]
        change HasARun k (if x ≠ e ∧ y ≠ e then
          y :: pushE (l ++ List.replicate (2 * k) a ++ r)
          else e :: x :: y :: (l ++ List.replicate (2 * k) a ++ r))
        rw [ite_eq_right hxy]
        apply hasARun_of_le (by omega : k ≤ 2 * k)
        exact ⟨[e, x, y] ++ l, r, by simp [List.append_assoc]⟩

theorem firstNormal_replicate_a_append (n : ℕ) (W : List A₂) :
    firstNormal (List.replicate n a ++ W) =
      List.replicate n a ++ firstNormal W := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [List.cons_append, firstNormal_a_cons, ih]

/-- After normalizing a prefix `X`, every one of its `e` letters can have
halved a following run at most once. -/
theorem firstNormal_hasARun_scaled (X Y : List A₂) (k : ℕ) :
    HasARun k (firstNormal
      (X ++ List.replicate (2 ^ eCount X * k) a ++ Y)) := by
  induction X generalizing k with
  | nil =>
      rw [eCount_nil, pow_zero, one_mul, List.nil_append,
        firstNormal_replicate_a_append]
      exact ⟨[], firstNormal Y, by simp⟩
  | cons x X ih =>
      by_cases hx : x = e
      · subst x
        change HasARun k (pushE (firstNormal
          (X ++ List.replicate (2 ^ eCount (e :: X) * k) a ++ Y)))
        simpa [eCount, pow_succ, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using
            (pushE_hasARun_half (ih (k := 2 * k)))
      · have hi := hasARun_prefix [x] (ih (k := k))
        simpa [eCount, hx, firstNormal] using hi

theorem noAAA_not_hasARun_three {W : List A₂} (h : NoAAA W) :
    ¬ HasARun 3 W := by
  simpa [NoAAA, HasARun] using h

/-- The elementary but nontrivial run estimate invoked on page 50: destroying
a run of `run` many `a`'s while producing a first-block normal form with no
`aaa` requires at least `u` occurrences of `e` in the left context. -/
def LongRunRequirement (u run : ℕ) : Prop :=
  ∀ X Y,
    NoAAA (firstNormal (X ++ List.replicate run a ++ Y)) →
    u ≤ eCount X

/-- The quantitative assertion used on page 50.  The transposed long side
starts with `2t = 2 * 2^u` copies of `a`; if fewer than `u` priority letters
occur to its left, at least four consecutive `a`'s survive normalization. -/
theorem longRunRequirement_two_power (u : ℕ) :
    LongRunRequirement u (2 * 2 ^ u) := by
  intro X Y hnormal
  by_contra hbound
  have hlt : eCount X < u := Nat.lt_of_not_ge hbound
  have hpow : 2 ^ (eCount X + 2) ≤ 2 ^ (u + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hscale : 2 ^ eCount X * 4 ≤ 2 * 2 ^ u := by
    calc
      2 ^ eCount X * 4 = 2 ^ (eCount X + 2) := by
        rw [pow_add]
        congr
      _ ≤ 2 ^ (u + 1) := hpow
      _ = 2 * 2 ^ u := by simp [pow_succ, Nat.mul_comm]
  have hrep :
      List.replicate (2 * 2 ^ u) a ++ Y =
        List.replicate (2 ^ eCount X * 4) a ++
          (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) := by
    calc
      List.replicate (2 * 2 ^ u) a ++ Y =
          List.replicate
            (2 ^ eCount X * 4 + (2 * 2 ^ u - 2 ^ eCount X * 4)) a ++ Y := by
              rw [Nat.add_sub_of_le hscale]
      _ = List.replicate (2 ^ eCount X * 4) a ++
          (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) := by
            simp only [List.replicate_add, List.append_assoc]
  have hfour : HasARun 4
      (firstNormal (X ++ List.replicate (2 * 2 ^ u) a ++ Y)) := by
    rw [List.append_assoc, hrep, ← List.append_assoc]
    exact firstNormal_hasARun_scaled X
      (List.replicate (2 * 2 ^ u - 2 ^ eCount X * 4) a ++ Y) 4
  exact noAAA_not_hasARun_three hnormal
    (hasARun_of_le (by omega : 3 ≤ 4) hfour)

/-- The invariant furnished by equation (25): every reachable first priority
normal form remains in the binary code language and hence has no `aaa`. -/
def ReachableNoAAA (L M X : List A₂) : Prop :=
  ∀ W, ThueEq (stage₂System L M) X W → NoAAA (firstNormal W)

/-- The exact shape needed from the transposed words: the initial `2t` copies
of `a` and a final `b`. -/
def LongShape (run : ℕ) (W : List A₂) : Prop :=
  ∃ middle, W = List.replicate run a ++ middle ++ [b]

/-- Decode a long side with a residual `d` inside arbitrary contexts. -/
theorem phi₂_residual_long_context {run : ℕ} {W : List A₂}
    (hshape : LongShape run W) (l : List (Fin 2)) (R : List A₂) :
    ∃ middle,
      phi₂ (l ++ rho₂ W ++ (0 : Fin 2) :: rho₂ R) =
        phi₂ l ++ List.replicate run a ++ middle ++ [a, e] ++ R := by
  obtain ⟨middle, rfl⟩ := hshape
  refine ⟨middle, ?_⟩
  have hblock :
      rho₂ (List.replicate run a ++ middle ++ [b]) ++ [(0 : Fin 2)] =
      rho₂ (List.replicate run a ++ middle ++ [a, e]) := by
    simp [rho₂, rho₂Letter, a, b, e, List.append_assoc]
  calc
    phi₂ (l ++ rho₂ (List.replicate run a ++ middle ++ [b]) ++
        (0 : Fin 2) :: rho₂ R) =
        phi₂ (l ++ (rho₂ (List.replicate run a ++ middle ++ [b]) ++
          [(0 : Fin 2)]) ++ rho₂ R) := by
          simp only [List.append_assoc, List.singleton_append]
    _ = phi₂ (l ++ rho₂ (List.replicate run a ++ middle ++ [a, e]) ++
          rho₂ R) := by rw [hblock]
    _ = phi₂ l ++ (List.replicate run a ++ middle ++ [a, e]) ++ R :=
      phi₂_context_rho₂ l _ R
    _ = phi₂ l ++ List.replicate run a ++ middle ++ [a, e] ++ R := by
      simp only [List.append_assoc]

/-! ### Excluding the residual decoder alignment -/

/-- If the two invariants isolated on page 50 hold, then an occurrence of
the long final relation cannot be followed by the residual unmatched `d`.
This is the counting core of the converse `T₃ → T₂`: the initial run of
`a`'s forces all `u` priority letters into the left context, while decoding
the residual `d` creates one additional `e`. -/
theorem long_aligned_of_decoded_reachable {u run : ℕ}
    {L M X : List A₂} {W : List (Fin 2)}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M)
    (hdecode : ThueEq (stage₂System L M) X (phi₂ W)) :
    ∀ l r,
      (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r := by
  intro l r hocc
  rcases rho₂_phi₂_reconstruct r with hexact | hresidual
  · exact hexact
  · have hnormal : NoAAA (firstNormal (phi₂ W)) :=
      hNoAAA (phi₂ W) hdecode
    have hform : ∃ middle,
        phi₂ W = phi₂ l ++ List.replicate run a ++
          middle ++ [a, e] ++ phi₂ r := by
      rcases hocc with hocc | hocc
      · obtain ⟨middle, hmiddle⟩ :=
          phi₂_residual_long_context hshapeL l (phi₂ r)
        refine ⟨middle, ?_⟩
        calc
          phi₂ W = phi₂ (l ++ rho₂ L ++ r) := congrArg phi₂ hocc
          _ = phi₂ (l ++ rho₂ L ++
              (0 : Fin 2) :: rho₂ (phi₂ r)) := by rw [hresidual]
          _ = _ := hmiddle
      · obtain ⟨middle, hmiddle⟩ :=
          phi₂_residual_long_context hshapeM l (phi₂ r)
        refine ⟨middle, ?_⟩
        calc
          phi₂ W = phi₂ (l ++ rho₂ M ++ r) := congrArg phi₂ hocc
          _ = phi₂ (l ++ rho₂ M ++
              (0 : Fin 2) :: rho₂ (phi₂ r)) := by rw [hresidual]
          _ = _ := hmiddle
    obtain ⟨middle, hform⟩ := hform
    rw [hform] at hnormal
    have hleft : u ≤ eCount (phi₂ l) := by
      apply hRun (phi₂ l) (middle ++ [a, e] ++ phi₂ r)
      simpa only [List.append_assoc] using hnormal
    have hcount := stage₂Eq_eCount L M hLM hdecode
    rw [hX, hform] at hcount
    simp only [eCount_append, eCount_replicate_a, eCount_ae,
      Nat.add_zero] at hcount
    omega

/-- Simultaneously decode a final-system derivation and establish the
alignment invariant required for its next long-rule step.  The simultaneous
induction avoids any circularity: alignment at the current word decodes the
next step, and the decoded prefix derivation re-establishes alignment at the
new word by `long_aligned_of_decoded_reachable`. -/
theorem final_decode_and_aligned {u run : ℕ}
    {L M X : List A₂} {W : List (Fin 2)}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M)
    (hfinal : ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W) :
    ThueEq (stage₂System L M) X (phi₂ W) ∧
      ∀ l r,
        (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
        rho₂ (phi₂ r) = r := by
  induction hfinal with
  | refl =>
      have hdecode :
          ThueEq (stage₂System L M) X (phi₂ (rho₂ X)) := by
        rw [phi₂_rho₂]
        exact Relation.ReflTransGen.refl
      exact ⟨hdecode, long_aligned_of_decoded_reachable hLM hX hNoAAA
        hRun hshapeL hshapeM hdecode⟩
  | tail hab hbc ih =>
      have hstep : ThueEq (stage₂System L M) (phi₂ _) (phi₂ _) :=
        phi₂_step_of_long_aligned L M ih.2 hbc
      have hdecode := ih.1.trans hstep
      exact ⟨hdecode, long_aligned_of_decoded_reachable hLM hX hNoAAA
        hRun hshapeL hshapeM hdecode⟩

/-- The page-50 invariants imply the exact alignment predicate consumed by
the final-stage reflection theorem. -/
theorem longRuleAlignedFrom_of_invariants {u run : ℕ}
    {L M X : List A₂}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M) :
    LongRuleAlignedFrom L M X := by
  intro W hfinal
  exact (final_decode_and_aligned hLM hX hNoAAA hRun
    hshapeL hshapeM hfinal).2

/-- A convenient conditional form of equivalence (10), with the two
priority invariants made explicit. -/
theorem rho₂_iff_of_priority_invariants {u run : ℕ}
    {L M X : List A₂}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M) (Y : List A₂) :
    ThueEq (stage₂System L M) X Y ↔
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  apply rho₂_iff_of_longRuleAligned
  exact longRuleAlignedFrom_of_invariants hLM hX hNoAAA hRun
    hshapeL hshapeM

end Priority
end Matiyasevich1993
end Thue
end Undecidability
