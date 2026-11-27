/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import Mathlib.Data.List.GetD
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Bits
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Problem

/-!
# Bit-parallel evaluation of the formula

The formula of a `Problem` is evaluated on `2 ^ b` assignments at once: each Boolean value is
replaced by a natural number whose bit `β` is the value under the assignment in which the first
`b` variables are the bits of `β`. The remaining variables are fixed by a number `α`. Constants
are represented by `0` (false) and by the sentinel `top b = 2 ^ 2 ^ b` (true), so that operations
involving them cost no big-number arithmetic.

`leaf P b α` is the number of models with the high variables given by `α`, and
`card_models_eq` expresses the number of all models as a sum of leaves.
-/

@[expose] public section

namespace RACert

/-- The sentinel representing the constant `true`. -/
def top (b : ℕ) : ℕ := Nat.pow 2 (Nat.pow 2 b)

theorem top_eq (b : ℕ) : top b = 2 ^ 2 ^ b := rfl

theorem top_pos (b : ℕ) : 0 < top b := Nat.pow_pos (by decide)

theorem ones_lt_top (b : ℕ) : ones b < top b := ones_lt b

/-- Selection on a Boolean, written with the recursor for fast kernel reduction. -/
local notation "sel(" c ", " t ", " e ")" => Bool.rec (motive := fun _ => ℕ) e t c

theorem beq_true {x y : ℕ} (h : x = y) : Nat.beq x y = true := by rw [Nat.beq_eq]; exact h

theorem beq_false {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  rw [Bool.eq_false_iff, Ne, Nat.beq_eq]; exact h

/-- Conjunction of tables. -/
noncomputable def and' (T x y : ℕ) : ℕ :=
  sel(Nat.beq x 0, 0, sel(Nat.beq y 0, 0, sel(Nat.beq x T, y, sel(Nat.beq y T, x, Nat.land x y))))

/-- Disjunction of tables. -/
noncomputable def or' (T x y : ℕ) : ℕ :=
  sel(Nat.beq x T, T, sel(Nat.beq y T, T, sel(Nat.beq x 0, y, sel(Nat.beq y 0, x, Nat.lor x y))))

/-- Inequality of tables; the result is a plain bit mask. `on` is the all-ones mask. -/
noncomputable def neq' (T on x y : ℕ) : ℕ :=
  sel(Nat.beq x T, sel(Nat.beq y T, 0, Nat.xor on y), sel(Nat.beq y T, Nat.xor on x, Nat.xor x y))

/-- The value of a table at the assignment `β`. -/
def sem (T x β : ℕ) : Bool := Nat.beq x T || x.testBit β

theorem sel_true (t e : ℕ) : sel(true, t, e) = t := rfl

theorem sel_false (t e : ℕ) : sel(false, t, e) = e := rfl

theorem sem_top (T β : ℕ) : sem T T β = true := by
  rw [sem, beq_true rfl, Bool.true_or]

theorem sem_of_ne {T x : ℕ} (h : x ≠ T) (β : ℕ) : sem T x β = x.testBit β := by
  rw [sem, beq_false h, Bool.false_or]

theorem sem_zero {T : ℕ} (hT : 0 < T) (β : ℕ) : sem T 0 β = false := by
  rw [sem_of_ne (by omega)]; simp

section Ops

variable {b : ℕ} {x y : ℕ}

theorem and'_spec (hx : x ≤ top b) (hy : y ≤ top b) (β : ℕ) :
    and' (top b) x y ≤ top b ∧
      sem (top b) (and' (top b) x y) β = (sem (top b) x β && sem (top b) y β) := by
  have hT := top_pos b
  unfold and'
  by_cases hx0 : x = 0
  · rw [beq_true hx0]
    dsimp only
    rw [hx0, sem_zero hT]
    exact ⟨Nat.zero_le _, rfl⟩
  rw [beq_false hx0]
  dsimp only
  by_cases hy0 : y = 0
  · rw [beq_true hy0]
    dsimp only
    rw [hy0, sem_zero hT, Bool.and_false]
    exact ⟨Nat.zero_le _, rfl⟩
  rw [beq_false hy0]
  dsimp only
  by_cases hxT : x = top b
  · rw [beq_true hxT]
    dsimp only
    rw [hxT, sem_top, Bool.true_and]
    exact ⟨hy, rfl⟩
  rw [beq_false hxT]
  dsimp only
  by_cases hyT : y = top b
  · rw [beq_true hyT]
    dsimp only
    rw [hyT, sem_top, Bool.and_true]
    exact ⟨hx, rfl⟩
  rw [beq_false hyT]
  dsimp only
  have hy' : y < 2 ^ 2 ^ b := lt_of_le_of_ne hy hyT
  have hl : Nat.land x y < top b := land_lt hy'
  exact ⟨hl.le, by rw [sem_of_ne hl.ne, sem_of_ne hxT, sem_of_ne hyT, testBit_land]⟩

theorem or'_spec (hx : x ≤ top b) (hy : y ≤ top b) (β : ℕ) :
    or' (top b) x y ≤ top b ∧
      sem (top b) (or' (top b) x y) β = (sem (top b) x β || sem (top b) y β) := by
  have hT := top_pos b
  unfold or'
  by_cases hxT : x = top b
  · rw [beq_true hxT]
    dsimp only
    rw [hxT, sem_top, Bool.true_or]
    exact ⟨le_refl _, rfl⟩
  rw [beq_false hxT]
  dsimp only
  by_cases hyT : y = top b
  · rw [beq_true hyT]
    dsimp only
    rw [hyT, sem_top, Bool.or_true]
    exact ⟨le_refl _, rfl⟩
  rw [beq_false hyT]
  dsimp only
  by_cases hx0 : x = 0
  · rw [beq_true hx0]
    dsimp only
    rw [hx0, sem_zero hT, Bool.false_or]
    exact ⟨hy, rfl⟩
  rw [beq_false hx0]
  dsimp only
  by_cases hy0 : y = 0
  · rw [beq_true hy0]
    dsimp only
    rw [hy0, sem_zero hT, Bool.or_false]
    exact ⟨hx, rfl⟩
  rw [beq_false hy0]
  dsimp only
  have hx' : x < 2 ^ 2 ^ b := lt_of_le_of_ne hx hxT
  have hy' : y < 2 ^ 2 ^ b := lt_of_le_of_ne hy hyT
  have hl : Nat.lor x y < top b := lor_lt hx' hy'
  exact ⟨hl.le, by rw [sem_of_ne hl.ne, sem_of_ne hxT, sem_of_ne hyT, testBit_lor]⟩

theorem neq'_spec (hx : x ≤ top b) (hy : y ≤ top b) {β : ℕ} (hβ : β < 2 ^ b) :
    neq' (top b) (ones b) x y < top b ∧
      (neq' (top b) (ones b) x y).testBit β = (sem (top b) x β ^^ sem (top b) y β) := by
  have hT := top_pos b
  have ho : ones b < 2 ^ 2 ^ b := ones_lt b
  have hob : (ones b).testBit β = true := by rw [testBit_ones]; simpa using hβ
  unfold neq'
  by_cases hxT : x = top b
  · rw [beq_true hxT]
    dsimp only
    by_cases hyT : y = top b
    · rw [beq_true hyT]
      dsimp only
      rw [hxT, hyT, sem_top]
      exact ⟨hT, by simp⟩
    · rw [beq_false hyT]
      dsimp only
      rw [hxT, sem_top, sem_of_ne hyT]
      have hy' : y < 2 ^ 2 ^ b := lt_of_le_of_ne hy hyT
      exact ⟨xor_lt ho hy', by rw [testBit_xor, hob]⟩
  · rw [beq_false hxT]
    dsimp only
    have hx' : x < 2 ^ 2 ^ b := lt_of_le_of_ne hx hxT
    by_cases hyT : y = top b
    · rw [beq_true hyT]
      dsimp only
      rw [hyT, sem_top, sem_of_ne hxT]
      exact ⟨xor_lt ho hx', by rw [testBit_xor, hob, Bool.xor_comm]⟩
    · rw [beq_false hyT]
      dsimp only
      rw [sem_of_ne hxT, sem_of_ne hyT]
      have hy' : y < 2 ^ 2 ^ b := lt_of_le_of_ne hy hyT
      exact ⟨xor_lt hx' hy', by rw [testBit_xor]⟩

end Ops

/-- The table of a class code, given the tables of the variables. -/
noncomputable def tab (T : ℕ) (vt : List ℕ) (code : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun m _ => Nat.rec (motive := fun _ => ℕ) T (fun j _ => nth 0 vt j) m) code

@[simp] theorem tab_zero (T : ℕ) (vt : List ℕ) : tab T vt 0 = 0 := rfl

@[simp] theorem tab_one (T : ℕ) (vt : List ℕ) : tab T vt 1 = T := rfl

@[simp] theorem tab_add_two (T : ℕ) (vt : List ℕ) (j : ℕ) : tab T vt (j + 2) = nth 0 vt j := rfl

/-- `List.map`, by direct recursion. -/
noncomputable def map' {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun x _ ih => f x :: ih) l

theorem map'_eq {α β : Type} (f : α → β) (l : List α) : map' f l = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (f x :: ·) ih

theorem nth_map {α β : Type} (f : α → β) (d : α) (l : List α) (i : ℕ) :
    nth (f d) (l.map f) i = f (nth d l i) := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih => cases i <;> simp [ih]

/-- The tables of all triples. -/
noncomputable def rowsOf (T : ℕ) (vt : List ℕ) (cls : List (List (List ℕ))) :
    List (List (List ℕ)) :=
  map' (map' (map' (tab T vt))) cls

/-- The row of tables `X a b ·`. -/
noncomputable def rowAt (rows : List (List (List ℕ))) (a b : ℕ) : List ℕ :=
  nth [] (nth [] rows a) b

theorem rowAt_rowsOf (T : ℕ) (vt : List ℕ) (cls : List (List (List ℕ))) (a b : ℕ) :
    rowAt (rowsOf T vt cls) a b = (nth [] (nth [] cls a) b).map (tab T vt) := by
  have e : rowsOf T vt cls = cls.map (List.map (List.map (tab T vt))) := by
    unfold rowsOf
    rw [map'_eq]
    congr 1
    funext l
    rw [map'_eq]
    congr 1
    funext l'
    rw [map'_eq]
  rw [rowAt, e]
  have h1 := nth_map (List.map (List.map (tab T vt))) [] cls a
  rw [List.map_nil] at h1
  rw [h1]
  have h2 := nth_map (List.map (tab T vt)) [] (nth [] cls a) b
  rw [List.map_nil] at h2
  exact h2

/-- `acc ∨ ⋁ q, l1[q] ∧ l2[q]` on tables. -/
noncomputable def dot (T : ℕ) (l1 : List ℕ) : List ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun x _ ih l2 acc =>
      List.rec (motive := fun _ => ℕ) acc (fun y ys _ => ih ys (or' T acc (and' T x y))) l2) l1

@[simp] theorem dot_nil (T : ℕ) (l2 : List ℕ) (acc : ℕ) : dot T [] l2 acc = acc := rfl

@[simp] theorem dot_cons_nil (T x : ℕ) (xs : List ℕ) (acc : ℕ) : dot T (x :: xs) [] acc = acc := rfl

@[simp] theorem dot_cons_cons (T x y : ℕ) (xs ys : List ℕ) (acc : ℕ) :
    dot T (x :: xs) (y :: ys) acc = dot T xs ys (or' T acc (and' T x y)) := rfl

/-- The variable tables `vt` realize the assignment `v` at `β`. -/
def GoodVt (b : ℕ) (vt : List ℕ) (v : ℕ → Bool) (β : ℕ) : Prop :=
  ∀ j, nth 0 vt j ≤ top b ∧ sem (top b) (nth 0 vt j) β = v j

theorem tab_spec {b : ℕ} {vt : List ℕ} {v : ℕ → Bool} {β : ℕ} (h : GoodVt b vt v β) (code : ℕ) :
    tab (top b) vt code ≤ top b ∧ sem (top b) (tab (top b) vt code) β = litB v code := by
  match code with
  | 0 => exact ⟨Nat.zero_le _, sem_zero (top_pos b) β⟩
  | 1 => exact ⟨le_refl _, sem_top _ _⟩
  | j + 2 => exact h j

theorem dot_spec {b : ℕ} {vt : List ℕ} {v : ℕ → Bool} {β : ℕ} (h : GoodVt b vt v β)
    (c1 c2 : List ℕ) {acc : ℕ} (hacc : acc ≤ top b) :
    dot (top b) (c1.map (tab (top b) vt)) (c2.map (tab (top b) vt)) acc ≤ top b ∧
      sem (top b) (dot (top b) (c1.map (tab (top b) vt)) (c2.map (tab (top b) vt)) acc) β =
        (sem (top b) acc β || (c1.zip c2).any fun p => litB v p.1 && litB v p.2) := by
  induction c1 generalizing c2 acc with
  | nil => simp [hacc]
  | cons i c1 ih =>
    cases c2 with
    | nil => simp [hacc]
    | cons j c2 =>
      obtain ⟨hi1, hi2⟩ := tab_spec h i
      obtain ⟨hj1, hj2⟩ := tab_spec h j
      obtain ⟨ha1, ha2⟩ := and'_spec hi1 hj1 β
      obtain ⟨ho1, ho2⟩ := or'_spec hacc ha1 β
      obtain ⟨h1, h2⟩ := ih c2 ho1
      rw [List.map_cons, List.map_cons, dot_cons_cons]
      refine ⟨h1, ?_⟩
      rw [h2, ho2, ha2, hi2, hj2, List.zip_cons_cons, List.any_cons, Bool.or_assoc]

theorem zip_any_eq_range (f : ℕ → Bool) :
    ∀ (k : ℕ) (c1 c2 : List ℕ), c1.length = k → c2.length = k →
      ((c1.zip c2).any fun p => f p.1 && f p.2) =
        (List.range k).any fun q => f (nth 0 c1 q) && f (nth 0 c2 q)
  | 0, c1, c2, h1, h2 => by
    rw [List.length_eq_zero_iff.mp h1]
    rfl
  | k + 1, x :: c1, y :: c2, h1, h2 => by
    rw [List.zip_cons_cons, List.any_cons, List.range_succ_eq_map, List.any_cons, List.any_map,
      zip_any_eq_range f k c1 c2 (by simpa using h1) (by simpa using h2)]
    rfl
  | k + 1, [], _, h1, _ => by simp at h1
  | k + 1, _ :: _, [], _, h2 => by simp at h2

namespace Problem

variable (P : Problem)

/-- Every row of classes has exactly one entry per atom. -/
noncomputable def checkRows : Bool :=
  allRange P.k fun a => allRange P.k fun b =>
    Nat.beq (nth [] (nth [] P.cls a) b).length P.k

theorem checkRows_spec {P : Problem} (h : P.checkRows = true) {a b : ℕ} (ha : a < P.k)
    (hb : b < P.k) : (nth [] (nth [] P.cls a) b).length = P.k := by
  have h1 := allRange_iff.mp (allRange_iff.mp h a ha) b hb
  simpa only [Nat.beq_eq] using h1

/-- The table of violations of the associativity condition of the quadruple `(r, u, t, p)`. -/
noncomputable def quadTab4 (T on : ℕ) (rows : List (List (List ℕ))) (r u t p : ℕ) : ℕ :=
  neq' T on (dot T (rowAt rows (cvN P.s r) p) (rowAt rows u t) 0)
    (dot T (rowAt rows r u) (rowAt rows p (cvN P.s t)) 0)

/-- The table of violations of the associativity condition of the quadruple with code `x`. -/
noncomputable def quadTab (T on : ℕ) (rows : List (List (List ℕ))) (x : ℕ) : ℕ :=
  P.quadTab4 T on rows (P.quadFirst x)
    (P.quadSecond x) (P.quadThird x) (P.quadFourth x)

theorem quadTab_eq (T on : ℕ) (rows : List (List (List ℕ))) (x : ℕ) :
    P.quadTab T on rows x = P.quadTab4 T on rows (x / P.k / P.k / P.k % P.k)
      (x / P.k / P.k % P.k) (x / P.k % P.k) (x % P.k) := rfl

/-- Accumulate the violations of all quadruples, stopping once every assignment is violated. -/
noncomputable def evalQuads (T on : ℕ) (rows : List (List (List ℕ))) (quads : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun bad => bad)
    (fun x _ ih bad => sel(Nat.beq bad on, on,
      ih (sel(Nat.beq (P.quadTab T on rows x) 0, bad, Nat.lor bad (P.quadTab T on rows x))))) quads

theorem evalQuads_nil (T on : ℕ) (rows : List (List (List ℕ))) (bad : ℕ) :
    P.evalQuads T on rows [] bad = bad := rfl

theorem evalQuads_cons (T on : ℕ) (rows : List (List (List ℕ))) (x : ℕ) (quads : List ℕ)
    (bad : ℕ) : P.evalQuads T on rows (x :: quads) bad =
      sel(Nat.beq bad on, on, P.evalQuads T on rows quads
        (sel(Nat.beq (P.quadTab T on rows x) 0, bad, Nat.lor bad (P.quadTab T on rows x)))) := rfl

variable {P}

theorem dot_rows_spec (hrows : P.checkRows = true) {b : ℕ} {vt : List ℕ} {v : ℕ → Bool} {β : ℕ}
    (h : GoodVt b vt v β) {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < P.k) (hb₁ : b₁ < P.k) (ha₂ : a₂ < P.k)
    (hb₂ : b₂ < P.k) :
    dot (top b) (rowAt (rowsOf (top b) vt P.cls) a₁ b₁) (rowAt (rowsOf (top b) vt P.cls) a₂ b₂)
        0 ≤ top b ∧
      sem (top b) (dot (top b) (rowAt (rowsOf (top b) vt P.cls) a₁ b₁)
        (rowAt (rowsOf (top b) vt P.cls) a₂ b₂) 0) β = dotB P.k (P.tbl v) a₁ b₁ a₂ b₂ := by
  rw [rowAt_rowsOf, rowAt_rowsOf]
  obtain ⟨h1, h2⟩ := dot_spec h (nth [] (nth [] P.cls a₁) b₁) (nth [] (nth [] P.cls a₂) b₂)
    (Nat.zero_le (top b))
  refine ⟨h1, ?_⟩
  rw [h2, sem_zero (top_pos b), Bool.false_or,
    zip_any_eq_range (litB v) P.k _ _ (checkRows_spec hrows ha₁ hb₁) (checkRows_spec hrows ha₂ hb₂)]
  rfl

theorem quadTab_spec (hrows : P.checkRows = true) {b : ℕ} {vt : List ℕ} {v : ℕ → Bool} {β : ℕ}
    (h : GoodVt b vt v β) (hβ : β < 2 ^ b) (x : ℕ) :
    P.quadTab (top b) (ones b) (rowsOf (top b) vt P.cls) x < top b ∧
      (P.quadTab (top b) (ones b) (rowsOf (top b) vt P.cls) x).testBit β = !P.quadAt v x := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  obtain ⟨hL1, hL2⟩ := dot_rows_spec hrows h (cvN_lt (hm (x / P.k / P.k / P.k))) (hm x)
    (hm (x / P.k / P.k)) (hm (x / P.k))
  obtain ⟨hR1, hR2⟩ := dot_rows_spec hrows h (hm (x / P.k / P.k / P.k)) (hm (x / P.k / P.k))
    (hm x) (cvN_lt (hm (x / P.k)))
  obtain ⟨h1, h2⟩ := neq'_spec hL1 hR1 hβ
  rw [quadTab_eq, quadTab4]
  refine ⟨h1, ?_⟩
  rw [h2, hL2, hR2, quadAt, quadB]
  cases dotB P.k (P.tbl v) (cvN P.s (x / P.k / P.k / P.k % P.k)) (x % P.k) (x / P.k / P.k % P.k)
      (x / P.k % P.k) <;>
    cases dotB P.k (P.tbl v) (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k) (x % P.k)
      (cvN P.s (x / P.k % P.k)) <;> rfl

theorem evalQuads_spec (hrows : P.checkRows = true) {b : ℕ} {vt : List ℕ} {v : ℕ → Bool} {β : ℕ}
    (h : GoodVt b vt v β) (hβ : β < 2 ^ b) (quads : List ℕ) {bad : ℕ} (hbad : bad < top b) :
    P.evalQuads (top b) (ones b) (rowsOf (top b) vt P.cls) quads bad < top b ∧
      (P.evalQuads (top b) (ones b) (rowsOf (top b) vt P.cls) quads bad).testBit β =
        (bad.testBit β || quads.any fun x => !P.quadAt v x) := by
  induction quads generalizing bad with
  | nil => exact ⟨hbad, by rw [evalQuads_nil]; simp⟩
  | cons x quads ih =>
    rw [evalQuads_cons]
    by_cases hon : bad = ones b
    · rw [beq_true hon]
      dsimp only
      rw [hon, testBit_ones]
      exact ⟨ones_lt_top b, by simp [hβ]⟩
    · rw [beq_false hon]
      dsimp only
      obtain ⟨hq1, hq2⟩ := quadTab_spec hrows h hβ x
      by_cases hq0 : P.quadTab (top b) (ones b) (rowsOf (top b) vt P.cls) x = 0
      · rw [beq_true hq0]
        dsimp only
        obtain ⟨h1, h2⟩ := ih hbad
        refine ⟨h1, ?_⟩
        rw [h2, List.any_cons, ← hq2, hq0]
        simp
      · rw [beq_false hq0]
        dsimp only
        obtain ⟨h1, h2⟩ := ih (lor_lt hbad hq1)
        refine ⟨h1, ?_⟩
        rw [h2, testBit_lor, hq2, List.any_cons, Bool.or_assoc]

end Problem

/-- The tables of the fixed variables: `T` if the corresponding bit of `α` is set, else `0`. -/
noncomputable def topTabs (T : ℕ) (t : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih α => sel(Nat.beq (Nat.mod α 2) 1, T, 0) :: ih (Nat.div α 2)) t

theorem topTabs_zero (T α : ℕ) : topTabs T 0 α = [] := rfl

theorem topTabs_succ (T t α : ℕ) :
    topTabs T (t + 1) α = sel(Nat.beq (Nat.mod α 2) 1, T, 0) :: topTabs T t (Nat.div α 2) := rfl

theorem nth_topTabs (T : ℕ) : ∀ (t α i : ℕ),
    nth 0 (topTabs T t α) i = if i < t ∧ α.testBit i = true then T else 0
  | 0, α, i => by simp [topTabs_zero]
  | t + 1, α, 0 => by
    rw [topTabs_succ, nth_cons_zero, Nat.testBit_zero]
    by_cases h : α % 2 = 1
    · rw [beq_true (show Nat.mod α 2 = 1 from h)]
      dsimp only
      simp [h]
    · rw [beq_false (show Nat.mod α 2 ≠ 1 from h)]
      dsimp only
      simp [h]
  | t + 1, α, i + 1 => by
    rw [topTabs_succ, nth_cons_succ, nth_topTabs T t _ i, Nat.testBit_succ]
    simp
    rfl

/-- The tables of the variables: truth-table columns for the first `b`, constants from `α` for the
remaining `t`. -/
noncomputable def varTabs (b t α : ℕ) : List ℕ :=
  map' (pat b) (List.range b) ++ topTabs (top b) t α

/-- The assignment in which the first `b` variables are the bits of `β` and the others the bits
of `α`. -/
def joinN (b α β j : ℕ) : Bool := if j < b then β.testBit j else α.testBit (j - b)

theorem goodVt_varTabs {b t α β : ℕ} (hα : α < 2 ^ t) (hβ : β < 2 ^ b) :
    GoodVt b (varTabs b t α) (joinN b α β) β := by
  intro j
  have hlen : (List.map (pat b) (List.range b)).length = b := by simp
  rw [varTabs, map'_eq, nth_eq_getD, joinN]
  by_cases hj : j < b
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hj), ite_eq_left_of_eq_true _ _ (eq_true hj)]
    have : (List.map (pat b) (List.range b)).getD j 0 = pat b j := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]
      simp
    rw [this]
    refine ⟨(pat_lt b j).le, ?_⟩
    rw [sem_of_ne (T := top b) (pat_lt b j).ne, testBit_pat hj]
    simp [hβ]
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega),
      ite_eq_right_of_eq_false _ _ (eq_false hj), hlen, ← nth_eq_getD, nth_topTabs]
    by_cases hc : j - b < t ∧ α.testBit (j - b) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), hc.2]
      exact ⟨le_refl _, sem_top _ _⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      refine ⟨Nat.zero_le _, ?_⟩
      rw [sem_zero (top_pos b)]
      by_cases hjt : j - b < t
      · have : α.testBit (j - b) = false := by simpa [hjt] using hc
        exact this.symm
      · have hle : 2 ^ t ≤ 2 ^ (j - b) := Nat.pow_le_pow_right (by omega) (by omega)
        exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hα hle)).symm

namespace Problem

variable (P : Problem)

/-- The number of models whose variables `b, b + 1, …` are given by the bits of `α`. -/
noncomputable def leaf (b α : ℕ) : ℕ :=
  popcount b (Nat.xor (ones b)
    (P.evalQuads (top b) (ones b) (rowsOf (top b) (varTabs b (Nat.sub P.V b) α) P.cls) P.quads 0))

/-- `∑ i < cnt, leaf (lo + i)`. -/
noncomputable def sumLeaves (b lo : ℕ) (cnt : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => Nat.add (P.leaf b (Nat.add lo i)) ih) cnt

theorem sumLeaves_zero (b lo : ℕ) : P.sumLeaves b lo 0 = 0 := rfl

theorem sumLeaves_succ (b lo cnt : ℕ) :
    P.sumLeaves b lo (cnt + 1) = P.leaf b (lo + cnt) + P.sumLeaves b lo cnt := rfl

theorem sumLeaves_eq_sum (b lo cnt : ℕ) :
    P.sumLeaves b lo cnt = ∑ i ∈ Finset.range cnt, P.leaf b (lo + i) := by
  induction cnt with
  | zero => simp [sumLeaves_zero]
  | succ cnt ih => rw [sumLeaves_succ, Finset.sum_range_succ, ih, Nat.add_comm]

theorem sumLeaves_add (b lo c₁ c₂ : ℕ) :
    P.sumLeaves b lo (c₁ + c₂) = P.sumLeaves b lo c₁ + P.sumLeaves b (lo + c₁) c₂ := by
  induction c₂ with
  | zero => simp [sumLeaves_zero]
  | succ c₂ ih =>
    rw [← Nat.add_assoc, sumLeaves_succ, sumLeaves_succ, ih, Nat.add_assoc lo]
    omega

variable {P}

/-- The assignment with low variables `w` and high variables the bits of `α`. -/
def join (b α : ℕ) (w : Fin b → Bool) (j : ℕ) : Bool :=
  if h : j < b then w ⟨j, h⟩ else α.testBit (j - b)

theorem join_testBit (b α β : ℕ) : join b α (fun i : Fin b => β.testBit i) = joinN b α β := by
  funext j
  simp only [join, joinN]
  split_ifs <;> rfl

/-- A leaf counts the models extending the assignment of the high variables. -/
theorem leaf_eq (hrows : P.checkRows = true) {b α : ℕ} (hα : α < 2 ^ (P.V - b)) :
    P.leaf b α = (Finset.univ.filter fun w : Fin b → Bool => P.phi (join b α w) = true).card := by
  have hbad : ∀ β < 2 ^ b, _ := fun β hβ =>
    evalQuads_spec hrows (goodVt_varTabs hα hβ) hβ P.quads (top_pos b)
  have h0 : P.evalQuads (top b) (ones b) (rowsOf (top b) (varTabs b (P.V - b) α) P.cls) P.quads 0
      < top b := (hbad 0 (Nat.pow_pos (by decide))).1
  rw [leaf]
  refine popcount_eq_card_filter_fun (xor_lt (ones_lt b) h0) (fun w => P.phi (join b α w)) ?_
  intro β hβ
  rw [testBit_xor, testBit_ones, (hbad β hβ).2, join_testBit, phi]
  simp only [hβ, decide_true, Nat.zero_testBit, Bool.false_or, Bool.true_xor]
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

theorem extFin_join {b : ℕ} (hb : b ≤ P.V) {α : ℕ} (hα : α < 2 ^ (P.V - b)) (w : Fin b → Bool) :
    extFin P.V (fun j : Fin P.V => join b α w j) = join b α w := by
  funext j
  by_cases hj : j < P.V
  · simp [extFin, hj]
  · have hjb : ¬ j < b := by omega
    have hle : 2 ^ (P.V - b) ≤ 2 ^ (j - b) := Nat.pow_le_pow_right (by omega) (by omega)
    simp [extFin, hj, join, hjb, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hα hle)]

/-- The high part of an assignment, as a number. -/
def highOf (b : ℕ) (hb : b ≤ P.V) (v : Fin P.V → Bool) : ℕ :=
  Nat.ofBits fun i : Fin (P.V - b) => v ⟨b + i, by omega⟩

theorem highOf_lt (b : ℕ) (hb : b ≤ P.V) (v : Fin P.V → Bool) : highOf b hb v < 2 ^ (P.V - b) :=
  Nat.ofBits_lt_two_pow _

theorem card_fiber (b : ℕ) (hb : b ≤ P.V) {α : ℕ} (hα : α < 2 ^ (P.V - b)) :
    ((Finset.univ.filter fun v : Fin P.V → Bool => P.phi (extFin P.V v) = true).filter
      fun v => highOf b hb v = α).card =
      (Finset.univ.filter fun w : Fin b → Bool => P.phi (join b α w) = true).card := by
  symm
  refine Finset.card_bij (fun w _ => fun j : Fin P.V => join b α w j) ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, by rw [extFin_join hb hα]; exact hw.2⟩, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < P.V - b
    · rw [highOf, Nat.testBit_ofBits_lt _ _ hi]
      simp [join]
    · have hle : 2 ^ (P.V - b) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (highOf_lt b hb _) hle),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hα hle)]
  · intro w _ w' _ heq
    funext ⟨i, hi⟩
    have := congrFun heq ⟨i, by omega⟩
    simpa [join, hi] using this
  · intro v hv
    rw [Finset.mem_filter, Finset.mem_filter] at hv
    obtain ⟨⟨-, hphi⟩, hhigh⟩ := hv
    have hv' : (fun j : Fin P.V => join b α (fun i : Fin b => v ⟨i, by omega⟩) j) = v := by
      funext ⟨j, hj⟩
      by_cases hjb : j < b
      · simp [join, hjb]
      · have hi : j - b < P.V - b := by omega
        have this : (highOf b hb v).testBit (j - b) = v ⟨b + (j - b), by omega⟩ :=
          Nat.testBit_ofBits_lt _ _ hi
        rw [hhigh] at this
        simp only [join, hjb, dite_false, this]
        congr 1
        apply Fin.ext
        simp only
        omega
    refine ⟨fun i => v ⟨i, by omega⟩, ?_, hv'⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← extFin_join hb hα, hv']
    exact hphi

/-- **The count.** The number of models is the sum of all leaves. -/
theorem card_models_eq (hrows : P.checkRows = true) {b : ℕ} (hb : b ≤ P.V) :
    Fintype.card (Models P) = P.sumLeaves b 0 (2 ^ (P.V - b)) := by
  rw [Fintype.card_subtype, sumLeaves_eq_sum,
    Finset.card_eq_sum_card_fiberwise (f := highOf b hb) (t := Finset.range (2 ^ (P.V - b)))
      (fun v _ => Finset.mem_range.mpr (highOf_lt b hb v))]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_range] at hα
  rw [Nat.zero_add, leaf_eq hrows hα, card_fiber b hb hα]

/-- The number of invariant lawful cycle sets, as a sum of leaves. -/
theorem fixCountL_eq_sumLeaves (hcheck : P.check = true) (hrows : P.checkRows = true) {b : ℕ}
    (hb : b ≤ P.V) : fixCountL P.s P.n P.perm = P.sumLeaves b 0 (2 ^ (P.V - b)) := by
  rw [fixCountL_eq hcheck, card_models_eq hrows hb]

/-- The form used by generated certificates: the count from the sum of all leaves. -/
theorem fixCountL_of_total (hcheck : P.check = true) (hrows : P.checkRows = true) {b cnt N : ℕ}
    (hb : Nat.ble b P.V = true) (hcnt : Nat.beq cnt (2 ^ (P.V - b)) = true)
    (htotal : P.sumLeaves b 0 cnt = N) : fixCountL P.s P.n P.perm = N := by
  rw [fixCountL_eq_sumLeaves hcheck hrows (Nat.le_of_ble_eq_true hb),
    ← Nat.eq_of_beq_eq_true hcnt, htotal]

end Problem

end RACert
