/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.LambekCore

/-!
  The free-group interpretation of the Lambek calculus and Pentus's lemma about free
  groups.
-/

@[expose] public section

namespace FormalLinguistics

variable {P : Type}

namespace FGWord

/-! ### Basic theory of the normaliser -/

/-- `x` and `y` are mutually inverse letters. -/
abbrev Canc (x y : P × Bool) : Prop := x.1 = y.1 ∧ x.2 = !y.2

theorem canc_symm {x y : P × Bool} (h : Canc x y) : Canc y x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.symm, ?_⟩
  rw [h2]; simp

/-- A word (or stack) without adjacent mutually inverse letters. -/
def Red (s : FGWord P) : Prop :=
  ∀ (l₁ l₂ : FGWord P) (x y : P × Bool), s = l₁ ++ x :: y :: l₂ → ¬ Canc x y

theorem red_nil : Red ([] : FGWord P) := by
  intro l₁ l₂ x y h
  have := congrArg List.length h
  simp at this

theorem red_single (x : P × Bool) : Red [x] := by
  intro l₁ l₂ a b h
  have := congrArg List.length h
  simp at this
  omega

theorem red_cons_cons {x y : P × Bool} {s : FGWord P} :
    Red (x :: y :: s) ↔ ¬ Canc x y ∧ Red (y :: s) := by
  constructor
  · intro H
    refine ⟨H [] s x y rfl, ?_⟩
    intro l₁ l₂ a b h
    exact H (x :: l₁) l₂ a b (by rw [h]; rfl)
  · rintro ⟨h1, h2⟩ l₁ l₂ a b h
    cases l₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact h1
    | cons c l₁ =>
      simp only [List.cons_append, List.cons.injEq] at h
      exact h2 l₁ l₂ a b h.2

theorem red_tail {x : P × Bool} {s : FGWord P} (h : Red (x :: s)) : Red s := by
  intro l₁ l₂ a b e
  exact h (x :: l₁) l₂ a b (by rw [e]; rfl)

theorem red_reverse {s : FGWord P} (h : Red s) : Red s.reverse := by
  intro l₁ l₂ a b e
  have e' : s = l₂.reverse ++ b :: a :: l₁.reverse := by
    have := congrArg List.reverse e
    simp only [List.reverse_reverse] at this
    rw [this]
    simp
  exact fun hc => h _ _ _ _ e' (canc_symm hc)

/-- The letter-wise inversion used in `inv`. -/
abbrev flip (x : P × Bool) : P × Bool := (x.1, !x.2)

theorem red_map_flip {t : FGWord P} (h : Red t) : Red (t.map flip) := by
  induction t with
  | nil => exact red_nil
  | cons x t ih =>
    cases t with
    | nil => exact red_single _
    | cons y s =>
      rw [red_cons_cons] at h
      have ih' := ih h.2
      simp only [List.map_cons] at ih' ⊢
      rw [red_cons_cons]
      refine ⟨?_, ih'⟩
      intro hc
      apply h.1
      obtain ⟨h1, h2⟩ := hc
      refine ⟨h1, ?_⟩
      simpa using h2

theorem push_cons_of_canc [DecidableEq P] {y x : P × Bool} {s : FGWord P} (h : Canc y x) :
    push (y :: s) x = s := by
  simp only [push]
  split
  · rfl
  · contradiction

theorem push_cons_of_not [DecidableEq P] {y x : P × Bool} {s : FGWord P} (h : ¬ Canc y x) :
    push (y :: s) x = x :: y :: s := by
  simp only [push]
  split
  · contradiction
  · rfl

theorem red_push [DecidableEq P] {s : FGWord P} (h : Red s) (x : P × Bool) :
    Red (push s x) := by
  cases s with
  | nil => exact red_single x
  | cons y s' =>
    by_cases hc : Canc y x
    · rw [push_cons_of_canc hc]; exact red_tail h
    · rw [push_cons_of_not hc, red_cons_cons]
      exact ⟨fun h' => hc (canc_symm h'), h⟩

theorem red_foldl [DecidableEq P] (w : FGWord P) :
    ∀ (s : FGWord P), Red s → Red (w.foldl push s) := by
  induction w with
  | nil => intro s hs; exact hs
  | cons x w ih => intro s hs; exact ih _ (red_push hs x)

/-- Pushing a letter and then its inverse onto a reduced stack gives the stack back. -/
theorem push_push [DecidableEq P] {s : FGWord P} (h : Red s) {x z : P × Bool}
    (hc : Canc x z) : push (push s x) z = s := by
  cases s with
  | nil =>
    show push [x] z = []
    exact push_cons_of_canc hc
  | cons y s' =>
    by_cases hy : Canc y x
    · rw [push_cons_of_canc hy]
      have hyz : y = z := by
        obtain ⟨a1, a2⟩ := hy
        obtain ⟨b1, b2⟩ := hc
        apply Prod.ext
        · exact a1.trans b1
        · rw [a2, b2]; simp
      subst hyz
      cases s' with
      | nil => rfl
      | cons w s'' =>
        rw [red_cons_cons] at h
        exact push_cons_of_not (fun h' => h.1 (canc_symm h'))
    · rw [push_cons_of_not hy]
      exact push_cons_of_canc hc

/-- The stack computed by the normaliser. -/
def stk [DecidableEq P] (w : FGWord P) : FGWord P := w.foldl push []

theorem reduce_eq_stk [DecidableEq P] (w : FGWord P) : reduce w = (stk w).reverse := rfl

theorem reduce_eq_iff [DecidableEq P] {u v : FGWord P} : reduce u = reduce v ↔ stk u = stk v := by
  rw [reduce_eq_stk, reduce_eq_stk, List.reverse_inj]

theorem norm_eq_len [DecidableEq P] (w : FGWord P) : norm w = (stk w).length := by
  simp [norm, reduce_eq_stk]

theorem red_stk [DecidableEq P] (w : FGWord P) : Red (stk w) := red_foldl w [] red_nil

theorem stk_append [DecidableEq P] (u v : FGWord P) : stk (u ++ v) = v.foldl push (stk u) :=
  List.foldl_append

theorem stk_nil [DecidableEq P] : stk ([] : FGWord P) = [] := rfl

theorem stk_reverse_of_red [DecidableEq P] {s : FGWord P} (h : Red s) : stk s.reverse = s := by
  induction s with
  | nil => rfl
  | cons y s' ih =>
    rw [List.reverse_cons, stk_append, ih (red_tail h)]
    show push s' y = y :: s'
    cases s' with
    | nil => rfl
    | cons w s'' =>
      rw [red_cons_cons] at h
      exact push_cons_of_not (fun h' => h.1 (canc_symm h'))

theorem foldl_push_reverse [DecidableEq P] {s : FGWord P} (hs : Red s) (t : FGWord P)
    (x : P × Bool) :
    (push t x).reverse.foldl push s = push (t.reverse.foldl push s) x := by
  cases t with
  | nil => rfl
  | cons y t' =>
    by_cases hc : Canc y x
    · rw [push_cons_of_canc hc, List.reverse_cons, List.foldl_append]
      exact (push_push (red_foldl _ _ hs) hc).symm
    · rw [push_cons_of_not hc, List.reverse_cons (a := x), List.foldl_append]
      rfl

theorem foldl_append_eq [DecidableEq P] {s : FGWord P} (hs : Red s) (v : FGWord P) :
    ∀ (t : FGWord P), (t.reverse ++ v).foldl push s = (v.foldl push t).reverse.foldl push s := by
  induction v with
  | nil => intro t; simp
  | cons x v ih =>
    intro t
    rw [List.foldl_cons, ← ih (push t x), List.foldl_append, List.foldl_append,
      List.foldl_cons, foldl_push_reverse hs]

theorem foldl_stk_reverse [DecidableEq P] {s : FGWord P} (hs : Red s) (v : FGWord P) :
    v.foldl push s = (stk v).reverse.foldl push s := by
  have := foldl_append_eq hs v []
  simp only [List.reverse_nil, List.nil_append] at this
  exact this

theorem stk_append_right [DecidableEq P] (u v : FGWord P) :
    stk (u ++ v) = stk (u ++ (stk v).reverse) := by
  rw [stk_append, stk_append, ← foldl_stk_reverse (red_stk u)]

theorem stk_append_left [DecidableEq P] (u v : FGWord P) :
    stk (u ++ v) = stk ((stk u).reverse ++ v) := by
  rw [stk_append, stk_append, stk_reverse_of_red (red_stk u)]

theorem stk_congr [DecidableEq P] {u u' v v' : FGWord P} (hu : stk u = stk u')
    (hv : stk v = stk v') : stk (u ++ v) = stk (u' ++ v') := by
  rw [stk_append_left, hu, stk_append_right, hv, ← stk_append_right, ← stk_append_left]

theorem stk_append_of_nil [DecidableEq P] (x : FGWord P) {y : FGWord P} (hy : stk y = []) :
    stk (x ++ y) = stk x := by
  rw [stk_append_right, hy]; simp

theorem stk_mid_of_nil [DecidableEq P] (x : FGWord P) {y : FGWord P} (z : FGWord P)
    (hy : stk y = []) : stk (x ++ (y ++ z)) = stk (x ++ z) := by
  rw [← List.append_assoc, stk_append_left, stk_append_of_nil x hy, ← stk_append_left]

theorem inv_nil : inv ([] : FGWord P) = [] := rfl

theorem inv_cons (x : P × Bool) (w : FGWord P) : inv (x :: w) = inv w ++ [flip x] := by
  simp [inv]

theorem inv_append (u v : FGWord P) : inv (u ++ v) = inv v ++ inv u := by
  simp [inv]

theorem inv_inv (w : FGWord P) : inv (inv w) = w := by
  simp [inv, List.map_reverse, Function.comp_def]

theorem length_inv (w : FGWord P) : (inv w).length = w.length := by
  simp [inv]

theorem stk_append_inv [DecidableEq P] (w : FGWord P) : stk (w ++ inv w) = [] := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [inv_cons]
    have e : x :: w ++ (inv w ++ [flip x]) = [x] ++ (w ++ inv w) ++ [flip x] := by simp
    rw [e, stk_append, List.foldl_cons, List.foldl_nil, stk_append_right, ih]
    show push [x] (flip x) = []
    exact push_cons_of_canc ⟨rfl, by simp⟩

theorem stk_inv_append [DecidableEq P] (w : FGWord P) : stk (inv w ++ w) = [] := by
  have := stk_append_inv (inv w)
  rwa [inv_inv] at this

theorem stk_cancel_inv_left [DecidableEq P] (x y z : FGWord P) :
    stk (x ++ (inv y ++ (y ++ z))) = stk (x ++ z) := by
  rw [← List.append_assoc (inv y)]
  exact stk_mid_of_nil x z (stk_inv_append y)

theorem stk_cancel_inv_right [DecidableEq P] (x y z : FGWord P) :
    stk (x ++ (y ++ (inv y ++ z))) = stk (x ++ z) := by
  rw [← List.append_assoc y]
  exact stk_mid_of_nil x z (stk_append_inv y)

theorem stk_inv_congr [DecidableEq P] {u v : FGWord P} (h : stk u = stk v) :
    stk (inv u) = stk (inv v) := by
  have h1 : stk (inv u ++ v) = [] := by
    rw [stk_append_right, ← h, ← stk_append_right, stk_inv_append]
  calc stk (inv u) = stk (inv u ++ (v ++ inv v)) := by
        rw [stk_append_of_nil _ (stk_append_inv v)]
    _ = stk (inv v) := by
        rw [← List.append_assoc, stk_append_left, h1]; simp

theorem stk_inv [DecidableEq P] (w : FGWord P) : stk (inv w) = inv (stk w) := by
  have h1 : stk w = stk (stk w).reverse := (stk_reverse_of_red (red_stk w)).symm
  rw [stk_inv_congr h1]
  have e : inv (stk w).reverse = ((stk w).map flip).reverse.reverse := by simp [inv]
  rw [e, stk_reverse_of_red (red_reverse (red_map_flip (red_stk w)))]
  rfl


/-! ### Cancellation between a stack and a reduced word -/

private theorem ite_of_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

private theorem ite_of_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- Number of letters cancelled when the word `w` is pushed onto the stack `s`. -/
def cl [DecidableEq P] : FGWord P → FGWord P → Nat
  | y :: s, x :: w => if y.1 = x.1 ∧ y.2 = !x.2 then cl s w + 1 else 0
  | _, _ => 0

theorem cl_cons_cons [DecidableEq P] (y x : P × Bool) (s w : FGWord P) :
    cl (y :: s) (x :: w) = if y.1 = x.1 ∧ y.2 = !x.2 then cl s w + 1 else 0 := by
  simp [cl]

theorem cl_nil_left [DecidableEq P] (w : FGWord P) : cl [] w = 0 := by
  cases w <;> simp [cl]

theorem cl_nil_right [DecidableEq P] (s : FGWord P) : cl s [] = 0 := by
  cases s <;> simp [cl]

theorem cl_le [DecidableEq P] (s : FGWord P) :
    ∀ (w : FGWord P), cl s w ≤ s.length ∧ cl s w ≤ w.length := by
  induction s with
  | nil => intro w; simp [cl_nil_left]
  | cons y s ih =>
    intro w
    cases w with
    | nil => simp [cl_nil_right]
    | cons x w =>
      rw [cl_cons_cons]
      by_cases hc : y.1 = x.1 ∧ y.2 = !x.2
      · rw [ite_of_pos hc]
        have := ih w
        simp only [List.length_cons]
        omega
      · rw [ite_of_neg hc]
        simp

theorem cl_head_zero [DecidableEq P] {x : P × Bool} {w : FGWord P} (hw : Red (x :: w))
    (s : FGWord P) : cl (x :: s) w = 0 := by
  cases w with
  | nil => exact cl_nil_right _
  | cons z w =>
    rw [red_cons_cons] at hw
    rw [cl_cons_cons, ite_of_neg (show ¬ (x.1 = z.1 ∧ x.2 = !z.2) from hw.1)]

theorem foldl_cl [DecidableEq P] (w : FGWord P) (hw : Red w) :
    ∀ (s : FGWord P), Red s →
      w.foldl push s = (w.drop (cl s w)).reverse ++ s.drop (cl s w) := by
  induction w with
  | nil => intro s _; simp [cl_nil_right]
  | cons x w ih =>
    intro s hs
    have hw' := red_tail hw
    cases s with
    | nil =>
      rw [List.foldl_cons]
      show w.foldl push [x] = _
      rw [ih hw' [x] (red_single x), cl_head_zero hw, cl_nil_left]
      simp
    | cons y s' =>
      by_cases hc : Canc y x
      · rw [List.foldl_cons, push_cons_of_canc hc, ih hw' s' (red_tail hs), cl_cons_cons,
          ite_of_pos (show y.1 = x.1 ∧ y.2 = !x.2 from hc)]
        simp
      · rw [List.foldl_cons, push_cons_of_not hc]
        have hs2 : Red (x :: y :: s') := red_cons_cons.2 ⟨fun h => hc (canc_symm h), hs⟩
        rw [ih hw' _ hs2, cl_head_zero hw, cl_cons_cons,
          ite_of_neg (show ¬ (y.1 = x.1 ∧ y.2 = !x.2) from hc)]
        simp

theorem cl_append_eq [DecidableEq P] (q m p : FGWord P) :
    ∀ (w : FGWord P), cl (q ++ m) w < q.length → cl (q ++ p) w = cl (q ++ m) w := by
  induction q with
  | nil => intro w h; simp at h
  | cons y q ih =>
    intro w h
    cases w with
    | nil => simp [cl_nil_right]
    | cons x w =>
      simp only [List.cons_append, cl_cons_cons] at h ⊢
      by_cases hc : y.1 = x.1 ∧ y.2 = !x.2
      · rw [ite_of_pos hc] at h ⊢
        rw [ite_of_pos hc, ih w (by simp only [List.length_cons] at h; omega)]
      · rw [ite_of_neg hc, ite_of_neg hc]

/-! ### Pentus's lemma: the inductive invariant -/

private theorem pentus_aux [DecidableEq P] (rest : List (FGWord P)) :
    ∀ (X u : FGWord P),
      (∃ q p m : FGWord P, stk X = q ++ p ∧ stk u = q ++ m ∧ (stk u).length ≤ 2 * q.length) →
      (∀ (l r : List (FGWord P)) (a b : FGWord P), u :: rest = l ++ a :: b :: r →
          max (norm a) (norm b) < norm (a ++ b)) →
      (rest = [] → 0 < (stk u).length) →
      0 < (stk (X ++ rest.flatten)).length := by
  induction rest with
  | nil =>
    intro X u ⟨q, p, m, hX, hu, hl⟩ _ hpos
    have := hpos rfl
    simp only [List.flatten_nil, List.append_nil, hX, List.length_append]
    omega
  | cons v rest ih =>
    intro X u ⟨q, p, m, hX, hu, hl⟩ hbad _
    have huv := hbad [] rest u v rfl
    obtain ⟨b, hbdef⟩ : ∃ b, b = (stk v).reverse := ⟨_, rfl⟩
    have hb : Red b := hbdef ▸ red_reverse (red_stk v)
    have hvb : stk v = b.reverse := by rw [hbdef, List.reverse_reverse]
    have e1 : stk (u ++ v) = (b.drop (cl (stk u) b)).reverse ++ (stk u).drop (cl (stk u) b) := by
      rw [stk_append, foldl_stk_reverse (red_stk u), ← hbdef, foldl_cl b hb _ (red_stk u)]
    have e2 : stk (X ++ v) = (b.drop (cl (stk X) b)).reverse ++ (stk X).drop (cl (stk X) b) := by
      rw [stk_append, foldl_stk_reverse (red_stk X), ← hbdef, foldl_cl b hb _ (red_stk X)]
    rw [norm_eq_len, norm_eq_len, norm_eq_len, e1, hvb] at huv
    have hk := cl_le (stk u) b
    have hmax1 := Nat.le_max_left (stk u).length b.reverse.length
    have hmax2 := Nat.le_max_right (stk u).length b.reverse.length
    simp only [List.length_append, List.length_reverse, List.length_drop] at huv hmax1 hmax2
    have hk1 : 2 * cl (stk u) b < b.length := by omega
    have hk2 : 2 * cl (stk u) b < (stk u).length := by omega
    have hkq : cl (q ++ m) b < q.length := by
      rw [hu] at hk2 hl; omega
    have hk : cl (stk X) b = cl (stk u) b := by
      rw [hX, hu]; exact cl_append_eq q m p b hkq
    rw [hk] at e2
    have := ih (X ++ v) v
      ⟨(b.drop (cl (stk u) b)).reverse, (stk X).drop (cl (stk u) b),
        (b.take (cl (stk u) b)).reverse, e2,
        by rw [hvb, ← List.reverse_append, List.take_append_drop],
        by simp only [hvb, List.length_reverse, List.length_drop]; omega⟩
      (fun l r a b' e => hbad (u :: l) r a b' (by rw [e]; rfl))
      (fun _ => by rw [hvb, List.length_reverse]; omega)
    simpa [List.append_assoc] using this

/-! ### Lengths and generators -/

theorem length_push_le [DecidableEq P] (s : FGWord P) (x : P × Bool) :
    (push s x).length ≤ s.length + 1 := by
  cases s with
  | nil => simp [push]
  | cons y s =>
    by_cases hc : Canc y x
    · rw [push_cons_of_canc hc]; simp only [List.length_cons]; omega
    · rw [push_cons_of_not hc]; simp

theorem length_foldl_push_le [DecidableEq P] (w : FGWord P) :
    ∀ (s : FGWord P), (w.foldl push s).length ≤ s.length + w.length := by
  induction w with
  | nil => intro s; simp
  | cons x w ih =>
    intro s
    have h1 := ih (push s x)
    have h2 := length_push_le s x
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem norm_le_length [DecidableEq P] (w : FGWord P) : norm w ≤ w.length := by
  rw [norm_eq_len]
  have := length_foldl_push_le w []
  simpa [stk] using this

theorem count_fst_inv [DecidableEq P] (p : P) (w : FGWord P) :
    ((inv w).map Prod.fst).count p = (w.map Prod.fst).count p := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [inv_cons]
    simp [List.count_append, List.count_cons, ih]

theorem red_of_count [DecidableEq P] {w : FGWord P}
    (h : ∀ p : P, (w.map Prod.fst).count p ≤ 1) : Red w := by
  intro l₁ l₂ x y e hc
  have := h x.1
  rw [e] at this
  simp [List.count_append, hc.1] at this
  omega

theorem stk_of_red [DecidableEq P] {w : FGWord P} (h : Red w) : stk w = w.reverse := by
  have := stk_reverse_of_red (red_reverse h)
  rwa [List.reverse_reverse] at this

/-- The norm of a word is the norm of its inverse. -/
theorem norm_inv [DecidableEq P] (w : FGWord P) : norm (inv w) = norm w := by
  rw [norm_eq_len, norm_eq_len, stk_inv, length_inv]

/-- Words with the same reduced form have the same norm. -/
theorem norm_eq_of_reduce_eq [DecidableEq P] {u v : FGWord P} (h : reduce u = reduce v) :
    norm u = norm v := by
  unfold norm; rw [h]

/-- If `u` and `v` have the same reduced form, then `u · v⁻¹` reduces to the empty word. -/
theorem reduce_append_inv_eq_nil [DecidableEq P] {u v : FGWord P} (h : reduce u = reduce v) :
    reduce (u ++ inv v) = [] := by
  have h' : stk u = stk v := reduce_eq_iff.1 h
  rw [reduce_eq_stk, stk_append_left, h', ← stk_append_left, stk_append_inv]
  rfl

/-- If `a · b` reduces to the empty word, then `a` and `b` have the same norm. -/
theorem norm_eq_of_reduce_append_eq_nil [DecidableEq P] {a b : FGWord P}
    (h : reduce (a ++ b) = []) : norm a = norm b := by
  have h0 : stk (a ++ b) = [] := by
    rw [reduce_eq_stk, List.reverse_eq_nil_iff] at h; exact h
  have hb : stk b = stk (inv a) := by
    calc stk b = stk (inv a ++ a ++ b) := by
          rw [stk_append_left (inv a ++ a), stk_inv_append]; rfl
      _ = stk (inv a) := by
          rw [List.append_assoc, stk_append_of_nil _ h0]
  rw [norm_eq_len b, hb, ← norm_eq_len, norm_inv]

/-- If `a · b · c` reduces to the empty word, then `b` has the same reduced form as
    `a⁻¹ · c⁻¹`, hence the same norm as `c · a`. -/
theorem norm_mid_eq_of_reduce_eq_nil [DecidableEq P] {a b c : FGWord P}
    (h : reduce (a ++ b ++ c) = []) : norm b = norm (c ++ a) := by
  have h0 : stk (a ++ (b ++ c)) = [] := by
    rw [reduce_eq_stk, List.reverse_eq_nil_iff, List.append_assoc] at h; exact h
  -- `b · c` has the reduced form of `a⁻¹`, so `b · c · a` reduces to the empty word.
  have hbc : stk (b ++ c) = stk (inv a) := by
    calc stk (b ++ c) = stk (inv a ++ a ++ (b ++ c)) := by
          rw [stk_append_left (inv a ++ a), stk_inv_append]; rfl
      _ = stk (inv a) := by
          rw [List.append_assoc, stk_append_of_nil _ h0]
  have h1 : stk (b ++ (c ++ a)) = [] := by
    rw [← List.append_assoc, stk_append_left, hbc, ← stk_append_left, stk_inv_append]
  apply norm_eq_of_reduce_append_eq_nil
  rw [reduce_eq_stk, h1]; rfl

/-- **Pentus's lemma.** If a product of at least two words reduces to the empty word,
    then some two adjacent factors `u`, `v` satisfy `|u v| ≤ max(|u|, |v|)`. -/
theorem pentus_lemma [DecidableEq P] (us : List (FGWord P)) (hlen : 2 ≤ us.length)
    (h : reduce us.flatten = []) :
    ∃ (l r : List (FGWord P)) (u v : FGWord P),
      us = l ++ u :: v :: r ∧ norm (u ++ v) ≤ max (norm u) (norm v) := by
  classical
  obtain ⟨u, v, rest, rfl⟩ : ∃ u v rest, us = u :: v :: rest := by
    match us, hlen with
    | [], h => simp at h
    | [_], h => simp at h
    | u :: v :: rest, _ => exact ⟨u, v, rest, rfl⟩
  refine Classical.byContradiction fun hne => ?_
  have hbad : ∀ (l r : List (FGWord P)) (a b : FGWord P), u :: v :: rest = l ++ a :: b :: r →
      max (norm a) (norm b) < norm (a ++ b) := by
    intro l r a b e
    exact Nat.lt_of_not_le (fun hle => hne ⟨l, r, a, b, e, hle⟩)
  have hpos := pentus_aux (v :: rest) u u
    ⟨stk u, [], [], by simp, by simp, by omega⟩ hbad (fun h => nomatch h)
  have h0 : stk (u :: v :: rest).flatten = [] := by
    rw [reduce_eq_stk, List.reverse_eq_nil_iff] at h; exact h
  rw [List.flatten_cons] at h0
  rw [h0] at hpos
  simp at hpos

end FGWord

private theorem interpList_nil : interpList ([] : List (LType P)) = [] := rfl

private theorem interpList_cons (A : LType P) (Γ : List (LType P)) :
    interpList (A :: Γ) = A.interp ++ interpList Γ := by
  simp [interpList]

private theorem interpList_append (Γ Δ : List (LType P)) :
    interpList (Γ ++ Δ) = interpList Γ ++ interpList Δ := by
  simp [interpList]

private theorem interp_sound_stk [DecidableEq P] {Γ : List (LType P)} {C : LType P}
    (h : LDer0 Γ C) : FGWord.stk (interpList Γ) = FGWord.stk C.interp := by
  induction h with
  | ax p => simp [interpList_cons, interpList_nil]
  | @overR Γ A B _ _ ih =>
    rw [interpList_append, interpList_cons, interpList_nil, List.append_nil] at ih
    simp only [LType.interp]
    calc FGWord.stk (interpList Γ)
        = FGWord.stk (interpList Γ ++ (B.interp ++ (FGWord.inv B.interp ++ []))) := by
          rw [FGWord.stk_cancel_inv_right, List.append_nil]
      _ = FGWord.stk (A.interp ++ FGWord.inv B.interp) := by
          rw [List.append_nil, ← List.append_assoc]
          exact FGWord.stk_congr ih rfl
  | @underR Γ A B _ _ ih =>
    rw [interpList_cons] at ih
    simp only [LType.interp]
    calc FGWord.stk (interpList Γ)
        = FGWord.stk ([] ++ (FGWord.inv B.interp ++ (B.interp ++ interpList Γ))) := by
          rw [FGWord.stk_cancel_inv_left, List.nil_append]
      _ = FGWord.stk (FGWord.inv B.interp ++ A.interp) := by
          rw [List.nil_append]
          exact FGWord.stk_congr rfl ih
  | @overL Γ Δ Θ A B C _ _ ih1 ih2 =>
    simp only [interpList_append, interpList_cons, interpList_nil, List.append_nil,
      LType.interp, List.append_assoc] at ih2 ⊢
    rw [← ih2]
    calc FGWord.stk (interpList Γ ++ (A.interp ++ (FGWord.inv B.interp ++
            (interpList Θ ++ interpList Δ))))
        = FGWord.stk ((interpList Γ ++ (A.interp ++ FGWord.inv B.interp)) ++
            (interpList Θ ++ interpList Δ)) := by simp only [List.append_assoc]
      _ = FGWord.stk ((interpList Γ ++ (A.interp ++ FGWord.inv B.interp)) ++
            (B.interp ++ interpList Δ)) := FGWord.stk_congr rfl (FGWord.stk_congr ih1 rfl)
      _ = FGWord.stk ((interpList Γ ++ A.interp) ++ (FGWord.inv B.interp ++
            (B.interp ++ interpList Δ))) := by simp only [List.append_assoc]
      _ = FGWord.stk (interpList Γ ++ (A.interp ++ interpList Δ)) := by
          rw [FGWord.stk_cancel_inv_left, List.append_assoc]
  | @underL Γ Δ Θ A B C _ _ ih1 ih2 =>
    simp only [interpList_append, interpList_cons, interpList_nil, List.append_nil,
      LType.interp, List.append_assoc] at ih2 ⊢
    rw [← ih2]
    calc FGWord.stk (interpList Γ ++ (interpList Θ ++ (FGWord.inv B.interp ++
            (A.interp ++ interpList Δ))))
        = FGWord.stk (interpList Γ ++ (B.interp ++ (FGWord.inv B.interp ++
            (A.interp ++ interpList Δ)))) :=
          FGWord.stk_congr rfl (FGWord.stk_congr ih1 rfl)
      _ = FGWord.stk (interpList Γ ++ (A.interp ++ interpList Δ)) :=
          FGWord.stk_cancel_inv_right _ _ _
  | @mulR Γ Δ A B _ _ ih1 ih2 =>
    rw [interpList_append]
    exact FGWord.stk_congr ih1 ih2
  | @mulL Γ Δ A B C _ ih =>
    simp only [interpList_append, interpList_cons, interpList_nil, List.append_nil,
      LType.interp, List.append_assoc] at ih ⊢
    exact ih

private theorem length_interp (A : LType P) : A.interp.length = A.size := by
  induction A with
  | prim p => rfl
  | over A B ihA ihB =>
    simp only [LType.interp, LType.size, List.length_append, FGWord.length_inv, ihA, ihB]
  | under B A ihB ihA =>
    simp only [LType.interp, LType.size, List.length_append, FGWord.length_inv, ihA, ihB]
  | mul A B ihA ihB =>
    simp only [LType.interp, LType.size, List.length_append, ihA, ihB]

private theorem count_interp [DecidableEq P] (p : P) (A : LType P) :
    (A.interp.map Prod.fst).count p = A.occ p := by
  induction A with
  | prim q =>
    simp only [LType.interp, LType.occ, List.map_cons, List.map_nil, List.count_cons,
      List.count_nil, beq_iff_eq]
    split <;> simp
  | over A B ihA ihB =>
    simp only [LType.interp, LType.occ, List.map_append, List.count_append,
      FGWord.count_fst_inv, ihA, ihB]
  | under B A ihB ihA =>
    simp only [LType.interp, LType.occ, List.map_append, List.count_append,
      FGWord.count_fst_inv, ihA, ihB]
  | mul A B ihA ihB =>
    simp only [LType.interp, LType.occ, List.map_append, List.count_append, ihA, ihB]

/-- Soundness of the free-group interpretation: a derivable sequent has equal
    interpretations on both sides. -/
theorem LDer0.interp_sound [DecidableEq P] {Γ : List (LType P)} {C : LType P}
    (h : LDer0 Γ C) : FGWord.reduce (interpList Γ) = FGWord.reduce C.interp :=
  FGWord.reduce_eq_iff.2 (interp_sound_stk h)

/-- The norm of the interpretation of a type is at most its size. -/
theorem LType.norm_interp_le [DecidableEq P] (A : LType P) :
    FGWord.norm A.interp ≤ A.size := by
  have := FGWord.norm_le_length A.interp
  rwa [length_interp] at this

/-- If every primitive type occurs at most once in `A`, the interpretation of `A` is
    already reduced, so its norm equals the size of `A`. -/
theorem LType.norm_interp_eq_size [DecidableEq P] (A : LType P)
    (h : ∀ p : P, A.occ p ≤ 1) : FGWord.norm A.interp = A.size := by
  have hr : FGWord.Red A.interp :=
    FGWord.red_of_count (fun p => by rw [count_interp]; exact h p)
  rw [FGWord.norm_eq_len, FGWord.stk_of_red hr, List.length_reverse, length_interp]

end FormalLinguistics
