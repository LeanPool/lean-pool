/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Orbit
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Popcount
public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Sym

/-!
# The sides of the associativity conditions as tables

For an assignment `α` of the high variables, every class code is false, true or a low variable
(`kindOf`), and the two sides of the condition of a quadruple become tables in the truth-table
columns `pat b j` of the low variables (`dotD`, `Problem.dotRL`, `Problem.dotRR`), with the
constants represented by sentinels. `Problem.quadD_spec` relates them to the condition.

A side only depends on the high variables of the terms that can contribute to it
(`Problem.coversQuad`, `Problem.dotR_land`). This is what the evaluator of
`Solution/Cert/Elim.lean` builds on; the functions of this file are used directly to recognise
leaves that vanish because the two sides of a condition are opposite constants
(`Problem.deadR`).
-/

@[expose] public section

namespace RACert

/-- The kind of a class code when the high variables are given by `α`: `0` (false), `1` (true), or
`j + 2` for the low variable `j < b`. -/
noncomputable def kindOf (b α c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun m _ => Nat.rec (motive := fun _ => ℕ) 1
      (fun j _ => bif Nat.blt j b then Nat.add j 2
        else Nat.land (Nat.shiftRight α (Nat.sub j b)) 1) m) c

theorem kindOf_low {b α j : ℕ} (hj : j < b) : kindOf b α (j + 2) = j + 2 := by
  have h : Nat.blt j b = true := by rw [Nat.blt_eq]; exact hj
  change (bif Nat.blt j b then Nat.add j 2 else _) = _
  rw [h]
  rfl

theorem land_shiftRight_one (α n : ℕ) :
    Nat.land (Nat.shiftRight α n) 1 = if α.testBit n = true then 1 else 0 := by
  change (α >>> n) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (α / 2 ^ n) with h | h <;> simp [h]

theorem kindOf_high {b α j : ℕ} (hj : ¬ j < b) :
    kindOf b α (j + 2) = if α.testBit (j - b) = true then 1 else 0 := by
  have h : Nat.blt j b = false := by rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; exact hj
  change (bif Nat.blt j b then Nat.add j 2 else Nat.land (Nat.shiftRight α (Nat.sub j b)) 1) = _
  rw [h]
  exact land_shiftRight_one α (j - b)

/-- The three possible kinds of a class code, with their meaning. -/
theorem kindOf_cases (b α β c : ℕ) :
    (kindOf b α c = 0 ∧ litB (joinN b α β) c = false) ∨
      (kindOf b α c = 1 ∧ litB (joinN b α β) c = true) ∨
      ∃ j < b, kindOf b α c = j + 2 ∧ litB (joinN b α β) c = β.testBit j := by
  match c with
  | 0 => exact Or.inl ⟨rfl, rfl⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | j + 2 =>
    by_cases hj : j < b
    · exact Or.inr (Or.inr ⟨j, hj, kindOf_low hj, by simp [litB, joinN, hj]⟩)
    · rw [kindOf_high hj]
      cases hbit : α.testBit (j - b)
      · exact Or.inl ⟨by simp, by simp [litB, joinN, hj, hbit]⟩
      · exact Or.inr (Or.inl ⟨by simp, by simp [litB, joinN, hj, hbit]⟩)

/-- Disjunction of a table into an accumulator which is `0` or a table. -/
noncomputable def orS (acc t : ℕ) : ℕ := bif Nat.beq acc 0 then t else Nat.lor acc t

/-- Conjunction of two low variables, in a canonical order. -/
noncomputable def andS (b i j : ℕ) : ℕ :=
  bif Nat.ble i j then Nat.land (pat b i) (pat b j) else Nat.land (pat b j) (pat b i)

theorem orS_spec {b acc t : ℕ} (hacc : acc < top b) (ht : t < top b) (β : ℕ) :
    orS acc t < top b ∧ (orS acc t).testBit β = (acc.testBit β || t.testBit β) := by
  unfold orS
  by_cases h0 : acc = 0
  · rw [beq_true h0, h0]
    exact ⟨ht, by simp⟩
  · rw [beq_false h0]
    exact ⟨lor_lt hacc ht, testBit_lor _ _ _⟩

theorem andS_spec {b i j β : ℕ} (hi : i < b) (hj : j < b) (hβ : β < 2 ^ b) :
    andS b i j < top b ∧ (andS b i j).testBit β = (β.testBit i && β.testBit j) := by
  have e1 : (pat b i).testBit β = β.testBit i := by rw [testBit_pat hi]; simp [hβ]
  have e2 : (pat b j).testBit β = β.testBit j := by rw [testBit_pat hj]; simp [hβ]
  unfold andS
  cases Nat.ble i j
  · exact ⟨land_lt (pat_lt b i), by
      change (Nat.land (pat b j) (pat b i)).testBit β = _
      rw [testBit_land, e1, e2, Bool.and_comm]⟩
  · exact ⟨land_lt (pat_lt b j), by
      change (Nat.land (pat b i) (pat b j)).testBit β = _
      rw [testBit_land, e1, e2]⟩

theorem pat_spec {b j β : ℕ} (hj : j < b) (hβ : β < 2 ^ b) :
    pat b j < top b ∧ (pat b j).testBit β = β.testBit j :=
  ⟨pat_lt b j, by rw [testBit_pat hj]; simp [hβ]⟩

/-- One step of a disjunction of conjunctions: add the conjunction of the kinds `x` and `y` to the
accumulator `acc` and pass the result to the continuation. -/
noncomputable def stepK (T b x y acc : ℕ) (k : ℕ → ℕ) : ℕ :=
  bif Nat.beq acc T then k T
  else
    Nat.rec (motive := fun _ => ℕ) (k acc)
      (fun x' _ => Nat.rec (motive := fun _ => ℕ)
        (Nat.rec (motive := fun _ => ℕ) (k acc)
          (fun y' _ => Nat.rec (motive := fun _ => ℕ) (k T)
            (fun j _ => k (orS acc (pat b j))) y') y)
        (fun i _ => Nat.rec (motive := fun _ => ℕ) (k acc)
          (fun y' _ => Nat.rec (motive := fun _ => ℕ) (k (orS acc (pat b i)))
            (fun j _ => k (orS acc (andS b i j))) y') y) x') x

/-- The value passed on by `stepK`. -/
noncomputable def stepD (T b x y acc : ℕ) : ℕ := stepK T b x y acc id

theorem stepK_eq (T b x y acc : ℕ) (k : ℕ → ℕ) : stepK T b x y acc k = k (stepD T b x y acc) := by
  unfold stepD stepK
  cases Nat.beq acc T
  · match x, y with
    | 0, _ => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 1, _ + 2 => rfl
    | _ + 2, 0 => rfl
    | _ + 2, 1 => rfl
    | _ + 2, _ + 2 => rfl
  · rfl

theorem stepD_top {T b x y acc : ℕ} (h : acc = T) : stepD T b x y acc = T := by
  unfold stepD stepK
  rw [beq_true h]
  rfl

section StepD

variable {T b acc : ℕ} (h : acc ≠ T)
include h

theorem stepD_zero (y : ℕ) : stepD T b 0 y acc = acc := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_one_zero : stepD T b 1 0 acc = acc := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_one_one : stepD T b 1 1 acc = T := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_one_var (j : ℕ) : stepD T b 1 (j + 2) acc = orS acc (pat b j) := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_var_zero (i : ℕ) : stepD T b (i + 2) 0 acc = acc := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_var_one (i : ℕ) : stepD T b (i + 2) 1 acc = orS acc (pat b i) := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

theorem stepD_var_var (i j : ℕ) : stepD T b (i + 2) (j + 2) acc = orS acc (andS b i j) := by
  unfold stepD stepK
  rw [beq_false h]
  rfl

end StepD

theorem stepD_spec {b α β c c' acc : ℕ} (hβ : β < 2 ^ b) (hacc : acc ≤ top b) :
    stepD (top b) b (kindOf b α c) (kindOf b α c') acc ≤ top b ∧
      sem (top b) (stepD (top b) b (kindOf b α c) (kindOf b α c') acc) β =
        (sem (top b) acc β || (litB (joinN b α β) c && litB (joinN b α β) c')) := by
  by_cases hT : acc = top b
  · rw [stepD_top hT, sem_top, hT, sem_top]
    exact ⟨le_refl _, rfl⟩
  have hlt : acc < top b := lt_of_le_of_ne hacc hT
  have hsem : sem (top b) acc β = acc.testBit β := sem_of_ne hT β
  have key : ∀ {t : ℕ}, t < top b →
      orS acc t ≤ top b ∧ sem (top b) (orS acc t) β = (sem (top b) acc β || t.testBit β) := by
    intro t ht
    obtain ⟨h1, h2⟩ := orS_spec hlt ht β
    exact ⟨h1.le, by rw [sem_of_ne h1.ne, h2, hsem]⟩
  rcases kindOf_cases b α β c with ⟨e, l⟩ | ⟨e, l⟩ | ⟨i, hi, e, l⟩ <;> rw [e, l]
  · rw [stepD_zero hT]
    exact ⟨hacc, by simp⟩
  · rcases kindOf_cases b α β c' with ⟨e', l'⟩ | ⟨e', l'⟩ | ⟨j, hj, e', l'⟩ <;> rw [e', l']
    · rw [stepD_one_zero hT]
      exact ⟨hacc, by simp⟩
    · rw [stepD_one_one hT, sem_top]
      exact ⟨le_refl _, by simp⟩
    · rw [stepD_one_var hT]
      obtain ⟨p1, p2⟩ := pat_spec hj hβ
      obtain ⟨h1, h2⟩ := key p1
      exact ⟨h1, by rw [h2, p2, Bool.true_and]⟩
  · rcases kindOf_cases b α β c' with ⟨e', l'⟩ | ⟨e', l'⟩ | ⟨j, hj, e', l'⟩ <;> rw [e', l']
    · rw [stepD_var_zero hT]
      exact ⟨hacc, by simp⟩
    · rw [stepD_var_one hT]
      obtain ⟨p1, p2⟩ := pat_spec hi hβ
      obtain ⟨h1, h2⟩ := key p1
      exact ⟨h1, by rw [h2, p2, Bool.and_true]⟩
    · rw [stepD_var_var hT]
      obtain ⟨p1, p2⟩ := andS_spec hi hj hβ
      obtain ⟨h1, h2⟩ := key p1
      exact ⟨h1, by rw [h2, p2]⟩

/-- `acc ∨ ⋁ q, l1[q] ∧ l2[q]` on lists of kinds, in continuation-passing style. -/
noncomputable def dotK (T b : ℕ) (l1 : List ℕ) : List ℕ → ℕ → (ℕ → ℕ) → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ → (ℕ → ℕ) → ℕ) (fun _ acc k => k acc)
    (fun x _ ih l2 acc k =>
      List.rec (motive := fun _ => ℕ) (k acc)
        (fun y ys _ => stepK T b x y acc (fun acc' => ih ys acc' k)) l2) l1

/-- The value passed on by `dotK`. -/
noncomputable def dotD (T b : ℕ) (l1 l2 : List ℕ) (acc : ℕ) : ℕ := dotK T b l1 l2 acc id

theorem dotK_cons_cons (T b x y : ℕ) (xs ys : List ℕ) (acc : ℕ) (k : ℕ → ℕ) :
    dotK T b (x :: xs) (y :: ys) acc k = stepK T b x y acc (fun acc' => dotK T b xs ys acc' k) :=
  rfl

theorem dotK_eq (T b : ℕ) (l1 l2 : List ℕ) (acc : ℕ) (k : ℕ → ℕ) :
    dotK T b l1 l2 acc k = k (dotD T b l1 l2 acc) := by
  induction l1 generalizing l2 acc k with
  | nil => rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      unfold dotD
      rw [dotK_cons_cons, dotK_cons_cons, stepK_eq, stepK_eq, ih, ih ys _ id]
      rfl

theorem dotD_nil (T b : ℕ) (l2 : List ℕ) (acc : ℕ) : dotD T b [] l2 acc = acc := rfl

theorem dotD_cons_nil (T b x : ℕ) (xs : List ℕ) (acc : ℕ) : dotD T b (x :: xs) [] acc = acc := rfl

theorem dotD_cons_cons (T b x y : ℕ) (xs ys : List ℕ) (acc : ℕ) :
    dotD T b (x :: xs) (y :: ys) acc = dotD T b xs ys (stepD T b x y acc) := by
  unfold dotD
  rw [dotK_cons_cons, stepK_eq, dotK_eq]

theorem dotD_spec {b α β : ℕ} (hβ : β < 2 ^ b) (c1 c2 : List ℕ) {acc : ℕ} (hacc : acc ≤ top b) :
    dotD (top b) b (c1.map (kindOf b α)) (c2.map (kindOf b α)) acc ≤ top b ∧
      sem (top b) (dotD (top b) b (c1.map (kindOf b α)) (c2.map (kindOf b α)) acc) β =
        (sem (top b) acc β ||
          (c1.zip c2).any fun p => litB (joinN b α β) p.1 && litB (joinN b α β) p.2) := by
  induction c1 generalizing c2 acc with
  | nil => simp [dotD_nil, hacc]
  | cons i c1 ih =>
    cases c2 with
    | nil => simp [dotD_cons_nil, hacc]
    | cons j c2 =>
      obtain ⟨h1, h2⟩ := stepD_spec (α := α) (c := i) (c' := j) hβ hacc
      obtain ⟨g1, g2⟩ := ih c2 h1
      rw [List.map_cons, List.map_cons, dotD_cons_cons]
      refine ⟨g1, ?_⟩
      rw [g2, h2, List.zip_cons_cons, List.any_cons, Bool.or_assoc]

/-- The kinds of all triples. -/
noncomputable def krowsOf (b α : ℕ) (cls : List (List (List ℕ))) : List (List (List ℕ)) :=
  map' (map' (map' (kindOf b α))) cls

theorem rowAt_krowsOf (b α : ℕ) (cls : List (List (List ℕ))) (a c : ℕ) :
    rowAt (krowsOf b α cls) a c = (nth [] (nth [] cls a) c).map (kindOf b α) := by
  have e : krowsOf b α cls = cls.map (List.map (List.map (kindOf b α))) := by
    unfold krowsOf
    rw [map'_eq]
    congr 1
    funext l
    rw [map'_eq]
    congr 1
    funext l'
    rw [map'_eq]
  rw [rowAt, e]
  have h1 := nth_map (List.map (List.map (kindOf b α))) [] cls a
  rw [List.map_nil] at h1
  rw [h1]
  have h2 := nth_map (List.map (kindOf b α)) [] (nth [] cls a) c
  rw [List.map_nil] at h2
  exact h2

/-- Inequality of two values which are tables or constants; the result is a plain bit mask. -/
noncomputable def neqS (T on L R : ℕ) : ℕ :=
  bif Nat.beq L T then (bif Nat.beq R T then 0 else Nat.xor on R)
  else bif Nat.beq R T then Nat.xor on L
  else bif Nat.beq L R then 0
  else bif Nat.ble L R then Nat.xor L R else Nat.xor R L

/-- Accumulate a mask of violations. -/
noncomputable def badS (bad q : ℕ) : ℕ :=
  bif Nat.beq q 0 then bad else bif Nat.beq bad 0 then q else Nat.lor bad q

theorem neqS_spec {b L R β : ℕ} (hL : L ≤ top b) (hR : R ≤ top b) (hβ : β < 2 ^ b) :
    neqS (top b) (ones b) L R < top b ∧
      (neqS (top b) (ones b) L R).testBit β = (sem (top b) L β ^^ sem (top b) R β) := by
  have hT := top_pos b
  have ho : ones b < 2 ^ 2 ^ b := ones_lt b
  have hob : (ones b).testBit β = true := by rw [testBit_ones]; simpa using hβ
  unfold neqS
  by_cases hLT : L = top b
  · rw [beq_true hLT]
    by_cases hRT : R = top b
    · rw [beq_true hRT, hLT, hRT, sem_top]
      exact ⟨hT, by simp⟩
    · rw [beq_false hRT, hLT, sem_top, sem_of_ne hRT]
      have hR' : R < 2 ^ 2 ^ b := lt_of_le_of_ne hR hRT
      simp only [Bool.cond_true, Bool.cond_false]
      exact ⟨xor_lt ho hR', by rw [testBit_xor, hob]⟩
  · rw [beq_false hLT]
    have hL' : L < 2 ^ 2 ^ b := lt_of_le_of_ne hL hLT
    by_cases hRT : R = top b
    · rw [beq_true hRT, hRT, sem_top, sem_of_ne hLT]
      simp only [Bool.cond_true, Bool.cond_false]
      exact ⟨xor_lt ho hL', by rw [testBit_xor, hob, Bool.xor_comm]⟩
    · rw [beq_false hRT, sem_of_ne hLT, sem_of_ne hRT]
      have hR' : R < 2 ^ 2 ^ b := lt_of_le_of_ne hR hRT
      by_cases hLR : L = R
      · rw [beq_true hLR, hLR]
        exact ⟨hT, by simp⟩
      · rw [beq_false hLR]
        cases Nat.ble L R
        · simp only [Bool.cond_false]
          exact ⟨xor_lt hR' hL', by rw [testBit_xor, Bool.xor_comm]⟩
        · simp only [Bool.cond_true, Bool.cond_false]
          exact ⟨xor_lt hL' hR', by rw [testBit_xor]⟩

theorem badS_spec {b bad q : ℕ} (hbad : bad < top b) (hq : q < top b) (β : ℕ) :
    badS bad q < top b ∧ (badS bad q).testBit β = (bad.testBit β || q.testBit β) := by
  unfold badS
  by_cases hq0 : q = 0
  · rw [beq_true hq0, hq0]
    exact ⟨hbad, by simp⟩
  · rw [beq_false hq0]
    by_cases hb0 : bad = 0
    · rw [beq_true hb0, hb0]
      exact ⟨hq, by simp⟩
    · rw [beq_false hb0]
      exact ⟨lor_lt hbad hq, testBit_lor _ _ _⟩

namespace Problem

variable (P : Problem)

/-- Add the violations of the quadruple `(r, u, t, p)` to `bad`. -/
noncomputable def quadD4 (T on b : ℕ) (krows : List (List (List ℕ))) (r u t p bad : ℕ) : ℕ :=
  badS bad (neqS T on (dotD T b (rowAt krows (cvN P.s r) p) (rowAt krows u t) 0)
    (dotD T b (rowAt krows r u) (rowAt krows p (cvN P.s t)) 0))

/-- Add the violations of the quadruple with code `x` to `bad`. -/
noncomputable def quadD (T on b : ℕ) (krows : List (List (List ℕ))) (x bad : ℕ) : ℕ :=
  P.quadD4 T on b krows (P.quadFirst x) (P.quadSecond x) (P.quadThird x)
    (P.quadFourth x) bad

variable {P}

theorem dotD_rows_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b)
    {a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < P.k) (hb₁ : b₁ < P.k) (ha₂ : a₂ < P.k) (hb₂ : b₂ < P.k) :
    dotD (top b) b (rowAt (krowsOf b α P.cls) a₁ b₁) (rowAt (krowsOf b α P.cls) a₂ b₂) 0 ≤ top b ∧
      sem (top b) (dotD (top b) b (rowAt (krowsOf b α P.cls) a₁ b₁)
        (rowAt (krowsOf b α P.cls) a₂ b₂) 0) β =
        dotB P.k (P.tbl (joinN b α β)) a₁ b₁ a₂ b₂ := by
  rw [rowAt_krowsOf, rowAt_krowsOf]
  obtain ⟨h1, h2⟩ := dotD_spec (α := α) hβ (nth [] (nth [] P.cls a₁) b₁)
    (nth [] (nth [] P.cls a₂) b₂) (Nat.zero_le (top b))
  refine ⟨h1, ?_⟩
  rw [h2, sem_zero (top_pos b), Bool.false_or,
    zip_any_eq_range (litB (joinN b α β)) P.k _ _ (checkRows_spec hrows ha₁ hb₁)
      (checkRows_spec hrows ha₂ hb₂)]
  rfl

theorem quadD_spec (hrows : P.checkRows = true) {b α β : ℕ} (hβ : β < 2 ^ b) (x : ℕ) {bad : ℕ}
    (hbad : bad < top b) :
    P.quadD (top b) (ones b) b (krowsOf b α P.cls) x bad < top b ∧
      (P.quadD (top b) (ones b) b (krowsOf b α P.cls) x bad).testBit β =
        (bad.testBit β || !P.quadAt (joinN b α β) x) := by
  have hk := numAtoms_pos P.s P.n
  have hm : ∀ y, y % P.k < P.k := fun y => Nat.mod_lt _ hk
  obtain ⟨hL1, hL2⟩ := dotD_rows_spec hrows (α := α) hβ (cvN_lt (hm (x / P.k / P.k / P.k))) (hm x)
    (hm (x / P.k / P.k)) (hm (x / P.k))
  obtain ⟨hR1, hR2⟩ := dotD_rows_spec hrows (α := α) hβ (hm (x / P.k / P.k / P.k))
    (hm (x / P.k / P.k)) (hm x) (cvN_lt (hm (x / P.k)))
  obtain ⟨h1, h2⟩ := neqS_spec hL1 hR1 hβ
  obtain ⟨g1, g2⟩ := badS_spec hbad h1 β
  rw [quadD, quadD4, quadFirst, quadSecond, quadThird, quadFourth]
  refine ⟨g1, ?_⟩
  rw [g2, h2, hL2, hR2, quadAt, quadB]
  cases dotB P.k (P.tbl (joinN b α β)) (cvN P.s (x / P.k / P.k / P.k % P.k)) (x % P.k)
      (x / P.k / P.k % P.k) (x / P.k % P.k) <;>
    cases dotB P.k (P.tbl (joinN b α β)) (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k)
      (x % P.k) (cvN P.s (x / P.k % P.k)) <;> rfl

end Problem

/-- The class code `c` is not a high variable outside the mask `m`. -/
def cov (b m c : ℕ) : Bool :=
  Nat.blt c (Nat.add b 2) || Nat.testBit m (Nat.sub (Nat.sub c 2) b)

theorem kindOf_land {b α m c : ℕ} (h : cov b m c = true) :
    kindOf b (Nat.land α m) c = kindOf b α c := by
  match c with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
    by_cases hj : j < b
    · rw [kindOf_low hj, kindOf_low hj]
    · have hlt : Nat.blt (j + 2) (Nat.add b 2) = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
        change ¬ j + 2 < b + 2
        omega
      rw [cov, hlt, Bool.false_or] at h
      have h' : m.testBit (j - b) = true := by simpa using h
      rw [kindOf_high hj, kindOf_high hj]
      change (if (α &&& m).testBit (j - b) = true then 1 else 0) = _
      rw [Nat.testBit_and, h', Bool.and_true]

/-- Some term of the disjunction of conjunctions of two rows is constant true. -/
def hasTop : List ℕ → List ℕ → Bool
  | x :: xs, y :: ys => (Nat.beq x 1 && Nat.beq y 1) || hasTop xs ys
  | _, _ => false

/-- Every term of the disjunction of conjunctions of two rows has a vanishing factor, or only
involves high variables selected by the mask `m`. -/
def allCov (b m : ℕ) : List ℕ → List ℕ → Bool
  | x :: xs, y :: ys =>
    (Nat.beq x 0 || (Nat.beq y 0 || (cov b m x && cov b m y))) && allCov b m xs ys
  | _, _ => true

/-- The disjunction of conjunctions of two rows only depends on the high variables selected by
the mask `m`. -/
def coversDot (b m : ℕ) (r₁ r₂ : List ℕ) : Bool := hasTop r₁ r₂ || allCov b m r₁ r₂

theorem dotD_top (T b : ℕ) (l₁ l₂ : List ℕ) : dotD T b l₁ l₂ T = T := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons x xs ih =>
    cases l₂ with
    | nil => rfl
    | cons y ys => rw [dotD_cons_cons, stepD_top rfl, ih]

theorem stepD_left_zero (T b y acc : ℕ) : stepD T b 0 y acc = acc := by
  by_cases h : acc = T
  · rw [stepD_top h, h]
  · exact stepD_zero h y

theorem stepD_right_zero (T b x acc : ℕ) : stepD T b x 0 acc = acc := by
  by_cases h : acc = T
  · rw [stepD_top h, h]
  · match x with
    | 0 => exact stepD_zero h 0
    | 1 => exact stepD_one_zero h
    | i + 2 => exact stepD_var_zero h i

theorem stepD_one_one' (T b acc : ℕ) : stepD T b 1 1 acc = T := by
  by_cases h : acc = T
  · exact stepD_top h
  · exact stepD_one_one h

theorem dotD_of_hasTop {T b : ℕ} (f : ℕ → ℕ) (hf : f 1 = 1) :
    ∀ {l₁ l₂ : List ℕ}, hasTop l₁ l₂ = true → ∀ acc, dotD T b (l₁.map f) (l₂.map f) acc = T
  | x :: xs, y :: ys, h, acc => by
    rw [hasTop, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    rw [List.map_cons, List.map_cons, dotD_cons_cons]
    rcases h with ⟨hx, hy⟩ | h
    · rw [hx, hy, hf, stepD_one_one', dotD_top]
    · exact dotD_of_hasTop f hf h _
  | [], _, h, _ => by simp [hasTop] at h
  | _ :: _, [], h, _ => by simp [hasTop] at h

theorem dotD_of_allCov {T b m α : ℕ} :
    ∀ {l₁ l₂ : List ℕ}, allCov b m l₁ l₂ = true → ∀ acc,
      dotD T b (l₁.map (kindOf b (Nat.land α m))) (l₂.map (kindOf b (Nat.land α m))) acc =
        dotD T b (l₁.map (kindOf b α)) (l₂.map (kindOf b α)) acc
  | x :: xs, y :: ys, h, acc => by
    rw [allCov, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq,
      Nat.beq_eq] at h
    rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, dotD_cons_cons, dotD_cons_cons]
    have hs : stepD T b (kindOf b (Nat.land α m) x) (kindOf b (Nat.land α m) y) acc =
        stepD T b (kindOf b α x) (kindOf b α y) acc := by
      rcases h.1 with hx | hy | ⟨hx, hy⟩
      · rw [hx]
        exact (stepD_left_zero _ _ _ _).trans (stepD_left_zero _ _ _ _).symm
      · rw [hy]
        exact (stepD_right_zero _ _ _ _).trans (stepD_right_zero _ _ _ _).symm
      · rw [kindOf_land hx, kindOf_land hy]
    rw [hs]
    exact dotD_of_allCov h.2 _
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem dotD_land {b m α : ℕ} {l₁ l₂ : List ℕ} (h : coversDot b m l₁ l₂ = true) (acc : ℕ) :
    dotD (top b) b (l₁.map (kindOf b (Nat.land α m))) (l₂.map (kindOf b (Nat.land α m))) acc =
      dotD (top b) b (l₁.map (kindOf b α)) (l₂.map (kindOf b α)) acc := by
  rw [coversDot, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [dotD_of_hasTop _ rfl h, dotD_of_hasTop _ rfl h]
  · exact dotD_of_allCov h acc

/-- Equality of lists of numbers, as a Boolean. -/
def listBeq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && listBeq xs ys
  | _, _ => false

theorem listBeq_eq : ∀ {l₁ l₂ : List ℕ}, listBeq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    rw [listBeq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, listBeq_eq h.2]
  | [], _ :: _, h => by simp [listBeq] at h
  | _ :: _, [], h => by simp [listBeq] at h

namespace Problem

variable (P : Problem)

/-- The left side of the condition of the quadruple with code `x`, the high variables being `r`. -/
noncomputable def dotRL (b x r : ℕ) : ℕ :=
  dotD (top b) b
    (rowAt (krowsOf b r P.cls) (cvN P.s (P.quadFirst x))
      (P.quadFourth x))
    (rowAt (krowsOf b r P.cls) (P.quadSecond x)
      (P.quadThird x)) 0

/-- The right side of the condition of the quadruple with code `x`, the high variables being
`r`. -/
noncomputable def dotRR (b x r : ℕ) : ℕ :=
  dotD (top b) b
    (rowAt (krowsOf b r P.cls) (P.quadFirst x)
      (P.quadSecond x))
    (rowAt (krowsOf b r P.cls) (P.quadFourth x) (cvN P.s (P.quadThird x))) 0

theorem dotRL_eq (b x r : ℕ) : P.dotRL b x r = dotD (top b) b
    (rowAt (krowsOf b r P.cls) (cvN P.s (x / P.k / P.k / P.k % P.k)) (x % P.k))
    (rowAt (krowsOf b r P.cls) (x / P.k / P.k % P.k) (x / P.k % P.k)) 0 := rfl

theorem dotRR_eq (b x r : ℕ) : P.dotRR b x r = dotD (top b) b
    (rowAt (krowsOf b r P.cls) (x / P.k / P.k / P.k % P.k) (x / P.k / P.k % P.k))
    (rowAt (krowsOf b r P.cls) (x % P.k) (cvN P.s (x / P.k % P.k))) 0 := rfl

theorem quadD_eq_dotR (b α x bad : ℕ) :
    P.quadD (top b) (ones b) b (krowsOf b α P.cls) x bad =
      badS bad (neqS (top b) (ones b) (P.dotRL b x α) (P.dotRR b x α)) := rfl

/-- The masks of an entry `(x, m₁, m₂)` select the high variables on which the two sides of the
condition of `x` depend. -/
noncomputable def coversQuad (b : ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  coversDot b e.2.1
      (nth [] (nth [] P.cls
        (cvN P.s (P.quadFirst e.1))) (P.quadFourth e.1))
      (nth [] (nth [] P.cls (P.quadSecond e.1))
        (P.quadThird e.1)) &&
    coversDot b e.2.2
      (nth [] (nth [] P.cls (P.quadFirst e.1))
        (P.quadSecond e.1))
      (nth [] (nth [] P.cls (P.quadFourth e.1)) (cvN P.s (P.quadThird e.1)))

variable {P}

theorem dotR_land {b α : ℕ} {e : ℕ × ℕ × ℕ} (h : P.coversQuad b e = true) :
    P.dotRL b e.1 (Nat.land α e.2.1) = P.dotRL b e.1 α ∧
      P.dotRR b e.1 (Nat.land α e.2.2) = P.dotRR b e.1 α := by
  rw [coversQuad, Bool.and_eq_true] at h
  constructor
  · unfold dotRL
    rw [rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf]
    exact dotD_land h.1 0
  · unfold dotRR
    rw [rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf, rowAt_krowsOf]
    exact dotD_land h.2 0

/-- Reduce a small number and pass it on as a canonical expression (Boolean result). -/
noncomputable def forceB (r : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) r

theorem forceB_eq (r : ℕ) (k : ℕ → Bool) : forceB r k = k r := by
  cases r <;> rfl

/-- The two sides of the condition of the entry `e = (x, m₁, m₂)` are opposite constants when
the high variables are given by `α`, evaluated on the memoised residuals. -/
noncomputable def deadR (P : Problem) (b α : ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  forceB (Nat.land α e.2.1) fun r₁ => forceB (Nat.land α e.2.2) fun r₂ =>
    deadLR (top b) (P.dotRL b e.1 r₁) (P.dotRR b e.1 r₂)

end Problem

end RACert
