/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Frame


/-!
# Allocating a list of arrays

`allocAll l` allocates the arrays of `l` in turn, each with the capacity its expression gives.
When the expressions read only locals (`Expr.noLoad`), they evaluate the same throughout, and
the result is exact (`exec_allocAll`): each listed array has its capacity and reads 0, every other
array is unchanged, and so are the locals.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-- The expression reads no array. -/
def Expr.noLoad : Expr → Bool
  | .lit _ => true
  | .var _ => true
  | .load _ _ => false
  | .bin _ a b => a.noLoad && b.noLoad
  | .un _ a => a.noLoad

theorem Expr.eval_noLoad {s s' : State} (hl : s'.loc = s.loc) : ∀ (e : Expr), e.noLoad →
  e.eval s' = e.eval s
  | .lit _, _ => rfl
  | .var x, _ => by simp [eval, hl]
  | .load _ _, h => by simp [noLoad] at h
  | .bin op a b, h => by
    simp only [noLoad, Bool.and_eq_true] at h
    simp only [eval, Expr.eval_noLoad hl a h.1, Expr.eval_noLoad hl b h.2]
  | .un op a, h => by simp only [noLoad] at h; simp only [eval, Expr.eval_noLoad hl a h]

/-- Allocate the listed arrays in order, followed by a skip instruction. -/
def allocAll (l : List (Arr × Expr)) : Stmt := l.foldr (fun ae c => .seq (.alloc ae.1 ae.2) c) .skip

/-- The static instruction cost of allocating the listed arrays. -/
def allocCost (l : List (Arr × Expr)) : Nat := (l.map fun ae => 1 + ae.2.cost).sum + 1

/-- **Allocating a list of arrays.** -/
theorem exec_allocAll : ∀ (l : List (Arr × Expr)) (s : State),
    (∀ ae ∈ l, ae.2.noLoad ∧ (ae.2.eval s).isSome) → (l.map Prod.fst).Nodup →
    (exec (allocAll l) s).status = .ok ∧ (exec (allocAll l) s).cost = allocCost l ∧
      (exec (allocAll l) s).st.loc = s.loc ∧
      (∀ ae ∈ l, (exec (allocAll l) s).st.cap ae.1 = (ae.2.eval s).getD 0 ∧
        ∀ i, (exec (allocAll l) s).st.mem ae.1 i = 0) ∧
      (∀ b, b ∉ l.map Prod.fst → Same b s (exec (allocAll l) s).st)
  | [], s, _, _ => ⟨rfl, rfl, rfl, fun _ h => by simp at h, fun _ _ => ⟨rfl, rfl⟩⟩
  | (a, e) :: l, s, h, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hne, hnd⟩ := hnd
    obtain ⟨hn, hev0⟩ := h (a, e) (by simp)
    obtain ⟨va, hev⟩ := Option.isSome_iff_exists.mp hev0
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = (s.bump (e.maxv s)).alloc a va := ⟨_, rfl⟩
    have hl1 : s1.loc = s.loc := by rw [hs1]; rfl
    have h' : ∀ ae ∈ l, ae.2.noLoad ∧ (ae.2.eval s1).isSome := fun ae hae => by
      obtain ⟨a1, a2⟩ := h ae (by simp [hae])
      exact ⟨a1, by rw [Expr.eval_noLoad hl1 _ a1]; exact a2⟩
    obtain ⟨r1, r2, r3, r4, r5⟩ := exec_allocAll l s1 h' hnd
    have he : exec (allocAll ((a, e) :: l)) s = (Out.bind ⟨s1, 1 + e.cost, .ok⟩ (exec
      (allocAll l))) := by
      simp only [allocAll, List.foldr_cons, exec, hev]; rw [hs1]
    rw [he]
    simp only [Out.bind, r1]
    refine ⟨trivial, ?_, r3.trans hl1, fun ae hae => ?_, fun b hb => ?_⟩
    · show 1 + e.cost + (exec (allocAll l) s1).cost = allocCost ((a, e) :: l)
      rw [r2]; simp only [allocCost, List.map_cons, List.sum_cons]; omega
    · simp only [List.mem_cons] at hae
      rcases hae with rfl | hae
      · have := r5 a hne
        refine ⟨?_, fun i => ?_⟩
        · rw [this.2, hs1, hev]
          simp [State.alloc, State.upd]
        · rw [this.1, hs1]
          simp [State.alloc]
      · obtain ⟨c1, c2⟩ := r4 ae hae
        obtain ⟨a1, -⟩ := h ae (by simp [hae])
        exact ⟨by rw [c1, Expr.eval_noLoad hl1 _ a1], c2⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hb
      have := r5 b hb.2
      constructor
      · rw [this.1, hs1]
        simp [State.alloc, State.bump, hb.1]
      · rw [this.2, hs1]
        simp [State.alloc, State.bump, State.upd, hb.1]

/-! ### The cost of straight-line code -/

/-- The cost of straight-line code, read off its syntax (`none` for branches, loops, calls). -/
def Stmt.slCost : Stmt → Option Nat
  | .skip => some 1
  | .assign _ e => some (1 + e.cost)
  | .store _ i e => some (1 + i.cost + e.cost)
  | .alloc _ n => some (1 + n.cost)
  | .seq c d => c.slCost.bind fun a => d.slCost.map (a + ·)
  | _ => none

/-- **Straight-line code that ends normally costs its syntactic cost.** -/
theorem cost_of_ok : ∀ (c : Stmt) (s : State) (k : Nat), c.slCost = some k → (exec c
  s).status = .ok →
    (exec c s).cost = k
  | .skip, s, k, h, _ => by simp [Stmt.slCost] at h; simp [exec, h]
  | .assign x e, s, k, h, hs => by
    simp [Stmt.slCost] at h; subst h
    simp only [exec] at hs ⊢; split <;> simp_all
  | .store a i e, s, k, h, hs => by
    simp [Stmt.slCost] at h; subst h
    simp only [exec] at hs ⊢
    split
    · split <;> simp_all
    · simp_all
  | .alloc a n, s, k, h, hs => by
    simp [Stmt.slCost] at h; subst h
    simp only [exec] at hs ⊢; split <;> simp_all
  | .seq c d, s, k, h, hs => by
    simp only [Stmt.slCost] at h
    cases hc : c.slCost with
    | none => simp [hc] at h
    | some a =>
      cases hd : d.slCost with
      | none => simp [hc, hd] at h
      | some b =>
        simp [hc, hd] at h
        simp only [exec, Out.bind] at hs ⊢
        cases hcs : (exec c s).status <;> simp only [hcs] at hs ⊢
        · rw [cost_of_ok c s a hc hcs, cost_of_ok d _ b hd hs, ← h]
        · cases hs
        · cases hs
  | .ite _ _ _, _, _, h, _ => by simp [Stmt.slCost] at h
  | .loop _ _ _, _, _, h, _ => by simp [Stmt.slCost] at h
  | .call _ _ _ _ _ _, _, _, h, _ => by simp [Stmt.slCost] at h
  | .fail, _, _, h, _ => by simp [Stmt.slCost] at h
  | .catch _ _, _, _, h, _ => by simp [Stmt.slCost] at h

/-! ### Storing a list of values into one array -/

/-- Store each `(i, e)` of `l` into array `a`, in turn. -/
def storeAll (a : Arr) (l : List (Nat × Expr)) : Stmt :=
  l.foldr (fun ie c => .seq (.store a (.lit ie.1) ie.2) c) .skip

/-- The contents after the stores. -/
def storeFold (s : State) (f : Nat → Nat) (l : List (Nat × Expr)) : Nat → Nat :=
  l.foldl (fun f ie => State.upd f ie.1 ((ie.2.eval s).getD 0)) f

/-- **Storing a list of values into one array.** -/
theorem exec_storeAll (a : Arr) : ∀ (l : List (Nat × Expr)) (s : State),
    (∀ ie ∈ l, ie.2.noLoad ∧ (ie.2.eval s).isSome ∧ ie.1 < s.cap a) →
    (exec (storeAll a l) s).status = .ok ∧ (exec (storeAll a l) s).st.loc = s.loc ∧
      (exec (storeAll a l) s).st.cap = s.cap ∧
      (exec (storeAll a l) s).st.mem a = storeFold s (s.mem a) l ∧
      (∀ b, b ≠ a → (exec (storeAll a l) s).st.mem b = s.mem b)
  | [], s, _ => ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | (i, e) :: l, s, h => by
    obtain ⟨hn, hev0, hi⟩ := h (i, e) (by simp)
    obtain ⟨v, hev⟩ := Option.isSome_iff_exists.mp hev0
    obtain ⟨s1, hs1⟩ : ∃ s1, s1 = ((s.bump (Expr.maxv s (.lit i))).bump (e.maxv s)).write a i
      v := ⟨_, rfl⟩
    have hl1 : s1.loc = s.loc := by rw [hs1]; rfl
    have hc1 : s1.cap = s.cap := by rw [hs1]; rfl
    have h' : ∀ ie ∈ l, ie.2.noLoad ∧ (ie.2.eval s1).isSome ∧ ie.1 < s1.cap a := fun ie hie => by
      obtain ⟨a1, a2, a3⟩ := h ie (by simp [hie])
      exact ⟨a1, by rw [Expr.eval_noLoad hl1 _ a1]; exact a2, by rw [hc1]; exact a3⟩
    obtain ⟨r1, r2, r3, r4, r5⟩ := exec_storeAll a l s1 h'
    have he : exec (storeAll a ((i, e) :: l)) s = (Out.bind ⟨s1, 1 + (Expr.lit i).cost +
      e.cost, .ok⟩
        (exec (storeAll a l))) := by
      simp only [storeAll, List.foldr_cons, exec, Expr.eval, hev, hi, ite_true]; rw [hs1]
    rw [he]
    simp only [Out.bind, r1]
    refine ⟨trivial, r2.trans hl1, r3.trans hc1, ?_, fun b hb => ?_⟩
    · rw [r4]
      have hf : ∀ (l' : List (Nat × Expr)) (f : Nat → Nat), (∀ ie ∈ l', ie.2.noLoad) →
          storeFold s1 f l' = storeFold s f l' := by
        intro l' f hl'
        induction l' generalizing f with
        | nil => rfl
        | cons ie t ih =>
          simp only [storeFold, List.foldl_cons]
          rw [Expr.eval_noLoad hl1 _ (hl' ie (by simp))]
          exact ih _ (fun x hx => hl' x (by simp [hx]))
      rw [hf l _ (fun ie hie => (h ie (by simp [hie])).1)]
      simp only [storeFold, List.foldl_cons, hev, Option.getD_some]
      rw [hs1]; simp [State.write, State.bump]
    · rw [r5 b hb, hs1]; simp [State.write, State.bump, hb]

end OrderMaintenance.Machine
