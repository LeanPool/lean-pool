/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PresIns


/-!
# M5: the order invariant after a chunk split

The chunk list gains `y` right before and `z` right after `x`; `y` and `z` carry `x`'s path, are
entries of `x`'s tables next to it, and children of `x`'s live parent next to it.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The chunk list after the split. -/
def clIns (cl : List Nat) (x y z : Nat) : List Nat := cl.replace1 x [y, x, z]

theorem replace1_split {A B : List Nat} {x : Nat} (ys : List Nat) (hA : x ∉ A) :
    (A ++ x :: B).replace1 x ys = A ++ ys ++ B := by
  induction A with
  | nil => simp [List.replace1]
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at hA
    simp only [List.cons_append, List.replace1, ite_eq_right (Ne.symm hA.1), ih hA.2]

/-- The order after the split: the chunk list changes. -/
def ordIns (ord : Nat → List Nat) (cl : List Nat) (x y z : Nat) : Nat → List Nat :=
  fun k => if k = 0 then clIns cl x y z else ord k

theorem ins_pp_ht {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    (hI : InvJ (ts s) cl ord dr n0 none) {c : Nat} (hc : c ∈ cl) {i : Nat} (h1 : 1 ≤ i)
    (hi : i ≤ s.P.H) : isN (ts s) (pp (ts s) c i) ∧ ht (ts s) (pp (ts s) c i) = i :=
  (hI.shape.ordMem i h1 hi _).mp (hI.shape.pathEnt c hc i hi)

theorem tagUp_one (u : TS) (c : Nat) : tagUp u c 1 = digit u c 1 := by simp [tagUp]

section shape
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
  (hI : InvJ (ts s) cl ord dr n0 none) (hTP : TopParams s.P)
  (hcs : ∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size) {x : Nat} (hx : x ∈ cl)
include hI hcs hx

theorem ins_cl : ∃ A B, cl = A ++ x :: B ∧ x ∉ A ∧ x ∉ B ∧
    clIns cl x s.C.size (s.C.size + 1) = A ++ s.C.size :: x :: (s.C.size + 1) :: B := by
  have hnd : cl.Nodup := hI.shape.ord0 ▸ hI.shape.ordNodup 0
  obtain ⟨A, B, rfl⟩ := List.mem_iff_append.mp hx
  have h1 := List.nodup_append.mp hnd
  have hA : x ∉ A := fun h => h1.2.2 x h x (by simp) rfl
  have hB : x ∉ B := fun h => (List.nodup_cons.mp h1.2.1).1 h
  refine ⟨A, B, rfl, hA, hB, ?_⟩
  unfold clIns; rw [replace1_split _ hA]; simp

theorem ins_fresh : s.C.size ∉ cl ∧ s.C.size + 1 ∉ cl := by
  constructor <;> intro h <;> have := (hcs _).mp h <;> omega

theorem ins_cl_nodup : (clIns cl x s.C.size (s.C.size + 1)).Nodup := by
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  have hnd : cl.Nodup := hI.shape.ord0 ▸ hI.shape.ordNodup 0
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  rw [hcl'];  rw [hcl] at hnd hy hz
  simp only [List.mem_append, List.mem_cons, not_or] at hy hz
  have h1 := List.nodup_append.mp hnd
  rw [List.nodup_append]
  refine ⟨h1.1, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, not_or]
    refine ⟨⟨by omega, by omega, fun h => hy.2.2 h⟩, ⟨by omega, hB⟩, fun h => hz.2.2 h,
      (List.nodup_cons.mp h1.2.1).2⟩
  · intro a ha b hb e
    subst e
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | rfl | hb
    · exact hy.1 ha
    · exact hA ha
    · exact hz.1 ha
    · exact h1.2.2 a ha a (by simp [hb]) rfl

theorem ins_sub : cl.Sublist (clIns cl x s.C.size (s.C.size + 1)) := by
  obtain ⟨A, B, hcl, -, -, hcl'⟩ := ins_cl hI hcs hx
  rw [hcl', hcl]
  exact (List.Sublist.refl A).append (((List.sublist_cons_self _ _).cons_cons x).cons _)

/-- The split chunk's level-1 path node holds `x`. -/
theorem ins_pp1 : pp (ts s) x 1 ∈ s.cin.getX x := by
  have S := hI.shape
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  have h3 := S.H3
  have hw := S.W3 x hx 1 le_rfl (by omega)
  have he := S.pathEnt x hx 1 (by omega)
  have hm := (S.ordMem 1 le_rfl (by omega) _).mp he
  have : pp (ts s) x 1 ∈ tabs (ts s) 0 x :=
    (S.tabsIff 0 x _ hent).mpr ⟨hm.1, hm.2, hw⟩
  unfold tabs at this; rw [ite_eq_left rfl] at this; exact this

/-- A table holding `x`: height 1. -/
theorem ins_cinX {X : Nat} (hX : X ∈ s.cin.getX x) :
    isN (ts s) X ∧ ht (ts s) X = 1 ∧ x ∈ order (ts s) X := by
  have hent : Ent ord 0 x := by unfold Ent; rw [hI.shape.ord0]; exact hx
  have hT' : X ∈ tabs (ts s) 0 x := by unfold tabs; rw [ite_eq_left rfl]; exact hX
  exact (hI.shape.tabsIff 0 x X hent).mp hT'

variable {f1x i1 : Nat} {t : TS} (F : InsFrame s x f1x i1 t)
include F

/-- The tables of `x` after the split: `y` right before and `z` right after `x`. -/
theorem ins_table (hTP : TopParams s.P) {T : Nat} (hT : T ∈ s.cin.getX x) :
    ∃ A le Bs a b, (s.nodes.getX T).table = A ++ (x, le) :: Bs ∧ x ∉ A.map (·.1) ∧
      (nd t T).table = A ++ (s.C.size, a) :: (x, le) :: (s.C.size + 1, b) :: Bs ∧
      GapsGe s.P.beta (gapB s.P.beta (n0 T) (dr T + 1))
        ((A ++ (s.C.size, a) :: (x, le) :: (s.C.size + 1, b) :: Bs).map (·.2)) ∧
      1 ≤ gapB s.P.beta (n0 T) (dr T + 1) ∧
      ((s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side x).isSome) ∧
      a = roomL s.P.beta (s.nodes.getX T).table x true ∧
      b = roomL s.P.beta (s.nodes.getX T).table x false := by
  obtain ⟨A, le, Bs, htab, hA, hside, h1, h2, hB, hg⟩ :=
    start_room hI hTP hx (T := T) hT s.C.size (s.C.size + 1)
  simp only [ts_P] at hB hg h1 h2
  have htab0 : (s.nodes.getX T).table = A ++ (x, le) :: Bs := htab
  have hTs : T < s.nodes.size := by
    have hent : Ent ord 0 x := by unfold Ent; rw [hI.shape.ord0]; exact hx
    have hT' : T ∈ tabs (ts s) 0 x := by unfold tabs; rw [ite_eq_left rfl]; exact hT
    exact ((hI.shape.tabsIff 0 x T hent).mp hT').1.2.1
  refine ⟨A, le, Bs, _, _, htab, hA, ?_, by rw [gapB_succ]; exact hg, by rw [gapB_succ]; omega, hside,
    by rw [htab0, roomL_eq hA], by rw [htab0, roomL_eq hA]⟩
  · rw [F.table, ite_eq_left ⟨hT, hTs⟩]
    show aroundT (nd (ts s) T).table x _ _ _ _ = _
    rw [htab, aroundT_eq hA]
    unfold insF aroundTab
    have e1 := roomL_eq (β := s.P.beta) (Bs := Bs) (le := le) hA true
    have e2 := roomL_eq (β := s.P.beta) (Bs := Bs) (le := le) hA false
    show A ++ (s.C.size, roomL s.P.beta (s.nodes.getX T).table x true) :: (x, le) ::
      (s.C.size + 1, roomL s.P.beta (s.nodes.getX T).table x false) :: Bs = _
    have htab' : (s.nodes.getX T).table = A ++ (x, le) :: Bs := htab
    rw [htab', e1, e2]

theorem ins_order_old {X : Nat} (hX : X ∉ s.cin.getX x) : order t X = order (ts s) X := by
  unfold order Node.order; rw [F.table, ite_eq_right (fun h => hX h.1)]; rfl

theorem ins_labs_old {X : Nat} (hX : X ∉ s.cin.getX x) : labs t X = labs (ts s) X := by
  unfold labs; rw [F.table, ite_eq_right (fun h => hX h.1)]; rfl

/-- Entries only gain: every old entry of a table is still one. -/
theorem ins_order_sup (hTP : TopParams s.P) (X e : Nat) (he : e ∈ order (ts s) X) : e ∈ order t X := by
  by_cases hX : X ∈ s.cin.getX x
  · obtain ⟨A, le, Bs, a, b, htab, -, htab', -⟩ := ins_table hI hcs hx F hTP hX
    unfold order Node.order at he ⊢
    rw [htab']
    have he' : e ∈ (s.nodes.getX X).table.map (·.1) := he
    rw [htab] at he'
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at he' ⊢
    tauto
  · rw [ins_order_old hI hcs hx F hX]; exact he

/-- **The tag-ordering part of the invariant after the split.** -/
theorem ins_shapeT (hTP : TopParams s.P) :
    ShapeT t (clIns cl x s.C.size (s.C.size + 1)) (ordIns ord cl x s.C.size (s.C.size + 1)) := by
  have S := hI.shape
  have h3 := S.H3
  have eP : (ts s).P = s.P := rfl
  rw [eP] at h3
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have hnd : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  have hmem : ∀ c, c ∈ clIns cl x s.C.size (s.C.size + 1) ↔ c ∈ cl ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; rw [hcl', hcl]; simp only [List.mem_append, List.mem_cons]; tauto
  have hord : ∀ k, 1 ≤ k → ordIns ord cl x s.C.size (s.C.size + 1) k = ord k := fun k hk => by
    unfold ordIns; rw [ite_eq_right (by omega)]
  -- the chunk standing for `c` before the split
  have hpp : ∀ c ∈ clIns cl x s.C.size (s.C.size + 1), ∀ j, 1 ≤ j → j ≤ s.P.H →
      pp t c j = pp (ts s) (if c = s.C.size ∨ c = s.C.size + 1 then x else c) j := by
    intro c _ j hj1 hj
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · rw [ite_eq_left hc]; exact F.pp_new c hc j hj1 hj
    · rw [ite_eq_right hc]; push Not at hc; exact F.pp_old c hc.1 hc.2 j
  have hproj : ∀ c ∈ clIns cl x s.C.size (s.C.size + 1),
      (if c = s.C.size ∨ c = s.C.size + 1 then x else c) ∈ cl := by
    intro c hc; split
    · exact hx
    · rcases (hmem c).mp hc with h | h | h
      · exact h
      all_goals tauto
  refine ⟨by rw [F.P]; exact h3, rfl, fun k => ?_, fun k hk1 hk v => ?_, fun k hk => ?_, fun v hv => ?_,
    ⟨?_, ?_, ?_⟩, fun c hc j hj => ?_, fun c hc j hj1 hj => ?_, fun j hj c d hcd => ?_,
    fun X hX => ?_, fun X hX => ?_⟩
  · by_cases hk : k = 0
    · unfold ordIns; rw [ite_eq_left hk]; exact ins_cl_nodup hI hcs hx
    · rw [hord k (by omega)]; exact S.ordNodup k
  · rw [F.P] at hk
    rw [hord k hk1, S.ordMem k hk1 hk, F.isN, F.ht]
  · rw [F.P] at hk
    rw [hord k (by omega)]; exact S.ordHigh k hk
  · rw [F.isN] at hv; rw [F.ht, F.P]; exact S.htN v hv
  · rw [F.P, hord _ (by omega)]; exact S.root.1
  · rw [F.P, F.liveN]; exact S.root.2.1
  · rw [F.P, F.livePar]; exact S.root.2.2
  · rw [F.P] at hj
    by_cases hj0 : j = 0
    · subst hj0; simp only [Ent, ordIns, pp, ↓reduceIte]; exact hc
    · show _ ∈ _; rw [hord j (by omega), hpp c hc j (by omega) hj]
      exact S.pathEnt _ (hproj c hc) j hj
  · rw [F.P] at hj
    by_cases hj2 : 2 ≤ j
    · rw [hpp c hc j hj1 hj, hpp c hc (j - 1) (by omega) (by omega)]
      exact ins_order_sup hI hcs hx F hTP _ _ (S.W3 _ (hproj c hc) j hj1 hj)
    · have e1 : j = 1 := by omega
      subst e1
      by_cases hcn : c = s.C.size ∨ c = s.C.size + 1
      · rw [F.pp_new c hcn 1 le_rfl (by omega)]
        show c ∈ order t (pp (ts s) x 1)
        obtain ⟨A', le, Bs, a, b, -, -, htab', -⟩ := ins_table hI hcs hx F hTP (ins_pp1 hI hcs hx)
        unfold order Node.order; rw [htab']
        simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
        omega
      · have hc0 : c ∈ cl := by have := hproj c hc; rwa [ite_eq_right hcn] at this
        rw [hpp c hc 1 le_rfl (by omega), ite_eq_right hcn]
        push Not at hcn
        rw [F.pp_old c hcn.1 hcn.2 0]
        exact ins_order_sup hI hcs hx F hTP _ _ (S.W3 c hc0 1 le_rfl hj)
  · rw [F.P] at hj
    by_cases hj0 : j = 0
    · subst hj0; right; unfold pp; rw [ite_eq_left rfl, ite_eq_left rfl]; unfold ordIns; rw [ite_eq_left rfl]; exact hcd
    · rw [hord j (by omega), hpp c hcd.mem_left j (by omega) hj,
      hpp d hcd.mem_right j (by omega) hj]
      rw [hcl'] at hcd
      have hyA : s.C.size ∉ A := fun h => hy (by rw [hcl]; simp [h])
      have hzA : s.C.size + 1 ∉ A := fun h => hz (by rw [hcl]; simp [h])
      have hyB : s.C.size ∉ B := fun h => hy (by rw [hcl]; simp [h])
      have hzB : s.C.size + 1 ∉ B := fun h => hz (by rw [hcl]; simp [h])
      rcases before_proj hyA hzA hyB hzB hcd with e | e <;> simp only at e
      · left; rw [e]
      · rw [← hcl] at e; exact S.O2 j hj _ _ e
  · rw [F.isN] at hX
    rw [F.ht]
    by_cases hXc : X ∈ s.cin.getX x
    · have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
      have hT' : X ∈ tabs (ts s) 0 x := by unfold tabs; rw [ite_eq_left rfl]; exact hXc
      have hX1 := ((S.tabsIff 0 x X hent).mp hT').2.1
      obtain ⟨A', le, Bs, a, b, htab, hA', htab', -⟩ := ins_table hI hcs hx F hTP hXc
      have hO := S.O1 X hX
      rw [hX1, S.ord0] at hO
      unfold order Node.order at hO ⊢
      rw [htab']; rw [show (nd (ts s) X).table = A' ++ (x, le) :: Bs from htab] at hO
      rw [hX1]; simp only [Nat.sub_self]; unfold ordIns; rw [ite_eq_left rfl, hcl']
      rw [hcl] at hO hnd
      simp only [List.map_append, List.map_cons] at hO ⊢
      exact sublist_around hO hA hB
    · rw [ins_order_old hI hcs hx F hXc]
      by_cases h1 : ht (ts s) X - 1 = 0
      · rw [h1]; unfold ordIns; rw [ite_eq_left rfl]
        exact (h1 ▸ S.O1 X hX).trans (S.ord0 ▸ ins_sub hI hcs hx)
      · rw [hord _ (by omega)]; exact S.O1 X hX
  · rw [F.isN] at hX
    rw [F.P]
    by_cases hXc : X ∈ s.cin.getX x
    · obtain ⟨A', le, Bs, a, b, -, -, htab', hg, h1, -⟩ := ins_table hI hcs hx F hTP hXc
      unfold labs; rw [htab']; exact gapsGe_mono h1 hg
    · rw [ins_labs_old hI hcs hx F hXc]; exact S.labsOk X hX

/-! ### Further views -/

theorem ins_order_mem (hTP : TopParams s.P) {X : Nat} (hX : X ∈ s.cin.getX x) (e : Nat) :
    e ∈ order t X ↔ e ∈ order (ts s) X ∨ e = s.C.size ∨ e = s.C.size + 1 := by
  obtain ⟨A', le, Bs, a, b, htab, -, htab', -⟩ := ins_table hI hcs hx F hTP hX
  unfold order Node.order
  rw [htab', show (nd (ts s) X).table = A' ++ (x, le) :: Bs from htab]
  simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
  tauto

/-! ### Digits and tags after the split -/

theorem ins_digit_hi {c : Nat} (hc : c ∈ cl) (c' : Nat)
    (hpc : ∀ j, 1 ≤ j → j ≤ s.P.H → pp t c' j = pp (ts s) c j) {i : Nat} (h2 : 2 ≤ i)
    (hi : i ≤ s.P.H) : digit t c' i = digit (ts s) c i := by
  unfold digit
  rw [hpc i (by omega) hi, hpc (i - 1) (by omega) (by omega)]
  have hn := ins_pp_ht hI hc (i := i) (by omega) hi
  have hX : pp (ts s) c i ∉ s.cin.getX x := fun h => by
    have := (ins_cinX hI hcs hx h).2.1; omega
  unfold Node.lab?; rw [F.table, ite_eq_right (fun h => hX h.1)]; rfl

theorem ins_digit_one_old (hTP : TopParams s.P) {c : Nat} (hc : c ∈ cl) :
    digit t c 1 = digit (ts s) c 1 := by
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have hcy : c ≠ s.C.size := fun e => hy (e ▸ hc)
  have hcz : c ≠ s.C.size + 1 := fun e => hz (e ▸ hc)
  unfold digit
  rw [F.pp_old c hcy hcz 1, F.pp_old c hcy hcz 0]
  by_cases hX : pp (ts s) c 1 ∈ s.cin.getX x
  · obtain ⟨A', le, Bs, a, b, htab, -, htab', -⟩ := ins_table hI hcs hx F hTP hX
    unfold Node.lab?; rw [htab']
    show _ = ((lookup (s.nodes.getX (pp (ts s) c 1)).table _).getD 0)
    rw [htab]
    have e0 : pp (ts s) c (1 - 1) = c := rfl
    rw [e0, lookup_around _ _ hcy hcz]
  · unfold Node.lab?; rw [F.table, ite_eq_right (fun h => hX h.1)]; rfl

theorem ins_digit_one_new (hTP : TopParams s.P) (c : Nat) (hcn : c = s.C.size ∨ c = s.C.size + 1) :
    digit t c 1 = roomL s.P.beta (s.nodes.getX (pp (ts s) x 1)).table x (decide (c = s.C.size)) := by
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have h3 : 3 ≤ s.P.H := hI.shape.H3
  have hT := ins_pp1 hI hcs hx
  obtain ⟨A', le, Bs, a, b, htab, -, htab', -, -, -, ha, hb⟩ := ins_table hI hcs hx F hTP hT
  obtain ⟨-, hT1, -⟩ := ins_cinX hI hcs hx hT
  have hkeys : ∀ k ∈ A'.map (·.1), k ∈ cl := by
    intro k hk
    have hk' : k ∈ order (ts s) (pp (ts s) x 1) := by
      unfold order Node.order; rw [show (nd (ts s) (pp (ts s) x 1)).table = A' ++ (x, le) :: Bs from htab]
      simp only [List.map_append, List.mem_append]; exact Or.inl hk
    have := (hI.shape.O1 _ (ins_cinX hI hcs hx hT).1).subset hk'
    rwa [hT1, Nat.sub_self, hI.shape.ord0] at this
  unfold digit
  rw [F.pp_new c hcn 1 le_rfl (by omega)]
  have e0 : pp t c (1 - 1) = c := rfl
  rw [e0]
  unfold Node.lab?; rw [htab']
  rcases hcn with rfl | rfl
  · rw [lookup_append_cons_self (fun h => hy (hkeys _ h)), ha]; simp
  · have hxs := (hcs x).mp hx
    rw [show A' ++ (s.C.size, a) :: (x, le) :: (s.C.size + 1, b) :: Bs =
      (A' ++ [(s.C.size, a), (x, le)]) ++ (s.C.size + 1, b) :: Bs by simp]
    rw [lookup_append_cons_self, hb]
    · simp
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hz (hkeys _ h), by omega, by omega⟩

/-- **The tags after the split** are the tags the paths spell. -/
theorem ins_tags (hTP : TopParams s.P) (hf1 : f1x = digit (ts s) x 1)
    (hi1 : (s.cin.getX x).idx? (pp (ts s) x 1) = some i1) :
    ∀ c ∈ clIns cl x s.C.size (s.C.size + 1), t.tag c = tagF t c := by
  have S := hI.shape
  have h3 := S.H3
  have eP : (ts s).P = s.P := rfl
  rw [eP] at h3
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  have hxs := (hcs x).mp hx
  have hβ : t.P.beta = (ts s).P.beta := by rw [F.P]; rfl
  intro c hc
  unfold tagF; rw [F.P, F.tag]
  have hmem : c ∈ cl ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    rw [hcl', hcl] at *; simp only [List.mem_append, List.mem_cons] at hc ⊢; tauto
  by_cases hcn : c = s.C.size ∨ c = s.C.size + 1
  · have hpc : ∀ j, 1 ≤ j → j ≤ s.P.H → pp t c j = pp (ts s) x j := fun j h1 h2 =>
      F.pp_new c hcn j h1 h2
    have hhi := tagUp_high (s := ts s) (s' := t) (c := x) (c' := c) hβ 1 s.P.H (by omega)
      (fun i h1 h2 => ins_digit_hi hI hcs hx F hx c hpc (by omega) h2)
    rw [tagUp_one, tagUp_one] at hhi
    have hmono : digit (ts s) x 1 ≤ tagUp (ts s) x s.P.H := by
      rw [← tagUp_one]; exact tagUp_mono _ _ _ _ (by omega)
    have htx : (s.C.getX x).tag = tagUp (ts s) x s.P.H := S.tags x hx
    have hd := ins_digit_one_new hI hcs hx F hTP c hcn
    obtain ⟨n1, n2, n3, n4, n5, -⟩ := ins0_top s x
    rcases hcn with rfl | rfl
    · rw [ite_eq_right (by omega), ite_eq_left rfl]
      unfold tagY
      rw [ins0_tag s x hxs.2, n3, n5, n1, hf1, htx, idx?_getD_map hi1]
      simp only [decide_true] at hd
      rw [← hd]; omega
    · rw [ite_eq_left rfl]
      unfold tagZ
      rw [ins0_tag s x hxs.2, n3, n5, n1, hf1, htx, idx?_getD_map hi1]
      simp only [show ¬(s.C.size + 1 = s.C.size) by omega, decide_false] at hd
      rw [← hd]; omega
  · have hc0 : c ∈ cl := by tauto
    push Not at hcn
    rw [ite_eq_right hcn.2, ite_eq_right hcn.1]
    have hpc : ∀ j, 1 ≤ j → j ≤ s.P.H → pp t c j = pp (ts s) c j := fun j _ _ =>
      F.pp_old c hcn.1 hcn.2 j
    rw [tagUp_congr hβ s.P.H (fun i h1 h2 => by
      rcases Nat.lt_or_ge i 2 with hi | hi
      · rw [show i = 1 by omega]; exact ins_digit_one_old hI hcs hx F hTP hc0
      · exact ins_digit_hi hI hcs hx F hc0 c hpc hi h2)]
    exact S.tags c hc0

/-- **The order invariant after the split.** -/
theorem ins_shape (hTP : TopParams s.P) (hf1 : f1x = digit (ts s) x 1)
    (hi1 : (s.cin.getX x).idx? (pp (ts s) x 1) = some i1) :
    Shape t (clIns cl x s.C.size (s.C.size + 1)) (ordIns ord cl x s.C.size (s.C.size + 1)) := by
  have S := hI.shape
  have ST := ins_shapeT hI hcs hx F hTP
  have h3 := S.H3
  have eP : (ts s).P = s.P := rfl
  rw [eP] at h3
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have hnd : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  have hnd' := ins_cl_nodup hI hcs hx
  have hmem : ∀ c, c ∈ clIns cl x s.C.size (s.C.size + 1) ↔ c ∈ cl ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; rw [hcl', hcl]; simp only [List.mem_append, List.mem_cons]; tauto
  have hord : ∀ k, 1 ≤ k → ordIns ord cl x s.C.size (s.C.size + 1) k = ord k := fun k hk => by
    unfold ordIns; rw [ite_eq_right (by omega)]
  have hord0 : ordIns ord cl x s.C.size (s.C.size + 1) 0 = clIns cl x s.C.size (s.C.size + 1) := rfl
  have hproj : ∀ c ∈ clIns cl x s.C.size (s.C.size + 1),
      (if c = s.C.size ∨ c = s.C.size + 1 then x else c) ∈ cl := by
    intro c hc; split
    · exact hx
    · rcases (hmem c).mp hc with h | h | h
      · exact h
      all_goals tauto
  have hlpr : ∀ c, lpr t c = lpr (ts s) (if c = s.C.size ∨ c = s.C.size + 1 then x else c) := by
    intro c; rw [F.lpar]; split <;> rfl
  have hpp : ∀ c, ∀ j, 1 ≤ j → j ≤ s.P.H →
      pp t c j = pp (ts s) (if c = s.C.size ∨ c = s.C.size + 1 then x else c) j := by
    intro c j hj1 hj
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · rw [ite_eq_left hc]; exact F.pp_new c hc j hj1 hj
    · rw [ite_eq_right hc]; push Not at hc; exact F.pp_old c hc.1 hc.2 j
  have hanc : ∀ c, ∀ j, 1 ≤ j →
      anc t c j = anc (ts s) (if c = s.C.size ∨ c = s.C.size + 1 then x else c) j := by
    intro c j hj1
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · rw [ite_eq_left hc]; exact F.anc_new c hc j hj1
    · rw [ite_eq_right hc]; push Not at hc; exact F.anc_old c hc.1 hc.2 j
  -- nodes of height at least 2 do not hold `x`
  have hnot : ∀ X, isN (ts s) X → 2 ≤ ht (ts s) X → X ∉ s.cin.getX x := fun X _ h2 hX => by
    have := (ins_cinX hI hcs hx hX).2.1; omega
  have hlx := S.lp x hx
  have hlxs : lpr (ts s) x < s.nodes.size := hlx.1.1.2.1
  have hchild : ∀ u, (nd t u).children = if u = lpr (ts s) x then
      (nd (ts s) u).children.replace1 x [s.C.size, x, s.C.size + 1] else (nd (ts s) u).children := by
    intro u; rw [F.children]
    by_cases hu : u = lpr (ts s) x
    · rw [ite_eq_left ⟨hu, hu ▸ hlxs⟩, ite_eq_left hu]; rfl
    · rw [ite_eq_right (fun h => hu h.1), ite_eq_right hu]; rfl
  -- the children of `x`'s parent
  obtain ⟨P', Q', hkx, hxP, hxQ⟩ : ∃ P' Q', (nd (ts s) (lpr (ts s) x)).children = P' ++ x :: Q' ∧
      x ∉ P' ∧ x ∉ Q' := by
    obtain ⟨P', Q', e⟩ := List.mem_iff_append.mp hlx.2.2
    have hn := (S.kids _ hlx.1).1
    rw [e] at hn
    have h1 := List.nodup_append.mp hn
    exact ⟨P', Q', e, fun h => h1.2.2 x h x (by simp) rfl, (List.nodup_cons.mp h1.2.1).1⟩
  have hkx' : (nd t (lpr (ts s) x)).children = P' ++ s.C.size :: x :: (s.C.size + 1) :: Q' := by
    rw [hchild, ite_eq_left rfl, hkx, replace1_split _ hxP]; simp
  have hkids_cl : ∀ e ∈ (nd (ts s) (lpr (ts s) x)).children, e ∈ cl := by
    intro e he
    have := (S.kids _ hlx.1).2.1.subset he
    rwa [hlx.2.1, S.ord0] at this
  refine ⟨ST, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- up
    intro v hv hH
    rw [F.liveN] at hv; rw [F.ht, F.P] at hH
    obtain ⟨h1, h2, h3'⟩ := S.up v hv hH
    have hne : (nd (ts s) v).livePar ≠ lpr (ts s) x := by
      intro e; rw [e, hlx.2.1] at h2; have := (S.htN v hv.1).1; omega
    simp only [F.livePar, F.liveN, F.ht]
    rw [hchild, ite_eq_right hne]
    exact ⟨h1, h2, h3'⟩
  · -- lp
    intro c hc
    have hc0 := hproj c hc
    rw [hlpr, F.liveN, F.ht]
    refine ⟨(S.lp _ hc0).1, (S.lp _ hc0).2.1, ?_⟩
    by_cases hcn : c = s.C.size ∨ c = s.C.size + 1
    · rw [ite_eq_left hcn, hkx']
      simp only [List.mem_append, List.mem_cons]; omega
    · rw [ite_eq_right hcn] at hc0 ⊢
      have hm := (S.lp c hc0).2.2
      by_cases hl : lpr (ts s) c = lpr (ts s) x
      · rw [hl, hkx']; rw [hl, hkx] at hm
        simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto
      · rw [hchild, ite_eq_right hl]; exact hm
  · -- kids
    intro u hu
    rw [F.liveN] at hu
    obtain ⟨k1, k2, k3⟩ := S.kids u hu
    rw [F.ht]
    by_cases hu' : u = lpr (ts s) x
    · subst hu'
      rw [hkx']
      have hh1 : ht (ts s) (lpr (ts s) x) - 1 = 0 := by rw [hlx.2.1]
      rw [hh1, hord0]
      rw [hkx] at k1 k2 hkids_cl
      rw [hh1, S.ord0, hcl] at k2
      refine ⟨?_, ?_, fun e he => ⟨?_, fun h => by rw [hlx.2.1] at h; omega⟩⟩
      · have hy' : s.C.size ∉ P' ++ x :: Q' := fun h => hy (hkids_cl _ h)
        have hz' : s.C.size + 1 ∉ P' ++ x :: Q' := fun h => hz (hkids_cl _ h)
        have h1 := List.nodup_append.mp k1
        simp only [List.mem_append, List.mem_cons, not_or] at hy' hz'
        rw [List.nodup_append]
        refine ⟨h1.1, ?_, ?_⟩
        · simp only [List.nodup_cons, List.mem_cons, not_or]
          exact ⟨⟨by omega, by omega, hy'.2.2⟩, ⟨by omega, hxQ⟩, hz'.2.2, (List.nodup_cons.mp h1.2.1).2⟩
        · intro a ha b hb e; subst e
          simp only [List.mem_cons] at hb
          rcases hb with rfl | rfl | rfl | hb
          · exact hy'.1 ha
          · exact hxP ha
          · exact hz'.1 ha
          · exact h1.2.2 a ha a (by simp [hb]) rfl
      · rw [hcl']; exact sublist_around k2 hA hB
      · rw [F.par_zero, hlpr]
        simp only [List.mem_append, List.mem_cons] at he
        by_cases hen : e = s.C.size ∨ e = s.C.size + 1
        · rw [ite_eq_left hen]
        · rw [ite_eq_right hen]
          have he' : e ∈ P' ++ x :: Q' := by simp only [List.mem_append, List.mem_cons]; tauto
          have := (k3 e (by rw [hkx]; exact he')).1
          rw [hlx.2.1] at this; simpa [par] using this
    · rw [hchild, ite_eq_right hu']
      refine ⟨k1, ?_, fun e he => ?_⟩
      · by_cases h1 : ht (ts s) u - 1 = 0
        · rw [h1, hord0]; rw [h1, S.ord0] at k2; exact k2.trans (ins_sub hI hcs hx)
        · rw [hord _ (by omega)]; exact k2
      · obtain ⟨k4, k5⟩ := k3 e he
        by_cases h1 : ht (ts s) u - 1 = 0
        · rw [h1, F.par_zero, hlpr]
          have hecl : e ∈ cl := by have := k2.subset he; rwa [h1, S.ord0] at this
          have hen : ¬(e = s.C.size ∨ e = s.C.size + 1) := by
            rintro (rfl | rfl)
            · exact hy hecl
            · exact hz hecl
          rw [ite_eq_right hen]; rw [h1] at k4
          exact ⟨by simpa [par] using k4, fun h2 => absurd h2 (by omega)⟩
        · rw [F.par_pos (by omega), F.liveN]; exact ⟨k4, k5⟩
  · -- OT
    intro h hh1 hh u u' e e' hu hu' huu he he' hpe hpe'
    unfold Ent at he he'
    rw [F.P] at hh; rw [F.liveN] at hu hu'
    rw [hord h hh1] at huu
    by_cases h2 : 2 ≤ h
    · rw [hord _ (by omega)] at he he' ⊢
      rw [F.par_pos (by omega)] at hpe hpe'
      exact S.OT h hh1 hh u u' e e' hu hu' huu he he' hpe hpe'
    · have e1 : h = 1 := by omega
      subst e1
      simp only [Nat.sub_self] at he he' hpe hpe' ⊢
      rw [hord0] at he he' ⊢
      rw [F.par_zero, hlpr] at hpe hpe'
      have hb := S.OT 1 le_rfl hh u u' _ _ hu hu' huu (by show _ ∈ ord 0; rw [S.ord0]; exact hproj e he)
        (by show _ ∈ ord 0; rw [S.ord0]; exact hproj e' he')
        (by simpa [par] using hpe) (by simpa [par] using hpe')
      rw [S.ord0] at hb
      have hne : (if e = s.C.size ∨ e = s.C.size + 1 then x else e) ≠
          (if e' = s.C.size ∨ e' = s.C.size + 1 then x else e') := by
        intro eq; rw [eq] at hpe; rw [hpe] at hpe'
        exact huu.ne (S.ordNodup 1) hpe'
      rw [hcl'] at he he' hnd' ⊢
      rw [hcl] at hb
      exact before_lift hnd' he he' hne hb
  · -- ghost
    intro v hv
    rw [F.ghostN] at hv
    have hv1 := (S.htN v hv.1).1
    have hvx : v ≠ lpr (ts s) x := fun e => by
      rw [e] at hv; exact absurd hv.2 (by rw [hlx.1.2]; simp)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ := S.ghost v hv
    obtain ⟨-, hup, -⟩ := S.up _ g1 (by rw [g3]; exact g10)
    have hne : (nd (ts s) (nd (ts s) v).t1).livePar ≠ lpr (ts s) x := by
      intro e; rw [e, hlx.2.1, g3] at hup; omega
    simp only [F.liveN, F.ht, F.t1, F.t2, F.srcOf, F.livePar, F.P]
    rw [hchild, hchild, ite_eq_right hvx, ite_eq_right hne, hord _ hv1]
    exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩
  · -- src
    intro u hu hs
    rw [F.liveN] at hu; rw [F.srcOf] at hs ⊢
    rw [F.ghostN, F.t1, F.t2]; exact S.src u hu hs
  · -- tabEnt
    intro X hX e he
    rw [F.isN] at hX; rw [F.ht]; unfold Ent
    by_cases hXc : X ∈ s.cin.getX x
    · obtain ⟨-, hX1, -⟩ := ins_cinX hI hcs hx hXc
      rw [hX1, Nat.sub_self, hord0, hmem]
      rcases (ins_order_mem hI hcs hx F hTP hXc e).mp he with h | h | h
      · have := S.tabEnt X hX e h; unfold Ent at this; rw [hX1, Nat.sub_self, S.ord0] at this
        exact Or.inl this
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [ins_order_old hI hcs hx F hXc] at he
      have := S.tabEnt X hX e he
      unfold Ent at this
      by_cases h1 : ht (ts s) X - 1 = 0
      · rw [h1, hord0]; rw [h1, S.ord0] at this; exact (ins_sub hI hcs hx).subset this
      · rw [hord _ (by omega)]; exact this
  · -- tabsIff
    intro h e X he
    unfold Ent at he
    rw [F.isN, F.ht]
    by_cases h0 : h = 0
    · subst h0
      rw [hord0] at he
      unfold tabs; rw [ite_eq_left rfl, F.cin]
      by_cases hen : e = s.C.size ∨ e = s.C.size + 1
      · rw [ite_eq_left hen]
        change X ∈ s.cin.getX x ↔ _
        constructor
        · intro hXc
          obtain ⟨a1, a2, -⟩ := ins_cinX hI hcs hx hXc
          exact ⟨a1, a2, (ins_order_mem hI hcs hx F hTP hXc e).mpr (Or.inr hen)⟩
        · rintro ⟨a1, a2, a3⟩
          by_contra hXc
          rw [ins_order_old hI hcs hx F hXc] at a3
          have := (S.O1 X a1).subset a3
          rw [a2, Nat.add_sub_cancel, S.ord0] at this
          rcases hen with rfl | rfl
          · exact hy this
          · exact hz this
      · rw [ite_eq_right hen]
        have hecl : e ∈ cl := by
          rcases (hmem e).mp he with h | h | h
          · exact h
          all_goals exact absurd (by tauto) hen
        have hent : Ent ord 0 e := by unfold Ent; rw [S.ord0]; exact hecl
        have hiff := S.tabsIff 0 e X hent
        unfold tabs at hiff; rw [ite_eq_left rfl] at hiff
        rw [hiff]
        have : e ∈ order t X ↔ e ∈ order (ts s) X := by
          by_cases hXc : X ∈ s.cin.getX x
          · rw [ins_order_mem hI hcs hx F hTP hXc]; tauto
          · rw [ins_order_old hI hcs hx F hXc]
        rw [this]
    · rw [hord h (by omega)] at he
      unfold tabs; rw [ite_eq_right h0, F.inTables]
      have hiff := S.tabsIff h e X he
      unfold tabs at hiff; rw [ite_eq_right h0] at hiff
      rw [hiff]
      constructor
      · rintro ⟨a1, a2, a3⟩
        refine ⟨a1, a2, ?_⟩
        rw [ins_order_old hI hcs hx F (hnot X a1 (by omega))]; exact a3
      · rintro ⟨a1, a2, a3⟩
        refine ⟨a1, a2, ?_⟩
        rw [ins_order_old hI hcs hx F (hnot X a1 (by omega))] at a3; exact a3
  · -- tabsNodup
    intro h e he
    unfold Ent at he
    by_cases h0 : h = 0
    · subst h0
      rw [hord0] at he
      have hp := hproj e he
      unfold tabs; rw [ite_eq_left rfl, F.cin]
      have := S.tabsNodup 0 _ (show _ ∈ ord 0 by rw [S.ord0]; exact hp)
      unfold tabs at this; rw [ite_eq_left rfl] at this
      by_cases hen : e = s.C.size ∨ e = s.C.size + 1
      · rw [ite_eq_left hen] at this ⊢; exact this
      · rw [ite_eq_right hen] at this ⊢; exact this
    · rw [hord h (by omega)] at he
      unfold tabs; rw [ite_eq_right h0, F.inTables]
      have := S.tabsNodup h e he
      unfold tabs at this; rw [ite_eq_right h0] at this; exact this
  · -- Q
    intro h e X he hX
    unfold Ent at he
    by_cases h0 : h = 0
    · subst h0
      rw [hord0] at he
      have hp := hproj e he
      unfold tabs at hX; rw [ite_eq_left rfl, F.cin] at hX
      rw [F.par_zero, F.srcOf, hlpr]
      have hQ := S.Q 0 _ X (show _ ∈ ord 0 by rw [S.ord0]; exact hp)
      unfold tabs par at hQ; simp only [] at hQ
      by_cases hen : e = s.C.size ∨ e = s.C.size + 1
      · rw [ite_eq_left hen] at hQ hX ⊢; exact hQ hX
      · rw [ite_eq_right hen] at hQ hX ⊢; exact hQ hX
    · rw [hord h (by omega)] at he
      unfold tabs at hX; rw [ite_eq_right h0, F.inTables] at hX
      rw [F.par_pos (by omega), F.srcOf]
      exact S.Q h e X he (by unfold tabs; rw [ite_eq_right h0]; exact hX)
  · -- W1
    intro v hv X hX
    rw [F.ghostN] at hv
    have hv1 := (S.htN v hv.1).1
    rw [F.ht] at hX
    unfold tabs at hX; rw [ite_eq_right (by omega), F.inTables] at hX
    have hent : Ent ord (ht (ts s) v) v :=
      (S.ordMem _ hv1 (S.htN v hv.1).2 v).mpr ⟨hv.1, rfl⟩
    have hX' : X ∈ tabs (ts s) (ht (ts s) v) v := by unfold tabs; rw [ite_eq_right (by omega)]; exact hX
    obtain ⟨a1, a2, -⟩ := (S.tabsIff _ v X hent).mp hX'
    rw [F.t1, F.t2, ins_order_old hI hcs hx F (hnot X a1 (by omega))]
    exact S.W1 v hv X hX'
  · -- side
    intro v hv e he
    rw [F.ghostN] at hv
    have hv1 := (S.htN v hv.1).1
    rw [F.side, F.ht, F.t1]
    by_cases hXc : v ∈ s.cin.getX x
    · obtain ⟨-, hX1, hxv⟩ := ins_cinX hI hcs hx hXc
      have hvs : v < s.nodes.size := hv.1.2.1
      rw [ite_eq_left ⟨hXc, hvs⟩, hX1, Nat.sub_self, F.par_zero, hlpr]
      unfold sideAround
      have hdr : (s.nodes.getX v).draining = true := hv.2
      rw [ite_eq_left hdr]
      have hsx := S.side v hv x hxv
      rw [hX1, Nat.sub_self] at hsx
      have hsx' : lookup (s.nodes.getX v).side x =
          some (if par (ts s) 0 x = (nd (ts s) v).t1 then Side.left else Side.right) := hsx
      rcases (ins_order_mem hI hcs hx F hTP hXc e).mp he with h | h | h
      · have hen : ¬(e = s.C.size ∨ e = s.C.size + 1) := by
          rintro (rfl | rfl)
          · have := (S.O1 v hv.1).subset h; rw [hX1, Nat.sub_self, S.ord0] at this; exact hy this
          · have := (S.O1 v hv.1).subset h; rw [hX1, Nat.sub_self, S.ord0] at this; exact hz this
        rw [ite_eq_right hen]
        push Not at hen
        rw [lookup_assocSet_ne _ _ _ _ hen.2, lookup_assocSet_ne _ _ _ _ hen.1]
        have := S.side v hv e h
        rw [hX1, Nat.sub_self, show par (ts s) 0 e = lpr (ts s) e by simp [par]] at this
        exact this
      · subst h
        rw [ite_eq_left (Or.inl rfl), lookup_assocSet_ne _ _ _ _ (by omega), lookup_assocSet_eq,
          hsx']
        simp [par]
      · subst h
        rw [ite_eq_left (Or.inr rfl), lookup_assocSet_eq, hsx']
        simp [par]
    · have hvs := ins_order_old hI hcs hx F hXc
      rw [ite_eq_right (fun h => hXc h.1)]
      rw [hvs] at he
      have := S.side v hv e he
      by_cases h1 : ht (ts s) v - 1 = 0
      · rw [h1, F.par_zero, hlpr]
        have hecl : e ∈ cl := by have := (S.O1 v hv.1).subset he; rwa [h1, S.ord0] at this
        have hen : ¬(e = s.C.size ∨ e = s.C.size + 1) := by
          rintro (rfl | rfl)
          · exact hy hecl
          · exact hz hecl
        rw [ite_eq_right hen]; rw [h1, show par (ts s) 0 e = lpr (ts s) e by simp [par]] at this
        exact this
      · rw [F.par_pos (by omega)]; exact this
  · -- pathSize
    intro c hc
    rw [F.P]
    by_cases hcn : c = s.C.size ∨ c = s.C.size + 1
    · exact F.psize c hcn
    · have hc0 := hproj c hc
      rw [ite_eq_right hcn] at hc0
      push Not at hcn
      rw [F.pother c hcn.1 hcn.2]
      exact S.pathSize c hc0
  · -- P
    intro c hc j hj1 hj
    rw [F.P] at hj
    simp only [hpp c j hj1 hj, hanc c j hj1, F.ghostN, F.t1, F.t2]
    exact S.P _ (hproj c hc) j hj1 hj
  · -- Sr
    intro c hc j hj1 hj hg
    rw [F.P] at hj
    rw [hpp c j hj1 hj, F.ghostN] at hg
    rw [hanc c j hj1]
    by_cases hj2 : 2 ≤ j
    · rw [hpp c (j - 1) (by omega) (by omega)]
      exact ins_order_sup hI hcs hx F hTP _ _ (S.Sr _ (hproj c hc) j hj1 hj hg)
    · have e1 : j = 1 := by omega
      subst e1
      have hsr := S.Sr _ (hproj c hc) 1 le_rfl hj hg
      change c ∈ order t (anc (ts s) _ 1)
      by_cases hcn : c = s.C.size ∨ c = s.C.size + 1
      · rw [ite_eq_left hcn] at hsr ⊢
        change x ∈ order (ts s) (lpr (ts s) x) at hsr
        have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
        have hlc : lpr (ts s) x ∈ tabs (ts s) 0 x := (S.tabsIff 0 x _ hent).mpr ⟨hlx.1.1, hlx.2.1, hsr⟩
        unfold tabs at hlc; rw [ite_eq_left rfl] at hlc
        exact (ins_order_mem hI hcs hx F hTP hlc c).mpr (Or.inr hcn)
      · rw [ite_eq_right hcn] at hsr ⊢
        exact ins_order_sup hI hcs hx F hTP _ _ hsr
  · -- ends
    have hxs := (hcs x).mp hx
    have hxy : x ≠ s.C.size := by omega
    have hxz : x ≠ s.C.size + 1 := by omega
    have hfr : ∀ c ∈ A ++ B, c ≠ s.C.size ∧ c ≠ s.C.size + 1 := fun c hc => by
      have : c ∈ cl := by rw [hcl]; simp only [List.mem_append, List.mem_cons] at hc ⊢; tauto
      exact ⟨fun e => hy (e ▸ this), fun e => hz (e ▸ this)⟩
    intro u hu
    rw [F.isN] at hu
    obtain ⟨e1, e2⟩ := S.ends u hu
    obtain ⟨hh1, hhH⟩ := S.htN u hu
    have hpt : ∀ c, decide (pp t c (ht (ts s) u) = u) =
        decide (pp (ts s) (if c = s.C.size ∨ c = s.C.size + 1 then x else c) (ht (ts s) u) = u) :=
      fun c => by rw [hpp c _ hh1 hhH]
    have eA : A.filter (fun c => decide (pp t c (ht (ts s) u) = u)) =
        A.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) :=
      List.filter_congr (fun c hc => by
        rw [hpt, ite_eq_right (by have := hfr c (by simp [hc]); omega)])
    have eB : B.filter (fun c => decide (pp t c (ht (ts s) u) = u)) =
        B.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) :=
      List.filter_congr (fun c hc => by
        rw [hpt, ite_eq_right (by have := hfr c (by simp [hc]); omega)])
    have hry : decide (pp t s.C.size (ht (ts s) u) = u) = decide (pp (ts s) x (ht (ts s) u) = u) := by
      rw [hpt, ite_eq_left (Or.inl rfl)]
    have hrz : decide (pp t (s.C.size + 1) (ht (ts s) u) = u) = decide (pp (ts s) x (ht (ts s) u) = u) := by
      rw [hpt, ite_eq_left (Or.inr rfl)]
    have hrx : decide (pp t x (ht (ts s) u) = u) = decide (pp (ts s) x (ht (ts s) u) = u) := by
      rw [hpt, ite_eq_right (by omega)]
    unfold rng; rw [F.ht, hcl', F.first, F.last]
    unfold rng at e1 e2; rw [hcl] at e1 e2
    simp only [List.filter_append, List.filter_cons, eA, eB, hry, hrz, hrx] at e1 e2 ⊢
    unfold insFirst insLast
    have hfst : (s.nodes.getX u).first = (nd (ts s) u).first := rfl
    have hlst : (s.nodes.getX u).last = (nd (ts s) u).last := rfl
    rw [hfst, hlst, e1, e2]
    have hAx : x ∉ A.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) :=
      fun h => hA (List.mem_of_mem_filter h)
    have hBx : x ∉ B.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) :=
      fun h => hB (List.mem_of_mem_filter h)
    by_cases hPx : pp (ts s) x (ht (ts s) u) = u
    · have hcp : cpHit (insJob s x) s.P.H (ts s) 1 u = true := (cpHit_iff _ _ _ _ _).mpr
        ⟨_, hh1, hhH, by
          have := hPx; simp only [pp, show ht (ts s) u ≠ 0 by omega,
            ite_false] at this; exact this.symm⟩
      have hd : decide (pp (ts s) x (ht (ts s) u) = u) = true := decide_eq_true hPx
      simp only [hd, ite_true, hcp, true_and]
      generalize List.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) A = LA at hAx ⊢
      generalize List.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) B = LB at hBx ⊢
      have k1 := headD_append_cons LA LB x NIL
      have k2 := headD_append_cons LA (x :: (s.C.size + 1) :: LB) s.C.size NIL
      have k3 := getLastD_append_cons LA LB x NIL
      have k4 : (LA ++ s.C.size :: x :: (s.C.size + 1) :: LB).getLastD NIL =
          if LB = [] then s.C.size + 1 else LB.getLastD NIL := by
        rw [show LA ++ s.C.size :: x :: (s.C.size + 1) :: LB = (LA ++ [s.C.size, x]) ++ (s.C.size + 1) :: LB by
          simp]
        exact getLastD_append_cons _ _ _ _
      rw [k1, k2, k3, k4]
      constructor
      · by_cases hLA : LA = []
        · simp [hLA]
        · rw [ite_eq_right hLA, ite_eq_right hLA,
          ite_eq_right (fun (e : LA.headD NIL = x) => hAx (e ▸ headD_mem hLA _))]
      · by_cases hLB : LB = []
        · simp [hLB]
        · rw [ite_eq_right hLB, ite_eq_right hLB,
          ite_eq_right (fun (e : LB.getLastD NIL = x) => hBx (e ▸ getLastD_mem hLB _))]
    · have hd : decide (pp (ts s) x (ht (ts s) u) = u) = false := decide_eq_false hPx
      simp only [hd, Bool.false_eq_true, ite_false]
      generalize List.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) A = LA at hAx ⊢
      generalize List.filter (fun c => decide (pp (ts s) c (ht (ts s) u) = u)) B = LB at hBx ⊢
      have hx0 : x ≠ NIL := by simp [NIL]; omega
      have hnx : x ∉ LA ++ LB := by simp only [List.mem_append, not_or]; exact ⟨hAx, hBx⟩
      constructor
      · rw [ite_eq_right]
        rintro ⟨-, e⟩
        by_cases hL : LA ++ LB = []
        · rw [hL] at e; exact hx0 e.symm
        · exact hnx (e ▸ headD_mem hL _)
      · rw [ite_eq_right]
        rintro ⟨-, e⟩
        by_cases hL : LA ++ LB = []
        · rw [hL] at e; exact hx0 e.symm
        · exact hnx (e ▸ getLastD_mem hL _)
  · exact ins_tags hI hcs hx F hTP hf1 hi1

end shape

end OrderMaintenance.Proof.Top
