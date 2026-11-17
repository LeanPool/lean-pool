/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Labels


/-!
# M5: inserting two entries around one, in every table holding it

`insertAroundIn e n1 n2 (T, a, b)` puts `(n1, a)` right before and `(n2, b)` right after entry
`e` in table `T` (`insertAroundIn_run`); over a list of distinct tables, a fold
(`forM_around_run`). Both `insertAround` (new chunks) and `startDrain` (new targets) do this.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- The side list after inserting `n1`, `n2` around `e`. -/
def sideAround (T : Node) (e n1 n2 : Nat) : List (Nat × Side) :=
  if T.draining then
    assocSet (assocSet T.side n1 ((lookup T.side e).getD .left)) n2 ((lookup T.side e).getD .left)
  else T.side

theorem lookup_map_replace {β : Type} (l : List (Nat × β)) (k k' : Nat) (v : β) (h : k' ≠ k) :
    (List.find? (fun x => x.1 == k') (l.map fun p => if p.1 == k then (k, v) else p)).map (·.2) =
      (List.find? (fun x => x.1 == k') l).map (·.2) := by
  have hkk : (k == k') = false := by simpa using Ne.symm h
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hp : p.1 = k
    · simp only [hp, beq_self_eq_true, ite_true, hkk]
      rw [← hp] at ih ⊢; exact ih
    · simp only [show (p.1 == k) = false by simpa using hp, Bool.false_eq_true, ite_false]
      split <;> [rfl; exact ih]

theorem lookup_assocSet_eq {β : Type} (l : List (Nat × β)) (k : Nat) (v : β) :
    lookup (assocSet l k v) k = some v := by
  unfold assocSet lookup
  split
  · rename_i h
    induction l with
    | nil => simp at h
    | cons p r ih =>
      obtain ⟨a, b⟩ := p
      by_cases hak : a = k
      · subst hak; simp
      · have h' : r.any (·.1 == k) = true := by simpa [hak] using h
        have := ih h'
        simpa [hak] using this
  · rename_i h
    have hn : List.find? (fun x => x.1 == k) l = none := by
      rw [List.find?_eq_none]; intro x hx
      simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at h
      simpa using h x hx
    simp [List.find?_append, hn]

theorem lookup_append_cons_self {β : Type} {A R : List (Nat × β)} {k : Nat} {v : β}
    (hA : k ∉ A.map (·.1)) : lookup (A ++ (k, v) :: R) k = some v := by
  unfold lookup
  have hn : List.find? (fun p => p.1 == k) A = none := by
    rw [List.find?_eq_none]; intro p hp
    have : p.1 ≠ k := fun e => hA (List.mem_map.mpr ⟨p, hp, e⟩)
    simpa using this
  simp [List.find?_append, hn]

theorem lookup_around {β : Type} (A B : List (Nat × β)) {k y z x : Nat} {a le b : β}
    (hy : k ≠ y) (hz : k ≠ z) :
    lookup (A ++ (y, a) :: (x, le) :: (z, b) :: B) k = lookup (A ++ (x, le) :: B) k := by
  unfold lookup
  have h1 : (y == k) = false := by simpa using Ne.symm hy
  have h2 : (z == k) = false := by simpa using Ne.symm hz
  simp only [List.find?_append, List.find?_cons, h1, h2]

theorem idx?_getD_map {l : List Nat} {a i : Nat} (h : l.idx? a = some i) (g : Nat → Nat) :
    (l.map g).getD i 0 = g a := by
  unfold List.idx? at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, hp, -⟩ := h
  have ha : l[i] = a := by simpa using hp
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  simp [ha]

theorem lookup_assocSet_ne {β : Type} (l : List (Nat × β)) (k k' : Nat) (v : β) (h : k' ≠ k) :
    lookup (assocSet l k v) k' = lookup l k' := by
  unfold assocSet lookup
  have hkk : (k == k') = false := by simpa using Ne.symm h
  split
  · exact lookup_map_replace l k k' v h
  · simp only [List.find?_append, List.find?_cons, hkk, List.find?_nil]
    cases (List.find? (fun x => x.1 == k') l) <;> rfl

/-- The table of `T` after `insertAroundIn`. -/
def aroundTab (A Bs : List (Nat × Nat)) (e le n1 n2 a b : Nat) : List (Nat × Nat) :=
  A ++ (n1, a) :: (e, le) :: (n2, b) :: Bs

theorem insertAroundIn_run {s : Core} {e n1 n2 T a b : Nat} {A Bs : List (Nat × Nat)} {le : Nat}
    (htab : (s.nodes.getX T).table = A ++ (e, le) :: Bs) (hA : e ∉ A.map (·.1)) (hn1 : n1 ≠ e)
    (hside : (s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side e).isSome) :
    (insertAroundIn e n1 n2 (T, a, b)).run s = .ok ⟨⟩ { s with nodes := s.nodes.modify T (setTS
      (aroundTab A Bs e le n1 n2 a b) (sideAround (s.nodes.getX T) e n1 n2)) } := by
  unfold insertAroundIn
  rw [run_bind, tableInsert_run htab hA true a hside]
  have hT : T < s.nodes.size := by
    by_contra h
    have : s.nodes.getX T = default := by unfold Array.getX Array.getD; rw [dite_eq_right h]
    have hd : (default : Node).table = [] := rfl
    rw [this, hd] at htab; exact absurd htab.symm (by simp)
  set s1 : Core := { s with nodes := s.nodes.modify T (setTS (insTab A Bs e le n1 a true)
    (sideAfter (s.nodes.getX T) e n1)) } with hs1
  have h1 : s1.nodes.getX T = setTS (insTab A Bs e le n1 a true) (sideAfter (s.nodes.getX T) e
    n1) (s.nodes.getX T) := by
    rw [hs1]; change (s.nodes.modify T _).getX T = _; rw [Array.getX_modify, ite_eq_left ⟨rfl, hT⟩]
  have htab1 : (s1.nodes.getX T).table = (A ++ [(n1, a)]) ++ (e, le) :: Bs := by
    rw [h1]; simp [setTS, insTab]
  have hA1 : e ∉ (A ++ [(n1, a)]).map (·.1) := by simp [hA, Ne.symm hn1]
  have hside1 : (s1.nodes.getX T).draining = true → (lookup (s1.nodes.getX T).side e).isSome := by
    rw [h1]; simp only [setTS]; intro hd
    unfold sideAfter; rw [ite_eq_left hd, lookup_assocSet_ne _ _ _ _ hn1.symm]; exact hside hd
  change (tableInsert T e n2 false b).run s1 = _
  rw [tableInsert_run htab1 hA1 false b hside1]
  congr 1
  have hside2 : sideAfter (s1.nodes.getX T) e n2 = sideAround (s.nodes.getX T) e n1 n2 := by
    rw [h1]; unfold sideAfter sideAround setTS
    by_cases hd : (s.nodes.getX T).draining = true
    · simp only [hd, ite_true]; rw [lookup_assocSet_ne _ _ _ _ hn1.symm]
    · simp only [hd, Bool.false_eq_true, ite_false]
  have htab2 : insTab (A ++ [(n1, a)]) Bs e le n2 b false = aroundTab A Bs e le n1 n2 a b := by
    simp [insTab, aroundTab]
  rw [hside2, htab2]
  simp only [hs1]
  congr 1
  apply Array.ext
  · simp
  · intro i _ _
    simp only [Array.getElem_modify]
    split <;> rfl

theorem foldl_ext {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | x :: t, init, h => by
    simp only [List.foldl_cons]
    rw [h x (by simp) init]
    exact foldl_ext t _ fun y hy acc => h y (List.mem_cons_of_mem _ hy) acc

/-- `aroundTab`, computed from the table itself. -/
def aroundT (tab : List (Nat × Nat)) (e n1 n2 a b : Nat) : List (Nat × Nat) :=
  let i := (tab.findIdx? (·.1 == e)).getD 0
  (tab.insertIdx (i + 1) (n2, b)).insertIdx i (n1, a)

theorem aroundT_eq {A Bs : List (Nat × Nat)} {e le n1 n2 a b : Nat} (hA : e ∉ A.map (·.1)) :
    aroundT (A ++ (e, le) :: Bs) e n1 n2 a b = aroundTab A Bs e le n1 n2 a b := by
  unfold aroundT aroundTab
  simp only [findIdx_split hA, Option.getD_some]
  rw [insertIdx_len1, insertIdx_len]

/-- The update `insertAroundIn` makes to table `T`. -/
def aroundF (s : Core) (e n1 n2 : Nat) (f : Nat → Nat × Nat) (T : Nat) : Node → Node :=
  setTS (aroundT (s.nodes.getX T).table e n1 n2 (f T).1 (f T).2) (sideAround (s.nodes.getX T) e
    n1 n2)

/-- Entry `e` is in table `T`, once (as the table's keys are distinct). -/
def AroundOK (s : Core) (e T : Nat) : Prop :=
  ∃ A le Bs, (s.nodes.getX T).table = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) ∧
    ((s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side e).isSome)

/-- **Insertions around `e` in a list of distinct tables.** -/
theorem forM_around_run (e n1 n2 : Nat) (f : Nat → Nat × Nat) (hne : n1 ≠ e) :
    ∀ (tbs : List Nat) (s : Core), tbs.Nodup → (∀ T ∈ tbs, AroundOK s e T) →
      ((tbs.map fun T => (T, f T)).forM (insertAroundIn e n1 n2)).run s =
        .ok ⟨⟩ {
          s with
          nodes := tbs.foldl (fun ns T => ns.modify T (aroundF s e n1 n2 f T)) s.nodes }
  | [], s, _, _ => rfl
  | T :: rest, s, hnd, hok => by
    have hT := List.nodup_cons.mp hnd
    obtain ⟨A, le, Bs, htab, hA, hside⟩ := hok T (by simp)
    change (do
      insertAroundIn e n1 n2 (T, f T)
      (rest.map fun T => (T, f T)).forM (insertAroundIn e n1 n2)).run s = _
    rw [run_bind, insertAroundIn_run htab hA hne hside]
    simp only
    set s1 : Core := { s with nodes := s.nodes.modify T (setTS (aroundTab A Bs e le n1 n2 (f
      T).1 (f T).2) (sideAround (s.nodes.getX T) e n1 n2)) } with hs1
    have hsame : ∀ T', T' ≠ T → s1.nodes.getX T' = s.nodes.getX T' := fun T' h => by
      rw [hs1]; change (s.nodes.modify T _).getX T' = _; rw [Array.getX_modify, ite_eq_right
        (fun h' => h h'.1.symm)]
    have hok1 : ∀ T' ∈ rest, AroundOK s1 e T' := fun T' hT' => by
      have hne' : T' ≠ T := fun h => hT.1 (h ▸ hT')
      unfold AroundOK; rw [hsame T' hne']; exact hok T' (by simp [hT'])
    rw [forM_around_run e n1 n2 f hne rest s1 hT.2 hok1]
    congr 1
    simp only [hs1, List.foldl_cons]
    have hTF : aroundF s e n1 n2 f T = setTS (aroundTab A Bs e le n1 n2 (f T).1 (f T).2)
        (sideAround (s.nodes.getX T) e n1 n2) := by
      unfold aroundF; rw [htab, aroundT_eq hA]
    rw [hTF]
    congr 1
    apply foldl_ext
    intro T' hT' acc
    have hne' : T' ≠ T := fun h => hT.1 (h ▸ hT')
    unfold aroundF; rw [hsame T' hne']

/-! ### `insertAround` -/

/-- The label `roomNextTo` picks, computed from the table. -/
def roomL (β : Nat) (tab : List (Nat × Nat)) (e : Nat) (before : Bool) : Nat :=
  let i := (tab.findIdx? (·.1 == e)).getD 0
  (roomLo (tab.take i) (tab.getD i (0, 0)).2 before +
    roomHi β (tab.drop (i + 1)) (tab.getD i (0, 0)).2 before - 1) / 2

theorem roomL_eq {β : Nat} {A Bs : List (Nat × Nat)} {e le : Nat} (hA : e ∉ A.map (·.1))
    (before : Bool) : roomL β (A ++ (e, le) :: Bs) e before =
      (roomLo A le before + roomHi β Bs le before - 1) / 2 := by
  unfold roomL
  simp only [findIdx_split hA, Option.getD_some, getD_split_mid, List.take_left',
    show A.length + 1 = (A ++ [(e, le)]).length by simp]
  rw [show A ++ (e, le) :: Bs = (A ++ [(e, le)]) ++ Bs by simp, List.drop_left]

/-- The table of `T` has room on both sides of `e`. -/
def RoomOK (s : Core) (e T : Nat) : Prop :=
  ∃ A le Bs, (s.nodes.getX T).table = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) ∧
    ((s.nodes.getX T).draining = true → (lookup (s.nodes.getX T).side e).isSome) ∧
    roomLo A le true < roomHi s.P.beta Bs le true ∧ roomLo A le false < roomHi s.P.beta Bs le false

theorem RoomOK.around {s : Core} {e T : Nat} (h : RoomOK s e T) : AroundOK s e T := by
  obtain ⟨A, le, Bs, h1, h2, h3, -⟩ := h; exact ⟨A, le, Bs, h1, h2, h3⟩

theorem roomNextTo_run' {s : Core} {e T : Nat} (h : RoomOK s e T) (before : Bool) :
    (roomNextTo T e before).run s = .ok (roomL s.P.beta (s.nodes.getX T).table e before) s := by
  obtain ⟨A, le, Bs, htab, hA, -, h1, h2⟩ := h
  rw [roomNextTo_run htab hA before (by cases before <;> assumption), htab, roomL_eq hA]

theorem zip_map_self {α β : Type} (l : List α) (f : α → β) : l.zip (l.map f) = l.map fun x =>
  (x, f x) := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [ih]

/-- **Running `insertAroundPrep`.** -/
theorem insertAroundPrep_run {s : Core} {x f1x i1 : Nat}
    (hroom : ∀ T ∈ s.cin.getX x, RoomOK s x T)
    (hf1 : (s.nodes.getX ((s.path.getX x).getX 1)).lab? x = some f1x)
    (hi1 : (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1)
    (htx : f1x ≤ (s.C.getX x).tag)
    (hlp : x ∈ (s.nodes.getX (s.lpar.getX x)).children) :
    let ly := (s.cin.getX x).map fun T => roomL s.P.beta (s.nodes.getX T).table x true
    let lz := (s.cin.getX x).map fun T => roomL s.P.beta (s.nodes.getX T).table x false
    (insertAroundPrep x).run s = .ok ((s.C.getX x).tag - f1x + ly.getD i1 0,
      (s.C.getX x).tag - f1x + lz.getD i1 0, s.cin.getX x, ly, lz, s.lpar.getX x) s := by
  intro ly lz
  unfold insertAroundPrep
  simp only [run_getPath_bind, run_get_bind]
  rw [run_bind, mapM_run _ _ (fun T => roomL s.P.beta (s.nodes.getX T).table x true) s
    (fun T hT => roomNextTo_run' (hroom T hT) true)]
  simp only
  rw [run_bind, mapM_run _ _ (fun T => roomL s.P.beta (s.nodes.getX T).table x false) s
    (fun T hT => roomNextTo_run' (hroom T hT) false)]
  simp only [run_getN_bind, hf1, hi1, run_getC_bind, ite_eq_right (Nat.not_lt.mpr htx),
    run_getLpar_bind]
  have : (s.nodes.getX (s.lpar.getX x)).children.contains x = true := List.elem_iff.mpr hlp
  simp only [this, Bool.not_true, Bool.false_eq_true, ite_false, run_pure]
  rfl

/-- `joinChunk`, as a state update. -/
def joinS (s : Core) (tabs : List Nat) (lp c : Nat) : Core :=
  { s with
    path := s.path.setX c (Array.replicate (s.P.H + 1) NIL)
    cin := s.cin.setX c tabs
    lpar := s.lpar.setX c lp }

theorem joinChunk_run (s : Core) (tabs : List Nat) (lp c : Nat) :
    (joinChunk tabs lp c).run s = .ok ⟨⟩ (joinS s tabs lp c) := by
  unfold joinChunk setPath setInTables setLpar
  simp only [run_getP_bind, run_modify_bind, beq_self_eq_true, ite_true, run_modify]
  rfl

/-- The state after `insertAroundFinish`. -/
def insFinS (s : Core) (x y z : Nat) (f : Nat → Nat × Nat) : Core :=
  let tabs := s.cin.getX x
  let lp := s.lpar.getX x
  let s1 := { s with nodes := tabs.foldl (fun ns T => ns.modify T (aroundF s x y z f T)) s.nodes }
  let s3 := joinS (joinS s1 tabs lp y) tabs lp z
  { s3 with
    nodes := s3.nodes.modify lp fun n => { n with children := n.children.replace1 x [y, x, z] } }

theorem insertAroundFinish_run {s : Core} {x y z : Nat} (g1 g2 : Nat → Nat) (hyx : y ≠ x)
    (hnd : (s.cin.getX x).Nodup) (hok : ∀ T ∈ s.cin.getX x, AroundOK s x T) :
    (insertAroundFinish x y z (s.cin.getX x) ((s.cin.getX x).map g1) ((s.cin.getX x).map g2)
      (s.lpar.getX x)).run s =
      .ok { x := x, y := y, z := z, pc := .copy 1 } (insFinS s x y z fun T => (g1 T, g2 T)) := by
  unfold insertAroundFinish insFinS
  have hz : ((s.cin.getX x).map g1).zip ((s.cin.getX x).map g2) =
      (s.cin.getX x).map fun T => (g1 T, g2 T) := by
    induction s.cin.getX x with
    | nil => rfl
    | cons a t ih => simp [ih]
  rw [hz, zip_map_self, run_bind, forM_around_run x y z _ hyx _ s hnd hok]
  simp only
  rw [run_bind, joinChunk_run]; simp only
  rw [run_bind, joinChunk_run]; simp only
  rw [run_modN_bind]
  rfl

/-- The tags written by `insertAround`. -/
def tagY (s : Core) (x f1x i1 : Nat) : Nat :=
  (s.C.getX x).tag - f1x + ((s.cin.getX x).map fun T => roomL s.P.beta (s.nodes.getX T).table x
    true).getD i1 0
/-- The tag assigned to the new chunk immediately after the split chunk. -/
def tagZ (s : Core) (x f1x i1 : Nat) : Nat :=
  (s.C.getX x).tag - f1x + ((s.cin.getX x).map fun T => roomL s.P.beta (s.nodes.getX T).table x
    false).getD i1 0

/-- The core after both tag writes. -/
def tagsS (s : Core) (y z ty tz : Nat) : Core :=
  { s with
    C := (s.C.modify y fun C => { C with tag := ty }).modify z fun C => { C with tag := tz } }

/-- **Running `insertAround`.** -/
theorem insertAround_run {s : Core} {x y z f1x i1 : Nat}
    (hroom : ∀ T ∈ s.cin.getX x, RoomOK s x T) (hnd : (s.cin.getX x).Nodup) (hyx : y ≠ x)
    (hf1 : (s.nodes.getX ((s.path.getX x).getX 1)).lab? x = some f1x)
    (hi1 : (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1)
    (htx : f1x ≤ (s.C.getX x).tag)
    (hlp : x ∈ (s.nodes.getX (s.lpar.getX x)).children)
    (hgy : TagOK s y (tagY s x f1x i1))
    (hgz : TagOK { s with C := s.C.modify y fun C => { C with tag := tagY s x f1x i1 } } z (tagZ
      s x f1x i1)) :
    (insertAround x y z).run s = .ok { x := x, y := y, z := z, pc := .copy 1 }
      (insFinS (tagsS s y z (tagY s x f1x i1) (tagZ s x f1x i1)) x y z
        fun T => (roomL s.P.beta (s.nodes.getX T).table x true,
          roomL s.P.beta (s.nodes.getX T).table x false)) := by
  unfold insertAround
  rw [run_bind, insertAroundPrep_run hroom hf1 hi1 htx hlp]
  simp only
  unfold tagY at hgy hgz; unfold tagZ at hgz
  rw [guardedSetTag_bind hgy, guardedSetTag_bind hgz]
  exact insertAroundFinish_run (s := tagsS s y z (tagY s x f1x i1) (tagZ s x f1x i1))
    (fun T => roomL s.P.beta (s.nodes.getX T).table x true)
    (fun T => roomL s.P.beta (s.nodes.getX T).table x false) hyx hnd
    (fun T hT => (hroom T hT).around)

end OrderMaintenance.Proof.Top
