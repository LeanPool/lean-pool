/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3511T1SourceDissection

-- [TABLET NODE: P3511T1LeafOrder]

/-!
# P3511T1LeafOrder

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DissectionLeafOrderConstruction

private noncomputable abbrev Face (α : Type) := Fin 3 → α

private noncomputable abbrev edges {α : Type} (l : List α) : List (α × α) := by
  classical
  exact List.zipWith Prod.mk l (l.rotate 1)

private theorem edges_cons {α : Type} (a : α) (l : List α) :
      edges (a :: l) = List.zipWith Prod.mk (a :: l) (l ++ [a]) := by
  classical
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  change (edges (a :: l) = List.zipWith Prod.mk (a :: l) (l ++ [a]))
  simp [edges]

private theorem path_split {α : Type} (a b z : α) (u v : List α) :
      List.zipWith Prod.mk (a :: (u ++ b :: v)) ((u ++ b :: v) ++ [z]) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++
          List.zipWith Prod.mk (b :: v) (v ++ [z]) := by
  classical
  induction u generalizing a with
  | nil => simp
  | cons c u ih => simpa using congrArg (fun l => (a, c) :: l) (ih c)

private theorem edges_split {α : Type} (a b : α) (u v : List α) :
      edges (a :: (u ++ b :: v)) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++
          List.zipWith Prod.mk (b :: v) (v ++ [a]) := by
  classical
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  have edges_cons {α : Type} (a : α) (l : List α) :
      edges (a :: l) = List.zipWith Prod.mk (a :: l) (l ++ [a]) := edges_cons (α := α) a l
  have path_split {α : Type} (a b z : α) (u v : List α) :
      List.zipWith Prod.mk (a :: (u ++ b :: v)) ((u ++ b :: v) ++ [z]) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++
          List.zipWith Prod.mk (b :: v) (v ++ [z]) := path_split (α := α) a b z u v
  change (edges (a :: (u ++ b :: v)) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++
          List.zipWith Prod.mk (b :: v) (v ++ [a]))
  rw [edges_cons, path_split]

private theorem edges_arc {α : Type} (a b : α) (u : List α) :
      edges (a :: (u ++ [b])) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ [(b, a)] := by
  classical
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  have edges_split {α : Type} (a b : α) (u v : List α) :
      edges (a :: (u ++ b :: v)) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++
          List.zipWith Prod.mk (b :: v) (v ++ [a]) := edges_split (α := α) a b u v
  change (edges (a :: (u ++ [b])) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ [(b, a)])
  simpa using edges_split a b u []

private theorem edges_rotate {α : Type} (l : List α) (k : Nat) :
      edges (l.rotate k) = (edges l).rotate k := by
  classical
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  change (edges (l.rotate k) = (edges l).rotate k)
  simp only [edges]
  rw [List.zipWith_rotate_distrib _ _ _ _ (List.length_rotate _ _).symm]
  congr 1
  rw [List.rotate_rotate, List.rotate_rotate, Nat.add_comm]

private theorem edges_members {α : Type} {l : List α} {a b : α}
      (h : (a, b) ∈ edges l) : a ∈ l ∧ b ∈ l := by
  classical
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  have hil : i < l.length := lt_of_lt_of_le hi (by simp [])
  have hir : i < (l.rotate 1).length := by simpa using hil
  have hab : (l[i], (l.rotate 1)[i]) = (a, b) := by
    simpa [edges] using he
  have ha := congrArg Prod.fst hab
  have hb := congrArg Prod.snd hab
  change l[i] = a at ha
  change (l.rotate 1)[i] = b at hb
  exact ⟨ha ▸ List.getElem_mem hil, List.mem_rotate.mp (hb ▸ List.getElem_mem hir)⟩

private theorem supported {α : Type} {l : List α} {fs : List (Face α)}
      (h : P3511T1CyclicDissection α l fs) :
      ∀ f ∈ fs, ∀ x ∈ Set.range f, x ∈ l := by
  classical
  induction h with
  | triangle a b c =>
    intro f hf x hx
    simp only [List.mem_singleton] at hf
    subst f
    obtain ⟨i, rfl⟩ := hx
    fin_cases i <;> simp
  | split a b u v left right hu hv hl hr ihl ihr =>
    intro f hf x hx
    rcases List.mem_append.mp hf with hf | hf
    · have := ihl f hf x hx
      simp only [List.mem_cons, List.mem_append] at this ⊢
      tauto
    · have := ihr f hf x hx
      simp only [List.mem_cons, List.mem_append] at this ⊢
      tauto
  | rotate l fs k h ih =>
    intro f hf x hx
    exact List.mem_rotate.mp (ih f hf x hx)

private noncomputable abbrev Shell {α : Type} (fs : List (Face α)) : Prop := by
  classical
  let Face (α : Type) := Fin 3 → α
  exact ∀ pre f post, fs = pre ++ f :: post → pre ≠ [] →
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Set.range f = {a, b, c} ∧
        (∀ g ∈ pre, c ∉ Set.range g) ∧
        ∃ g ∈ pre, a ∈ Set.range g ∧ b ∈ Set.range g

private theorem triple_pair {α : Type} {f : Face α} (hf : Function.Injective f)
      {a b : α} (hab : a ≠ b) (ha : a ∈ Set.range f) (hb : b ∈ Set.range f) :
      ∃ c, a ≠ c ∧ b ≠ c ∧ Set.range f = {a, b, c} := by
  classical
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have hij : i ≠ j := fun h => hab (congrArg f h)
  have hrange : Set.range f = {f 0, f 1, f 2} := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp_all only [Fin.zero_eta, Fin.isValue, ne_eq, Fin.mk_one, Fin.reduceFinMk,
      not_true_eq_false]
  · exact ⟨f 2, hf.ne (by decide), hf.ne (by decide), rfl⟩
  · refine ⟨f 1, hf.ne (by decide), hf.ne (by decide), ?_⟩
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · refine ⟨f 2, hf.ne (by decide), hf.ne (by decide), ?_⟩
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · refine ⟨f 0, hf.ne (by decide), hf.ne (by decide), ?_⟩
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · refine ⟨f 1, hf.ne (by decide), hf.ne (by decide), ?_⟩
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  · refine ⟨f 0, hf.ne (by decide), hf.ne (by decide), ?_⟩
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

private theorem split_lists {α : Type} {a b : α} {u v : List α}
      (hn : (a :: (u ++ b :: v)).Nodup) :
      (a :: (u ++ [b])).Nodup ∧ (b :: (v ++ [a])).Nodup ∧ a ≠ b ∧
        (∀ x, x ∈ a :: (u ++ [b]) → x ∈ b :: (v ++ [a]) → x = a ∨ x = b) := by
  classical
  simp only [List.nodup_cons, List.nodup_append, List.mem_append,
    List.mem_cons] at hn ⊢
  grind

private theorem shell_join {α : Type} {left : List (Face α)} {r : Face α}
      {tail : List (Face α)} {a b : α}
      (hl : Shell left) (hr : Shell (r :: tail))
      (hab : a ≠ b) (hir : Function.Injective r)
      (ha : a ∈ Set.range r) (hb : b ∈ Set.range r)
      (hattach : ∃ g ∈ left, a ∈ Set.range g ∧ b ∈ Set.range g)
      (hsep : ∀ g ∈ left, ∀ f ∈ r :: tail, ∀ x,
        x ∈ Set.range g → x ∈ Set.range f → x = a ∨ x = b) :
      Shell (left ++ r :: tail) := by
  classical
  let Face (α : Type) := Fin 3 → α
  let Shell {α : Type} (fs : List (Face α)) : Prop :=
    ∀ pre f post, fs = pre ++ f :: post → pre ≠ [] →
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Set.range f = {a, b, c} ∧
        (∀ g ∈ pre, c ∉ Set.range g) ∧
        ∃ g ∈ pre, a ∈ Set.range g ∧ b ∈ Set.range g
  have triple_pair {α : Type} {f : Face α} (hf : Function.Injective f)
      {a b : α} (hab : a ≠ b) (ha : a ∈ Set.range f) (hb : b ∈ Set.range f) :
      ∃ c, a ≠ c ∧ b ≠ c ∧ Set.range f = {a, b, c} := triple_pair (α := α) (f := f) hf (a := a)
          (b := b) hab ha hb
  change (Shell (left ++ r :: tail))
  have hfirst (post : List (Face α)) (he : r :: tail = r :: post) :
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Set.range r = {a, b, c} ∧
        (∀ g ∈ left, c ∉ Set.range g) ∧
        ∃ g ∈ left, a ∈ Set.range g ∧ b ∈ Set.range g := by
    obtain ⟨c, hac, hbc, hset⟩ := triple_pair hir hab ha hb
    refine ⟨a, b, c, hab, hac, hbc, hset, ?_, hattach⟩
    intro g hg hc
    have hcr : c ∈ Set.range r := by rw [hset]; simp
    rcases hsep g hg r (by simp) c hc hcr with h | h
    · exact hac h.symm
    · exact hbc h.symm
  intro pre f post he hp
  rcases List.append_eq_append_iff.mp he with ⟨mid, hpre, hright⟩ | ⟨mid, hleft, hrest⟩
  · cases mid with
    | nil =>
      simp only [List.append_nil] at hpre
      simp only [List.nil_append, List.cons.injEq] at hright
      obtain ⟨rfl, htail⟩ := hright
      subst pre
      exact hfirst post (by simp [htail])
    | cons q mid =>
      obtain ⟨x, y, c, hxy, hxc, hyc, hfset, hnew, hg⟩ :=
        hr (q :: mid) f post hright (by simp)
      have hq : q = r := by simpa using (List.cons.inj hright).1.symm
      have hroot : r ∈ q :: mid := by simp [hq]
      have hca : c ≠ a := by
        intro h; subst c; exact hnew r hroot ha
      have hcb : c ≠ b := by
        intro h; subst c; exact hnew r hroot hb
      refine ⟨x, y, c, hxy, hxc, hyc, hfset, ?_, ?_⟩
      · intro g hg hc
        rw [hpre] at hg
        rcases List.mem_append.mp hg with hg | hg
        · have hcf : c ∈ Set.range f := by rw [hfset]; simp
          have hfm : f ∈ r :: tail := by rw [hright]; simp
          rcases hsep g hg f hfm c hc hcf with h | h
          · exact hca h
          · exact hcb h
        · exact hnew g hg hc
      · obtain ⟨g, hg, hx, hy⟩ := hg
        exact ⟨g, by rw [hpre]; exact List.mem_append_right _ hg, hx, hy⟩
  · cases mid with
    | nil =>
      simp only [List.append_nil] at hleft
      simp only [List.nil_append, List.cons.injEq] at hrest
      obtain ⟨rfl, htail⟩ := hrest
      subst pre
      exact hfirst post (by simp [htail])
    | cons q mid =>
      have hq : f = q := (List.cons.inj hrest).1
      subst q
      exact hl pre f mid hleft hp

private theorem rooted {α : Type} {l : List α} {fs : List (Face α)}
      (h : P3511T1CyclicDissection α l fs) (hn : l.Nodup)
      (hi : ∀ f ∈ fs, Function.Injective f) :
      ∀ x y, (x, y) ∈ edges l →
        ∃ r tail, (r :: tail).Perm fs ∧ x ∈ Set.range r ∧ y ∈ Set.range r ∧
          Shell (r :: tail) := by
  classical
  let Face (α : Type) := Fin 3 → α
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  have edges_split {α : Type} (a b : α) (u v : List α) :
      edges (a :: (u ++ b :: v)) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++
          List.zipWith Prod.mk (b :: v) (v ++ [a]) := edges_split (α := α) a b u v
  have edges_arc {α : Type} (a b : α) (u : List α) :
      edges (a :: (u ++ [b])) =
        List.zipWith Prod.mk (a :: u) (u ++ [b]) ++ [(b, a)] := edges_arc (α := α) a b u
  have edges_rotate {α : Type} (l : List α) (k : Nat) :
      edges (l.rotate k) = (edges l).rotate k := edges_rotate (α := α) l k
  have edges_members {α : Type} {l : List α} {a b : α}
      (h : (a, b) ∈ edges l) : a ∈ l ∧ b ∈ l := edges_members (α := α) (l := l) (a := a) (b := b) h
  have supported {α : Type} {l : List α} {fs : List (Face α)}
      (h : P3511T1CyclicDissection α l fs) :
      ∀ f ∈ fs, ∀ x ∈ Set.range f, x ∈ l := supported (α := α) (l := l) (fs := fs) h
  let Shell {α : Type} (fs : List (Face α)) : Prop :=
    ∀ pre f post, fs = pre ++ f :: post → pre ≠ [] →
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Set.range f = {a, b, c} ∧
        (∀ g ∈ pre, c ∉ Set.range g) ∧
        ∃ g ∈ pre, a ∈ Set.range g ∧ b ∈ Set.range g
  have split_lists {α : Type} {a b : α} {u v : List α}
      (hn : (a :: (u ++ b :: v)).Nodup) :
      (a :: (u ++ [b])).Nodup ∧ (b :: (v ++ [a])).Nodup ∧ a ≠ b ∧
        (∀ x, x ∈ a :: (u ++ [b]) → x ∈ b :: (v ++ [a]) → x = a ∨ x = b) := split_lists (α := α)
            (a := a) (b := b) (u := u) (v := v) hn
  have shell_join {α : Type} {left : List (Face α)} {r : Face α}
      {tail : List (Face α)} {a b : α}
      (hl : Shell left) (hr : Shell (r :: tail))
      (hab : a ≠ b) (hir : Function.Injective r)
      (ha : a ∈ Set.range r) (hb : b ∈ Set.range r)
      (hattach : ∃ g ∈ left, a ∈ Set.range g ∧ b ∈ Set.range g)
      (hsep : ∀ g ∈ left, ∀ f ∈ r :: tail, ∀ x,
        x ∈ Set.range g → x ∈ Set.range f → x = a ∨ x = b) :
      Shell (left ++ r :: tail) := shell_join (α := α) (left := left) (r := r) (tail := tail) (a
          := a) (b := b) hl hr hab hir ha hb hattach hsep
  change (∀ x y, (x, y) ∈ edges l →
        ∃ r tail, (r :: tail).Perm fs ∧ x ∈ Set.range r ∧ y ∈ Set.range r ∧
          Shell (r :: tail))
  induction h with
  | triangle a b c =>
    intro x y hxy
    have hm := edges_members hxy
    refine ⟨![a, b, c], [], List.Perm.refl _, ?_, ?_, ?_⟩
    · simpa [Set.mem_range, Fin.exists_fin_succ, eq_comm,
        or_comm, or_left_comm, or_assoc] using hm.1
    · simpa [Set.mem_range, Fin.exists_fin_succ, eq_comm,
        or_comm, or_left_comm, or_assoc] using hm.2
    · intro pre f post he hp
      have hlen := congrArg List.length he
      have hpos : 0 < pre.length := List.length_pos_iff.mpr hp
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      omega
  | split a b u v left right hu hv hl hr ihl ihr =>
    obtain ⟨hnl, hnr, hab, hover⟩ := split_lists hn
    have hil : ∀ f ∈ left, Function.Injective f :=
      fun f hf => hi f (List.mem_append_left _ hf)
    have hir : ∀ f ∈ right, Function.Injective f :=
      fun f hf => hi f (List.mem_append_right _ hf)
    have hba : (b, a) ∈ edges (a :: (u ++ [b])) := by rw [edges_arc]; simp
    have habr : (a, b) ∈ edges (b :: (v ++ [a])) := by rw [edges_arc]; simp
    have hpairl : ∃ g ∈ left, a ∈ Set.range g ∧ b ∈ Set.range g := by
      obtain ⟨r, tail, hp, hb, ha, hs⟩ := ihl hnl hil b a hba
      exact ⟨r, hp.mem_iff.mp (by simp), ha, hb⟩
    have hpairr : ∃ g ∈ right, a ∈ Set.range g ∧ b ∈ Set.range g := by
      obtain ⟨r, tail, hp, ha, hb, hs⟩ := ihr hnr hir a b habr
      exact ⟨r, hp.mem_iff.mp (by simp), ha, hb⟩
    intro x y hxy
    rw [edges_split] at hxy
    rcases List.mem_append.mp hxy with hxy | hxy
    · have hxy' : (x, y) ∈ edges (a :: (u ++ [b])) := by
        rw [edges_arc]; exact List.mem_append_left _ hxy
      obtain ⟨rl, tl, hpl, hx, hy, hsl⟩ := ihl hnl hil x y hxy'
      obtain ⟨rr, tr, hpr, ha, hb, hsr⟩ := ihr hnr hir a b habr
      refine ⟨rl, tl ++ rr :: tr, ?_, hx, hy, ?_⟩
      · exact hpl.append hpr
      · apply shell_join hsl hsr hab (hir rr (hpr.mem_iff.mp (by simp))) ha hb
        · obtain ⟨g, hg, hga, hgb⟩ := hpairl
          exact ⟨g, hpl.mem_iff.mpr hg, hga, hgb⟩
        · intro g hg f hf z hzg hzf
          exact hover z (supported hl g (hpl.mem_iff.mp hg) z hzg)
            (supported hr f (hpr.mem_iff.mp hf) z hzf)
    · have hxy' : (x, y) ∈ edges (b :: (v ++ [a])) := by
        rw [edges_arc]; exact List.mem_append_left _ hxy
      obtain ⟨rr, tr, hpr, hx, hy, hsr⟩ := ihr hnr hir x y hxy'
      obtain ⟨rl, tl, hpl, hb, ha, hsl⟩ := ihl hnl hil b a hba
      refine ⟨rr, tr ++ rl :: tl, ?_, hx, hy, ?_⟩
      · exact (hpr.append hpl).trans (List.perm_append_comm ..)
      · apply shell_join hsr hsl hab (hil rl (hpl.mem_iff.mp (by simp))) ha hb
        · obtain ⟨g, hg, hga, hgb⟩ := hpairr
          exact ⟨g, hpr.mem_iff.mpr hg, hga, hgb⟩
        · intro g hg f hf z hzg hzf
          exact hover z (supported hl f (hpl.mem_iff.mp hf) z hzf)
            (supported hr g (hpr.mem_iff.mp hg) z hzg)
  | rotate l fs k h ih =>
    intro x y hxy
    apply ih (List.nodup_rotate.mpr hn) hi x y
    rw [edges_rotate]
    exact List.mem_rotate.mpr hxy

end DissectionLeafOrderConstruction

theorem P3511T1LeafOrder {n : Nat}
    {p : P3381T1PolygonBoundary n} {X : Set (Real × Real)}
    (s : P3511T1SourceDissection p X) :
    ∃ order : Fin s.count ≃ Fin s.count,
      ∀ k : Fin s.count, 0 < k.val →
        ∃ a b c : Fin (n + 3), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          Set.range (s.face (order k)) = {a, b, c} ∧
          (∀ l : Fin s.count, l.val < k.val →
            c ∉ Set.range (s.face (order l))) ∧
          Set.ncard {l : Fin s.count | l.val < k.val ∧
            a ∈ Set.range (s.face (order l)) ∧
            b ∈ Set.range (s.face (order l))} = 1 := by
-- BODY
  classical
  -- Root shellings at a cyclic boundary edge, including the split diagonal.
  let Face (α : Type) := Fin 3 → α
  let edges {α : Type} (l : List α) : List (α × α) :=
    List.zipWith Prod.mk l (l.rotate 1)
  let Shell {α : Type} (fs : List (Face α)) : Prop :=
    ∀ pre f post, fs = pre ++ f :: post → pre ≠ [] →
      ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Set.range f = {a, b, c} ∧
        (∀ g ∈ pre, c ∉ Set.range g) ∧
        ∃ g ∈ pre, a ∈ Set.range g ∧ b ∈ Set.range g
  have rooted {α : Type} {l : List α} {fs : List (Face α)}
      (h : P3511T1CyclicDissection α l fs) (hn : l.Nodup)
      (hi : ∀ f ∈ fs, Function.Injective f) :
      ∀ x y, (x, y) ∈ edges l →
        ∃ r tail, (r :: tail).Perm fs ∧ x ∈ Set.range r ∧ y ∈ Set.range r ∧
          Shell (r :: tail) := DissectionLeafOrderConstruction.rooted (α := α) (l := l) (fs :=
              fs) h hn hi
  let boundary := List.ofFn (fun i : Fin (n + 3) => i)
  have hn : boundary.Nodup := List.nodup_ofFn.mpr Function.injective_id
  have hi : ∀ f ∈ List.ofFn s.face, Function.Injective f := by
    intro f hf
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hf
    exact s.face_injective k
  have hne : edges boundary ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp [edges, boundary] at hlen
  obtain ⟨⟨x, y⟩, hxy⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨r, tail, hp, hx, hy, hs⟩ := rooted s.dissection hn hi x y hxy
  let fs := r :: tail
  have hlen : fs.length = s.count := by simpa [fs] using hp.length_eq
  let e : Fin fs.length ≃ Fin (List.ofFn s.face).length :=
    Equiv.ofBijective hp.idxBij ⟨hp.idxBij_injective, hp.idxBij_surjective⟩
  let order : Fin s.count ≃ Fin s.count :=
    (finCongr hlen.symm).trans (e.trans (finCongr (List.length_ofFn (f := s.face))))
  have hface (k : Fin s.count) : s.face (order k) = fs[k.val]'(by omega) := by
    have he := hp.getElem_idxBij_eq_getElem (Fin.cast hlen.symm k)
    simpa only [order, e, fs, Equiv.trans_apply, Equiv.ofBijective, finCongr,
      Equiv.coe_fn_mk, List.getElem_ofFn, Fin.val_cast, Fin.cast] using he
  refine ⟨order, ?_⟩
  intro k hk
  have hkfs : k.val < fs.length := by omega
  have hsplit : fs = fs.take k.val ++ fs[k.val] :: fs.drop (k.val + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hpre : fs.take k.val ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_take, List.length_nil] at hh
    omega
  obtain ⟨a, b, c, hab, hac, hbc, hset, hnew, g, hg, hga, hgb⟩ :=
    hs (fs.take k.val) fs[k.val] (fs.drop (k.val + 1)) hsplit hpre
  refine ⟨a, b, c, hab, hac, hbc, ?_, ?_, ?_⟩
  · simpa only [hface] using hset
  · intro l hl
    rw [hface]
    apply hnew
    exact List.mem_take_iff_getElem.mpr ⟨l.val, by omega, rfl⟩
  · obtain ⟨j, hj, hjg⟩ := List.mem_take_iff_getElem.mp hg
    let l : Fin s.count := ⟨j, by omega⟩
    have hlj : l.val < k.val := by dsimp [l]; omega
    have hgl : s.face (order l) = g := by rw [hface]; exact hjg
    have hka : a ∈ Set.range (s.face (order k)) := by rw [hface, hset]; simp
    have hkb : b ∈ Set.range (s.face (order k)) := by rw [hface, hset]; simp
    have hla : a ∈ Set.range (s.face (order l)) := by rw [hgl]; exact hga
    have hlb : b ∈ Set.range (s.face (order l)) := by rw [hgl]; exact hgb
    let S : Set (Fin s.count) := {i | a ∈ Set.range (s.face i) ∧ b ∈ Set.range (s.face i)}
    have hbound : S.ncard ≤ 2 := by
      have hc := s.edge_count a b hab
      change S.ncard = _ at hc
      split_ifs at hc <;> omega
    have hmemk : order k ∈ S := ⟨hka, hkb⟩
    have hmeml : order l ∈ S := ⟨hla, hlb⟩
    have hkl : order k ≠ order l := by
      intro he
      have := congrArg Fin.val (order.injective he)
      omega
    have heq : ({order k, order l} : Set (Fin s.count)) = S := by
      apply Set.eq_of_subset_of_ncard_le
      · intro i hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl
        · exact hmemk
        · exact hmeml
      · rw [Set.ncard_pair hkl]
        exact hbound
      · exact Set.toFinite _
    have hpred : {i : Fin s.count | i.val < k.val ∧
        a ∈ Set.range (s.face (order i)) ∧ b ∈ Set.range (s.face (order i))} = {l} := by
      ext i
      constructor
      · rintro ⟨hik, hia, hib⟩
        have hm : order i ∈ S := ⟨hia, hib⟩
        rw [← heq] at hm
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with h | h
        · have := congrArg Fin.val (order.injective h)
          omega
        · exact order.injective h
      · intro he
        simp only [Set.mem_singleton_iff] at he
        subst i
        exact ⟨hlj, hla, hlb⟩
    rw [hpred, Set.ncard_singleton]

end ApollonianSuperharmonic

end
