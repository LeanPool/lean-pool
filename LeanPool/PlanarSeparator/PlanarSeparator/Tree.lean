/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Cochain

/-!
# Spanning trees of a map

A spanning tree of a map `M` is given by a root and, for every other vertex `v`, a *parent dart*
leaving `v`, such that a `height` function decreases from a vertex to the head of its parent
dart (the *parent* of the vertex). The edges of the parent darts are the *tree edges*.

For a vertex `v` we define the set `anc v` of its ancestors (the vertices of the path from `v` to
the root in the tree) and the cochain `pathC v` of the edges of this path. The cochain of the
path from `v` to the root has odd degree exactly at `v` and at the root
(`PlanarSeparator.Map.SpTree.sum_pathC`).

The basic fact about trees used below is that a tree contains no nonzero closed cochain: a set
of tree edges with even degree at every vertex is empty (`PlanarSeparator.Map.SpTree.eq_zero`).
Indeed, a deepest vertex `u` whose parent edge belongs to the set has degree one in it.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} (M : Map D P)

/-- The indicator of the edge of a dart, as a cochain on the darts. -/
def edgeInd [DecidableEq D] (e : D) : D → ZMod 2 := fun d => if d = e ∨ d = M.α e then 1 else 0

variable {M}

section EdgeInd

variable [DecidableEq D]

lemma edgeInd_α (e d : D) : M.edgeInd e (M.α d) = M.edgeInd e d := by
  simp only [edgeInd]
  congr 1
  apply propext
  constructor
  · rintro (h | h)
    · right; rw [← h, M.α_α]
    · left; exact M.α_injective h
  · rintro (rfl | rfl)
    · right; rfl
    · left; rw [M.α_α]

lemma edgeInd_of_α (e d : D) : M.edgeInd (M.α e) d = M.edgeInd e d := by
  simp only [edgeInd, M.α_α, or_comm]

@[simp] lemma edgeInd_self (e : D) : M.edgeInd e e = 1 := by simp [edgeInd]

lemma edgeInd_ne_zero {e d : D} (h : M.edgeInd e d ≠ 0) : d = e ∨ d = M.α e := by
  by_contra h'
  exact h (by simp [edgeInd, h'])

lemma edgeInd_eq_zero {e d : D} (h1 : d ≠ e) (h2 : d ≠ M.α e) : M.edgeInd e d = 0 := by
  simp [edgeInd, h1, h2]

variable [Fintype D] [DecidableEq P]

/-- The degrees of the indicator of an edge. -/
lemma sum_edgeInd (e : D) (w : P) :
    ∑ d with M.vert d = w, M.edgeInd e d =
      (if M.vert e = w then 1 else 0) + (if M.vert (M.α e) = w then 1 else 0) := by
  rw [sum_filter]
  have : ∀ d : D, (if M.vert d = w then M.edgeInd e d else 0) =
      if d ∈ ({e, M.α e} : Finset D) then (if M.vert d = w then 1 else 0) else 0 := by
    intro d
    simp only [edgeInd, mem_insert, mem_singleton]
    by_cases h1 : d = e ∨ d = M.α e <;> by_cases h2 : M.vert d = w <;> simp [h1, h2]
  rw [sum_congr rfl fun d _ => this d, ← sum_filter, filter_mem_eq_inter, univ_inter,
    sum_pair (M.α_ne e).symm]

end EdgeInd

/-- A spanning tree of a map, given by a root and the parent dart of every other vertex; the
height decreases from a vertex to its parent. -/
structure SpTree (M : Map D P) where
  /-- The root. -/
  root : P
  /-- The dart from a vertex to its parent. -/
  par : ∀ v, v ≠ root → D
  /-- A height function decreasing towards the root. -/
  height : P → ℕ
  vert_par : ∀ v (h : v ≠ root), M.vert (par v h) = v
  height_lt : ∀ v (h : v ≠ root), height (M.vert (M.α (par v h))) < height v

namespace SpTree

variable (T : SpTree M)

/-- A tree dart: a parent dart or its reversal. -/
def IsTree (d : D) : Prop := ∃ v, ∃ h : v ≠ T.root, d = T.par v h ∨ d = M.α (T.par v h)

lemma isTree_α {d : D} : T.IsTree (M.α d) ↔ T.IsTree d := by
  constructor
  · rintro ⟨v, h, hd | hd⟩
    · exact ⟨v, h, Or.inr (by rw [← hd, M.α_α])⟩
    · exact ⟨v, h, Or.inl (M.α_injective hd)⟩
  · rintro ⟨v, h, rfl | rfl⟩
    · exact ⟨v, h, Or.inr rfl⟩
    · exact ⟨v, h, Or.inl (M.α_α _)⟩

lemma isTree_par (v : P) (h : v ≠ T.root) : T.IsTree (T.par v h) := ⟨v, h, Or.inl rfl⟩

/-- A parent dart is never the reversal of a parent dart. -/
lemma par_ne_α_par {u v : P} (hu : u ≠ T.root) (hv : v ≠ T.root) :
    T.par u hu ≠ M.α (T.par v hv) := by
  intro h
  have h1 : M.vert (M.α (T.par v hv)) = u := by rw [← h, T.vert_par]
  have h2 : M.vert (M.α (T.par u hu)) = v := by rw [h, M.α_α, T.vert_par]
  have := T.height_lt u hu
  have := T.height_lt v hv
  rw [h2] at *
  rw [h1] at *
  omega

lemma par_inj {u v : P} (hu : u ≠ T.root) (hv : v ≠ T.root) (h : T.par u hu = T.par v hv) :
    u = v := by
  rw [← T.vert_par u hu, h, T.vert_par]

variable [DecidableEq P]

/-- The parent of a vertex (the root is its own parent). -/
def parent (v : P) : P := if h : v = T.root then T.root else M.vert (M.α (T.par v h))

lemma parent_of_ne {v : P} (h : v ≠ T.root) : T.parent v = M.vert (M.α (T.par v h)) := by
  simp [parent, h]

lemma height_parent_lt {v : P} (h : v ≠ T.root) : T.height (T.parent v) < T.height v := by
  rw [T.parent_of_ne h]
  exact T.height_lt v h

/-- Induction from the root along the tree. -/
theorem induction {p : P → Prop} (hroot : p T.root)
    (hstep : ∀ v, v ≠ T.root → p (T.parent v) → p v) (v : P) : p v := by
  induction hn : T.height v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = T.root
    · subst hv
      exact hroot
    · exact hstep v hv (ih _ (hn ▸ T.height_parent_lt hv) _ rfl)

/-- The ancestors of a vertex: the vertices of the path to the root. -/
def anc (v : P) : Finset P :=
  if _h : v = T.root then {T.root} else insert v (anc (T.parent v))
termination_by T.height v
decreasing_by exact T.height_parent_lt _h

lemma anc_root : T.anc T.root = {T.root} := by
  rw [anc]
  simp

lemma anc_of_ne {v : P} (h : v ≠ T.root) : T.anc v = insert v (T.anc (T.parent v)) := by
  rw [anc]
  simp [h]

lemma mem_anc_self (v : P) : v ∈ T.anc v := by
  by_cases h : v = T.root
  · subst h
    simp [anc_root]
  · rw [T.anc_of_ne h]
    exact mem_insert_self _ _

lemma root_mem_anc (v : P) : T.root ∈ T.anc v := by
  refine T.induction (p := fun v => T.root ∈ T.anc v) (by simp [anc_root]) (fun v hv ih => ?_) v
  rw [T.anc_of_ne hv]
  exact mem_insert_of_mem ih

lemma parent_mem_anc {u v : P} (hu : u ∈ T.anc v) : T.parent u ∈ T.anc v := by
  induction v using T.induction with
  | hroot =>
    rw [anc_root, mem_singleton] at hu
    subst hu
    simp [parent, anc_root]
  | hstep v hv ih =>
    rw [T.anc_of_ne hv] at hu ⊢
    rcases mem_insert.1 hu with rfl | hu
    · exact mem_insert_of_mem (T.mem_anc_self _)
    · exact mem_insert_of_mem (ih hu)

lemma height_le_of_mem_anc {u v : P} (hu : u ∈ T.anc v) : T.height u ≤ T.height v := by
  induction v using T.induction with
  | hroot =>
    rw [anc_root, mem_singleton] at hu
    rw [hu]
  | hstep v hv ih =>
    rw [T.anc_of_ne hv] at hu
    rcases mem_insert.1 hu with rfl | hu
    · exact le_rfl
    · exact (ih hu).trans (T.height_parent_lt hv).le

/-- Along a part `Q` of the tree closed under parents, on which a level function decreases by one
from a vertex to its parent, the ancestors of any vertex lying in `Q` have distinct levels. -/
lemma injOn_anc {Q : Finset P} {lev : P → ℕ}
    (hQ : ∀ v ∈ Q, v ≠ T.root → T.parent v ∈ Q ∧ lev (T.parent v) + 1 = lev v) (v : P) :
    Set.InjOn lev ↑((T.anc v).filter (· ∈ Q)) := by
  suffices h : ∀ v, Set.InjOn lev ↑((T.anc v).filter (· ∈ Q)) ∧
      (v ∈ Q → ∀ u ∈ (T.anc v).filter (· ∈ Q), lev u ≤ lev v) from (h v).1
  intro v
  induction v using T.induction with
  | hroot =>
    refine ⟨fun a ha b hb _ => ?_, fun _ u hu => ?_⟩
    · simp only [anc_root, coe_filter, mem_singleton, Set.mem_ofPred_eq] at ha hb
      rw [ha.1, hb.1]
    · simp only [anc_root, mem_filter, mem_singleton] at hu
      rw [hu.1]
  | hstep v hv ih =>
    by_cases hvQ : v ∈ Q
    · obtain ⟨hpQ, hlev⟩ := hQ v hvQ hv
      have hbound := ih.2 hpQ
      have hlt : ∀ u ∈ (T.anc (T.parent v)).filter (· ∈ Q), lev u < lev v := fun u hu => by
        have := hbound u hu
        omega
      rw [T.anc_of_ne hv, filter_insert, ite_eq_left hvQ]
      refine ⟨?_, fun _ u hu => ?_⟩
      · intro a ha b hb hab
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · rfl
        · exact absurd hab.symm (hlt b hb).ne
        · exact absurd hab (hlt a ha).ne
        · exact ih.1 ha hb hab
      · rcases mem_insert.1 hu with rfl | hu
        · exact le_rfl
        · exact (hlt u hu).le
    · rw [T.anc_of_ne hv, filter_insert, ite_eq_right hvQ]
      exact ⟨ih.1, fun h => absurd h hvQ⟩

/-- The number of ancestors of a vertex in `Q` with a level in `I` is at most `#I`. -/
lemma card_anc_filter_le {Q : Finset P} {lev : P → ℕ}
    (hQ : ∀ v ∈ Q, v ≠ T.root → T.parent v ∈ Q ∧ lev (T.parent v) + 1 = lev v) (v : P)
    (I : Finset ℕ) : #((T.anc v).filter (fun u => u ∈ Q ∧ lev u ∈ I)) ≤ #I := by
  refine card_le_card_of_injOn lev (fun u hu => (mem_filter.1 hu).2.2) ?_
  intro a ha b hb hab
  refine T.injOn_anc hQ v ?_ ?_ hab
  · simp only [coe_filter, Set.mem_ofPred_eq] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  · simp only [coe_filter, Set.mem_ofPred_eq] at hb ⊢
    exact ⟨hb.1, hb.2.1⟩

variable [DecidableEq D]

/-- The cochain of the path from a vertex to the root. -/
def pathC (v : P) : D → ZMod 2 :=
  if h : v = T.root then 0 else M.edgeInd (T.par v h) + pathC (T.parent v)
termination_by T.height v
decreasing_by exact T.height_parent_lt h

lemma pathC_root : T.pathC T.root = 0 := by
  rw [pathC]
  simp

lemma pathC_of_ne {v : P} (h : v ≠ T.root) :
    T.pathC v = M.edgeInd (T.par v h) + T.pathC (T.parent v) := by
  rw [pathC]
  simp [h]

lemma pathC_α (v : P) (d : D) : T.pathC v (M.α d) = T.pathC v d := by
  induction v using T.induction with
  | hroot => simp [pathC_root]
  | hstep v hv ih => simp only [T.pathC_of_ne hv, Pi.add_apply, edgeInd_α, ih]

/-- The support of the path cochain consists of tree darts along the path. -/
lemma pathC_ne_zero {v : P} {d : D} (hd : T.pathC v d ≠ 0) :
    ∃ u ∈ T.anc v, ∃ h : u ≠ T.root, d = T.par u h ∨ d = M.α (T.par u h) := by
  induction v using T.induction with
  | hroot => simp [pathC_root] at hd
  | hstep v hv ih =>
    rw [T.pathC_of_ne hv, Pi.add_apply] at hd
    by_cases h1 : M.edgeInd (T.par v hv) d = 0
    · rw [h1, zero_add] at hd
      obtain ⟨u, hu, h, hd⟩ := ih hd
      exact ⟨u, by rw [T.anc_of_ne hv]; exact mem_insert_of_mem hu, h, hd⟩
    · exact ⟨v, T.mem_anc_self v, hv, edgeInd_ne_zero h1⟩

lemma isTree_of_pathC_ne_zero {v : P} {d : D} (hd : T.pathC v d ≠ 0) : T.IsTree d := by
  obtain ⟨u, -, h, hd⟩ := T.pathC_ne_zero hd
  exact ⟨u, h, hd⟩

/-- The vertices of the support of the path cochain lie on the path. -/
lemma vert_mem_anc_of_pathC_ne_zero {v : P} {d : D} (hd : T.pathC v d ≠ 0) :
    M.vert d ∈ T.anc v := by
  obtain ⟨u, hu, h, rfl | rfl⟩ := T.pathC_ne_zero hd
  · rwa [T.vert_par]
  · rw [← T.parent_of_ne h]
    exact T.parent_mem_anc hu

/-- The path cochain on a parent dart. -/
lemma pathC_par (v : P) {u : P} (hu : u ≠ T.root) :
    T.pathC v (T.par u hu) = if u ∈ T.anc v then 1 else 0 := by
  induction v using T.induction with
  | hroot =>
    rw [pathC_root, anc_root]
    simp [hu]
  | hstep v hv ih =>
    rw [T.pathC_of_ne hv, Pi.add_apply, ih, T.anc_of_ne hv]
    by_cases huv : u = v
    · subst huv
      have : u ∉ T.anc (T.parent u) := fun h =>
        absurd (T.height_le_of_mem_anc h) (not_le.2 (T.height_parent_lt hv))
      simp [this]
    · have h1 : M.edgeInd (T.par v hv) (T.par u hu) = 0 :=
        edgeInd_eq_zero (fun h => huv (T.par_inj hu hv h)) (T.par_ne_α_par hu hv)
      simp [h1, huv]

variable [Fintype D]

/-- The cochain of the path from `v` to the root has odd degree exactly at `v` and at the
root. -/
lemma sum_pathC (v w : P) : ∑ d with M.vert d = w, T.pathC v d =
    (if v = w then 1 else 0) + (if T.root = w then 1 else 0) := by
  induction v using T.induction with
  | hroot =>
    simp only [pathC_root, Pi.zero_apply, sum_const_zero]
    exact (Kasteleyn.ZMod.two_add_self _).symm
  | hstep v hv ih =>
    rw [T.pathC_of_ne hv]
    simp only [Pi.add_apply, sum_add_distrib, sum_edgeInd, ih, T.vert_par, ← T.parent_of_ne hv]
    generalize (if v = w then (1 : ZMod 2) else 0) = a
    generalize (if T.parent v = w then (1 : ZMod 2) else 0) = b
    generalize (if T.root = w then (1 : ZMod 2) else 0) = c
    revert a b c
    decide

omit [DecidableEq D] in
/-- **A tree carries no closed cochain.** A cochain which takes the same value on the two darts
of each edge, has even degree at every vertex and is supported on tree darts vanishes. -/
theorem eq_zero [Finite P] (c : D → ZMod 2) (hcα : ∀ d, c (M.α d) = c d)
    (hc : ∀ v, ∑ d with M.vert d = v, c d = 0) (hT : ∀ d, c d ≠ 0 → T.IsTree d) (d : D) :
    c d = 0 := by
  classical
  let := Fintype.ofFinite P
  by_contra hd
  set S : Finset P := {u | ∃ h : u ≠ T.root, c (T.par u h) ≠ 0}
  have hS : S.Nonempty := by
    obtain ⟨u, h, rfl | rfl⟩ := hT d hd
    · exact ⟨u, mem_filter.2 ⟨mem_univ _, h, hd⟩⟩
    · exact ⟨u, mem_filter.2 ⟨mem_univ _, h, by rwa [hcα] at hd⟩⟩
  obtain ⟨u, hu, hmax⟩ := exists_max_image S T.height hS
  obtain ⟨hur, hcu⟩ : ∃ h : u ≠ T.root, c (T.par u h) ≠ 0 := by simpa [S] using hu
  have key : ∑ d with M.vert d = u, c d = c (T.par u hur) := by
    refine sum_eq_single_of_mem _ (by simp [T.vert_par]) fun d hd hne => ?_
    have hdu : M.vert d = u := (mem_filter.1 hd).2
    by_contra hcd
    obtain ⟨u', h', rfl | rfl⟩ := hT d hcd
    · rw [T.vert_par] at hdu
      subst hdu
      exact hne rfl
    · have hp : T.parent u' = u := by rw [T.parent_of_ne h']; exact hdu
      have hu' : u' ∈ S := mem_filter.2 ⟨mem_univ _, h', by rwa [hcα] at hcd⟩
      have := hmax u' hu'
      have := T.height_parent_lt h'
      rw [hp] at this
      omega
  have h1 := hc u
  rw [key] at h1
  exact hcu h1

end SpTree

end Map

end PlanarSeparator
