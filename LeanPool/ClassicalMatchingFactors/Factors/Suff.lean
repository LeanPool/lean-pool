/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import LeanPool.ClassicalMatchingFactors.Factors.Comp
public import LeanPool.ClassicalMatchingFactors.Factors.Gadget

/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# Normal form of a minimal Tutte violator of the gadget

For a Tutte violator `U` of `FFactor.gadget G f` such that no vertex of `U` satisfies
`FFactor.TwoComp`, we show that for every vertex `v` of `G`, `U` contains either all inner
vertices of `v` and no outer vertex of `v` (`v ∈ Tset`), or all outer vertices of `v` and no
inner vertex of `v` (`v ∈ Sset`), or no vertex of `v` at all.
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}

section Normal

variable {U : Set (GV G f)}

open Classical in
theorem inner_mem_of_inner_mem (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    {i j : Fin (G.degree v - f v)} (hi : (.inr ⟨v, i⟩ : GV G f) ∈ U) :
    (.inr ⟨v, j⟩ : GV G f) ∈ U := by
  by_contra hj
  apply hmin _ hi
  intro a b c ha hb hc
  let y0 : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts :=
    ⟨.inr ⟨v, j⟩, (mem_del_verts _).mpr hj⟩
  have key : ∀ a : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (gadget G f).Adj (.inr ⟨v, i⟩) a → (del (gadget G f) U).Reachable a y0 := by
    rintro ⟨a | q, haU⟩ ha
    · exact Adj.reachable ((del_adj _).mpr (show (gadget G f).Adj (.inl a) (.inr ⟨v, j⟩) from ha))
    · exact absurd ha (gadget_adj_inr_inr _ _)
  exact Or.inl ((key a ha).trans (key b hb).symm)

open Classical in
theorem outer_notMem_of_inner_all (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    (hT : ∀ i, (.inr ⟨v, i⟩ : GV G f) ∈ U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∉ U := by
  intro hdU
  apply hmin _ hdU
  intro a b c ha hb hc
  have key : ∀ a : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (gadget G f).Adj (.inl d) a → a.val = .inl d.symm := by
    rintro ⟨a | ⟨w, i⟩, haU⟩ ha
    · simp only [gadget_adj_inl_inl] at ha
      simp [ha]
    · have hw : d.fst = w := ha
      obtain rfl : w = v := hw.symm.trans hd
      exact absurd (hT i) ((mem_del_verts _).mp haU)
  have : a = b := Subtype.ext ((key a ha).trans (key b hb).symm)
  exact Or.inl (this ▸ Reachable.refl _)

open Classical in
theorem outer_notMem_of_outer_notMem (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    {z : G.Dart} (hz : z.fst = v)
    (hzU : (.inl z : GV G f) ∉ U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∉ U := by
  intro hdU
  apply hmin _ hdU
  intro a b c ha hb hc
  let zv : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts :=
    ⟨.inl z, (mem_del_verts _).mpr hzU⟩
  have key : ∀ a : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (gadget G f).Adj (.inl d) a → a.val = .inl d.symm ∨ (del (gadget G f) U).Reachable a zv := by
    rintro ⟨a | ⟨w, i⟩, haU⟩ ha
    · left
      simp only [gadget_adj_inl_inl] at ha
      simp [ha]
    · right
      have hw : d.fst = w := ha
      obtain rfl : w = v := hw.symm.trans hd
      exact Adj.reachable ((del_adj _).mpr (show (gadget G f).Adj (.inr ⟨_, i⟩) (.inl z) from hz))
  have eqR : ∀ a b : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts, a.val = b.val →
      (del (gadget G f) U).Reachable a b := fun a b h => by rw [Subtype.ext h]
  have zR : ∀ a b : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (del (gadget G f) U).Reachable a zv → (del (gadget G f) U).Reachable b zv →
      (del (gadget G f) U).Reachable a b := fun _ _ h h' => h.trans h'.symm
  rcases key a ha with h1 | h1 <;> rcases key b hb with h2 | h2 <;>
    rcases key c hc with h3 | h3 <;>
    first
    | exact Or.inl (eqR _ _ (h1.trans h2.symm))
    | exact Or.inl (zR _ _ h1 h2)
    | exact Or.inr (Or.inl (eqR _ _ (h1.trans h3.symm)))
    | exact Or.inr (Or.inl (zR _ _ h1 h3))
    | exact Or.inr (Or.inr (eqR _ _ (h2.trans h3.symm)))
    | exact Or.inr (Or.inr (zR _ _ h2 h3))

open Classical in
variable (G f U) in
/-- `T`: vertices all of whose inner vertices lie in `U`. -/
noncomputable def Tset : Finset V :=
  {v | ∀ i : Fin (G.degree v - f v), (.inr ⟨v, i⟩ : GV G f) ∈ U}

open Classical in
variable (G f U) in
/-- `S`: vertices not in `T` all of whose outer vertices lie in `U`. -/
noncomputable def Sset : Finset V :=
  {v | v ∉ Tset G f U ∧ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U}

open Classical in
theorem disjoint_Sset_Tset : Disjoint (Sset G f U) (Tset G f U) := by
  rw [Finset.disjoint_left]
  intro v hv
  simp only [Sset, mem_filter, mem_univ, true_and] at hv
  exact hv.1

open Classical in
theorem mem_Tset {v : V} : v ∈ Tset G f U ↔ ∀ i, (.inr ⟨v, i⟩ : GV G f) ∈ U := by
  simp [Tset]

open Classical in
theorem mem_Sset {v : V} : v ∈ Sset G f U ↔
    v ∉ Tset G f U ∧ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U := by
  simp [Sset]

open Classical in
theorem F1 (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hv : v ∉ Tset G f U)
    (i : Fin (G.degree v - f v)) : (.inr ⟨v, i⟩ : GV G f) ∉ U := by
  intro hi
  exact hv (mem_Tset.mpr (fun j => inner_mem_of_inner_mem hmin hi))

open Classical in
theorem F2 (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hv : v ∈ Tset G f U)
    {d : G.Dart} (hd : d.fst = v) : (.inl d : GV G f) ∉ U :=
  outer_notMem_of_inner_all hmin (mem_Tset.mp hv) hd

open Classical in
theorem F3 (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hvT : v ∉ Tset G f U)
    (hvS : v ∉ Sset G f U) {d : G.Dart} (hd : d.fst = v) : (.inl d : GV G f) ∉ U := by
  have : ¬ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U := fun h =>
    hvS (mem_Sset.mpr ⟨hvT, h⟩)
  push Not at this
  obtain ⟨z, hz, hzU⟩ := this
  exact outer_notMem_of_outer_notMem hmin hz hzU hd

open Classical in
theorem F4 {v : V} (hv : v ∈ Sset G f U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∈ U :=
  (mem_Sset.mp hv).2 d hd

open Classical in
theorem F5 {v : V} (hv : v ∈ Tset G f U) (i : Fin (G.degree v - f v)) :
    (.inr ⟨v, i⟩ : GV G f) ∈ U :=
  mem_Tset.mp hv i

open Classical in
theorem exists_inner_of_notMem_Tset {v : V} (hv : v ∉ Tset G f U) :
    ∃ _ : Fin (G.degree v - f v), True := by
  by_contra h
  push Not at h
  exact hv (mem_Tset.mpr (fun i => (h i).elim))

open Classical in
theorem exists_dart_of_notMem_Tset {v : V} (hv : v ∉ Tset G f U) :
    ∃ d : G.Dart, d.fst = v := by
  obtain ⟨i, -⟩ := exists_inner_of_notMem_Tset hv
  have : 0 < G.degree v := by have := i.2; omega
  obtain ⟨u, hu⟩ := G.degree_pos_iff_exists_adj v |>.mp this
  exact ⟨⟨(v, u), hu⟩, rfl⟩

end Normal

section Label

variable [DecidableEq V] {U : Set (GV G f)}

open Classical in
variable (G f U) in
/-- The vertex of `G` a vertex of the gadget "belongs to" after removing `U`. -/
noncomputable def home : GV G f → V
  | .inl d => if d.fst ∈ Tset G f U then d.snd else d.fst
  | .inr p => p.1

open Classical in
@[simp] theorem home_inl (d : G.Dart) :
    home G f U (.inl d) = if d.fst ∈ Tset G f U then d.snd else d.fst := rfl
open Classical in
@[simp] theorem home_inr (p : Σ v : V, Fin (G.degree v - f v)) :
    home G f U (.inr p) = p.1 := rfl

open Classical in
variable (G f U) in
/-- The graph `G - (S ∪ T)`. -/
abbrev Gr : SimpleGraph ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ) :=
  G.induce (((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ)

open Classical in
variable (G f U) in
/-- The labelling of the vertices of the gadget whose fibres are the components of
`gadget - U`. -/
noncomputable def lab (a : GV G f) : (Gr G f U).ConnectedComponent ⊕ (Sym2 V ⊕ GV G f) :=
  if h : home G f U a ∉ Sset G f U ∪ Tset G f U then
    .inl ((Gr G f U).connectedComponentMk ⟨home G f U a, h⟩)
  else match a with
    | .inl d => .inr (.inl d.edge)
    | .inr _ => .inr (.inr a)

open Classical in
theorem lab_of_notMem {a : GV G f} (h : home G f U a ∉ Sset G f U ∪ Tset G f U) :
    lab G f U a = .inl ((Gr G f U).connectedComponentMk ⟨home G f U a, h⟩) := by
  simp only [lab, dite_eq_left h]

open Classical in
theorem lab_inl_of_mem {d : G.Dart} (h : home G f U (.inl d) ∈ Sset G f U ∪ Tset G f U) :
    lab G f U (.inl d) = .inr (.inl d.edge) := by
  simp only [lab, h, not_true_eq_false, dite_false]

open Classical in
theorem lab_inr_of_mem {p : Σ v : V, Fin (G.degree v - f v)}
    (h : home G f U (.inr p) ∈ Sset G f U ∪ Tset G f U) :
    lab G f U (.inr p) = .inr (.inr (.inr p)) := by
  simp only [lab, h, not_true_eq_false, dite_false]

open Classical in
theorem lab_eq_of_home_eq {a b : GV G f} (hab : home G f U a = home G f U b)
    (h : home G f U a ∉ Sset G f U ∪ Tset G f U) : lab G f U a = lab G f U b := by
  rw [lab_of_notMem h, lab_of_notMem (hab ▸ h)]
  congr 2
  exact Subtype.ext hab

omit [DecidableEq V] in
open Classical in
theorem fst_notMem_S_of_notMem {d : G.Dart} (hd : (.inl d : GV G f) ∉ U) :
    d.fst ∉ Sset G f U := fun h => hd (F4 h rfl)

omit [DecidableEq V] in
open Classical in
theorem notMem_T_of_inner_notMem {v : V} {i : Fin (G.degree v - f v)}
    (h : (.inr ⟨v, i⟩ : GV G f) ∉ U) : v ∉ Tset G f U := fun hv => h (F5 hv i)

open Classical in
theorem lab_eq_of_adj_inl_inr {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)}
    (ha : (.inl d : GV G f) ∉ U) (hb : (.inr p : GV G f) ∉ U) (hadj : d.fst = p.1) :
    lab G f U (.inl d) = lab G f U (.inr p) := by
  obtain ⟨v, i⟩ := p
  simp only at hadj
  subst hadj
  have hT := notMem_T_of_inner_notMem hb
  have hS := fst_notMem_S_of_notMem ha
  apply lab_eq_of_home_eq
  · simp [hT]
  · simp [hT, hS]

open Classical in
theorem lab_eq_of_adj (a b : GV G f) (ha : a ∉ U) (hb : b ∉ U) (hadj : (gadget G f).Adj a b) :
    lab G f U a = lab G f U b := by
  rcases a with d | p <;> rcases b with d' | p'
  · simp only [gadget_adj_inl_inl] at hadj
    subst hadj
    have hS1 := fst_notMem_S_of_notMem ha
    have hS2 : d.snd ∉ Sset G f U := fst_notMem_S_of_notMem (d := d.symm) hb
    by_cases ht1 : d.fst ∈ Tset G f U <;> by_cases ht2 : d.snd ∈ Tset G f U
    · rw [lab_inl_of_mem (by simp [ht1, ht2]), lab_inl_of_mem (by simp [ht1, ht2]),
        Dart.edge_symm]
    · apply lab_eq_of_home_eq
      · simp [ht1, ht2]
      · simp [ht1, ht2, hS2]
    · apply lab_eq_of_home_eq
      · simp [ht1, ht2]
      · simp [ht1, hS1]
    · rw [lab_of_notMem (by simp [ht1, hS1]), lab_of_notMem (by simp [ht2, hS2])]
      congr 1
      apply ConnectedComponent.connectedComponentMk_eq_of_adj
      simp [ht1, ht2, d.adj]
  · exact lab_eq_of_adj_inl_inr ha hb hadj
  · exact (lab_eq_of_adj_inl_inr hb ha hadj).symm
  · exact absurd hadj (gadget_adj_inr_inr _ _)

omit [DecidableEq V] in
open Classical in
theorem reach_adj {a b : GV G f} (ha : a ∉ U) (hb : b ∉ U) (h : (gadget G f).Adj a b) :
    (del (gadget G f) U).Reachable ⟨a, (mem_del_verts _).mpr ha⟩
      ⟨b, (mem_del_verts _).mpr hb⟩ :=
  Adj.reachable ((del_adj _).mpr h)

open Classical in
theorem notMem_T_of_notMem_union {r : V} (hr : r ∉ Sset G f U ∪ Tset G f U) :
    r ∉ Tset G f U := fun h => hr (mem_union_right _ h)

open Classical in
theorem notMem_S_of_notMem_union {r : V} (hr : r ∉ Sset G f U ∪ Tset G f U) :
    r ∉ Sset G f U := fun h => hr (mem_union_left _ h)

open Classical in
theorem reach_inner (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {r : V}
    (hr : r ∉ Sset G f U ∪ Tset G f U) (x : GV G f) (hx : x ∉ U)
    (hxr : home G f U x = r) (i : Fin (G.degree r - f r)) :
    (del (gadget G f) U).Reachable ⟨x, (mem_del_verts _).mpr hx⟩
      ⟨.inr ⟨r, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr) i)⟩ := by
  have hrT := notMem_T_of_notMem_union hr
  have hrS := notMem_S_of_notMem_union hr
  rcases x with d | ⟨r', j⟩
  · simp only [home_inl] at hxr
    by_cases ht : d.fst ∈ Tset G f U
    · rw [ite_eq_left ht] at hxr
      have hs : (.inl d.symm : GV G f) ∉ U := F3 hmin hrT hrS (d := d.symm) hxr
      exact (reach_adj hx hs rfl).trans (reach_adj hs (F1 hmin hrT i) hxr)
    · rw [ite_eq_right ht] at hxr
      exact reach_adj hx (F1 hmin hrT i) hxr
  · simp only [home_inr] at hxr
    subst hxr
    obtain ⟨z, hz⟩ := exists_dart_of_notMem_Tset hrT
    have hzU : (.inl z : GV G f) ∉ U := F3 hmin hrT hrS hz
    exact (reach_adj hx hzU hz).trans (reach_adj hzU (F1 hmin hrT i) hz)

open Classical in
theorem reach_inner_inner (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {r r' : V}
    (hr : r ∉ Sset G f U ∪ Tset G f U) (hr' : r' ∉ Sset G f U ∪ Tset G f U)
    (hadj : G.Adj r r') (i : Fin (G.degree r - f r)) (i' : Fin (G.degree r' - f r')) :
    (del (gadget G f) U).Reachable
      ⟨.inr ⟨r, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr) i)⟩
      ⟨.inr ⟨r', i'⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union hr') i')⟩ := by
  let d : G.Dart := ⟨(r, r'), hadj⟩
  have hd : (.inl d : GV G f) ∉ U :=
    F3 hmin (notMem_T_of_notMem_union hr) (notMem_S_of_notMem_union hr) (d := d) rfl
  have hd' : (.inl d.symm : GV G f) ∉ U :=
    F3 hmin (notMem_T_of_notMem_union hr') (notMem_S_of_notMem_union hr') (d := d.symm) rfl
  have h1 := reach_inner hmin hr (.inl d) hd
    (by simp [d, notMem_T_of_notMem_union hr]) i
  have h2 := reach_inner hmin hr' (.inl d.symm) hd'
    (by simp [d, notMem_T_of_notMem_union hr']) i'
  exact h1.symm.trans ((reach_adj hd hd' rfl).trans h2)

open Classical in
theorem reach_inner_of_reachable (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    {u w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ)} (p : (Gr G f U).Walk u w) :
    ∀ (i : Fin (G.degree u.1 - f u.1)) (i' : Fin (G.degree w.1 - f w.1)),
    (del (gadget G f) U).Reachable
      ⟨.inr ⟨u.1, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union u.2) i)⟩
      ⟨.inr ⟨w.1, i'⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union w.2) i')⟩ := by
  induction p with
  | @nil x =>
    intro i i'
    exact reach_inner hmin x.2 (.inr ⟨_, i⟩) (F1 hmin (notMem_T_of_notMem_union x.2) i) rfl i'
  | @cons a b c hadj p ih =>
    intro i i'
    obtain ⟨i'', -⟩ := exists_inner_of_notMem_Tset (notMem_T_of_notMem_union b.2)
    exact (reach_inner_inner hmin a.2 b.2 hadj i i'').trans (ih i'' i')

open Classical in
theorem reach_of_lab_eq (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) (a b : GV G f)
    (ha : a ∉ U) (hb : b ∉ U) (hab : lab G f U a = lab G f U b) :
    (del (gadget G f) U).Reachable ⟨a, (mem_del_verts _).mpr ha⟩
      ⟨b, (mem_del_verts _).mpr hb⟩ := by
  by_cases hha : home G f U a ∈ Sset G f U ∪ Tset G f U
  · rcases a with d | p <;> rcases b with d' | q
    · by_cases hhb : home G f U (.inl d') ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inl_of_mem hha, lab_inl_of_mem hhb] at hab
        simp only [Sum.inr.injEq, Sum.inl.injEq] at hab
        rcases (dart_edge_eq_iff _ _).mp hab with h | h
        · subst h; rfl
        · subst h
          exact reach_adj ha hb (by simp)
      · rw [lab_inl_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
    · by_cases hhb : home G f U (.inr q) ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inl_of_mem hha, lab_inr_of_mem hhb] at hab
        simp at hab
      · rw [lab_inl_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
    · by_cases hhb : home G f U (.inl d') ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inr_of_mem hha, lab_inl_of_mem hhb] at hab
        simp at hab
      · rw [lab_inr_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
    · by_cases hhb : home G f U (.inr q) ∈ Sset G f U ∪ Tset G f U
      · rw [lab_inr_of_mem hha, lab_inr_of_mem hhb] at hab
        simp only [Sum.inr.injEq] at hab
        subst hab; rfl
      · rw [lab_inr_of_mem hha, lab_of_notMem hhb] at hab
        simp at hab
  · by_cases hhb : home G f U b ∈ Sset G f U ∪ Tset G f U
    · exfalso
      rw [lab_of_notMem hha] at hab
      rcases b with d' | q
      · rw [lab_inl_of_mem hhb] at hab; simp at hab
      · rw [lab_inr_of_mem hhb] at hab; simp at hab
    · rw [lab_of_notMem hha, lab_of_notMem hhb] at hab
      simp only [Sum.inl.injEq] at hab
      obtain ⟨p⟩ := ConnectedComponent.exact hab
      obtain ⟨i, -⟩ := exists_inner_of_notMem_Tset (notMem_T_of_notMem_union hha)
      obtain ⟨i', -⟩ := exists_inner_of_notMem_Tset (notMem_T_of_notMem_union hhb)
      exact (reach_inner hmin hha a ha rfl i).trans
        ((reach_inner_of_reachable hmin p i i').trans (reach_inner hmin hhb b hb rfl i').symm)

end Label

end FFactor
