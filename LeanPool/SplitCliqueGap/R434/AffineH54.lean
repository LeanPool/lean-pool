/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.MidpointHosts
public import LeanPool.SplitCliqueGap.R434.LocalH54
public import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The affine realization of H54 and recovery of the owner of a core edge. -/

@[expose] public section

open Finset

namespace GapExtremal.R434.H54

/-- A vertex role in one of the three parts of the 15-vertex template. -/
abbrev Role := Fin 3 × Fin 5

/-- The lower part of an edge of the given kind. -/
def lowerPart (k : Fin 3) : Fin 3 := if k = 1 then 1 else 0
/-- The upper part of an edge of the given kind. -/
def upperPart (k : Fin 3) : Fin 3 := if k = 0 then 1 else 2

/-- The edge kind for the ordered pair of parts `i < j`. -/
def edgeKind (i j : Fin 3) : Fin 3 :=
  if i = 0 then (if j = 1 then 0 else 2) else 1

/-- Adjacency in the finite role template, oriented from lower to higher part. -/
def orderedAdj (a b : Role) : Prop :=
  a.1 < b.1 ∧ (edgeKind a.1 b.1, a.2, b.2) ∈ edges

instance (a b : Role) : Decidable (orderedAdj a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The undirected graph on the three sets of five roles. -/
def roleGraph : SimpleGraph Role where
  Adj a b := orderedAdj a b ∨ orderedAdj b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun a h => h.elim (fun h' => (lt_irrefl a.1) h'.1)
    (fun h' => (lt_irrefl a.1) h'.1)⟩

instance : DecidableRel roleGraph.Adj := fun a b =>
  inferInstanceAs (Decidable (orderedAdj a b ∨ orderedAdj b a))

theorem roleGraph_ordered {a b : Role} (h : a.1 < b.1) :
    roleGraph.Adj a b ↔ (edgeKind a.1 b.1, a.2, b.2) ∈ edges := by
  change orderedAdj a b ∨ orderedAdj b a ↔ _
  simp [orderedAdj, h, not_lt_of_ge h.le]

section

variable {R : Type} [CommRing R] (h : R)

/-- The signed inverse step between parts, with `h` for the outer pair. -/
def directedStep (i j : Fin 3) : R :=
  if i < j then (if i = 0 ∧ j = 2 then h else 1)
  else if j < i then -(if j = 0 ∧ i = 2 then h else 1)
  else 0

theorem directedStep_swap (i j : Fin 3) : directedStep h j i = -directedStep h i j := by
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · simp [directedStep, hlt, not_lt_of_ge hlt.le]
  · simp [directedStep]
  · simp [directedStep, hgt, not_lt_of_ge hgt.le]

/-- The directed step for a pair of roles, determined by their parts. -/
def roleStep (a b : Role) : R := directedStep h a.1 b.1

theorem roleStep_swap (a b : Role) : roleStep h b a = -roleStep h a b :=
  directedStep_swap h a.1 b.1

/-- The vertex at role `r` in the affine block of slope `a` and intercept `x`. -/
def affineVertex (a x : R) (r : Role) : Role × R := (r, x + (r.1.val : R) * a)

theorem directedStep_inverse (hh : 2 * h = 1) {i j : Fin 3} (hij : i < j) :
    directedStep h i j * ((j.val : R) - (i.val : R)) = 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [directedStep, mul_comm h (2 : R)] ; ring

theorem edge_direction (hh : 2 * h = 1) {r s : Role} (hrs : r.1 < s.1) (a x : R) :
    pairDirection (roleStep h) (affineVertex a x r) (affineVertex a x s) = a := by
  change directedStep h r.1 s.1 * ((x + (s.1.val : R) * a) - (x + (r.1.val : R) * a)) = a
  calc
    _ = (directedStep h r.1 s.1 * ((s.1.val : R) - (r.1.val : R))) * a := by ring
    _ = a := by rw [directedStep_inverse h hh hrs, one_mul]

theorem position_eq_of_direction (hh : 2 * h = 1) {r s : Role} (hrs : r.1 < s.1)
    (p q : R) :
    let a := pairDirection (roleStep h) (r,p) (s,q)
    affineVertex a (p - (r.1.val : R) * a) s = (s,q) := by
  dsimp only
  refine Prod.ext (show (affineVertex _ _ s).1 = s from rfl) ?_
  change p - (r.1.val : R) * (directedStep h r.1 s.1 * (q - p)) +
    (s.1.val : R) * (directedStep h r.1 s.1 * (q - p)) = q
  calc
    _ = p + (directedStep h r.1 s.1 * ((s.1.val : R) - (r.1.val : R))) * (q - p) := by ring
    _ = q := by rw [directedStep_inverse h hh hrs, one_mul]; ring

/-- The edge of an affine block corresponding to a template edge. -/
def blockEdge (a x : R) (e : Edge) : Sym2 (Role × R) :=
  s(affineVertex a x (lowerPart e.1, e.2.1), affineVertex a x (upperPart e.1, e.2.2))

theorem part_lt (k : Fin 3) : lowerPart k < upperPart k := by decide +revert +kernel

theorem parts_of_order {i j : Fin 3} (hij : i < j) :
    lowerPart (edgeKind i j) = i ∧ upperPart (edgeKind i j) = j := by
  revert i j
  decide +kernel

theorem kind_of_parts (k : Fin 3) : edgeKind (lowerPart k) (upperPart k) = k := by
  decide +revert +kernel

theorem blockEdge_injective (hh : 2 * h = 1) :
    Function.Injective (fun t : R × R × Edge => blockEdge t.1 t.2.1 t.2.2) := by
  intro ⟨a,x,k,u,v⟩ ⟨b,y,l,p,q⟩ he
  change blockEdge a x (k,u,v) = blockEdge b y (l,p,q) at he
  rcases Sym2.eq_iff.mp he with hdir | hswap
  · have h₁ : (lowerPart k, u) = (lowerPart l, p) := congrArg Prod.fst hdir.1
    have h₂ : (upperPart k, v) = (upperPart l, q) := congrArg Prod.fst hdir.2
    have hlo : lowerPart k = lowerPart l := congrArg Prod.fst h₁
    have hup : upperPart k = upperPart l := congrArg Prod.fst h₂
    have hk : k = l := by
      calc
        k = edgeKind (lowerPart k) (upperPart k) := (kind_of_parts k).symm
        _ = edgeKind (lowerPart l) (upperPart l) := congrArg₂ edgeKind hlo hup
        _ = l := kind_of_parts l
    have hu : u = p := congrArg Prod.snd h₁
    have hv : v = q := congrArg Prod.snd h₂
    subst l
    subst p
    subst q
    have ha : a = b := calc
      a = pairDirection (roleStep h)
          (affineVertex a x (lowerPart k, u)) (affineVertex a x (upperPart k, v)) :=
        (edge_direction h hh (part_lt k) a x).symm
      _ = _ := congrArg₂ (pairDirection (roleStep h)) hdir.1 hdir.2
      _ = b := edge_direction h hh (part_lt k) b y
    subst b
    have hx : x = y := add_right_cancel (congrArg Prod.snd hdir.1)
    subst y
    rfl
  · have h₁ : lowerPart k = upperPart l := congrArg (fun z => z.1.1) hswap.1
    have h₂ : upperPart k = lowerPart l := congrArg (fun z => z.1.1) hswap.2
    have hlt := part_lt k
    rw [h₁, h₂] at hlt
    exact ((not_lt_of_ge (part_lt l).le) hlt).elim

variable [Fintype R] [DecidableEq R]

omit [DecidableEq R] [Fintype R] in
theorem blockEdge_adj (hh : 2 * h = 1) {A : Finset R} {a x : R} {e : Edge}
    (ha : a ∈ A) (he : e ∈ edges) :
    (directionCore roleGraph (roleStep h) A (roleStep_swap h)).Adj
      (affineVertex a x (lowerPart e.1, e.2.1)) (affineVertex a x (upperPart e.1, e.2.2)) := by
  refine ⟨(roleGraph_ordered (part_lt e.1)).mpr ?_, ?_⟩
  · change (edgeKind (lowerPart e.1) (upperPart e.1), e.2.1, e.2.2) ∈ edges
    simpa only [kind_of_parts] using he
  · simpa only [edge_direction h hh (r := (lowerPart e.1, e.2.1))
      (s := (upperPart e.1, e.2.2)) (part_lt e.1)] using ha

omit [DecidableEq R] [Fintype R] in
theorem blockEdge_of_adj (hh : 2 * h = 1) {A : Finset R} {u v : Role × R}
    (huv : (directionCore roleGraph (roleStep h) A (roleStep_swap h)).Adj u v) :
    ∃ a ∈ A, ∃ x, ∃ e ∈ edges, blockEdge a x e = s(u,v) := by
  have ordered (r s : Role) (p q : R) (hrs : r.1 < s.1)
      (hr : roleGraph.Adj r s) (ha : pairDirection (roleStep h) (r,p) (s,q) ∈ A) :
      ∃ a ∈ A, ∃ x, ∃ e ∈ edges, blockEdge a x e = s((r,p),(s,q)) := by
    let a := pairDirection (roleStep h) (r,p) (s,q)
    let x := p - (r.1.val : R) * a
    refine ⟨a, ha, x, (edgeKind r.1 s.1, r.2, s.2), (roleGraph_ordered hrs).mp hr, ?_⟩
    unfold blockEdge
    rw [(parts_of_order hrs).1, (parts_of_order hrs).2]
    have h₁ : affineVertex a x r = (r,p) := Prod.ext rfl (sub_add_cancel _ _)
    have h₂ : affineVertex a x s = (s,q) := position_eq_of_direction h hh hrs p q
    rw [h₁, h₂]
  change roleGraph.Adj u.1 v.1 ∧ pairDirection (roleStep h) u v ∈ A at huv
  rcases huv.1 with hlt | hgt
  · exact ordered u.1 v.1 u.2 v.2 hlt.1 (.inl hlt) huv.2
  · obtain ⟨a, ha, x, e, he, heq⟩ :=
      ordered v.1 u.1 v.2 u.2 hgt.1 (.inl hgt)
        ((pairDirection_swap (roleStep h) (roleStep_swap h) u v).symm ▸ huv.2)
    exact ⟨a, ha, x, e, he, heq.trans Sym2.eq_swap⟩

end

end GapExtremal.R434.H54
