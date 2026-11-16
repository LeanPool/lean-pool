/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Tactic.Positivity.Basic

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import LeanPool.DeciSigma1.Automata.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Systems of difference constraints

A system of difference constraints over a finite index type `ι` is a set of inequalities
`x i + c ≤ x j` between integer unknowns; it is the constraint graph with an edge `i → j` of
weight `c` for each inequality. The shortening arguments choose the number of letters to
delete from each periodic factor, and the lengths of the periodic continuations of several
words, as solutions of such systems.

A closed walk of positive weight makes a system infeasible. Conversely, if there is no
positive cycle, the maximal weights of simple walks give a nonnegative solution bounded by
`|ι|` times the largest edge weight (`exists_sat_nonneg_bounded`). Above given lower bounds
there is then a least solution, and each of its values is reached from a vertex at its lower
bound along a duplicate-free path of tight constraints (`least_above`); this is how the
shortening bounds the size of the least solution.

## Main declarations

- `DifferenceSystem`, `DifferenceSystem.Sat`: systems of difference constraints and their
  solutions.
- `DifferenceSystem.weight`, `DifferenceSystem.HasPositiveCycle`: weights of walks and positive
  cycles.
- `DifferenceSystem.exists_sat_nonneg_bounded`: a system without positive cycles has a bounded
  nonnegative solution.
- `DifferenceSystem.exists_long_solution`: such a system has a natural-number solution above
  any lower bounds.
- `DifferenceSystem.least_above`: the least solution above lower bounds, with tight paths.
- `DifferenceSystem.ofFinset`: the system of a finite set of constraints.
-/

@[expose] public section


namespace DeciSigma1.Arithmetic

/-- A system of difference constraints on `ι`: `edgeWeight i j = some c` is the constraint
`x i + c ≤ x j`, and `none` means that there is no constraint from `i` to `j`. -/
structure DifferenceSystem (ι : Type) where
  /-- The weight of the constraint from `i` to `j`, if any. -/
  edgeWeight : ι → ι → Option ℤ

namespace DifferenceSystem

variable {ι : Type} (D : DifferenceSystem ι)

/-- `x` satisfies every constraint of the system. -/
def Sat (x : ι → ℤ) : Prop := ∀ i j c, D.edgeWeight i j = some c → x i + c ≤ x j

/-- A walk: consecutive vertices are joined by a constraint. -/
def IsWalk (p : List ι) : Prop := p.IsChain (fun u v => (D.edgeWeight u v).isSome)

instance (p : List ι) : Decidable (D.IsWalk p) :=
  inferInstanceAs (Decidable (p.IsChain _))

/-- The total weight of a list of vertices, as a walk; a missing constraint counts `0`. -/
def weight : List ι → ℤ
  | i :: j :: p => (D.edgeWeight i j).getD 0 + weight (j :: p)
  | _ => 0

/-- A closed walk of positive total weight. -/
def HasPositiveCycle :
    Prop := ∃ (i : ι) (p : List ι), D.IsWalk (i :: p ++ [i]) ∧ 0 < D.weight (i :: p ++ [i])

variable {D}

@[simp] theorem weight_nil : D.weight [] = 0 := rfl

@[simp] theorem weight_singleton (i : ι) : D.weight [i] = 0 := rfl

@[simp] theorem weight_cons_cons (i j : ι) (p : List ι) :
    D.weight (i :: j :: p) = (D.edgeWeight i j).getD 0 + D.weight (j :: p) := rfl

theorem weight_append_cons (s t : List ι) (j : ι) :
    D.weight (s ++ j :: t) = D.weight (s ++ [j]) + D.weight (j :: t) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    cases s with
    | nil => simp
    | cons b s =>
      simp only [List.cons_append, weight_cons_cons] at ih ⊢
      rw [ih]; ring

theorem weight_snoc_snoc (s : List ι) (i j : ι) :
    D.weight (s ++ [i, j]) = D.weight (s ++ [i]) + (D.edgeWeight i j).getD 0 := by
  rw [weight_append_cons s [j] i]; simp

theorem isWalk_cons_cons {i j : ι} {p : List ι} :
    D.IsWalk (i :: j :: p) ↔ (D.edgeWeight i j).isSome ∧ D.IsWalk (j :: p) :=
  List.isChain_cons_cons

/-! ## Solutions bound walk weights -/

theorem Sat.add_const {x : ι → ℤ} (h : D.Sat x) (c : ℤ) : D.Sat (fun i => x i + c) := by
  intro i j d hd
  have := h i j d hd
  linarith

/-! ## Weights of walks -/

/-- The largest positive constraint weight (`0` if there is none). -/
def maxNonnegativeWeight [Fintype ι] (D : DifferenceSystem ι) : ℕ :=
  Finset.univ.sup (fun ij : ι × ι => ((D.edgeWeight ij.1 ij.2).getD 0).toNat)

theorem le_maxNonnegativeWeight [Fintype ι] {i j : ι} {c : ℤ} (h : D.edgeWeight i j = some c) :
    c ≤ D.maxNonnegativeWeight := by
  have : ((D.edgeWeight i j).getD 0).toNat ≤ D.maxNonnegativeWeight :=
    Finset.le_sup (f := fun ij : ι × ι => ((D.edgeWeight ij.1 ij.2).getD 0).toNat)
      (Finset.mem_univ (i, j))
  rw [h, Option.getD_some] at this
  omega

theorem weight_le_maxNonnegativeWeight [Fintype ι] :
    ∀ p : List ι, D.IsWalk p → D.weight p ≤ (p.length - 1 : ℕ) * (D.maxNonnegativeWeight : ℤ)
  | [], _ => by simp
  | [_], _ => by simp
  | i :: j :: p, hw => by
    rw [isWalk_cons_cons] at hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hw.1
    have h1 := le_maxNonnegativeWeight hc
    have h2 := weight_le_maxNonnegativeWeight (j :: p) hw.2
    rw [weight_cons_cons, hc, Option.getD_some]
    simp only [List.length_cons, Nat.add_sub_cancel] at h2 ⊢
    push_cast at h2 ⊢
    nlinarith

/-- Along a walk inside a set on which `x` satisfies every constraint, `x` grows at least by the
weight of the walk. -/
theorem weight_le_local {ι : Type}
    {D : DifferenceSystem ι} {x : ι → ℤ} (P : ι → Prop)
    (hP : ∀ u v c, P u → P v → D.edgeWeight u v = some c → x u + c ≤ x v) :
    ∀ (i : ι) (q : List ι), D.IsWalk (i :: q) → (∀ z ∈ i :: q, P z) →
      x i + D.weight (i :: q) ≤ x ((i :: q).getLast (List.cons_ne_nil _ _))
  | i, [], _, _ => by simp
  | i, j :: q, hw, hall => by
    rw [DifferenceSystem.isWalk_cons_cons] at hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hw.1
    have h1 := hP i j c (hall i List.mem_cons_self)
      (hall j (List.mem_cons_of_mem _ List.mem_cons_self)) hc
    have h2 :=
        Arithmetic.DifferenceSystem.weight_le_local P hP j q hw.2
            (fun z hz => hall z (List.mem_cons_of_mem _ hz))
    rw [DifferenceSystem.weight_cons_cons, hc, Option.getD_some, List.getLast_cons_cons]
    linarith

theorem isWalk_append_singleton {p : List ι} {i j : ι} (hp : D.IsWalk p)
    (hl : p.getLast? = some i) (hij : (D.edgeWeight i j).isSome) : D.IsWalk (p ++ [j]) := by
  unfold IsWalk at hp ⊢
  rw [List.isChain_append]
  refine ⟨hp, List.isChain_singleton _, ?_⟩
  intro x hx y hy
  rw [hl, Option.mem_some_iff] at hx
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hx; subst hy; exact hij

/-! ## Feasibility -/

open Classical in
/-- Without a positive cycle, the maximal weights of simple walks ending at each vertex (the
empty walk counts `0`) form a nonnegative solution bounded by
`(|ι| - 1) · maxNonnegativeWeight`. -/
theorem exists_sat_nonneg_of_no_positiveCycle [Fintype ι]
    (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ ((Fintype.card ι - 1 : ℕ) : ℤ) *
        D.maxNonnegativeWeight := by
  set n := Fintype.card ι
  -- candidate simple paths ending at `i`
  let P : ι → Finset (List ι) := fun i =>
    (Automata.wordsUpTo n).filter (fun q => q.Nodup ∧ q.getLast? = some i ∧ D.IsWalk q)
  have mem_P : ∀ i q, q ∈ P i ↔ q.Nodup ∧ q.getLast? = some i ∧ D.IsWalk q := by
    intro i q
    simp only [P, Finset.mem_filter, Automata.mem_wordsUpTo, and_iff_right_iff_imp]
    exact fun h => h.1.length_le_card
  have single : ∀ i, [i] ∈ P i := fun i => (mem_P i [i]).mpr
    ⟨List.nodup_singleton i, rfl, List.isChain_singleton i⟩
  let x : ι → ℤ := fun i => ((P i).sup (fun q => (D.weight q).toNat) : ℕ)
  have le_x : ∀ i q, q ∈ P i → D.weight q ≤ x i := by
    intro i q hq
    have : (D.weight q).toNat ≤ (P i).sup (fun q => (D.weight q).toNat) :=
      Finset.le_sup (f := fun q => (D.weight q).toNat) hq
    simp only [x]
    omega
  have attained : ∀ i, ∃ q ∈ P i, D.weight q = x i := by
    intro i
    obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_eq_sup (P i) ⟨[i], single i⟩
      (fun q => (D.weight q).toNat)
    by_cases hneg : 0 ≤ D.weight q
    · refine ⟨q, hq, ?_⟩
      simp only [x, hqx]; omega
    · refine ⟨[i], single i, ?_⟩
      simp only [x, hqx, weight_singleton]; omega
  refine ⟨x, ?_, fun i => ⟨by simp [x], ?_⟩⟩
  · intro i j c hc
    obtain ⟨q, hq, hqx⟩ := attained i
    obtain ⟨hnd, hlast, hw⟩ := (mem_P i q).mp hq
    have hqne : q ≠ [] := by rintro rfl; simp at hlast
    by_cases hj : j ∈ q
    · -- the extension would close a cycle: cut it off
      obtain ⟨s, t, rfl⟩ := List.append_of_mem hj
      have hsplit := List.isChain_split.mp hw
      have hcyc : D.IsWalk (j :: t ++ [j]) := by
        refine isWalk_append_singleton hsplit.2 ?_ (by rw [hc]; rfl)
        rw [← hlast, List.getLast?_append_cons]
      have hcyc_wt : D.weight (j :: t ++ [j]) = D.weight (j :: t) + c := by
        have hl : (j :: t).getLast? = some i := by rw [← hlast, List.getLast?_append_cons]
        obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hl
        rw [hu, List.append_assoc, List.singleton_append, weight_snoc_snoc, hc, Option.getD_some]
      have hnot : ¬ 0 < D.weight (j :: t ++ [j]) := fun hpos => h ⟨j, t, hcyc, hpos⟩
      have hmem : s ++ [j] ∈ P j :=
        (mem_P j _).mpr ⟨hnd.sublist (by simp), by simp, hsplit.1⟩
      have hwq := weight_append_cons (D := D) s t j
      have := le_x j _ hmem
      rw [← hqx]
      linarith
    · have hmem : q ++ [j] ∈ P j := by
        refine (mem_P j _).mpr ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton j, ?_⟩,
          by simp, isWalk_append_singleton hw hlast (by rw [hc]; rfl)⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact fun hab => hj (hab ▸ ha)
      have hwq : D.weight (q ++ [j]) = D.weight q + c := by
        obtain ⟨u, hu⟩ := List.getLast?_eq_some_iff.mp hlast
        rw [hu, List.append_assoc, List.singleton_append, weight_snoc_snoc, hc, Option.getD_some]
      have := le_x j _ hmem
      rw [← hqx]
      linarith
  · have hsup : (P i).sup (fun q => (D.weight q).toNat) ≤ (n - 1) * D.maxNonnegativeWeight := by
      refine Finset.sup_le fun q hq => ?_
      obtain ⟨hnd, _, hw⟩ := (mem_P i q).mp hq
      have hlen : q.length ≤ n := hnd.length_le_card
      have h1 := weight_le_maxNonnegativeWeight q hw
      have h2 : ((q.length - 1 : ℕ) : ℤ) * (D.maxNonnegativeWeight : ℤ) ≤
          ((n - 1 : ℕ) : ℤ) * (D.maxNonnegativeWeight : ℤ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hlen 1)
          (by positivity)
      rw [Int.toNat_le]
      push_cast [Nat.cast_mul]
      linarith
    simp only [x]
    exact_mod_cast hsup

/-- A system without positive cycles has a nonnegative solution bounded by
`|ι| · maxNonnegativeWeight`. -/
theorem exists_sat_nonneg_bounded [Fintype ι] (h : ¬ D.HasPositiveCycle) :
    ∃ x, D.Sat x ∧ ∀ i, 0 ≤ x i ∧ x i ≤ (Fintype.card ι : ℤ) * D.maxNonnegativeWeight := by
  obtain ⟨x, hx, hb⟩ := exists_sat_nonneg_of_no_positiveCycle h
  refine ⟨x, hx, fun i => ⟨(hb i).1, (hb i).2.trans ?_⟩⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (by positivity)

/-- A system without positive cycles has a natural-number solution above any lower bounds. -/
theorem exists_long_solution [Finite ι] (D : DifferenceSystem ι)
    (h : ¬ D.HasPositiveCycle) (lower : ι → ℕ) :
    ∃ L : ι → ℕ, D.Sat (fun i => (L i : ℤ)) ∧ ∀ i, lower i ≤ L i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨x, hx, hb⟩ := D.exists_sat_nonneg_bounded h
  refine ⟨fun i => (x i).toNat + Finset.univ.sup lower, ?_, fun i => ?_⟩
  · have := hx.add_const ((Finset.univ.sup lower : ℕ) : ℤ)
    intro i j c hc
    have h1 := this i j c hc
    have h2 := (hb i).1
    have h3 := (hb j).1
    simp only [Nat.cast_add, Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h3]
    exact h1
  · have := Finset.le_sup (f := lower) (Finset.mem_univ i)
    change lower i ≤ (x i).toNat + Finset.univ.sup lower
    omega

/-! ## Least solution above lower bounds -/

/-- The constraint from `u` to `v` holds with equality at `x`. -/
def IsTight (D : DifferenceSystem ι) (x : ι → ℤ) (u v : ι) :
    Prop := ∃ c, D.edgeWeight u v = some c ∧ x u + c = x v

open Classical in
/-- Given lower bounds `floor` and one solution above them, there is a least solution above
them, and every vertex is the end of a duplicate-free path of tight constraints that starts at
a vertex where the least solution equals its lower bound. -/
theorem least_above (floor x0 : ι → ℤ) (h0 : D.Sat x0) (hf : floor ≤ x0) :
    ∃ xm, D.Sat xm ∧ floor ≤ xm ∧ (∀ x, D.Sat x → floor ≤ x → xm ≤ x) ∧
      ∀ i, ∃ p : List ι, p.Nodup ∧ p.getLast? = some i ∧
        (∃ j, p.head? = some j ∧ xm j = floor j) ∧ p.IsChain (D.IsTight xm) := by
  have hex : ∀ i, ∃ n : ℕ, ∃ x, D.Sat x ∧ floor ≤ x ∧ x i = floor i + n := by
    intro i
    have hfi : floor i ≤ x0 i := hf i
    exact ⟨(x0 i - floor i).toNat, x0, h0, hf, by omega⟩
  let xm : ι → ℤ := fun i => floor i + Nat.find (hex i)
  have hmin : ∀ x, D.Sat x → floor ≤ x → xm ≤ x := by
    intro x hx hfx i
    have hfi : floor i ≤ x i := hfx i
    have := Nat.find_min' (hex i) ⟨x, hx, hfx, (by omega :
      x i = floor i + (x i - floor i).toNat)⟩
    simp only [xm]
    omega
  have hsat : D.Sat xm := by
    intro i j c hc
    obtain ⟨y, hy, hfy, hyj⟩ := Nat.find_spec (hex j)
    have h1 := hmin y hy hfy i
    have h2 := hy i j c hc
    simp only [xm] at h1 ⊢
    linarith
  have hfm : floor ≤ xm := fun i => by simp only [xm]; omega
  refine ⟨xm, hsat, hfm, hmin, fun i => ?_⟩
  -- the vertices with a duplicate-free tight path to `i`
  let R : ι → Prop := fun j => ∃ p : List ι, p.Nodup ∧ p.getLast? = some i ∧ p.head? = some j ∧
    p.IsChain (D.IsTight xm)
  have hRi : R i := ⟨[i], List.nodup_singleton i, rfl, rfl, List.isChain_singleton i⟩
  have hRclosed : ∀ u v, D.IsTight xm u v → R v → R u := by
    rintro u v huv ⟨p, hnd, hlast, hhead, hch⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = v :: p' := by
      cases p with
      | nil => simp at hhead
      | cons a p' => simp only [List.head?_cons, Option.some_inj] at hhead; exact ⟨p', hhead ▸ rfl⟩
    by_cases hu : u ∈ v :: p'
    · obtain ⟨s, t, hst⟩ := List.append_of_mem hu
      refine ⟨u :: t, ?_, ?_, rfl, ?_⟩
      · rw [hst] at hnd; exact hnd.sublist (List.sublist_append_right _ _)
      · rw [hst] at hlast; rw [← hlast, List.getLast?_append_cons]
      · rw [hst] at hch; exact (List.isChain_split.mp hch).2
    · refine ⟨u :: v :: p', List.nodup_cons.mpr ⟨hu, hnd⟩, ?_, rfl, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hlast
      · exact List.isChain_cons_cons.mpr ⟨huv, hch⟩
  by_contra hno
  have hnoR : ∀ j, R j → floor j < xm j := by
    intro j ⟨p, hnd, hlast, hhead, hch⟩
    rcases lt_or_eq_of_le (hfm j) with h | h
    · exact h
    · exact absurd ⟨p, hnd, hlast, ⟨j, hhead, h.symm⟩, hch⟩ hno
  -- lowering every vertex of `R` by one keeps a solution above the floors
  let x' : ι → ℤ := fun v => if R v then xm v - 1 else xm v
  have hsat' : D.Sat x' := by
    intro u v c hc
    have huv := hsat u v c hc
    by_cases hv : R v
    · by_cases hu : R u
      · simp only [x', hu, hv, ite_true]; linarith
      · have hnt : xm u + c ≠ xm v := fun he => hu (hRclosed u v ⟨c, hc, he⟩ hv)
        simp only [x', hu, hv, ite_true, ite_false]; omega
    · by_cases hu : R u
      · simp only [x', hu, hv, ite_true, ite_false]; linarith
      · simp only [x', hu, hv, ite_false]; exact huv
  have hf' : floor ≤ x' := by
    intro v
    by_cases hv : R v
    · simp only [x', hv, ite_true]; have := hnoR v hv; omega
    · simp only [x', hv, ite_false]; exact hfm v
  have := hmin x' hsat' hf' i
  simp only [x', hRi, ite_true] at this
  omega

/-! ## Merging several constraints on one ordered pair -/

/-- The system of a finite set of constraints `(i, j, c)`, each meaning `x i + c ≤ x j`; for
each ordered pair the strongest constraint is kept. -/
def ofFinset [DecidableEq ι] (E : Finset (ι × ι × ℤ)) : DifferenceSystem ι :=
  ⟨fun i j => ((E.filter (fun e => e.1 = i ∧ e.2.1 = j)).image (fun e => e.2.2)).max⟩

theorem sat_ofFinset_iff [DecidableEq ι] (E : Finset (ι × ι × ℤ)) (x : ι → ℤ) :
    (ofFinset E).Sat x ↔ ∀ e ∈ E, x e.1 + e.2.2 ≤ x e.2.1 := by
  constructor
  · intro h e he
    set s := (E.filter (fun e' => e'.1 = e.1 ∧ e'.2.1 = e.2.1)).image (fun e => e.2.2)
    have hmem : e.2.2 ∈ s := Finset.mem_image.mpr ⟨e, by simp [he], rfl⟩
    obtain ⟨m, hm⟩ := Finset.max_of_mem hmem
    have hle : e.2.2 ≤ m := Finset.le_max_of_eq hmem hm
    have := h e.1 e.2.1 m hm
    linarith
  · intro h i j c hc
    have hmem := Finset.mem_of_max hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨heE, rfl, rfl⟩ := by simpa using he
    exact h e heE

end DifferenceSystem

end DeciSigma1.Arithmetic
