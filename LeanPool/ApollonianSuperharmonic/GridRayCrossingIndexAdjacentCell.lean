/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Algebra.Group.Fin.Basic

public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import LeanPool.ApollonianSuperharmonic.GridRayCrossingIndex


-- [TABLET NODE: GridRayCrossingIndexAdjacentCell]

/-!
# GridRayCrossingIndexAdjacentCell

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace AdjacentCellCrossings

private theorem open_edges_no_reverse {α : Type}
    {p : List α} (hp : p.Nodup) {u v : α}
    (huv : (u, v) ∈ p.zip p.tail) (hvu : (v, u) ∈ p.zip p.tail) : False := by
  rw [List.mem_iff_getElem] at huv hvu
  rcases huv with ⟨i, hi, huv⟩
  rcases hvu with ⟨j, hj, hvu⟩
  rw [List.getElem_zip, List.getElem_tail] at huv hvu
  injection huv with huv₁ huv₂
  injection hvu with hvu₁ hvu₂
  have hij : i + 1 = j :=
    (hp.getElem_inj_iff).mp (huv₂.trans hvu₁.symm)
  have hji : j + 1 = i :=
    (hp.getElem_inj_iff).mp (hvu₂.trans huv₁.symm)
  omega
private theorem open_head_last_not_edge {α : Type}
    {p : List α} (hp : p.Nodup) (hlen : 3 ≤ p.length) {x y : α}
    (hhead : p.head? = some x) (hlast : p.getLast? = some y) :
    (x, y) ∉ p.zip p.tail := by
  intro hxy
  rw [List.mem_iff_getElem] at hxy
  rcases hxy with ⟨i, hi, hxy⟩
  rw [List.getElem_zip, List.getElem_tail] at hxy
  injection hxy with hix hiy
  have hpne : p ≠ [] := by
    intro hp0
    simp [hp0] at hlen
  have hzero : 0 < p.length := by omega
  have hx0 : p[0] = x := by
    rw [← List.head_eq_getElem hpne]
    simpa [List.head?_eq_some_head hpne] using hhead
  have hyLast : p[p.length - 1] = y := by
    rw [← List.getLast_eq_getElem hpne]
    rw [List.getLast?_eq_getLast_of_ne_nil hpne] at hlast
    exact Option.some.inj hlast
  have hi0 : i = 0 := (hp.getElem_inj_iff).mp (hix.trans hx0.symm)
  have hiLast : i + 1 = p.length - 1 :=
    (hp.getElem_inj_iff).mp (hiy.trans hyLast.symm)
  omega
private theorem cyclic_edges_no_reverse {α : Type}
    {p : List α} (hp : p.Nodup) (hlen : 3 ≤ p.length) {x y u v : α}
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (huv : (u, v) ∈ p.zip p.tail ∨ (u = y ∧ v = x))
    (hvu : (v, u) ∈ p.zip p.tail ∨ (v = y ∧ u = x)) : False := by
  have hpne : p ≠ [] := by
    intro hp0
    simp [hp0] at hlen
  have hxy : x ≠ y := by
    have hxhead : p.head hpne = x := by
      rcases (List.head?_eq_some_iff.mp hhead) with ⟨ys, rfl⟩
      rfl
    have hylast : p.getLast hpne = y := by
      rw [List.getLast?_eq_getLast_of_ne_nil hpne] at hlast
      exact Option.some.inj hlast
    intro h
    have heq : p.head hpne = p.getLast hpne := by
      rw [hxhead, hylast, h]
    rcases (List.Nodup.head_eq_getLast_iff hpne hp).mp heq with ⟨z, rfl⟩
    simp at hlen
  rcases huv with huv | ⟨rfl, rfl⟩
  · rcases hvu with hvu | ⟨rfl, rfl⟩
    · exact open_edges_no_reverse hp huv hvu
    · exact open_head_last_not_edge hp hlen hhead hlast huv
  · rcases hvu with hvu | h
    · exact open_head_last_not_edge hp hlen hhead hlast hvu
    · exact hxy h.1
private theorem open_last_head_not_edge {α : Type}
    {p : List α} (hp : p.Nodup) (hlen : 2 ≤ p.length) {x y : α}
    (hlast : p.getLast? = some y) :
    (y, x) ∉ p.zip p.tail := by
  intro hyx
  rw [List.mem_iff_getElem] at hyx
  rcases hyx with ⟨i, hi, hyx⟩
  have hi' : i < p.tail.length := by
    simpa [List.length_zip] using hi
  have hip : i + 1 < p.length := by
    simp only [List.length_tail] at hi'
    omega
  rw [List.getElem_zip, List.getElem_tail] at hyx
  injection hyx with hiy hix
  have hpne : p ≠ [] := by
    intro hp0
    simp [hp0] at hlen
  have hyLast : p[p.length - 1] = y := by
    rw [← List.getLast_eq_getElem hpne]
    rw [List.getLast?_eq_getLast_of_ne_nil hpne] at hlast
    exact Option.some.inj hlast
  have hiLast : i = p.length - 1 :=
    (hp.getElem_inj_iff).mp (hiy.trans hyLast.symm)
  omega
private theorem open_edges_nodup {α : Type}
    {p : List α} (hp : p.Nodup) : (p.zip p.tail).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  have hfirst := congrArg Prod.fst hij
  simp only [List.getElem_zip] at hfirst
  apply Fin.ext
  exact (hp.getElem_inj_iff).mp hfirst
private theorem cyclic_edge_list_nodup {α : Type}
    {p : List α} (hp : p.Nodup) (hlen : 3 ≤ p.length) {x y : α}
    (hlast : p.getLast? = some y) :
    ((p.zip p.tail) ++ [(y, x)]).Nodup := by
  rw [List.nodup_append]
  refine ⟨open_edges_nodup hp, by simp, ?_⟩
  intro a ha b hb hab
  have hbEq : b = (y, x) := by simpa using hb
  apply open_last_head_not_edge hp (by omega) hlast
  rw [← hbEq, ← hab]
  exact ha
private theorem signed_target_sum_formula {α : Type} [DecidableEq α]
    (edges : List (α × α)) (he : edges.Nodup) (u v : α) (huv : u ≠ v) :
    (edges.map (fun e => if e = (u, v) then (1 : Int)
      else if e = (v, u) then -1 else 0)).sum =
      (if (u, v) ∈ edges then 1 else 0) +
        (if (v, u) ∈ edges then -1 else 0) := by
  induction edges with
  | nil => simp
  | cons e edges ih =>
      simp only [List.nodup_cons] at he
      rw [List.map_cons, List.sum_cons, ih he.2]
      by_cases heu : e = (u, v)
      · subst e
        simp [he.1, huv]
      · by_cases hev : e = (v, u)
        · subst e
          simp [he.1, heu, huv, add_comm]
        · have heu' : (u, v) ≠ e := Ne.symm heu
          have hev' : (v, u) ≠ e := Ne.symm hev
          simp [heu, hev, heu', hev']
private theorem gaussian_eq_iff (a b : GaussianInt) : a = b ↔ a.re = b.re ∧ a.im = b.im := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hr, hi⟩
    apply Zsqrtd.ext <;> assumption
private theorem east_step_delta (q a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
    (if b = a + ⟨0, 1⟩ ∧ a.im = (q + 1).im ∧ a.re ≤ (q + 1).re then 1
     else if b = a - ⟨0, 1⟩ ∧ b.im = (q + 1).im ∧ a.re ≤ (q + 1).re then -1
     else 0) -
    (if b = a + ⟨0, 1⟩ ∧ a.im = q.im ∧ a.re ≤ q.re then 1
     else if b = a - ⟨0, 1⟩ ∧ b.im = q.im ∧ a.re ≤ q.re then -1
     else 0) =
      (if (a, b) = (q + 1, q + 1 + ⟨0, 1⟩) then 1
       else if (a, b) = (q + 1 + ⟨0, 1⟩, q + 1) then -1 else 0) := by
  rcases hab with (rfl | rfl | rfl | rfl) <;>
    simp [gaussian_eq_iff] <;> omega
private def NorthStepDelta (q a b : GaussianInt) : Prop :=
    (if b = a + ⟨0, 1⟩ ∧ a.im = (q + ⟨0, 1⟩).im ∧
        a.re ≤ (q + ⟨0, 1⟩).re then 1
     else if b = a - ⟨0, 1⟩ ∧ b.im = (q + ⟨0, 1⟩).im ∧
        a.re ≤ (q + ⟨0, 1⟩).re then -1
     else 0) -
    (if b = a + ⟨0, 1⟩ ∧ a.im = q.im ∧ a.re ≤ q.re then 1
     else if b = a - ⟨0, 1⟩ ∧ b.im = q.im ∧ a.re ≤ q.re then -1
     else 0) =
      (if (a, b) = (q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) then 1
       else if (a, b) = (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) then -1 else 0) +
      (if a.im = q.im + 1 ∧ a.re ≤ q.re then 1 else 0) -
      (if b.im = q.im + 1 ∧ b.re ≤ q.re then 1 else 0)

private theorem northDeltaEast (q a : GaussianInt) :
    NorthStepDelta q a (a + 1) := by
  simp [NorthStepDelta, gaussian_eq_iff]; omega

private theorem northDeltaWest (q a : GaussianInt) :
    NorthStepDelta q a (a - 1) := by
  simp [NorthStepDelta, gaussian_eq_iff]; omega

private theorem northDeltaNorth (q a : GaussianInt) :
    NorthStepDelta q a (a + ⟨0, 1⟩) := by
  by_cases horizontal : a.re ≤ q.re <;>
    by_cases same : a.im = q.im <;>
    by_cases above : a.im = q.im + 1 <;>
    simp [NorthStepDelta, gaussian_eq_iff, horizontal, same, above] <;> omega

private theorem northDeltaSouth (q a : GaussianInt) :
    NorthStepDelta q a (a - ⟨0, 1⟩) := by
  by_cases horizontal : a.re ≤ q.re <;>
    by_cases same : a.im = q.im <;>
    by_cases above : a.im = q.im + 1 <;>
    simp [NorthStepDelta, gaussian_eq_iff, horizontal, same, above] <;> omega

private theorem north_step_delta (q a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
    (if b = a + ⟨0, 1⟩ ∧ a.im = (q + ⟨0, 1⟩).im ∧
        a.re ≤ (q + ⟨0, 1⟩).re then 1
     else if b = a - ⟨0, 1⟩ ∧ b.im = (q + ⟨0, 1⟩).im ∧
        a.re ≤ (q + ⟨0, 1⟩).re then -1
     else 0) -
    (if b = a + ⟨0, 1⟩ ∧ a.im = q.im ∧ a.re ≤ q.re then 1
     else if b = a - ⟨0, 1⟩ ∧ b.im = q.im ∧ a.re ≤ q.re then -1
     else 0) =
      (if (a, b) = (q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) then 1
       else if (a, b) = (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) then -1 else 0) +
      (if a.im = q.im + 1 ∧ a.re ≤ q.re then 1 else 0) -
      (if b.im = q.im + 1 ∧ b.re ≤ q.re then 1 else 0) := by
  rcases hab with rfl | rfl | rfl | rfl
  · exact northDeltaEast q a
  · exact northDeltaWest q a
  · exact northDeltaNorth q a
  · exact northDeltaSouth q a
private theorem zipWith_eq_map_zip {α β γ : Type} (f : α → β → γ)
    (l : List α) (r : List β) :
    List.zipWith f l r = (l.zip r).map (fun e => f e.1 e.2) := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
      cases r <;> simp [ih]
private theorem map_sub_sum (edges : List (GaussianInt × GaussianInt))
    (f g : GaussianInt → GaussianInt → Int) :
    (edges.map (fun e => f e.1 e.2 - g e.1 e.2)).sum =
      (edges.map (fun e => f e.1 e.2)).sum -
        (edges.map (fun e => g e.1 e.2)).sum := by
  induction edges with
  | nil => simp
  | cons e edges ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega
private theorem cyclic_sum_sub
    (p : List GaussianInt) (x y : GaussianInt)
    (f g h : GaussianInt → GaussianInt → Int)
    (hedge : ∀ a b, (a, b) ∈ p.zip p.tail ∨ (a = y ∧ b = x) →
      f a b - g a b = h a b) :
    ((List.zipWith f p p.tail).sum + f y x) -
        ((List.zipWith g p p.tail).sum + g y x) =
      (((p.zip p.tail) ++ [(y, x)]).map (fun e => h e.1 e.2)).sum := by
  rw [zipWith_eq_map_zip, zipWith_eq_map_zip, List.map_append,
    List.sum_append]
  simp only [List.map_singleton, List.sum_singleton]
  have hsub := map_sub_sum (p.zip p.tail) f g
  have hopen : (p.zip p.tail).map (fun e => f e.1 e.2 - g e.1 e.2) =
      (p.zip p.tail).map (fun e => h e.1 e.2) := by
    apply List.map_congr_left
    intro e he
    exact hedge e.1 e.2 (Or.inl he)
  have hclose := hedge y x (Or.inr ⟨rfl, rfl⟩)
  rw [hopen] at hsub
  omega
private theorem zip_potential_sum (p : List GaussianInt) (x y : GaussianInt)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (potential : GaussianInt → Int) :
    (List.zipWith (fun a b => potential a - potential b) p p.tail).sum =
      potential x - potential y := by
  induction p generalizing x y with
  | nil => simp at hhead
  | cons a p ih =>
      cases p with
      | nil =>
          simp at hhead hlast
          subst x
          subst y
          simp
      | cons b p =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst x
          have htailLast : (b :: p).getLast? = some y := by
            simpa using hlast
          have hih := ih b y rfl htailLast
          simp only [List.tail_cons] at hih
          simp only [List.tail_cons, List.zipWith_cons_cons, List.sum_cons]
          rw [hih]
          omega
private theorem map_augmented_sum (edges : List (GaussianInt × GaussianInt))
    (sign : GaussianInt → GaussianInt → Int)
    (potential : GaussianInt → Int) :
    (edges.map (fun e => sign e.1 e.2 + potential e.1 - potential e.2)).sum =
      (edges.map (fun e => sign e.1 e.2)).sum +
        (edges.map (fun e => potential e.1 - potential e.2)).sum := by
  induction edges with
  | nil => simp
  | cons e edges ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

end AdjacentCellCrossings

open AdjacentCellCrossings

theorem GridRayCrossingIndexAdjacentCell
    (p : List GaussianInt) (x y : GaussianInt)
    (hhead : p.head? = some x) (hlast : p.getLast? = some y)
    (hnodup : p.Nodup) (hlen : 3 ≤ p.length)
    (hadj : ∀ a b, (a, b) ∈ p.zip p.tail → FourNeighborAdjacent a b)
    (hclose : FourNeighborAdjacent y x) :
    let cyclicEdges := (p.zip p.tail) ++ [(y, x)]
    ∀ q : LatticeCell,
      (((q + 1, q + 1 + ⟨0, 1⟩) ∉ cyclicEdges ∧
          (q + 1 + ⟨0, 1⟩, q + 1) ∉ cyclicEdges) →
          GridRayCrossingIndex (q + 1) p = GridRayCrossingIndex q p) ∧
      (((q + 1, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges ∨
          (q + 1 + ⟨0, 1⟩, q + 1) ∈ cyclicEdges) →
          Int.natAbs (GridRayCrossingIndex (q + 1) p -
            GridRayCrossingIndex q p) = 1) ∧
      (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∉ cyclicEdges ∧
          (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∉ cyclicEdges) →
          GridRayCrossingIndex (q + ⟨0, 1⟩) p =
            GridRayCrossingIndex q p) ∧
      (((q + 1 + ⟨0, 1⟩, q + ⟨0, 1⟩) ∈ cyclicEdges ∨
          (q + ⟨0, 1⟩, q + 1 + ⟨0, 1⟩) ∈ cyclicEdges) →
          Int.natAbs (GridRayCrossingIndex (q + ⟨0, 1⟩) p -
            GridRayCrossingIndex q p) = 1) := by
-- BODY
  dsimp only
  intro q
  let edges := (p.zip p.tail) ++ [(y, x)]
  have hedges : edges.Nodup := cyclic_edge_list_nodup hnodup hlen hlast
  have edge_adj : ∀ a b, (a, b) ∈ p.zip p.tail ∨ (a = y ∧ b = x) →
      FourNeighborAdjacent a b := by
    intro a b hab
    rcases hab with hab | ⟨rfl, rfl⟩
    · exact hadj a b hab
    · exact hclose
  let eastU : GaussianInt := q + 1
  let eastV : GaussianInt := q + 1 + ⟨0, 1⟩
  let northU : GaussianInt := q + 1 + ⟨0, 1⟩
  let northV : GaussianInt := q + ⟨0, 1⟩
  have east_ne : eastU ≠ eastV := by
    intro h
    apply_fun Zsqrtd.im at h
    simp [eastU, eastV] at h
  have north_ne : northU ≠ northV := by
    intro h
    apply_fun Zsqrtd.re at h
    simp [northU, northV] at h
  let eastSign : GaussianInt → GaussianInt → Int := fun a b =>
    if (a, b) = (eastU, eastV) then 1
    else if (a, b) = (eastV, eastU) then -1 else 0
  let northSign : GaussianInt → GaussianInt → Int := fun a b =>
    if (a, b) = (northU, northV) then 1
    else if (a, b) = (northV, northU) then -1 else 0
  have east_delta : GridRayCrossingIndex (q + 1) p -
      GridRayCrossingIndex q p =
      (edges.map (fun e => eastSign e.1 e.2)).sum := by
    rw [GridRayCrossingIndex, GridRayCrossingIndex]
    dsimp only
    rw [hlast, hhead]
    apply cyclic_sum_sub
    intro a b hab
    simpa [eastSign, eastU, eastV] using east_step_delta q a b (edge_adj a b hab)
  have north_delta : GridRayCrossingIndex (q + ⟨0, 1⟩) p -
      GridRayCrossingIndex q p =
      (edges.map (fun e => northSign e.1 e.2)).sum := by
    rw [GridRayCrossingIndex, GridRayCrossingIndex]
    dsimp only
    rw [hlast, hhead]
    let potential : GaussianInt → Int := fun a =>
      if a.im = q.im + 1 ∧ a.re ≤ q.re then 1 else 0
    let augmented : GaussianInt → GaussianInt → Int := fun a b =>
      northSign a b + potential a - potential b
    calc
      _ = (edges.map (fun e => augmented e.1 e.2)).sum := by
        apply cyclic_sum_sub
        intro a b hab
        simpa [augmented, northSign, northU, northV, potential] using
          north_step_delta q a b (edge_adj a b hab)
      _ = (edges.map (fun e => northSign e.1 e.2)).sum := by
        rw [show (edges.map (fun e => augmented e.1 e.2)).sum =
            (edges.map (fun e => northSign e.1 e.2)).sum +
              (edges.map (fun e => potential e.1 - potential e.2)).sum by
          simpa [augmented] using map_augmented_sum edges northSign potential]
        have hpotOpen := zip_potential_sum p x y hhead hlast potential
        rw [zipWith_eq_map_zip] at hpotOpen
        have hpot : (edges.map (fun e => potential e.1 - potential e.2)).sum = 0 := by
          simp only [edges, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton]
          rw [hpotOpen]
          omega
        rw [hpot, add_zero]
  have east_formula := signed_target_sum_formula edges hedges eastU eastV east_ne
  have north_formula := signed_target_sum_formula edges hedges northU northV north_ne
  have east_exclusive : ¬((eastU, eastV) ∈ edges ∧ (eastV, eastU) ∈ edges) := by
    rintro ⟨huv, hvu⟩
    simp only [edges, List.mem_append, List.mem_singleton] at huv hvu
    apply cyclic_edges_no_reverse hnodup hlen hhead hlast
    · rcases huv with huv | huv
      · exact Or.inl huv
      · exact Or.inr (Prod.mk.inj huv)
    · rcases hvu with hvu | hvu
      · exact Or.inl hvu
      · exact Or.inr (Prod.mk.inj hvu)
  have north_exclusive : ¬((northU, northV) ∈ edges ∧ (northV, northU) ∈ edges) := by
    rintro ⟨huv, hvu⟩
    simp only [edges, List.mem_append, List.mem_singleton] at huv hvu
    apply cyclic_edges_no_reverse hnodup hlen hhead hlast
    · rcases huv with huv | huv
      · exact Or.inl huv
      · exact Or.inr (Prod.mk.inj huv)
    · rcases hvu with hvu | hvu
      · exact Or.inl hvu
      · exact Or.inr (Prod.mk.inj hvu)
  constructor
  · rintro ⟨huv, hvu⟩
    have hz : GridRayCrossingIndex (q + 1) p - GridRayCrossingIndex q p = 0 := by
      rw [east_delta, east_formula]
      simp [edges, eastU, eastV, huv, hvu]
    omega
  constructor
  · intro hoccur
    rw [east_delta, east_formula]
    rcases hoccur with huv | hvu
    · have : (eastV, eastU) ∉ edges := fun h => east_exclusive ⟨huv, h⟩
      simp [edges, eastU, eastV, huv, this]
    · have : (eastU, eastV) ∉ edges := fun h => east_exclusive ⟨h, hvu⟩
      simp [edges, eastU, eastV, hvu, this]
  constructor
  · rintro ⟨huv, hvu⟩
    have hz : GridRayCrossingIndex (q + ⟨0, 1⟩) p -
        GridRayCrossingIndex q p = 0 := by
      rw [north_delta, north_formula]
      simp [edges, northU, northV, huv, hvu]
    omega
  · intro hoccur
    rw [north_delta, north_formula]
    rcases hoccur with huv | hvu
    · have : (northV, northU) ∉ edges := fun h => north_exclusive ⟨huv, h⟩
      simp [edges, northU, northV, huv, this]
    · have : (northU, northV) ∉ edges := fun h => north_exclusive ⟨h, hvu⟩
      simp [edges, northU, northV, hvu, this]

end ApollonianSuperharmonic

end
