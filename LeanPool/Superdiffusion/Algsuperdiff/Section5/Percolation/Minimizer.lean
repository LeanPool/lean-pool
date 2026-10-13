/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.Geodesic
public import Mathlib.Order.Minimal

/-!
# Minimizer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Lexicographic crossing-path minimizers

This file formulates the path selected by first minimizing the number of
inflated-good vertices and then its length.  The second minimization is the
mechanism that controls excursions through an occurring inflated cube.
-/

namespace Algsuperdiff.Section5.Percolation

open MeasureTheory

/-- Replace the part of `Γ` from positions `i` through `j` by the synchronous
geodesic joining the two indexed vertices. -/
def spliceGeodesic {d : ℕ} (Γ : List (Site d))
    (i j : Fin Γ.length) : List (Site d) :=
  Γ.take i.1 ++ geodesic (Γ.get i) (Γ.get j) ++ Γ.drop (j.1 + 1)

private theorem isPath_spliceGeodesic {d : ℕ} {Γ : List (Site d)}
    (hΓ : IsPath Γ) (i j : Fin Γ.length) :
    IsPath (spliceGeodesic Γ i j) := by
  have hleft : IsPath (Γ.take i.1) := hΓ.take i.1
  have hmiddle : IsPath (geodesic (Γ.get i) (Γ.get j)) :=
    isPath_geodesic _ _
  have hright : IsPath (Γ.drop (j.1 + 1)) := hΓ.drop (j.1 + 1)
  have hjoinLeft : ∀ x ∈ (Γ.take i.1).getLast?,
      ∀ y ∈ (geodesic (Γ.get i) (Γ.get j)).head?, Adj x y := by
    intro x hx y hy
    have hyEq : y = Γ.get i := by
      have hyRev : Γ.get i = y := by
        simpa only [head?_geodesic, Option.mem_some_iff] using hy
      exact hyRev.symm
    subst y
    by_cases hi : i.1 = 0
    · simp only [hi, List.take_zero, List.getLast?_nil, Option.not_mem_none] at hx
    · have hiPred : i.1 - 1 < Γ.length := by omega
      have hxEq : x = Γ[i.1 - 1] := by
        rw [List.getLast?_take, ite_eq_right hi,
          List.getElem?_eq_getElem hiPred] at hx
        have hxRev : Γ[i.1 - 1] = x := by
          simpa only [Option.some_or, Option.mem_some_iff] using hx
        exact hxRev.symm
      subst x
      have hadj := hΓ.getElem (i.1 - 1) (by omega)
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)] using! hadj
  have hleftMiddle : IsPath
      (Γ.take i.1 ++ geodesic (Γ.get i) (Γ.get j)) :=
    hleft.append hmiddle hjoinLeft
  apply hleftMiddle.append hright
  intro x hx y hy
  by_cases hj : j.1 + 1 = Γ.length
  · rw [List.head?_drop, List.getElem?_eq_none (by omega)] at hy
    simp only [Option.not_mem_none] at hy
  · have hjSucc : j.1 + 1 < Γ.length := by omega
    have hyEq : y = Γ[j.1 + 1] := by
      rw [List.head?_drop, List.getElem?_eq_getElem hjSucc] at hy
      have hyRev : Γ[j.1 + 1] = y := by
        simpa only [Option.mem_some_iff] using hy
      exact hyRev.symm
    subst y
    have hxEq : x = Γ.get j := by
      rw [List.getLast?_append] at hx
      have hxRev : Γ.get j = x := by
        simpa only [getLast?_geodesic, Option.some_or,
          Option.mem_some_iff] using hx
      exact hxRev.symm
    subst x
    exact hΓ.getElem j.1 hjSucc

private theorem head?_spliceGeodesic {d : ℕ} {Γ : List (Site d)}
    (i j : Fin Γ.length) :
    (spliceGeodesic Γ i j).head? = Γ.head? := by
  unfold spliceGeodesic
  rw [List.head?_append, List.head?_append, List.head?_take]
  by_cases hi : i.1 = 0
  · simp only [ite_eq_left hi, Option.none_or, head?_geodesic, Option.some_or]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    let i0 : Fin Γ.length := ⟨0, by omega⟩
    have hiFin : i = i0 := Fin.ext (by simp only [i0]; exact hi)
    apply congrArg some
    simpa only [i0, List.get_eq_getElem] using congrArg Γ.get hiFin
  · rw [ite_eq_right hi, List.head?_eq_getElem?,
      List.getElem?_eq_getElem (by omega), Option.some_or, Option.some_or]

private theorem getLast?_spliceGeodesic {d : ℕ} {Γ : List (Site d)}
    (i j : Fin Γ.length) :
    (spliceGeodesic Γ i j).getLast? = Γ.getLast? := by
  unfold spliceGeodesic
  rw [List.getLast?_append]
  by_cases hj : j.1 + 1 = Γ.length
  · rw [List.drop_eq_nil_iff.mpr (by omega), List.getLast?_nil,
      Option.none_or, List.getLast?_append, getLast?_geodesic,
      Option.some_or]
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    let jlast : Fin Γ.length := ⟨Γ.length - 1, by omega⟩
    have hjFin : j = jlast := Fin.ext (by simp only [jlast]; omega)
    apply congrArg some
    simpa only [jlast, List.get_eq_getElem] using congrArg Γ.get hjFin
  · have hjSucc : j.1 + 1 < Γ.length := by omega
    have hdrop : (Γ.drop (j.1 + 1)).getLast? = Γ.getLast? := by
      rw [List.getLast?_drop, ite_eq_right (by omega)]
    rw [hdrop]
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega), Option.some_or]

private theorem isPathFrom_spliceGeodesic {d k : ℕ}
    {Γ : List (Site d)} (hΓ : IsPathFrom k Γ)
    (i j : Fin Γ.length) : IsPathFrom k (spliceGeodesic Γ i j) := by
  cases Γ with
  | nil => exact Fin.elim0 i
  | cons x xs =>
      obtain ⟨hpath, hx, hy⟩ := hΓ
      have hpathSplice := isPath_spliceGeodesic hpath i j
      have hhead := head?_spliceGeodesic i j
      have hlast := getLast?_spliceGeodesic i j
      cases hΔ : spliceGeodesic (x :: xs) i j with
      | nil =>
          rw [hΔ, List.head?_nil] at hhead
          exact False.elim (by cases hhead)
      | cons z zs =>
          have hz : z = x := by
            rw [hΔ, List.head?_cons, List.head?_cons,
              Option.some.injEq] at hhead
            exact hhead
          subst z
          refine ⟨by simpa only [hΔ] using hpathSplice, hx, ?_⟩
          intro hout
          apply hy
          have hlastValue :
              (x :: zs).getLast (List.cons_ne_nil x zs) =
                (x :: xs).getLast (List.cons_ne_nil x xs) := by
            have hlast' : (x :: zs).getLast? = (x :: xs).getLast? := by
              simpa only [hΔ] using hlast
            have hlastSome :
                some ((x :: zs).getLast (List.cons_ne_nil x zs)) =
                  some ((x :: xs).getLast (List.cons_ne_nil x xs)) := by
              simpa only [List.getLast?_eq_some_getLast] using! hlast'
            exact Option.some.inj hlastSome
          rwa [← hlastValue]

private theorem mem_inflatedBadSet_of_mem_latticeCubeSites
    {Ω : Type*} {d L : ℕ} {B : ℕ → Site d → Set Ω}
    {v z : Site d} {ω : Ω} (hω : ω ∈ inflatedBadEvent B L v)
    (hz : z ∈ latticeCubeSites L v) : ω ∈ inflatedBadSet B z := by
  simp only [inflatedBadSet, Set.mem_iUnion]
  refine ⟨L, ?_⟩
  rw [centerIndex_eq_of_mem_latticeCubeSites hz]
  exact hω

def pathWalk {d : ℕ} (x : Site d) :
    (xs : List (Site d)) → IsPath (x :: xs) →
      (latticeGraph d).Walk x ((x :: xs).getLast (List.cons_ne_nil x xs))
  | [], _h => SimpleGraph.Walk.nil
  | y :: ys, h => SimpleGraph.Walk.cons h.rel (pathWalk y ys h.tail)

private theorem support_pathWalk {d : ℕ} (x : Site d) :
    ∀ (xs : List (Site d)) (h : IsPath (x :: xs)),
      (pathWalk x xs h).support = x :: xs
  | [], _h => rfl
  | y :: ys, h => by
      simp only [pathWalk]
      exact congrArg (List.cons x) (support_pathWalk y ys h.tail)

/-- Every crossing walk has a crossing subpath with no repeated vertices and
no new vertices. -/
theorem exists_nodup_crossing_subpath {d k : ℕ} {Γ : List (Site d)}
    (hΓ : IsPathFrom k Γ) :
    ∃ Δ : List (Site d), IsPathFrom k Δ ∧ Δ.Nodup ∧ Δ ⊆ Γ := by
  cases Γ with
  | nil => exact False.elim hΓ
  | cons x xs =>
      obtain ⟨hpath, hx, hy⟩ := hΓ
      let y := (x :: xs).getLast (List.cons_ne_nil x xs)
      let p : (latticeGraph d).Walk x y := pathWalk x xs hpath
      let q : (latticeGraph d).Path x y := p.toPath
      let Δ : List (Site d) := (q : (latticeGraph d).Walk x y).support
      have hΔcons : Δ = x :: Δ.tail := by
        show (q : (latticeGraph d).Walk x y).support = x :: _
        rw [SimpleGraph.Walk.cons_tail_support]
      have hΔpath : IsPath Δ :=
        SimpleGraph.Walk.isChain_adj_support (q : (latticeGraph d).Walk x y)
      have hΔlast : Δ.getLast (SimpleGraph.Walk.support_ne_nil
          (q : (latticeGraph d).Walk x y)) = y :=
        SimpleGraph.Walk.getLast_support (q : (latticeGraph d).Walk x y)
      have hΔcross : IsPathFrom k Δ := by
        rw [hΔcons]
        refine ⟨?_, hx, ?_⟩
        · simpa only [← hΔcons] using hΔpath
        · have hlast : (x :: Δ.tail).getLast (List.cons_ne_nil x Δ.tail) = y := by
            simpa only [← hΔcons] using hΔlast
          rw [hlast]
          exact hy
      have hΔnodup : Δ.Nodup := SimpleGraph.Path.nodup_support q
      have hsubsetP : Δ ⊆ p.support :=
        SimpleGraph.Walk.support_toPath_subset_support p
      have hpSupport : p.support = x :: xs := support_pathWalk x xs hpath
      exact ⟨Δ, hΔcross, hΔnodup, by simpa only [hpSupport] using hsubsetP⟩

open Classical in
/-- The number of distinct vertices of `Γ` outside the inflated bad set. -/
noncomputable def inflatedGoodVertexCountNat {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) (ω : Ω) : ℕ :=
  (Γ.toFinset.filter fun z => ω ∉ inflatedBadSet B z).card

private theorem inflatedGoodVertexCountNat_mono {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (ω : Ω) {Δ Γ : List (Site d)}
    (hsub : Δ ⊆ Γ) :
    inflatedGoodVertexCountNat B Δ ω ≤ inflatedGoodVertexCountNat B Γ ω := by
  classical
  unfold inflatedGoodVertexCountNat
  apply Finset.card_le_card
  intro z hz
  have hzΔ : z ∈ Δ := List.mem_toFinset.mp (Finset.mem_of_mem_filter z hz)
  exact Finset.mem_filter.mpr
    ⟨List.mem_toFinset.mpr (hsub hzΔ), (Finset.mem_filter.mp hz).2⟩

private theorem inflatedGoodVertexCountNat_spliceGeodesic_le
    {Ω : Type*} {d L : ℕ} {B : ℕ → Site d → Set Ω}
    {v : Site d} {ω : Ω} {Γ : List (Site d)}
    (i j : Fin Γ.length) (hi : Γ.get i ∈ latticeCubeSites L v)
    (hj : Γ.get j ∈ latticeCubeSites L v)
    (hω : ω ∈ inflatedBadEvent B L v) :
    inflatedGoodVertexCountNat B (spliceGeodesic Γ i j) ω ≤
      inflatedGoodVertexCountNat B Γ ω := by
  classical
  unfold inflatedGoodVertexCountNat
  apply Finset.card_le_card
  intro z hz
  have hzSplice : z ∈ spliceGeodesic Γ i j :=
    List.mem_toFinset.mp (Finset.mem_of_mem_filter z hz)
  have hzGood : ω ∉ inflatedBadSet B z := (Finset.mem_filter.mp hz).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, hzGood⟩
  apply List.mem_toFinset.mpr
  unfold spliceGeodesic at hzSplice
  obtain hzLeftMiddle | hzRight := List.mem_append.mp hzSplice
  · obtain hzLeft | hzMiddle := List.mem_append.mp hzLeftMiddle
    · exact (List.take_prefix i.1 Γ).subset hzLeft
    · exact False.elim (hzGood
        (mem_inflatedBadSet_of_mem_latticeCubeSites hω
          (mem_latticeCubeSites_of_mem_geodesic hi hj hzMiddle)))
  · exact (List.drop_suffix (j.1 + 1) Γ).subset hzRight

/-- A crossing path preferred lexicographically by inflated-good count and
then by length. -/
def IsPreferredPath {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (k : ℕ) (ω : Ω)
    (Γ : List (Site d)) : Prop :=
  IsPathFrom k Γ ∧
    ∀ Δ : List (Site d), IsPathFrom k Δ →
      inflatedGoodVertexCountNat B Γ ω ≤ inflatedGoodVertexCountNat B Δ ω ∧
      (inflatedGoodVertexCountNat B Δ ω = inflatedGoodVertexCountNat B Γ ω →
        Γ.length ≤ Δ.length)

/-- Whenever a crossing path exists, a lexicographically preferred crossing
path exists. -/
theorem exists_preferredPath {Ω : Type*} {d k : ℕ}
    (B : ℕ → Site d → Set Ω) (ω : Ω)
    (hex : ∃ Γ : List (Site d), IsPathFrom k Γ) :
    ∃ Γ : List (Site d), IsPreferredPath B k ω Γ := by
  classical
  obtain ⟨Γ₀, hΓ₀⟩ :=
    exists_minimalFor_of_wellFoundedLT
      (fun Γ : List (Site d) => IsPathFrom k Γ)
      (fun Γ => inflatedGoodVertexCountNat B Γ ω) hex
  have hcostMin : ∀ Δ : List (Site d), IsPathFrom k Δ →
      inflatedGoodVertexCountNat B Γ₀ ω ≤ inflatedGoodVertexCountNat B Δ ω := by
    intro Δ hΔ
    by_cases hle : inflatedGoodVertexCountNat B Δ ω ≤
        inflatedGoodVertexCountNat B Γ₀ ω
    · exact hΓ₀.2 hΔ hle
    · exact Nat.le_of_lt (lt_of_not_ge hle)
  let sameCost : List (Site d) → Prop := fun Γ =>
    IsPathFrom k Γ ∧
      inflatedGoodVertexCountNat B Γ ω = inflatedGoodVertexCountNat B Γ₀ ω
  have hsame : ∃ Γ, sameCost Γ := ⟨Γ₀, hΓ₀.1, rfl⟩
  obtain ⟨Γ, hΓ⟩ :=
    exists_minimalFor_of_wellFoundedLT sameCost List.length hsame
  refine ⟨Γ, hΓ.1.1, ?_⟩
  intro Δ hΔ
  refine ⟨?_, ?_⟩
  · rw [hΓ.1.2]
    exact hcostMin Δ hΔ
  · intro hcost
    have hΔsame : sameCost Δ := by
      refine ⟨hΔ, ?_⟩
      rw [← hΓ.1.2]
      exact hcost
    by_cases hlen : Δ.length ≤ Γ.length
    · exact hΓ.2 hΔsame hlen
    · exact Nat.le_of_lt (lt_of_not_ge hlen)

/-- A preferred path has no greater inflated-good cost than any crossing
path. -/
theorem IsPreferredPath.cost_le {Ω : Type*} {d k : ℕ}
    {B : ℕ → Site d → Set Ω} {ω : Ω} {Γ Δ : List (Site d)}
    (hΓ : IsPreferredPath B k ω Γ) (hΔ : IsPathFrom k Δ) :
    inflatedGoodVertexCountNat B Γ ω ≤ inflatedGoodVertexCountNat B Δ ω :=
  (hΓ.2 Δ hΔ).1

/-- Among crossing paths with the same inflated-good cost, a preferred path
has minimal length. -/
theorem IsPreferredPath.length_le {Ω : Type*} {d k : ℕ}
    {B : ℕ → Site d → Set Ω} {ω : Ω} {Γ Δ : List (Site d)}
    (hΓ : IsPreferredPath B k ω Γ) (hΔ : IsPathFrom k Δ)
    (hcost : inflatedGoodVertexCountNat B Δ ω =
      inflatedGoodVertexCountNat B Γ ω) :
    Γ.length ≤ Δ.length :=
  (hΓ.2 Δ hΔ).2 hcost

/-- A lexicographically preferred crossing path has no repeated vertices. -/
theorem IsPreferredPath.nodup {Ω : Type*} {d k : ℕ}
    {B : ℕ → Site d → Set Ω} {ω : Ω} {Γ : List (Site d)}
    (hΓ : IsPreferredPath B k ω Γ) : Γ.Nodup := by
  classical
  obtain ⟨Δ, hΔcross, hΔnodup, hsub⟩ :=
    exists_nodup_crossing_subpath hΓ.1
  have hcostΓΔ := hΓ.cost_le hΔcross
  have hcostΔΓ := inflatedGoodVertexCountNat_mono B ω hsub
  have hcost : inflatedGoodVertexCountNat B Δ ω =
      inflatedGoodVertexCountNat B Γ ω := Nat.le_antisymm hcostΔΓ hcostΓΔ
  have hlenΓΔ := hΓ.length_le hΔcross hcost
  by_contra hnot
  have hcardStrict : Γ.toFinset.card < Γ.length := by
    have hcardLe : Γ.toFinset.card ≤ Γ.length := List.toFinset_card_le Γ
    apply lt_of_le_of_ne hcardLe
    intro hcardEq
    apply hnot
    have hiff : Γ.toFinset.card = Γ.length ↔ Γ.Nodup := by
      change ((↑Γ : Multiset (Site d)).toFinset).card =
        (↑Γ : Multiset (Site d)).card ↔ (↑Γ : Multiset (Site d)).Nodup
      exact Multiset.toFinset_card_eq_card_iff_nodup
    exact hiff.mp hcardEq
  have hfinSub : Δ.toFinset ⊆ Γ.toFinset := by
    intro z hz
    exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hz))
  have hΔcard : Δ.length = Δ.toFinset.card :=
    (List.toFinset_card_of_nodup hΔnodup).symm
  have hlenStrict : Δ.length < Γ.length := by
    rw [hΔcard]
    exact (Finset.card_le_card hfinSub).trans_lt hcardStrict
  exact (Nat.not_lt_of_ge hlenΓΔ) hlenStrict

private theorem length_spliceGeodesic {d : ℕ} {Γ : List (Site d)}
    (i j : Fin Γ.length) :
    (spliceGeodesic Γ i j).length =
      i.1 + (siteDist (Γ.get i) (Γ.get j) + 1) +
        (Γ.length - (j.1 + 1)) := by
  simp only [spliceGeodesic, List.length_append, List.length_take,
    List.length_drop, length_geodesic, Nat.min_eq_left (Nat.le_of_lt i.2)]

private theorem IsPreferredPath.index_gap_le_siteDist
    {Ω : Type*} {d k L : ℕ} {B : ℕ → Site d → Set Ω}
    {v : Site d} {ω : Ω} {Γ : List (Site d)}
    (hΓ : IsPreferredPath B k ω Γ) (i j : Fin Γ.length)
    (hij : i.1 ≤ j.1) (hi : Γ.get i ∈ latticeCubeSites L v)
    (hj : Γ.get j ∈ latticeCubeSites L v)
    (hω : ω ∈ inflatedBadEvent B L v) :
    j.1 - i.1 ≤ siteDist (Γ.get i) (Γ.get j) := by
  let Δ := spliceGeodesic Γ i j
  have hΔ : IsPathFrom k Δ := isPathFrom_spliceGeodesic hΓ.1 i j
  have hcostΓΔ := hΓ.cost_le hΔ
  have hcostΔΓ :=
    inflatedGoodVertexCountNat_spliceGeodesic_le i j hi hj hω
  have hcost : inflatedGoodVertexCountNat B Δ ω =
      inflatedGoodVertexCountNat B Γ ω :=
    Nat.le_antisymm hcostΔΓ hcostΓΔ
  have hlength := hΓ.length_le hΔ hcost
  rw [show Δ = spliceGeodesic Γ i j by rfl,
    length_spliceGeodesic i j] at hlength
  omega

open Classical in
/-- The distinct vertices of a path which belong to one centered triadic
cube. -/
noncomputable def pathVerticesInCube {d : ℕ} (L : ℕ)
    (Γ : List (Site d)) (v : Site d) : Finset (Site d) :=
  Γ.toFinset.filter fun z => z ∈ latticeCubeSites L v

open Classical in
noncomputable def cubeVisitIndices {d : ℕ} (L : ℕ)
    (Γ : List (Site d)) (v : Site d) : Finset (Fin Γ.length) :=
  Finset.univ.filter fun i => Γ.get i ∈ latticeCubeSites L v

private theorem image_cubeVisitIndices_eq_pathVerticesInCube {d L : ℕ}
    (Γ : List (Site d)) (v : Site d) :
    (cubeVisitIndices L Γ v).image Γ.get = pathVerticesInCube L Γ v := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hz
    have hiCube : Γ.get i ∈ latticeCubeSites L v :=
      (Finset.mem_filter.mp hi).2
    rw [← hiz]
    exact Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (List.get_mem Γ i), hiCube⟩
  · intro hz
    obtain ⟨hzΓ, hzCube⟩ := Finset.mem_filter.mp hz
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hzΓ)
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hi⟩
    rwa [hi]

/-- A preferred path visits at most `3^L + 1` distinct sites of any occurring
inflated bad cube. -/
theorem IsPreferredPath.card_pathVerticesInCube_le
    {Ω : Type*} {d k L : ℕ} {B : ℕ → Site d → Set Ω}
    {v : Site d} {ω : Ω} {Γ : List (Site d)}
    (hΓ : IsPreferredPath B k ω Γ)
    (hω : ω ∈ inflatedBadEvent B L v) :
    (pathVerticesInCube L Γ v).card ≤ 3 ^ L + 1 := by
  classical
  let s := cubeVisitIndices L Γ v
  have himage : s.image Γ.get = pathVerticesInCube L Γ v :=
    image_cubeVisitIndices_eq_pathVerticesInCube Γ v
  have hcard : (pathVerticesInCube L Γ v).card = s.card := by
    rw [← himage]
    exact Finset.card_image_of_injective s hΓ.nodup.injective_get
  rw [hcard]
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    let j := s.max' hs
    have hiMem : i ∈ s := Finset.min'_mem s hs
    have hjMem : j ∈ s := Finset.max'_mem s hs
    have hiCube : Γ.get i ∈ latticeCubeSites L v :=
      (Finset.mem_filter.mp hiMem).2
    have hjCube : Γ.get j ∈ latticeCubeSites L v :=
      (Finset.mem_filter.mp hjMem).2
    have hij : i.1 ≤ j.1 := by
      exact Finset.min'_le_max' s hs
    have hgapDist := hΓ.index_gap_le_siteDist i j hij hiCube hjCube hω
    have hdist := siteDist_le_three_pow_of_mem_latticeCubeSites hiCube hjCube
    have hbounds : ∀ t ∈ s, i.1 ≤ t.1 ∧ t.1 ≤ j.1 := by
      intro t ht
      exact ⟨Finset.min'_le s t ht, Finset.le_max' s t ht⟩
    let f : {t // t ∈ s} → Fin (j.1 - i.1 + 1) := fun t =>
      ⟨t.1.1 - i.1, by
        have htBounds := hbounds t.1 t.2
        omega⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Fin.ext
      have haBounds := hbounds a.1 a.2
      have hbBounds := hbounds b.1 b.2
      have habVal := congrArg Fin.val hab
      change a.1.1 - i.1 = b.1.1 - i.1 at habVal
      omega
    have hcardGap : s.card ≤ j.1 - i.1 + 1 := by
      rw [← Fintype.card_coe]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    omega
  · have hsCard : s.card = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hs (Finset.card_pos.mp hpos)
    rw [hsCard]
    exact Nat.zero_le _

open Classical in
/-- The vertices of `Γ` at which the all-scale inflated bad event occurs. -/
noncomputable def inflatedBadVertices {Ω : Type*} {d : ℕ}
    (B : ℕ → Site d → Set Ω) (Γ : List (Site d)) (ω : Ω) : Finset (Site d) :=
  Γ.toFinset.filter fun z => ω ∈ inflatedBadSet B z

/-- The real inflated-vertex count is the cardinality of the corresponding
finite vertex set. -/
theorem inflatedVertexCount_eq_card_inflatedBadVertices
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    (Γ : List (Site d)) (ω : Ω) :
    inflatedVertexCount B Γ ω = (inflatedBadVertices B Γ ω).card := by
  classical
  rw [inflatedVertexCount, inflatedBadVertices]
  induction Γ.toFinset using Finset.induction_on with
  | empty => simp
  | @insert z s hz ih =>
      by_cases hbad : ω ∈ inflatedBadSet B z
      · have hzfilter : z ∉ s.filter fun y => ω ∈ inflatedBadSet B y := by
          intro hzs
          exact hz (Finset.mem_of_mem_filter z hzs)
        rw [Finset.filter_insert, ite_eq_left hbad, Finset.sum_insert hz,
          Set.indicator_of_mem hbad, ih, Finset.card_insert_of_notMem hzfilter]
        push_cast
        ring
      · rw [Finset.filter_insert, ite_eq_right hbad, Finset.sum_insert hz,
          Set.indicator_of_notMem hbad, ih, zero_add]

/-- The inflated-good and inflated-bad vertex counts partition the distinct
vertices of a path. -/
theorem inflatedGoodVertexCountNat_add_inflatedVertexCount_eq_card
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    (Γ : List (Site d)) (ω : Ω) :
    (inflatedGoodVertexCountNat B Γ ω : ℝ) + inflatedVertexCount B Γ ω =
      Γ.toFinset.card := by
  classical
  rw [inflatedGoodVertexCountNat,
    inflatedVertexCount_eq_card_inflatedBadVertices, inflatedBadVertices]
  norm_cast
  simpa only [not_not, add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := Γ.toFinset) (p := fun z => ω ∈ inflatedBadSet B z))

/-- The inflated-good count is no larger than the original good-vertex
count. -/
theorem coe_inflatedGoodVertexCountNat_le_goodVertexCount
    {Ω : Type*} {d : ℕ} (B : ℕ → Site d → Set Ω)
    (Γ : List (Site d)) (ω : Ω) :
    (inflatedGoodVertexCountNat B Γ ω : ℝ) ≤ goodVertexCount B Γ ω := by
  classical
  let s := Γ.toFinset.filter fun z => ω ∉ inflatedBadSet B z
  have hterm : ∀ z ∈ s,
      (badSet B z)ᶜ.indicator (fun _ => (1 : ℝ)) ω = 1 := by
    intro z hz
    have hnotInflated := (Finset.mem_filter.mp hz).2
    have hnotBad : ω ∉ badSet B z := by
      intro hbad
      exact hnotInflated (badSet_subset_inflatedBadSet B z hbad)
    have hgood : ω ∈ (badSet B z)ᶜ := hnotBad
    simp only [Set.indicator_of_mem hgood]
  rw [inflatedGoodVertexCountNat, goodVertexCount]
  change (s.card : ℝ) ≤ _
  calc
    (s.card : ℝ) = ∑ z ∈ s, (1 : ℝ) := by simp
    _ = ∑ z ∈ s, (badSet B z)ᶜ.indicator (fun _ => (1 : ℝ)) ω := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hterm z hz]
    _ ≤ ∑ z ∈ Γ.toFinset,
        (badSet B z)ᶜ.indicator (fun _ => (1 : ℝ)) ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro z _hz _hnot
      by_cases hgood : ω ∈ (badSet B z)ᶜ
      · rw [Set.indicator_of_mem hgood]
        norm_num
      · rw [Set.indicator_of_notMem hgood]

private theorem IsPreferredPath.exists_scales_inflatedVertexCount_le
    {Ω : Type*} {d k : ℕ} {B : ℕ → Site d → Set Ω}
    {ω : Ω} {Γ : List (Site d)} (hΓ : IsPreferredPath B k ω Γ) :
    ∃ scales : Finset ℕ,
      inflatedVertexCount B Γ ω ≤ 2 * weightedCubeMassOn B Γ scales ω := by
  classical
  let s := inflatedBadVertices B Γ ω
  let badScale : {z // z ∈ s} → ℕ := fun z =>
    Classical.choose (Set.mem_iUnion.mp (Finset.mem_filter.mp z.2).2)
  have hbadScale : ∀ z : {z // z ∈ s},
      ω ∈ inflatedBadEvent B (badScale z) (centerIndex (badScale z) z.1) := by
    intro z
    exact Classical.choose_spec (Set.mem_iUnion.mp (Finset.mem_filter.mp z.2).2)
  let pair : {z // z ∈ s} → ℕ × Site d := fun z =>
    (badScale z, centerIndex (badScale z) z.1)
  let pairs : Finset (ℕ × Site d) := Finset.univ.image pair
  let scales : Finset ℕ := pairs.image Prod.fst
  have hpairs_occurs : ∀ p ∈ pairs,
      ω ∈ inflatedBadEvent B p.1 p.2 := by
    intro p hp
    obtain ⟨z, _hz, hpz⟩ := Finset.mem_image.mp hp
    rw [← hpz]
    exact hbadScale z
  have hpairs_touched : ∀ p ∈ pairs, p.2 ∈ touchingCenters p.1 Γ := by
    intro p hp
    obtain ⟨z, _hz, hpz⟩ := Finset.mem_image.mp hp
    rw [← hpz]
    exact centerIndex_mem_touchingCenters
      (List.mem_toFinset.mp (Finset.mem_of_mem_filter z.1 z.2))
  have hfiber_le : ∀ p ∈ pairs,
      (Finset.univ.filter fun z : {z // z ∈ s} => pair z = p).card ≤
        3 ^ p.1 + 1 := by
    intro p hp
    have hsub : (Finset.univ.filter fun z : {z // z ∈ s} => pair z = p).image
        (fun z => z.1) ⊆ pathVerticesInCube p.1 Γ p.2 := by
      intro z hz
      obtain ⟨z', hz', hzz'⟩ := Finset.mem_image.mp hz
      have hpair := (Finset.mem_filter.mp hz').2
      rw [← hzz']
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_of_mem_filter z'.1 z'.2, ?_⟩
      have hscale := congrArg Prod.fst hpair
      have hcenter := congrArg Prod.snd hpair
      apply mem_latticeCubeSites_iff_centerIndex_eq.mpr
      rw [← hscale]
      simpa only [pair] using hcenter
    have hinj : Function.Injective (fun z : {z // z ∈ s} => z.1) :=
      Subtype.val_injective
    calc
      (Finset.univ.filter fun z : {z // z ∈ s} => pair z = p).card =
          ((Finset.univ.filter fun z : {z // z ∈ s} => pair z = p).image
            (fun z => z.1)).card :=
        (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (pathVerticesInCube p.1 Γ p.2).card := Finset.card_le_card hsub
      _ ≤ 3 ^ p.1 + 1 := hΓ.card_pathVerticesInCube_le (hpairs_occurs p hp)
  have hcard_s : s.card ≤ ∑ p ∈ pairs, (3 ^ p.1 + 1) := by
    calc
      s.card = (Finset.univ : Finset {z // z ∈ s}).card := by simp
      _ = ∑ p ∈ pairs,
          (Finset.univ.filter fun z : {z // z ∈ s} => pair z = p).card := by
        exact Finset.card_eq_sum_card_image pair Finset.univ
      _ ≤ ∑ p ∈ pairs, (3 ^ p.1 + 1) := Finset.sum_le_sum hfiber_le
  have hcard_double : s.card ≤ 2 * ∑ p ∈ pairs, 3 ^ p.1 := by
    apply hcard_s.trans
    calc
      ∑ p ∈ pairs, (3 ^ p.1 + 1) ≤ ∑ p ∈ pairs, 2 * 3 ^ p.1 := by
        apply Finset.sum_le_sum
        intro p _hp
        have hpow : 1 ≤ 3 ^ p.1 := one_le_pow₀ (by norm_num)
        omega
      _ = 2 * ∑ p ∈ pairs, 3 ^ p.1 := by rw [Finset.mul_sum]
  have hpair_sum_le : (∑ p ∈ pairs, (3 : ℝ) ^ p.1) ≤
      weightedCubeMassOn B Γ scales ω := by
    have hfiber : ∀ L ∈ scales,
        ((pairs.filter fun p => p.1 = L).card : ℝ) ≤
          inflatedCubeCount B L Γ ω := by
      intro L hL
      let occurring := (touchingCenters L Γ).filter fun v =>
        ω ∈ inflatedBadEvent B L v
      have hfmem : ∀ p ∈ pairs.filter (fun p => p.1 = L), p.2 ∈ occurring := by
        intro p hpFilter
        have hp : p ∈ pairs := Finset.mem_of_mem_filter p hpFilter
        have hpL : p.1 = L := (Finset.mem_filter.mp hpFilter).2
        apply Finset.mem_filter.mpr
        constructor
        · simpa only [hpL] using hpairs_touched p hp
        · simpa only [hpL] using hpairs_occurs p hp
      have hfinj : Set.InjOn Prod.snd
          (↑(pairs.filter fun p => p.1 = L) : Set (ℕ × Site d)) := by
        intro p hp q hq hpq
        change p ∈ pairs.filter (fun p => p.1 = L) at hp
        change q ∈ pairs.filter (fun p => p.1 = L) at hq
        apply Prod.ext
        · exact (Finset.mem_filter.mp hp).2.trans
            (Finset.mem_filter.mp hq).2.symm
        · exact hpq
      have hcard : (pairs.filter fun p => p.1 = L).card ≤ occurring.card := by
        calc
          (pairs.filter fun p => p.1 = L).card =
              ((pairs.filter fun p => p.1 = L).image Prod.snd).card :=
            (Finset.card_image_of_injOn hfinj).symm
          _ ≤ occurring.card := Finset.card_le_card (by
            intro v hv
            obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp hv
            rw [← hpv]
            exact hfmem p hp)
      exact_mod_cast hcard
    rw [weightedCubeMassOn]
    have hregroup : ∑ p ∈ pairs, (3 : ℝ) ^ p.1 =
        ∑ L ∈ scales, ∑ p ∈ pairs.filter (fun p => p.1 = L),
          (3 : ℝ) ^ p.1 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun p hp => Finset.mem_image_of_mem Prod.fst hp)
        (fun p => (3 : ℝ) ^ p.1)
    rw [hregroup]
    apply Finset.sum_le_sum
    intro L hL
    calc
      ∑ p ∈ pairs.filter (fun p => p.1 = L), (3 : ℝ) ^ p.1 =
          (3 : ℝ) ^ L * (pairs.filter fun p => p.1 = L).card := by
        calc
          ∑ p ∈ pairs.filter (fun p => p.1 = L), (3 : ℝ) ^ p.1 =
              ∑ _p ∈ pairs.filter (fun p => p.1 = L), (3 : ℝ) ^ L := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
          _ = (3 : ℝ) ^ L * (pairs.filter fun p => p.1 = L).card := by
            rw [Finset.sum_const]
            simp only [nsmul_eq_mul]
            ring
      _ ≤ (3 : ℝ) ^ L * inflatedCubeCount B L Γ ω :=
        mul_le_mul_of_nonneg_left (hfiber L hL) (by positivity)
  refine ⟨scales, ?_⟩
  rw [inflatedVertexCount_eq_card_inflatedBadVertices]
  have hcardDoubleR : (s.card : ℝ) ≤
      2 * ∑ p ∈ pairs, (3 : ℝ) ^ p.1 := by
    exact_mod_cast hcard_double
  change ((s.card : ℕ) : ℝ) ≤ 2 * weightedCubeMassOn B Γ scales ω
  exact hcardDoubleR.trans
    (mul_le_mul_of_nonneg_left hpair_sum_le (by norm_num))

/-- A preferred path inherits the weighted inflated-cube threshold from any
light crossing path at the same outcome. -/
theorem IsPreferredPath.mem_weightedCubeEvent_of_competitor_goodVertexCount_lt
    {Ω : Type*} {d k m : ℕ} {B : ℕ → Site d → Set Ω}
    {lam : ℝ} {ω : Ω} {Γ Δ : List (Site d)}
    (hΓ : IsPreferredPath B k ω Γ) (hΔ : IsPathFrom k Δ)
    (hlen : Γ.length = 3 ^ k + m)
    (hgood : goodVertexCount B Δ ω < (1 - lam) * 3 ^ k) :
    ω ∈ weightedCubeEvent B Γ ((lam * 3 ^ k + m) / 2) := by
  have hcostNat := hΓ.cost_le hΔ
  have hcostCast : (inflatedGoodVertexCountNat B Γ ω : ℝ) ≤
      inflatedGoodVertexCountNat B Δ ω := by
    exact_mod_cast hcostNat
  have hcost : (inflatedGoodVertexCountNat B Γ ω : ℝ) <
      (1 - lam) * 3 ^ k := hcostCast.trans_lt
    ((coe_inflatedGoodVertexCountNat_le_goodVertexCount B Δ ω).trans_lt hgood)
  have hpartition :=
    inflatedGoodVertexCountNat_add_inflatedVertexCount_eq_card B Γ ω
  rw [List.toFinset_card_of_nodup hΓ.nodup, hlen] at hpartition
  have hbad : lam * 3 ^ k + m < inflatedVertexCount B Γ ω := by
    norm_num at hpartition ⊢
    linarith only [hcost, hpartition]
  obtain ⟨scales, hmass⟩ := hΓ.exists_scales_inflatedVertexCount_le
  refine ⟨scales, ?_⟩
  linarith only [hbad, hmass]

end Algsuperdiff.Section5.Percolation
