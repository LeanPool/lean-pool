/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Data.List.Infix

public import LeanPool.ApollonianSuperharmonic.AffineTriangularStrip

-- [TABLET NODE: TriangularStripSegmentOrderInterval]

/-!
# TriangularStripSegmentOrderInterval

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace StripOrderIntervalProof

private theorem walk :
    ∀ (p : List Int),
      ∀ (a : Int),
        ∀ (b : Int),
          p.head? = some a →
            p.getLast? = some b →
              p.Nodup →
                (p.IsChain fun u v : Int => v = u + 1 ∨ u = v + 1) →
                  ∀ z : Int, z ∈ p ↔ min a b ≤ z ∧ z ≤ max a b := by
  classical
  intro p
  induction p using List.reverseRecOn with
  | nil =>
      intro a b ha hb hn hc
      simp at ha
  | append_singleton l c ih =>
      intro a b ha hb hn hc
      cases l with
      | nil =>
          have hac : a = c := by simpa using ha.symm
          have hbc : b = c := by simpa using hb.symm
          subst a
          subst b
          intro z
          constructor
          · intro hz
            have hzc : z = c := by simpa using hz
            subst z
            omega
          · intro hz
            have : z = c := by omega
            simp [this]
      | cons d t =>
          have hhead : (d :: t).head? = some a := by simpa using ha
          have hnodup : (d :: t).Nodup := (List.nodup_append.mp hn).1
          have hchain : (d :: t).IsChain (fun u v : Int => v = u + 1 ∨ u = v + 1) :=
            List.IsChain.left_of_append hc
          have hlast : ∃ u, (d :: t).getLast? = some u := by
            induction t using List.reverseRecOn with
            | nil => simp
            | append_singleton l e =>
                exact ⟨e, by simpa [List.cons_append] using
                  (List.getLast?_concat (l := d :: l) (a := e))⟩
          obtain ⟨u, hu⟩ := hlast
          have hi := ih a u hhead hu hnodup hchain
          have hb' : b = c := by
            have hcget : (d :: t ++ [c]).getLast? = some c := by
              simpa [List.cons_append] using
                (List.getLast?_concat (l := d :: t) (a := c))
            exact Option.some.inj (hb.symm.trans hcget)
          have hs := hc.rel_getLast_dropLast (by
            intro hh
            cases t <;> simp at hh)
          have hstep : c = u + 1 ∨ u = c + 1 := by
            have hfull : (d :: t ++ [c]).getLast (by simp) = c := by
              have hcget : (d :: t ++ [c]).getLast? = some c := by
                simpa [List.cons_append] using
                  (List.getLast?_concat (l := d :: t) (a := c))
              exact Option.some.inj ((List.getLast?_eq_some_getLast _).symm.trans hcget)
            have hne : (d :: t ++ [c]).dropLast ≠ [] := by
              apply List.ne_nil_of_mem (a := d)
              rw [List.dropLast_concat]
              simp
            have hdrop : (d :: t ++ [c]).dropLast.getLast hne = u := by
              have hdrop_eq : (d :: t ++ [c]).dropLast = d :: t := by
                rw [List.dropLast_concat]
              have hdropget : (d :: t ++ [c]).dropLast.getLast? = some u := by
                rw [hdrop_eq]
                exact hu
              exact Option.some.inj ((List.getLast?_eq_some_getLast _).symm.trans hdropget)
            rw [hfull, hdrop] at hs
            exact hs
          have hnew : c ∉ d :: t := by
            intro hcm
            have hh := (List.nodup_append.mp hn).2.2 c hcm c (by simp)
            exact hh rfl
          intro z
          constructor
          · intro hz
            have hz' : z ∈ d :: t ∨ z = c := by
              simpa only [List.mem_append, List.mem_singleton, or_assoc] using hz
            rcases hz' with hz | hzcval
            · have hzold := (hi z).mp hz
              rw [hb']
              have hout : ¬ (min a u ≤ c ∧ c ≤ max a u) := by
                intro hh
                exact hnew ((hi c).mpr hh)
              rcases hstep with hstep | hstep <;> omega
            · subst z
              rw [hb']
              have hout : ¬ (min a u ≤ c ∧ c ≤ max a u) := by
                intro hh
                exact hnew ((hi c).mpr hh)
              rcases hstep with hstep | hstep <;> omega
          · intro hz
            rcases hz with ⟨hz1, hz2⟩
            by_cases hzc : z = c
            · simp [hzc]
            · have hzold : min a u ≤ z ∧ z ≤ max a u := by
                have hout : ¬ (z < min a u ∨ max a u < z) := by
                  intro hh
                  rcases hh with hh | hh <;> omega
                omega
              have : z ∈ d :: t := (hi z).mpr hzold
              simpa [hzc] using this

private theorem hindices_nodup :
    ∀ (x : Int × Int), ∀ (y : Int × Int), ∀ (path : List (Int × Int)), ∀ (order : ℤ ≃
        { z : ℤ × ℤ // TriangularBoundaryStrip x y z }), (path.head? = some x ∧ path.getLast? =
        some y ∧ path.Nodup ∧ (∀ z ∈ path, TriangularBoundaryStrip x y z) ∧ path.IsChain
        TriangularLatticeAdjacent) → (
    let index : (Int × Int) → Int := fun z =>
      @dite Int (TriangularBoundaryStrip x y z) (Classical.propDecidable _)
        (fun hz => order.symm ⟨z, hz⟩) (fun _ => 0)
    let indices := path.map index
    (∀ z, z ∈ path → (order (index z)).1 = z) → (indices.Nodup)) := by
  classical
  intro x y path order hdata index indices hindex_apply
  apply List.Nodup.map_on (l := path)
  · intro a ha b hb hab
    have he : order (index a) = order (index b) := by
      exact congrArg order hab
    calc
      a = (order (index a)).1 := (hindex_apply a ha).symm
      _ = (order (index b)).1 := congrArg Subtype.val he
      _ = b := hindex_apply b hb
  · exact hdata.2.2.1

private theorem hindices_chain :
    ∀ (x : Int × Int), ∀ (y : Int × Int), ∀ (path : List (Int × Int)), ∀ (order : ℤ ≃
        { z : ℤ × ℤ // TriangularBoundaryStrip x y z }), (∀ (m : ℤ), ∀ (n : ℤ),
        TriangularLatticeAdjacent (↑((order : ℤ → { z : ℤ × ℤ // TriangularBoundaryStrip x y z })
        m) : ℤ × ℤ) (↑((order : ℤ → { z : ℤ × ℤ // TriangularBoundaryStrip x y z }) n) : ℤ × ℤ) ↔
        n = m + (1 : ℤ) ∨ m = n + (1 : ℤ)) → ((path.head? = some x ∧ path.getLast? = some y ∧
        path.Nodup ∧ (∀ z ∈ path, TriangularBoundaryStrip x y z) ∧ path.IsChain
        TriangularLatticeAdjacent) → (
    let index : (Int × Int) → Int := fun z =>
      @dite Int (TriangularBoundaryStrip x y z) (Classical.propDecidable _)
        (fun hz => order.symm ⟨z, hz⟩) (fun _ => 0)
    let indices := path.map index
    (∀ z, z ∈ path → (order (index z)).1 = z) → (indices.IsChain (fun u v : Int => v = u + 1 ∨ u
        = v + 1)))) := by
  classical
  intro x y path order hadj hdata index indices hindex_apply
  change List.IsChain (fun u v : Int => v = u + 1 ∨ u = v + 1) (path.map index)
  rw [List.isChain_map]
  apply List.IsChain.imp_of_mem_imp (l := path)
  · intro a b ha hb hab
    have q : TriangularLatticeAdjacent (order (index a)).1 (order (index b)).1 := by
      rw [hindex_apply a ha, hindex_apply b hb]
      exact hab
    exact (hadj (index a) (index b)).mp q
  · exact hdata.2.2.2.2

private theorem trim_property :
    (∀ (p : List Int),
        ∀ (a : Int),
          ∀ (b : Int),
            p.head? = some a →
              p.getLast? = some b →
                p.Nodup →
                  (p.IsChain fun u v : Int => v = u + 1 ∨ u = v + 1) →
                    ∀ z : Int, z ∈ p ↔ min a b ≤ z ∧ z ≤ max a b) →
      ∀ (l : List Int),
        ∀ (a : Int),
          ∀ (b : Int),
            l.head? = some a →
              l.getLast? = some b →
                l.Nodup → ∀ q, q ∈ (l.drop 1).dropLast ↔ q ∈ l ∧ q ≠ a ∧ q ≠ b := by
  classical
  intro walk l
  cases l with
  | nil =>
      intro a b ha hb hn q
      simp at ha
  | cons c t =>
      intro a b ha hb hn q
      have hac : a = c := by simpa using ha.symm
      subst a
      cases t with
      | nil => simp_all; omega
      | cons d s =>
          have htail : (d :: s).getLast? = some b := by simpa using hb
          have htail_nodup : (d :: s).Nodup := (List.nodup_cons.mp hn).2
          constructor
          · intro hq
            have hqt : q ∈ d :: s := List.mem_of_mem_dropLast hq
            have hqc : q ≠ c := by
              intro hqc
              exact (List.nodup_cons.mp hn).1 (hqc ▸ hqt)
            have hqb : q ≠ b := by
              intro hqb
              subst q
              have hdup : d :: s = (d :: s).dropLast ++ [b] :=
                (List.dropLast_append_getLast? b (by simpa using htail)).symm
              rw [hdup] at htail_nodup
              have hq' : b ∈ (d :: s).dropLast := by simpa using hq
              exact ((List.nodup_append.mp htail_nodup).2.2 b hq' b (by simp)) rfl
            exact ⟨by simp [hqt], hqc, hqb⟩
          · rintro ⟨hq, hqc, hqb⟩
            have hqt : q ∈ d :: s := by simpa [hqc] using hq
            have hqopt : some q ≠ (d :: s).getLast? := by
              intro he
              have heq : q = b := Option.some.inj (he.trans htail)
              exact hqb heq
            exact List.mem_dropLast_of_mem_of_ne_getLast? hqt hqopt

private theorem hmaptrim :
    ∀ (x : Int × Int), ∀ (y : Int × Int), ∀ (path : List (Int × Int)), ∀ (order : ℤ ≃
        { z : ℤ × ℤ // TriangularBoundaryStrip x y z }),
    let index : (Int × Int) → Int := fun z =>
      @dite Int (TriangularBoundaryStrip x y z) (Classical.propDecidable _)
        (fun hz => order.symm ⟨z, hz⟩) (fun _ => 0)
    let indices := path.map index
    (∀ z, z ∈ path → (order (index z)).1 = z) → ((∀ z, TriangularBoundaryStrip x y z → (order
        (index z)).1 = z) → (∀ z, TriangularBoundaryStrip x y z →
      (z ∈ (path.drop 1).dropLast ↔
      index z ∈ (indices.drop 1).dropLast))) := by
  classical
  intro x y path order index indices hindex_apply hindex_boundary z hzb
  constructor
  · intro hz
    change index z ∈ ((path.map index).drop 1).dropLast
    rw [← List.map_drop, ← List.map_dropLast]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  · intro hz
    change index z ∈ ((path.map index).drop 1).dropLast at hz
    rw [← List.map_drop, ← List.map_dropLast] at hz
    rcases List.mem_map.mp hz with ⟨w, hw, hwi⟩
    have hwpath : w ∈ path := List.mem_of_mem_drop (List.mem_of_mem_dropLast hw)
    have heq : w = z := by
      have he : order (index w) = order (index z) := by rw [hwi]
      calc
        w = (order (index w)).1 := (hindex_apply w hwpath).symm
        _ = (order (index z)).1 := congrArg Subtype.val he
        _ = z := hindex_boundary z hzb
    exact heq ▸ hw

private theorem hzmem :
    ∀ (x : Int × Int), ∀ (y : Int × Int), ∀ (path : List (Int × Int)), ∀ (order : ℤ ≃
        { z : ℤ × ℤ // TriangularBoundaryStrip x y z }), ∀ (m : ℤ), ∀ (n : ℤ),
    let index : (Int × Int) → Int := fun z =>
      @dite Int (TriangularBoundaryStrip x y z) (Classical.propDecidable _)
        (fun hz => order.symm ⟨z, hz⟩) (fun _ => 0)
    let indices := path.map index
    (∀ z, z ∈ path → (order (index z)).1 = z) → ((∀ (z : ℤ), z ∈ indices ↔ min m n ≤ z ∧ z ≤ max
        m n) → (∀ (z : ℤ × ℤ), ∀ (k : ℤ), (min m n ≤ k) → ((k ≤ max m n) → (((↑((order : ℤ →
        { z : ℤ × ℤ // TriangularBoundaryStrip x y z }) k) : ℤ × ℤ) = z) → (z ∈ path))))) := by
  classical
  intro x y path order m n index indices hindex_apply hindset z k hk1 hk2 hk
  have hi := (hindset k).mpr ⟨hk1, hk2⟩
  change k ∈ path.map index at hi
  rcases List.mem_map.mp hi with ⟨w, hw, hwi⟩
  have heq : w = z := by
    have he' := congrArg order hwi
    have he'' := congrArg Subtype.val he'
    rw [hindex_apply w hw, hk] at he''
    exact he''
  exact heq ▸ hw

end StripOrderIntervalProof

theorem TriangularStripSegmentOrderInterval
    (x y : Int × Int) (hxy : x ≠ y)
    (path : List (Int × Int))
    (hpath : TriangularStripSegment x y path) :
    ∃ order : Int ≃ {z : Int × Int // TriangularBoundaryStrip x y z},
      (∀ m n : Int,
        TriangularLatticeAdjacent (order m).1 (order n).1 ↔
          n = m + 1 ∨ m = n + 1) ∧
      ∃ m n : Int,
        (order m).1 = x ∧ (order n).1 = y ∧
        (∀ z : Int × Int, z ∈ path ↔
          ∃ k : Int,
            min m n ≤ k ∧ k ≤ max m n ∧ (order k).1 = z) ∧
        (∀ z : Int × Int, z ∈ (path.drop 1).dropLast ↔
          ∃ k : Int,
            min m n < k ∧ k < max m n ∧ (order k).1 = z) := by
-- BODY
  have hmain := (AffineTriangularStrip).2 x y hxy
  obtain ⟨hinc, hstrip, order, hadj⟩ := hmain
  have hdata : path.head? = some x ∧ path.getLast? = some y ∧
      path.Nodup ∧ (∀ z ∈ path, TriangularBoundaryStrip x y z) ∧
      path.IsChain TriangularLatticeAdjacent := by
    simpa [TriangularStripSegment, hxy] using hpath
  have hxmem : x ∈ path := by
    apply List.mem_of_mem_head?
    simp [hdata.1]
  have hymem : y ∈ path := by
    exact List.mem_of_getLast? hdata.2.1
  obtain ⟨m, hm⟩ := order.surjective ⟨x, hdata.2.2.2.1 x hxmem⟩
  obtain ⟨n, hn⟩ := order.surjective ⟨y, hdata.2.2.2.1 y hymem⟩
  have walk : ∀ (p : List Int) (a b : Int),
      p.head? = some a → p.getLast? = some b → p.Nodup →
      p.IsChain (fun u v : Int => v = u + 1 ∨ u = v + 1) →
      (∀ z : Int, z ∈ p ↔ min a b ≤ z ∧ z ≤ max a b) := StripOrderIntervalProof.walk
  have hfirst : path.head? = some x := hdata.1
  have hlast : path.getLast? = some y := hdata.2.1
  classical
  let index : (Int × Int) → Int := fun z => if hz : TriangularBoundaryStrip x y z then
      order.symm ⟨z, hz⟩ else 0
  let indices := path.map index
  have hindex_apply : ∀ z, z ∈ path → (order (index z)).1 = z := by
    intro z hz
    simp [index, hdata.2.2.2.1 z hz]
  have hindx : index x = m := by
    apply order.injective
    apply Subtype.ext
    rw [hindex_apply x hxmem]
    exact congrArg Subtype.val hm.symm
  have hindy : index y = n := by
    apply order.injective
    apply Subtype.ext
    rw [hindex_apply y hymem]
    exact congrArg Subtype.val hn.symm
  have hindices_head : indices.head? = some m := by
    simp [indices, List.head?_map, hfirst, hindx]
  have hindices_last : indices.getLast? = some n := by
    simp [indices, List.getLast?_map, hlast, hindy]
  have hindices_nodup : indices.Nodup := StripOrderIntervalProof.hindices_nodup x y path order
      hdata hindex_apply
  have hindices_chain : indices.IsChain (fun u v : Int => v = u + 1 ∨ u = v + 1) :=
      StripOrderIntervalProof.hindices_chain x y path order hadj hdata hindex_apply
  have hindset := walk indices m n hindices_head hindices_last hindices_nodup hindices_chain
  have hindex_boundary : ∀ z, TriangularBoundaryStrip x y z →
      (order (index z)).1 = z := by
    intro z hz
    simp [index, hz]
  have trim_property : ∀ (l : List Int) (a b : Int),
      l.head? = some a → l.getLast? = some b → l.Nodup →
      ∀ q, q ∈ (l.drop 1).dropLast ↔ q ∈ l ∧ q ≠ a ∧ q ≠ b :=
          StripOrderIntervalProof.trim_property walk
  have hmaptrim : ∀ z, TriangularBoundaryStrip x y z →
      (z ∈ (path.drop 1).dropLast ↔
      index z ∈ (indices.drop 1).dropLast) := StripOrderIntervalProof.hmaptrim x y path order
          hindex_apply hindex_boundary
  refine ⟨order, hadj, m, n, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hm
  · exact congrArg Subtype.val hn
  · intro z
    constructor
    · intro hz
      have hz' := (hindset (index z)).mp (by
        apply List.mem_map.mpr
        exact ⟨z, hz, rfl⟩)
      rcases hz' with ⟨hk1, hk2⟩
      refine ⟨index z, hk1, hk2, ?_⟩
      exact hindex_apply z hz
    · rintro ⟨k, hk1, hk2, hk⟩
      have hzmem : z ∈ path := StripOrderIntervalProof.hzmem x y path order m n hindex_apply
          hindset z k hk1 hk2 hk
      exact hzmem
  · intro z
    constructor
    · intro hz
      have hzpath : z ∈ path := List.mem_of_mem_drop (List.mem_of_mem_dropLast hz)
      have hzb : TriangularBoundaryStrip x y z := hdata.2.2.2.1 z hzpath
      have htrim := trim_property indices m n hindices_head hindices_last hindices_nodup (index z)
      have hi := (hmaptrim z hzb).mp hz
      have hbounds := (htrim.mp hi).1
      have hneq := (htrim.mp hi).2
      have hclosed := (hindset (index z)).mp hbounds
      refine ⟨index z, ?_, ?_, hindex_boundary z hzb⟩
      · omega
      · omega
    · rintro ⟨k, hk1, hk2, hk⟩
      have hzb : TriangularBoundaryStrip x y z := by
        rw [← hk]
        exact (order k).property
      have hik : index z = k := by
        apply order.injective
        apply Subtype.ext
        rw [hindex_boundary z hzb, hk]
      have hclosed : min m n ≤ k ∧ k ≤ max m n := by omega
      have himem := (hindset k).mpr hclosed
      have htrim := trim_property indices m n hindices_head hindices_last hindices_nodup (index z)
      have hstrict : index z ≠ m ∧ index z ≠ n := by omega
      have hinner := htrim.mpr ⟨by simpa [hik] using himem, hstrict.1, hstrict.2⟩
      exact (hmaptrim z hzb).mpr hinner

end ApollonianSuperharmonic

end
