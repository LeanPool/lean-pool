/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5435T1ShellPaths
public import LeanPool.ApollonianSuperharmonic.P5435T1PeriodGap
public import LeanPool.ApollonianSuperharmonic.P4818T1Representatives
public import Mathlib.Data.List.Chain

-- [TABLET NODE: P5435T1WebGeometry]

/-!
# P5435T1WebGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5435T1WebGeometry (K : DiamondParameter) :
    let D := DiamondVertexDomains K true
    let S := DiamondVertexDomains K false \ D
    let W : Set GaussianInt :=
      {x | ∃ v ∈ DiamondExceptionalLattice K, x - v ∈ S}
    FourNeighborConnected W ∧
      ∀ x, x ∉ W → ∃ v ∈ DiamondExceptionalLattice K, ∀ y,
        Relation.ReflTransGen
          (fun u z => u ∉ W ∧ z ∉ W ∧ FourNeighborAdjacent u z) x y →
        y - v ∈ D := by
-- BODY
  classical
  dsimp only
  let k : Int := K.1
  let a : GaussianInt := ⟨0, -(2*K.1 : Int)⟩
  let b : GaussianInt := ⟨(K.1+1 : Int), (K.1 : Int)⟩
  let L := DiamondExceptionalLattice K
  let D := DiamondVertexDomains K true
  let S := DiamondVertexDomains K false \ D
  let W : Set GaussianInt := {x | ∃ v ∈ L, x-v ∈ S}
  change FourNeighborConnected W ∧ _
  obtain ⟨hS, hA, hB⟩ := P5435T1ShellPaths K
  have hs0 : (0 : GaussianInt) ∈ S := by
    convert hA.1 using 1
    ext <;> rfl
  have ha : a ∈ L := AddSubgroup.subset_closure (Or.inl rfl)
  have hb : b ∈ L := AddSubgroup.subset_closure (Or.inr rfl)
  have adjSymm {x y : GaussianInt} (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := by
    rcases h with rfl | rfl | rfl | rfl <;>
      simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
  have adjShift {x y : GaussianInt} (h : FourNeighborAdjacent x y) (v : GaussianInt) :
      FourNeighborAdjacent (x+v) (y+v) := by
    rcases h with rfl | rfl | rfl | rfl <;>
      simp [FourNeighborAdjacent, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  have inW (v : GaussianInt) (hv : v ∈ L) (s : GaussianInt) (hs : s ∈ S) :
      s+v ∈ W := ⟨v, hv, by simpa using hs⟩
  have shiftW (x : GaussianInt) (hx : x ∈ W) (v : GaussianInt) (hv : v ∈ L) :
      x+v ∈ W := by
    obtain ⟨u, hu, hs⟩ := hx
    exact ⟨u+v, L.add_mem hu hv, by simpa only [add_sub_add_right_eq_sub] using hs⟩
  let Q := fun x y => x ∈ W ∧ y ∈ W ∧ FourNeighborAdjacent x y
  have reverse {x y} (h : Relation.ReflTransGen Q x y) :
      Relation.ReflTransGen Q y x := by
    induction h with
    | refl => exact .refl
    | tail h e ih => exact (Relation.ReflTransGen.single
        ⟨e.2.1, e.1, adjSymm e.2.2⟩).trans ih
  have shellReach (v : GaussianInt) (hv : v ∈ L)
      (s : GaussianInt) (hs : s ∈ S) (t : GaussianInt) (ht : t ∈ S) :
      Relation.ReflTransGen Q (s+v) (t+v) := by
    obtain ⟨p, hp, hlast, pall, padj⟩ := hS.2 s hs t ht
    have hc : p.IsChain (fun u z => u ∈ S ∧ z ∈ S ∧ FourNeighborAdjacent u z) := by
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro u z l₁ l₂ he
      exact ⟨pall u (by simp [he]), pall z (by simp [he]), padj u z l₁ l₂ he⟩
    have hr : Relation.ReflTransGen
        (fun u z => u ∈ S ∧ z ∈ S ∧ FourNeighborAdjacent u z) s t := by
      cases p with
      | nil => simp at hp
      | cons u p =>
        simp only [List.head?_cons, Option.some.injEq] at hp
        subst u
        exact List.relationReflTransGen_of_exists_isChain_cons p hc
          (List.getLast_of_getLast?_eq_some hlast)
    exact Relation.ReflTransGen.lift (fun u => u+v)
      (fun u z he => ⟨inW v hv u he.1, inW v hv z he.2.1, adjShift he.2.2 v⟩)
      _ _ hr
  have genReach (d : GaussianInt) (hd : d ∈ L)
      (t : GaussianInt) (ht : t ∈ S) (htd : t-d ∈ S) :
      ∀ x ∈ W, Relation.ReflTransGen Q x (x+d) := by
    rintro x ⟨v, hv, hs⟩
    have h1 := shellReach v hv (x-v) hs t ht
    have h2 := shellReach (v+d) (L.add_mem hv hd) (t-d) htd (x-v) hs
    have h2' : Relation.ReflTransGen Q (t+v) (x+d) := by
      convert h2 using 1 <;> abel
    simpa only [sub_add_cancel] using h1.trans h2'
  let H : AddSubgroup GaussianInt :=
    { carrier := {v | v ∈ L ∧ ∀ x ∈ W, Relation.ReflTransGen Q x (x+v)}
      zero_mem' := ⟨L.zero_mem, by intro x hx; simpa using (Relation.ReflTransGen.refl (a := x)
          (r := Q))⟩
      add_mem' := by
        rintro u v ⟨hu, hpu⟩ ⟨hv, hpv⟩
        refine ⟨L.add_mem hu hv, ?_⟩
        intro x hx
        simpa only [add_assoc] using (hpu x hx).trans (hpv (x+u) (shiftW x hx u hu))
      neg_mem' := by
        rintro v ⟨hv, hp⟩
        refine ⟨L.neg_mem hv, ?_⟩
        intro x hx
        have h := reverse (hp (x-v) (by
          simpa only [sub_eq_add_neg] using shiftW x hx (-v) (L.neg_mem hv)))
        rw [sub_add_cancel] at h
        simpa only [sub_eq_add_neg] using h }
  have hgen : {v : GaussianInt | v=a ∨ v=b} ⊆ H := by
    intro v hv
    rcases hv with rfl | rfl
    · refine ⟨ha, genReach a ha 0 hs0 ?_⟩
      have he : (0 : GaussianInt)-a = ⟨0, (2*K.1 : Int)⟩ := by
        ext <;> simp [a]
      rw [he]
      exact hA.2
    · refine ⟨hb, genReach b hb ⟨k,k+1⟩ hB.1 ?_⟩
      have he : (⟨k,k+1⟩ : GaussianInt)-b = ⟨-1,1⟩ := by
        ext <;> simp [b, k]
      rw [he]
      exact hB.2
  have hLH : L ≤ H := (AddSubgroup.closure_le H).mpr hgen
  have zeroW : (0 : GaussianInt) ∈ W := ⟨0, L.zero_mem, by simpa using hs0⟩
  have reach0 : ∀ x ∈ W, Relation.ReflTransGen Q 0 x := by
    rintro x ⟨v, hv, hs⟩
    have h1 := (hLH hv).2 0 zeroW
    have h2 := shellReach v hv 0 hs0 (x-v) hs
    simpa only [zero_add, sub_add_cancel] using h1.trans h2
  constructor
  · refine ⟨⟨0, zeroW⟩, ?_⟩
    intro x hx y hy
    have hr := (reverse (reach0 x hx)).trans (reach0 y hy)
    obtain ⟨p, hc, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hr
    refine ⟨x::p, rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p), hlast]
    · exact hc.induction (fun t => t ∈ W) (x::p)
        (fun {u z} he _ => he.2.1) (fun _ => hx)
    · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp
        (hc.imp (fun _ _ he => he.2.2))
  · have coverage : ∀ x, x ∉ W → ∃ v ∈ L, x-v ∈ D := by
      intro x hx
      obtain ⟨p, hp, _⟩ := P4818T1Representatives K x
      let v := p.2.1 • a + p.2.2 • b
      have hv : v ∈ L := L.add_mem (L.zsmul_mem ha _) (L.zsmul_mem hb _)
      have he : x-v=p.1 := by
        have he' : x=p.1+v := by
          simpa only [v, a, b, neg_mul, add_assoc] using hp.2
        rw [he']; abel
      refine ⟨v, hv, ?_⟩
      by_contra hn
      exact hx ⟨v, hv, he ▸ ⟨hp.1.1, he ▸ hn⟩⟩
    have inner (x : GaussianInt) (hx : x ∈ D) :
        |x.re| + |x.im-k| ≤ k-1 := by
      change x.re.natAbs + (x.im-k).natAbs ≤ K.1-1 at hx
      have ha := Int.natCast_natAbs x.re
      have hb := Int.natCast_natAbs (x.im-k)
      have hk := K.2
      dsimp only [k] at hx ha hb ⊢
      omega
    have adjacentOwner (x y v v' : GaussianInt)
        (hv : v ∈ L) (hv' : v' ∈ L) (hx : x-v ∈ D) (hy : y-v' ∈ D)
        (hadj : FourNeighborAdjacent x y) : v=v' := by
      by_contra hn
      have hg := P5435T1PeriodGap K (v-v') (L.sub_mem hv hv') (sub_ne_zero.mpr hn)
      have hxi := inner (x-v) hx
      have hyi := inner (y-v') hy
      change 2*k ≤ |(v-v').re|+|(v-v').im| at hg
      rcases hadj with rfl | rfl | rfl | rfl <;>
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
          Zsqrtd.re_one, Zsqrtd.im_one, add_zero, sub_zero,
          abs_eq_max_neg] at hg hxi hyi <;> omega
    intro x hx
    obtain ⟨v, hv, hxv⟩ := coverage x hx
    refine ⟨v, hv, ?_⟩
    intro y hy
    induction hy with
    | refl => exact hxv
    | @tail y z h e ih =>
      obtain ⟨v', hv', hz⟩ := coverage z e.2.1
      have he := adjacentOwner y z v v' hv hv' ih hz e.2.2
      simpa only [he] using hz

end ApollonianSuperharmonic

end
