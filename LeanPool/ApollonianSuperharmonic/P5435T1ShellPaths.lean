/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

-- [TABLET NODE: P5435T1ShellPaths]

/-!
# P5435T1ShellPaths

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5435T1ShellPaths (K : DiamondParameter) :
    let k : Int := K.1
    let S := DiamondVertexDomains K false \ DiamondVertexDomains K true
    FourNeighborConnected S ∧
      ((⟨0, 0⟩ : GaussianInt) ∈ S ∧ ⟨0, 2 * k⟩ ∈ S) ∧
      ((⟨k, k + 1⟩ : GaussianInt) ∈ S ∧ ⟨-1, 1⟩ ∈ S) := by
-- BODY
  classical
  dsimp only
  let k : Int := K.1
  let S := DiamondVertexDomains K false \ DiamondVertexDomains K true
  have hk : 0 < K.1 := K.2
  have bounds (x : GaussianInt) : x ∈ S ↔
      x.re.natAbs ≤ K.1 ∧ (x.im-k).natAbs ≤ K.1 ∧
        K.1 ≤ x.re.natAbs + (x.im-k).natAbs ∧
        x.re.natAbs + (x.im-k).natAbs ≤ K.1+1 := by
    change (max x.re.natAbs (max (x.im-k).natAbs
      (x.re.natAbs + (x.im-k).natAbs - 1)) ≤ K.1 ∧
        ¬ x.re.natAbs + (x.im-k).natAbs ≤ K.1-1) ↔ _
    rw [max_le_iff, max_le_iff]
    omega
  let Q := fun x y : GaussianInt => x ∈ S ∧ y ∈ S ∧ FourNeighborAdjacent x y
  have reverse {x y} (h : Relation.ReflTransGen Q x y) :
      Relation.ReflTransGen Q y x := by
    induction h with
    | refl => exact .refl
    | @tail u z h e ih =>
      have hs : FourNeighborAdjacent z u := by
        rcases e.2.2 with h | h | h | h <;> rw [h] <;>
          simp [FourNeighborAdjacent, add_assoc, add_comm, add_left_comm]
      exact (Relation.ReflTransGen.single ⟨e.2.1, e.1, hs⟩).trans ih
  let pt (sx sy : Int) (p r : Nat) : GaussianInt := ⟨sx*p, k+sy*r⟩
  have pmem (sx sy : Int) (hsx : sx=1 ∨ sx = -1) (hsy : sy=1 ∨ sy = -1)
      (p r : Nat) (hp : p ≤ K.1) (hr : r ≤ K.1)
      (hlo : K.1 ≤ p+r) (hhi : p+r ≤ K.1+1) : pt sx sy p r ∈ S := by
    rw [bounds]
    have he : (pt sx sy p r).re.natAbs = p := by
      rcases hsx with rfl | rfl <;> simp [pt]
    have hi : ((pt sx sy p r).im-k).natAbs = r := by
      rcases hsy with rfl | rfl <;> simp [pt]
    rw [he, hi]
    exact ⟨hp, hr, hlo, hhi⟩
  have horiz (sx sy : Int) (hsx : sx=1 ∨ sx = -1) (p r : Nat) :
      FourNeighborAdjacent (pt sx sy (p+1) r) (pt sx sy p r) := by
    rcases hsx with rfl | rfl
    · apply Or.inr; apply Or.inl
      ext <;> simp [pt]
    · apply Or.inl
      ext <;> simp [pt]
  have vert (sx sy : Int) (hsy : sy=1 ∨ sy = -1) (p r : Nat) :
      FourNeighborAdjacent (pt sx sy p r) (pt sx sy p (r+1)) := by
    rcases hsy with rfl | rfl
    · apply Or.inr; apply Or.inr; apply Or.inl
      ext <;> simp [pt]; ring
    · apply Or.inr; apply Or.inr; apply Or.inr
      ext <;> simp [pt]; ring
  have quadrant (sx sy : Int) (hsx : sx=1 ∨ sx = -1) (hsy : sy=1 ∨ sy = -1) :
      ∀ p r : Nat, p ≤ K.1 → r ≤ K.1 → K.1 ≤ p+r → p+r ≤ K.1+1 →
        Relation.ReflTransGen Q (pt sx sy p r) (pt sx sy 0 K.1) := by
    intro p
    induction p with
    | zero =>
      intro r hp hr hlo hhi
      have he : r=K.1 := by omega
      subst r
      exact .refl
    | succ p ih =>
      intro r hp hr hlo hhi
      have hstart := pmem sx sy hsx hsy (p+1) r hp hr hlo hhi
      by_cases hout : p+1+r=K.1+1
      · have hnext := pmem sx sy hsx hsy p r (by omega) hr (by omega) (by omega)
        exact (Relation.ReflTransGen.single ⟨hstart, hnext, horiz sx sy hsx p r⟩).trans
          (ih r (by omega) hr (by omega) (by omega))
      · have hpeak := pmem sx sy hsx hsy (p+1) (r+1) hp (by omega) (by omega) (by omega)
        have hnext := pmem sx sy hsx hsy p (r+1) (by omega) (by omega) (by omega) (by omega)
        exact (Relation.ReflTransGen.single ⟨hstart, hpeak, vert sx sy hsy (p+1) r⟩).trans
          ((Relation.ReflTransGen.single ⟨hpeak, hnext, horiz sx sy hsx p (r+1)⟩).trans
            (ih (r+1) (by omega) (by omega) (by omega) (by omega)))
  let top := pt 1 1 0 K.1
  let bot := pt 1 (-1) 0 K.1
  have bridge : Relation.ReflTransGen Q top bot := by
    have h1 := quadrant 1 1 (Or.inl rfl) (Or.inl rfl) K.1 0
      (by omega) (by omega) (by omega) (by omega)
    have h2 := quadrant 1 (-1) (Or.inl rfl) (Or.inr rfl) K.1 0
      (by omega) (by omega) (by omega) (by omega)
    have he : pt 1 (-1) K.1 0 = pt 1 1 K.1 0 := by simp [pt]
    rw [he] at h2
    exact (reverse h1).trans h2
  have signed (n : Int) : ∃ s : Int, (s=1 ∨ s = -1) ∧ n=s*(n.natAbs : Int) := by
    by_cases hn : 0 ≤ n
    · exact ⟨1, Or.inl rfl, by simp [abs_of_nonneg hn]⟩
    · exact ⟨-1, Or.inr rfl, by simp [abs_of_neg (by omega : n<0)]⟩
  have toBot : ∀ x ∈ S, Relation.ReflTransGen Q x bot := by
    intro x hx
    obtain ⟨sx, hsx, hex⟩ := signed x.re
    obtain ⟨sy, hsy, hey⟩ := signed (x.im-k)
    have hxpt : x=pt sx sy x.re.natAbs (x.im-k).natAbs := by
      ext
      · exact hex
      · change x.im=k+sy*((x.im-k).natAbs : Int)
        omega
    obtain ⟨hp, hr, hlo, hhi⟩ := (bounds x).mp hx
    have hq := quadrant sx sy hsx hsy _ _ hp hr hlo hhi
    rw [← hxpt] at hq
    rcases hsy with rfl | rfl
    · have he : pt sx 1 0 K.1=top := by simp [pt, top]
      rw [he] at hq
      exact hq.trans bridge
    · have he : pt sx (-1) 0 K.1=bot := by simp [pt, bot]
      rw [he] at hq
      exact hq
  have hbot : bot ∈ S := pmem 1 (-1) (Or.inl rfl) (Or.inr rfl) 0 K.1
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨bot, hbot⟩, ?_⟩
    intro x hx y hy
    obtain ⟨p, hc, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen
      ((toBot x hx).trans (reverse (toBot y hy)))
    refine ⟨x::p, rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p), hlast]
    · exact hc.induction (fun t => t ∈ S) (x::p)
        (fun {u z} he _ => he.2.1) (fun _ => hx)
    · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp
        (hc.imp (fun _ _ he => he.2.2))
  · constructor
    · convert hbot using 1; ext <;> simp [bot, pt, k]
    · have ht := pmem 1 1 (Or.inl rfl) (Or.inl rfl) 0 K.1
        (by omega) (by omega) (by omega) (by omega)
      convert ht using 1; ext <;> simp [pt, k]; ring
  · constructor
    · have ht := pmem 1 1 (Or.inl rfl) (Or.inl rfl) K.1 1
        (by omega) (by omega) (by omega) (by omega)
      convert ht using 1; ext <;> simp [pt, k]
    · have ht := pmem (-1) (-1) (Or.inr rfl) (Or.inr rfl) 1 (K.1-1)
        (by omega) (by omega) (by omega) (by omega)
      convert ht using 1
      ext <;> simp only [Int.reduceNeg, Nat.cast_one, mul_one, pt, neg_mul, one_mul, k]
      have hcast : ((K.1-1 : Nat) : Int)=(K.1 : Int)-1 := by omega
      rw [hcast]
      ring

end ApollonianSuperharmonic

end
