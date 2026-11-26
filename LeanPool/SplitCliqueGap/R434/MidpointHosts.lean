/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.ExactGraphTransfer
public import LeanPool.SplitCliqueGap.R434.OddMidpoints
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Midpoint palettes on a core with translation-invariant role directions. -/

@[expose] public section

open Finset

namespace GapExtremal.R434

section

variable {L R C : Type} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
variable [CommRing R] [DecidableEq C]

variable (H : SimpleGraph L) [DecidableRel H.Adj] (step : L → L → R)
variable (A : Finset R) (h : R)

/-- The direction of an ordered vertex pair after applying the role-dependent step. -/
def pairDirection (x y : L × R) : R := step x.1 y.1 * (y.2 - x.2)

omit [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] in
theorem pairDirection_swap (hs : ∀ i j, step j i = -step i j)
    (x y : L × R) : pairDirection step y x = pairDirection step x y := by
  unfold pairDirection
  rw [hs]
  ring

/-- The graph whose edges have adjacent roles and an allowed direction. -/
def directionCore (hs : ∀ i j, step j i = -step i j) : SimpleGraph (L × R) where
  Adj x y := H.Adj x.1 y.1 ∧ pairDirection step x y ∈ A
  symm := ⟨by
    intro x y hp
    exact ⟨hp.1.symm, (pairDirection_swap step hs x y).symm ▸ hp.2⟩⟩
  loopless := ⟨fun _ hp => H.loopless.irrefl _ hp.1⟩

instance directionCoreDecidable (hs : ∀ i j, step j i = -step i j) :
    DecidableRel (directionCore H step A hs).Adj :=
  fun x y => inferInstanceAs (Decidable (H.Adj x.1 y.1 ∧ pairDirection step x y ∈ A))

/-- A host label consisting of a role pair, a midpoint, and an optional colour. -/
abbrev MidHost (L R C : Type) := Sym2 L × R × Option C

/-- The host index for a pair of vertices, determined by its roles and midpoint. -/
def midAssign (χ : R → C) (x y : L × R) : MidHost L R C :=
  (s(x.1,y.1), h * (x.2 + y.2),
    if H.Adj x.1 y.1 then some (χ (pairDirection step x y)) else none)

omit [DecidableEq C] [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] in
theorem midAssign_swap (hs : ∀ i j, step j i = -step i j) (χ : R → C)
    (x y : L × R) : midAssign H step h χ x y = midAssign H step h χ y x := by
  have hAdj : H.Adj y.1 x.1 ↔ H.Adj x.1 y.1 := ⟨fun ha => ha.symm, fun ha => ha.symm⟩
  simp only [midAssign, ← Sym2.eq_swap (a := x.1) (b := y.1), hAdj,
    pairDirection_swap step hs x y, add_comm y.2 x.2]

/-- The finite palette of vertices admitted by the given midpoint host. -/
noncomputable def midPalette (hs : ∀ i j, step j i = -step i j) (χ : R → C)
    (k : MidHost L R C) : Finset (L × R) := by
  classical
  exact univ.filter fun x => ∃ y, x ≠ y ∧ ¬ (directionCore H step A hs).Adj x y ∧
    midAssign H step h χ x y = k

omit [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] in
theorem direction_of_cross_fibre (hs : ∀ i j, step j i = -step i j) (hh : 2 * h = 1)
    (x x' y y' : L × R) (hr : x.1 = y'.1) (hs' : x'.1 = y.1)
    (hm : h * (x.2 + x'.2) = h * (y.2 + y'.2)) :
    pairDirection step x y = h * (pairDirection step x x' + pairDirection step y y') := by
  have hsum := congrArg (fun u : R => 2 * u) hm
  simp only [← mul_assoc, hh, one_mul] at hsum
  unfold pairDirection
  rw [hs', ← hr, hs x.1 y.1]
  calc
    _ = (2 * h) * (step x.1 y.1 * (y.2 - x.2)) := by rw [hh, one_mul]
    _ = _ := by linear_combination -(h * step x.1 y.1) * hsum

theorem midpoint_host_hyp (hs : ∀ i j, step j i = -step i j) (hh : 2 * h = 1)
    (χ : R → C)
    (hχ : ∀ a b, a ∉ A → b ∉ A → χ a = χ b → h * (a + b) ∉ A) :
    HostHyp (directionCore H step A hs) (midPalette H step A h hs χ)
      (midAssign H step h χ) := by
  classical
  constructor
  · intro k x hx y hy hxy
    change H.Adj x.1 y.1 ∧ pairDirection step x y ∈ A at hxy
    change x ∈ univ.filter _ at hx
    change y ∈ univ.filter _ at hy
    obtain ⟨x', _, hxx, hxk⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨y', _, hyy, hyk⟩ := (Finset.mem_filter.mp hy).2
    have heq := hxk.trans hyk.symm
    have hroles : s(x.1,x'.1) = s(y.1,y'.1) := congrArg Prod.fst heq
    rcases Sym2.eq_iff.mp hroles with ⟨he, _⟩ | ⟨hr, hs'⟩
    · exact H.loopless.irrefl _ (he ▸ hxy.1)
    · have h₁ : H.Adj x.1 x'.1 := hs'.symm ▸ hxy.1
      have h₂ : H.Adj y.1 y'.1 := hr ▸ hxy.1.symm
      have hcolor : χ (pairDirection step x x') = χ (pairDirection step y y') := by
        have hc := congrArg (fun u : MidHost L R C => u.2.2) heq
        simpa only [midAssign, ite_eq_left h₁, ite_eq_left h₂, Option.some.injEq] using hc
      have hbad₁ : pairDirection step x x' ∉ A := fun ha => hxx ⟨h₁, ha⟩
      have hbad₂ : pairDirection step y y' ∉ A := fun ha => hyy ⟨h₂, ha⟩
      apply hχ _ _ hbad₁ hbad₂ hcolor
      rw [← direction_of_cross_fibre step h hs hh x x' y y' hr hs']
      · exact hxy.2
      · exact congrArg (fun u : MidHost L R C => u.2.1) heq
  · intro x y hne hxy
    constructor
    · exact Finset.mem_filter.mpr ⟨mem_univ _, y, hne, hxy, rfl⟩
    · exact Finset.mem_filter.mpr ⟨mem_univ _, x, hne.symm, fun h' => hxy h'.symm,
        midAssign_swap H step h hs χ y x⟩
  · exact midAssign_swap H step h hs χ
  · intro x y y' _ _ _ _ heq
    have hroles : s(x.1,y.1) = s(x.1,y'.1) := congrArg Prod.fst heq
    have hr : y.1 = y'.1 := by
      rcases Sym2.eq_iff.mp hroles with ⟨_, hh'⟩ | ⟨h₁,h₂⟩
      · exact hh'
      · exact h₂.trans h₁
    exact Prod.ext hr (midpoint_partner_unique h x.2 y.2 y'.2 hh
      (congrArg (fun u : MidHost L R C => u.2.1) heq))

end

end GapExtremal.R434
