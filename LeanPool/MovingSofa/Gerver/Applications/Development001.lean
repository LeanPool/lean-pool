/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Classical.Foundations.Development001
public import LeanPool.MovingSofa.Convex.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001
public import LeanPool.MovingSofa.Gerver.Foundations.Development002
public import LeanPool.MovingSofa.Gerver.Foundations.Development001


/-!
# Moving sofa: related mathematical developments

* `Gerver.Area.Evaluator`.
* `Gerver.Area.CapFan`.
* `Gerver.Area.NicheCover`.
* `Gerver.Area`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Soundness of the contact evaluator

`GerverAreaCert.evalZ s z kind` evaluates one of the five phase formulas of Gerver's sofa,
and one of its four contact curves, on an interval of rotation angles.  This module proves
that it encloses the analytic value: `gerverBranch_eq` identifies the branch that the
piecewise vendor definitions `GerverSofa.Romik.path` and `GerverSofa.PartC.alphaBetaAt`
select, the five per-stage lemmas verify the phase formulas and the two velocity
coefficients against `GerverSofa.Romik.path1 … path5` and
`GerverSofa.Romik.alphaBeta1 … alphaBeta5`, and `evalZ_sound` assembles them through the
coordinate dictionary `fromPlane_paperGerverContacts`.  `contactZ_sound` and
`evalZ_interval_sound` specialise this to a grid angle and to a whole grid subinterval.
-/

/-! ### The contact evaluator -/

@[expose] public section

noncomputable section

namespace MovingSofa

open GerverAreaCert

/-- The five certified phase maps, selected by stage index. -/
def gerverBranchPath : ℕ → ℝ → GerverSofa.Point
  | 1 => GerverSofa.Romik.path1 GerverSofa.PartB.params
  | 2 => GerverSofa.Romik.path2 GerverSofa.PartB.params
  | 3 => GerverSofa.Romik.path3 GerverSofa.PartB.params
  | 4 => GerverSofa.Romik.path4 GerverSofa.PartB.params
  | _ => GerverSofa.Romik.path5 GerverSofa.PartB.params

/-- The five certified velocity-coefficient pairs, selected by stage index. -/
def gerverBranchAlphaBeta : ℕ → ℝ → GerverSofa.Point
  | 1 => GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params
  | 2 => GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params
  | 3 => GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params
  | 4 => GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params
  | _ => GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params

/-- On a grid angle of stage `s` both piecewise definitions select branch `s`. -/
theorem gerverBranch_eq (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {x : ℝ}
    (hxhi : x ≤ gerverStageTime s) (hxlo : 2 ≤ s → gerverStageTime (s - 1) < x) :
    GerverSofa.Romik.path GerverSofa.PartB.params x = gerverBranchPath s x ∧
      GerverSofa.PartC.alphaBetaAt x = gerverBranchAlphaBeta s x := by
  have o12 : GerverSofa.PartB.params.phi < GerverSofa.PartB.params.theta := by
    have := gerverStageTime_lt_succ 1 (by norm_num)
    rwa [gerverStageTime_one, gerverStageTime_two] at this
  have o23 : GerverSofa.PartB.params.theta < GerverSofa.PartC.eta := by
    have := gerverStageTime_lt_succ 2 (by norm_num)
    rwa [gerverStageTime_two, gerverStageTime_three] at this
  have o34 : GerverSofa.PartC.eta < GerverSofa.PartC.tau := by
    have := gerverStageTime_lt_succ 3 (by norm_num)
    rwa [gerverStageTime_three, gerverStageTime_four] at this
  have hpath : GerverSofa.Romik.path GerverSofa.PartB.params x =
      if x ≤ GerverSofa.PartB.params.phi then
        GerverSofa.Romik.path1 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartB.params.theta then
        GerverSofa.Romik.path2 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.eta then
        GerverSofa.Romik.path3 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.tau then
        GerverSofa.Romik.path4 GerverSofa.PartB.params x
      else GerverSofa.Romik.path5 GerverSofa.PartB.params x := rfl
  have hab : GerverSofa.PartC.alphaBetaAt x =
      if x ≤ GerverSofa.PartB.params.phi then
        GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartB.params.theta then
        GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.eta then
        GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.tau then
        GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params x
      else GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params x := rfl
  interval_cases s
  · rw [gerverStageTime_one] at hxhi
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_two] at hxhi
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := by
      have := hxlo (by norm_num)
      rw [gerverStageTime_one] at this
      exact not_le.mpr this
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_right h1, ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_three] at hxhi
    have h2 : GerverSofa.PartB.params.theta < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_two] at this
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_four] at hxhi
    have h3 : GerverSofa.PartC.eta < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_three] at this
    have h2 : GerverSofa.PartB.params.theta < x := o23.trans h3
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_left hxhi]
      rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_left hxhi]
      rfl
  · have h4 : GerverSofa.PartC.tau < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_four] at this
    have h3 : GerverSofa.PartC.eta < x := o34.trans h4
    have h2 : GerverSofa.PartB.params.theta < x := o23.trans h3
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_right (not_le.mpr h4)]
      rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_right (not_le.mpr h4)]
      rfl

/-- Transport an enclosure along an equality of the enclosed real number. -/
private theorem contains_of_eq_real {z : SI} {a b : ℝ} (hab : a = b) (h : SI.Contains z a) :
    SI.Contains z b := hab ▸ h

open SI in
/-- Stage-1 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage1_sound {z : SI} {x : ℝ}
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 1 z 0).1 (gerverBranchPath 1 x).1 ∧
      SI.Contains (evalZ 1 z 0).2 (gerverBranchPath 1 x).2 ∧
      SI.Contains (evalZ 1 z 2).1
        ((gerverBranchPath 1 x).1 - (gerverBranchAlphaBeta 1 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 1 z 2).2
        ((gerverBranchPath 1 x).2 + (gerverBranchAlphaBeta 1 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 1 z 4).1
        ((gerverBranchPath 1 x).1 - (gerverBranchAlphaBeta 1 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 1 z 4).2
        ((gerverBranchPath 1 x).2 - (gerverBranchAlphaBeta 1 x).2 * Real.sin x) := by
  obtain ⟨hk11, hk12, -, -, -, -, -, -, -, -, ha1, ha2, -⟩ := contains_params
  have hf := contains_add (contains_add (contains_mul ha1 hcos) (contains_mul ha2 hsin))
    (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hg := contains_add (contains_add (contains_mul (contains_neg ha2) hcos)
    (contains_mul ha1 hsin)) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hal := contains_add (contains_add (contains_mul (contains_imul (-2) ha1) hsin)
    (contains_mul (contains_imul 2 ha2) hcos)) (contains_ratI (a := 1) (b := 2) (by norm_num))
  have hbe := contains_add (contains_add (contains_mul (contains_imul 2 ha1) hcos)
    (contains_mul (contains_imul 2 ha2) hsin)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk11
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk12
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path1,
      GerverSofa.Romik.alphaBeta1, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-2 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage2_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 2 z 0).1 (gerverBranchPath 2 x).1 ∧
      SI.Contains (evalZ 2 z 0).2 (gerverBranchPath 2 x).2 ∧
      SI.Contains (evalZ 2 z 2).1
        ((gerverBranchPath 2 x).1 - (gerverBranchAlphaBeta 2 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 2 z 2).2
        ((gerverBranchPath 2 x).2 + (gerverBranchAlphaBeta 2 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 2 z 4).1
        ((gerverBranchPath 2 x).1 - (gerverBranchAlphaBeta 2 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 2 z 4).2
        ((gerverBranchPath 2 x).2 - (gerverBranchAlphaBeta 2 x).2 * Real.sin x) := by
  obtain ⟨-, -, hk21, hk22, -, -, -, -, -, -, -, -, hb1, hb2, -⟩ := contains_params
  have hf := contains_add (contains_add
    (contains_divn (b := 4) (by norm_num) (contains_neg (contains_mul hz hz)))
    (contains_mul hb1 hz)) hb2
  have hg := contains_add (contains_add (contains_divn (b := 2) (by norm_num) hz)
    (contains_neg hb1)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hal := contains_add (contains_add (contains_ratI (a := 1) (b := 1) (by norm_num))
    (contains_imul 2 hb1)) (contains_neg hz)
  have hbe := contains_add hf (contains_ratI (a := 1) (b := 2) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk21
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk22
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path2,
      GerverSofa.Romik.alphaBeta2, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-3 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage3_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 3 z 0).1 (gerverBranchPath 3 x).1 ∧
      SI.Contains (evalZ 3 z 0).2 (gerverBranchPath 3 x).2 ∧
      SI.Contains (evalZ 3 z 2).1
        ((gerverBranchPath 3 x).1 - (gerverBranchAlphaBeta 3 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 3 z 2).2
        ((gerverBranchPath 3 x).2 + (gerverBranchAlphaBeta 3 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 3 z 4).1
        ((gerverBranchPath 3 x).1 - (gerverBranchAlphaBeta 3 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 3 z 4).2
        ((gerverBranchPath 3 x).2 - (gerverBranchAlphaBeta 3 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, hk31, hk32, -, -, -, -, -, -, -, -, hc1, hc2, -⟩ := contains_params
  have hf := contains_sub hc1 hz
  have hg := contains_add hc2 hz
  have hal := contains_add (contains_ratI (a := -1) (b := 1) (by norm_num)) (contains_neg hg)
  have hbe := contains_add (contains_ratI (a := 1) (b := 1) (by norm_num)) hf
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk31
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk32
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
    simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path3,
      GerverSofa.Romik.alphaBeta3, GerverSofa.Romik.addK, GerverSofa.Romik.rot] <;>
    push_cast <;> ring

open SI in
/-- Stage-4 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage4_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 4 z 0).1 (gerverBranchPath 4 x).1 ∧
      SI.Contains (evalZ 4 z 0).2 (gerverBranchPath 4 x).2 ∧
      SI.Contains (evalZ 4 z 2).1
        ((gerverBranchPath 4 x).1 - (gerverBranchAlphaBeta 4 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 4 z 2).2
        ((gerverBranchPath 4 x).2 + (gerverBranchAlphaBeta 4 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 4 z 4).1
        ((gerverBranchPath 4 x).1 - (gerverBranchAlphaBeta 4 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 4 z 4).2
        ((gerverBranchPath 4 x).2 - (gerverBranchAlphaBeta 4 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, -, -, hk41, hk42, -, -, -, -, -, -, -, -, hd1, hd2, -⟩ := contains_params
  have hf := contains_add (contains_add
    (contains_neg (contains_divn (b := 2) (by norm_num) hz)) hd1)
    (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hg := contains_add (contains_add
    (contains_divn (b := 4) (by norm_num) (contains_neg (contains_mul hz hz)))
    (contains_mul hd1 hz)) hd2
  have hal := contains_add (contains_neg hg) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hbe := contains_add (contains_add (contains_imul 2 hd1)
    (contains_ratI (a := -1) (b := 1) (by norm_num))) (contains_neg hz)
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk41
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk42
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path4,
      GerverSofa.Romik.alphaBeta4, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-5 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage5_sound {z : SI} {x : ℝ}
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 5 z 0).1 (gerverBranchPath 5 x).1 ∧
      SI.Contains (evalZ 5 z 0).2 (gerverBranchPath 5 x).2 ∧
      SI.Contains (evalZ 5 z 2).1
        ((gerverBranchPath 5 x).1 - (gerverBranchAlphaBeta 5 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 5 z 2).2
        ((gerverBranchPath 5 x).2 + (gerverBranchAlphaBeta 5 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 5 z 4).1
        ((gerverBranchPath 5 x).1 - (gerverBranchAlphaBeta 5 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 5 z 4).2
        ((gerverBranchPath 5 x).2 - (gerverBranchAlphaBeta 5 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, -, -, -, -, hk51, hk52, -, -, -, -, -, -, -, -, he1, he2, -⟩ :=
    contains_params
  have hf := contains_add (contains_add (contains_mul he1 hcos) (contains_mul he2 hsin))
    (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hg := contains_add (contains_add (contains_mul (contains_neg he2) hcos)
    (contains_mul he1 hsin)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hal := contains_add (contains_add (contains_ratI (a := 1) (b := 1) (by norm_num))
    (contains_mul (contains_imul (-2) he1) hsin)) (contains_mul (contains_imul 2 he2) hcos)
  have hbe := contains_add (contains_add (contains_mul (contains_imul 2 he1) hcos)
    (contains_mul (contains_imul 2 he2) hsin)) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk51
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk52
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path5,
      GerverSofa.Romik.alphaBeta5, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

/-- Per-stage soundness of the phase-map evaluation, i.e. of the `kind = 0` output.
Pure interval arithmetic against `GerverSofa.Romik.path1 … path5`: five cases, each a chain
of `SI.contains_*` applications on top of `contains_params`, `hsin` and `hcos`. -/
theorem evalZ_zero_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ s z 0).1 (gerverBranchPath s x).1 ∧
      SI.Contains (evalZ s z 0).2 (gerverBranchPath s x).2 := by
  interval_cases s
  · exact ⟨(evalZ_stage1_sound hsin hcos).1, (evalZ_stage1_sound hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage2_sound hz hsin hcos).1, (evalZ_stage2_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage3_sound hz hsin hcos).1, (evalZ_stage3_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage4_sound hz hsin hcos).1, (evalZ_stage4_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage5_sound hsin hcos).1, (evalZ_stage5_sound hsin hcos).2.1⟩

/-- Per-stage soundness of the `B` and `D` offsets, i.e. of the two velocity
coefficients `α` and `β` against `GerverSofa.Romik.alphaBeta1 … alphaBeta5`.  Note
`evalZ s z 1 = evalZ s z 2` shifted by `(cos x, sin x)` and
`evalZ s z 3 = evalZ s z 4` shifted by `(-sin x, cos x)`, so the remaining two kinds need no
separate stage analysis. -/
theorem evalZ_offset_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ s z 2).1
        ((gerverBranchPath s x).1 - (gerverBranchAlphaBeta s x).1 * Real.sin x) ∧
      SI.Contains (evalZ s z 2).2
        ((gerverBranchPath s x).2 + (gerverBranchAlphaBeta s x).1 * Real.cos x) ∧
      SI.Contains (evalZ s z 4).1
        ((gerverBranchPath s x).1 - (gerverBranchAlphaBeta s x).2 * Real.cos x) ∧
      SI.Contains (evalZ s z 4).2
        ((gerverBranchPath s x).2 - (gerverBranchAlphaBeta s x).2 * Real.sin x) := by
  interval_cases s
  · exact (evalZ_stage1_sound hsin hcos).2.2
  · exact (evalZ_stage2_sound hz hsin hcos).2.2
  · exact (evalZ_stage3_sound hz hsin hcos).2.2
  · exact (evalZ_stage4_sound hz hsin hcos).2.2
  · exact (evalZ_stage5_sound hsin hcos).2.2

/-- Soundness of the executable phase/contact evaluator: on the branch that the
piecewise definitions select, the interval evaluation encloses both coordinates of the
selected curve.  Reduces to `gerverBranch_eq`, `evalZ_zero_sound`, `evalZ_offset_sound`,
`trigZ_sound` and the coordinate dictionary
`fromPlane_paperGerverContacts` (`GerverSofa.u t = (cos t, sin t)`,
`GerverSofa.v t = (-sin t, cos t)`). -/
theorem evalZ_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hx0 : 0 ≤ x) (hxT : x ≤ Real.pi / 2)
    (hxhi : x ≤ gerverStageTime s) (hxlo : 2 ≤ s → gerverStageTime (s - 1) < x)
    (kind : ℕ) (hk : kind ≤ 4) :
    SI.Contains (evalZ s z kind).1 (gerverContactPoint kind x 0) ∧
      SI.Contains (evalZ s z kind).2 (gerverContactPoint kind x 1) := by
  have hx2 : x ≤ 2 := by linarith [Real.pi_lt_d2]
  obtain ⟨hsin, hcos⟩ := trigZ_sound hz hx0 hx2
  obtain ⟨hp, hab⟩ := gerverBranch_eq s hs1 hs5 hxhi hxlo
  obtain ⟨h0x, h0y⟩ := evalZ_zero_sound s hs1 hs5 hz hsin hcos
  obtain ⟨h2x, h2y, h4x, h4y⟩ := evalZ_offset_sound s hs1 hs5 hz hsin hcos
  have ht : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx0, hxT⟩
  -- The four contact curves in terms of the branch phase map and coefficients.
  set P : ℝ × ℝ := gerverBranchPath s x with hPdef
  set AB : ℝ × ℝ := gerverBranchAlphaBeta s x with hABdef
  have hpath1 : (GerverSofa.Romik.path GerverSofa.PartB.params x).1 = P.1 := by rw [hp]
  have hpath2 : (GerverSofa.Romik.path GerverSofa.PartB.params x).2 = P.2 := by rw [hp]
  have hal : (GerverSofa.PartC.alphaBetaAt x).1 = AB.1 := by rw [hab]
  have hbe : (GerverSofa.PartC.alphaBetaAt x).2 = AB.2 := by rw [hab]
  have hdA1 : gerverContactPoint 1 x 0 = P.1 - AB.1 * Real.sin x + Real.cos x := by
    have h' : gerverContactPoint 1 x 0 = (GerverSofa.PartC.A x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 0)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).1 + (GerverSofa.u x).1 = _
    rw [hpath1, hal]
    show P.1 + AB.1 * (-Real.sin x) + Real.cos x = _
    ring
  have hdA2 : gerverContactPoint 1 x 1 = P.2 + AB.1 * Real.cos x + Real.sin x := by
    have h' : gerverContactPoint 1 x 1 = (GerverSofa.PartC.A x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 0)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).2 + (GerverSofa.u x).2 = _
    rw [hpath2, hal]
    show P.2 + AB.1 * Real.cos x + Real.sin x = _
    ring
  have hdB1 : gerverContactPoint 2 x 0 = P.1 - AB.1 * Real.sin x := by
    have h' : gerverContactPoint 2 x 0 = (GerverSofa.PartC.B x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 1)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).1 = _
    rw [hpath1, hal]
    show P.1 + AB.1 * (-Real.sin x) = _
    ring
  have hdB2 : gerverContactPoint 2 x 1 = P.2 + AB.1 * Real.cos x := by
    have h' : gerverContactPoint 2 x 1 = (GerverSofa.PartC.B x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 1)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).2 = _
    rw [hpath2, hal]
    rfl
  have hdC1 : gerverContactPoint 3 x 0 = P.1 - AB.2 * Real.cos x - Real.sin x := by
    have h' : gerverContactPoint 3 x 0 = (GerverSofa.PartC.C x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 2)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).1 + (GerverSofa.v x).1 = _
    rw [hpath1, hbe]
    show P.1 - AB.2 * Real.cos x + -Real.sin x = _
    ring
  have hdC2 : gerverContactPoint 3 x 1 = P.2 - AB.2 * Real.sin x + Real.cos x := by
    have h' : gerverContactPoint 3 x 1 = (GerverSofa.PartC.C x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 2)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).2 + (GerverSofa.v x).2 = _
    rw [hpath2, hbe]
    rfl
  have hdD1 : gerverContactPoint 4 x 0 = P.1 - AB.2 * Real.cos x := by
    have h' : gerverContactPoint 4 x 0 = (GerverSofa.PartC.D x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 3)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).1 = _
    rw [hpath1, hbe]
    rfl
  have hdD2 : gerverContactPoint 4 x 1 = P.2 - AB.2 * Real.sin x := by
    have h' : gerverContactPoint 4 x 1 = (GerverSofa.PartC.D x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 3)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).2 = _
    rw [hpath2, hbe]
    rfl
  have hd01 : gerverContactPoint 0 x 0 = P.1 := hpath1
  have hd02 : gerverContactPoint 0 x 1 = P.2 := hpath2
  -- The `A` and `C` outputs are the `B` and `D` outputs shifted by the frame vectors.
  have eA1 : (evalZ s z 1).1 = SI.add (evalZ s z 2).1 (trigZ z).2 := rfl
  have eA2 : (evalZ s z 1).2 = SI.add (evalZ s z 2).2 (trigZ z).1 := rfl
  have eC1 : (evalZ s z 3).1 = SI.sub (evalZ s z 4).1 (trigZ z).1 := rfl
  have eC2 : (evalZ s z 3).2 = SI.add (evalZ s z 4).2 (trigZ z).2 := rfl
  interval_cases kind
  · exact ⟨hd01 ▸ h0x, hd02 ▸ h0y⟩
  · refine ⟨?_, ?_⟩
    · rw [hdA1, eA1]
      exact SI.contains_add h2x hcos
    · rw [hdA2, eA2]
      exact SI.contains_add h2y hsin
  · exact ⟨hdB1 ▸ h2x, hdB2 ▸ h2y⟩
  · refine ⟨?_, ?_⟩
    · rw [hdC1, eC1]
      exact SI.contains_sub h4x hsin
    · rw [hdC2, eC2]
      exact SI.contains_add h4y hcos
  · exact ⟨hdD1 ▸ h4x, hdD2 ▸ h4y⟩

/-- The left endpoint of the branch selected at the right end of a grid subinterval
does not exceed the left end of that subinterval. -/
theorem stageTime_pred_le_gerverGridTime (m : ℕ) (hm : m + 1 ≤ 5 * NN)
    (h2 : 2 ≤ stageOf (m + 1)) :
    gerverStageTime (stageOf (m + 1) - 1) ≤ gerverGridTime m := by
  have hNN : 0 < NN := by norm_num [NN]
  rw [stageOf] at h2 ⊢
  split_ifs at h2 ⊢ with h
  · have hd : 2 ≤ (m + 1) / NN := by
      rcases le_max_iff.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hk : (m + 1) / NN * NN = m + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have hstep : ((m + 1) / NN - 1) * NN = m + 1 - NN := by rw [Nat.sub_one_mul, hk]
    have hle : ((m + 1) / NN - 1) * NN ≤ m := by rw [hstep]; omega
    rw [max_eq_right (Nat.le_of_succ_le hd), ← gerverGridTime_mul_NN ((m + 1) / NN - 1)]
    exact gerverGridTime_le_of_le hle (by omega)
  · rw [Nat.add_sub_cancel]
    have hle1 : (m + 1) / NN * NN ≤ m + 1 := Nat.div_mul_le_self (m + 1) NN
    have hne : (m + 1) / NN * NN ≠ m + 1 := by
      intro he
      exact h (by rw [← he]; exact Nat.mul_mod_left _ _)
    have hle : (m + 1) / NN * NN ≤ m := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle1 hne)
    rw [← gerverGridTime_mul_NN ((m + 1) / NN)]
    exact gerverGridTime_le_of_le hle (by omega)

/-- The evaluator at a grid angle. -/
theorem contactZ_sound (m : ℕ) (hm : m ≤ 5 * NN) (kind : ℕ) (hk : kind ≤ 4) :
    SI.Contains (contactZ m kind).1 (gerverContactPoint kind (gerverGridTime m) 0) ∧
      SI.Contains (contactZ m kind).2 (gerverContactPoint kind (gerverGridTime m) 1) := by
  obtain ⟨h1, h5⟩ := stageOf_mem m hm
  obtain ⟨hg0, hgT⟩ := gerverGridTime_mem_Icc m hm
  exact evalZ_sound (stageOf m) h1 h5 (ttZ_sound m hm) hg0 hgT
    (gerverGridTime_le_stageTime m hm) (fun h ↦ stageTime_lt_gerverGridTime m hm h) kind hk

/-- The evaluator over a whole grid subinterval, on the branch selected at its right
endpoint (which is the branch of every angle in the half-open subinterval). -/
theorem evalZ_interval_sound (m : ℕ) (hm : m + 1 ≤ 5 * NN) (kind : ℕ) (hk : kind ≤ 4)
    {x : ℝ} (hx : x ∈ Set.Ioc (gerverGridTime m) (gerverGridTime (m + 1))) :
    SI.Contains (evalZ (stageOf (m + 1))
        ⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ kind).1 (gerverContactPoint kind x 0) ∧
      SI.Contains (evalZ (stageOf (m + 1))
        ⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ kind).2 (gerverContactPoint kind x 1) := by
  have hmm : m ≤ 5 * NN := by omega
  obtain ⟨hxl, hxr⟩ := hx
  obtain ⟨h1, h5⟩ := stageOf_mem (m + 1) hm
  obtain ⟨hg0, -⟩ := gerverGridTime_mem_Icc m hmm
  obtain ⟨-, hgT⟩ := gerverGridTime_mem_Icc (m + 1) hm
  have hM := SI.Mpos
  have hz : SI.Contains (⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ : SI) x := by
    obtain ⟨ha, -⟩ := ttZ_sound m hmm
    obtain ⟨-, hb⟩ := ttZ_sound (m + 1) hm
    exact ⟨ha.trans (mul_le_mul_of_nonneg_left hxl.le hM.le),
      (mul_le_mul_of_nonneg_left hxr hM.le).trans hb⟩
  refine evalZ_sound (stageOf (m + 1)) h1 h5 hz (hg0.trans hxl.le) (hxr.trans hgT)
    (hxr.trans (gerverGridTime_le_stageTime (m + 1) hm)) (fun h2 ↦ ?_) kind hk
  exact lt_of_le_of_lt (stageTime_pred_le_gerverGridTime m hm h2) hxl

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The support-contact fan of the Gerver outer cap

The literal Gerver outer cap is a compact convex subset of the plane lying in the closed
quadrant above the fan anchor `L = C (π / 2)`, which sits on the wall.  The `640` listed
contacts `A (t)` and `C (t)` at the grid angles attain the cap support at the strictly
increasing normals `t` and `t + π / 2` of `[0, π)`, so `supportContact_fan_area` bounds the
cap area below by half the shoelace sum of the fan over the anchor.  The certificate
encloses that sum (`capDoubledZ_sound`), and its kernel-checked numeric conclusion
`GerverAreaCert.capOK_true` turns the enclosure into `28609 / 10000 ≤ |K₀|`.
-/

/-! ### Elementary geometry of the outer cap -/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open GerverAreaCert

/-- The paper path starts at the origin. -/
theorem paperGerverPath_zero : paperGerverPath 0 = 0 := by
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  show GerverSofa.PartF.Coordinates.toPlane
    (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
  rw [hreg.2.1]
  ext i
  fin_cases i <;> rfl

/-- The outer cap written as an intersection of closed half-planes. -/
theorem gerverOuterCap_eq_iInter :
    gerverOuterCap =
      {q : Point | 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} ∩
        ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          ({q : Point | inner ℝ q (normalVector (t : Real.Angle)) ≤
              inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1} ∩
            {q : Point | inner ℝ q (tangentVector (t : Real.Angle)) ≤
              inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1}) := by
  ext q
  simp only [gerverOuterCap, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter₂,
    inner_normalVector_pi_div_two]

/-- The outer cap is closed, being an intersection of closed half-spaces. -/
theorem isClosed_gerverOuterCap : IsClosed gerverOuterCap := by
  rw [gerverOuterCap_eq_iInter]
  refine IsClosed.inter (isClosed_le continuous_const
    (continuous_id.inner continuous_const)) ?_
  exact isClosed_biInter fun t _ ↦ IsClosed.inter
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)

/-- The outer cap is convex, being an intersection of half-spaces. -/
theorem convex_gerverOuterCap : Convex ℝ gerverOuterCap := by
  rw [gerverOuterCap_eq_iInter]
  refine Convex.inter (convex_halfSpace_ge (isLinearMap_inner_left _) 0) ?_
  exact convex_iInter₂ fun t _ ↦ Convex.inter
    (convex_halfSpace_le (isLinearMap_inner_left _) _)
    (convex_halfSpace_le (isLinearMap_inner_left _) _)

/-- The outer cap is contained in an explicit coordinate rectangle. -/
theorem gerverOuterCap_subset_box :
    gerverOuterCap ⊆ {p : Point |
      p 0 ∈ Set.Icc (-(inner ℝ (paperGerverPath (Real.pi / 2))
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1)) 1 ∧ p 1 ∈ Set.Icc 0 1} := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  intro q hq
  obtain ⟨hy, hcap⟩ := hq
  have h0 := hcap 0 ⟨le_rfl, hTpos.le⟩
  have hT := hcap (Real.pi / 2) ⟨hTpos.le, le_rfl⟩
  rw [paperGerverPath_zero, inner_normalVector_zero, inner_normalVector_zero,
    inner_tangentVector_zero, inner_tangentVector_zero] at h0
  refine ⟨⟨?_, ?_⟩, hy, ?_⟩
  · have h := hT.2
    rw [inner_tangentVector_pi_div_two] at h
    linarith
  · have h := h0.1
    simpa using h
  · have h := h0.2
    simpa using h

/-- The outer cap is compact: it is closed and contained in a coordinate rectangle. -/
theorem isCompact_gerverOuterCap : IsCompact gerverOuterCap := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_gerverOuterCap ?_
  set c : ℝ := -(inner ℝ (paperGerverPath (Real.pi / 2))
    (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1) with hc
  set K : ℝ := |c| + 1 with hK
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 * K, fun q hq ↦ ?_⟩
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := gerverOuterCap_subset_box hq
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; linarith [abs_nonneg c]
  have hsq : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two, sq_abs]
  have hx : |q 0| ≤ K := by
    rw [abs_le]
    refine ⟨?_, by rw [hK]; linarith [abs_nonneg c]⟩
    have hcle : -|c| ≤ c := neg_abs_le c
    rw [hK]
    linarith [hx0]
  have hy : |q 1| ≤ K := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hx2 : q 0 ^ 2 ≤ K ^ 2 := by nlinarith [sq_abs (q 0), abs_nonneg (q 0)]
  have hy2 : q 1 ^ 2 ≤ K ^ 2 := by nlinarith [sq_abs (q 1), abs_nonneg (q 1)]
  nlinarith [norm_nonneg q, hsq, hx2, hy2, hK1]

/-- The outer cap is Borel measurable. -/
theorem measurableSet_gerverOuterCap : MeasurableSet gerverOuterCap :=
  isClosed_gerverOuterCap.measurableSet

/-- The outer cap has finite planar volume. -/
theorem volume_gerverOuterCap_lt_top : volume gerverOuterCap < ⊤ :=
  isCompact_gerverOuterCap.measure_lt_top

/-! ### The support-contact fan and the cap lower bound -/

/-- The fan anchor `L = C (π / 2)`. -/
def gerverFanAnchor : Point := paperGerverContacts (Real.pi / 2) 2

/-- The `i`-th listed support contact, `i < fanCount`. -/
def gerverFanPoint (i : ℕ) : Point :=
  gerverContactPoint (fanKind i) (gerverGridTime (fanIdx i))

/-- The support normal of the `i`-th listed contact. -/
def gerverFanNormal (i : ℕ) : ℝ :=
  if i ≤ 5 * NN then gerverGridTime i else gerverGridTime (i - 5 * NN) + Real.pi / 2

/-- The support value of the first outer contact in its own normal direction. -/
private theorem inner_paperGerverContacts_zero_normalVector (t : ℝ) :
    inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 := by
  show inner ℝ (paperGerverPath t +
    (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle) +
      normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_add_left, real_inner_smul_left,
    inner_tangentVector_normalVector_real, inner_normalVector_self]
  simp

/-- The support value of the third outer contact in the rotated normal direction. -/
private theorem inner_paperGerverContacts_two_tangentVector (t : ℝ) :
    inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
  show inner ℝ (paperGerverPath t -
    (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle) +
      tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_normalVector_tangentVector, inner_tangentVector_self]
  ring

/-- `A t` attains the cap support at normal `t`. -/
theorem gerverOuterCap_support_A (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    {q : Point} (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) := by
  rw [inner_paperGerverContacts_zero_normalVector]
  exact (hq.2 t ht).1

/-- `C t` attains the cap support at normal `t + π / 2`. -/
theorem gerverOuterCap_support_C (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    {q : Point} (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ (paperGerverContacts t 2) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  rw [normalVector_add_pi_div_two_real, inner_paperGerverContacts_two_tangentVector]
  exact (hq.2 t ht).2

/-- The anchor sits on the wall. -/
theorem gerverFanAnchor_snd : gerverFanAnchor 1 = 0 := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  have h := congrArg Prod.snd (fromPlane_paperGerverContacts (Real.pi / 2) hT 2)
  have hC : (GerverSofa.PartC.C (Real.pi / 2)).2 = 0 :=
    GerverSofa.PartC.Stage2.C_T_snd_zero
  show (GerverSofa.PartF.Coordinates.fromPlane (paperGerverContacts (Real.pi / 2) 2)).2 = 0
  rw [h]
  simpa using hC

/-- The cap lies in the closed quadrant above the anchor. -/
theorem gerverOuterCap_quadrant {q : Point} (hq : q ∈ gerverOuterCap) :
    gerverFanAnchor 0 ≤ q 0 ∧ 0 ≤ q 1 := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  refine ⟨?_, hq.1⟩
  have h := gerverOuterCap_support_C (Real.pi / 2) hT hq
  have hsplit : (Real.pi / 2 + Real.pi / 2 : ℝ) = 0 + Real.pi := by ring
  rw [hsplit, normalVector_add_pi, inner_neg_right, inner_neg_right,
    inner_normalVector_zero, inner_normalVector_zero] at h
  show gerverFanAnchor 0 ≤ q 0
  simp only [gerverFanAnchor]
  linarith

/-- The listed support normals are strictly increasing. -/
theorem gerverFanNormal_lt_succ (i : ℕ) (hi : i + 1 < fanCount) :
    gerverFanNormal i < gerverFanNormal (i + 1) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanNormal]
  split_ifs with h1 h2
  · exact gerverGridTime_lt_succ i (by omega)
  · have hi5 : i = 5 * NN := by omega
    subst hi5
    rw [Nat.add_sub_cancel_left, gerverGridTime_top]
    have h0 : gerverGridTime 0 < gerverGridTime 1 := gerverGridTime_lt_succ 0 (by omega)
    rw [gerverGridTime_zero] at h0
    linarith
  · omega
  · have hrw : i + 1 - 5 * NN = (i - 5 * NN) + 1 := by omega
    rw [hrw]
    have h := gerverGridTime_lt_succ (i - 5 * NN) (by omega)
    linarith

/-- The listed support normals lie in `[0, π)`. -/
theorem gerverFanNormal_mem_Ico (i : ℕ) (hi : i < fanCount) :
    0 ≤ gerverFanNormal i ∧ gerverFanNormal i < Real.pi := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  simp only [gerverFanNormal]
  split_ifs with h1
  · obtain ⟨hlo, hhi⟩ := gerverGridTime_mem_Icc i h1
    exact ⟨hlo, by linarith⟩
  · have hlt : i - 5 * NN < 5 * NN := by omega
    have hstrict := gerverGridTime_lt_of_lt hlt le_rfl
    rw [gerverGridTime_top] at hstrict
    obtain ⟨hlo, -⟩ := gerverGridTime_mem_Icc (i - 5 * NN) hlt.le
    exact ⟨by linarith, by linarith⟩

/-- The `kind = 1` slot of the contact dictionary is the first outer contact. -/
private theorem gerverContactPoint_one (x : ℝ) :
    gerverContactPoint 1 x = paperGerverContacts x 0 := rfl

/-- The `kind = 3` slot of the contact dictionary is the third outer contact. -/
private theorem gerverContactPoint_three (x : ℝ) :
    gerverContactPoint 3 x = paperGerverContacts x 2 := rfl

/-- Every listed contact lies in the cap. -/
theorem gerverFanPoint_mem (i : ℕ) (hi : i < fanCount) :
    gerverFanPoint i ∈ gerverOuterCap := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanPoint, fanKind, fanIdx]
  split_ifs with h1
  · rw [gerverContactPoint_one]
    exact gerver_outer_contact_A _ (gerverGridTime_mem_Icc i h1)
  · rw [gerverContactPoint_three]
    exact gerver_outer_contact_C _ (gerverGridTime_mem_Icc (i - 5 * NN) (by omega))

/-- Every listed contact attains the cap support at its listed normal. -/
theorem gerverFanPoint_support (i : ℕ) (hi : i < fanCount) {q : Point}
    (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector (gerverFanNormal i : Real.Angle)) ≤
      inner ℝ (gerverFanPoint i) (normalVector (gerverFanNormal i : Real.Angle)) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanPoint, gerverFanNormal, fanKind, fanIdx]
  split_ifs with h1
  · rw [gerverContactPoint_one]
    exact gerverOuterCap_support_A _ (gerverGridTime_mem_Icc i h1) hq
  · rw [gerverContactPoint_three]
    exact gerverOuterCap_support_C _ (gerverGridTime_mem_Icc (i - 5 * NN) (by omega)) hq

/-- The certificate encloses both coordinates of every listed fan contact. -/
private theorem fanZ_sound (i : ℕ) (hi : i < fanCount) :
    SI.Contains (fanZ i).1 (gerverFanPoint i 0) ∧
      SI.Contains (fanZ i).2 (gerverFanPoint i 1) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  have hidx : fanIdx i ≤ 5 * NN := by
    simp only [fanIdx]
    split_ifs with h <;> omega
  have hkind : fanKind i ≤ 4 := by
    simp only [fanKind]
    split_ifs <;> norm_num
  exact contactZ_sound (fanIdx i) hidx (fanKind i) hkind

/-- The certificate encloses both coordinates of the fan anchor. -/
private theorem anchorZ_sound :
    SI.Contains anchorZ.1 (gerverFanAnchor 0) ∧ SI.Contains anchorZ.2 (gerverFanAnchor 1) := by
  have h := contactZ_sound (5 * NN) le_rfl 3 (by norm_num)
  rwa [gerverGridTime_top] at h

/-- The certificate encloses the fan shoelace sum. -/
theorem capDoubledZ_sound :
    SI.Contains capDoubledZ (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) := by
  have hNN : NN = 64 := rfl
  refine SI.contains_foldl_range (fanCount - 1) fun i hi => ?_
  simp only [fanCount] at hi
  obtain ⟨ha1, ha2⟩ := fanZ_sound i (by simp only [fanCount]; omega)
  obtain ⟨hb1, hb2⟩ := fanZ_sound (i + 1) (by simp only [fanCount]; omega)
  obtain ⟨hL1, hL2⟩ := anchorZ_sound
  have hcross : planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
      (gerverFanPoint (i + 1) - gerverFanAnchor) =
      (gerverFanPoint i 0 - gerverFanAnchor 0) *
          (gerverFanPoint (i + 1) 1 - gerverFanAnchor 1) -
        (gerverFanPoint i 1 - gerverFanAnchor 1) *
          (gerverFanPoint (i + 1) 0 - gerverFanAnchor 0) := by
    simp [planeCrossProduct]
  rw [hcross]
  exact SI.contains_sub
    (SI.contains_mul (SI.contains_sub ha1 hL1) (SI.contains_sub hb2 hL2))
    (SI.contains_mul (SI.contains_sub ha2 hL2) (SI.contains_sub hb1 hL1))

/-- The cap area lower bound. -/
theorem gerverOuterCap_area_certified_lower_bound :
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap := by
  have hNN : NN = 64 := rfl
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcount : fanCount = 640 := rfl
  -- The fan data on `Fin 640`.
  have hlt : ∀ i : Fin 640, (i : ℕ) < fanCount := fun i => by
    rw [hcount]; exact i.isLt
  have hmono : StrictMono fun i : Fin 640 => gerverFanNormal (i : ℕ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    simpa using gerverFanNormal_lt_succ (i : ℕ) (by rw [hcount]; omega)
  obtain ⟨-, hfan⟩ := supportContact_fan_area gerverOuterCap
    isCompact_gerverOuterCap convex_gerverOuterCap gerverFanAnchor
    (gerver_outer_contact_C (Real.pi / 2) ⟨hTpos.le, le_rfl⟩)
    gerverFanAnchor_snd (fun _ hq => gerverOuterCap_quadrant hq) 639
    (fun i : Fin 640 => gerverFanNormal (i : ℕ)) hmono
    (fun i => gerverFanNormal_mem_Ico (i : ℕ) (hlt i))
    (fun i : Fin 640 => gerverFanPoint (i : ℕ)) (fun i => gerverFanPoint_mem (i : ℕ) (hlt i))
    (fun i q hq => gerverFanPoint_support (i : ℕ) (hlt i) hq)
  -- Identify the `Fin`-indexed fan sum with the certificate's range sum.
  rw [show (∑ i : Fin 639, planeCrossProduct
        (gerverFanPoint (i.castSucc : Fin 640) - gerverFanAnchor)
        (gerverFanPoint (i.succ : Fin 640) - gerverFanAnchor)) =
      ∑ i ∈ Finset.range (fanCount - 1),
        planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
          (gerverFanPoint (i + 1) - gerverFanAnchor) by
    rw [hcount]
    exact Fin.sum_univ_eq_sum_range (fun i => planeCrossProduct
      (gerverFanPoint i - gerverFanAnchor) (gerverFanPoint (i + 1) - gerverFanAnchor)) 639] at hfan
  -- The kernel-checked numeric inequality.  The fan sum and the certificate endpoint are
  -- abstracted into local variables first, and the arithmetic tactics are used in their
  -- `only` form, so that no tactic ever tries to evaluate the 639-term fold.
  obtain ⟨S, hS⟩ : ∃ S : ℝ, (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) = S := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, capDoubledZ.lo = z := ⟨_, rfl⟩
  obtain ⟨hlo, -⟩ := capDoubledZ_sound
  rw [hS] at hfan
  rw [hS, hz] at hlo
  have hOK : 2 * 28609 * M ≤ 10000 * capDoubledZ.lo := by
    have h := capOK_true
    unfold capOK at h
    exact of_decide_eq_true h
  rw [hz] at hOK
  have hOK' : (2 * 28609 * (M : ℝ)) ≤ 10000 * (z : ℝ) := by exact_mod_cast hOK
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hkey : 2 * 28609 ≤ 10000 * S := by nlinarith only [hlo, hOK', hM]
  refine le_trans ?_ hfan
  linarith only [hkey]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The rectangle cover of the literal Gerver niche

The literal niche is the union of the strict vertical fills under the three pieces of its
roof (`gerver_niche_vertical_fills`).  Each piece is traversed with monotone horizontal
coordinate, so subdividing the seven monotone roof stretches at the grid angles covers the
niche by `7 * NN` coordinate rectangles whose widths and heights the certificate encloses
(`gerverNicheRect_covers`).  The kernel-checked numeric conclusion
`GerverAreaCert.nicheOK_true` bounds the total rectangle area, hence `|N₀| ≤ 3301 / 5000`.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory
open GerverAreaCert

/-- The literal niche is Borel measurable: it is a closed half-plane intersected with a
countable union of open sets. -/
theorem measurableSet_gerverLiteralNiche : MeasurableSet gerverLiteralNiche := by
  have h : gerverLiteralNiche =
      {q : Point | 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} ∩
        ⋃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ({q : Point | inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0} ∩
            {q : Point |
              inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0}) := by
    ext q
    simp only [gerverLiteralNiche, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion₂,
      inner_normalVector_pi_div_two]
    tauto
  rw [h]
  refine MeasurableSet.inter
    ((isClosed_le continuous_const (continuous_id.inner continuous_const)).measurableSet) ?_
  refine IsOpen.measurableSet (isOpen_biUnion fun t _ ↦ IsOpen.inter ?_ ?_)
  · exact isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const
  · exact isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const

/-! ### The rectangle cover and the niche upper bound -/

/-- The covering rectangle of the `j`-th subinterval of roof piece `r`. -/
def gerverNicheRect (r j : ℕ) : Set Point :=
  {p : Point | p 0 ∈ Set.Icc (((rectLoZ r j : ℤ) : ℝ) / (M : ℝ))
      (((rectHiZ r j : ℤ) : ℝ) / (M : ℝ)) ∧
    p 1 ∈ Set.Icc 0 (((rectHZ r j : ℤ) : ℝ) / (M : ℝ))}

/-- A strict vertical fill splits along a subdivision of its parameter interval. -/
theorem strictVerticalFill_Icc_union {f : ℝ → Point} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    strictVerticalFill f (Set.Icc a c) =
      strictVerticalFill f (Set.Icc a b) ∪ strictVerticalFill f (Set.Icc b c) := by
  ext q
  simp only [strictVerticalFill, Set.mem_ofPred_eq, Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    rcases le_total t b with h | h
    · exact Or.inl ⟨t, ⟨h1, h⟩, h3⟩
    · exact Or.inr ⟨t, ⟨h, h2⟩, h3⟩
  · rintro (⟨t, ⟨h1, h2⟩, h3⟩ | ⟨t, ⟨h1, h2⟩, h3⟩)
    · exact ⟨t, ⟨h1, h2.trans hbc⟩, h3⟩
    · exact ⟨t, ⟨hab.trans h1, h2⟩, h3⟩

/-- The strictly increasing chain of the six `ℕ`-indexed stage endpoints. -/
private theorem gerverStageTime_chain :
    gerverStageTime 0 = 0 ∧ gerverStageTime 0 < gerverStageTime 1 ∧
      gerverStageTime 1 < gerverStageTime 2 ∧ gerverStageTime 2 < gerverStageTime 3 ∧
      gerverStageTime 3 < gerverStageTime 4 ∧ gerverStageTime 4 < gerverStageTime 5 ∧
      gerverStageTime 5 = Real.pi / 2 :=
  ⟨gerverStageTime_zero, gerverStageTime_lt_succ 0 (by norm_num),
    gerverStageTime_lt_succ 1 (by norm_num), gerverStageTime_lt_succ 2 (by norm_num),
    gerverStageTime_lt_succ 3 (by norm_num), gerverStageTime_lt_succ 4 (by norm_num),
    gerverStageTime_five⟩

/-- `gerverRoofReverseTime` written in the `ℕ`-indexed stage endpoints. -/
private theorem gerverRoofReverseTime_eq_stageTime (s : ℝ) :
    gerverRoofReverseTime s = gerverStageTime 4 -
      (gerverStageTime 4 - gerverStageTime 1) / (gerverStageTime 3 - gerverStageTime 2) *
        (s - gerverStageTime 2) := rfl

/-- The first roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_D {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : s ≤ gerverStageTime 2) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 3 :=
  gerverNicheRoof_of_le_two hs h

/-- The middle roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h2 : gerverStageTime 2 ≤ s) (h3 : s ≤ gerverStageTime 3) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverPath (gerverRoofReverseTime s) :=
  gerverNicheRoof_mid hs h2 h3

/-- The last roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_B {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h3 : gerverStageTime 3 ≤ s) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 1 :=
  gerverNicheRoof_of_ge_three hs h3

/-- Two roof arguments compare as their underlying reals. -/
private theorem gerverNicheRoof_fst_le_of_le {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) (hab : a ≤ b) :
    gerverNicheRoof ⟨a, ha⟩ 0 ≤ gerverNicheRoof ⟨b, hb⟩ 0 :=
  gerver_niche_roof_strictMono.monotone (Subtype.mk_le_mk.mpr hab)

/-- The `D` piece has monotone horizontal coordinate. -/
private theorem monotoneOn_paperGerverContacts_three_fst :
    MonotoneOn (fun t ↦ paperGerverContacts t 3 0)
      (Set.Icc (gerverStageTime 0) (gerverStageTime 2)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  intro a ha b hb hab
  have hA : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hB : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h := gerverNicheRoof_fst_le_of_le hA hB hab
  rwa [gerverNicheRoof_eq_D hA ha.2, gerverNicheRoof_eq_D hB hb.2] at h

/-- The `B` piece has monotone horizontal coordinate. -/
private theorem monotoneOn_paperGerverContacts_one_fst :
    MonotoneOn (fun t ↦ paperGerverContacts t 1 0)
      (Set.Icc (gerverStageTime 3) (gerverStageTime 5)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  intro a ha b hb hab
  have hA : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hB : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h := gerverNicheRoof_fst_le_of_le hA hB hab
  rwa [gerverNicheRoof_eq_B hA ha.1, gerverNicheRoof_eq_B hB hb.1] at h

/-- The ambient path has antitone horizontal coordinate over the middle roof piece. -/
private theorem antitoneOn_paperGerverPath_fst :
    AntitoneOn (fun t ↦ paperGerverPath t 0)
      (Set.Icc (gerverStageTime 1) (gerverStageTime 4)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  have hne32 : gerverStageTime 3 - gerverStageTime 2 ≠ 0 :=
    sub_ne_zero_of_ne (by intro hz; linarith)
  have hne41 : gerverStageTime 4 - gerverStageTime 1 ≠ 0 :=
    sub_ne_zero_of_ne (by intro hz; linarith)
  have hc : 0 < (gerverStageTime 4 - gerverStageTime 1) /
      (gerverStageTime 3 - gerverStageTime 2) := div_pos (by linarith) (by linarith)
  have hcne : (gerverStageTime 4 - gerverStageTime 1) /
      (gerverStageTime 3 - gerverStageTime 2) ≠ 0 := ne_of_gt hc
  set c := (gerverStageTime 4 - gerverStageTime 1) /
    (gerverStageTime 3 - gerverStageTime 2) with hcdef
  -- The reverse-time map is inverted by `t ↦ e₂ + (e₄ - t) / c`.
  have hinv : ∀ t : ℝ, gerverRoofReverseTime (gerverStageTime 2 +
      (gerverStageTime 4 - t) / c) = t := by
    intro t
    rw [gerverRoofReverseTime_eq_stageTime, ← hcdef]
    field_simp
    ring
  have heq : (gerverStageTime 4 - gerverStageTime 1) / c =
      gerverStageTime 3 - gerverStageTime 2 := by
    rw [hcdef]
    field_simp
  have hmem : ∀ t : ℝ, gerverStageTime 1 ≤ t → t ≤ gerverStageTime 4 →
      gerverStageTime 2 ≤ gerverStageTime 2 + (gerverStageTime 4 - t) / c ∧
        gerverStageTime 2 + (gerverStageTime 4 - t) / c ≤ gerverStageTime 3 := by
    intro t ht1 ht4
    have hnn : 0 ≤ (gerverStageTime 4 - t) / c := div_nonneg (by linarith) hc.le
    have hstep : (gerverStageTime 4 - gerverStageTime 1) / c -
        (gerverStageTime 4 - t) / c = (t - gerverStageTime 1) / c := by
      field_simp
      ring
    have hnn2 : 0 ≤ (t - gerverStageTime 1) / c := div_nonneg (by linarith) hc.le
    exact ⟨by linarith, by linarith⟩
  intro a ha b hb hab
  obtain ⟨ha2, ha3⟩ := hmem a ha.1 ha.2
  obtain ⟨hb2, hb3⟩ := hmem b hb.1 hb.2
  have hAmem : gerverStageTime 2 + (gerverStageTime 4 - a) / c ∈
      Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hBmem : gerverStageTime 2 + (gerverStageTime 4 - b) / c ∈
      Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hba : gerverStageTime 2 + (gerverStageTime 4 - b) / c ≤
      gerverStageTime 2 + (gerverStageTime 4 - a) / c := by
    have hsub : (gerverStageTime 4 - a) / c - (gerverStageTime 4 - b) / c = (b - a) / c := by
      field_simp
      ring
    have hnn : 0 ≤ (b - a) / c := div_nonneg (by linarith) hc.le
    linarith
  have h := gerverNicheRoof_fst_le_of_le hBmem hAmem hba
  rwa [gerverNicheRoof_eq_path hBmem hb2 hb3, gerverNicheRoof_eq_path hAmem ha2 ha3,
    hinv a, hinv b] at h

/-- Each roof piece has monotone horizontal coordinate in the direction recorded by
`rowFwd`. -/
theorem gerverNicheRow_monotone (r : ℕ) (hr : r < 7) :
    (rowFwd r = true → MonotoneOn (fun t ↦ gerverContactPoint (rowKind r) t 0)
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)))) ∧
      (rowFwd r = false → AntitoneOn (fun t ↦ gerverContactPoint (rowKind r) t 0)
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)))) := by
  obtain ⟨-, c01, c12, c23, c34, c45, -⟩ := gerverStageTime_chain
  have sD0 : Set.Icc (gerverStageTime 0) (gerverStageTime 1) ⊆
      Set.Icc (gerverStageTime 0) (gerverStageTime 2) := Set.Icc_subset_Icc le_rfl c12.le
  have sD1 : Set.Icc (gerverStageTime 1) (gerverStageTime 2) ⊆
      Set.Icc (gerverStageTime 0) (gerverStageTime 2) := Set.Icc_subset_Icc c01.le le_rfl
  have sP2 : Set.Icc (gerverStageTime 3) (gerverStageTime 4) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) :=
    Set.Icc_subset_Icc (c12.trans c23).le le_rfl
  have sP3 : Set.Icc (gerverStageTime 2) (gerverStageTime 3) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) := Set.Icc_subset_Icc c12.le c34.le
  have sP4 : Set.Icc (gerverStageTime 1) (gerverStageTime 2) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) :=
    Set.Icc_subset_Icc le_rfl (c23.trans c34).le
  have sB5 : Set.Icc (gerverStageTime 3) (gerverStageTime 4) ⊆
      Set.Icc (gerverStageTime 3) (gerverStageTime 5) := Set.Icc_subset_Icc le_rfl c45.le
  have sB6 : Set.Icc (gerverStageTime 4) (gerverStageTime 5) ⊆
      Set.Icc (gerverStageTime 3) (gerverStageTime 5) := Set.Icc_subset_Icc c34.le le_rfl
  interval_cases r
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_three_fst.mono sD0, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_three_fst.mono sD1, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP2⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP3⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP4⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_one_fst.mono sB5, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_one_fst.mono sB6, fun h ↦ absurd h (by decide)⟩

/-- An integer lower bound at scale `M` read as a bound on the real quotient. -/
private theorem div_M_le_of_le {p : ℤ} {x : ℝ} (h : (p : ℝ) ≤ (M : ℝ) * x) :
    (p : ℝ) / (M : ℝ) ≤ x :=
  (div_le_iff₀ SI.Mpos).2 (by linarith)

/-- An integer upper bound at scale `M` read as a bound on the real quotient. -/
private theorem le_div_M_of_le {p : ℤ} {x : ℝ} (h : (M : ℝ) * x ≤ (p : ℝ)) :
    x ≤ (p : ℝ) / (M : ℝ) :=
  (le_div_iff₀ SI.Mpos).2 (by linarith)

/-- A strict vertical fill over an increasing subdivision of its parameter interval is the
union of the fills of the pieces.  Iterated form of `strictVerticalFill_Icc_union`. -/
private theorem strictVerticalFill_Icc_biUnion {f : ℝ → Point} (a : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → (∀ i j, i ≤ j → j ≤ n → a i ≤ a j) →
      strictVerticalFill f (Set.Icc (a 0) (a n)) =
        ⋃ i ∈ Finset.range n, strictVerticalFill f (Set.Icc (a i) (a (i + 1))) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
    intro _ ha
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [strictVerticalFill_Icc_union (ha 0 n (Nat.zero_le _) (by omega))
        (ha n (n + 1) (by omega) le_rfl),
        ih hpos fun i j hij hj => ha i j hij (by omega),
        Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]

/-- Each covering rectangle contains the strict vertical fill of its subinterval. -/
theorem gerverNicheRect_covers (r j : ℕ) (hr : r < 7) (hj : j < NN) :
    strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r j)) (gerverGridTime (rowBase r j + 1))) ⊆
      gerverNicheRect r j := by
  have hNN : NN = 64 := rfl
  have hM := SI.Mpos
  have hk : rowKind r ≤ 4 := by interval_cases r <;> decide
  have hS1 : 1 ≤ rowStage r := by interval_cases r <;> decide
  have hS5 : rowStage r ≤ 5 := by interval_cases r <;> decide
  have hj64 : j < 64 := by rwa [hNN] at hj
  have hm1 : rowBase r j + 1 ≤ 5 * NN := by simp only [rowBase, hNN]; omega
  have hm : rowBase r j ≤ 5 * NN := by omega
  have hlo : gerverStageTime (rowStage r - 1) ≤ gerverGridTime (rowBase r j) := by
    have h := gerverGridTime_le_of_le
      (show (rowStage r - 1) * NN ≤ rowBase r j by simp only [rowBase]; omega) hm
    rwa [gerverGridTime_mul_NN] at h
  have hhi : gerverGridTime (rowBase r j + 1) ≤ gerverStageTime (rowStage r) := by
    have h := gerverGridTime_le_of_le
      (show rowBase r j + 1 ≤ rowStage r * NN by simp only [rowBase, hNN]; omega)
      (Nat.mul_le_mul_right NN hS5)
    rwa [gerverGridTime_mul_NN] at h
  have hstep : gerverGridTime (rowBase r j) ≤ gerverGridTime (rowBase r j + 1) :=
    gerverGridTime_le_of_le (Nat.le_succ _) hm1
  have hmemL : gerverGridTime (rowBase r j) ∈
      Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo, hstep.trans hhi⟩
  have hmemR : gerverGridTime (rowBase r j + 1) ∈
      Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo.trans hstep, hhi⟩
  obtain ⟨hmono, hanti⟩ := gerverNicheRow_monotone r hr
  rintro q ⟨t, ⟨htl, htr⟩, hq0, hq1a, hq1b⟩
  have hmemt : t ∈ Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo.trans htl, htr.trans hhi⟩
  have hHmax : rectHZ r j = max
      (evalZ (stageOf (rowBase r j + 1))
        ⟨(ttZ (rowBase r j)).lo, (ttZ (rowBase r j + 1)).hi⟩ (rowKind r)).2.hi
      (contactZ (rowBase r j) (rowKind r)).2.hi := by
    simp only [rectHZ, SI.imax_eq_max]
  have hH : (M : ℝ) * gerverContactPoint (rowKind r) t 1 ≤ (rectHZ r j : ℝ) := by
    rcases eq_or_lt_of_le htl with heq | hlt
    · have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).2.2
      rw [← heq]
      refine h.trans ?_
      rw [hHmax]
      exact_mod_cast le_max_right _ _
    · have h := (evalZ_interval_sound (rowBase r j) hm1 (rowKind r) hk ⟨hlt, htr⟩).2.2
      refine h.trans ?_
      rw [hHmax]
      exact_mod_cast le_max_left _ _
  refine ⟨⟨?_, ?_⟩, hq1a, ?_⟩
  · rcases Bool.eq_false_or_eq_true (rowFwd r) with hf | hf
    · have hlo' : rectLoZ r j = (contactZ (rowBase r j) (rowKind r)).1.lo := by
        simp [rectLoZ, hf]
      have hx : gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j)) 0 ≤
          gerverContactPoint (rowKind r) t 0 := hmono hf hmemL hmemt htl
      have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).1.1
      refine div_M_le_of_le ?_
      rw [hq0, hlo']
      exact h.trans (mul_le_mul_of_nonneg_left hx hM.le)
    · have hlo' : rectLoZ r j = (contactZ (rowBase r j + 1) (rowKind r)).1.lo := by
        simp [rectLoZ, hf]
      have hx : gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j + 1)) 0 ≤
          gerverContactPoint (rowKind r) t 0 := hanti hf hmemt hmemR htr
      have h := (contactZ_sound (rowBase r j + 1) hm1 (rowKind r) hk).1.1
      refine div_M_le_of_le ?_
      rw [hq0, hlo']
      exact h.trans (mul_le_mul_of_nonneg_left hx hM.le)
  · rcases Bool.eq_false_or_eq_true (rowFwd r) with hf | hf
    · have hhi' : rectHiZ r j = (contactZ (rowBase r j + 1) (rowKind r)).1.hi := by
        simp [rectHiZ, hf]
      have hx : gerverContactPoint (rowKind r) t 0 ≤
          gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j + 1)) 0 :=
        hmono hf hmemt hmemR htr
      have h := (contactZ_sound (rowBase r j + 1) hm1 (rowKind r) hk).1.2
      refine le_div_M_of_le ?_
      rw [hq0, hhi']
      exact (mul_le_mul_of_nonneg_left hx hM.le).trans h
    · have hhi' : rectHiZ r j = (contactZ (rowBase r j) (rowKind r)).1.hi := by
        simp [rectHiZ, hf]
      have hx : gerverContactPoint (rowKind r) t 0 ≤
          gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j)) 0 :=
        hanti hf hmemL hmemt htl
      have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).1.2
      refine le_div_M_of_le ?_
      rw [hq0, hhi']
      exact (mul_le_mul_of_nonneg_left hx hM.le).trans h
  · have h2 : (M : ℝ) * q 1 ≤ (M : ℝ) * gerverContactPoint (rowKind r) t 1 :=
      mul_le_mul_of_nonneg_left hq1b.le hM.le
    exact le_div_M_of_le (h2.trans hH)

/-- The `NN` rectangles of a row cover the strict vertical fill of its whole stage. -/
private theorem strictVerticalFill_row_subset (r : ℕ) (hr : r < 7) :
    strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r))) ⊆
      ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
  have hNN : NN = 64 := rfl
  have hS1 : 1 ≤ rowStage r := by interval_cases r <;> decide
  have hS5 : rowStage r ≤ 5 := by interval_cases r <;> decide
  have ha0 : gerverGridTime (rowBase r 0) = gerverStageTime (rowStage r - 1) := by
    simpa [rowBase] using gerverGridTime_mul_NN (rowStage r - 1)
  have haN : gerverGridTime (rowBase r NN) = gerverStageTime (rowStage r) := by
    have hb : rowBase r NN = rowStage r * NN := by simp only [rowBase, hNN]; omega
    rw [hb, gerverGridTime_mul_NN]
  have hmono : ∀ i j, i ≤ j → j ≤ NN →
      gerverGridTime (rowBase r i) ≤ gerverGridTime (rowBase r j) := by
    intro i j hij hj
    refine gerverGridTime_le_of_le (by simp only [rowBase]; omega) ?_
    simp only [rowBase, hNN]; omega
  have hsplit : strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r 0)) (gerverGridTime (rowBase r NN))) =
      ⋃ i ∈ Finset.range NN, strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r i)) (gerverGridTime (rowBase r i + 1))) :=
    strictVerticalFill_Icc_biUnion (fun i => gerverGridTime (rowBase r i)) NN
      (by simp [hNN]) hmono
  rw [← ha0, ← haN, hsplit]
  refine Set.iUnion₂_subset fun i hi q hq => ?_
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨i, hi, gerverNicheRect_covers r i hr (Finset.mem_range.1 hi) hq⟩

/-- The `7 * NN` rectangles cover the literal niche. -/
theorem gerverLiteralNiche_subset_rects :
    gerverLiteralNiche ⊆
      ⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
  have e0 : gerverStageTimes 0 = gerverStageTime 0 := rfl
  have e1 : gerverStageTimes 1 = gerverStageTime 1 := rfl
  have e2 : gerverStageTimes 2 = gerverStageTime 2 := rfl
  have e3 : gerverStageTimes 3 = gerverStageTime 3 := rfl
  have e4 : gerverStageTimes 4 = gerverStageTime 4 := rfl
  have e5 : gerverStageTimes 5 = gerverStageTime 5 := rfl
  have h01 : gerverStageTime 0 ≤ gerverStageTime 1 := (gerverStageTime_lt_succ 0 (by norm_num)).le
  have h12 : gerverStageTime 1 ≤ gerverStageTime 2 := (gerverStageTime_lt_succ 1 (by norm_num)).le
  have h23 : gerverStageTime 2 ≤ gerverStageTime 3 := (gerverStageTime_lt_succ 2 (by norm_num)).le
  have h34 : gerverStageTime 3 ≤ gerverStageTime 4 := (gerverStageTime_lt_succ 3 (by norm_num)).le
  have h45 : gerverStageTime 4 ≤ gerverStageTime 5 := (gerverStageTime_lt_succ 4 (by norm_num)).le
  have hrow : ∀ r, r < 7 → strictVerticalFill (gerverContactPoint (rowKind r))
      (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r))) ⊆
      ⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
    intro r hr q hq
    have h := strictVerticalFill_row_subset r hr hq
    simp only [Set.mem_iUnion, exists_prop] at h ⊢
    obtain ⟨j, hj, hjq⟩ := h
    exact ⟨r, Finset.mem_range.2 hr, j, hj, hjq⟩
  rw [gerver_niche_vertical_fills, e0, e1, e2, e3, e4, e5]
  refine Set.union_subset (Set.union_subset ?_ ?_) ?_
  · rw [strictVerticalFill_Icc_union h01 h12]
    exact Set.union_subset (hrow 0 (by norm_num)) (hrow 1 (by norm_num))
  · rw [strictVerticalFill_Icc_union h12 (h23.trans h34), strictVerticalFill_Icc_union h23 h34]
    exact Set.union_subset (hrow 4 (by norm_num))
      (Set.union_subset (hrow 3 (by norm_num)) (hrow 2 (by norm_num)))
  · rw [strictVerticalFill_Icc_union h34 h45]
    exact Set.union_subset (hrow 5 (by norm_num)) (hrow 6 (by norm_num))

/-- The planar volume of one covering rectangle. -/
theorem volume_gerverNicheRect (r j : ℕ) :
    volume (gerverNicheRect r j) =
      ENNReal.ofReal ((((rectHiZ r j - rectLoZ r j : ℤ)) : ℝ) / (M : ℝ)) *
        ENNReal.ofReal (((rectHZ r j : ℤ) : ℝ) / (M : ℝ)) := by
  rw [gerverNicheRect, EuclideanSpace.volume_setOf_apply_mem_Icc]
  congr 2
  · push_cast
    ring
  · ring

/-- The certificate bounds the total rectangle volume. -/
theorem gerverNicheRect_volume_sum_le :
    ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j) ≤
      ENNReal.ofReal ((3301 : ℝ) / 5000) := by
  have hM := SI.Mpos
  have hQ : (0 : ℝ) < (M : ℝ) * (M : ℝ) := mul_pos hM hM
  -- `unfold` rather than a type ascription: matching `nicheOK` against `decide _` by
  -- unification would force the elaborator to evaluate the whole certificate.
  have hcert : 5000 * nicheSumZ ≤ 3301 * M * M := by
    have h := nicheOK_true
    unfold nicheOK at h
    exact of_decide_eq_true h
  have harea : ∀ r j : ℕ,
      rectAreaZ r j = max 0 (rectHiZ r j - rectLoZ r j) * max 0 (rectHZ r j) := by
    intro r j
    simp only [rectAreaZ, SI.imax_eq_max]
  have hnn : ∀ r j : ℕ, (0 : ℝ) ≤ (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ)) := by
    intro r j
    refine div_nonneg ?_ hQ.le
    have : (0 : ℤ) ≤ rectAreaZ r j := by
      rw [harea]
      exact mul_nonneg (le_max_left _ _) (le_max_left _ _)
    exact_mod_cast this
  have hcell : ∀ r j : ℕ, volume (gerverNicheRect r j) ≤
      ENNReal.ofReal ((rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) := by
    intro r j
    have hA : ((rectHiZ r j - rectLoZ r j : ℤ) : ℝ) / (M : ℝ) ≤
        ((max 0 (rectHiZ r j - rectLoZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      gcongr
      exact_mod_cast le_max_right (0 : ℤ) (rectHiZ r j - rectLoZ r j)
    have hB : ((rectHZ r j : ℤ) : ℝ) / (M : ℝ) ≤
        ((max 0 (rectHZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      gcongr
      exact_mod_cast le_max_right (0 : ℤ) (rectHZ r j)
    have hA0 : (0 : ℝ) ≤ ((max 0 (rectHiZ r j - rectLoZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      refine div_nonneg ?_ hM.le
      exact_mod_cast le_max_left (0 : ℤ) (rectHiZ r j - rectLoZ r j)
    rw [volume_gerverNicheRect]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hB)) ?_
    rw [← ENNReal.ofReal_mul hA0]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [harea]
    push_cast
    field_simp
  have hns : nicheSumZ = ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, rectAreaZ r j := by
    rw [nicheSumZ, SI.foldl_range_int]
    exact Finset.sum_congr rfl fun r _ => by rw [rowSumZ, SI.foldl_range_int]
  have hsum : ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
      (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ)) =
        (nicheSumZ : ℝ) / ((M : ℝ) * (M : ℝ)) := by
    rw [hns]
    push_cast
    simp only [← Finset.sum_div]
  calc ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j)
      ≤ ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
          ENNReal.ofReal ((rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => hcell r j
    _ = ∑ r ∈ Finset.range 7, ENNReal.ofReal
          (∑ j ∈ Finset.range NN, (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        Finset.sum_congr rfl fun r _ =>
          (ENNReal.ofReal_sum_of_nonneg fun j _ => hnn r j).symm
    _ = ENNReal.ofReal (∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
          (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        (ENNReal.ofReal_sum_of_nonneg fun r _ => Finset.sum_nonneg fun j _ => hnn r j).symm
    _ ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsum, div_le_div_iff₀ hQ (by norm_num)]
        have hR : (5000 : ℝ) * (nicheSumZ : ℝ) ≤ 3301 * (M : ℝ) * (M : ℝ) := by
          exact_mod_cast hcert
        linarith

/-- The niche volume bound. -/
theorem gerver_niche_volume_le :
    volume gerverLiteralNiche ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := by
  calc volume gerverLiteralNiche
      ≤ volume (⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j) :=
        measure_mono gerverLiteralNiche_subset_rects
    _ ≤ ∑ r ∈ Finset.range 7, volume (⋃ j ∈ Finset.range NN, gerverNicheRect r j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j) :=
        Finset.sum_le_sum fun _ _ => measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := gerverNicheRect_volume_sum_le

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Rational area bounds for the canonical Gerver sofa

The canonical Gerver sofa is the paper's literal set (`gerver_canonical_paper_literal`), the
difference of the literal outer cap and the literal niche.  The cap and the niche are Borel
of finite area with `28609 / 10000 ≤ |K₀|` and `|N₀| ≤ 3301 / 5000`
(`gerver_geometric_area_bounds`), both numeric bounds coming from the kernel-checked
certificate `MovingSofa.Gerver.AreaCertificate` through the fan bound of
`MovingSofa.Gerver.Area.CapFan` and the rectangle cover of
`MovingSofa.Gerver.Area.NicheCover`.  Subadditivity of area then gives
`11 / 5 ≤ |G|` (`gerver_area_lower_bound`).
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory

theorem gerver_canonical_paper_literal :
    gerversSofa = paperGerverSofa ∧ paperGerverSofa = gerverLiteralSofa := by
  refine ⟨?_, paperGerverSofa_eq_literal⟩
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  -- Translate-then-rotate splits into rotation of the point plus rotation of the shift.
  have hrt : ∀ (α : Real.Angle) (v s : Point),
      rotateTranslate α v s = rotationMap α s + rotationMap α v := by
    intro α v s
    show (EuclideanGeometry.o.rotation α) (s + v) = _
    exact map_add _ _ _
  -- The canonical placements agree with the paper ones on `[0, π/2]`.
  have himg : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ S : Set Point,
      rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' S =
        (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' S := by
    intro t ht S
    apply Set.image_congr'
    intro s
    rw [hrt, canonical_path_rotation_eq_paper t ht]
  -- Membership in a rotated-translated coordinate region is read off in the moving frame.
  have himage : ∀ (P : ℝ → ℝ → Prop) (S : Set Point),
      (∀ s : Point, s ∈ S ↔ P (s 0) (s 1)) →
      ∀ (t : Real.Angle) (v z : Point),
        z ∈ (fun s ↦ rotationMap t s + v) '' S ↔
          P (inner ℝ (z - v) (normalVector t)) (inner ℝ (z - v) (tangentVector t)) := by
    intro P S hS t v z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h0 : inner ℝ (rotationMap t s + v - v) (normalVector t) = s 0 := by
        rw [add_sub_cancel_right, inner_rotationMap_normalVector]
      have h1 : inner ℝ (rotationMap t s + v - v) (tangentVector t) = s 1 := by
        rw [add_sub_cancel_right, inner_rotationMap_tangentVector]
      rw [h0, h1]
      exact (hS s).1 hs
    · intro h
      obtain ⟨s, hs⟩ := (EuclideanGeometry.o.rotation t).surjective (z - v)
      have hsz : rotationMap t s = z - v := hs
      have h0 : s 0 = inner ℝ (z - v) (normalVector t) := by
        rw [← inner_rotationMap_normalVector s t, hsz]
      have h1 : s 1 = inner ℝ (z - v) (tangentVector t) := by
        rw [← inner_rotationMap_tangentVector s t, hsz]
      refine ⟨s, (hS s).2 ?_, ?_⟩
      · rw [h0, h1]; exact h
      · show rotationMap t s + v = z
        rw [hsz]; abel
  have hhoriz : ∀ s : Point, s ∈ horizontalHallway ↔ s 0 ≤ 1 ∧ 0 ≤ s 1 ∧ s 1 ≤ 1 :=
    fun s => ⟨mem_horizontalHallway_coordinates,
      fun h => mem_horizontalHallway_of_coordinates s h.1 ⟨h.2.1, h.2.2⟩⟩
  have hvert : ∀ s : Point, s ∈ verticalHallway ↔ 0 ≤ s 0 ∧ s 0 ≤ 1 ∧ s 1 ≤ 1 :=
    fun s => ⟨mem_verticalHallway_coordinates,
      fun h => mem_verticalHallway_of_coordinates s ⟨h.1, h.2.1⟩ h.2.2⟩
  have hhall : ∀ s : Point, s ∈ hallway ↔ (s 0 ≤ 1 ∧ s 1 ≤ 1) ∧ (0 ≤ s 0 ∨ 0 ≤ s 1) :=
    mem_hallway_iff
  -- Endpoint normalisations of the paper path.
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hpath0 : paperGerverPath 0 = 0 := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hpathT : paperGerverPath (Real.pi / 2) 1 = 0 :=
    GerverSofa.Romik.path_end_y_zero_of_mem_box_and_equations
      GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hstrip : ∀ z : Point,
      z ∈ (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ↔ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
    intro z
    have h := mem_stripParallelogram_iff (Real.pi / 2) z
    rw [inner_normalVector_pi_div_two] at h
    have hset : (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 =
        (stripParallelogram (Real.pi / 2)).1 := rfl
    rw [hset, h]
    tauto
  -- Rewrite both endpoint arms and the family of hallways in the paper frame.
  have hzero : ((0 : ℝ) : Real.Angle) = (0 : Real.Angle) := Real.Angle.coe_zero
  have hgs : gerversSofa =
      ((fun s ↦ rotationMap ((0 : ℝ) : Real.Angle) s + paperGerverPath 0) ''
          horizontalHallway ∩
        (fun s ↦ rotationMap ((Real.pi / 2 : ℝ) : Real.Angle) s +
          paperGerverPath (Real.pi / 2)) '' verticalHallway) ∩
      ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' hallway := by
    show rotateTranslate 0 (GerversSofa.p 0) '' horizontalHallway ∩
        rotateTranslate ((Real.pi / 2 : ℝ) : Real.Angle)
          (GerversSofa.p (Real.pi / 2)) '' verticalHallway ∩
        (⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' hallway) = _
    rw [← hzero, himg 0 hT0 horizontalHallway,
      himg (Real.pi / 2) hTT verticalHallway,
      Set.iInter₂_congr (fun t (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) => himg t ht hallway)]
  have hpaper : paperGerverSofa =
      {z : Point | 0 ≤ z 1 ∧ z 1 ≤ 1} ∩
        ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' hallway := by
    show (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ∩ _ = _
    rw [Set.ext hstrip]
    rfl
  rw [hgs, hpaper]
  ext q
  have hn0 : inner ℝ (q - paperGerverPath 0) (normalVector ((0 : ℝ) : Real.Angle)) = q 0 := by
    rw [hpath0, sub_zero, inner_normalVector_zero]
  have hg0 : inner ℝ (q - paperGerverPath 0) (tangentVector ((0 : ℝ) : Real.Angle)) = q 1 := by
    rw [hpath0, sub_zero, inner_tangentVector_zero]
  have hnT : inner ℝ (q - paperGerverPath (Real.pi / 2))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = q 1 := by
    rw [inner_normalVector_pi_div_two]
    show q 1 - paperGerverPath (Real.pi / 2) 1 = q 1
    rw [hpathT, sub_zero]
  have hAhoriz := himage (fun a b => a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1) horizontalHallway hhoriz
  have hAvert := himage (fun a b => 0 ≤ a ∧ a ≤ 1 ∧ b ≤ 1) verticalHallway hvert
  have hAhall := himage (fun a b => (a ≤ 1 ∧ b ≤ 1) ∧ (0 ≤ a ∨ 0 ≤ b)) hallway hhall
  simp only [Set.mem_inter_iff, Set.mem_iInter₂, Set.mem_ofPred_eq, hAhoriz, hAvert, hAhall,
    hn0, hg0, hnT]
  constructor
  · rintro ⟨⟨⟨-, hb0, hb1⟩, -⟩, hC⟩
    exact ⟨⟨hb0, hb1⟩, hC⟩
  · rintro ⟨⟨hb0, hb1⟩, hC⟩
    refine ⟨⟨⟨?_, hb0, hb1⟩, hb0, hb1, ?_⟩, hC⟩
    · have h := (hC 0 hT0).1.1
      rwa [hn0] at h
    · exact (hC (Real.pi / 2) hTT).1.2

theorem gerver_geometric_area_bounds :
    MeasurableSet gerverOuterCap ∧ volume gerverOuterCap < ⊤ ∧
    MeasurableSet gerverLiteralNiche ∧ volume gerverLiteralNiche < ⊤ ∧
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap ∧
    ClassicalResults.area gerverLiteralNiche ≤ (3301 : ℝ) / 5000 := by
  have hfin : volume gerverLiteralNiche ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) :=
    gerver_niche_volume_le
  refine ⟨measurableSet_gerverOuterCap, volume_gerverOuterCap_lt_top,
    measurableSet_gerverLiteralNiche, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top,
    gerverOuterCap_area_certified_lower_bound, ?_⟩
  calc ClassicalResults.area gerverLiteralNiche
      = (volume gerverLiteralNiche).toReal := rfl
    _ ≤ (ENNReal.ofReal ((3301 : ℝ) / 5000)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = (3301 : ℝ) / 5000 := ENNReal.toReal_ofReal (by norm_num)

theorem gerver_area_lower_bound :
    volume gerversSofa < ⊤ ∧ (11 : ℝ) / 5 ≤ ClassicalResults.area gerversSofa := by
  obtain ⟨-, hKtop, -, hNtop, hKarea, hNarea⟩ := gerver_geometric_area_bounds
  have hG : gerversSofa = gerverOuterCap \ gerverLiteralNiche :=
    gerver_canonical_paper_literal.1.trans gerver_canonical_paper_literal.2
  have hGtop : volume gerversSofa < ⊤ :=
    lt_of_le_of_lt (measure_mono (hG ▸ Set.sdiff_subset)) hKtop
  refine ⟨hGtop, ?_⟩
  -- The cap is covered by the sofa together with the niche, so areas are subadditive.
  have hcover : volume gerverOuterCap ≤ volume gerversSofa + volume gerverLiteralNiche := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    rw [hG]
    exact Set.subset_sdiff_union _ _
  have hreal : ClassicalResults.area gerverOuterCap ≤
      ClassicalResults.area gerversSofa + ClassicalResults.area gerverLiteralNiche := by
    have h := ENNReal.toReal_mono (by finiteness) hcover
    rwa [ENNReal.toReal_add hGtop.ne hNtop.ne] at h
  linarith only [hreal, hKarea, hNarea]

end MovingSofa

end

end

end
