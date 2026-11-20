/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Mathlib.Analysis.Polynomial.Order
public import LeanPool.Ratpoints.Spec.Sturm

import LeanPool.Ratpoints.Mathlib.Analysis.Polynomial.Sturm
import LeanPool.Ratpoints.Mathlib.FieldTheory.Perfect

/-!
# What Sturm's theorem says about an interval

The consequences of Sturm's theorem (`Ratpoints.SturmTheorem`) for an interval with ends that may be
infinite, which the bisection of the Sturm step relies on: the counts of the Sturm sequence at the
ends (`Ratpoints.vLeft`, `Ratpoints.vRight`: `V(l)` at the lower end, `V(r)` plus `1` at a root `r`
at the upper end, `V(∓∞)` at the ends at infinity) agree exactly when the squarefree polynomial `F`
has no root strictly between them (`Ratpoints.vLeft_eq_vRight_iff`); then, when `F` is negative just
inside the lower end, it is negative between the ends and just inside the upper end
(`Ratpoints.eval_neg_of_vLeft_eq_vRight`); when the counts differ, or `F` is positive just inside
the lower end, `F` is positive somewhere between the ends (`Ratpoints.exists_inside_eval_pos`); and
equal counts at `∓∞` leave no root at all, so that `F` is negative everywhere when it is negative at
`0` (`Ratpoints.eval_neg_of_vBot_eq_vTop`). Infinite ends are replaced by points far out, where the
counts and the signs are those at infinity (`Ratpoints.eventually_atBot_sturm`,
`Ratpoints.eventually_atTop_sturm`).

## Main definitions

* `Ratpoints.sturmV`, `Ratpoints.vBot`, `Ratpoints.vTop`: the counts of the Sturm sequence at a
  point and at `∓∞`.
* `Ratpoints.vLeft`, `Ratpoints.vRight`, `Ratpoints.sgnLeftEnd`, `Ratpoints.sgnRightEnd`: the
  counts at the ends of an interval and, for a squarefree `F`, the signs of `F` just inside them.
* `Ratpoints.Inside`: a point strictly between the ends.

## Main statements

* `Ratpoints.sturmV_eq_iff`: the counts at finite ends agree exactly when no root lies between.
* `Ratpoints.vLeft_eq_vRight_iff`: the same for ends that may be infinite.
* `Ratpoints.eval_neg_of_vLeft_eq_vRight`: an interval that the bisection drops holds no `x` with
  `F(x) ≥ 0`.
* `Ratpoints.exists_inside_eval_pos`: an interval that the bisection keeps holds an `x` with
  `F(x) > 0`.
* `Ratpoints.eval_neg_of_vBot_eq_vTop`: a polynomial with equal counts at `∓∞`, negative at `0`, is
  negative everywhere.
-/

@[expose] public section

open Polynomial Filter Topology

namespace Ratpoints

/-- The number of sign variations of the Sturm sequence of `F` and `F'` at `x`, the count of
`Ratpoints.SturmTheorem`. -/
noncomputable abbrev sturmV (F : ℝ[X]) (x : ℝ) : ℕ :=
  ((sturmSeq F (derivative F)).map (eval x)).signVariations

/-- The count of the Sturm sequence of `F` and `F'` at `-∞`: the number of sign variations of the
leading coefficients of its entries, each times `(-1) ^ deg`. -/
noncomputable def vBot (F : ℝ[X]) : ℕ :=
  ((sturmSeq F (derivative F)).map fun p ↦ (-1) ^ p.natDegree * p.leadingCoeff).signVariations

/-- The count of the Sturm sequence of `F` and `F'` at `+∞`: the number of sign variations of the
leading coefficients of its entries. -/
noncomputable def vTop (F : ℝ[X]) : ℕ :=
  ((sturmSeq F (derivative F)).map leadingCoeff).signVariations

/-- The count at the lower end `l` of an interval, `none` for `-∞`: `V(l)`, or `V(-∞)`. -/
noncomputable def vLeft (F : ℝ[X]) : Option ℝ → ℕ
  | none => vBot F
  | some a => sturmV F a

/-- The count at the upper end `r` of an interval, `none` for `+∞`: `V(r)`, plus `1` at a root of
`F`, or `V(+∞)`. -/
noncomputable def vRight (F : ℝ[X]) : Option ℝ → ℕ
  | none => vTop F
  | some b => sturmV F b + if F.IsRoot b then 1 else 0

/-- At the lower end `l` of an interval, `none` for `-∞`: the sign of `(-1) ^ deg F` times the
leading coefficient of `F` at `-∞`, and at a finite end `a` that of `F(a)`, or of `F'(a)` when
`F(a) = 0`. This is the sign of `F` just inside the end when `F(a)` and `F'(a)` do not both vanish,
as for a squarefree `F`, where it is not zero (`Ratpoints.sgnLeftEnd_ne_zero`). -/
noncomputable def sgnLeftEnd (F : ℝ[X]) : Option ℝ → SignType
  | none => SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff)
  | some a =>
    if F.eval a = 0 then SignType.sign (F.derivative.eval a) else SignType.sign (F.eval a)

/-- At the upper end `r` of an interval, `none` for `+∞`: the sign of the leading coefficient of
`F` at `+∞`, and at a finite end `b` that of `F(b)`, or of `-F'(b)` when `F(b) = 0`. This is the
sign of `F` just inside the end when `F(b)` and `F'(b)` do not both vanish, as for a squarefree
`F`. -/
noncomputable def sgnRightEnd (F : ℝ[X]) : Option ℝ → SignType
  | none => SignType.sign F.leadingCoeff
  | some b =>
    if F.eval b = 0 then -SignType.sign (F.derivative.eval b) else SignType.sign (F.eval b)

/-- `x` lies strictly between the ends `l` and `r`, `none` for `∓∞`. -/
def Inside (l r : Option ℝ) (x : ℝ) : Prop := (∀ a ∈ l, a < x) ∧ ∀ b ∈ r, x < b

-- The roots of `F` in `(l, r]` when none lies in `(l, r)`: `r`, if it is one.
private theorem setOf_isRoot_eq {F : ℝ[X]} {l r : ℝ} (hlr : l < r)
    (h : ∀ x, l < x → x < r → ¬ F.IsRoot x) :
    {x | l < x ∧ x ≤ r ∧ F.IsRoot x} = if F.IsRoot r then {r} else ∅ := by
  ext x
  split_ifs with hr <;> simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  · exact ⟨fun ⟨h1, h2, h3⟩ ↦ h2.lt_or_eq.elim (fun h4 ↦ absurd h3 (h x h1 h4)) id,
      fun hx ↦ by rw [hx]; exact ⟨hlr, le_rfl, hr⟩⟩
  · exact fun h1 h2 h3 ↦ h2.lt_or_eq.elim (fun h4 ↦ h x h1 h4 h3) fun h4 ↦ hr (h4 ▸ h3)

/-- By Sturm's theorem, the counts `V(l)` and `V(r)`, plus `1` at a root `r`, agree exactly when
`F` has no root in `(l, r)`, for `l < r`. -/
theorem sturmV_eq_iff (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F) {l r : ℝ} (hlr : l < r) :
    sturmV F l = sturmV F r + (if F.IsRoot r then 1 else 0) ↔
      ∀ x, l < x → x < r → ¬ F.IsRoot x := by
  have hS' := hS F hF l r hlr.le
  refine ⟨fun h x hlx hxr hx ↦ ?_, fun h ↦ ?_⟩
  · have hfin : {x | l < x ∧ x ≤ r ∧ F.IsRoot x}.Finite :=
      (finite_setOfPred_isRoot hF.ne_zero).subset fun y hy ↦ hy.2.2
    by_cases hr : F.IsRoot r
    · have h1 := Set.ncard_le_ncard (s := {x, r}) (by
        simpa [Set.insert_subset_iff] using ⟨⟨hlx, hxr.le, hx⟩, hlx.trans hxr, hr⟩) hfin
      simp only [Set.ncard_pair hxr.ne, hr, ↓reduceIte] at h1 h
      lia
    · have h1 := Set.ncard_le_ncard (s := {x}) (by simpa using ⟨hlx, hxr.le, hx⟩) hfin
      simp only [Set.ncard_singleton, hr, ↓reduceIte] at h1 h
      lia
  · rw [setOf_isRoot_eq hlr h] at hS'
    split_ifs at hS' ⊢ <;> simp at hS' <;> lia

/-- Far left, the count is `V(-∞)`, `F` has no root, and the sign of `F` is that at `-∞`. -/
theorem eventually_atBot_sturm {F : ℝ[X]} (hF : F ≠ 0) :
    ∀ᶠ y in atBot, sturmV F y = vBot F ∧ ¬ F.IsRoot y ∧
      SignType.sign (F.eval y) = SignType.sign ((-1) ^ F.natDegree * F.leadingCoeff) :=
  (eventually_atBot_signVariations fun _ hp ↦ ne_zero_of_mem_sturmSeq hp).and
    ((eventually_atBot_not_isRoot hF).and (eventually_atBot_sign_eval hF))

/-- Far right, the count is `V(+∞)`, `F` has no root, and the sign of `F` is that of its leading
coefficient. -/
theorem eventually_atTop_sturm {F : ℝ[X]} (hF : F ≠ 0) :
    ∀ᶠ y in atTop, sturmV F y = vTop F ∧ ¬ F.IsRoot y ∧
      SignType.sign (F.eval y) = SignType.sign F.leadingCoeff :=
  (eventually_atTop_signVariations fun _ hp ↦ ne_zero_of_mem_sturmSeq hp).and
    ((eventually_atTop_not_isRoot hF).and (eventually_atTop_sign_eval hF))

/-- A finite point `l' < x` standing for the lower end `l` left of `x`: `l` itself, or a point far
left, with the count and the sign just right of it of the end. -/
theorem exists_lt_sturmV_eq_vLeft {F : ℝ[X]} (hF : F ≠ 0) {l : Option ℝ} {x : ℝ}
    (hx : ∀ a ∈ l, a < x) :
    ∃ l' < x, (∀ a ∈ l, l' = a) ∧ sturmV F l' = vLeft F l ∧
      sgnLeftEnd F (some l') = sgnLeftEnd F l := by
  cases l with
  | some a => exact ⟨a, hx a rfl, fun _ h ↦ Option.some.inj h, rfl, rfl⟩
  | none =>
    obtain ⟨A, hA⟩ := eventually_atBot.mp (eventually_atBot_sturm hF)
    obtain ⟨h1, h2, h3⟩ := hA (min A (x - 1)) (min_le_left _ _)
    exact ⟨min A (x - 1), by linarith [min_le_right A (x - 1)], nofun, h1, by
      simp only [sgnLeftEnd]; rw [ite_eq_right (show eval _ F ≠ 0 from h2), h3]⟩

/-- A finite point `r' > x` standing for the upper end `r` right of `x`: `r` itself, or a point far
right, with the count and the sign just left of it of the end. -/
theorem exists_gt_sturmV_add_eq_vRight {F : ℝ[X]} (hF : F ≠ 0) {r : Option ℝ} {x : ℝ}
    (hx : ∀ b ∈ r, x < b) :
    ∃ r' > x, (∀ b ∈ r, r' = b) ∧ sturmV F r' + (if F.IsRoot r' then 1 else 0) = vRight F r ∧
      sgnRightEnd F (some r') = sgnRightEnd F r := by
  cases r with
  | some b => exact ⟨b, hx b rfl, fun _ h ↦ Option.some.inj h, rfl, rfl⟩
  | none =>
    obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_atTop_sturm hF)
    obtain ⟨h1, h2, h3⟩ := hB (max B (x + 1)) (le_max_left _ _)
    exact ⟨max B (x + 1), by linarith [le_max_right B (x + 1)], nofun,
      by rw [ite_eq_right h2, h1]; rfl, by
      simp only [sgnRightEnd]; rw [ite_eq_right (show eval _ F ≠ 0 from h2), h3]⟩

/-- Ends in order have a point between them. -/
theorem exists_inside {l r : Option ℝ} (hlr : ∀ a ∈ l, ∀ b ∈ r, a < b) : ∃ x, Inside l r x := by
  rcases l with _ | a <;> rcases r with _ | b
  · exact ⟨0, by simp [Inside]⟩
  · exact ⟨b - 1, by simp [Inside]⟩
  · exact ⟨a + 1, by simp [Inside]⟩
  · have := hlr a rfl b rfl
    exact ⟨(a + b) / 2, by
      simp only [Inside, Option.mem_def, Option.some.injEq, forall_eq']; constructor <;> linarith⟩

/-- Near a point between the ends, every point lies between them. -/
theorem eventually_inside {l r : Option ℝ} {x : ℝ} (hx : Inside l r x) :
    ∀ᶠ y in 𝓝 x, Inside l r y := by
  rcases l with _ | a <;> rcases r with _ | b <;>
    simp only [Inside, Option.mem_def, Option.some.injEq, forall_eq', reduceCtorEq, false_implies,
      implies_true, true_and, and_true, Filter.eventually_true] at hx ⊢
  · exact eventually_lt_nhds hx
  · exact eventually_gt_nhds hx
  · exact (eventually_gt_nhds hx.1).and (eventually_lt_nhds hx.2)

/-- By Sturm's theorem, the counts at the ends of an interval agree exactly when `F` has no root
strictly between them. -/
theorem vLeft_eq_vRight_iff (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F) {l r : Option ℝ}
    (hlr : ∀ a ∈ l, ∀ b ∈ r, a < b) :
    vLeft F l = vRight F r ↔ ∀ x, Inside l r x → ¬ F.IsRoot x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨l', hl', -, hvl, -⟩ := exists_lt_sturmV_eq_vLeft hF.ne_zero hx.1
    obtain ⟨r', hr', -, hvr, -⟩ := exists_gt_sturmV_add_eq_vRight hF.ne_zero hx.2
    exact (sturmV_eq_iff hS hF (hl'.trans hr')).mp (by rw [hvl, h, hvr]) x hl' hr'
  · obtain ⟨x, hx⟩ := exists_inside hlr
    obtain ⟨l', hl', hle, hvl, -⟩ := exists_lt_sturmV_eq_vLeft hF.ne_zero hx.1
    obtain ⟨r', hr', hre, hvr, -⟩ := exists_gt_sturmV_add_eq_vRight hF.ne_zero hx.2
    rw [← hvl, ← hvr]
    exact (sturmV_eq_iff hS hF (hl'.trans hr')).mpr fun y h1 h2 ↦ h y
      ⟨fun a ha ↦ hle a ha ▸ h1, fun b hb ↦ hre b hb ▸ h2⟩

/-- The sign of a squarefree `F` just inside a lower end is not zero. -/
theorem sgnLeftEnd_ne_zero {F : ℝ[X]} (hF : Squarefree F) (l : Option ℝ) : sgnLeftEnd F l ≠ 0 := by
  rcases l with _ | a
  · simp [sgnLeftEnd, hF.ne_zero]
  · simp only [sgnLeftEnd]
    split_ifs with h
    · exact sign_ne_zero.mpr
        ((hF.eval_ne_zero_or_eval_derivative_ne_zero a).resolve_left (by simpa))
    · exact sign_ne_zero.mpr h

/-- By Sturm's theorem, when the counts at the ends of an interval agree and `F` is negative just
inside its lower end, `F` is negative between the ends and just inside the upper end: the interval
holds no `x` with `F(x) ≥ 0`. -/
theorem eval_neg_of_vLeft_eq_vRight (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F)
    {l r : Option ℝ} (hlr : ∀ a ∈ l, ∀ b ∈ r, a < b) (h : vLeft F l = vRight F r)
    (hs : sgnLeftEnd F l = -1) : (∀ x, Inside l r x → F.eval x < 0) ∧ sgnRightEnd F r = -1 := by
  have hroot := (vLeft_eq_vRight_iff hS hF hlr).mp h
  have key (x : ℝ) (hx : Inside l r x) : F.eval x < 0 := by
    obtain ⟨l', hl', hle, -, hsl⟩ := exists_lt_sturmV_eq_vLeft hF.ne_zero hx.1
    obtain ⟨r', hr', hre, -, -⟩ := exists_gt_sturmV_add_eq_vRight hF.ne_zero hx.2
    refine eval_neg_of_forall_not_isRoot (fun y h1 h2 ↦ hroot y
      ⟨fun a ha ↦ hle a ha ▸ h1, fun b hb ↦ hre b hb ▸ h2⟩) ?_ hl' hr'
    filter_upwards [eventually_sign_eval_nhdsGT (hF.eval_ne_zero_or_eval_derivative_ne_zero l')]
      with y hy
    exact sign_eq_neg_one_iff.mp (hy.trans (hsl.trans hs))
  refine ⟨key, ?_⟩
  obtain ⟨x, hx⟩ := exists_inside hlr
  obtain ⟨r', hr', hre, -, hsr⟩ := exists_gt_sturmV_add_eq_vRight hF.ne_zero hx.2
  obtain ⟨y, hy, hxy, hyr⟩ := ((eventually_sign_eval_nhdsLT
    (hF.eval_ne_zero_or_eval_derivative_ne_zero r')).and (Ioo_mem_nhdsLT hr')).exists
  exact hsr.symm.trans <| hy.symm.trans <| sign_neg
    (key y ⟨fun a ha ↦ (hx.1 a ha).trans hxy, fun b hb ↦ hre b hb ▸ hyr⟩)

/-- By Sturm's theorem, a squarefree real polynomial with equal counts at `∓∞` has no real root,
so that it is negative everywhere when it is negative at `0`. -/
theorem eval_neg_of_vBot_eq_vTop (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F)
    (h : vBot F = vTop F) (h0 : F.eval 0 < 0) (x : ℝ) : F.eval x < 0 := by
  have hroot := (vLeft_eq_vRight_iff hS hF (l := none) (r := none) (by simp)).mp h
  have hx0 (y : ℝ) : F.eval y ≠ 0 := hroot y (by simp [Inside])
  by_contra! hx
  have hx' := lt_of_le_of_ne hx (hx0 x).symm
  rcases lt_trichotomy x 0 with hlt | rfl | hgt
  · obtain ⟨z, -, hz⟩ := exists_isRoot_of_eval_mul_eval_neg hlt (mul_neg_of_pos_of_neg hx' h0)
    exact hx0 z hz
  · linarith
  · obtain ⟨z, -, hz⟩ := exists_isRoot_of_eval_mul_eval_neg hgt (mul_neg_of_neg_of_pos h0 hx')
    exact hx0 z hz

/-- Next to a root of a squarefree `F` between the ends of an interval, `F` is positive at some
point between them: it changes its sign at the root. -/
theorem exists_inside_eval_pos_of_isRoot {F : ℝ[X]} (hF : Squarefree F) {l r : Option ℝ} {z : ℝ}
    (hz : Inside l r z) (hz0 : F.IsRoot z) : ∃ x, Inside l r x ∧ 0 < F.eval x := by
  have hd := hF.eval_ne_zero_or_eval_derivative_ne_zero z
  rcases (hd.resolve_left (not_not.mpr hz0)).lt_or_gt with hneg | hpos
  · obtain ⟨y, hy, hyi⟩ := ((eventually_sign_eval_nhdsLT hd).and
      (nhdsWithin_le_nhds (eventually_inside hz))).exists
    refine ⟨y, hyi, sign_eq_one_iff.mp ?_⟩
    rw [hy, ite_eq_left (IsRoot.def.mp hz0), sign_neg hneg]
    rfl
  · obtain ⟨y, hy, hyi⟩ := ((eventually_sign_eval_nhdsGT hd).and
      (nhdsWithin_le_nhds (eventually_inside hz))).exists
    refine ⟨y, hyi, sign_eq_one_iff.mp ?_⟩
    rw [hy, ite_eq_left (IsRoot.def.mp hz0), sign_pos hpos]

/-- By Sturm's theorem, `F` is positive at some point between the ends of an interval when the
counts at its ends differ, so that a root lies between them, or when `F` is positive just inside
its lower end. -/
theorem exists_inside_eval_pos (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F)
    {l r : Option ℝ} (hlr : ∀ a ∈ l, ∀ b ∈ r, a < b)
    (h : vLeft F l ≠ vRight F r ∨ sgnLeftEnd F l = 1) : ∃ x, Inside l r x ∧ 0 < F.eval x := by
  rcases h with h | h
  · obtain ⟨z, hz, hz0⟩ : ∃ z, Inside l r z ∧ F.IsRoot z := by
      by_contra! h'
      exact h ((vLeft_eq_vRight_iff hS hF hlr).mpr h')
    exact exists_inside_eval_pos_of_isRoot hF hz hz0
  · obtain ⟨x, hx⟩ := exists_inside hlr
    obtain ⟨l', hl', hle, -, hsl⟩ := exists_lt_sturmV_eq_vLeft hF.ne_zero hx.1
    obtain ⟨y, hy, hly, hyx⟩ := ((eventually_sign_eval_nhdsGT
      (hF.eval_ne_zero_or_eval_derivative_ne_zero l')).and (Ioo_mem_nhdsGT hl')).exists
    exact ⟨y, ⟨fun a ha ↦ hle a ha ▸ hly, fun b hb ↦ hyx.trans (hx.2 b hb)⟩,
      sign_eq_one_iff.mp (hy.trans (hsl.trans h))⟩

end Ratpoints

end
