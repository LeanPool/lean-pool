/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import LeanPool.Ratpoints.Proof.Bisection
public import LeanPool.Ratpoints.Proof.SturmSigns

import LeanPool.Ratpoints.Mathlib.Algebra.Polynomial.Eval.Coeff
import LeanPool.Ratpoints.Mathlib.Basic.Sign.Defs
import LeanPool.Ratpoints.Mathlib.FieldTheory.Perfect
import LeanPool.Ratpoints.Proof.Double

/-!
# The Sturm step keeps every point

`Ratpoints.Sturm.covers_computeSturm` shows that the intervals left by the Sturm step include
each value `x` in the caller's intervals such that `|x| ≤ 2 ^ 63` and `f(x) ≥ 0`.

The bisection uses the signs and variation counts of the squarefree polynomial at each endpoint.
A dropped interval has negative values throughout. If an interval needs to be split, one of its
halves retains each value with nonnegative evaluation, including any root at the midpoint.
-/

@[expose] public section

open Polynomial

namespace Ratpoints

namespace Sturm

/-- The lower end `nl / 2 ^ del` of an interval of the bisection over `ℝ`, none for the end
`-LONG_MAX` at `-∞`. -/
noncomputable def lowerEnd (nl del : Int64) : Option ℝ :=
  if nl = -longMax then none else some (endValue nl del : ℝ)

/-- The upper end `nr / 2 ^ der` of an interval of the bisection over `ℝ`, none for the end
`LONG_MAX` at `+∞`. -/
noncomputable def upperEnd (nr der : Int64) : Option ℝ :=
  if nr = longMax then none else some (endValue nr der : ℝ)

/-- The real ends of an interval of the bisection are in order. -/
theorem EndsWF.lt_ends {depth : ℕ} {nl nr del der : Int64} (h : EndsWF depth nl nr del der) :
    ∀ a ∈ lowerEnd nl del, ∀ b ∈ upperEnd nr der, a < b := by
  intro a ha b hb
  by_cases hl : nl = -longMax
  · simp [lowerEnd, hl] at ha
  by_cases hr : nr = longMax
  · simp [upperEnd, hr] at hb
  simp only [lowerEnd, upperEnd, hl, hr, ↓reduceIte, Option.mem_def, Option.some.injEq] at ha hb
  rw [← ha, ← hb]
  exact_mod_cast h.lt

/-- The invariant of the bisection `Ratpoints.Sturm.iterate` on the interval from `nl / 2 ^ del`
to `nr / 2 ^ der` at the depth `depth`, for the real polynomial `F` whose chain it evaluates: an
interval of the bisection (`Ratpoints.Sturm.EndsWF`) whose counts `cl`, `cr` and signs `sl`, `sr`
are those of `F` at its ends (`Ratpoints.vLeft`, `Ratpoints.vRight`, `Ratpoints.sgnLeftEnd`,
`Ratpoints.sgnRightEnd`). -/
structure IterateInvariant (F : ℝ[X]) (depth : ℕ) (nl nr del der : Int64) (cl cr : ℕ) (sl sr : ℤ) :
    Prop where
  /-- An interval of the bisection at the depth. -/
  ends : EndsWF depth nl nr del der
  /-- The count at the lower end. -/
  cl_eq : cl = vLeft F (lowerEnd nl del)
  /-- The count at the upper end. -/
  cr_eq : cr = vRight F (upperEnd nr der)
  /-- The sign just inside the lower end. -/
  sl_eq : sl = sgnLeftEnd F (lowerEnd nl del)
  /-- The sign just inside the upper end. -/
  sr_eq : sr = sgnRightEnd F (upperEnd nr der)

/-- The values `x` that the bisection of an interval keeps: between the values of the doubles of
its ends, at a finite end only when `F` is positive just inside it. -/
def Kept (nl nr del der : Int64) (sl sr : ℤ) (x : ℚ) : Prop :=
  (endValue nl del < x ∨ x = endValue nl del ∧ (nl = -longMax ∨ 0 < sl)) ∧
    (x < endValue nr der ∨ x = endValue nr der ∧ (nr = longMax ∨ 0 < sr))

theorem Kept.le {nl nr del der : Int64} {sl sr : ℤ} {x : ℚ} (h : Kept nl nr del der sl sr x) :
    endValue nl del ≤ x ∧ x ≤ endValue nr der :=
  ⟨h.1.elim le_of_lt fun h ↦ h.1.ge, h.2.elim le_of_lt fun h ↦ h.1.le⟩

/-- A value that the bisection of an interval keeps lies between its real ends, or at a finite
end where `F` is positive just inside. -/
theorem Kept.inside_or {nl nr del der : Int64} {sl sr : ℤ} {x : ℚ}
    (h : Kept nl nr del der sl sr x) :
    Inside (lowerEnd nl del) (upperEnd nr der) x ∨ (nl ≠ -longMax ∧ x = endValue nl del ∧ 0 < sl) ∨
      (nr ≠ longMax ∧ x = endValue nr der ∧ 0 < sr) := by
  obtain ⟨h1, h2⟩ := h
  by_cases hl : nl = -longMax <;> by_cases hr : nr = longMax <;>
    simp only [Inside, lowerEnd, upperEnd, hl, hr, ↓reduceIte, Option.mem_def, reduceCtorEq,
      false_implies, implies_true, Option.some.injEq, forall_eq', true_and, and_true, Rat.cast_lt,
      ne_eq, not_true_eq_false, false_and, or_false, not_false_eq_true, false_or] at h1 h2 ⊢ <;>
    grind

/-- By Sturm's theorem, an interval that the bisection drops, with equal counts at its ends and `F`
negative just inside its lower end, holds no value `x` with `F(x) ≥ 0` that it would keep. -/
theorem IterateInvariant.not_kept (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F) {depth : ℕ}
    {nl nr del der : Int64} {cl cr : ℕ} {sl sr : ℤ}
    (hI : IterateInvariant F depth nl nr del der cl cr sl sr) (hc : cl = cr) (hsl : sl < 0) {x : ℚ}
    (hx : 0 ≤ F.eval (x : ℝ)) : ¬ Kept nl nr del der sl sr x := by
  have hs : sgnLeftEnd F (lowerEnd nl del) = -1 := by
    have := hI.sl_eq ▸ hsl
    revert this
    cases sgnLeftEnd F (lowerEnd nl del) <;> decide
  obtain ⟨hneg, hsr⟩ := eval_neg_of_vLeft_eq_vRight hS hF hI.ends.lt_ends
    (by rw [← hI.cl_eq, ← hI.cr_eq, hc]) hs
  have hsr' : sr < 0 := by rw [hI.sr_eq, hsr]; decide
  intro hcl
  rcases hcl.inside_or with h | h | h
  · exact (hneg _ h).not_ge hx
  · lia [h.2.2]
  · lia [h.2.2]

/-- The halves at the midpoint `m = nm / 2 ^ dem` of an interval of the bisection keep the
invariant with the counts and signs that `Ratpoints.Sturm.iterate` hands them, when `s0`, `s1` and
`cmid` are the signs of `F(m)` and `F'(m)` and the count `V(m)`. -/
theorem IterateInvariant.halves {F : ℝ[X]} {depth : ℕ} {nl nr del der : Int64} {cl cr : ℕ}
    {sl sr : ℤ} (hI : IterateInvariant F depth nl nr del der cl cr sl sr) (hd : depth < 55)
    {nm dem : Int64}
    (hm : midpoint nl nr del der = (nm, dem)) {s0 s1 : ℤ} {cmid : ℕ}
    (h0 : s0 = SignType.sign (F.eval (endValue nm dem : ℝ)))
    (h1 : s1 = SignType.sign (F.derivative.eval (endValue nm dem : ℝ)))
    (hc : cmid = sturmV F (endValue nm dem)) :
    IterateInvariant F (depth + 1) nl nm del dem cl (if s0 = 0 then cmid + 1 else cmid) sl
        (if s0 = 0 then -s1 else s0) ∧
      IterateInvariant F (depth + 1) nm nr dem der cmid cr (if s0 = 0 then s1 else s0) sr := by
  obtain ⟨hL, hR⟩ := hI.ends.halves hd
  rw [hm] at hL hR
  have hl : lowerEnd nm dem = some (endValue nm dem : ℝ) := by simp [lowerEnd, hL.right_ne]
  have hr : upperEnd nm dem = some (endValue nm dem : ℝ) := by simp [upperEnd, hR.left_ne]
  subst h0 h1 hc
  refine ⟨⟨hL, hI.cl_eq, ?_, hI.sl_eq, ?_⟩, ⟨hR, ?_, hI.cr_eq, ?_, hI.sr_eq⟩⟩ <;>
    simp only [hl, hr, vLeft, vRight, sgnLeftEnd, sgnRightEnd, IsRoot.def, SignType.coe_eq_zero,
      sign_eq_zero_iff] <;> split_ifs <;> simp

/-- A value `x` with `F(x) ≥ 0` that the bisection of an interval keeps is kept by one of its
halves at the midpoint `m`, with the signs that `Ratpoints.Sturm.iterate` hands them: at `m` itself
by the left half when `F(m) > 0` or `F'(m) < 0`, and by the right half when `F'(m) > 0`. -/
theorem kept_halves {F : ℝ[X]} (hF : Squarefree F) {nl nr del der nm dem : Int64}
    {sl sr s0 s1 : ℤ} (h0 : s0 = SignType.sign (F.eval (endValue nm dem : ℝ)))
    (h1 : s1 = SignType.sign (F.derivative.eval (endValue nm dem : ℝ))) {x : ℚ}
    (hx : 0 ≤ F.eval (x : ℝ)) (hc : Kept nl nr del der sl sr x) :
    Kept nl nm del dem sl (if s0 = 0 then -s1 else s0) x ∨
      Kept nm nr dem der (if s0 = 0 then s1 else s0) sr x := by
  rcases lt_trichotomy x (endValue nm dem) with h | rfl | h
  · exact .inl ⟨hc.1, .inl h⟩
  · rcases hx.lt_or_eq with hp | hz
    · exact .inl ⟨hc.1, .inr ⟨rfl, .inr (by simp [h0, sign_pos hp])⟩⟩
    have hz' : F.eval ((endValue nm dem : ℚ) : ℝ) = 0 := hz.symm
    rcases ((hF.eval_ne_zero_or_eval_derivative_ne_zero _).resolve_left
      (not_not.mpr hz')).lt_or_gt with hn | hp
    · exact .inl ⟨hc.1, .inr ⟨rfl, .inr (by simp [h0, h1, hz', sign_neg hn])⟩⟩
    · exact .inr ⟨.inr ⟨rfl, .inr (by simp [h0, h1, hz', sign_pos hp])⟩, hc.2⟩
  · exact .inr ⟨.inl h, hc.2⟩

/-- The intervals kept hold what they held, and every value between the ends of an interval of the
bisection, after the bisection keeps that interval. -/
theorem covers_addInterval {depth : ℕ} {nl nr del der : Int64} (hE : EndsWF depth nl nr del der)
    (hd : depth ≤ 55) {acc : Array (Double × Double)} (hacc : ∀ i ∈ acc.toList, IsInterval i)
    (hb : ∀ i ∈ acc.back?, doubleValue i.2.bits ≤ (endValue nl del : WithBotTop ℚ)) {sl sr : ℤ} :
    (∀ x, InIntervals (domainValues acc.toList) x →
      InIntervals (domainValues (addInterval acc nl nr del der).toList) x) ∧
    ∀ x, Kept nl nr del der sl sr x →
      InIntervals (domainValues (addInterval acc nl nr del der).toList) x := by
  refine ⟨fun x hx ↦ ?_, fun x hc ↦ ?_⟩ <;> rw [inIntervals_domainValues_iff] at *
  · exact exists_mem_addInterval_of_exists_mem hacc hb (hE.hasValue_right hd) hE.lt hx
  · exact exists_mem_addInterval hacc (hE.hasValue_left hd) (hE.hasValue_right hd)
      ⟨WithBotTop.coe_le_coe.mpr hc.le.1, WithBotTop.coe_le_coe.mpr hc.le.2⟩

/-- The signs and the count that `Ratpoints.Sturm.signsAt` computes for the chain `rows` at the
finite points `nm / 2 ^ dem` with `0 ≤ dem ≤ 55` are those of the real polynomial `F`. -/
def SignsOf (F : ℝ[X]) (rows : Array (Array ℤ)) (k : ℕ) : Prop :=
  ∀ nm dem : Int64, nm ≠ longMax → nm ≠ -longMax → 0 ≤ dem.toInt → dem.toInt ≤ 55 →
    Id.run (signsAt rows k nm dem) = ((SignType.sign (F.eval (endValue nm dem : ℝ)) : ℤ),
      (SignType.sign (F.derivative.eval (endValue nm dem : ℝ)) : ℤ), sturmV F (endValue nm dem))

/-- The signs and the count at the midpoint of an interval of the bisection, below the depth
`55`. -/
theorem SignsOf.midpoint {F : ℝ[X]} {rows : Array (Array ℤ)} {k : ℕ} (h : SignsOf F rows k)
    {depth : ℕ} {nl nr del der nm dem : Int64} (hE : EndsWF depth nl nr del der) (hd : depth < 55)
    (hm : midpoint nl nr del der = (nm, dem)) {s0 s1 : ℤ} {cmid : ℕ}
    (hs : Id.run (signsAt rows k nm dem) = (s0, s1, cmid)) :
    s0 = SignType.sign (F.eval (endValue nm dem : ℝ)) ∧
      s1 = SignType.sign (F.derivative.eval (endValue nm dem : ℝ)) ∧
      cmid = sturmV F (endValue nm dem) := by
  obtain ⟨hL, hR⟩ := hE.halves hd
  rw [hm] at hL hR
  have := h nm dem hR.left_ne hL.right_ne hL.zero_le_der (by lia [hL.der_le])
  rwa [hs, Prod.mk.injEq, Prod.mk.injEq] at this

/-- By Sturm's theorem, the bisection `Ratpoints.Sturm.iterate` of an interval with the invariant
`Ratpoints.Sturm.IterateInvariant` of a squarefree `F`, up to the depth `iter ≤ 55`, keeps what the
intervals kept so far hold, and every value with `F ≥ 0` that it keeps
(`Ratpoints.Sturm.Kept`). -/
theorem covers_iterate (hS : SturmTheorem) {F : ℝ[X]} (hF : Squarefree F)
    {rows : Array (Array ℤ)} {k iter : ℕ} (hsig : SignsOf F rows k) (hit : iter ≤ 55)
    {nl nr del der : Int64} {cl cr : ℕ} {sl sr : ℤ} {depth : ℕ} {acc : Array (Double × Double)}
    (hI : IterateInvariant F depth nl nr del der cl cr sl sr) (hd : depth ≤ iter)
    (hacc : AreIntervals acc.toList)
    (hb : ∀ i ∈ acc.back?, doubleValue i.2.bits ≤ (endValue nl del : WithBotTop ℚ)) :
    (∀ x, InIntervals (domainValues acc.toList) x → InIntervals (domainValues
      (Id.run (iterate rows k iter nl nr del der cl cr sl sr depth acc)).toList) x) ∧
    ∀ x : ℚ, 0 ≤ F.eval (x : ℝ) → Kept nl nr del der sl sr x → InIntervals (domainValues
      (Id.run (iterate rows k iter nl nr del der cl cr sl sr depth acc)).toList) x := by
  fun_induction iterate rows k iter nl nr del der cl cr sl sr depth acc with
  | case1 _ _ _ _ _ _ _ _ _ _ h =>
    exact ⟨fun x hx ↦ hx, fun x hx hc ↦ absurd hc (hI.not_kept hS hF h.1 h.2 hx)⟩
  | case2 nl nr del der cl cr sl sr depth acc =>
    obtain ⟨h1, h2⟩ := covers_addInterval (sl := sl) (sr := sr) hI.ends (by lia) hacc.1 hb
    exact ⟨h1, fun x _ ↦ h2 x⟩
  | case3 nl nr del der cl cr sl sr depth acc _ hk nm dem hm ih2 ih1 =>
    simp only [Id.run_bind]
    rcases hs : Id.run (signsAt rows k nm dem) with ⟨s0, s1, cmid⟩
    obtain ⟨h0, h1, hc⟩ := hsig.midpoint hI.ends (by lia) hm hs
    obtain ⟨hIL, hIR⟩ := hI.halves (by lia) hm h0 h1 hc
    obtain ⟨hwf, hb'⟩ := iterate_wf (rows := rows) (k := k) hIL.ends hit (by lia) hacc hb
    obtain ⟨m1, c1⟩ := ih2 s0 s1 cmid hIL (by lia) hacc hb
    obtain ⟨m2, c2⟩ := ih1 s0 s1 cmid _ hIR (by lia) hwf hb'
    refine ⟨fun x hx ↦ m2 x (m1 x hx), fun x hx hcl ↦ ?_⟩
    rcases kept_halves hF h0 h1 hx hcl with h | h
    exacts [m2 x (c1 x hx h), c2 x hx h]

/-- The real polynomial of the chain of `c` and `d` is squarefree when the chain succeeds: over `ℚ`
by `Ratpoints.Sturm.run_chain_eq_none_iff`, and a separable polynomial stays separable over
`ℝ`. -/
theorem squarefree_chainPoly {c : List ℤ} {d : ℕ} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0)
    {rows : Array (Array ℤ)} (h : Id.run (chain c d) = some rows) :
    Squarefree (chainPoly c d) := by
  exact (PerfectField.separable_iff_squarefree.mpr
    (not_not.mp ((run_chain_eq_none_iff hd hc).not.mp (by simp [h])))).map.squarefree

/-- The invariant of the bisection on the whole line, with the counts and signs of `F` at `∓∞`. -/
theorem iterateInvariant_zero (F : ℝ[X]) :
    IterateInvariant F 0 (-longMax) longMax 0 0 (vBot F) (vTop F) (sgnLeftEnd F none)
      (sgnRightEnd F none) :=
  ⟨endsWF_zero, by simp [lowerEnd, vLeft], by simp [upperEnd, vRight], by simp [lowerEnd],
    by simp [upperEnd]⟩

/-- The bisection of the whole line keeps every value `x` with `|x| ≤ 2 ^ 63`, the values of the
doubles of its ends `∓LONG_MAX`. -/
theorem kept_neg_longMax_longMax_of_abs_le {sl sr : ℤ} {x : ℚ} (hx : |x| ≤ 2 ^ 63) :
    Kept (-longMax) longMax 0 0 sl sr x := by
  have h1 : endValue (-longMax) 0 = -2 ^ 63 := by simp [endValue, show -longMax ≠ longMax by decide]
  have h2 : endValue longMax 0 = 2 ^ 63 := by simp [endValue]
  rw [Kept, h1, h2]
  obtain ⟨hl, hr⟩ := abs_le.mp hx
  exact ⟨hl.lt_or_eq.imp id fun h ↦ ⟨h.symm, .inl rfl⟩, hr.lt_or_eq.imp id fun h ↦ ⟨h, .inl rfl⟩⟩

theorem eval_zero_chainPoly (c : List ℤ) (d : ℕ) : (chainPoly c d).eval 0 = c.getD 0 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_map, coeff_poly]
  simp [List.getD_eq_getElem?_getD]

/-- For a chain whose last row is constant, of a polynomial of degree `d < 2 ^ 57` that is
squarefree over `ℝ`, `Ratpoints.Sturm.signsAt` computes the signs and the count of the real
polynomial (`Ratpoints.Sturm.IsChain.run_signsAt_eq`). -/
theorem IsChain.signsOf {c : List ℤ} {d : ℕ} {rows : Array (Array ℤ)} (h : IsChain c d rows)
    (h1 : rows.back!.size = 1) (hd : d < 2 ^ 57) (hF : Squarefree (chainPoly c d)) :
    SignsOf (chainPoly c d) rows (rows.size - 1) := fun nm dem hl hr h0 h55 ↦ by
  rw [h.run_signsAt_eq h1 hd hF nm h0 h55, endValue_eq_div hl hr h0]

/-- The sign of the real polynomial of a chain at `+∞`, that of `c_d`. -/
theorem IsChain.sgnRightEnd_none {c : List ℤ} {d : ℕ} {rows : Array (Array ℤ)}
    (h : IsChain c d rows) : (sgnRightEnd (chainPoly c d) none : ℤ) = (c.getD d 0).sign := by
  have := h.sign_leadingCoeff_map (n := 0) (by lia [h.two_le_size])
  rw [h.poly_toList_getElem!_zero] at this
  rw [sgnRightEnd, this]
  simp [signAtTop, h.getElem!_zero]

/-- The sign of the real polynomial of a chain at `-∞`, that of `c_d`, negated for odd `d`. -/
theorem IsChain.sgnLeftEnd_none {c : List ℤ} {d : ℕ} {rows : Array (Array ℤ)}
    (h : IsChain c d rows) : (sgnLeftEnd (chainPoly c d) none : ℤ) =
      if d % 2 = 1 then -(c.getD d 0).sign else (c.getD d 0).sign := by
  have := h.sign_neg_one_pow_mul_leadingCoeff_map (n := 0) (by lia [h.two_le_size])
  rw [h.poly_toList_getElem!_zero] at this
  rw [sgnLeftEnd, this]
  simp [signAtBot, signAtTop, h.getElem!_zero]

/-- A chain that succeeds on a polynomial of degree `d ≥ 1` with `c_d ≠ 0`: a chain whose last row
is constant. -/
theorem isChain_of_run_chain_eq_some {c : List ℤ} {d : ℕ} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0)
    {rows : Array (Array ℤ)} (h : Id.run (chain c d) = some rows) :
    IsChain c d rows ∧ rows.back!.size = 1 := by
  simpa [h, IsChainResult] using isChainResult_run_chain hd hc

/-- By Sturm's theorem, the Sturm step at a depth of at most `55` on a polynomial of degree
`1 ≤ d < 2 ^ 57` with `c_d ≠ 0`, for well-formed intervals of the caller, leaves intervals that hold
every value `x` with `|x| ≤ 2 ^ 63` and `f(x) ≥ 0` in the caller's intervals. -/
theorem covers_computeSturm (hS : SturmTheorem) {c : List ℤ} {d iter : ℕ}
    {ivs iv' : Array (Double × Double)} (hd : 1 ≤ d) (hcd : c.getD d 0 ≠ 0) (hd57 : d < 2 ^ 57)
    (hit : iter ≤ 55) (hwf : IntervalsWF (domainBits ivs.toList))
    (h : Id.run (computeSturm c d iter ivs) = some iv') {x : ℚ}
    (hx : 0 ≤ (chainPoly c d).eval (x : ℝ)) (hb : |x| ≤ 2 ^ 63)
    (hxi : InIntervals (domainValues ivs.toList) x) : InIntervals (domainValues iv'.toList) x := by
  rcases hc : Id.run (chain c d) with _ | rows
  · rw [← run_computeSturm_eq_none_iff c d iter ivs] at hc
    simp [hc] at h
  obtain ⟨hch, h1⟩ := isChain_of_run_chain_eq_some hd hcd hc
  have hF := squarefree_chainPoly hd hcd hc
  rw [run_computeSturm_of_chain_eq_some hc, hch.run_countsAtInfinity_eq h1] at h
  by_cases hex : vBot (chainPoly c d) = vTop (chainPoly c d) ∧ c.getD 0 0 < 0
  · exact absurd hx (not_le.mpr (eval_neg_of_vBot_eq_vTop hS hF hex.1
      (by rw [eval_zero_chainPoly]; exact_mod_cast hex.2) x))
  rw [ite_eq_right hex, Option.some.injEq] at h
  subst h
  rw [← hch.sgnLeftEnd_none, ← hch.sgnRightEnd_none, toList_run_intersect]
  exact inIntervals_intersectList ((intervalsWF_domainBits_iff _).mpr
    (areIntervals_run_iterate_zero hit)) hwf ((covers_iterate hS hF (hch.signsOf h1 hd57 hF) hit
      (iterateInvariant_zero _) (by lia) .nil nofun).2 x hx
        (kept_neg_longMax_longMax_of_abs_le hb)) hxi

/-- The value of the real polynomial of the chain of `c` and its degree at a rational point. -/
theorem eval_chainPoly_degree (c : List ℤ) (q : ℚ) :
    (chainPoly c (degree c)).eval (q : ℝ) = ((poly c).eval q : ℚ) := by
  rw [chainPoly, poly_take_of_degree_lt (Nat.lt_succ_self _), eval_ratCast_map]
  rfl

/-- The real polynomial of the chain of `c` and its degree is not negative at `a / b`, `b > 0`,
when the binary form is not negative at `(a, b)`. -/
theorem eval_chainPoly_nonneg {c : List ℤ} {a : ℤ} {b : ℕ} (hb : 0 < b)
    (h : 0 ≤ binaryForm c a b) : 0 ≤ (chainPoly c (degree c)).eval (((a : ℚ) / b : ℚ) : ℝ) := by
  have h' := binaryForm_eq_mul_eval (c := c) a (b := b) (by lia)
  rw [Int.cast_natCast] at h'
  have hpos : (0 : ℚ) < (b : ℚ) ^ (degree c + degree c % 2) := by positivity
  have h2 : (0 : ℚ) ≤ (b : ℚ) ^ (degree c + degree c % 2) * (poly c).eval ((a : ℚ) / b) := by
    rw [← h']; exact_mod_cast h
  rw [eval_chainPoly_degree]
  exact_mod_cast (mul_nonneg_iff_of_pos_left hpos).mp h2

end Sturm

end Ratpoints

end
