/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov
-/
module

public import LeanPool.ConwaySoifer.Certificates.Witness
import Mathlib.Tactic

/-! Extensional checkpoint lemmas for kernel-checked certificate replay.
Concrete checkpoints are untrusted data; every transition is proved in Lean. -/

/-
Adapted from https://github.com/AnanasClassic/conway-soifer-n3-lean
at b71b1d22b6f7ebb0f0173fc70a66075f44c86ce6 (public release: 11 September 2026).
The original MIT grant is retained below; the Lean Pool adaptation is released under Apache 2.0.

MIT License

Copyright (c) 2026 Vladislav Kuznetsov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

@[expose] public section

namespace ConwaySoifer.Certificates

/-- Two replay models agree when all owner fields agree. -/
theorem Model.ext_fields (M N : Model)
    (hB : ∀ j, M.B j = N.B j) (hc : ∀ j, M.caps j = N.caps j)
    (ho : ∀ j, M.ord j = N.ord j) : M = N := by
  cases M
  cases N
  rw [Model.mk.injEq]
  exact ⟨funext hB, funext hc, funext ho⟩

/-- A concrete model is the initial model if initialization succeeds and each field agrees. -/
theorem initial_checkpoint (o : Option Model) (M : Model)
    (hs : o.isSome = true)
    (hB : ∀ j, (o.getD ⟨fun _ => [], fun _ => [], fun _ => none⟩).B j = M.B j)
    (hc : ∀ j, (o.getD ⟨fun _ => [], fun _ => [], fun _ => none⟩).caps j = M.caps j)
    (ho : ∀ j, (o.getD ⟨fun _ => [], fun _ => [], fun _ => none⟩).ord j = M.ord j) :
    o = some M := by
  cases o with
  | none => simp at hs
  | some N => exact congrArg some (Model.ext_fields N M hB hc ho)

/-- An exclusion holds for every triangle and parameter in a closed interval. -/
def ExcludedOn (Ps : List IPoint) (den : Int) (caps : List Cap) (ord : Option (Fin 6))
    (a b d : Int) : Prop :=
  ∀ (U : EquilateralTriangle) (x : ℝ), 0 < x → (a : ℝ) / d ≤ x → x ≤ (b : ℝ) / d →
    Ctx U (den : ℝ) x Ps caps ord → False

/-- A forced-point step preserves the semantic model throughout the interval. -/
def StepValid (M : Model) (den : Int) (st : Step) (a b d : Int) : Prop :=
  ∀ (T : Configuration) (x : ℝ), 0 < x → (a : ℝ) / d ≤ x → x ≤ (b : ℝ) / d →
    ModelHolds M T (den : ℝ) x → ModelHolds (M.insert st) T (den : ℝ) x

/-- A model cannot hold at any positive parameter in the interval. -/
def ModelImpossible (M : Model) (den a b d : Int) : Prop :=
  ∀ (T : Configuration) (x : ℝ), 0 < x → (a : ℝ) / d ≤ x → x ≤ (b : ℝ) / d →
    ModelHolds M T (den : ℝ) x → False

/-- The same semantic certificate contract as `CertData.check_sound`. -/
def CertData.Valid (C : CertData) : Prop :=
  0 < C.den ∧ 0 ≤ C.lo ∧ C.lo < C.hi ∧ C.hi ≤ 11 / 25 ∧
    ∃ M, initModel C.case C.lo C.hi C.den = some M ∧
      ∀ (T : Configuration) (x : ℝ), 0 < x → x ≤ ((C.hi - C.lo : Rat) : ℝ) →
        ModelHolds M T (C.den : ℝ) x → False

/-- Ownership follows from target membership and the rejection of every other owner. -/
theorem step_checkpoint (M : Model) (den : Int) (st : Step) (a b d : Int) (fuel : Nat)
    (hden : 0 < den) (hd : 0 < d) (hq : inTarget st.q den a b d fuel = true)
    (he : ∀ j, j ≠ st.owner → ExcludedOn (M.B j ++ [st.q]) den (M.caps j) (M.ord j) a b d) :
    StepValid M den st a b d := by
  intro T x hx hlo hhi H
  have hmem : realPt (den : ℝ) st.q x ∈ (T st.owner).carrier := by
    obtain ⟨j, hj⟩ := H.covers _ (inTarget_sound rfl hden hd hq hlo hhi)
    by_cases ho : j = st.owner
    · simpa only [ho] using hj
    · exfalso
      apply he j ho (T j) x hx hlo hhi
      refine ⟨H.side_pos j, H.side_lt j, ?_, H.cap j, H.ord j⟩
      intro P hP
      rcases List.mem_append.mp hP with hP | hP
      · exact H.mem j P hP
      · rw [List.mem_singleton] at hP; subst hP; exact hj
  refine ⟨H.side_pos, H.side_lt, H.covers, ?_, H.cap, H.ord⟩
  intro j P hP
  simp only [Model.insert] at hP
  split_ifs at hP with hj
  · subst hj
    rcases List.mem_append.mp (mem_thinHullChecked hP) with hP | hP
    · exact H.mem _ P hP
    · rw [List.mem_singleton] at hP; subst hP; exact hmem
  · exact H.mem j P hP

/-- Compose a forced step, a checked state equality, and the remaining contradiction. -/
theorem replay_checkpoint (M N : Model) (den a b d : Int) (st : Step)
    (hn : M.insert st = N) (hs : StepValid M den st a b d)
    (ht : ModelImpossible N den a b d) : ModelImpossible M den a b d := by
  intro T x hx hlo hhi H
  apply ht T x hx hlo hhi
  rw [← hn]
  exact hs T x hx hlo hhi H

/-- Excluding the last owner's mandatory points contradicts the final model. -/
theorem final_checkpoint (M : Model) (den a b d : Int) (last : Fin 10)
    (h : ExcludedOn (M.B last) den (M.caps last) (M.ord last) a b d) :
    ModelImpossible M den a b d := by
  intro T x hx hlo hhi H
  exact h (T last) x hx hlo hhi (H.ctx last)

/-- Assemble the exact original interval contract from the checked initial model. -/
theorem certificate_checkpoint (C : CertData) (M : Model) (den b d : Int)
    (hd : 0 < C.den) (hlo : 0 ≤ C.lo) (hlt : C.lo < C.hi) (hhi : C.hi ≤ 11 / 25)
    (hm : initModel C.case C.lo C.hi C.den = some M)
    (hden : C.den = den) (hb : (C.hi - C.lo).num = b)
    (hwidth : ((C.hi - C.lo).den : Int) = d)
    (hr : ModelImpossible M den 0 b d) : C.Valid := by
  refine ⟨hd, hlo, hlt, hhi, M, hm, ?_⟩
  intro T x hx hxw H
  have hcast : (b : ℝ) / (d : ℝ) = ((C.hi - C.lo : Rat) : ℝ) := by
    rw [← hb, ← hwidth, Rat.cast_def]
    push_cast
    rfl
  apply hr T x hx
  · simpa only [Int.cast_zero, zero_div] using hx.le
  · rw [hcast]; exact hxw
  · simpa only [hden] using H

end ConwaySoifer.Certificates
