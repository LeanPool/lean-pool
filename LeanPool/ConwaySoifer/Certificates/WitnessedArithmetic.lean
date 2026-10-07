/-
Copyright (c) 2026 Vladislav Kuznetsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Kuznetsov, Lean Pool contributors
-/
module

public import LeanPool.ConwaySoifer.Certificates.CheckerSound
import Mathlib.Tactic

/-! Explicit arithmetic witnesses avoid re-running proposal searches in the kernel. -/

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
open IPoly

variable {U : EquilateralTriangle} {den x : ℝ} {Ps : List IPoint}
  {caps : List Cap} {ord : Option (Fin 6)}

/-- Check the distance obstruction for two supplied indices, without searching other pairs. -/
def pairCheck (Ps : List IPoint) (den : Int) (i j : Nat) (a b d : Int) (fuel : Nat) : Bool :=
  match nth Ps i, nth Ps j with
  | some P, some Q => nonnegOn (sub (normP (psub Q P)) [den * den]) a b d fuel
  | _, _ => false

theorem pairCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {i j : Nat} {a b d : Int}
    (hd : 0 < d) {fuel : Nat} (h : pairCheck Ps denI i j a b d fuel = true)
    (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) : False := by
  unfold pairCheck at h
  split at h
  · next P Q hP hQ =>
    have hb := nonnegOn_sound _ a b d fuel h hd x hlo hhi
    rw [evalR_sub, evalR_normP, evalF_psub] at hb
    simp only [evalR_cons, evalR_nil, mul_zero, add_zero] at hb
    push_cast at hb
    have hdenR : (0 : ℝ) < den := by
      rw [← hden]; exact_mod_cast hdpos
    have hdist : 1 ≤ sqDist (realPt den Q x) (realPt den P x) := by
      rw [sqDist_realPt]
      have hn : normSq (evalF Q x - evalF P x) ≥ den ^ 2 := by
        rw [← hden]
        linarith
      calc
        (1 : ℝ) = den⁻¹ ^ 2 * den ^ 2 := by
          field_simp
        _ ≤ den⁻¹ ^ 2 * normSq (evalF Q x - evalF P x) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
    exact U.cannot_contain_unit_chord C.side_lt hdist
      (C.mem Q (nth_mem _ _ hQ)) (C.mem P (nth_mem _ _ hP))
  · simp at h

/-- A support triple, or a request to use the cap checker. -/
abbrev BoundWitness := Option Triple

/-- Check a supplied support triple or cap obstruction at a single direction. -/
def nodeWitnessCheck (Ps : List IPoint) (den : Int) (caps : List Cap)
    (witness : BoundWitness) (u : IPoint) (a b d : Int) (fuel : Nat) : Bool :=
  match witness with
  | some T => supportOK Ps den u T a b d fuel
  | none => capNode Ps caps u a b d fuel

/-- Check one supplied triple at both cone endpoints, or use a cap obstruction. -/
def coneWitnessCheck (Ps : List IPoint) (den : Int) (caps : List Cap)
    (witness : BoundWitness) (u v : IPoint) (a b d : Int) (fuel : Nat) : Bool :=
  match witness with
  | some T => supportOK Ps den u T a b d fuel && supportOK Ps den v T a b d fuel
  | none => capCone Ps caps u v a b d fuel

theorem nodeWitnessCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {witness : BoundWitness}
    {u : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : nodeWitnessCheck Ps denI caps witness u a b d fuel = true)
    (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d)
    (O : Orientation U) {t : ℝ} (ht : 0 < t) (hdir : O.dir = t • evalF u x) : False := by
  cases witness with
  | none => exact capNode_sound C hden hdpos hd h hx hlo hhi O ht hdir
  | some T =>
    have hb := supportOK_sound hdpos hd h hlo hhi
    rw [hden] at hb
    have hb' : HasBound den Ps x O.dir := by
      rw [hdir]
      exact hb.smul ht.le
    exact hb'.false C O

theorem coneWitnessCheck_sound (C : Ctx U den x Ps caps ord) {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {witness : BoundWitness}
    {u v : IPoint} {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : coneWitnessCheck Ps denI caps witness u v a b d fuel = true)
    (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d)
    (O : Orientation U) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hdir : O.dir = α • evalF u x + β • evalF v x) : False := by
  cases witness with
  | none => exact capCone_sound C hden hdpos hd h hx hlo hhi O hα hβ hdir
  | some T =>
    simp only [coneWitnessCheck, Bool.and_eq_true] at h
    have hb := supportOK_cone hdpos hd h.1 h.2 hlo hhi hα.le hβ.le
    rw [hden] at hb
    have hb' : HasBound den Ps x O.dir := by
      rw [hdir]; exact hb
    exact hb'.false C O

/-- Semantic rejection at both boundary rays and inside a cone covers its closed directions. -/
theorem reject_closed_cone (O : Orientation U) {u v : Point}
    (hu : ∀ t : ℝ, 0 < t → O.dir = t • u → False)
    (hv : ∀ t : ℝ, 0 < t → O.dir = t • v → False)
    (huv : ∀ α β : ℝ, 0 < α → 0 < β → O.dir = α • u + β • v → False)
    (hdet : 0 ≤ cross u v) (hu' : InArc u) (hu0 : u ≠ 0)
    (hv' : InArc v) (hv0 : v ≠ 0) (hO : InArc O.dir)
    (h1 : 0 ≤ cross u O.dir) (h2 : 0 ≤ cross O.dir v) : False := by
  have hO0 : O.dir ≠ 0 := by
    intro h0
    have hp := O.dir_pos
    rw [h0] at hp
    simp [normSq] at hp
  rcases lt_or_eq_of_le hdet with hpos | hzero
  · obtain ⟨α, β, hα, hβ, hdir⟩ := exists_nonneg_combo_of_cross hpos h1 h2
    rcases lt_or_eq_of_le hα with hα' | hα'
    · rcases lt_or_eq_of_le hβ with hβ' | hβ'
      · exact huv α β hα' hβ' hdir
      · rw [← hβ', zero_smul, add_zero] at hdir
        exact hu α hα' hdir
    · rw [← hα', zero_smul, zero_add] at hdir
      rcases lt_or_eq_of_le hβ with hβ' | hβ'
      · exact hv β hβ' hdir
      · rw [← hβ', zero_smul] at hdir
        exact hO0 hdir
  · have hpar : cross u O.dir = 0 := by
      obtain ⟨c, hc, hcv⟩ :=
        pos_of_parallel_in_arc hu0 hv0 hu'.1 hu'.2 hv'.1 hv'.2 hzero.symm
      rw [hcv, cross_smul_right] at h2
      have he : cross O.dir u = -cross u O.dir := cross_anticomm _ _
      nlinarith
    obtain ⟨t, ht, hdir⟩ :=
      pos_of_parallel_in_arc hu0 hO0 hu'.1 hu'.2 hO.1 hO.2 hpar
    exact hu t ht hdir

/-- A finite fan terminating at the fixed 120-degree endpoint, with explicit arithmetic bounds. -/
inductive FanWitness where
  | terminal (nodeLeft nodeRight cone : BoundWitness)
  | next (direction : IPoint) (node cone : BoundWitness) (rest : FanWitness)

/-- The arithmetic witness at the left boundary of a fan. -/
def FanWitness.first : FanWitness → BoundWitness
  | .terminal nodeLeft _ _ => nodeLeft
  | .next _ node _ _ => node

/-- Verify every fan cone, boundary ray, ordering determinant and intermediate arc condition. -/
def FanWitness.check (Ps : List IPoint) (den : Int) (caps : List Cap)
    (a b d : Int) (fuel : Nat) : FanWitness → IPoint → Bool
  | .terminal nodeLeft nodeRight cone, u =>
      nodeWitnessCheck Ps den caps nodeLeft u a b d fuel &&
      coneWitnessCheck Ps den caps cone u rotEastP a b d fuel &&
      nonnegOn (detP u rotEastP) a b d fuel &&
      nodeWitnessCheck Ps den caps nodeRight rotEastP a b d fuel
  | .next v node cone rest, u =>
      nodeWitnessCheck Ps den caps node u a b d fuel &&
      coneWitnessCheck Ps den caps cone u v a b d fuel &&
      nonnegOn (detP u v) a b d fuel && nodeCond v a b d fuel &&
      rest.check Ps den caps a b d fuel v

theorem FanWitness.first_checked {w : FanWitness} {denI a b d : Int} {fuel : Nat}
    {u : IPoint} (h : w.check Ps denI caps a b d fuel u = true) :
    nodeWitnessCheck Ps denI caps w.first u a b d fuel = true := by
  cases w with
  | terminal _ _ _ =>
    simp only [FanWitness.check, Bool.and_eq_true] at h
    exact h.1.1.1
  | next _ _ _ _ =>
    simp only [FanWitness.check, Bool.and_eq_true] at h
    exact h.1.1.1.1

theorem FanWitness.sound (C : Ctx U den x Ps caps ord) {denI : Int}
    (hden : (denI : ℝ) = den) (hdpos : 0 < denI) {a b d : Int} (hd : 0 < d)
    {fuel : Nat} (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d)
    (O : Orientation U) (hO : InArc O.dir) (w : FanWitness) :
    ∀ u : IPoint, w.check Ps denI caps a b d fuel u = true →
      InArc (evalF u x) → evalF u x ≠ 0 →
      0 ≤ cross (evalF u x) O.dir → 0 ≤ cross O.dir (rot eastDir) → False := by
  induction w with
  | terminal nodeLeft nodeRight cone =>
    intro u h hu' hu0 h1 h2
    simp only [FanWitness.check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hnu, hc⟩, hdet⟩, hnv⟩ := h
    have hdet' := nonnegOn_sound _ a b d fuel hdet hd x hlo hhi
    rw [evalR_detP] at hdet'
    apply reject_closed_cone O
      (fun t ht he => nodeWitnessCheck_sound C hden hdpos hd hnu hx hlo hhi O ht he)
      (fun t ht he => nodeWitnessCheck_sound C hden hdpos hd hnv hx hlo hhi O ht he)
      (fun α β hα hβ he => coneWitnessCheck_sound C hden hdpos hd hc hx hlo hhi O hα hβ he)
      hdet' hu' hu0
      (by rw [evalF_rotEastP]; exact inArc_rotEast)
      (by rw [evalF_rotEastP]; exact rotEast_ne_zero) hO h1
    rw [evalF_rotEastP]
    exact h2
  | next v node cone rest ih =>
    intro u h hu' hu0 h1 h2
    simp only [FanWitness.check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hnu, hc⟩, hdet⟩, hcond⟩, hrest⟩ := h
    have hdet' := nonnegOn_sound _ a b d fuel hdet hd x hlo hhi
    rw [evalR_detP] at hdet'
    obtain ⟨hv', hv0⟩ := nodeCond_sound hd hcond hx hlo hhi
    rcases le_total (cross (evalF v x) O.dir) 0 with hle | hge
    · have h2' : 0 ≤ cross O.dir (evalF v x) := by
        rw [cross_anticomm]
        linarith
      have hnv := FanWitness.first_checked hrest
      exact reject_closed_cone O
        (fun t ht he => nodeWitnessCheck_sound C hden hdpos hd hnu hx hlo hhi O ht he)
        (fun t ht he => nodeWitnessCheck_sound C hden hdpos hd hnv hx hlo hhi O ht he)
        (fun α β hα hβ he => coneWitnessCheck_sound C hden hdpos hd hc hx hlo hhi O hα hβ he)
        hdet' hu' hu0 hv' hv0 hO h1 h2'
    · exact ih v hrest hv' hv0 hge h2

theorem FanWitness.rejects (w : FanWitness) (C : Ctx U den x Ps caps ord)
    {denI : Int} (hden : (denI : ℝ) = den) (hdpos : 0 < denI)
    {a b d : Int} (hd : 0 < d) {fuel : Nat}
    (h : w.check Ps denI caps a b d fuel eastP = true)
    (hx : 0 < x) (hlo : (a : ℝ) / d ≤ x) (hhi : x ≤ (b : ℝ) / d) : False := by
  obtain ⟨O, hO1, hO2⟩ := U.exists_orientation_in_arc C.side_pos
  refine w.sound C hden hdpos hd hx hlo hhi O ⟨hO1, hO2⟩ eastP h ?_ ?_ ?_ hO2
  · rw [evalF_eastP]; simp [InArc, cross, eastDir, rot]
  · rw [evalF_eastP]; simp [eastDir]
  · rw [evalF_eastP]; exact hO1

end ConwaySoifer.Certificates
