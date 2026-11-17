/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/AntichainDecoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticAtoms
public import LeanPool.TuringConeRigidity.Syntax.BoundedDecoding

/-!
# Antichain Decoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.AntichainDecoding
open IndexPresentation ArithmeticHierarchy SetCoding BoundedDecoding

/-- The represented degree lies below `b` and has a nontrivial common lower degree after both
joins. -/
def Nontrivial (Y : Oracle) (b l r x : ℕ) : Prop :=
  LE Y x b ∧ ∃ z, Dom Y z ∧ LE Y z (joinIndex l x) ∧
    LE Y z (joinIndex r x) ∧ ¬ LE Y z x

/-- Minimality among the represented degrees satisfying the nontrivial common-lower property. -/
def Minimal (Y : Oracle) (b l r x : ℕ) : Prop :=
  ∀ w, Dom Y w → Nontrivial Y b l r w → LE Y w x → LE Y x w

/-- The conjunction of the represented nontriviality and minimality properties. -/
def Antichain (Y : Oracle) (b l r x : ℕ) : Prop :=
  Nontrivial Y b l r x ∧ Minimal Y b l r x

theorem nontrivial_sigma (Y : Oracle) {b l r x : ℕ → ℕ}
    (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Sigma Y 4 (fun v => Nontrivial Y (b v) (l v) (r v) (x v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hdom : Sigma Y 4 (fun v => Dom Y (Nat.unpair v).2) := (dom_pi Y s).switch.raise
  have h₀ := (le_sigma Y s (joinIndex_primrec.comp (hl.comp f) (hx.comp f))).raise
  have h₁ := (le_sigma Y s (joinIndex_primrec.comp (hr.comp f) (hx.comp f))).raise
  have hn : Sigma Y 4 (fun v => ¬ LE Y (Nat.unpair v).2 (x (Nat.unpair v).1)) :=
    (le_sigma Y s (hx.comp f)).neg.switch
  have hw := (hdom.and (h₀.and (h₁.and hn))).ex
  exact ((le_sigma Y hx hb).raise.and hw).congr (fun v => by
    simp only [Nat.unpair_pair]; rfl)

theorem minimal_pi (Y : Oracle) {b l r x : ℕ → ℕ}
    (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Pi Y 4 (fun v => Minimal Y (b v) (l v) (r v) (x v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hd : Pi Y 4 (fun v => ¬ Dom Y (Nat.unpair v).2) := (dom_pi Y s).neg.switch.raise
  have hn := (nontrivial_sigma Y (hb.comp f) (hl.comp f) (hr.comp f) s).neg
  have hw : Pi Y 4 (fun v => ¬ LE Y (Nat.unpair v).2 (x (Nat.unpair v).1)) :=
    (le_sigma Y s (hx.comp f)).neg.raise
  have hxw : Pi Y 4 (fun v => LE Y (x (Nat.unpair v).1) (Nat.unpair v).2) :=
    (le_sigma Y (hx.comp f) s).switch
  exact ((hd.or (hn.or (hw.or hxw))).all).congr (fun v => by
    simp only [Nat.unpair_pair, Minimal, imp_iff_not_or])

theorem antichain_sigma (Y : Oracle) {b l r x : ℕ → ℕ}
    (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Sigma Y 5 (fun v => Antichain Y (b v) (l v) (r v) (x v)) :=
  (nontrivial_sigma Y hb hl hr hx).raise.and (minimal_pi Y hb hl hr hx).switch

theorem nontrivial_iff {Y : Oracle} {b l r x : ℕ}
    (hb : Dom Y b) (hl : Dom Y l) (hr : Dom Y r) (hx : Dom Y x) :
    Nontrivial Y b l r x ↔ LocalNontrivial (degree Y)
      (value Y b) (value Y l) (value Y r) (value Y x) := by
  unfold Nontrivial LocalNontrivial
  rw [le_iff hx hb]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z, hz, h₀, h₁, hn⟩
    refine ⟨value Y z, value_below Y z, ?_, ?_, ?_⟩
    · simpa only [join_value hl hx] using (le_iff hz (join_dom hl hx)).mp h₀
    · simpa only [join_value hr hx] using (le_iff hz (join_dom hr hx)).mp h₁
    · exact fun he => hn ((le_iff hz hx).mpr he)
  · rintro ⟨z, hz, h₀, h₁, hn⟩
    obtain ⟨w, hw, rfl⟩ := value_surjective Y z hz
    exact ⟨w, hw, (le_iff hw (join_dom hl hx)).mpr (by simpa only [join_value hl hx] using h₀),
      (le_iff hw (join_dom hr hx)).mpr (by simpa only [join_value hr hx] using h₁),
      fun he => hn ((le_iff hw hx).mp he)⟩

theorem antichain_iff {Y : Oracle} {b l r x : ℕ}
    (hb : Dom Y b) (hl : Dom Y l) (hr : Dom Y r) (hx : Dom Y x) :
    Antichain Y b l r x ↔ (AntichainCode.mk (value Y b) (value Y l) (value Y r)).Holds
      (value Y x) := by
  rw [← local_antichain_iff (degree Y) _ ⟨value_below Y b, value_below Y l, value_below Y r⟩]
  unfold Antichain LocalAntichain
  rw [nontrivial_iff hb hl hr hx]
  apply and_congr_right
  intro _
  constructor
  · intro hm w hw hn hle
    obtain ⟨i, hi, rfl⟩ := value_surjective Y w hw
    exact (le_iff hx hi).mp (hm i hi ((nontrivial_iff hb hl hr hi).mpr hn)
      ((le_iff hi hx).mpr hle))
  · intro hm w hw hn hle
    exact (le_iff hx hw).mpr (hm (value Y w) (value_below Y w)
      ((nontrivial_iff hb hl hr hw).mp hn) ((le_iff hw hx).mp hle))

end TuringRigidity.AntichainDecoding

end OAI
