/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/CodingSplitting.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.CodingOnePoint

/-!
# Coding Splitting
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CodingSplitting
open CodingForcing

def OnePoint (base : List Bool) (f : List Bool → Part ℕ) : Prop :=
  ∃ s m b v w, base <+: s ∧ base.length ≤ m ∧ m < s.length ∧ v ≠ w ∧
    v ∈ f s ∧ w ∈ f (s.set m b)

private theorem interpolate (base : List Bool) (f : List Bool → Part ℕ)
    (hmono : ∀ {s t}, s <+: t → ∀ v, v ∈ f s → v ∈ f t)
    (hdense : ∀ s, base <+: s → ∃ u v, v ∈ f (s ++ u))
    (u : List Bool) : ∀ v : List Bool, u.length = v.length →
      ∀ pre tail, base <+: pre → ∀ a b,
        a ∈ f (pre ++ u ++ tail) → b ∈ f (pre ++ v ++ tail) → a ≠ b → OnePoint base f := by
  induction u with
  | nil =>
    intro v hlen pre tail hpre a b ha hb hab
    have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
    subst v
    exact False.elim (hab (Part.mem_unique ha hb))
  | cons x u ih =>
    intro v hlen pre tail hpre a b ha hb hab
    cases v with
    | nil => simp at hlen
    | cons y v =>
      have hlen' : u.length = v.length := Nat.succ.inj hlen
      let mid := pre ++ (x :: v) ++ tail
      have hmid : base <+: mid := by
        simpa only [mid, List.append_assoc] using hpre.trans (List.prefix_append pre ((x :: v) ++
          tail))
      obtain ⟨extra, c, hc⟩ := hdense mid hmid
      have ha' : a ∈ f ((pre ++ (x :: u) ++ tail) ++ extra) :=
        hmono (List.prefix_append _ _) a ha
      have hb' : b ∈ f ((pre ++ (y :: v) ++ tail) ++ extra) :=
        hmono (List.prefix_append _ _) b hb
      by_cases hcb : c = b
      · apply ih v hlen' (pre ++ [x]) (tail ++ extra)
          (hpre.trans (List.prefix_append _ _)) a c
        · simpa only [List.append_assoc, List.cons_append, List.nil_append] using ha'
        · simpa only [mid, List.append_assoc, List.cons_append, List.nil_append] using hc
        · simpa only [hcb] using hab
      · refine ⟨mid ++ extra, pre.length, y, c, b,
          hmid.trans (List.prefix_append _ _), hpre.length_le, ?_, hcb, hc, ?_⟩
        · simp [mid]
        · have heq : (mid ++ extra).set pre.length y =
              (pre ++ (y :: v) ++ tail) ++ extra := by
            simp [mid, List.append_assoc, List.set_append_right]
          rw [heq]
          exact hb'

theorem onePoint_of_dense {base s t : List Bool} {f : List Bool → Part ℕ}
    (hmono : ∀ {s t}, s <+: t → ∀ v, v ∈ f s → v ∈ f t)
    (hdense : ∀ s, base <+: s → ∃ u v, v ∈ f (s ++ u))
    (hs : base <+: s) (ht : base <+: t) (a b : ℕ)
    (ha : a ∈ f s) (hb : b ∈ f t) (hab : a ≠ b) : OnePoint base f := by
  obtain ⟨u, rfl⟩ := hs
  obtain ⟨v, rfl⟩ := ht
  let L := max u.length v.length
  let u' := u ++ List.replicate (L - u.length) false
  let v' := v ++ List.replicate (L - v.length) false
  have hlu : u'.length = L := by simp only [u', List.length_append, List.length_replicate]; omega
  have hlv : v'.length = L := by simp only [v', List.length_append, List.length_replicate]; omega
  have ha' : a ∈ f (base ++ u') := by
    apply hmono (show base ++ u <+: base ++ u' from ?_) a ha
    exact ⟨List.replicate (L-u.length) false, by simp [u', List.append_assoc]⟩
  have hb' : b ∈ f (base ++ v') := by
    apply hmono (show base ++ v <+: base ++ v' from ?_) b hb
    exact ⟨List.replicate (L-v.length) false, by simp [v', List.append_assoc]⟩
  exact interpolate base f hmono hdense u' v' (hlu.trans hlv.symm)
    base [] List.prefix_rfl a b (by simpa using ha') (by simpa using hb') hab

theorem split_or_divergent_word {Y : Oracle} {e : OracleCode} {base s t : List Bool}
    (hs : base <+: s) (ht : base <+: t) (n a b : ℕ)
    (ha : a ∈ CommonIdeal.run Y e s n) (hb : b ∈ CommonIdeal.run Y e t n) (hab : a ≠ b) :
    OnePoint base (fun w => CommonIdeal.run Y e w n) ∨
      ∃ w, base <+: w ∧ ∀ u v, v ∉ CommonIdeal.run Y e (w ++ u) n := by
  by_cases hd : ∀ w, base <+: w → ∃ u v, v ∈ CommonIdeal.run Y e (w ++ u) n
  · exact Or.inl (onePoint_of_dense (fun h v hv => CommonIdeal.run_mono h n v hv)
      hd hs ht a b ha hb hab)
  · right
    push Not at hd
    exact hd

end TuringRigidity.CodingSplitting

end OAI
