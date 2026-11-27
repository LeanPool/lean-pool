/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.EffectiveOpen

/-!
# Effective existential search

A computably enumerable relation remains computably enumerable after an
existential quantifier over any primitively encodable type. The proof dovetails
over both possible witnesses and bounded computation stages. In particular, it
does not wait forever for an unsuccessful candidate witness.
-/

@[expose] public section

namespace Klr

/-- Existential projection preserves computable enumerability. -/
theorem rePred_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {W : α × β → Prop} (hW : REPred W) : REPred (fun a => ∃ b, W (a, b)) := by
  obtain ⟨c, hc⟩ := exists_programAccepts hW
  let search (a : α) (k : ℕ) : Option ℕ :=
    (Encodable.decode (α := β × ℕ) k).bind fun bt =>
      Nat.Partrec.Code.evaln bt.2 c (Encodable.encode (a, bt.1))
  have hbounded : Computable₂ (fun (p : α × ℕ) (bt : β × ℕ) =>
      Nat.Partrec.Code.evaln bt.2 c (Encodable.encode (p.1, bt.1))) :=
    (Nat.Partrec.Code.primrec_evaln.to_comp.comp
      (((Computable.snd.comp Computable.snd).pair (Computable.const c)).pair
        (Computable.encode.comp ((Computable.fst.comp Computable.fst).pair
          (Computable.fst.comp Computable.snd))))).to₂
  have hsearch : Computable₂ search :=
    (Computable.option_bind (Computable.decode.comp Computable.snd) hbounded).to₂
  apply (Partrec.rfindOpt hsearch).dom_re.of_eq
  intro a
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨k, x, hx⟩
    obtain ⟨⟨b, t⟩, _, hbt⟩ := Option.mem_bind_iff.mp hx
    refine ⟨b, (hc (a, b)).mp ?_⟩
    exact Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound hbt⟩
  · rintro ⟨b, hb⟩
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp ((hc (a, b)).mpr hb)
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    refine ⟨Encodable.encode (b, t), x, ?_⟩
    simpa [search] using ht

end Klr
