/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteShuffleCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ShuffleRequirements

/-!
# Finite Shuffle Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.FiniteShuffleCertificate
open FiniteShuffle ShuffleRequirements GenericCoding

/-- A finite certificate uniformly meets `D` for every word of the selected length. -/
def Certificate (D : List Bool → Prop) (q : List Bool) : Prop :=
  ∃ k : ℕ, 2*k ≤ q.length ∧ ∀ s : List Bool, s.length = k →
    ∃ l ≤ k, D (initial (code (fun i => s.getD i false) (fun i => q.getD i false)) l)

theorem certificate_transfer (D : List Bool → Prop) (q : List Bool)
    (h : Certificate D q) : Transfer D q := by
  obtain ⟨k,hk,hs⟩ := h
  intro A
  obtain ⟨l,hl,hD⟩ := hs (initial A k) (prefix_length A k)
  refine ⟨_,hD,fun G hG => ?_⟩
  apply (realizes_initial _ _ _).mpr
  apply code_agree
  · intro i hi
    exact prefix_getD A k i (lt_of_lt_of_le hi hl)
  · exact hG.mono (by omega)

theorem certificate_mono (D : List Bool → Prop) {q r : List Bool}
    (hqr : q <+: r) (h : Certificate D q) : Certificate D r := by
  obtain ⟨k,hk,hs⟩ := h
  refine ⟨k,hk.trans hqr.length_le,fun s hsk => ?_⟩
  obtain ⟨l,hl,hD⟩ := hs s hsk
  refine ⟨l,hl,?_⟩
  have he : Agree l (code (fun i => s.getD i false) (fun i => q.getD i false))
      (code (fun i => s.getD i false) (fun i => r.getD i false)) :=
    code_agree (fun _ _ => rfl) (fun i hi => getD_of_prefix hqr i (by omega))
  rwa [←prefix_agree he]

theorem certificate_denseOpen (D : List Bool → Prop) (hD : DenseOpen D) :
    DenseOpen (Certificate D) := by
  refine ⟨?_,fun _ _ hqr h => certificate_mono D hqr h⟩
  intro p
  let G : Oracle := fun i => p.getD i false
  obtain ⟨m,H,hn,hGH,_,hall⟩ := all_extension D hD (p.length+1) G
  let q := initial H (2*m)
  refine ⟨q,?_,m,by simp [q],fun s _ => ?_⟩
  · rw [←prefix_default p]
    exact initial_prefix (by omega) (hGH.mono (by omega))
  · obtain ⟨l,hl,hDl⟩ := hall (fun i => s.getD i false)
    refine ⟨l,hl,?_⟩
    have he : Agree l (code (fun i => s.getD i false) (fun i => q.getD i false))
        (code (fun i => s.getD i false) H) :=
      code_agree (fun _ _ => rfl) (fun i hi => prefix_getD H (2*m) i (by omega))
    rwa [prefix_agree he]

end TuringRigidity.FiniteShuffleCertificate

end OAI
