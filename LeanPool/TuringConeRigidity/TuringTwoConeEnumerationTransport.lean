/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeEnumerationTransport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeIdealCopies
public import LeanPool.TuringConeRigidity.TuringConeEnumeration

/-!
# Transport entire enumeration codes between two ideal cones

One transported successor/payload pair records every output simultaneously.
Both parameter bounds are retained, and the specifications quantify over all
ambient degrees: bounded codes do not gain solutions outside the target ideal.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeEnumeration

open IdealInterpretation SetCoding RelationCoding BoundedDecoding
open ArithmeticModelDecoding ConeRelativeCoding TwoConeIdealCodes

noncomputable section

theorem transport_enumeration {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (c : ConeEnumeration.Enumeration a.val)
    (z : Set.Ici a)
    (haS : RelationAbove c.successor a.val) (haP : RelationAbove c.payload a.val)
    (hS : RelationBelow c.successor (val z)) (hP : RelationBelow c.payload (val z))
    (v : ℕ → Set.Ici a) (hv : ∀ n, val (v n) = c.output n) :
    ∃ d : ConeEnumeration.Enumeration b.val,
      (∀ n, d.output n = val (ρ (v n))) ∧
      RelationAbove d.successor b.val ∧ RelationAbove d.payload b.val ∧
      RelationBelow d.successor (val (ρ z)) ∧ RelationBelow d.payload (val (ρ z)) := by
  let S := liftRelation z c.successor haS hS
  let P := liftRelation z c.payload haP hP
  have hn (n : ℕ) : a.val ≤ c.node n ∧ c.node n ∈ I.carrier := by
    obtain ⟨tags, ht, _⟩ := (c.successor_spec (c.node n) (c.node (n + 1))).mpr ⟨n, rfl, rfl⟩
    exact ⟨(ht 0).1, I.lower ((ht 0).2.1.trans (hS.1 0).1) z.val.property⟩
  let node (n : ℕ) : Set.Ici a :=
    ⟨⟨c.node n, (hn n).2⟩, Set.mem_Ici.mpr (hn n).1⟩
  have heq (x : Set.Ici b) (k : ℕ) :
      val (ρ.symm x) = c.node k ↔ x = ρ (node k) := by
    constructor
    · intro h
      have h' : ρ.symm x = node k := Subtype.ext (Element.ext _ _ h)
      exact (ρ.apply_symm_apply x).symm.trans (congrArg ρ h')
    · intro h
      rw [h, ρ.symm_apply_apply]
  have hveq (x : Set.Ici b) (k : ℕ) :
      val (ρ.symm x) = c.output k ↔ x = ρ (v k) := by
    rw [← hv k]
    constructor
    · intro h
      have h' : ρ.symm x = v k := Subtype.ext (Element.ext _ _ h)
      exact (ρ.apply_symm_apply x).symm.trans (congrArg ρ h')
    · intro h
      rw [h, ρ.symm_apply_apply]
  have hi : Function.Injective (fun n => val (ρ (node n))) := by
    intro i j h
    have h' : node i = node j := ρ.injective (Subtype.ext (Element.ext _ _ h))
    exact c.injective (congrArg val h')
  have hs (x y : Set.Ici b) :
      ConeCoding.Holds b.val (S.map ρ).external (two (val x) (val y)) ↔
        ∃ k, x = ρ (node k) ∧ y = ρ (node (k + 1)) := by
    have hh := S.transport_two ρ (ρ.symm x) (ρ.symm y)
    simp only [ρ.apply_symm_apply, S, liftRelation_external] at hh
    rw [hh, c.successor_spec]
    exact exists_congr (fun k => and_congr (heq x k) (heq y (k + 1)))
  have hp (x y : Set.Ici b) :
      ConeCoding.Holds b.val (P.map ρ).external (two (val x) (val y)) ↔
        ∃ k, x = ρ (node k) ∧ y = ρ (v k) := by
    have hh := P.transport_two ρ (ρ.symm x) (ρ.symm y)
    simp only [ρ.apply_symm_apply, P, liftRelation_external] at hh
    rw [hh, c.payload_spec]
    exact exists_congr (fun k => and_congr (heq x k) (hveq y k))
  have hs' (x y : Degree) : ConeCoding.Holds b.val (S.map ρ).external (two x y) ↔
      ∃ k, x = val (ρ (node k)) ∧ y = val (ρ (node (k + 1))) := by
    constructor
    · intro h
      have hx : b.val ≤ x := by obtain ⟨_, ht, _⟩ := h; exact (ht 0).1
      have hy : b.val ≤ y := by obtain ⟨_, ht, _⟩ := h; exact (ht 1).1
      let x' : Set.Ici b := ⟨⟨x, (S.map ρ).coordinates_mem h 0⟩, Set.mem_Ici.mpr hx⟩
      let y' : Set.Ici b := ⟨⟨y, (S.map ρ).coordinates_mem h 1⟩, Set.mem_Ici.mpr hy⟩
      obtain ⟨k, hk, hl⟩ := (hs x' y').mp h
      exact ⟨k, congrArg val hk, congrArg val hl⟩
    · rintro ⟨k, rfl, rfl⟩
      exact (hs _ _).mpr ⟨k, rfl, rfl⟩
  have hp' (x y : Degree) : ConeCoding.Holds b.val (P.map ρ).external (two x y) ↔
      ∃ k, x = val (ρ (node k)) ∧ y = val (ρ (v k)) := by
    constructor
    · intro h
      have hx : b.val ≤ x := by obtain ⟨_, ht, _⟩ := h; exact (ht 0).1
      have hy : b.val ≤ y := by obtain ⟨_, ht, _⟩ := h; exact (ht 1).1
      let x' : Set.Ici b := ⟨⟨x, (P.map ρ).coordinates_mem h 0⟩, Set.mem_Ici.mpr hx⟩
      let y' : Set.Ici b := ⟨⟨y, (P.map ρ).coordinates_mem h 1⟩, Set.mem_Ici.mpr hy⟩
      obtain ⟨k, hk, hl⟩ := (hp x' y').mp h
      exact ⟨k, congrArg val hk, congrArg val hl⟩
    · rintro ⟨k, rfl, rfl⟩
      exact (hp _ _).mpr ⟨k, rfl, rfl⟩
  let d : ConeEnumeration.Enumeration b.val :=
    ⟨fun k => val (ρ (node k)), hi, fun k => val (ρ (v k)),
      (S.map ρ).external, (P.map ρ).external, hs', hp'⟩
  refine ⟨d, fun _ => rfl, (S.map ρ).above, (P.map ρ).above, ?_, ?_⟩
  · exact S.map_below ρ z (by simpa only [S, liftRelation_external] using hS)
  · exact P.map_below ρ z (by simpa only [P, liftRelation_external] using hP)

end
end OAI.TuringRigidity.TwoConeEnumeration
