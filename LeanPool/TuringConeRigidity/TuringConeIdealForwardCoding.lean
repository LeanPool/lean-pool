/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeIdealForwardCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeIdealBackCoding

/-!
# Forward transport of bounded unary copies on an ideal

The target copy is interpreted in the ambient principal cone. The parameter
bounds force every satisfying tuple back into the target ideal, so no
unbounded-domain assumption is hidden in the transport.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeIdealForwardCoding

open IdealInterpretation SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding
open ConeIdealCoding

noncomputable section

/-- Forward transport of a bounded unary copy through a partial cone isomorphism. -/
theorem transport_copy {U : ℕ → Prop} {I : DegreeIdeal} {a : I}
    (ρ : I ≃o Set.Ici a) (c : ArithmeticModelDecoding.Copy U) (b : I)
    (hS : RelationBelow c.successor b.val) (hP : RelationBelow c.predicate b.val) :
    ∃ d : ConeCoding.Copy a.val U,
      RelationBelow d.successor (image ρ b) ∧ RelationBelow d.predicate (image ρ b) := by
  let S := RCode.ofBelow c.successor b hS
  let P := RCode.ofBelow c.predicate b hP
  have hn (n : ℕ) : c.node n ∈ I.carrier := by
    have hh : S.external.Holds (two (c.node n) (c.node (n + 1))) := by
      simpa only [S, RCode.external_ofBelow] using (c.successor_spec _ _).mpr ⟨n, rfl, rfl⟩
    exact S.coordinates_mem hh 0
  let node : ℕ → I := fun n => ⟨c.node n, hn n⟩
  let up (x : I) : Set.Ici a.val := ⟨image ρ x, Set.mem_Ici.mpr (base_le_image ρ x)⟩
  have hup (x y : I) : up x = up y ↔ x.val = y.val := by
    constructor
    · intro h
      have he : ρ x = ρ y := Subtype.ext (Element.ext _ _ (congrArg Subtype.val h))
      exact congrArg Element.val (ρ.injective he)
    · intro h
      exact congrArg up (Element.ext _ _ h)
  have hpre (x : Set.Ici a.val) (hx : x.val ∈ I.carrier) : ∃ y : I, up y = x := by
    let t : Set.Ici a := ⟨⟨x.val, hx⟩, x.property⟩
    exact ⟨ρ.symm t, Subtype.ext (congrArg (fun z : Set.Ici a => z.val.val) (ρ.apply_symm_apply t))⟩
  have hs (x y : I) :
      ConeCoding.Holds a.val (mapRelation ρ S) (two (up x).val (up y).val) ↔
        ∃ k, up x = up (node k) ∧ up y = up (node (k + 1)) := by
    have hh := map_relation_two ρ S x y
    simp only [S, RCode.external_ofBelow] at hh
    rw [hh, c.successor_spec]
    exact exists_congr (fun k => and_congr (hup x (node k)).symm (hup y (node (k + 1))).symm)
  have hp (x : I) :
      ConeCoding.Holds a.val (mapRelation ρ P) (one (up x).val) ↔
        ∃ k, U k ∧ up x = up (node k) := by
    have hh := ConeIdealBackCoding.map_relation_one ρ P x
    simp only [P, RCode.external_ofBelow] at hh
    rw [hh, c.predicate_spec]
    exact exists_congr (fun k => and_congr_right (fun _ => (hup x (node k)).symm))
  have hs' (x y : Set.Ici a.val) :
      ConeCoding.Holds a.val (mapRelation ρ S) (two x.val y.val) ↔
        ∃ k, x = up (node k) ∧ y = up (node (k + 1)) := by
    constructor
    · intro h
      have hx : x.val ∈ I.carrier := (coordinates_mem ρ S h 0).2
      have hy : y.val ∈ I.carrier := (coordinates_mem ρ S h 1).2
      obtain ⟨u, rfl⟩ := hpre x hx
      obtain ⟨v, rfl⟩ := hpre y hy
      exact (hs u v).mp h
    · rintro ⟨k, rfl, rfl⟩
      exact (hs _ _).mpr ⟨k, rfl, rfl⟩
  have hp' (x : Set.Ici a.val) :
      ConeCoding.Holds a.val (mapRelation ρ P) (one x.val) ↔
        ∃ k, U k ∧ x = up (node k) := by
    constructor
    · intro h
      have hx : x.val ∈ I.carrier := (coordinates_mem ρ P h 0).2
      obtain ⟨u, rfl⟩ := hpre x hx
      exact (hp u).mp h
    · rintro ⟨k, hk, rfl⟩
      exact (hp _).mpr ⟨k, hk, rfl⟩
  let d : ConeCoding.Copy a.val U :=
    { node := fun k => up (node k)
      injective := fun i j h => c.injective ((hup (node i) (node j)).mp h)
      successor := mapRelation ρ S
      predicate := mapRelation ρ P
      successor_spec := hs'
      predicate_spec := hp' }
  refine ⟨d, map_relation_below ρ S b ?_, map_relation_below ρ P b ?_⟩
  · simpa only [S, RCode.external_ofBelow] using hS
  · simpa only [P, RCode.external_ofBelow] using hP

end
end OAI.TuringRigidity.ConeIdealForwardCoding
