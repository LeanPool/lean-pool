/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.Certificate

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The tag-5 induction case of certificate persistence

Constructor number `5` is composition.
`evalnCertificateFormula_natCode_persist_of_tag_five` concerns a standard index `q` with
`partrecCodeTag q = 5`.  It proves that the raw evaluator certificate for `q` persists from a
stage `s` to every stage `t ≥ s`, assuming the same persistence for every standard index
`p < q`, whatever the constructor number of `p`.  The theory assumptions are `𝐏𝐀` and
`𝐈𝐎𝐩𝐞𝐧`.

A private helper rewrites `q` as the canonical composition index
`canonicalPartrecCompIndex (partrecCodePayload₁ q) (partrecCodePayload₂ q)`, relating
`bodd.toNat` to `% 2` through `Nat.mod_two_of_bodd`; a second helper places both payloads
strictly below `q`.  At that index, `evalnCertificateFormula_canonicalPartrecCompIndex_forward`
reduces the certificate at stage `s` to an inner certificate for the second payload and an
outer certificate for the first.  The induction hypothesis gives both at stage `t`, and
`evalnCertificateFormula_canonicalPartrecCompIndex_reverse` reconstructs the certificate for
the canonical index at stage `t`.

The file states one induction case.  It proves neither the cases for the other constructor
numbers nor persistence for all standard indices.
-/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open CategoricalRiceShapiro.ArithmeticCode

open CategoricalRiceShapiro.PartialRecursive

namespace CategoricalRiceShapiro
namespace Evaluator

variable {M : Type*} [ORingStructure M]

/-- A standard index of constructor number `5` is the canonical composition
index of its two payloads.  `bodd.toNat` and `% 2` are related by
`Nat.mod_two_of_bodd`, not assumed definitionally equal. -/
private theorem tagFive_canonical_reencoding (q : ℕ) (hq : partrecCodeTag q = 5) :
    q = canonicalPartrecCompIndex (partrecCodePayload₁ q) (partrecCodePayload₂ q) :=
  by
  have hb : ∀ n : ℕ, n.bodd.toNat = n % 2 := fun n => by rw [Nat.mod_two_of_bodd]
  have h4 : ¬q < 4 := by
    intro hlt
    simp only [partrecCodeTag, hlt, ite_true] at hq
    omega
  simp only [partrecCodeTag, h4, ite_false, hb, Nat.div2_val] at hq
  rw [canonicalPartrecCompIndex_eq]
  simp only [partrecCodePayload₁, partrecCodePayload₂, Nat.pair_unpair, partrecCodePayload,
    Nat.div2_val]
  omega

/-- Both payloads of a standard index of constructor number `5` lie strictly
below it. -/
private theorem tagFive_payloads_lt (q : ℕ) (hq : partrecCodeTag q = 5) :
    partrecCodePayload₁ q < q ∧ partrecCodePayload₂ q < q :=
  by
  have hindex := tagFive_canonical_reencoding q hq
  have houter :=
    canonicalPartrecCompIndex_outer_lt (partrecCodePayload₁ q) (partrecCodePayload₂ q)
  have hinner :=
    canonicalPartrecCompIndex_inner_lt (partrecCodePayload₁ q) (partrecCodePayload₂ q)
  rw [← hindex] at houter hinner
  exact ⟨houter, hinner⟩

/-- **Tag-5 induction case of certificate persistence.**  For a standard index
`q` of constructor number `5`, persistence of the certificate for `q` from stage
`s` to any later stage `t` follows from persistence for every strictly smaller
standard index, whatever its constructor number. -/
theorem evalnCertificateFormula_natCode_persist_of_tag_five [M↓[ℒₒᵣ] ⊧* 𝐏𝐀] [M↓[ℒₒᵣ] ⊧* 𝐈𝐎𝐩𝐞𝐧]
    (q : ℕ) (hq : partrecCodeTag q = 5)
    (ih :
      ∀ p : ℕ,
        p < q →
          ∀ s t u y : M,
            s ≤ t →
              Semiformula.Evalb ![s, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4) →
                Semiformula.Evalb ![t, ((p : ℕ) : M), u, y]
                  (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    ∀ s t u y : M,
      s ≤ t →
        Semiformula.Evalb ![s, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) →
          Semiformula.Evalb ![t, ((q : ℕ) : M), u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  intro s t u y hst source_certificate
  have hindex := tagFive_canonical_reencoding q hq
  obtain ⟨payload₁_lt, payload₂_lt⟩ := tagFive_payloads_lt q hq
  have source_canonical :
    Semiformula.Evalb
      ![s,
        (ORingStructure.numeral
            (canonicalPartrecCompIndex (partrecCodePayload₁ q) (partrecCodePayload₂ q)) :
          M),
        u, y]
      (evalnCertificateFormula : ArithmeticSemisentence 4) :=
    by
    rw [numeral_eq_natCast_app, ← hindex]
    exact source_certificate
  obtain ⟨x, inner_at_s, outer_at_s⟩ :=
    evalnCertificateFormula_canonicalPartrecCompIndex_forward s u y (partrecCodePayload₁ q)
      (partrecCodePayload₂ q) source_canonical
  rw [numeral_eq_natCast_app] at inner_at_s outer_at_s
  have inner_at_t := ih (partrecCodePayload₂ q) payload₂_lt s t u x hst inner_at_s
  have outer_at_t := ih (partrecCodePayload₁ q) payload₁_lt s t x y hst outer_at_s
  have target_canonical :=
    evalnCertificateFormula_canonicalPartrecCompIndex_reverse t u x y (partrecCodePayload₁ q)
      (partrecCodePayload₂ q) (by rw [numeral_eq_natCast_app]; exact inner_at_t)
      (by rw [numeral_eq_natCast_app]; exact outer_at_t)
        -- (6) back from the canonical composition index to `q`
  rw [numeral_eq_natCast_app, ← hindex] at target_canonical
  exact target_canonical

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
