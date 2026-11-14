/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.NumeralEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# The canonical index of a composed partial-recursive program

`canonicalPartrecCompIndex f g` is the Mathlib index of `Nat.Partrec.Code.comp`
applied to the programs those two indices name.  Its constructor number is `5`
and its two subcodes are the given indices, which the three theorems below
record.  Each rests on the same closed form,

`canonicalPartrecCompIndex f g = 2 * (2 * Nat.pair f g + 1) + 4`,

proved once in `canonicalPartrecCompIndex_eq`.

The evaluation results then read those numbers off inside an arbitrary model of
`𝐏𝐀⁻`: a code whose graph holds at the canonical index has, at the same
assignment, the graph of the constructor number at `5` and of the two subcodes
at `fCode` and `gCode`.
-/

@[expose] public section

namespace CategoricalRiceShapiro
namespace PartialRecursive

open Encodable Denumerable

open CategoricalRiceShapiro.ArithmeticCode

/-- The index of the composition of the programs named by `fCode` and `gCode`. -/
def canonicalPartrecCompIndex (fCode gCode : ℕ) : ℕ :=
  Encodable.encode
    (Nat.Partrec.Code.comp (Denumerable.ofNat Nat.Partrec.Code fCode)
      (Denumerable.ofNat Nat.Partrec.Code gCode))

/-- The closed form of the canonical composition index. -/
theorem canonicalPartrecCompIndex_eq (fCode gCode : ℕ) :
    canonicalPartrecCompIndex fCode gCode = 2 * (2 * Nat.pair fCode gCode + 1) + 4 :=
  by
  unfold canonicalPartrecCompIndex
  rw [Nat.Partrec.Code.encodeCode_eq]
  simp only [Nat.Partrec.Code.encodeCode]
  simp only [← Nat.Partrec.Code.encodeCode_eq, Denumerable.encode_ofNat]

/-- The outer subindex is below the canonical composition index. -/
theorem canonicalPartrecCompIndex_outer_lt (fCode gCode : ℕ) :
    fCode < canonicalPartrecCompIndex fCode gCode :=
  by
  unfold canonicalPartrecCompIndex
  simpa only [Denumerable.encode_ofNat] using
    (Nat.Partrec.Code.encode_lt_comp (Denumerable.ofNat Nat.Partrec.Code fCode)
        (Denumerable.ofNat Nat.Partrec.Code gCode)).1

/-- The inner subindex is below the canonical composition index. -/
theorem canonicalPartrecCompIndex_inner_lt (fCode gCode : ℕ) :
    gCode < canonicalPartrecCompIndex fCode gCode :=
  by
  unfold canonicalPartrecCompIndex
  simpa only [Denumerable.encode_ofNat] using
    (Nat.Partrec.Code.encode_lt_comp (Denumerable.ofNat Nat.Partrec.Code fCode)
        (Denumerable.ofNat Nat.Partrec.Code gCode)).2

/-- The payload of the canonical composition index is the pair of subindices. -/
theorem partrecCodePayload_canonicalPartrecCompIndex (fCode gCode : ℕ) :
    partrecCodePayload (canonicalPartrecCompIndex fCode gCode) = Nat.pair fCode gCode :=
  by
  have hsub : canonicalPartrecCompIndex fCode gCode - 4 = 2 * (2 * Nat.pair fCode gCode + 1) :=
    by rw [canonicalPartrecCompIndex_eq]; omega
  simp only [partrecCodePayload, hsub]
  simp

/-- The canonical composition index has constructor number `5`. -/
theorem canonicalPartrecCompIndex_constructor_number (fCode gCode : ℕ) :
    partrecCodeTag (canonicalPartrecCompIndex fCode gCode) = 5 :=
  by
  have hlt : ¬(canonicalPartrecCompIndex fCode gCode < 4) := by
    rw [canonicalPartrecCompIndex_eq]; omega
  have hsub : canonicalPartrecCompIndex fCode gCode - 4 = 2 * (2 * Nat.pair fCode gCode + 1) :=
    by rw [canonicalPartrecCompIndex_eq]; omega
  simp only [partrecCodeTag, ite_eq_right hlt, hsub]
  simp

/-- The first subcode of the canonical composition index is the outer one. -/
theorem canonicalPartrecCompIndex_outer_index (fCode gCode : ℕ) :
    partrecCodePayload₁ (canonicalPartrecCompIndex fCode gCode) = fCode := by
  simp only [partrecCodePayload₁, partrecCodePayload_canonicalPartrecCompIndex, Nat.unpair_pair]

/-- The second subcode of the canonical composition index is the inner one. -/
theorem canonicalPartrecCompIndex_inner_index (fCode gCode : ℕ) :
    partrecCodePayload₂ (canonicalPartrecCompIndex fCode gCode) = gCode := by
  simp only [partrecCodePayload₂, partrecCodePayload_canonicalPartrecCompIndex, Nat.unpair_pair]

/-!
### Evaluation in an arbitrary model -/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

open Nat.ArithPart₁

/-- The payload of the canonical composition index, read inside a model. -/
theorem eval_codePartrecPayload_canonicalPartrecCompIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecCompIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb (((Nat.pair fCode gCode : ℕ) : M) :> v) (code (codePartrecPayload d)) :=
  by
  simpa only [partrecCodePayload_canonicalPartrecCompIndex] using
    IndexDecoder.eval_codePartrecPayload_natCast d (canonicalPartrecCompIndex fCode gCode) v hd

/-- The constructor number of the canonical composition index, read inside a
model: it is `5`, the number of composition. -/
theorem eval_codePartrecTag_canonicalPartrecCompIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecCompIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb ((5 : M) :> v) (code (codePartrecTag d)) :=
  by
  simpa only [Nat.succ_eq_add_one, canonicalPartrecCompIndex_constructor_number,
    Nat.cast_ofNat] using
    IndexDecoder.eval_codePartrecTag_natCast d (canonicalPartrecCompIndex fCode gCode) v hd

/-- The outer subcode of the canonical composition index, read inside a model. -/
theorem eval_codePartrecPayload₁_canonicalPartrecCompIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecCompIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb (((fCode : ℕ) : M) :> v) (code (codePartrecPayload₁ d)) :=
  by
  simpa only [canonicalPartrecCompIndex_outer_index] using
    IndexDecoder.eval_codePartrecPayload₁_natCast d (canonicalPartrecCompIndex fCode gCode) v hd

/-- The inner subcode of the canonical composition index, read inside a model. -/
theorem eval_codePartrecPayload₂_canonicalPartrecCompIndex {M : Type*} [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻] {r : ℕ} (d : Code r) (fCode gCode : ℕ) (v : Fin r → M)
    (hd : Semiformula.Evalb ((canonicalPartrecCompIndex fCode gCode : M) :> v) (code d)) :
    Semiformula.Evalb (((gCode : ℕ) : M) :> v) (code (codePartrecPayload₂ d)) :=
  by
  simpa only [canonicalPartrecCompIndex_inner_index] using
    IndexDecoder.eval_codePartrecPayload₂_natCast d (canonicalPartrecCompIndex fCode gCode) v hd

end PartialRecursive
end CategoricalRiceShapiro

end

end PointwiseComposition
