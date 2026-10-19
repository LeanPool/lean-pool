/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.PartialRecursive
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.RecursionEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Evaluation existence for the partial-recursive index decoders

`PartialRecursive` defines the four codes that read a partial-recursive index:
its constructor tag, its payload, and the two components of that payload.  This
file proves that each has a value in an arbitrary model of `𝐏𝐀`, given a value
for the index.

Nothing here decodes an index or asserts what the value is.  For an arbitrary
element of the model the constructions still terminate, and only that is
proved; no witness is identified with a quotient, a remainder or a Cantor
component of an external number.

The tag is an eager conditional, so both of its branches are evaluated before
the test selects one: the index itself, and the compound tag built from the two
parity bits of the shifted index.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace ArithmeticCode

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

/-- The payload of a partial-recursive index has a value at any value of the
index: the shifted index is a truncated difference, and halving it twice has a
value by `eval_codeDiv2_exists_of_value`. -/
theorem eval_codePartrecPayload_exists_of_value {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    {k : ℕ} (d : Code k) (q : M) (v : Fin k → M) (hd : Semiformula.Evalb (q :> v) (code d)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codePartrecPayload d)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hfour : Semiformula.Evalb ((4 : M) :> v) (code (codeConst (n := k) 4)) := by
    rw [eval_codeConst_iff]; simp
  obtain ⟨w, hw⟩ :=
    eval_codeDiv2_exists_of_value (codeSub d (codeConst 4)) (q - 4) v
      (eval_codeSub d (codeConst 4) q 4 v hd hfour)
  exact eval_codeDiv2_exists_of_value (codeDiv2 (codeSub d (codeConst 4))) w v hw

/-- The first payload component has a value at any value of the index. -/
theorem eval_codePartrecPayload₁_exists_of_value {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    {k : ℕ} (d : Code k) (q : M) (v : Fin k → M) (hd : Semiformula.Evalb (q :> v) (code d)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codePartrecPayload₁ d)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨w, hw⟩ := eval_codePartrecPayload_exists_of_value d q v hd
  exact ⟨_, eval_codeUnpair₁ (codePartrecPayload d) w v hw⟩

/-- The second payload component has a value at any value of the index. -/
theorem eval_codePartrecPayload₂_exists_of_value {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    {k : ℕ} (d : Code k) (q : M) (v : Fin k → M) (hd : Semiformula.Evalb (q :> v) (code d)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codePartrecPayload₂ d)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨w, hw⟩ := eval_codePartrecPayload_exists_of_value d q v hd
  exact ⟨_, eval_codeUnpair₂ (codePartrecPayload d) w v hw⟩

/-- The constructor tag of a partial-recursive index has a value at any value of
the index.

`codeIfPos` is eager, so both branches are evaluated whatever the test does: the
index itself, and the compound tag `4 + 2 * (r % 2) + (h % 2)`, where `r` is the
shifted index and `h` is some value of its half.  The comparison against `4`
then selects one of the two. -/
theorem eval_codePartrecTag_exists_of_value {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    {k : ℕ} (d : Code k) (q : M) (v : Fin k → M) (hd : Semiformula.Evalb (q :> v) (code d)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codePartrecTag d)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  let : M↓[ℒₒᵣ] ⊧* 𝐈Σ1 := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  have hfour : Semiformula.Evalb ((4 : M) :> v) (code (codeConst (n := k) 4)) := by
    rw [eval_codeConst_iff]; simp
  have htwo : Semiformula.Evalb ((2 : M) :> v) (code (codeConst (n := k) 2)) := by
    rw [eval_codeConst_iff]; simp
  have hshift := eval_codeSub d (codeConst 4) q 4 v hd hfour
  have hbodd :
    Semiformula.Evalb (((q - 4) % 2) :> v) (code (codeBodd (codeSub d (codeConst 4)))) :=
    eval_codeRem (codeSub d (codeConst 4)) (codeConst 2) (q - 4) 2 v hshift htwo
  obtain ⟨h, hh⟩ := eval_codeDiv2_exists_of_value (codeSub d (codeConst 4)) (q - 4) v hshift
  have hbodd2 :
    Semiformula.Evalb ((h % 2) :> v) (code (codeBodd (codeDiv2 (codeSub d (codeConst 4))))) :=
    eval_codeRem (codeDiv2 (codeSub d (codeConst 4))) (codeConst 2) h 2 v hh htwo
  have hcompound :
    Semiformula.Evalb ((4 + 2 * ((q - 4) % 2) + h % 2) :> v)
      (code
        (codeAdd
          (codeAdd (codeConst 4) (codeMul (codeConst 2) (codeBodd (codeSub d (codeConst 4)))))
          (codeBodd (codeDiv2 (codeSub d (codeConst 4)))))) :=
    (eval_codeAdd_iff _ _ _ _).mpr
      ⟨4 + 2 * ((q - 4) % 2), h % 2,
        (eval_codeAdd_iff _ _ _ _).mpr
          ⟨4, 2 * ((q - 4) % 2), hfour,
            (eval_codeMul_iff _ _ _ _).mpr ⟨2, (q - 4) % 2, htwo, hbodd, rfl⟩, rfl⟩,
        hbodd2, rfl⟩
  by_cases hq : q < 4
  · exact
      ⟨q,
        eval_codeIfPos_of _ _ _ 1 q (4 + 2 * ((q - 4) % 2) + h % 2) q v
          ((eval_codeLt_iff _ _ _ _).mpr ⟨q, 4, hd, hfour, Or.inl ⟨hq, rfl⟩⟩) hd hcompound
          (Or.inl ⟨by simp, rfl⟩)⟩
  · exact
      ⟨4 + 2 * ((q - 4) % 2) + h % 2,
        eval_codeIfPos_of _ _ _ 0 q (4 + 2 * ((q - 4) % 2) + h % 2)
          (4 + 2 * ((q - 4) % 2) + h % 2) v
          ((eval_codeLt_iff _ _ _ _).mpr ⟨q, 4, hd, hfour, Or.inr ⟨hq, rfl⟩⟩) hd hcompound
          (Or.inr ⟨rfl, rfl⟩)⟩

end ArithmeticCode
end CategoricalRiceShapiro

end

end PointwiseComposition
