/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Tagged.SortBack
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.VectorSort
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Install.Weight
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Choices
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.RAM.Calls
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Cost
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Shaving.Defs

/-! # Verifying a deterministic controller on two named tapes -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Coloring

open Install
variable {F : Type} [Field F] {A D : Format} {f : A.obj → D.obj} {j k c : ℕ}

open scoped Classical in
/-- Returns `1` when `f (A.code.symm (z ∘ Sum.inl)) = D.code.symm (z ∘ Sum.inr)` holds, and `0`
otherwise. -/
def graph (F : Type) [Field F] (A D : Format) (f : A.obj → D.obj)
    (z : A.pins ⊕ D.pins → Bool) : F :=
  if f (A.code.symm (z ∘ Sum.inl)) = D.code.symm (z ∘ Sum.inr) then 1 else 0

open scoped Classical in
theorem Cheap.weight (h : Cheap F j k A D f c) :
    Weight F (graph F A D f) (2 ^ j * (100 + k) ^ c) := by
  obtain ⟨m, hf, hm⟩ := h
  let a := word A.width
  let b := word D.width
  let i : A.pins ≃ slots a := Fintype.equivOfCardEq (by simp [a, Format.width])
  let l : D.pins ≃ slots b := Fintype.equivOfCardEq (by simp [b, Format.width])
  obtain ⟨v, hv, hf⟩ := hf a b i l
  have hb : wd b = D.width := wd_word _
  apply Weight.of_layout (a := .pair a b) (i.sumCongr l)
  refine ⟨v + wd b, by omega, ?_⟩
  have hu (k : Val a → Val b → F) (hk : Net F a b k v) :
      Net F (.pair a b) .unit (fun x _ => k x.1 x.2) (v + wd b) := by
    have both := (hk.par (Tagged.cap b)).pre (.assoc a b b)
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
      (both.post (.swap _ _)).trace
  convert hu _ hf using 1
  funext z _
  have he (u : D.obj) : u = D.code.symm (bits b z.2 ∘ l) ↔
      (bits b).symm (D.code u ∘ l.symm) = z.2 := by
    rw [Equiv.eq_symm_apply, Equiv.symm_apply_eq]
    simp only [funext_iff, Function.comp_apply]
    exact ⟨fun h t => by simpa using h (l.symm t), fun h t => by simpa using h (l t)⟩
  change (if f (A.code.symm (bits a z.1 ∘ i)) = D.code.symm (bits b z.2 ∘ l) then (1 : F) else 0)
    = _
  simp only [he, Function.comp_apply]

end MatrixMultiplicationAllFields.MatrixExponent.Coloring
end

/- # Labeled networks for a selected family of routed diagrams -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM

open Filter

open scoped Classical in
theorem labeled {K : Type} [Field K] {a b : Wire} {f : Val a → Val b → K}
    {W : List Bool → K} {U s : ℕ} (h : Wide K (8 * (U + 1)) (labels U W) a b f s) :
    Labeled f (ceiling U + 1) s (8 * (U + 1)) := by
  let L := (Finset.range (ceiling U + 1)).image (label U W)
  have he : (↑L : Set (Table K)) = labels U W := by
    ext
    simp [L, labels]
  exact ⟨L, Finset.card_image_le.trans_eq (Finset.card_range _), he.symm ▸ h⟩

end MatrixMultiplicationAllFields.MatrixExponent.Transcript.RAM
end
