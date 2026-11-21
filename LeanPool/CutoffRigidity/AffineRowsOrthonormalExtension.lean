/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module
public import LeanPool.CutoffRigidity.AffineSubspaceSplitting

/-! # A full ordered orthonormal basis extending every Gaussian direction

The genuine affine row-space basis is extended to an actual ambient
orthonormal basis, with its rows occupying the first k coordinates.
-/
public section
namespace CutoffRigidity
open Set
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_orthonormalBasis_extending_affine_rows (V : E → ℝ) (ρ : ℝ) :
    ∃ e : OrthonormalBasis (Fin d) ℝ E,
      ∀ i : Fin (Module.finrank ℝ (affineEigenRows V ρ)),
        e (Fin.castLE (affineEigenRows_finrank_le V ρ) i)=affineEigenBasisRows V ρ i := by
  classical
  let k := Module.finrank ℝ (affineEigenRows V ρ)
  let s : Set (Fin d) := {i | i.val < k}
  let v := fun i : Fin d => if h : i.val < k then affineEigenBasisRows V ρ ⟨i.val,h⟩ else 0
  let f : s → Fin k := fun i => ⟨i.val.val,i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin k => z.val) hij
  have hrow (i : s) : s.domRestrict v i=affineEigenBasisRows V ρ (f i) := by
    simp only [Set.domRestrict_apply,v]
    have hi : i.val.val < k := i.property
    rw [dite_eq_left hi]
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    convert! (affineEigenBasisRows_orthonormal V ρ).comp f hf using 1
    funext i
    exact hrow i
  obtain ⟨e,he⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (ι := Fin d) (v := v) (s := s) (by simp) hv
  refine ⟨e,?_⟩
  intro i
  rw [he _ (show Fin.castLE (affineEigenRows_finrank_le V ρ) i ∈ s from i.isLt)]
  dsimp only [v]
  rw [dite_eq_left (show (Fin.castLE (affineEigenRows_finrank_le V ρ) i).val < k from i.isLt)]
  rfl

end CutoffRigidity
