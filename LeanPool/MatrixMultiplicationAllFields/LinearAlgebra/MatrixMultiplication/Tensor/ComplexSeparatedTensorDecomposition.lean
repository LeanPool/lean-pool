/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteSeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexDotPairing

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section DependentSum

variable {K S : Type*} [CommSemiring K] [DecidableEq S]
variable {X Y Z : S → Type*}

/-- Direct sum of tensors whose coordinate spaces may depend on the summand. -/
def dependentDirectSum (T : ∀ s, Tensor K (X s) (Y s) (Z s)) :
    Tensor K (Σ s, X s) (Σ s, Y s) (Σ s, Z s) :=
  fun x y z =>
    if hxy : y.1 = x.1 then
      if hxz : z.1 = x.1 then T x.1 x.2 (hxy ▸ y.2) (hxz ▸ z.2)
      else 0
    else 0

@[simp] theorem dependentDirectSum_matching
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (s : S) (x : X s) (y : Y s) (z : Z s) :
    dependentDirectSum T ⟨s, x⟩ ⟨s, y⟩ ⟨s, z⟩ = T s x y z := by
  simp [dependentDirectSum]

theorem dependentDirectSum_zero_of_left_ne
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (x : Σ s, X s) (y : Σ s, Y s) (z : Σ s, Z s)
    (h : x.1 ≠ y.1) : dependentDirectSum T x y z = 0 := by
  simp [dependentDirectSum, Ne.symm h]

/-- Replace summand-dependent coordinates by a common coordinate type using chosen
equivalences. -/
def directSumCoordinateEquiv {A : Type*} (e : ∀ s, X s ≃ A) :
    (Σ s, X s) ≃ S × A where
  toFun x := (x.1, e x.1 x.2)
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv := by
    rintro ⟨s, x⟩
    simp
  right_inv := by
    rintro ⟨s, x⟩
    simp

theorem dependentDirectSum_reindex {A B C : Type*}
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (ex : ∀ s, X s ≃ A) (ey : ∀ s, Y s ≃ B) (ez : ∀ s, Z s ≃ C) :
    pullback (directSumCoordinateEquiv ex).symm
      (directSumCoordinateEquiv ey).symm (directSumCoordinateEquiv ez).symm
      (dependentDirectSum T) =
      directSum (fun s => pullback (ex s).symm (ey s).symm (ez s).symm (T s)) := by
  funext x y z
  rcases x with ⟨s, x⟩
  rcases y with ⟨t, y⟩
  rcases z with ⟨v, z⟩
  by_cases ht : t = s
  · subst t
    by_cases hv : v = s
    · subst v
      simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum]
    · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
        hv, Ne.symm hv]
  · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
      ht, Ne.symm ht]

end DependentSum
end Tensor

section FiberDecomposition

variable {X Y Z S U : Type*} [DecidableEq S] [DecidableEq U]

/-- Restrict the first two tensor legs to fibers with a specified common label. -/
def labelFiberTensor (lx : X → S) (ly : Y → S) (T : Tensor ℂ X Y Z) (s : S) :
    Tensor ℂ {x // lx x = s} {y // ly y = s} Z :=
  fun x y z => T x.1 y.1 z

/-- Identify labelled fiber coordinates with the original coordinates and an auxiliary
factor. -/
def fiberCoordinateEquiv (lx : X → S) :
    (Σ s, {x // lx x = s} × U) ≃ X × U where
  toFun x := (x.2.1.1, x.2.2)
  invFun x := ⟨lx x.1, (⟨x.1, rfl⟩, x.2)⟩
  left_inv := by
    rintro ⟨s, ⟨⟨x, hx⟩, u⟩⟩
    cases hx
    rfl
  right_inv := by
    rintro ⟨x, u⟩
    rfl

/-- Exchange a summand tag and its tensor coordinate, removing a singleton factor. -/
def tagCoordinateEquiv : (Σ _ : S, Z × Unit) ≃ Z × S where
  toFun z := (z.2.1, z.1)
  invFun z := ⟨z.2, (z.1, ())⟩
  left_inv := by
    rintro ⟨s, z, u⟩
    cases u
    rfl
  right_inv := by
    rintro ⟨z, s⟩
    rfl

theorem separatedTensor_eq_fiber_directSum
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.pullback (fiberCoordinateEquiv (U := U) lx)
      (fiberCoordinateEquiv (U := U) ly) (tagCoordinateEquiv (Z := Z) (S := S))
      (separatedTensor lx T) =
      Tensor.dependentDirectSum (fun s =>
        Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U)) := by
  classical
  funext x y z
  rcases x with ⟨s, x, u⟩
  rcases y with ⟨t, y, v⟩
  rcases z with ⟨w, z, q⟩
  by_cases ht : t = s
  · subst t
    by_cases hw : w = s
    · subst w
      rw [Tensor.dependentDirectSum_matching]
      simp [Tensor.pullback, fiberCoordinateEquiv, tagCoordinateEquiv,
        separatedTensor, Tensor.product, labelFiberTensor, Tensor.dotPairing,
        x.property, mul_ite]
    · simp [Tensor.pullback, fiberCoordinateEquiv, tagCoordinateEquiv,
        separatedTensor, Tensor.dependentDirectSum, x.property, hw, Ne.symm hw]
  · have hzero : T x.1 y.1 z = 0 := by
      by_contra hzero
      have hxy := hlabels x.1 y.1 z hzero
      exact ht (y.property.symm.trans (hxy.symm.trans x.property))
    simp [Tensor.pullback, fiberCoordinateEquiv, tagCoordinateEquiv,
      separatedTensor, Tensor.dependentDirectSum, ht, hzero]

theorem fiber_directSum_eq_separatedTensor
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.pullback (fiberCoordinateEquiv (U := U) lx).symm
      (fiberCoordinateEquiv (U := U) ly).symm
      (tagCoordinateEquiv (Z := Z) (S := S)).symm
      (Tensor.dependentDirectSum (fun s =>
        Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) =
      separatedTensor lx T := by
  rw [← separatedTensor_eq_fiber_directSum T lx ly hlabels]
  funext x y z
  simp [Tensor.pullback]

theorem separatedTensor_fiber_directSum_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) r := by
  rw [← separatedTensor_eq_fiber_directSum T lx ly hlabels]
  exact h.pullback _ _ _

theorem separatedTensor_fiber_directSum_rankAtMost_iff
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := U) lx T) r ↔
      Tensor.RankAtMost (Tensor.dependentDirectSum (fun s =>
        Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) r := by
  constructor
  · exact separatedTensor_fiber_directSum_rankAtMost T lx ly hlabels
  · intro h
    rw [← fiber_directSum_eq_separatedTensor T lx ly hlabels]
    exact h.pullback _ _ _

theorem separatedTensor_fiber_directSum_borderRankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S) {r : ℕ}
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (h : Tensor.BorderRankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.BorderRankAtMost (Tensor.dependentDirectSum (fun s =>
      Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U))) r := by
  classical
  rw [← separatedTensor_eq_fiber_directSum T lx ly hlabels]
  exact h.pullback _ _ _

theorem separatedTensor_uniform_directSum_rankAtMost {A B : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (ex : ∀ s, {x // lx x = s} ≃ A) (ey : ∀ s, {y // ly y = s} ≃ B)
    {r : ℕ} (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.directSum (fun s => Tensor.pullback
      (Equiv.prodCongr (ex s) (Equiv.refl U)).symm
      (Equiv.prodCongr (ey s) (Equiv.refl U)).symm
      (Equiv.refl (Z × Unit)).symm
      (Tensor.product (labelFiberTensor lx ly T s) (Tensor.dotPairing U)))) r := by
  have hf := separatedTensor_fiber_directSum_rankAtMost T lx ly hlabels h
  have hp := hf.pullback
    (Tensor.directSumCoordinateEquiv
      (fun s => Equiv.prodCongr (ex s) (Equiv.refl U))).symm
    (Tensor.directSumCoordinateEquiv
      (fun s => Equiv.prodCongr (ey s) (Equiv.refl U))).symm
    (Tensor.directSumCoordinateEquiv (fun _ : S => Equiv.refl (Z × Unit))).symm
  rw [Tensor.dependentDirectSum_reindex] at hp
  exact hp

theorem separatedTensor_localModels_identity {A B C : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (fx : S → A → X) (fy : S → B → Y) (fz : S → C → Z)
    (hfx : ∀ s a, lx (fx s a) = s) (hfy : ∀ s b, ly (fy s b) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.pullback
      (fun x : S × (A × U) => (fx x.1 x.2.1, x.2.2))
      (fun y : S × (B × U) => (fy y.1 y.2.1, y.2.2))
      (fun z : S × (C × Unit) => (fz z.1 z.2.1, z.1))
      (separatedTensor lx T) =
      Tensor.directSum (fun s => Tensor.product
        (Tensor.pullback (fx s) (fy s) (fz s) T) (Tensor.dotPairing U)) := by
  funext x y z
  rcases x with ⟨s, a, u⟩
  rcases y with ⟨t, b, v⟩
  rcases z with ⟨w, c, q⟩
  by_cases ht : t = s
  · subst t
    by_cases hw : w = s
    · subst w
      simp [Tensor.pullback, separatedTensor, Tensor.directSum,
        Tensor.product, Tensor.dotPairing, hfx, mul_ite]
    · simp [Tensor.pullback, separatedTensor, Tensor.directSum,
        hfx, Ne.symm hw]
  · have hzero : T (fx s a) (fy t b) (fz w c) = 0 := by
      by_contra hzero
      have hxy := hlabels (fx s a) (fy t b) (fz w c) hzero
      exact ht ((hfy t b).symm.trans (hxy.symm.trans (hfx s a)))
    simp [Tensor.pullback, separatedTensor, Tensor.directSum,
      Ne.symm ht, hzero]

theorem separatedTensor_localModels_rankAtMost {A B C : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (fx : S → A → X) (fy : S → B → Y) (fz : S → C → Z)
    (hfx : ∀ s a, lx (fx s a) = s) (hfy : ∀ s b, ly (fy s b) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    {r : ℕ} (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.directSum (fun s => Tensor.product
      (Tensor.pullback (fx s) (fy s) (fz s) T) (Tensor.dotPairing U))) r := by
  rw [← separatedTensor_localModels_identity T lx ly fx fy fz hfx hfy hlabels]
  exact h.pullback _ _ _

theorem separatedTensor_localModels_borderRankAtMost {A B C : Type*}
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (fx : S → A → X) (fy : S → B → Y) (fz : S → C → Z)
    (hfx : ∀ s a, lx (fx s a) = s) (hfy : ∀ s b, ly (fy s b) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    {r : ℕ} (h : Tensor.BorderRankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.BorderRankAtMost (Tensor.directSum (fun s => Tensor.product
      (Tensor.pullback (fx s) (fy s) (fz s) T) (Tensor.dotPairing U))) r := by
  classical
  rw [← separatedTensor_localModels_identity T lx ly fx fy fz hfx hfy hlabels]
  exact h.pullback _ _ _

theorem separatedTensor_scalar_identity
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (sx : S → X) (sy : S → Y) (sz : S → Z)
    (hsx : ∀ s, lx (sx s) = s) (hsy : ∀ s, ly (sy s) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hscalar : ∀ s, T (sx s) (sy s) (sz s) = 1) :
    Tensor.pullback
      (fun x : S × U => (sx x.1, x.2))
      (fun y : S × U => (sy y.1, y.2))
      (fun z : S × Unit => (sz z.1, z.1)) (separatedTensor lx T) =
      Tensor.directSum (fun _ : S => Tensor.dotPairing U) := by
  have hmodels := separatedTensor_localModels_identity (U := U) T lx ly
    (fun s (_ : Unit) => sx s) (fun s (_ : Unit) => sy s) (fun s (_ : Unit) => sz s)
    (fun s _ => hsx s) (fun s _ => hsy s) hlabels
  have h := congrArg (Tensor.pullback
    (fun x : S × U => (x.1, ((), x.2)))
    (fun y : S × U => (y.1, ((), y.2)))
    (fun z : S × Unit => (z.1, ((), z.2)))) hmodels
  funext x y z
  have hpoint := congrFun (congrFun (congrFun h x) y) z
  simpa only [Tensor.pullback, Tensor.directSum, Tensor.product, hscalar, one_mul]
    using hpoint

theorem separatedTensor_scalar_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (sx : S → X) (sy : S → Y) (sz : S → Z)
    (hsx : ∀ s, lx (sx s) = s) (hsy : ∀ s, ly (sy s) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hscalar : ∀ s, T (sx s) (sy s) (sz s) = 1)
    {r : ℕ} (h : Tensor.RankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.RankAtMost (Tensor.directSum (fun _ : S => Tensor.dotPairing (K := ℂ) U)) r := by
  rw [← separatedTensor_scalar_identity T lx ly sx sy sz hsx hsy hlabels hscalar]
  exact h.pullback _ _ _

theorem separatedTensor_scalar_borderRankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (sx : S → X) (sy : S → Y) (sz : S → Z)
    (hsx : ∀ s, lx (sx s) = s) (hsy : ∀ s, ly (sy s) = s)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hscalar : ∀ s, T (sx s) (sy s) (sz s) = 1)
    {r : ℕ} (h : Tensor.BorderRankAtMost (separatedTensor (U := U) lx T) r) :
    Tensor.BorderRankAtMost (Tensor.directSum (fun _ : S => Tensor.dotPairing U)) r := by
  classical
  rw [← separatedTensor_scalar_identity T lx ly sx sy sz hsx hsy hlabels hscalar]
  exact h.pullback _ _ _

end FiberDecomposition
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
