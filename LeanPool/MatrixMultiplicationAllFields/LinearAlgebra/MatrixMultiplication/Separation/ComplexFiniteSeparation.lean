/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexGroupTensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexModularSeparation

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

section Separation

variable {X Y Z S U G : Type*}
variable [AddCommGroup G] [Fintype G] [DecidableEq G]
variable [DecidableEq S] [DecidableEq U]

def separatedTensor (lx : X → S) (T : Tensor ℂ X Y Z) :
    Tensor ℂ (X × U) (Y × U) (Z × S) :=
  fun x y z => if lx x.1 = z.2 ∧ x.2 = y.2 then T x.1 y.1 z.1 else 0

omit [Fintype G] in
theorem finite_separation_identity
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.pullback
      (fun x : X × U => (x.1, point (lx x.1) x.2))
      (fun y : Y × U => (y.1, tag (ly y.1) - point (ly y.1) y.2))
      (fun z : Z × S => (z.1, tag z.2))
      (Tensor.product T (groupTensor G)) = separatedTensor lx T := by
  funext x y z
  by_cases hzero : T x.1 y.1 z.1 = 0
  · simp [Tensor.pullback, Tensor.product, separatedTensor, hzero]
  · have hxy := hlabels x.1 y.1 z.1 hzero
    simp only [Tensor.pullback, Tensor.product, groupTensor, separatedTensor]
    simp only [← hxy, hcollision, mul_ite, mul_one, mul_zero]

theorem finite_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    separatedTensor (U := U) lx T ∈
      Tensor.restrictionOrbit (Tensor.product T (groupTensor G)) := by
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  refine ⟨(fun (x : X × U) (original : X × G) =>
      if original = (x.1, point (lx x.1) x.2) then 1 else 0),
    (fun (y : Y × U) (original : Y × G) =>
      if original = (y.1, tag (ly y.1) - point (ly y.1) y.2) then 1 else 0),
    (fun (z : Z × S) (original : Z × G) =>
      if original = (z.1, tag z.2) then 1 else 0), ?_⟩
  exact Tensor.pullback_eq_restrict _ _ _ _

theorem finite_separation_degeneratesTo
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.DegeneratesTo (Tensor.product T (groupTensor G))
      (separatedTensor (U := U) lx T) := by
  exact subset_closure
    (finite_separation_mem_restrictionOrbit T lx ly tag point hlabels hcollision)

omit [DecidableEq G] in
theorem finite_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G) {r : ℕ}
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.RankAtMost (separatedTensor (U := U) lx T) (r * Fintype.card G) := by
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  exact (hT.product (groupTensor_rankAtMost G)).pullback _ _ _

omit [DecidableEq G] in
theorem finite_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype S] [Fintype U]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    (tag : S → G) (point : S → U → G) {r : ℕ}
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y)
    (hcollision : ∀ s s' i j,
      point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j) :
    Tensor.BorderRankAtMost (separatedTensor (U := U) lx T)
      (r * Fintype.card G) := by
  classical
  classical
  rw [← finite_separation_identity T lx ly tag point hlabels hcollision]
  rw [Tensor.pullback_eq_restrict]
  exact (hT.product (groupTensor_rankAtMost G).borderRankAtMost).restrict _ _ _

end Separation

section FiniteGrid

variable {X Y Z S : Type*} [Fintype S] [DecidableEq S]

theorem finite_grid_separation_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m : ℕ} [NeZero (4 * Q)]
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    separatedTensor (U := Fin m) lx T ∈ Tensor.restrictionOrbit
      (Tensor.product T (groupTensor (Separation.AuxiliaryGroup d Q))) := by
  classical
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  exact finite_separation_mem_restrictionOrbit T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hlabels hc

theorem finite_grid_separation_rankAtMost
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m r : ℕ} (hQ : 0 < Q)
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hT : Tensor.RankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.RankAtMost (separatedTensor (U := Fin m) lx T) (r * (4 * Q) ^ d) := by
  classical
  let : NeZero (4 * Q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hQ)⟩
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  have hr := finite_separation_rankAtMost T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hT hlabels hc
  simpa only [Separation.card_auxiliaryGroup] using hr

theorem finite_grid_separation_borderRankAtMost
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (lx : X → S) (ly : Y → S)
    {d Q m r : ℕ} (hQ : 0 < Q)
    (hK : (d * Q ^ 2 + 1) * Fintype.card S ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d)
    (hT : Tensor.BorderRankAtMost T r)
    (hlabels : ∀ x y z, T x y z ≠ 0 → lx x = ly y) :
    Tensor.BorderRankAtMost (separatedTensor (U := Fin m) lx T)
      (r * (4 * Q) ^ d) := by
  classical
  let : NeZero (4 * Q) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hQ)⟩
  obtain ⟨tag, point, hcollision⟩ := Separation.exists_modular_separation hK hm
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hc : ∀ s s' i j,
      point (e s) i + (tag (e s) - point (e s) j) = tag (e s') ↔
        s = s' ∧ i = j := by
    intro s s' i j
    rw [hcollision, e.injective.eq_iff]
  have hr := finite_separation_borderRankAtMost T lx ly
    (fun s => tag (e s)) (fun s => point (e s)) hT hlabels hc
  simpa only [Separation.card_auxiliaryGroup] using hr

end FiniteGrid
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
