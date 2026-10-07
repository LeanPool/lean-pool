/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialOrderShift
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialFinsetSumLinearity
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Multi-index derivatives on time slices of `Ω × I`

Slice-level calculus for `multiPartial` used in the proof of `thm:analytic:interior`: joint
smoothness gives smoothness of time slices, spatial partials commute, `∂^α (∂_j g) = ∂^{α+e_j} g`,
and the Laplacian commutes with `∂^α`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section



namespace CIV

/-- A jointly smooth field on `Ω × I` has smooth time slices. -/
theorem contDiffOn_slice_of_spaceTimeSet {g : ParabolicPoint → ℝ} {Ω : Set Vec3} {I : Set ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {t : ℝ}
    (ht : t ∈ I) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω := by
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) Ω :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  exact hg.comp hmap fun x hx => ⟨hx, ht⟩

/-- The time slice of a spatial partial derivative is smooth. -/
theorem contDiffOn_slice_spatialPartial {g : ParabolicPoint → ℝ} {Ω : Set Vec3}
    (hΩ : IsOpen Ω) (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω)
    (j : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => spatialPartial g j (x, t)) Ω := by
  have h := contDiffOn_foldr_axisDeriv Ω hΩ (fun x : Vec3 => g (x, t)) hG [j]
  simp only [List.foldr_cons, List.foldr_nil] at h
  exact h

/-- Spatial partial derivatives commute on a time slice. -/
theorem spatialPartial_comm_spaceTimeSet {g : ParabolicPoint → ℝ} {Ω : Set Vec3}
    (hΩ : IsOpen Ω) (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω)
    {x : Vec3} (hx : x ∈ Ω) (i j : Fin 3) :
    spatialPartial (fun w => spatialPartial g i w) j (x, t) =
      spatialPartial (fun w => spatialPartial g j w) i (x, t) :=
  axisDeriv_axisDeriv_symm Ω hΩ (fun y : Vec3 => g (y, t)) hG j i x hx

/-- `∂^α (∂_j g) = ∂^{α + e_j} g` on a time slice. -/
theorem multiPartial_spatialPartial_spaceTimeSet {g : ParabolicPoint → ℝ} {Ω : Set Vec3}
    (hΩ : IsOpen Ω) (t : ℝ) (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω)
    {x : Vec3} (hx : x ∈ Ω) (α : Fin 3 → ℕ) (j : Fin 3) :
    multiPartial (fun w => spatialPartial g j w) α (x, t) =
      multiPartial g (α + Pi.single j 1) (x, t) := by
  let l : List (Fin 3) := List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
    ++ List.replicate (α 2) (2 : Fin 3)
  have hslice : (fun x : Vec3 => spatialPartial g j (x, t)) =
      axisDeriv j (fun x : Vec3 => g (x, t)) := rfl
  have h_fun_eq : (fun y : Vec3 => multiPartial (fun w => spatialPartial g j w) α (y, t)) =
      List.foldr axisDeriv (fun x : Vec3 => g (x, t)) (l ++ [j]) := by
    rw [multiPartial_slice (fun w => spatialPartial g j w) α t]
    rw [hslice]
    simp [l, foldr_axisDeriv_replicate, List.foldr_append]
  let β : Fin 3 → ℕ := fun i => α i + (if i = j then 1 else 0)
  have hβ_eq : β = α + Pi.single j 1 := by
    ext i; simp [β, Pi.single_apply]
  have h_target_eq : multiPartial g β (x, t) =
      List.foldr axisDeriv (fun x : Vec3 => g (x, t))
        (List.replicate (β 0) (0 : Fin 3)
        ++ List.replicate (β 1) (1 : Fin 3)
        ++ List.replicate (β 2) (2 : Fin 3)) x := by
    have h_slice := congrFun (multiPartial_slice g β t) x
    simpa [foldr_axisDeriv_replicate, List.foldr_append] using h_slice
  have h_perm : (l ++ [j]).Perm (List.replicate (β 0) (0 : Fin 3)
      ++ List.replicate (β 1) (1 : Fin 3) ++ List.replicate (β 2) (2 : Fin 3)) := by
    rw [List.perm_iff_count]
    intro c
    fin_cases c <;> fin_cases j <;>
      dsimp [l, β] <;>
      simp [List.count_append, List.count_replicate]
  have h_eq_on := eqOn_foldr_axisDeriv_of_perm Ω hΩ (fun x : Vec3 => g (x, t)) hG h_perm
  calc multiPartial (fun w => spatialPartial g j w) α (x, t)
      = List.foldr axisDeriv (fun x : Vec3 => g (x, t)) (l ++ [j]) x :=
        congrFun h_fun_eq x
    _ = multiPartial g β (x, t) := by rw [h_eq_on hx, h_target_eq]
    _ = multiPartial g (α + Pi.single j 1) (x, t) := by rw [hβ_eq]

/-- The Laplacian commutes with `∂^α` on a time slice. -/
theorem sum_spatialSecondPartial_multiPartial_spaceTimeSet {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} (hΩ : IsOpen Ω) (t : ℝ)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω) {x : Vec3} (hx : x ∈ Ω)
    (α : Fin 3 → ℕ) :
    ∑ j, spatialSecondPartial (multiPartial g α) j j (x, t) =
      multiPartial (fun w => ∑ j, spatialSecondPartial g j j w) α (x, t) := by
  have hsm : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec3 => spatialSecondPartial g j j (y, t)) Ω := by
    intro j _
    exact contDiffOn_slice_spatialPartial (g := fun w => spatialPartial g j w) hΩ t
      (contDiffOn_slice_spatialPartial hΩ t hG j) j
  rw [multiPartial_finset_sum hΩ t hsm α hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL : spatialSecondPartial (multiPartial g α) j j (x, t) =
      multiPartial g (α + Pi.single j 2) (x, t) :=
    axisDeriv_axisDeriv_multiPartial_slice_eq_single hΩ t hG α j hx
  have hR1 : multiPartial (fun w => spatialSecondPartial g j j w) α (x, t) =
      multiPartial (fun w => spatialPartial g j w) (α + Pi.single j 1) (x, t) :=
    multiPartial_spatialPartial_spaceTimeSet (g := fun w => spatialPartial g j w) hΩ t
      (contDiffOn_slice_spatialPartial hΩ t hG j) hx α j
  have hR2 := multiPartial_spatialPartial_spaceTimeSet hΩ t hG hx (α + Pi.single j 1) j
  rw [hL, hR1, hR2]
  congr 1
  ext i
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

end CIV
