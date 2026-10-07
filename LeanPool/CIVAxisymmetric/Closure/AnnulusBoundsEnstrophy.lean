/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Identities.PlaneTransfer

/-!
# Annulus Bounds Enstrophy

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

private lemma multiPartial_single_eq_spatialPartial (g : ParabolicPoint → ℝ) (j : Fin 3)
    (z : ParabolicPoint) :
    multiPartial g (fun k => if k = j then 1 else 0) z = spatialPartial g j z := by
  fin_cases j <;> simp [multiPartial]

/-- The second-order derivative bound supplied by `lem:aniso:annulus` on the regular annulus
reduces to pointwise bounds on the velocity `u` and the vorticity `vorticityField u`:
`|u_i| ≤ M` and `|ω_i| ≤ 2M` whenever the multi-index bound `hbound` holds on the annulus
`Rm < ‖x‖ < Rp`. This is the translation that `cutoff_enstrophy_balance` needs to connect
the closed-set hypothesis it receives to the open-annulus hypothesis `lem:aniso:annulus`
provides. -/
theorem abs_apply_and_vorticityField_le_of_multiPartial_le
    {u : ParabolicPoint → Vec3} {Rm Rp t₀ M : ℝ}
    (hbound : ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3, ∀ α : Fin 3 → ℕ, α 0 + α 1 + α 2 ≤ 2 →
        |multiPartial (fun w => u w i) α (x, t)| ≤ M) (hM : 0 ≤ M) :
    ∀ x : Vec3, Rm < vec3EuclideanNorm x → vec3EuclideanNorm x < Rp →
      ∀ t ∈ Ioo t₀ (0 : ℝ), ∀ i : Fin 3,
        |u (x, t) i| ≤ M ∧ |vorticityField u (x, t) i| ≤ 2 * M := by
  intro x hxRm hxRp t ht i
  -- bound on |u (x, t) i|
  have hu_bound : |u (x, t) i| ≤ M := by
    have h := hbound x hxRm hxRp t ht i (fun _ => 0) (by norm_num)
    have hM_abs : |M| = M := abs_of_nonneg hM
    simpa [multiPartial, hM_abs] using h
  -- bound on |vorticityField u (x, t) i|
  have hω_bound : |vorticityField u (x, t) i| ≤ 2 * M := by
    have h1 : |multiPartial (fun w => u w (i + 2))
        (fun k => if k = i + 1 then 1 else 0) (x, t)| ≤ M :=
      hbound x hxRm hxRp t ht (i + 2) (fun k => if k = i + 1 then 1 else 0)
        (by fin_cases i <;> decide)
    have h2 : |multiPartial (fun w => u w (i + 1))
        (fun k => if k = i + 2 then 1 else 0) (x, t)| ≤ M :=
      hbound x hxRm hxRp t ht (i + 1) (fun k => if k = i + 2 then 1 else 0)
        (by fin_cases i <;> decide)
    have ha := abs_le.1 h1
    have hb := abs_le.1 h2
    have hsub : |multiPartial (fun w => u w (i + 2))
        (fun k => if k = i + 1 then 1 else 0) (x, t)
        - multiPartial (fun w => u w (i + 1))
        (fun k => if k = i + 2 then 1 else 0) (x, t)| ≤ 2 * M :=
      abs_le.2 ⟨by linarith only [ha.1, hb.2], by linarith only [ha.2, hb.1]⟩
    rw [multiPartial_single_eq_spatialPartial (fun w => u w (i + 2)) (i + 1) (x, t),
      multiPartial_single_eq_spatialPartial (fun w => u w (i + 1)) (i + 2) (x, t)] at hsub
    simpa [vorticityField, curlComp] using hsub
  exact And.intro hu_bound hω_bound

end CIV
