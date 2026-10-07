/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn

/-!
# Lipschitz Bound Of Pointwise Limit

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter
open scoped NNReal Topology
open CKN

noncomputable section
namespace CIV

/-- A pointwise limit of uniformly `K`-Lipschitz functions is `K`-Lipschitz. -/
theorem lipschitzWith_of_tendsto {α : Type*} [PseudoMetricSpace α] {F : Type*}
    [NormedAddCommGroup F] {f : ℕ → α → F} {g : α → F} {K : ℝ≥0}
    (hf : ∀ n, LipschitzWith K (f n))
    (hg : ∀ x, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    LipschitzWith K g := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  refine le_of_tendsto' ((hg x).dist (hg y)) fun n => ?_
  exact (lipschitzWith_iff_dist_le_mul.mp (hf n)) x y

/-- A pointwise limit of functions uniformly bounded by `M` is bounded by `M`. -/
theorem norm_le_of_tendsto {α : Type*} {F : Type*} [NormedAddCommGroup F]
    {f : ℕ → α → F} {g : α → F} {M : ℝ} (hf : ∀ n x, ‖f n x‖ ≤ M)
    (hg : ∀ x, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    ∀ x, ‖g x‖ ≤ M := by
  intro x
  have hnorm : Tendsto (fun n => ‖f n x‖) atTop (𝓝 ‖g x‖) := (hg x).norm
  refine le_of_tendsto' hnorm fun n => hf n x

/-- A pointwise limit of uniformly Lipschitz, uniformly bounded functions
preserves both bounds with the same constants. -/
theorem lipschitzWith_and_norm_le_of_tendsto {α : Type*} [PseudoMetricSpace α] {F : Type*}
    [NormedAddCommGroup F] {f : ℕ → α → F} {g : α → F} {K : ℝ≥0} {M : ℝ}
    (hLip : ∀ n, LipschitzWith K (f n)) (hBd : ∀ n x, ‖f n x‖ ≤ M)
    (hg : ∀ x, Tendsto (fun n => f n x) atTop (nhds (g x))) :
    (∀ x, ‖g x‖ ≤ M) ∧ LipschitzWith K g := by
  exact ⟨norm_le_of_tendsto hBd hg, lipschitzWith_of_tendsto hLip hg⟩

/-- A.e.-in-time limit of uniformly Lipschitz, uniformly bounded approximating
sequences inherits the same Lipschitz and boundedness constants. -/
theorem ae_lipschitzWith_and_norm_le_of_tendsto {m : ℕ} {Bn : ℕ → Vec m × ℝ → Vec m}
    {B : Vec m × ℝ → Vec m} {Λ : ℝ≥0} {J : Set ℝ}
    (hLip : ∀ n τ, LipschitzWith Λ (fun x => Bn n (x, τ)))
    (hBd : ∀ n τ x, ‖Bn n (x, τ)‖ ≤ (Λ : ℝ))
    (hconv : ∀ᵐ τ ∂(volume.restrict J),
      ∀ x, Tendsto (fun n => Bn n (x, τ)) atTop (nhds (B (x, τ)))) :
    ∀ᵐ τ ∂(volume.restrict J), (∀ x, ‖B (x, τ)‖ ≤ (Λ : ℝ)) ∧ LipschitzWith Λ (fun x => B (x, τ))
      := by
  refine hconv.mono fun τ hτ => ?_
  exact lipschitzWith_and_norm_le_of_tendsto (f := fun n x => Bn n (x, τ))
    (fun n => hLip n τ) (fun n => hBd n τ) hτ

/-- A.e.-in-space-time limit of uniformly bounded scalar fields is bounded by the
same constant. -/
theorem ae_norm_le_of_tendsto {m : ℕ} {qn : ℕ → Vec m × ℝ → ℝ} {q : Vec m × ℝ → ℝ} {M : ℝ}
    {J : Set ℝ}
    (hBd : ∀ n z, |qn n z| ≤ M)
    (hconv : ∀ᵐ z ∂(volume.restrict (univ ×ˢ J)),
      Tendsto (fun n => qn n z) atTop (nhds (q z))) :
    ∀ᵐ z ∂(volume.restrict (univ ×ˢ J)), |q z| ≤ M := by
  refine hconv.mono fun z hz => ?_
  refine le_of_tendsto' (hz.abs) fun n => hBd n z

end CIV
