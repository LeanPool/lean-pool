/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Tori.Embedding
public import LeanPool.ArnoldKAM.Arnold1963.Dynamics.TorusDensity

/-!
The projected orbit closure equals the invariant torus, using nonresonant flow density.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963.Iteration.InitialData
local instance : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem projected_orbit_closure {p : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (q : RealSpace n) :
    closure (range (fun t : ℝ => torusProjection (realPartPhase (h.orbit b p q t)))) =
      h.invariantTorus b p := by
  let v := realPart (h.limitFrequency b (complexify p))
  have hnr : ∀ k : FourierIndex n, k ≠ 0 → ∑ j, (k j : ℝ) * v j ≠ 0 := by
    intro k hk he
    apply h.limitFrequency_no_integer_relation b hp k hk
    rw [← h.limitFrequency_real_value b hp]
    change (∑ j, (k j : ℂ) * ((v j : ℝ) : ℂ)) = 0
    exact_mod_cast he
  have hd := denseRange_realTorusLine v q hnr
  have hc := h.torusEmbedding_continuous b hp
  have he : (fun t : ℝ => torusProjection (realPartPhase (h.orbit b p q t))) =
      h.torusEmbedding b p ∘ realTorusLine v q := by
    funext t
    rw [h.orbit_eq_real_angle b hp q t]
    exact (h.torusEmbedding_lift b hp (q + t • v)).symm
  rw [he, ← h.torusEmbedding_range b p, range_comp]
  apply Subset.antisymm
  · exact closure_minimal (image_subset_range _ _) (isCompact_range hc).isClosed
  · rintro z ⟨Q, rfl⟩
    exact image_closure_subset_closure_image hc ⟨Q, hd Q, rfl⟩

end KamProject.Arnold1963.Iteration.InitialData
