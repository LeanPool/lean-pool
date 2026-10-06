/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitRepresentative

/-!
# A measurable field for the all-time local trace

The weakly continuous local `L³` trace admits a jointly measurable
representative that retains its uniform bound on every time slice.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The jointly measurable representative agrees with the original source
field on almost every inner-ball time slice. -/
theorem blowup_limit_trace_eq_source_ae_slices
    {u : ParabolicPoint → Vec3}
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hrep : ∀ t,
      (fun x => W (x,t)) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
        (fun x => weakContL3OfLp (v t x)))
    (htrace : ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        ∃ huSlice : MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x,t))) 3
          (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))),
          v ⟨t, ht⟩ = huSlice.toLp _) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
      ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (fun x => W (x,⟨t,ht⟩)) =ᵐ[volume.restrict
          (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
          (fun x => u (x,t)) := by
  filter_upwards [htrace] with t htrace
  rcases htrace with ⟨ht, huSlice, hvEq⟩
  refine ⟨ht, ?_⟩
  have hvAE : (fun x : Vec3 => v ⟨t,ht⟩ x) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => huSlice.toLp _ x) := Lp.ext_iff.mp hvEq
  filter_upwards [hrep ⟨t,ht⟩, hvAE, huSlice.coeFn_toLp] with x hxrep hxv hxu
  calc
    W (x,⟨t,ht⟩) = weakContL3OfLp (v ⟨t,ht⟩ x) := hxrep
    _ = weakContL3OfLp (huSlice.toLp _ x) := congrArg weakContL3OfLp hxv
    _ = weakContL3OfLp (WithLp.toLp 2 (u (x,t))) := congrArg weakContL3OfLp hxu
    _ = u (x,t) := by
      change WithLp.ofLp (WithLp.toLp 2 (u (x,t))) = u (x,t)
      rfl

end ESS
