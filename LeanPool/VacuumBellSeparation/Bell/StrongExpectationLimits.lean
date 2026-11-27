/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs

/-!
# Bounded strong products and the three vacuum expectations

Strong convergence of both factors, with a uniform bound on the left,
proves strong convergence of the product. Independent nets therefore
preserve every closed continuous inequality in the two marginal vacuum
expectations and their joint expectation.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem strong_tendsto_mul_of_bounded {ι : Type*} {l : Filter ι}
    {As Bs : ι → H →L[ℂ] H} {A B : H →L[ℂ] H} {C : ℝ}
    (hbound : ∀ i, ‖As i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hB : ∀ x, Tendsto (fun i => Bs i x) l (𝓝 (B x))) (x : H) :
    Tendsto (fun i => (As i * Bs i) x) l (𝓝 ((A * B) x)) := by
  have hb := ((hB x).sub (tendsto_const_nhds (x := B x))).norm
  have ha := ((hA (B x)).sub (tendsto_const_nhds (x := A (B x)))).norm
  have hzero : Tendsto (fun i => C * ‖Bs i x - B x‖ + ‖As i (B x) - A (B x)‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero, add_zero] using (hb.const_mul C).add ha
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) _ hzero
  intro i
  calc
    ‖(As i * Bs i) x - (A * B) x‖ =
        ‖As i (Bs i x - B x) + (As i (B x) - A (B x))‖ := by
      congr 1
      simp only [mul_apply_eq_comp, map_sub]
      abel
    _ ≤ ‖As i (Bs i x - B x)‖ + ‖As i (B x) - A (B x)‖ := norm_add_le _ _
    _ ≤ C * ‖Bs i x - B x‖ + ‖As i (B x) - A (B x)‖ :=
      add_le_add ((As i).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg _))) le_rfl

/-- Vacuum expectation triple given by `((inner ℂ Ω (A Ω)).re, (inner ℂ Ω (B Ω)).re, (inner ℂ Ω ((A
* B) Ω)).re)`. -/
noncomputable def vacuumExpectationTriple (Ω : H) (A B : H →L[ℂ] H) : ℝ × ℝ × ℝ :=
  ((inner ℂ Ω (A Ω)).re, (inner ℂ Ω (B Ω)).re, (inner ℂ Ω ((A * B) Ω)).re)

omit [CompleteSpace H] in
theorem tendsto_vacuumExpectationTriple {ι : Type*} {l : Filter ι}
    (Ω : H) {As Bs : ι → H →L[ℂ] H} {A B : H →L[ℂ] H} {C : ℝ}
    (hbound : ∀ i, ‖As i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hB : ∀ x, Tendsto (fun i => Bs i x) l (𝓝 (B x))) :
    Tendsto (fun i => vacuumExpectationTriple Ω (As i) (Bs i)) l
      (𝓝 (vacuumExpectationTriple Ω A B)) := by
  have heval : Continuous (fun x : H => (inner ℂ Ω x).re) := by fun_prop
  exact (heval.continuousAt.tendsto.comp (hA Ω)).prodMk_nhds
    ((heval.continuousAt.tendsto.comp (hB Ω)).prodMk_nhds
      (heval.continuousAt.tendsto.comp (strong_tendsto_mul_of_bounded hbound hA hB Ω)))

omit [CompleteSpace H] in
/-- Independent approximation nets suffice; the limiting inequality is actual, not formal. -/
theorem vacuum_inequality_of_independent_strong_limits
    {ι κ : Type*} {l : Filter ι} {k : Filter κ} [l.NeBot] [k.NeBot]
    (Ω : H) {As : ι → H →L[ℂ] H} {Bs : κ → H →L[ℂ] H}
    {A B : H →L[ℂ] H} {C : ℝ} (hbound : ∀ i, ‖As i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => As i x) l (𝓝 (A x)))
    (hB : ∀ x, Tendsto (fun j => Bs j x) k (𝓝 (B x)))
    (f : ℝ × ℝ × ℝ → ℝ) (hf : Continuous f)
    (hineq : ∀ᶠ q : ι × κ in l ×ˢ k, f (vacuumExpectationTriple Ω (As q.1) (Bs q.2)) ≤ 0) :
    f (vacuumExpectationTriple Ω A B) ≤ 0 := by
  have ht := tendsto_vacuumExpectationTriple Ω (fun q : ι × κ => hbound q.1)
    (fun x => (hA x).comp tendsto_fst) (fun x => (hB x).comp tendsto_snd)
  exact (isClosed_Iic.mem_of_tendsto (hf.continuousAt.tendsto.comp ht) hineq)

end VacuumBellSeparation
