/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Geodesic phase equation

A geodesic for the connection `D + σ K` is an integral curve of the phase
field `(x,v) ↦ (v, -σ K_x(v,v))`. This file proves local initial-value
existence from smooth coefficients. It does not assume parameter regularity.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace PlanarMidpoint

/-- Position and velocity in the product normed phase space. -/
abbrev Phase := E × E

/-- The acceleration field of the affine geodesic equation. -/
def phaseField (C : E → Coeff) (σ : ℝ) (z : Phase) : Phase :=
  (z.2, -σ • K (C z.1) z.2 z.2)

theorem contDiffAt_K {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {n : ℕ∞ω} {c : A → Coeff} {u v : A → E} {x : A}
    (hc : ContDiffAt ℝ n c x) (hu : ContDiffAt ℝ n u x) (hv : ContDiffAt ℝ n v x) :
    ContDiffAt ℝ n (fun y ↦ K (c y) (u y) (v y)) x := by
  apply (contDiffAt_piLp 2).2
  intro i
  fin_cases i <;> dsimp [K, vec]
  all_goals
    have hci (j : Fin 4) := (contDiffAt_pi.mp hc) j
    have hui (j : Fin 2) := (contDiffAt_piLp 2).mp hu j
    have hvi (j : Fin 2) := (contDiffAt_piLp 2).mp hv j
    fun_prop

theorem contDiffAt_phaseField {C : E → Coeff} {p : E} {v : E} {n : ℕ∞ω}
    (hC : ContDiffAt ℝ n C p) (σ : ℝ) :
    ContDiffAt ℝ n (phaseField C σ) (p, v) := by
  exact contDiffAt_snd.prodMk ((contDiffAt_K
    (hC.comp (p, v) contDiffAt_fst) contDiffAt_snd contDiffAt_snd).const_smul (-σ))

theorem exists_local_geodesic {C : E → Coeff} {p v : E}
    (hC : ContDiffAt ℝ 1 C p) (σ t₀ : ℝ) :
    ∃ z : ℝ → Phase, z t₀ = (p, v) ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt z (phaseField C σ (z t)) t := by
  exact (contDiffAt_phaseField hC
      σ).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

theorem geodesic_components {C : E → Coeff} {σ : ℝ} {z : ℝ → Phase} {t : ℝ}
    (hz : HasDerivAt z (phaseField C σ (z t)) t) :
    HasDerivAt (fun s ↦ (z s).1) (z t).2 t ∧
      HasDerivAt (fun s ↦ (z s).2) (-σ • K (C (z t).1) (z t).2 (z t).2) t := by
  exact ⟨hz.fst, hz.snd⟩

/-- Two actual geodesics with the same initial phase have the same local germ. -/
theorem local_geodesic_unique {C : E → Coeff} {p v : E} {σ t₀ : ℝ}
    (hC : ContDiffAt ℝ 1 C p) {z w : ℝ → Phase}
    (hz₀ : z t₀ = (p, v)) (hw₀ : w t₀ = (p, v))
    (hz : ∀ᶠ t in 𝓝 t₀, HasDerivAt z (phaseField C σ (z t)) t)
    (hw : ∀ᶠ t in 𝓝 t₀, HasDerivAt w (phaseField C σ (w t)) t) :
    z =ᶠ[𝓝 t₀] w := by
  obtain ⟨L, S, hS, hLip⟩ := (contDiffAt_phaseField (v := v) hC σ).exists_lipschitzOnWith
  have hzc : ContinuousAt z t₀ := (hz.self_of_nhds).continuousAt
  have hwc : ContinuousAt w t₀ := (hw.self_of_nhds).continuousAt
  have hzS : ∀ᶠ t in 𝓝 t₀, z t ∈ S := hzc (hz₀ ▸ hS)
  have hwS : ∀ᶠ t in 𝓝 t₀, w t ∈ S := hwc (hw₀ ▸ hS)
  exact ODE_solution_unique_of_eventually
    (v := fun _ ↦ phaseField C σ) (s := fun _ ↦ S)
    (Filter.Eventually.of_forall fun _ ↦ hLip) (hz.and hzS) (hw.and hwS)
    (hz₀.trans hw₀.symm)

@[simp] theorem phaseField_zero (C : E → Coeff) (σ : ℝ) (p : E) :
    phaseField C σ (p, 0) = 0 := by
  apply Prod.ext
  · rfl
  · apply vec_ext <;> simp [phaseField, K]

/-- The constant curve is the geodesic with zero initial velocity. -/
theorem constant_geodesic (C : E → Coeff) (σ : ℝ) (p : E) (t : ℝ) :
    HasDerivAt (fun _ : ℝ ↦ (p, (0 : E)))
      (phaseField C σ (p, 0)) t := by
  simpa only [phaseField_zero] using hasDerivAt_const t (p, (0 : E))

/-- The acceleration has zero strict derivative at every zero-velocity phase.
Consequently its local Lipschitz constant can be made arbitrarily small. -/
theorem hasStrictFDerivAt_acceleration_zero {C : E → Coeff} {p : E}
    (hC : ContDiffAt ℝ 1 C p) (σ : ℝ) :
    HasStrictFDerivAt (𝕜 := ℝ) (fun z : Phase ↦ -σ • K (C z.1) z.2 z.2) 0 (p, 0) := by
  have hc (i : Fin 4) := (hasStrictFDerivAt_apply (𝕜 := ℝ) i (C p)).comp (p, (0 : E))
    ((hC.hasStrictFDerivAt one_ne_zero).comp (p, (0 : E)) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p :=
        (p, (0 : E)))))
  have hu (j : Fin 2) := (PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (0 : E) j).comp
    (p, (0 : E)) (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (p, (0 : E))))
  have hterm (i : Fin 4) (j k : Fin 2) :
      HasStrictFDerivAt (𝕜 := ℝ) (fun z : Phase ↦ C z.1 i * z.2 j * z.2 k) 0 (p, 0) := by
    convert ((hc i).mul (hu j)).mul (hu k) using 1; simp
  have hk : HasStrictFDerivAt (𝕜 := ℝ) (fun z : Phase ↦ K (C z.1) z.2 z.2) 0 (p, 0) := by
    apply (hasStrictFDerivAt_piLp 2).2
    intro i
    fin_cases i
    · convert (((hterm 0 0 0).add (hterm 1 0 1)).add
        (hterm 1 1 0)).add (hterm 2 1 1) using 1
      · ext z
        simp [K]
        ring
      · simp
    · convert (((hterm 1 0 0).add (hterm 2 0 1)).add
        (hterm 2 1 0)).add (hterm 3 1 1) using 1
      · ext z
        simp [K]
        ring
      · simp
  convert hk.const_smul (-σ) using 1; simp

end PlanarMidpoint
