/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Dynamics.RealOrbits
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Connected.Clopen

/-!
Uniqueness of analytic autonomous trajectories, including trajectories from different labels.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace KamProject.Arnold1963

theorem eq_of_analytic_autonomous_orbits {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : E → E} {f g : ℝ → E}
    (ha : ∀ t, AnalyticAt ℂ X (f t))
    (hf : ∀ t, HasDerivAt f (X (f t)) t)
    (hg : ∀ t, HasDerivAt g (X (g t)) t)
    (he : f 0 = g 0) : f = g := by
  have hc : IsClosed {t | f t = g t} :=
    isClosed_eq (continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt)
      (continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt)
  have ho : IsOpen {t | f t = g t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change f t = g t at ht
    obtain ⟨K, U, hU, hL⟩ := (ha t).contDiffAt.exists_lipschitzOnWith
    have hfu : ∀ᶠ s in 𝓝 t, f s ∈ U := (hf t).continuousAt hU
    have hgu : ∀ᶠ s in 𝓝 t, g s ∈ U := (hg t).continuousAt (by simpa only [← ht] using hU)
    exact ODE_solution_unique_of_eventually (v := fun _ => X) (s := fun _ => U)
      (Eventually.of_forall fun _ => hL)
      (hfu.mono fun s hs => ⟨hf s, hs⟩) (hgu.mono fun s hs => ⟨hg s, hs⟩) ht
  have hu := (show IsClopen {t | f t = g t} from ⟨hc, ho⟩).eq_univ ⟨0, he⟩
  funext t
  exact show t ∈ {t | f t = g t} from hu ▸ mem_univ t

namespace Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem orbit_eq_of_initial_eq {p p' : RealSpace n}
    (hp : p ∈ realSlice (h.limitDomain b)) (hp' : p' ∈ realSlice (h.limitDomain b))
    (q q' : RealSpace n) (he : h.orbit b p q 0 = h.orbit b p' q' 0) :
    h.orbit b p q = h.orbit b p' q' :=
  eq_of_analytic_autonomous_orbits
    (fun t => h.vectorField_analytic b 0 _ (h.orbit_mem_initial b hp q t))
    (h.orbit_hasDerivAt b hp q) (h.orbit_hasDerivAt b hp' q') he

end Iteration.InitialData
end KamProject.Arnold1963
