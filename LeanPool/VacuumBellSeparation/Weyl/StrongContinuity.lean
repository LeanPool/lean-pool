/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Weyl.Existence

/-!
# Strong continuity in the one-particle norm

For the actual Gaussian-kernel construction, convergence of the labels in
one-particle norm implies strong convergence of the Weyl operators. The label
space itself need not have a topology. The proof first treats the Gaussian
vectors, then their linear span, and finally its closure using the common
isometry bound.
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology
open scoped InnerProductSpace

variable {X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem tendsto_weylKernel (u : X → K) {α : Type*} {l : Filter α}
    {F G : α → X} {F₀ G₀ : X}
    (hF : Tendsto (fun i => u (F i)) l (𝓝 (u F₀)))
    (hG : Tendsto (fun i => u (G i)) l (𝓝 (u G₀))) :
    Tendsto (fun i => weylKernel u (F i) (G i)) l (𝓝 (weylKernel u F₀ G₀)) := by
  have hc : Continuous (fun p : K × K => weylKernel id p.1 p.2) := by
    unfold weylKernel
    dsimp only [id_eq]
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (((continuous_fst.norm.pow 2).neg.div_const 2).sub
          ((continuous_snd.norm.pow 2).div_const 2))).add
            (continuous_fst.inner continuous_snd))
  have hp : Tendsto (fun i => (u (F i), u (G i))) l (𝓝 (u F₀, u G₀)) :=
    hF.prodMk_nhds hG
  simpa only [Function.comp_def, weylKernel, id_eq] using
    (hc.continuousAt (x := (u F₀, u G₀))).tendsto.comp hp

/-- Actual convergence of the kernel vectors, proved from their Gram formula. -/
theorem tendsto_weylVec (u : X → K) {α : Type*} {l : Filter α}
    {F : α → X} {F₀ : X}
    (hF : Tendsto (fun i => u (F i)) l (𝓝 (u F₀))) :
    Tendsto (fun i => weylVec u (F i)) l (𝓝 (weylVec u F₀)) := by
  have ht := ((tendsto_weylKernel u hF hF).sub
      (tendsto_weylKernel u (F := fun _ => F₀) (F₀ := F₀) tendsto_const_nhds hF)).sub
    ((tendsto_weylKernel u (G := fun _ => F₀) (G₀ := F₀) hF tendsto_const_nhds).sub
      (tendsto_const_nhds (x := weylKernel u F₀ F₀)))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_sub_left, inner_sub_right,
    inner_weylVec, Function.comp_def, RCLike.re_to_complex, sub_self, Complex.zero_re,
      Real.sqrt_zero]
    using hs

theorem tendsto_weylPhase (u : X → K) {α : Type*} {l : Filter α}
    {F : α → X} {F₀ : X} (G : X)
    (hF : Tendsto (fun i => u (F i)) l (𝓝 (u F₀))) :
    Tendsto (fun i => weylPhase u (F i) G) l (𝓝 (weylPhase u F₀ G)) := by
  have hc : Continuous (fun x : K =>
      Complex.exp (-(Complex.I * ((⟪x, u G⟫_ℂ).im : ℂ)))) := by fun_prop
  exact hc.continuousAt.tendsto.comp hF

/-- Strong convergence on every vector follows from actual one-particle norm
convergence, with no density or continuity assumption added to the statement. -/
theorem tendsto_weylOp [AddGroup X] (u : X → K)
    (hu : ∀ F G, u (F + G) = u F + u G)
    {α : Type*} {l : Filter α} {F : α → X} {F₀ : X}
    (hF : Tendsto (fun i => u (F i)) l (𝓝 (u F₀))) (x : WeylSpace u) :
    Tendsto (fun i => weylOp u hu (F i) x) l (𝓝 (weylOp u hu F₀ x)) := by
  have hequi : Equicontinuous (fun (i : α) (x : WeylSpace u) => weylOp u hu (F i) x) :=
    Metric.equicontinuous_of_continuity_modulus id tendsto_id _
      (fun x y i => ((weylOp u hu (F i)).isometry.dist_eq x y).le)
  have hclosed := hequi.isClosed_setOfPred_tendsto (l := l) (weylOp u hu F₀).continuous
  have hd : Dense (Submodule.span ℂ (Set.range (weylVec u)) : Set (WeylSpace u)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (weylVec_dense u)
  refine hd.induction (P := fun y =>
    Tendsto (fun i => weylOp u hu (F i) y) l (𝓝 (weylOp u hu F₀ y))) ?_ hclosed x
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨G, rfl⟩ := hy
      have hFG : Tendsto (fun i => u (F i + G)) l (𝓝 (u (F₀ + G))) := by
        simpa only [hu] using hF.add (tendsto_const_nhds (x := u G))
      simpa only [weylOp_weylVec] using
        (tendsto_weylPhase u G hF).smul (tendsto_weylVec u hFG)
  | zero => simpa only [map_zero] using (tendsto_const_nhds (x := (0 : WeylSpace u)))
  | add y z hy hz ihy ihz => simpa only [map_add] using ihy.add ihz
  | smul c y hy ih => simpa only [map_smul] using
      (tendsto_const_nhds (x := c)).smul ih

theorem tendsto_weylCLM_strong [AddGroup X] (u : X → K)
    (hu : ∀ F G, u (F + G) = u F + u G)
    {α : Type*} {l : Filter α} {F : α → X} {F₀ : X}
    (hF : Tendsto (fun i => u (F i)) l (𝓝 (u F₀))) (x : WeylSpace u) :
    Tendsto (fun i => weylCLM u hu (F i) x) l (𝓝 (weylCLM u hu F₀ x)) :=
  tendsto_weylOp u hu hF x

/-- In particular, the full one-particle Weyl representation is strongly
continuous in its Hilbert-space label. -/
theorem continuous_weylCLM_id_apply (x : WeylSpace (id : K → K)) :
    Continuous (fun z : K => weylCLM id (fun _ _ => rfl) z x) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact tendsto_weylCLM_strong id (fun _ _ => rfl) tendsto_id x

end VacuumBellSeparation
