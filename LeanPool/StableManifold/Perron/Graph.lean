/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Perron.Operator
import LeanPool.StableManifold.Orbit
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import LeanPool.StableManifold.Sequence.Superpose

/-!
# The stable manifold of a small Lipschitz perturbation of a hyperbolic linear map

Let `S` be a hyperbolic splitting of `A` on a real Banach space `E` (projection `P`, constants
`C`, `λ`), and `F x = A x + φ x` a **globally** small Lipschitz perturbation: `φ 0 = 0` and `φ` is
`L`-Lipschitz with `L * S.bound ≤ 1 / 2` (`StableManifold.Perturbation`). Perron's method:

* `Perturbation.perronMap ξ x = stableOrbit ξ + perronOp (superpose φ x)` is a `1/2`-contraction
  of the Banach space `ℕ →ᵇ E` of bounded sequences (`contractingWith_perronMap`); its fixed
  points are the bounded `F`-orbits with stable component `P ξ` at time `0`
  (`Perron.Operator`);
* `Perturbation.orbitSeq ξ`: the fixed point, the unique bounded `F`-orbit with
  `P (orbitSeq ξ 0) = P ξ`; it depends Lipschitz-continuously on `ξ` (`dist_orbitSeq_le`) and decays
  geometrically, `‖orbitSeq ξ n‖ ≤ 2 C θⁿ ‖P ξ‖` with `θ = S.decayRate`
  (`norm_orbitSeq_apply_le`);
* `Perturbation.graph ξ = (1 - P) (orbitSeq ξ 0)`: a Lipschitz map, constant along the unstable
  directions (`graph_proj`), with values in the unstable subspace (`proj_graph`) and `graph 0 = 0`.

**The global stable manifold** (`bddOrbit_iff`): the `F`-orbit of `x` is bounded if and only if
`(1 - P) x = graph x`, that is `x = P x + graph (P x)` lies on the graph of `graph` over the stable
subspace; such orbits tend to `0` geometrically (`norm_iterate_le`). If `φ` has derivative `0` at
`0`, the graph is tangent to the stable subspace: `graph` has derivative `0` at `0`
(`hasFDerivAt_graph_zero`).

## Proofs

* `contractingWith_perronMap`: `superpose φ` is `L`-Lipschitz (`lipschitzWith_superpose`), so
  `perronMap ξ` is `‖perronOp‖ L`-Lipschitz (`LipschitzWith.const`, `LipschitzWith.add`,
  `ContinuousLinearMap.lipschitzWith`, `LipschitzWith.comp`), and
  `‖perronOp‖ L ≤ S.bound L ≤ 1/2` (`norm_perronOp_le`, `LipschitzWith.weaken`).
* `orbitSeq` is `ContractingWith.fixedPoint`. `orbitSeq_succ`, `proj_orbitSeq_apply_zero`: the
  fixed point equation, with `stableOrbit_add_perronOp_succ`,
  `proj_stableOrbit_add_perronOp_zero` and `superpose_apply_of_lipschitzWith`.
* `eq_orbitSeq_of_forall_succ`: by `eq_stableOrbit_add_perronOp`, a bounded orbit `x` is a fixed
  point of `perronMap (x 0)`, hence `orbitSeq (x 0)` (`ContractingWith.fixedPoint_unique`).
  `orbitSeq_proj`: `perronMap (P ξ) = perronMap ξ` (`stableOrbit_proj`). `orbitSeq_zero`: `0` is
  the fixed point of `perronMap 0` (`superpose_zero`).
* `dist_orbitSeq_le`: `ContractingWith.fixedPoint_lipschitz_in_map` for two `1/2`-contractions
  whose values differ by `stableOrbit ξ - stableOrbit η`, with terms `Aⁿ P (ξ - η)` of norm
  `≤ C λⁿ ‖P ξ - P η‖ ≤ C ‖P ξ - P η‖` (`norm_pow_apply_proj_le`,
  `BoundedContinuousFunction.dist_le`); so the fixed points are `2 C ‖P ξ - P η‖` apart.
* `norm_orbitSeq_apply_le`: the set `K = {x | ∀ n, ‖x n‖ ≤ M θⁿ}`, `M = 2 C ‖P ξ‖`, is closed
  (`isClosed_iInter`, `isClosed_le`, `BoundedContinuousFunction.lipschitz_eval_const`), and
  `perronMap ξ` maps it into itself: `‖Aⁿ P ξ‖ ≤ C θⁿ ‖P ξ‖` (`norm_pow_apply_proj_le`, `λ ≤ θ`),
  `‖φ (x n)‖ ≤ L M θⁿ` (`LipschitzWith.norm_le_mul`, `φ 0 = 0`), and
  `norm_perronOp_apply_le_of_le` bounds the Lyapunov–Perron term by `S.bound L M θⁿ ≤ M θⁿ / 2`.
  The iterates of `perronMap ξ` from `0` stay in `K` and tend to the fixed point
  (`ContractingWith.tendsto_iterate_fixedPoint`, `IsClosed.mem_of_tendsto`).
* `graph_proj`, `proj_graph`, `graph_zero`, `orbitSeq_apply_zero`: `orbitSeq_proj`,
  `P (1 - P) = 0` (`proj_mul_one_sub_proj`), `orbitSeq_zero`, `proj_orbitSeq_apply_zero`.
* `lipschitzWith_graph`: `‖1 - P‖ ≤ C`, `‖x 0‖ ≤ ‖x‖` (`dist_coe_le_dist`), `dist_orbitSeq_le` and
  `‖P‖ ≤ C` (`norm_one_sub_proj_le`, `norm_proj_le`) give the constant `2 C³`.
* `orbitSeq_apply_eq_iterate`: `orbitSeq x 0 = P x + graph x = x` (`orbitSeq_apply_zero`), then
  induction on `n` with `orbitSeq_succ` (`Function.iterate_succ_apply'`).
* `bddOrbit_iff`: a bounded forward orbit is a bounded sequence `z`
  (`BoundedContinuousFunction.ofNormedAddCommGroupDiscrete`) with `z (n + 1) = F (z n)`, so
  `z = orbitSeq x` (`eq_orbitSeq_of_forall_succ`) and `(1 - P) x = graph x` by definition of
  `graph`; conversely the orbit is `orbitSeq x` (`orbitSeq_apply_eq_iterate`), bounded by its
  norm (`BoundedContinuousFunction.norm_coe_le_norm`).
* `norm_iterate_le`, `tendsto_iterate`: `orbitSeq_apply_eq_iterate` and `norm_orbitSeq_apply_le`,
  then `tendsto_pow_atTop_nhds_zero_of_lt_one` and `squeeze_zero_norm`.
* `hasFDerivAt_graph_zero`: the fixed point equation at time `0` and `orbitSeq_apply_zero` give
  `graph ξ = perronOp (φ ∘ orbitSeq ξ) 0`, and `dist_orbitSeq_le` with `η = 0` gives
  `‖orbitSeq ξ‖ ≤ 2 C² ‖ξ‖`. Given `c > 0`, let `c' = c / (2 C² S.bound)`: `‖φ y‖ ≤ c' ‖y‖` for
  `‖y‖ < δ` (`HasFDerivAt` at `0`, `φ 0 = 0`). For `‖ξ‖ < δ / (2 C²)` every term of
  `orbitSeq ξ` has norm `< δ`, so `‖φ ∘ orbitSeq ξ‖ ≤ 2 C² c' ‖ξ‖` and
  `‖graph ξ‖ ≤ S.bound · 2 C² c' ‖ξ‖ = c ‖ξ‖` (`norm_perronOp_le`): this is
  `HasFDerivAt graph 0 0` (`hasFDerivAt_iff_isLittleO_nhds_zero`, `IsLittleO.of_bound`).
-/

@[expose] public section

open Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace StableManifold

open BoundedContinuousFunction ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E →L[ℝ] E}

/-- A **globally small Lipschitz perturbation** `x ↦ A x + φ x` of a linear map `A` with a
hyperbolic splitting `S`: `φ 0 = 0` and `φ` is `L`-Lipschitz with `L * S.bound ≤ 1 / 2`. -/
structure Perturbation (S : A.HyperbolicSplitting) where
  /-- The nonlinear part. -/
  φ : E → E
  /-- The Lipschitz constant `L` of the nonlinear part. -/
  lip : ℝ≥0
  lipschitzWith : LipschitzWith lip φ
  map_zero : φ 0 = 0
  lip_mul_bound_le : (lip : ℝ) * S.bound ≤ 1 / 2

namespace Perturbation

variable {S : A.HyperbolicSplitting} (F : Perturbation S)

/-- The perturbed map `x ↦ A x + φ x`. -/
def map (x : E) : E := A x + F.φ x

theorem map_apply (x : E) : F.map x = A x + F.φ x :=
  rfl

theorem map_zero' : F.map 0 = 0 := by
  simp [map, F.map_zero]

variable [CompleteSpace E]

/-- The **Lyapunov–Perron map** `x ↦ stableOrbit ξ + perronOp (φ ∘ x)` on bounded sequences: its
fixed points are the bounded `F`-orbits with stable component `P ξ` at time `0`. -/
noncomputable def perronMap (ξ : E) (x : ℕ →ᵇ E) : ℕ →ᵇ E :=
  S.stableOrbit ξ + S.perronOp (superpose F.φ x)

theorem perronMap_apply (ξ : E) (x : ℕ →ᵇ E) :
    F.perronMap ξ x = S.stableOrbit ξ + S.perronOp (superpose F.φ x) :=
  rfl

/-- The nonlinear term of the Lyapunov–Perron map has Lipschitz constant at most `1/2`. -/
theorem lipschitzWith_perronNonlinear :
    LipschitzWith (1 / 2) (S.perronOp ∘ superpose F.φ) := by
  refine (S.perronOp.lipschitzWith.comp (lipschitzWith_superpose F.lipschitzWith)).weaken ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm]
  calc ‖S.perronOp‖ * F.lip ≤ S.bound * F.lip := by gcongr; exact S.norm_perronOp_le
    _ = F.lip * S.bound := mul_comm _ _
    _ ≤ 1 / 2 := F.lip_mul_bound_le
    _ = ((1 / 2 : ℝ≥0) : ℝ) := by norm_num

/-- The Lyapunov–Perron map is a `1/2`-contraction. -/
theorem contractingWith_perronMap (ξ : E) : ContractingWith (1 / 2) (F.perronMap ξ) := by
  refine ⟨by norm_num, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [perronMap, Function.comp_apply, dist_eq_norm, add_sub_add_left_eq_sub] using
    F.lipschitzWith_perronNonlinear.norm_sub_le x y

/-- The **bounded orbit** through `ξ`: the fixed point of `perronMap ξ`, the unique bounded
`F`-orbit with stable component `P ξ` at time `0`. -/
noncomputable def orbitSeq (ξ : E) : ℕ →ᵇ E :=
  ContractingWith.fixedPoint (F.perronMap ξ) (F.contractingWith_perronMap ξ)

theorem perronMap_orbitSeq (ξ : E) : F.perronMap ξ (F.orbitSeq ξ) = F.orbitSeq ξ :=
  ContractingWith.fixedPoint_isFixedPt (F.contractingWith_perronMap ξ)

theorem eq_orbitSeq_of_perronMap_eq {ξ : E} {x : ℕ →ᵇ E} (hx : F.perronMap ξ x = x) :
    x = F.orbitSeq ξ :=
  ContractingWith.fixedPoint_unique (F.contractingWith_perronMap ξ) hx

/-- `orbitSeq ξ` is an `F`-orbit. -/
theorem orbitSeq_succ (ξ : E) (n : ℕ) : F.orbitSeq ξ (n + 1) = F.map (F.orbitSeq ξ n) := by
  have h : S.stableOrbit ξ + S.perronOp (superpose F.φ (F.orbitSeq ξ)) = F.orbitSeq ξ :=
    F.perronMap_orbitSeq ξ
  have := S.stableOrbit_add_perronOp_succ ξ (superpose F.φ (F.orbitSeq ξ)) n
  rwa [h, superpose_apply_of_lipschitzWith F.lipschitzWith] at this

/-- `orbitSeq ξ` has stable component `P ξ` at time `0`. -/
theorem proj_orbitSeq_apply_zero (ξ : E) : S.proj (F.orbitSeq ξ 0) = S.proj ξ := by
  have h : S.stableOrbit ξ + S.perronOp (superpose F.φ (F.orbitSeq ξ)) = F.orbitSeq ξ :=
    F.perronMap_orbitSeq ξ
  have := S.proj_stableOrbit_add_perronOp_zero ξ (superpose F.φ (F.orbitSeq ξ))
  rwa [h] at this

/-- **Uniqueness**: a bounded `F`-orbit `x` is `orbitSeq (x 0)`.

Proof: by `eq_stableOrbit_add_perronOp`, `x` is a fixed point of `perronMap (x 0)`. -/
theorem eq_orbitSeq_of_forall_succ {x : ℕ →ᵇ E} (hx : ∀ n, x (n + 1) = F.map (x n)) :
    x = F.orbitSeq (x 0) := by
  refine F.eq_orbitSeq_of_perronMap_eq ?_
  rw [perronMap_apply]
  exact (S.eq_stableOrbit_add_perronOp (y := superpose F.φ x) fun n ↦ by
    rw [hx, F.map_apply, superpose_apply_of_lipschitzWith F.lipschitzWith]).symm

theorem orbitSeq_proj (ξ : E) : F.orbitSeq (S.proj ξ) = F.orbitSeq ξ := by
  refine F.eq_orbitSeq_of_perronMap_eq ?_
  rw [perronMap_apply, ← S.stableOrbit_proj ξ]
  exact F.perronMap_orbitSeq _

theorem orbitSeq_zero : F.orbitSeq 0 = 0 := by
  refine (F.eq_orbitSeq_of_perronMap_eq ?_).symm
  simp [perronMap_apply, superpose_zero F.map_zero]

/-- `orbitSeq` is Lipschitz in the stable component.

Proof: `ContractingWith.fixedPoint_lipschitz_in_map`, the two Lyapunov–Perron maps differing by
`stableOrbit (ξ - η)`, of norm `≤ C ‖P ξ - P η‖`. -/
theorem dist_orbitSeq_le (ξ η : E) :
    dist (F.orbitSeq ξ) (F.orbitSeq η) ≤ 2 * S.const * ‖S.proj ξ - S.proj η‖ := by
  have hC : 0 ≤ S.const * ‖S.proj ξ - S.proj η‖ := by positivity [S.const_pos]
  have h := (F.contractingWith_perronMap ξ).fixedPoint_lipschitz_in_map
    (F.contractingWith_perronMap η) (C := S.const * ‖S.proj ξ - S.proj η‖) fun z ↦ by
      rw [perronMap_apply, perronMap_apply, dist_add_right, dist_le hC]
      intro n
      rw [dist_eq_norm, S.stableOrbit_apply, S.stableOrbit_apply, ← map_sub, ← map_sub]
      refine (S.norm_pow_apply_proj_le n (ξ - η)).trans ?_
      rw [map_sub]
      exact mul_le_mul_of_nonneg_right
        (S.const_mul_rate_pow_le n) (norm_nonneg _)
  refine h.trans (le_of_eq ?_)
  norm_num
  ring

/-- **Geometric decay** of the bounded orbits: `‖orbitSeq ξ n‖ ≤ 2 C θⁿ ‖P ξ‖`,
`θ = S.decayRate`.

Proof: `perronMap ξ` maps the closed set `{x | ∀ n, ‖x n‖ ≤ 2 C ‖P ξ‖ θⁿ}` into itself
(`norm_perronOp_apply_le_of_le`), so its fixed point lies there. -/
theorem norm_orbitSeq_apply_le (ξ : E) (n : ℕ) :
    ‖F.orbitSeq ξ n‖ ≤ 2 * S.const * S.decayRate ^ n * ‖S.proj ξ‖ := by
  have hC := S.const_pos
  have hθ := S.decayRate_pos
  have hM0 : 0 ≤ 2 * S.const * ‖S.proj ξ‖ := by positivity
  set M := 2 * S.const * ‖S.proj ξ‖ with hM
  set K : Set (ℕ →ᵇ E) := {x | ∀ n, ‖x n‖ ≤ M * S.decayRate ^ n} with hK
  have hKc : IsClosed K := by
    simp only [hK, Set.ofPred_forall]
    exact isClosed_iInter fun n ↦ isClosed_le
      (continuous_norm.comp (lipschitz_eval_const n).continuous) continuous_const
  have hKmap : ∀ x ∈ K, F.perronMap ξ x ∈ K := by
    intro x hx n
    have hy : ∀ n, ‖superpose F.φ x n‖ ≤ (F.lip * M) * S.decayRate ^ n := fun n ↦ by
      rw [superpose_apply_of_lipschitzWith F.lipschitzWith]
      calc ‖F.φ (x n)‖ ≤ F.lip * ‖x n‖ := F.lipschitzWith.norm_le_mul F.map_zero (x n)
        _ ≤ F.lip * (M * S.decayRate ^ n) := by gcongr; exact hx n
        _ = _ := by ring
    have h1 : ‖S.perronOp (superpose F.φ x) n‖ ≤ M / 2 * S.decayRate ^ n := by
      refine (S.norm_perronOp_apply_le_of_le hy n).trans ?_
      have : S.bound * (F.lip * M) ≤ M / 2 := by
        calc S.bound * (F.lip * M) = (F.lip * S.bound) * M := by ring
          _ ≤ 1 / 2 * M := by gcongr; exact F.lip_mul_bound_le
          _ = M / 2 := by ring
      gcongr
    have h2 : ‖(A ^ n) (S.proj ξ)‖ ≤ S.const * S.decayRate ^ n * ‖S.proj ξ‖ := by
      refine (S.norm_pow_apply_proj_le n ξ).trans ?_
      gcongr
      exacts [S.rate_pos.le, S.rate_lt_decayRate.le]
    rw [perronMap_apply, BoundedContinuousFunction.add_apply, S.stableOrbit_apply]
    refine (norm_add_le _ _).trans ((add_le_add h2 h1).trans (le_of_eq ?_))
    rw [hM]
    ring
  have hiter : ∀ k, (F.perronMap ξ)^[k] 0 ∈ K := by
    intro k
    induction k with
    | zero =>
      intro n
      change ‖(0 : E)‖ ≤ M * S.decayRate ^ n
      simpa only [norm_zero] using mul_nonneg hM0 (pow_nonneg hθ.le n)
    | succ k ih => rw [Function.iterate_succ_apply']; exact hKmap _ ih
  have hmem : F.orbitSeq ξ ∈ K :=
    hKc.mem_of_tendsto ((F.contractingWith_perronMap ξ).tendsto_iterate_fixedPoint 0)
      (Eventually.of_forall hiter)
  refine (hmem n).trans (le_of_eq ?_)
  rw [hM]
  ring

/-- The map whose graph over the stable subspace is the **global stable manifold**:
`graph ξ = (1 - P) (orbitSeq ξ 0)`, the unstable component at time `0` of the bounded orbit with
stable component `P ξ`. -/
noncomputable def graph (ξ : E) : E :=
  (1 - S.proj) (F.orbitSeq ξ 0)

theorem graph_proj (ξ : E) : F.graph (S.proj ξ) = F.graph ξ := by
  unfold graph
  rw [F.orbitSeq_proj]

theorem proj_graph (ξ : E) : S.proj (F.graph ξ) = 0 := by
  rw [graph, ← mul_apply_eq_comp, S.proj_mul_one_sub_proj, zero_apply]

theorem graph_zero : F.graph 0 = 0 := by
  rw [graph, orbitSeq_zero]
  exact (1 - S.proj : E →L[ℝ] E).map_zero

/-- The bounded orbit through `ξ` starts at `P ξ + graph ξ`. -/
theorem orbitSeq_apply_zero (ξ : E) : F.orbitSeq ξ 0 = S.proj ξ + F.graph ξ := by
  rw [graph, _root_.sub_apply, one_apply_eq_self, F.proj_orbitSeq_apply_zero]
  abel

/-- The bounded orbit sequence varies Lipschitz-continuously with the initial point. -/
theorem dist_orbitSeq_le_norm (ξ η : E) :
    dist (F.orbitSeq ξ) (F.orbitSeq η) ≤ 2 * S.const ^ 2 * ‖ξ - η‖ := by
  calc dist (F.orbitSeq ξ) (F.orbitSeq η) ≤ 2 * S.const * ‖S.proj ξ - S.proj η‖ :=
      F.dist_orbitSeq_le ξ η
    _ ≤ 2 * S.const * (S.const * ‖ξ - η‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity [S.const_pos])
      rw [← map_sub]
      exact S.proj.le_of_opNorm_le S.norm_proj_le _
    _ = 2 * S.const ^ 2 * ‖ξ - η‖ := by ring

/-- `graph` is Lipschitz, with constant `2 C³`. -/
theorem lipschitzWith_graph : LipschitzWith (2 * S.const ^ 3).toNNReal F.graph := by
  have hC := S.const_pos
  refine LipschitzWith.of_dist_le_mul fun ξ η ↦ ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm, graph, graph, ← map_sub]
  calc ‖(1 - S.proj) (F.orbitSeq ξ 0 - F.orbitSeq η 0)‖
      ≤ S.const * ‖F.orbitSeq ξ 0 - F.orbitSeq η 0‖ :=
        (1 - S.proj).le_of_opNorm_le S.norm_one_sub_proj_le _
    _ ≤ S.const * dist (F.orbitSeq ξ) (F.orbitSeq η) := by
        gcongr
        rw [← dist_eq_norm]
        exact dist_coe_le_dist 0
    _ ≤ S.const * (2 * S.const ^ 2 * ‖ξ - η‖) :=
      mul_le_mul_of_nonneg_left (F.dist_orbitSeq_le_norm ξ η) hC.le
    _ = 2 * S.const ^ 3 * ‖ξ - η‖ := by ring

/-- On the graph, the bounded orbit is the forward `F`-orbit. -/
theorem orbitSeq_apply_eq_iterate {x : E} (hx : (1 - S.proj) x = F.graph x) (n : ℕ) :
    F.orbitSeq x n = F.map^[n] x := by
  refine StableManifold.orbit_eq_iterate ?_ (F.orbitSeq_succ x) n
  rw [F.orbitSeq_apply_zero, ← hx, _root_.sub_apply, one_apply_eq_self]
  abel

/-- **The global stable manifold**: the forward `F`-orbit of `x` is bounded if and only if
`(1 - P) x = graph x`, that is `x = P x + graph (P x)`.

Proof: a bounded orbit is `orbitSeq x` (`eq_orbitSeq_of_forall_succ`), whose unstable component at
`0` is `graph x`; conversely `orbitSeq_apply_eq_iterate`. -/
theorem bddOrbit_iff (x : E) :
    (∃ M, ∀ n, ‖F.map^[n] x‖ ≤ M) ↔ (1 - S.proj) x = F.graph x := by
  constructor
  · rintro ⟨M, hM⟩
    set z : ℕ →ᵇ E := ofNormedAddCommGroupDiscrete (fun n ↦ F.map^[n] x) M hM
    have hz0 : z 0 = x := rfl
    have hz : z = F.orbitSeq (z 0) :=
      F.eq_orbitSeq_of_forall_succ fun n ↦ Function.iterate_succ_apply' F.map n x
    rw [hz0] at hz
    rw [graph, ← hz, hz0]
  · intro hx
    exact ⟨‖F.orbitSeq x‖, fun n ↦ F.orbitSeq_apply_eq_iterate hx n ▸ norm_coe_le_norm _ n⟩

/-- On the graph, the forward orbits decay geometrically: `‖Fⁿ x‖ ≤ 2 C θⁿ ‖P x‖`. -/
theorem norm_iterate_le {x : E} (hx : (1 - S.proj) x = F.graph x) (n : ℕ) :
    ‖F.map^[n] x‖ ≤ 2 * S.const * S.decayRate ^ n * ‖S.proj x‖ := by
  rw [← F.orbitSeq_apply_eq_iterate hx]
  exact F.norm_orbitSeq_apply_le x n

/-- On the graph, the forward orbits tend to `0`. -/
theorem tendsto_iterate {x : E} (hx : (1 - S.proj) x = F.graph x) :
    Tendsto (fun n ↦ F.map^[n] x) atTop (𝓝 0) := by
  refine squeeze_zero_norm (F.norm_iterate_le hx) ?_
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one S.decayRate_pos.le
    S.decayRate_lt_one).const_mul (2 * S.const)).mul_const ‖S.proj x‖

/-- **Tangency**: if `φ` has derivative `0` at `0`, so has `graph`; the stable manifold is tangent
to the stable subspace at `0`.

Proof: `graph ξ = perronOp (φ ∘ orbitSeq ξ) 0`, with `‖orbitSeq ξ‖ ≤ 2 C² ‖ξ‖` and
`‖φ y‖ ≤ ε ‖y‖` near `0`, so `‖graph ξ‖ ≤ S.bound * 2 C² ε ‖ξ‖` near `0`. -/
theorem hasFDerivAt_graph_zero (hφ : HasFDerivAt F.φ (0 : E →L[ℝ] E) 0) :
    HasFDerivAt F.graph (0 : E →L[ℝ] E) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hφ ⊢
  simp only [zero_add, F.map_zero, F.graph_zero, sub_zero, zero_apply] at hφ ⊢
  refine Asymptotics.IsLittleO.of_bound fun c hc ↦ ?_
  have hC := S.const_pos
  have hb := S.bound_pos
  have hK : 0 < S.bound * (2 * S.const ^ 2) := by positivity
  obtain ⟨δ, hδ, hφδ⟩ := Metric.eventually_nhds_iff.1 (hφ.def (div_pos hc hK))
  have hr : 0 < δ / (2 * S.const ^ 2) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with ξ hξ
  rw [mem_ball_zero_iff] at hξ
  have ho : ‖F.orbitSeq ξ‖ ≤ 2 * S.const ^ 2 * ‖ξ‖ := by
    simpa only [F.orbitSeq_zero, dist_zero_right, sub_zero] using F.dist_orbitSeq_le_norm ξ 0
  have hy : ‖superpose F.φ (F.orbitSeq ξ)‖ ≤
      c / (S.bound * (2 * S.const ^ 2)) * (2 * S.const ^ 2 * ‖ξ‖) := by
    refine (norm_le (by positivity)).2 fun n ↦ ?_
    rw [superpose_apply_of_lipschitzWith F.lipschitzWith]
    have hn : ‖F.orbitSeq ξ n‖ ≤ 2 * S.const ^ 2 * ‖ξ‖ := (norm_coe_le_norm _ n).trans ho
    have hlt : dist (F.orbitSeq ξ n) 0 < δ := by
      rw [dist_zero_right]
      calc _ ≤ 2 * S.const ^ 2 * ‖ξ‖ := hn
        _ < 2 * S.const ^ 2 * (δ / (2 * S.const ^ 2)) := by gcongr
        _ = δ := by field_simp
    exact (hφδ hlt).trans (by gcongr)
  have hg : F.graph ξ = S.perronOp (superpose F.φ (F.orbitSeq ξ)) 0 := by
    have h1 : F.orbitSeq ξ 0 = S.proj ξ + S.perronOp (superpose F.φ (F.orbitSeq ξ)) 0 := by
      conv_lhs => rw [← F.perronMap_orbitSeq ξ]
      rw [perronMap_apply, BoundedContinuousFunction.add_apply, S.stableOrbit_apply,
        pow_zero, one_apply_eq_self]
    rw [F.orbitSeq_apply_zero] at h1
    exact add_left_cancel h1
  rw [hg]
  calc ‖S.perronOp (superpose F.φ (F.orbitSeq ξ)) 0‖
      ≤ ‖S.perronOp (superpose F.φ (F.orbitSeq ξ))‖ := norm_coe_le_norm _ 0
    _ ≤ S.bound * ‖superpose F.φ (F.orbitSeq ξ)‖ :=
        S.perronOp.le_of_opNorm_le S.norm_perronOp_le _
    _ ≤ S.bound * (c / (S.bound * (2 * S.const ^ 2)) * (2 * S.const ^ 2 * ‖ξ‖)) := by gcongr
    _ = c * ‖ξ‖ := by field_simp

end Perturbation

end StableManifold
