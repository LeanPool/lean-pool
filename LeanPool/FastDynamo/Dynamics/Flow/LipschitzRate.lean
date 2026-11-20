/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Flow.TorusFlow
public import LeanPool.FastDynamo.Analysis.LogLinearGrowth

/-!
# The optimal Lipschitz constant of the flow, and its vanishing exponential rate

`prop:particle-flow` states, after the linear bound `eq:linear-flow-lipschitz`, the limit

```
  lim_{|t| → ∞} |t|⁻¹ log Lip(Φ_t) = 0
```

(the unlabelled display following "In particular" in its statement).

This is the one clause of the proposition that speaks about the *optimal* Lipschitz constant
`Lip(F)` rather than about an admissible one: an upper bound alone cannot give a limit, a lower
bound on the optimal constant is needed as well.  Mathlib has no optimal-constant notion —
`LipschitzWith` takes an admissible constant — so this module introduces one.

## Contents

* `lipschitzConstants F` — the set of admissible real Lipschitz constants of `F`, and
  `lipConst F = sInf (lipschitzConstants F)`, the paper's `Lip(F)` ("the optimal Lipschitz
  constant", §1.2).  Nothing here claims
  that the infimum is attained: the limit needs only that `lipConst` is squeezed between an
  admissible constant from above (`csInf_le`) and a bound valid for *every* admissible
  constant from below (`le_csInf`), which is exactly what the two inequalities supply.
* `inv_le_lipConst_of_leftInverse` — the lower bound: if `G ∘ F = id` and `G` is `L`-Lipschitz
  then every admissible constant of `F` is at least `1/L`, so `Lip(F) ≥ 1/L`.  It is used with
  `G = Φ_{-t} = Φ_t^{-1}`, whose Lipschitz constant `eq:linear-flow-lipschitz` also bounds; the
  paper passes from `eq:linear-flow-lipschitz` to the limit with the words "In particular" and
  leaves this lower bound implicit.  No measure-theoretic input and no volume-distortion estimate
  is needed.
* `lipConst_literalFlow_le`, `inv_flowLipschitzBound_le_lipConst_literalFlow` — the two
  inequalities at the flow, at the constant `flowLipschitzBound … t = 2(1 + |t| · slope)` of
  `FastDynamo/Dynamics/Flow/PlaneFlowLipschitz.lean`.
* `tendsto_abs_inv_mul_log_lipConst_literalFlow` — the clause itself, with `|t| → ∞` read as
  the cocompact filter of `ℝ` (`Filter.cocompact ℝ = atBot ⊔ atTop`).

The squeeze is the same one that gives the vanishing ideal operator rate
(`FastDynamo/Analysis/LogLinearGrowth.lean`), read on the two-sided filter.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter

/-! ## The optimal Lipschitz constant -/

/-- **The admissible Lipschitz constants of `F`**: the non-negative reals `K` with
`dist (F x) (F y) ≤ K · dist x y` for all `x`, `y`.  The set is upward closed and bounded
below by `0`. -/
def lipschitzConstants {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : X → Y) : Set ℝ :=
  {K : ℝ | 0 ≤ K ∧ ∀ x y : X, dist (F x) (F y) ≤ K * dist x y}

/-- **The paper's `Lip(F)`**: the least admissible Lipschitz constant of `F`, as an
infimum.  When `F` is not Lipschitz the set of admissible constants is empty and the value is
`0` by Mathlib's convention `sInf ∅ = 0`; every statement below supplies an admissible constant
explicitly, so that convention is never used. -/
def lipConst {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (F : X → Y) : ℝ :=
  sInf (lipschitzConstants F)

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- The set of admissible constants is bounded below by `0`. -/
theorem bddBelow_lipschitzConstants (F : X → Y) : BddBelow (lipschitzConstants F) :=
  ⟨0, fun _ hK ↦ hK.1⟩

/-- **`Lip(F) ≤ C` for every admissible `C`**, the upper half of the squeeze. -/
theorem lipConst_le_of_dist_le {F : X → Y} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : X, dist (F x) (F y) ≤ C * dist x y) : lipConst F ≤ C :=
  csInf_le (bddBelow_lipschitzConstants F) ⟨hC, hF⟩

/-- **`Lip(F) ≥ 1/L` when `F` has an `L`-Lipschitz left inverse**, the lower half of the
squeeze, provided the space has two distinct points and `F` is Lipschitz at all.

For any admissible `K` and any `x ≠ y`,
`dist x y = dist (G (F x)) (G (F y)) ≤ L · dist (F x) (F y) ≤ L K · dist x y`, and dividing by
the positive number `dist x y` gives `1 ≤ L K`.  This is why the Lipschitz constants cannot
decay: `eq:linear-flow-lipschitz` bounds `Lip(Φ_t^{-1})` as well, and `Φ_t^{-1} = Φ_{-t}` (proof
of `prop:particle-flow`). -/
theorem inv_le_lipConst_of_leftInverse {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {F : X → Y} {G : Y → X} {C L : ℝ} {x₀ y₀ : X} (hxy : x₀ ≠ y₀) (hL : 0 < L) (hC : 0 ≤ C)
    (hFC : ∀ x y : X, dist (F x) (F y) ≤ C * dist x y)
    (hGL : ∀ y y' : Y, dist (G y) (G y') ≤ L * dist y y')
    (hGF : ∀ x : X, G (F x) = x) :
    1 / L ≤ lipConst F := by
  refine le_csInf ⟨C, hC, hFC⟩ ?_
  rintro K ⟨hK0, hK⟩
  have hd : 0 < dist x₀ y₀ := dist_pos.2 hxy
  have hchain : dist x₀ y₀ ≤ L * K * dist x₀ y₀ := by
    calc dist x₀ y₀ = dist (G (F x₀)) (G (F y₀)) := by rw [hGF, hGF]
      _ ≤ L * dist (F x₀) (F y₀) := hGL _ _
      _ ≤ L * (K * dist x₀ y₀) := mul_le_mul_of_nonneg_left (hK x₀ y₀) hL.le
      _ = L * K * dist x₀ y₀ := by ring
  have hone : 1 ≤ L * K := by nlinarith
  rw [div_le_iff₀ hL]
  nlinarith

/-! ## The two-sided logarithmic squeeze -/

/-- **The squeeze on the cocompact filter.**  A positive quantity trapped between
`1 / (C(1 + |t|))` and `C(1 + |t|)` has vanishing exponential growth rate as `|t| → ∞`.

It is `tendsto_inv_mul_log_linear_atTop` (`FastDynamo/Analysis/LogLinearGrowth.lean`)
precomposed with `t ↦ |t|`, which tends to `atTop` along `Filter.cocompact ℝ`. -/
theorem tendsto_abs_inv_mul_log_of_two_sided {f : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hlow : ∀ t : ℝ, 1 / (C * (1 + |t|)) ≤ f t)
    (hup : ∀ t : ℝ, f t ≤ C * (1 + |t|)) :
    Tendsto (fun t : ℝ ↦ |t|⁻¹ * Real.log (f t)) (cocompact ℝ) (nhds (0 : ℝ)) := by
  have habs : Tendsto (fun t : ℝ ↦ |t|) (cocompact ℝ) atTop := by
    have h := tendsto_norm_cocompact_atTop (E := ℝ)
    exact h.congr fun t ↦ Real.norm_eq_abs t
  have hmaj : Tendsto (fun t : ℝ ↦ |t|⁻¹ * Real.log (C * (1 + |t|)))
      (cocompact ℝ) (nhds (0 : ℝ)) := (tendsto_inv_mul_log_linear_atTop hC).comp habs
  refine squeeze_zero_norm ?_ hmaj
  intro t
  have hden : (0 : ℝ) < C * (1 + |t|) := by positivity
  have hl := hlow t
  have hu := hup t
  have hpos : (0 : ℝ) < f t := lt_of_lt_of_le (by positivity) hl
  have hlog1 : Real.log (f t) ≤ Real.log (C * (1 + |t|)) := Real.log_le_log hpos hu
  have hlog2 : -Real.log (C * (1 + |t|)) ≤ Real.log (f t) := by
    have h := Real.log_le_log (by positivity) hl
    rwa [Real.log_div one_ne_zero hden.ne', Real.log_one, zero_sub] at h
  calc ‖|t|⁻¹ * Real.log (f t)‖ = |t|⁻¹ * |Real.log (f t)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.2 (abs_nonneg t))]
    _ ≤ |t|⁻¹ * Real.log (C * (1 + |t|)) :=
        mul_le_mul_of_nonneg_left (abs_le.2 ⟨hlog2, hlog1⟩) (inv_nonneg.2 (abs_nonneg t))

/-! ## The literal three-torus has two distinct points -/

/-- Half is not an integer, so it is not zero in `ℝ/ℤ`. -/
theorem half_ne_zero_unitAddCircle : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  intro hx
  rw [AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨n, hn⟩ := hx
  have hr : (n : ℝ) = 1 / 2 := by simpa using hn
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- The literal three-torus has two distinct points, which is what makes the lower bound on
`Lip(Φ_t)` non-vacuous. -/
theorem exists_ne_torusThree : ∃ x y : Torus 3, x ≠ y := by
  refine ⟨0, fun _ ↦ ((1 / 2 : ℝ) : UnitAddCircle), fun hxy ↦ ?_⟩
  exact half_ne_zero_unitAddCircle (congrFun hxy 0).symm

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## `Lip(Φ_t)` is squeezed between two linear functions of `|t|` -/

/-- **`Lip(Φ_t) ≤ 2(1 + |t| · slope)`**, the optimal-constant reading of
`eq:linear-flow-lipschitz`: the bound `flowLipschitzBound … t` is admissible, so the infimum is
at most it. -/
theorem lipConst_literalFlow_le (htau : 0 ≤ tau) (t : ℝ) :
    lipConst (literalFlow h P angularSpeed axialSpeed tau t) ≤
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
  refine lipConst_le_of_dist_le
    (flowLipschitzBound_nonneg h P angularSpeed axialSpeed tau htau t) fun x y ↦ ?_
  have hlip := (lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau t).dist_le_mul x y
  rwa [coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau] at hlip

/-- **`Lip(Φ_t) ≥ 1 / (2(1 + |t| · slope))`**: the inverse map `Φ_{-t}` (`Φ_t^{-1} = Φ_{-t}`,
proof of `prop:particle-flow`) has the same bound, and `Φ_{-t} ∘ Φ_t = id`, so no admissible
constant of `Φ_t` can be smaller than the
reciprocal. -/
theorem inv_flowLipschitzBound_le_lipConst_literalFlow (htau : 0 ≤ tau) (t : ℝ) :
    1 / flowLipschitzBound h P angularSpeed axialSpeed tau t ≤
      lipConst (literalFlow h P angularSpeed axialSpeed tau t) := by
  obtain ⟨x₀, y₀, hxy⟩ := exists_ne_torusThree
  have hpos : (0 : ℝ) < flowLipschitzBound h P angularSpeed axialSpeed tau t :=
    lt_of_lt_of_le zero_lt_one (one_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t)
  have hposneg : (0 : ℝ) < flowLipschitzBound h P angularSpeed axialSpeed tau (-t) :=
    lt_of_lt_of_le zero_lt_one
      (one_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau (-t))
  have hFC : ∀ x y : Torus 3,
      dist (literalFlow h P angularSpeed axialSpeed tau t x)
          (literalFlow h P angularSpeed axialSpeed tau t y) ≤
        flowLipschitzBound h P angularSpeed axialSpeed tau t * dist x y := by
    intro x y
    have hlip :=
      (lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau t).dist_le_mul x y
    rwa [coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau] at hlip
  have hGL : ∀ x y : Torus 3,
      dist (literalFlow h P angularSpeed axialSpeed tau (-t) x)
          (literalFlow h P angularSpeed axialSpeed tau (-t) y) ≤
        flowLipschitzBound h P angularSpeed axialSpeed tau (-t) * dist x y := by
    intro x y
    have hlip :=
      (lipschitzWith_literalFlow h P angularSpeed axialSpeed tau htau (-t)).dist_le_mul x y
    rwa [coe_flowLipschitzBoundNN h P angularSpeed axialSpeed tau htau] at hlip
  have hbound := inv_le_lipConst_of_leftInverse (X := Torus 3) (Y := Torus 3)
    (x₀ := x₀) (y₀ := y₀) hxy hposneg hpos.le hFC hGL
    (literalFlow_neg_literalFlow h P angularSpeed axialSpeed tau t)
  have hneg : flowLipschitzBound h P angularSpeed axialSpeed tau (-t) =
      flowLipschitzBound h P angularSpeed axialSpeed tau t := by
    rw [flowLipschitzBound, flowLipschitzBound, abs_neg]
  rwa [hneg] at hbound

/-- The time-`t` bound is dominated by `C_L (1 + |t|)`: its sum with the bound at `-t` already
is (`flowLipschitzBound_add_neg_le`), and the other summand is positive. -/
theorem flowLipschitzBound_le_flowCL_mul (htau : 0 ≤ tau) (t : ℝ) :
    flowLipschitzBound h P angularSpeed axialSpeed tau t ≤
      flowCL h P angularSpeed axialSpeed tau * (1 + |t|) := by
  have hsum := flowLipschitzBound_add_neg_le h P angularSpeed axialSpeed tau htau t
  have hneg := two_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau (-t)
  linarith

/-- **`lim_{|t| → ∞} |t|⁻¹ log Lip(Φ_t) = 0`** (statement of `prop:particle-flow`), with
`|t| → ∞` read as the cocompact filter of `ℝ`.

`Lip(Φ_t)` is trapped between `1 / (C_L(1 + |t|))` and `C_L(1 + |t|)` by the two inequalities
above, and between two logarithms of linear functions the rate is squeezed to zero. -/
theorem tendsto_abs_inv_mul_log_lipConst_literalFlow (htau : 0 ≤ tau) :
    Tendsto
      (fun t : ℝ ↦
        |t|⁻¹ * Real.log (lipConst (literalFlow h P angularSpeed axialSpeed tau t)))
      (cocompact ℝ) (nhds (0 : ℝ)) := by
  refine tendsto_abs_inv_mul_log_of_two_sided
    (flowCL_pos h P angularSpeed axialSpeed tau htau) (fun t ↦ ?_) fun t ↦ ?_
  · refine le_trans ?_ (inv_flowLipschitzBound_le_lipConst_literalFlow h P angularSpeed
      axialSpeed tau htau t)
    have hpos : (0 : ℝ) < flowLipschitzBound h P angularSpeed axialSpeed tau t :=
      lt_of_lt_of_le zero_lt_one
        (one_le_flowLipschitzBound h P angularSpeed axialSpeed tau htau t)
    exact one_div_le_one_div_of_le hpos
      (flowLipschitzBound_le_flowCL_mul h P angularSpeed axialSpeed tau htau t)
  · exact le_trans (lipConst_literalFlow_le h P angularSpeed axialSpeed tau htau t)
      (flowLipschitzBound_le_flowCL_mul h P angularSpeed axialSpeed tau htau t)

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
