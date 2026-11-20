/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TorusNet
public import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy

/-!
# Zero topological entropy from linearly growing Lipschitz constants

`prop:particle-flow` of the paper asserts that the particle flow of the
fast-dynamo velocity has vanishing topological entropy (last clause of the statement; the
argument is the last paragraph of its proof).

The paper **fixes no definition of `h_top`**: it refers to
[HasselblattKatok02, Section 2.5e] (§1.2), and its proof runs entirely on
abstract properties of that quantity — the power rule and the Lipschitz bound of
[HasselblattKatok02, Section 2.5f(3) and Proposition 2.5.5]:

```
  m h_top(Φ_s) = h_top(Φ_{m s}) ≤ 3 log (C_L (1 + m |s|))     (proof of `prop:particle-flow`)
```

so that `h_top(Φ_s) = 0` on dividing by `m` and letting `m → ∞`.

This module instead fixes the quantity concretely and runs the classical Bowen–Dinaburg
argument through a packing bound `s_m(F, ρ) ≤ C_ρ (1 + m)³`, in the *cover* form that
Mathlib's `Dynamics.coverEntropy` expresses; it is therefore a route of the formalisation,
quantitative where the paper is abstract, and it gives the same conclusion.  A separated-set
quantity and Mathlib's `Dynamics.coverEntropy` agree on a compact metric space (Mathlib's
`Dynamics.coverEntropy_eq_iSup_netEntropyEntourage`), but that bridge lives in
`Mathlib/Dynamics/TopologicalEntropy/NetEntropy.lean`, is not needed by any clause of
`MainLagrangianClauses`, and is not used here: the packing bound bounds covers
directly, and the matching lower bound `0 ≤ coverEntropy` is Mathlib's.

## Main declarations

* `eventually_mul_add_one_pow_le_exp` — a polynomial in `n` is eventually dominated by `exp (r n)`;
* `expGrowthSup_le_zero_of_le_ofReal_pow` — hence a polynomially bounded sequence has vanishing
  `ExpGrowth.expGrowthSup`;
* `entropyNetSize`, `isDynCoverOf_torusGrid`, `coverMincard_le_ofReal_pow` — the grid of
  `FastDynamo/Analysis/TorusNet.lean` as a dynamical cover, with its cardinality bound;
* `coverEntropy_eq_zero_of_lipschitz_iterate` — the criterion itself.

The criterion is stated for an arbitrary self-map of `Torus 3` so that the flow modules can apply
it to `literalFlow t` for each fixed `t`; nothing about the particular velocity field enters.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter
open scoped ENNReal NNReal

/-! ## Polynomial growth has vanishing exponential growth rate -/

/-- A polynomial in `n` is eventually dominated by `exp (r * n)` for every positive rate `r`.
This is the analytic half of the entropy bound in the proof of `prop:particle-flow`. -/
theorem eventually_mul_add_one_pow_le_exp {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (A * ((n : ℝ) + 1)) ^ k ≤ Real.exp (r * n) := by
  have hlittle : (fun x : ℝ => x ^ k) =o[atTop] Real.exp := Real.isLittleO_pow_exp_atTop
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have htend : Tendsto (fun n : ℕ => r * ((n : ℝ) + 1)) atTop atTop := h0.const_mul_atTop hr
  have h2 := hlittle.comp_tendsto htend
  have hε : (0 : ℝ) < (r / A) ^ k * Real.exp (-r) := by positivity
  filter_upwards [h2.def hε] with n hn
  simp only [Function.comp_apply, Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r * ((n : ℝ) + 1)) ^ k),
    abs_of_nonneg (Real.exp_pos _).le] at hn
  have hkey : (A * ((n : ℝ) + 1)) ^ k = (A / r) ^ k * (r * ((n : ℝ) + 1)) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hexp : Real.exp (-r) * Real.exp (r * ((n : ℝ) + 1)) = Real.exp (r * n) := by
    rw [← Real.exp_add]
    ring_nf
  calc (A * ((n : ℝ) + 1)) ^ k = (A / r) ^ k * (r * ((n : ℝ) + 1)) ^ k := hkey
    _ ≤ (A / r) ^ k * ((r / A) ^ k * Real.exp (-r) * Real.exp (r * ((n : ℝ) + 1))) := by gcongr
    _ = Real.exp (r * n) := by
        rw [mul_assoc, hexp, ← mul_assoc, ← mul_pow]
        rw [show A / r * (r / A) = 1 by field_simp]
        simp

/-- A sequence of extended nonnegative reals bounded by a polynomial has vanishing upper
exponential growth rate.  This is the `ℝ≥0∞`/`EReal` form of "polynomial beats exponential"
needed to insert the packing bound into a separated-set or cover definition of `h_top`
(see the module docstring; the paper fixes no such definition). -/
theorem expGrowthSup_le_zero_of_le_ofReal_pow {u : ℕ → ℝ≥0∞} {A : ℝ} (hA : 0 < A) (k : ℕ)
    (hu : ∀ n : ℕ, u n ≤ ENNReal.ofReal ((A * ((n : ℝ) + 1)) ^ k)) :
    ExpGrowth.expGrowthSup u ≤ 0 := by
  rw [ExpGrowth.expGrowthSup_le_iff]
  intro b hb
  have hc0 : (0 : EReal) < min b 1 := lt_min hb (by norm_num)
  have hc1 : min b 1 ≤ (1 : EReal) := min_le_right _ _
  have hcb : min b 1 ≤ b := min_le_left _ _
  have h1top : (1 : EReal) ≠ ⊤ := EReal.coe_one ▸ EReal.coe_ne_top 1
  have hctop : min b 1 ≠ ⊤ := ne_top_of_le_ne_top h1top hc1
  have hcbot : min b 1 ≠ ⊥ := by
    intro hcontra
    rw [hcontra] at hc0
    simp at hc0
  have hr : (((min b 1).toReal : ℝ) : EReal) = min b 1 := EReal.coe_toReal hctop hcbot
  set r : ℝ := (min b 1).toReal with hrdef
  have hr0 : 0 < r := by
    have hlt := hc0
    rw [← hr] at hlt
    exact_mod_cast hlt
  filter_upwards [eventually_mul_add_one_pow_le_exp hA hr0 k] with n hn
  have hstep : ENNReal.ofReal (Real.exp (r * n)) = EReal.exp ((r : EReal) * (n : EReal)) := by
    rw [show ((r : EReal) * (n : EReal)) = (((r * (n : ℝ) : ℝ)) : EReal) by
      rw [EReal.coe_mul, EReal.coe_natCast]]
    rw [EReal.exp_coe]
  calc u n ≤ ENNReal.ofReal ((A * ((n : ℝ) + 1)) ^ k) := hu n
    _ ≤ ENNReal.ofReal (Real.exp (r * n)) := ENNReal.ofReal_le_ofReal hn
    _ = EReal.exp ((r : EReal) * (n : EReal)) := hstep
    _ ≤ EReal.exp (b * (n : EReal)) := by
        refine EReal.exp_monotone ?_
        rw [hr]
        exact mul_le_mul_of_nonneg_right hcb (by positivity)

/-! ## The grid as a dynamical cover -/

/-- The resolution of the grid used at time `m` for the entourage of radius `ρ`: `N` is chosen
so that `C (1 + m) / N < ρ`, which is the packing bound behind the Lipschitz entropy bound
quoted in the proof of `prop:particle-flow`. -/
def entropyNetSize (C ρ : ℝ) (m : ℕ) : ℕ := ⌈C * (1 + m) / ρ⌉₊ + 1

/-- The chosen resolution grows at most linearly in the time `m`. -/
theorem entropyNetSize_le {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) (m : ℕ) :
    ((entropyNetSize C ρ m : ℕ) : ℝ) ≤ (C / ρ + 2) * ((m : ℝ) + 1) := by
  have hceil : (⌈C * (1 + (m : ℝ)) / ρ⌉₊ : ℝ) ≤ C * (1 + (m : ℝ)) / ρ + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hval : ((entropyNetSize C ρ m : ℕ) : ℝ) = (⌈C * (1 + (m : ℝ)) / ρ⌉₊ : ℝ) + 1 := by
    rw [entropyNetSize]
    push_cast
    ring
  have hdiv : C * (1 + (m : ℝ)) / ρ = (C / ρ) * ((m : ℝ) + 1) := by
    field_simp
    ring
  rw [hdiv] at hceil hval
  rw [hval]
  nlinarith [hceil, Nat.cast_nonneg (α := ℝ) m]

/-- **The dynamical cover.**  If the `m`-th iterate of `F` is Lipschitz with constant `C (1 + m)`
then the grid of resolution `entropyNetSize C ρ m` is an `(m, ρ)`-dynamical cover of the whole
torus: two points at grid distance are still `ρ`-close after `k < m` steps.  This is the
separation argument behind the Lipschitz entropy bound [HasselblattKatok02, Proposition 2.5.5]
that the proof of `prop:particle-flow` quotes, read on covers. -/
theorem isDynCoverOf_torusGrid {F : Torus 3 → Torus 3} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ m : ℕ, LipschitzWith (C * (1 + m)) (F^[m]))
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    Dynamics.IsDynCoverOf F Set.univ { p : Torus 3 × Torus 3 | dist p.1 p.2 < ρ } m
      (torusGrid (entropyNetSize (C : ℝ) ρ m)) := by
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  set N : ℕ := entropyNetSize (C : ℝ) ρ m with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hNlarge : (C : ℝ) * (1 + (m : ℝ)) < ρ * (N : ℝ) := by
    have hceil : (C : ℝ) * (1 + (m : ℝ)) / ρ ≤ (⌈(C : ℝ) * (1 + (m : ℝ)) / ρ⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hNval : (N : ℝ) = (⌈(C : ℝ) * (1 + (m : ℝ)) / ρ⌉₊ : ℝ) + 1 := by
      rw [hN, entropyNetSize]
      push_cast
      ring
    rw [hNval]
    rw [div_le_iff₀ hρ] at hceil
    nlinarith [hρ]
  intro x _
  obtain ⟨g, hg, hd⟩ := exists_mem_torusGrid_dist_le hNpos x
  refine ⟨g, Finset.mem_coe.2 hg, ?_⟩
  rw [Dynamics.mem_dynEntourage]
  intro k hk
  change dist (F^[k] x) (F^[k] g) < ρ
  have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk.le
  have hlip : dist (F^[k] x) (F^[k] g) ≤ ((C : ℝ) * (1 + (k : ℝ))) * dist x g := by
    have hdist := (h k).dist_le_mul x g
    push_cast at hdist
    exact hdist
  calc dist (F^[k] x) (F^[k] g) ≤ ((C : ℝ) * (1 + (k : ℝ))) * dist x g := hlip
    _ ≤ ((C : ℝ) * (1 + (k : ℝ))) * (1 / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ < ρ := by
        rw [mul_one_div, div_lt_iff₀ (by positivity)]
        nlinarith [hNlarge, hNR, hρ, hkm, hCR]

/-- The minimal cardinality of an `(m, ρ)`-dynamical cover grows at most polynomially: this is
the packing bound `s_m(F, ρ) ≤ C_ρ (1 + m)³` behind the entropy step of `prop:particle-flow`, in
the cover form and with the explicit constant `C / ρ + 2`. -/
theorem coverMincard_le_ofReal_pow {F : Torus 3 → Torus 3} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ m : ℕ, LipschitzWith (C * (1 + m)) (F^[m]))
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    ((Dynamics.coverMincard F Set.univ { p : Torus 3 × Torus 3 | dist p.1 p.2 < ρ } m : ℕ∞)
        : ℝ≥0∞)
      ≤ ENNReal.ofReal ((((C : ℝ) / ρ + 2) * ((m : ℝ) + 1)) ^ 3) := by
  have hCR : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hcov := (isDynCoverOf_torusGrid hC h hρ m).coverMincard_le_card
  have h1 : ((Dynamics.coverMincard F Set.univ { p : Torus 3 × Torus 3 | dist p.1 p.2 < ρ } m
      : ℕ∞) : ℝ≥0∞) ≤ (((torusGrid (entropyNetSize (C : ℝ) ρ m)).card : ℕ) : ℝ≥0∞) := by
    have hmono := ENat.toENNReal_mono hcov
    rwa [ENat.toENNReal_coe] at hmono
  refine h1.trans ?_
  have h2 : (((torusGrid (entropyNetSize (C : ℝ) ρ m)).card : ℕ) : ℝ≥0∞)
      ≤ (((entropyNetSize (C : ℝ) ρ m) ^ 3 : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.2 (card_torusGrid_le _)
  refine h2.trans ?_
  rw [← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  exact pow_le_pow_left₀ (by positivity) (entropyNetSize_le hCR hρ m) 3

/-! ## The criterion -/

/-- Every metric entourage of the literal three-torus has vanishing cover entropy for a map with
linearly growing iterate Lipschitz constants. -/
theorem coverEntropyEntourage_le_zero {F : Torus 3 → Torus 3} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ m : ℕ, LipschitzWith (C * (1 + m)) (F^[m]))
    {ρ : ℝ} (hρ : 0 < ρ) :
    Dynamics.coverEntropyEntourage F Set.univ { p : Torus 3 × Torus 3 | dist p.1 p.2 < ρ }
      ≤ 0 := by
  simp only [Dynamics.coverEntropyEntourage]
  exact expGrowthSup_le_zero_of_le_ofReal_pow (by positivity) 3
    (fun m => coverMincard_le_ofReal_pow hC h hρ m)

/-- **Zero topological entropy from linearly growing Lipschitz constants**
(`prop:particle-flow`, entropy clause of the statement and last paragraph of the proof).  A
self-map of the literal three-torus whose iterates satisfy `Lip (F^[m]) ≤ C (1 + m)` has
vanishing cover entropy.  The upper bound is a packing bound inserted into the cover
definition of `h_top`; the lower bound is `Dynamics.coverEntropy_nonneg`. -/
theorem coverEntropy_eq_zero_of_lipschitz_iterate
    {F : Torus 3 → Torus 3} {C : ℝ≥0} (hC : 0 < C)
    (h : ∀ m : ℕ, LipschitzWith (C * (1 + m)) (F^[m])) :
    Dynamics.coverEntropy F Set.univ = 0 := by
  refine le_antisymm ?_ (Dynamics.coverEntropy_nonneg F Set.univ_nonempty)
  rw [Dynamics.coverEntropy_eq_iSup_basis Metric.uniformity_basis_dist F Set.univ]
  exact iSup₂_le fun _ hρ => coverEntropyEntourage_le_zero hC h hρ

end

end FastDynamo
