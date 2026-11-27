/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

/-!
# The support function of a compact convex set in `ℝ^m`

For `K ⊂ ℝ^m = Fin m → ℝ`, the support function `H_K (y) = sup_{z ∈ K} z · y` (`supportFun`), with
the dot product `⬝ᵥ`. The following facts of convex analysis are standard. For `K` nonempty and
compact:

* `dotProduct_le_supportFun`, `exists_dotProduct_eq_supportFun`: the supremum is attained;
* `supportFun_zero`, `supportFun_add_le`, `supportFun_smul`: `H_K` is sublinear;
* `lipschitzWith_supportFun`: `H_K` is Lipschitz;
* `mem_of_forall_dotProduct_le_supportFun`: for `K` also convex, `a ∈ K` if `a · y ≤ H_K (y)` for
  every `y` (Hahn–Banach separation);
* `gradient_supportFun_mem`: for `K` also convex, the gradient of `H_K` lies in `K` wherever `H_K`
  is differentiable.

Two facts about `ℝ^m` that the proofs use: `dotProduct_le_mul_norm_mul_norm` (`z · v ≤ m ‖z‖ ‖v‖`,
sup norms) and `continuousLinearMap_apply_eq_dotProduct` (`L v = (L e_j)_j · v`).
-/

@[expose] public section

noncomputable section

namespace CalculusOfVariations

variable {m : ℕ}

/-- The support function `H_K (y) = sup_{z ∈ K} z · y` of `K ⊂ ℝ^m` (`0` for `K = ∅`, and for an
unbounded image, by the conventions of `sSup` on `ℝ`). -/
def supportFun (K : Set (Fin m → ℝ)) (y : Fin m → ℝ) : ℝ :=
  sSup ((fun z => z ⬝ᵥ y) '' K)

variable {K : Set (Fin m → ℝ)}

/-- The linear form `z ↦ z · y` is continuous. -/
private theorem continuous_dotProduct_left (y : Fin m → ℝ) :
    Continuous fun z : Fin m → ℝ => z ⬝ᵥ y :=
  continuous_id.dotProduct continuous_const

/-- `z · v ≤ m ‖z‖ ‖v‖`, with the sup norms. -/
theorem dotProduct_le_mul_norm_mul_norm (z v : Fin m → ℝ) :
    z ⬝ᵥ v ≤ m * (‖z‖ * ‖v‖) := by
  calc z ⬝ᵥ v = ∑ i, z i * v i := rfl
    _ ≤ ∑ _i : Fin m, ‖z‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
        calc z i * v i ≤ |z i * v i| := le_abs_self _
          _ = ‖z i‖ * ‖v i‖ := by rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖z‖ * ‖v‖ := mul_le_mul (norm_le_pi_norm z i) (norm_le_pi_norm v i)
              (norm_nonneg _) (norm_nonneg _)
    _ = m * (‖z‖ * ‖v‖) := by simp

/-- A continuous linear functional on `ℝ^m` is the dot product with its values on the standard
basis: `L v = (L e_j)_j · v`. -/
theorem continuousLinearMap_apply_eq_dotProduct (L : (Fin m → ℝ) →L[ℝ] ℝ) (v : Fin m → ℝ) :
    L v = (fun j => L (Pi.single j 1)) ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum, map_smul, dotProduct, mul_comm]

/-- `z · y ≤ H_K (y)` for every `z` of a compact `K`. -/
theorem dotProduct_le_supportFun (hK : IsCompact K) {z : Fin m → ℝ} (hz : z ∈ K)
    (y : Fin m → ℝ) : z ⬝ᵥ y ≤ supportFun K y :=
  le_csSup (hK.image (continuous_dotProduct_left y)).bddAbove (Set.mem_image_of_mem _ hz)

/-- For `K` compact and nonempty, the supremum `H_K (y)` is attained: `z · y = H_K (y)` for some
`z ∈ K`. -/
theorem exists_dotProduct_eq_supportFun (hK : IsCompact K) (hne : K.Nonempty) (y : Fin m → ℝ) :
    ∃ z ∈ K, z ⬝ᵥ y = supportFun K y := by
  obtain ⟨z, hz, hzy⟩ := (hK.image (continuous_dotProduct_left y)).sSup_mem (hne.image _)
  exact ⟨z, hz, hzy⟩

/-- `H_K (0) = 0` for `K` compact and nonempty. -/
theorem supportFun_zero (hK : IsCompact K) (hne : K.Nonempty) : supportFun K 0 = 0 := by
  obtain ⟨z, -, hz⟩ := exists_dotProduct_eq_supportFun hK hne 0
  rw [← hz, dotProduct_zero]

/-- Subadditivity: `H_K (y + y') ≤ H_K (y) + H_K (y')` for `K` compact and nonempty. -/
theorem supportFun_add_le (hK : IsCompact K) (hne : K.Nonempty) (y y' : Fin m → ℝ) :
    supportFun K (y + y') ≤ supportFun K y + supportFun K y' := by
  obtain ⟨z, hz, hzy⟩ := exists_dotProduct_eq_supportFun hK hne (y + y')
  rw [← hzy, dotProduct_add]
  exact add_le_add (dotProduct_le_supportFun hK hz y) (dotProduct_le_supportFun hK hz y')

/-- Positive homogeneity: `H_K (c y) = c H_K (y)` for `c ≥ 0`, `K` compact and nonempty. -/
theorem supportFun_smul (hK : IsCompact K) (hne : K.Nonempty) {c : ℝ} (hc : 0 ≤ c)
    (y : Fin m → ℝ) : supportFun K (c • y) = c * supportFun K y := by
  apply le_antisymm
  · obtain ⟨z, hz, hzy⟩ := exists_dotProduct_eq_supportFun hK hne (c • y)
    rw [← hzy, dotProduct_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (dotProduct_le_supportFun hK hz y) hc
  · obtain ⟨z, hz, hzy⟩ := exists_dotProduct_eq_supportFun hK hne y
    rw [← hzy, ← smul_eq_mul, ← dotProduct_smul]
    exact dotProduct_le_supportFun hK hz _

/-- For `K` compact and nonempty, `H_K` is Lipschitz: if `‖z‖ ≤ R` on `K`, the constant `m R`
works (sup norms). -/
theorem lipschitzWith_supportFun (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ C : NNReal, LipschitzWith C (supportFun K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨Real.toNNReal (m * R), LipschitzWith.of_le_add_mul _ fun y y' => ?_⟩
  obtain ⟨z, hz, hzy⟩ := exists_dotProduct_eq_supportFun hK hne y
  have h1 := dotProduct_le_supportFun hK hz y'
  have h2 : z ⬝ᵥ (y - y') ≤ m * R * dist y y' := by
    rw [dist_eq_norm]
    calc _ ≤ m * (‖z‖ * ‖y - y'‖) := dotProduct_le_mul_norm_mul_norm z _
      _ ≤ m * (R * ‖y - y'‖) := by gcongr; exact hR z hz
      _ = _ := by ring
  rw [dotProduct_sub] at h2
  rw [← hzy]
  have h3 : (m * R : ℝ) * dist y y' ≤ Real.toNNReal (m * R) * dist y y' :=
    mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
  linarith

/-- For `K` compact, convex and nonempty, `a ∈ K` if `a · y ≤ H_K (y)` for every `y`.

Proof: if `a ∉ K`, the Hahn–Banach separation of the point `a` from the closed convex `K`
(`geometric_hahn_banach_closed_point`) gives a linear functional `w · _` with `H_K (w) < w · a`.

`K.Nonempty` is needed: for `K = ∅`, `H_K = sSup ∅ = 0` and `a = 0` satisfies the hypothesis. -/
theorem mem_of_forall_dotProduct_le_supportFun (hK : IsCompact K) (hne : K.Nonempty)
    (hcv : Convex ℝ K) {a : Fin m → ℝ} (h : ∀ y, a ⬝ᵥ y ≤ supportFun K y) : a ∈ K := by
  by_contra ha
  obtain ⟨f, u, hfK, hfa⟩ := geometric_hahn_banach_closed_point hcv hK.isClosed ha
  obtain ⟨z, hz, hzw⟩ := exists_dotProduct_eq_supportFun hK hne fun j => f (Pi.single j 1)
  have h1 := h fun j => f (Pi.single j 1)
  have h2 := hfK z hz
  rw [continuousLinearMap_apply_eq_dotProduct] at hfa h2
  rw [← hzw, dotProduct_comm] at h1
  rw [dotProduct_comm] at h2
  linarith

/-- For `K` compact, convex and nonempty, wherever `H_K` is differentiable, its gradient
`(∂_j H_K (y))_j` lies in `K`.

Proof: by sublinearity, `H_K (y + t v) ≤ H_K (y) + t H_K (v)` for `t > 0`; dividing by `t` and
letting `t → 0⁺`, the gradient `g` satisfies `g · v = D H_K (y) v ≤ H_K (v)` for every `v`, so
`g ∈ K` by `mem_of_forall_dotProduct_le_supportFun`. -/
theorem gradient_supportFun_mem (hK : IsCompact K) (hne : K.Nonempty) (hcv : Convex ℝ K)
    {y : Fin m → ℝ} (hy : DifferentiableAt ℝ (supportFun K) y) :
    (fun j => fderiv ℝ (supportFun K) y (Pi.single j 1)) ∈ K := by
  apply mem_of_forall_dotProduct_le_supportFun hK hne hcv
  intro v
  rw [← continuousLinearMap_apply_eq_dotProduct]
  have hd : HasDerivAt (fun t : ℝ => supportFun K (y + t • v))
      (fderiv ℝ (supportFun K) y v) 0 := by
    have := hy.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ))
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y) (by simp)
    simpa [Function.comp_def] using this
  refine le_of_tendsto hd.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
  simp only [zero_smul, add_zero, smul_eq_mul, zero_add]
  rw [inv_mul_le_iff₀ htpos]
  have := supportFun_add_le hK hne y (t • v)
  rw [supportFun_smul hK hne htpos.le] at this
  linarith

end CalculusOfVariations
