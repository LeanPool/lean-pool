/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.AtomAnalysis
public import LeanPool.FunctionSpaces.Domains.Lipschitz.LipschitzGraph

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The boundary of a Lipschitz graph domain as a graph over a hyperplane

For a Lipschitz graph domain `Ω = {x : φ(x) < ⟪x, e⟫}` (`Rd.LipschitzGraph`), the boundary is the
graph of `φ` over the hyperplane `H = e^⊥` (`Rd.LipschitzGraph.hyperplane`), of dimension `n - 1`
(`Rd.LipschitzGraph.finrank_hyperplane_add_one`), with `H^⊥ = ℝ e`
(`Rd.LipschitzGraph.orthogonal_hyperplane`) and the Lebesgue measure of its inner product.
The **graph map** `γ(x') = x' + φ(x') e` (`Rd.LipschitzGraph.graphMap`) satisfies `P(γ x') = x'`
for the orthogonal projection `Px = x - ⟪x, e⟫ e` onto `H` (`Rd.LipschitzGraph.proj`, from the
formula for the projection onto the hyperplane of any unit vector,
`Rd.coe_orthogonalProjectionOnto_orthogonalComplement_singleton`), and it is Lipschitz with
constant `1 + M` (`Rd.LipschitzGraph.norm_graphMap_sub_le`), and the graph function `φ|_H`
(`Rd.LipschitzGraph.phiH`) is `M`-Lipschitz (`Rd.LipschitzGraph.lipschitzWith_phiH`). The
boundary of `Ω` is the graph: `y ∈ ∂Ω` iff `γ(Py) = y` iff `⟪y, e⟫ = φ(y)`
(`Rd.LipschitzGraph.mem_frontier_domain_iff`, `Rd.LipschitzGraph.graphMap_proj_eq_iff`), so `∂Ω`
is the range of `γ` (`Rd.LipschitzGraph.range_graphMap`).

**Traces of atoms** (`Rd.LipschitzGraph.isRegularAtom_comp_graphMap`): a continuous `a` on `V`
that vanishes outside `closedBall(c, d 2^(-j))`, with `|a| ≤ A` and `|a(x + h) - a(x)| ≤ A
min(1, 2^j ‖h‖)`,
restricts to `a ∘ γ`, which vanishes outside `closedBall(Pc, d 2^(-j))` in `H`, with `|a ∘ γ| ≤
A` and
`|a ∘ γ(x' + h') - a ∘ γ(x')| ≤ (1 + M) A min(1, 2^j ‖h'‖)`: a regular atom of order and exponent
`1` on `H`, as in the proof of Schneider–Vybíral, Theorem 4.2. Only sup bounds enter.
-/

@[expose] public section

open MeasureTheory Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-- `min(1, K t) ≤ K min(1, t)` for `K ≥ 1`. -/
theorem min_one_mul_le {K : ℝ≥0∞} (hK : 1 ≤ K) (t : ℝ≥0∞) : min 1 (K * t) ≤ K * min 1 t := by
  rcases le_total t 1 with ht | ht
  · rw [min_eq_right ht]
    exact min_le_right _ _
  · rw [min_eq_left ht, mul_one]
    exact (min_le_left _ _).trans hK

/-- The orthogonal projection onto the hyperplane `ν^⊥` of a unit vector `ν` is
`P w = w - ⟪ν, w⟫ ν`: the identity minus Mathlib's projection onto the line `ℝ ν`
(`Submodule.starProjection_unit_singleton`). -/
theorem coe_orthogonalProjectionOnto_orthogonalComplement_singleton {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ν : V} (hν : ‖ν‖ = 1) (w : V) :
    ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto w : V) = w - inner ℝ ν w • ν := by
  rw [Submodule.orthogonalProjectionOnto_orthogonal, Submodule.coe_mk,
    Submodule.starProjection_unit_singleton ℝ hν]

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (Ω : LipschitzGraph V)

/-! ### The hyperplane and the graph map -/

/-- The **hyperplane** `H = e^⊥` over which the boundary of `Ω` is a graph. -/
noncomputable abbrev hyperplane : Submodule ℝ V := (ℝ ∙ Ω.e)ᗮ

/-- The orthogonal complement of the hyperplane is the line `ℝ e` (Mathlib's
`Submodule.orthogonal_orthogonal`). -/
theorem orthogonal_hyperplane : Ω.hyperplaneᗮ = ℝ ∙ Ω.e := Submodule.orthogonal_orthogonal _

/-- The upward direction is nonzero. -/
theorem e_ne_zero : Ω.e ≠ 0 := fun h => by simpa [h] using Ω.norm_e

/-- `⟪e, e⟫ = 1`. -/
theorem inner_e_self : inner ℝ Ω.e Ω.e = 1 := by
  rw [real_inner_self_eq_norm_sq, Ω.norm_e, one_pow]

/-- The points of `H` are orthogonal to `e`. -/
theorem inner_coe_e (x' : Ω.hyperplane) : inner ℝ (x' : V) Ω.e = 0 := by
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 x'.2

/-- `x - ⟪x, e⟫ e ∈ H`. -/
theorem sub_inner_smul_mem (x : V) : x - inner ℝ x Ω.e • Ω.e ∈ Ω.hyperplane := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right,
    Ω.inner_e_self, mul_one, real_inner_comm, sub_self]

/-- `H` has dimension `n - 1`. -/
theorem finrank_hyperplane_add_one [FiniteDimensional ℝ V] :
    finrank ℝ Ω.hyperplane + 1 = finrank ℝ V := by
  have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ Ω.e)
  rw [finrank_span_singleton Ω.e_ne_zero] at h
  change finrank ℝ ↥(ℝ ∙ Ω.e)ᗮ + 1 = finrank ℝ V
  omega

/-- `dim H = n - 1`, with the subtraction of natural numbers. -/
theorem finrank_hyperplane_eq_sub_one [FiniteDimensional ℝ V] :
    finrank ℝ Ω.hyperplane = finrank ℝ V - 1 := by
  have h := Ω.finrank_hyperplane_add_one
  omega

/-- The **orthogonal projection** onto `H`. -/
noncomputable def proj : V →L[ℝ] Ω.hyperplane := Ω.hyperplane.orthogonalProjectionOnto

/-- `Px = x - ⟪x, e⟫ e`. -/
theorem coe_proj (x : V) : (Ω.proj x : V) = x - inner ℝ x Ω.e • Ω.e := by
  rw [proj, coe_orthogonalProjectionOnto_orthogonalComplement_singleton Ω.norm_e, real_inner_comm]

/-- For `a ∈ H`, `⟪a, v⟫ = ⟪a, Pv⟫`: Mathlib's
`Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`. -/
theorem inner_coe_eq_inner_proj (a : Ω.hyperplane) (v : V) :
    inner ℝ (a : V) v = inner ℝ a (Ω.proj v) :=
  (Ω.hyperplane.inner_orthogonalProjectionOnto_eq_of_mem_left a v).symm

/-- `‖Px‖ ≤ ‖x‖`. -/
theorem norm_proj_le (x : V) : ‖Ω.proj x‖ ≤ ‖x‖ :=
  Submodule.norm_orthogonalProjectionOnto_apply_le _ x

/-- `P x' = x'` on `H`. -/
theorem proj_coe (x' : Ω.hyperplane) : Ω.proj x' = x' :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x'

/-- `P e = 0`. -/
theorem proj_e : Ω.proj Ω.e = 0 := by
  apply Subtype.ext
  rw [coe_proj, Ω.inner_e_self, one_smul, sub_self]
  rfl

/-- The **graph map** `γ(x') = x' + φ(x') e`. -/
noncomputable def graphMap (x' : Ω.hyperplane) : V := (x' : V) + Ω.phi x' • Ω.e

/-- `P(γ x') = x'`. -/
theorem proj_graphMap (x' : Ω.hyperplane) : Ω.proj (Ω.graphMap x') = x' := by
  rw [graphMap, map_add, map_smul, Ω.proj_e, smul_zero, add_zero, Ω.proj_coe]

/-- `⟪γ x', e⟫ = φ(x')`: the graph map lands on the boundary. -/
theorem inner_graphMap (x' : Ω.hyperplane) : inner ℝ (Ω.graphMap x') Ω.e = Ω.phi x' := by
  rw [graphMap, inner_add_left, Ω.inner_coe_e, real_inner_smul_left, Ω.inner_e_self, mul_one,
    zero_add]

/-- `φ(γ x') = φ(x')`. -/
theorem phi_graphMap (x' : Ω.hyperplane) : Ω.phi (Ω.graphMap x') = Ω.phi x' :=
  Ω.const _ _

/-- **The graph map is Lipschitz**: `‖γ x' - γ y'‖ ≤ (1 + M) ‖x' - y'‖`. -/
theorem norm_graphMap_sub_le (x' y' : Ω.hyperplane) :
    ‖Ω.graphMap x' - Ω.graphMap y'‖ ≤ (1 + Ω.M) * ‖x' - y'‖ := by
  have hsub : Ω.graphMap x' - Ω.graphMap y' =
      ((x' - y' : Ω.hyperplane) : V) + (Ω.phi x' - Ω.phi y') • Ω.e := by
    simp only [graphMap, Submodule.coe_sub, sub_smul]
    abel
  have hlip : |Ω.phi x' - Ω.phi y'| ≤ Ω.M * ‖x' - y'‖ := by
    have h := Ω.lipschitz x' y'
    rwa [← Submodule.coe_sub, Submodule.norm_coe] at h
  rw [hsub]
  calc ‖((x' - y' : Ω.hyperplane) : V) + (Ω.phi x' - Ω.phi y') • Ω.e‖
      ≤ ‖((x' - y' : Ω.hyperplane) : V)‖ + ‖(Ω.phi x' - Ω.phi y') • Ω.e‖ := norm_add_le _ _
    _ = ‖x' - y'‖ + |Ω.phi x' - Ω.phi y'| := by
        rw [norm_smul, Ω.norm_e, mul_one, Real.norm_eq_abs, Submodule.norm_coe]
    _ ≤ ‖x' - y'‖ + Ω.M * ‖x' - y'‖ := add_le_add le_rfl hlip
    _ = (1 + Ω.M) * ‖x' - y'‖ := by ring

/-- The graph map is continuous. -/
theorem continuous_graphMap : Continuous Ω.graphMap :=
  continuous_subtype_val.add ((Ω.continuous_phi.comp continuous_subtype_val).smul continuous_const)

/-- The graph function on the hyperplane, `φ|_H`. -/
noncomputable def phiH (x' : Ω.hyperplane) : ℝ := Ω.phi x'

/-- `φ|_H` is `M`-Lipschitz. -/
theorem lipschitzWith_phiH : LipschitzWith ⟨Ω.M, Ω.M_nonneg⟩ Ω.phiH :=
  LipschitzWith.of_dist_le_mul fun x' y' => by
    rw [Real.dist_eq, dist_eq_norm, ← Submodule.norm_coe, Submodule.coe_sub]
    exact Ω.lipschitz x' y'

/-- `φ|_H` is continuous. -/
theorem continuous_phiH : Continuous Ω.phiH := Ω.lipschitzWith_phiH.continuous

/-- **Steps into the cone from the boundary stay in the domain**: `γ x' + K ⊆ Ω`, since
`φ(γ x') = ⟪γ x', e⟫` and a step `y` into the cone raises `⟪·, e⟫` faster than `φ`
(`Rd.LipschitzGraph.phi_add_le`). -/
theorem graphMap_add_mem (x' : Ω.hyperplane) {y : V} (hy : y ∈ Ω.cone) :
    Ω.graphMap x' + y ∈ Ω.domain := by
  have h := Ω.phi_add_le (Ω.graphMap x') y
  have hy' : Ω.M * ‖y - inner ℝ y Ω.e • Ω.e‖ < inner ℝ y Ω.e := hy
  rw [Ω.phi_graphMap] at h
  change Ω.phi (Ω.graphMap x' + y) < inner ℝ (Ω.graphMap x' + y) Ω.e
  rw [inner_add_left, Ω.inner_graphMap]
  linarith

/-- `‖x' - Pc‖ ≤ ‖γ x' - c‖`: the projection is a contraction. -/
theorem norm_sub_proj_le (x' : Ω.hyperplane) (c : V) : ‖x' - Ω.proj c‖ ≤ ‖Ω.graphMap x' - c‖ := by
  calc ‖x' - Ω.proj c‖ = ‖Ω.proj (Ω.graphMap x' - c)‖ := by rw [map_sub, Ω.proj_graphMap]
    _ ≤ ‖Ω.graphMap x' - c‖ := Ω.norm_proj_le _

/-! ### The boundary of a graph domain -/

/-- `φ(Py) = φ(y)`: `φ` is constant in the direction `e`. -/
theorem phi_proj (y : V) : Ω.phi (Ω.proj y) = Ω.phi y := by
  have h := Ω.const (Ω.proj y) (inner ℝ y Ω.e)
  rw [coe_proj, sub_add_cancel] at h
  rw [coe_proj]
  exact h.symm

/-- **The graph** `γ(Py) = y` consists of the points with `⟪y, e⟫ = φ(y)`. -/
theorem graphMap_proj_eq_iff (y : V) :
    Ω.graphMap (Ω.proj y) = y ↔ inner ℝ y Ω.e = Ω.phi y := by
  constructor
  · intro h
    have h1 := Ω.inner_graphMap (Ω.proj y)
    rw [h, phi_proj] at h1
    exact h1
  · intro h
    rw [graphMap, phi_proj, coe_proj, ← h, sub_add_cancel]

/-- **The boundary of a graph domain is the graph**: `y ∈ ∂Ω` iff `γ(Py) = y`, since the
closure of `Ω` is `{φ ≤ ⟪·, e⟫}` (`Rd.LipschitzGraph.closure_domain`) and `Ω` is open. -/
theorem mem_frontier_domain_iff (y : V) :
    y ∈ frontier Ω.domain ↔ Ω.graphMap (Ω.proj y) = y := by
  rw [graphMap_proj_eq_iff, frontier, Ω.isOpen_domain.interior_eq, Ω.closure_domain]
  exact ⟨fun h => (le_antisymm h.1 (not_lt.1 h.2)).symm, fun h => ⟨h.ge, h.not_gt⟩⟩

/-- **The range of the graph map is the boundary** of the graph domain. -/
theorem range_graphMap : Set.range Ω.graphMap = frontier Ω.domain := by
  ext y
  rw [Ω.mem_frontier_domain_iff]
  constructor
  · rintro ⟨x', rfl⟩
    rw [Ω.proj_graphMap]
  · intro h
    exact ⟨_, h⟩

/-! ### Traces of atoms -/

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Traces of atoms** (as in the proof of Schneider–Vybíral, Theorem 4.2): if `a` is continuous,
vanishes outside `closedBall(c, d 2^(-j))`, `|a| ≤ A` and `|a(x + h) - a(x)| ≤ A min(1, 2^j
‖h‖)`, then
`a ∘ γ` is a regular atom of order and exponent `1` on `H` with centre `Pc`, radius factor `d` and
constant `(1 + M) A (2 d^(n-1) |B_1|)^(1/p)`, since `γ` is Lipschitz with constant `1 + M`. -/
theorem isRegularAtom_comp_graphMap {p : ℝ≥0∞} {d : ℝ} (hd : 0 ≤ d) {A : ℝ≥0∞} {j : ℕ} {c : V}
    {a : V → ℂ} (hac : Continuous a) (h0 : ∀ x, d / 2 ^ j < ‖x - c‖ → a x = 0)
    (hle : ∀ x, ‖a x‖ₑ ≤ A)
    (hdiff : ∀ h x, ‖a (x + h) - a x‖ₑ ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖))) :
    IsRegularAtom p 1 1 d (ENNReal.ofReal (1 + Ω.M) * A * (((1 + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (d ^ finrank ℝ Ω.hyperplane) * volume (ball (0 : Ω.hyperplane) 1))) ^
        (1 / p.toReal)) j (Ω.proj c) (a ∘ Ω.graphMap) := by
  have hK : 1 ≤ ENNReal.ofReal (1 + Ω.M) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Ω.M_nonneg])
  refine isRegularAtom_of_pointwise hd (hac.comp Ω.continuous_graphMap).aestronglyMeasurable
    (fun x' hx' => ?_) (fun x' => ?_) (fun h' x' => ?_)
  · exact h0 _ (hx'.trans_le (Ω.norm_sub_proj_le x' c))
  · exact (hle _).trans (le_mul_of_one_le_left' hK)
  · simp only [Function.iterate_one, fwdDiff, Function.comp_apply, ENNReal.rpow_one]
    set v := Ω.graphMap (x' + h') - Ω.graphMap x'
    have hv : ‖v‖ ≤ (1 + Ω.M) * ‖h'‖ := by
      have h := Ω.norm_graphMap_sub_le (x' + h') x'
      rwa [add_sub_cancel_left] at h
    have h1 := hdiff v (Ω.graphMap x')
    rw [add_sub_cancel] at h1
    have h2 : 2 ^ j * ‖v‖ ≤ (1 + Ω.M) * (2 ^ j * ‖h'‖) := by
      calc 2 ^ j * ‖v‖ ≤ 2 ^ j * ((1 + Ω.M) * ‖h'‖) :=
            mul_le_mul_of_nonneg_left hv (by positivity)
        _ = (1 + Ω.M) * (2 ^ j * ‖h'‖) := by ring
    calc ‖a (Ω.graphMap (x' + h')) - a (Ω.graphMap x')‖ₑ
        ≤ A * min 1 (ENNReal.ofReal (2 ^ j * ‖v‖)) := h1
      _ ≤ A * min 1 (ENNReal.ofReal (1 + Ω.M) * ENNReal.ofReal (2 ^ j * ‖h'‖)) := by
          gcongr
          rw [← ENNReal.ofReal_mul (by linarith [Ω.M_nonneg])]
          exact ENNReal.ofReal_le_ofReal h2
      _ ≤ A * (ENNReal.ofReal (1 + Ω.M) * min 1 (ENNReal.ofReal (2 ^ j * ‖h'‖))) :=
          mul_le_mul' le_rfl (min_one_mul_le hK _)
      _ = ENNReal.ofReal (1 + Ω.M) * A * min 1 (ENNReal.ofReal (2 ^ j * ‖h'‖)) := by ring

end LipschitzGraph

end Rd
