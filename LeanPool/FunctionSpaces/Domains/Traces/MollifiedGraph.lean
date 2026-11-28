/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Traces.GraphTrace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The mollified graph and the vertical cut-off

To extend functions from the boundary of a Lipschitz graph domain `Ω = {φ(x) < ⟪x, e⟫}` into `V`
with smoothness above `1`, the graph is replaced at each scale `2^(-j)` by a smoothed one:
`φ_j = Re (ρ_{2^j} ⋆ φ)` on the hyperplane `H` (`Rd.LipschitzGraph.smoothGraph`), with `ρ` the
moment kernel of order `2` of a bump of radius `1`. Only differences enter, no derivatives of
convolutions:

* `φ_j` is Lipschitz with constant `M ‖ρ‖_1` (`Rd.LipschitzGraph.abs_smoothGraph_sub_le`);
* `|φ_j - φ| ≤ 2 M ‖ρ‖_1 2^(-j)` (`Rd.LipschitzGraph.abs_smoothGraph_sub_phi_le`);
* `|Δ_h^2 φ_j| ≤ 4 M ‖D^2 ρ‖_1 2^j ‖h‖^2` for `‖h‖ ≤ 2^(-j)`
  (`Rd.LipschitzGraph.abs_second_smoothGraph_le`), since `Δ_h^2 (ρ_{2^j} ⋆ φ) = (Δ_h^2 ρ_{2^j}) ⋆ φ`
  and `∫ Δ_h^2 ρ_{2^j} = 0`.

The **vertical cut-off** `v_j(x) = χ(2^j (⟪x, e⟫ - φ_j(Px)))` (`Rd.LipschitzGraph.vertCutoff`),
with a smooth profile `χ` equal to `1` on `[-c, c]`, `c > 2 M ‖ρ‖_1`, equals `1` on the boundary
(`Rd.LipschitzGraph.vertCutoff_graphMap`), vanishes at distance `(c + 1) 2^(-j)` above or below the
smoothed graph, and has `|Δ_h^m v_j| ≤ B min(1, (2^j ‖h‖)^m)` for `m ≤ 2`
(`Rd.LipschitzGraph.enorm_higherDiff_vertCutoff_le`): by the chain rule for differences,
`Δ_h^2 (χ ∘ ψ) = [χ(ψ_2) - χ(2ψ_1 - ψ_0)] + Δ_t^2 χ(ψ_0)` with `t = ψ_1 - ψ_0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### Differences of length one and two -/

section Differences

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ W] in
/-- `Δ_h f(x) = f(x + h) - f(x)`. -/
theorem higherDiff_one_apply (h : W) (f : W → ℂ) (x : W) :
    (fwdDiff h)^[1] f x = f (x + h) - f x := by
  rw [Function.iterate_one, fwdDiff_eq_sub, Pi.sub_apply]

/-- `Δ_h^2 f(x) = f(x + 2h) - 2 f(x + h) + f(x)`. -/
theorem higherDiff_two_apply (h : W) (f : W → ℂ) (x : W) :
    (fwdDiff h)^[2] f x = f (x + (2 : ℝ) • h) - 2 * f (x + h) + f x := by
  rw [higherDiff_apply]
  simp [Finset.sum_range_succ]
  ring

end Differences

/-! ### Convolution with Lipschitz functions -/

section Lipschitz

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- `∫ Δ_h^r K = 0` for integrable `K` and `r ≥ 1`: a difference integrates to `0`. -/
theorem integral_higherDiff_eq_zero {K : W → ℂ} (hK : Integrable K) {r : ℕ} (hr : 1 ≤ r) (h : W) :
    ∫ x, (fwdDiff h)^[r] K x = 0 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hg := integrable_higherDiff hK r' h
  have heq : ∀ x, (fwdDiff h)^[r' + 1] K x =
      (fwdDiff h)^[r'] K (x + h) - (fwdDiff h)^[r'] K x := fun x => by
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub, Pi.sub_apply]
  simp_rw [heq]
  rw [integral_sub (hg.comp_add_right h) hg, integral_add_right_eq_self, sub_self]

/-- **Convolution keeps Lipschitz bounds**: for `u` with `‖u(x) - u(y)‖ ≤ M ‖x - y‖`,
`‖(K ⋆ u)(x) - (K ⋆ u)(y)‖ ≤ M ‖K‖_1 ‖x - y‖`. -/
theorem norm_conv_sub_conv_le {K u : W → ℂ} (hK : Integrable K) {M : ℝ}
    (hu : ∀ x y, ‖u x - u y‖ ≤ M * ‖x - y‖)
    (hint : ∀ x, Integrable (fun z => K z * u (x - z))) (x y : W) :
    ‖conv K u volume x - conv K u volume y‖ ≤ M * (∫ z, ‖K z‖) * ‖x - y‖ := by
  rw [conv_apply, conv_apply, ← integral_sub (hint x) (hint y)]
  calc ‖∫ z, (K z * u (x - z) - K z * u (y - z))‖ ≤ ∫ z, ‖K z‖ * (M * ‖x - y‖) :=
        norm_integral_le_of_norm_le (hK.norm.mul_const _) (Eventually.of_forall fun z => by
          rw [← mul_sub, norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h := hu (x - z) (y - z)
          rwa [sub_sub_sub_cancel_right] at h)
    _ = M * (∫ z, ‖K z‖) * ‖x - y‖ := by
        rw [integral_mul_const]
        ring

/-- **Convolution moves Lipschitz functions little**: for `∫ K = 1` and `K = 0` outside
`closedBall(0, R)`, `‖(K ⋆ u)(x) - u(x)‖ ≤ M R ‖K‖_1`. -/
theorem norm_conv_sub_self_le {K u : W → ℂ} (hK : Integrable K) (h1 : ∫ z, K z = 1) {R : ℝ}
    (hKR : ∀ z, R < ‖z‖ → K z = 0) {M : ℝ} (hM : 0 ≤ M) (hu : ∀ x y, ‖u x - u y‖ ≤ M * ‖x - y‖)
    {x : W} (hint : Integrable (fun z => K z * u (x - z))) :
    ‖conv K u volume x - u x‖ ≤ M * R * ∫ z, ‖K z‖ := by
  have hux : u x = ∫ z, K z * u x := by rw [integral_mul_const, h1, one_mul]
  rw [conv_apply, hux, ← integral_sub hint (hK.mul_const _)]
  calc ‖∫ z, (K z * u (x - z) - K z * u x)‖ ≤ ∫ z, ‖K z‖ * (M * R) :=
        norm_integral_le_of_norm_le (hK.norm.mul_const _) (Eventually.of_forall fun z => by
          rw [← mul_sub, norm_mul]
          by_cases hz : K z = 0
          · simp [hz]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hzR : ‖z‖ ≤ R := not_lt.1 fun h => hz (hKR z h)
          calc ‖u (x - z) - u x‖ ≤ M * ‖x - z - x‖ := hu _ _
            _ = M * ‖z‖ := by rw [sub_sub_cancel_left, norm_neg]
            _ ≤ M * R := mul_le_mul_of_nonneg_left hzR hM)
    _ = M * R * ∫ z, ‖K z‖ := by
        rw [integral_mul_const]
        ring

/-- **Second differences of convolutions with Lipschitz functions**: for `K = 0` outside
`closedBall(0, R)`, `‖Δ_h^2 (K ⋆ u)(x)‖ ≤ M (R + 2‖h‖) ‖Δ_h^2 K‖_1`, since
`Δ_h^2 (K ⋆ u) = (Δ_h^2 K) ⋆ u` and `∫ Δ_h^2 K = 0`. -/
theorem norm_higherDiff_two_conv_le {K u : W → ℂ} (hK : Integrable K) {R : ℝ}
    (hKR : ∀ z, R < ‖z‖ → K z = 0) {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ x y, ‖u x - u y‖ ≤ M * ‖x - y‖)
    (htr : ∀ v x, Integrable (fun z => K (z + v) * u (x - z))) (h x : W) :
    ‖(fwdDiff h)^[2] (conv K u volume) x‖ ≤ M * (R + 2 * ‖h‖) * ∫ z, ‖(fwdDiff h)^[2] K z‖ := by
  rw [higherDiff_conv_apply htr 2 h x, conv_apply]
  have hint2 : Integrable (fun z => (fwdDiff h)^[2] K z * u (x - z)) := by
    simp_rw [higherDiff_apply, Finset.sum_mul]
    exact integrable_finsetSum _ fun l _ =>
      ((htr ((l : ℝ) • h) x).const_mul ((-1 : ℂ) ^ (2 - l) * (Nat.choose 2 l : ℂ))).congr
        (Eventually.of_forall fun z => by ring)
  have h0 : ∫ z, (fwdDiff h)^[2] K z * u x = 0 := by
    rw [integral_mul_const, integral_higherDiff_eq_zero hK (by norm_num), zero_mul]
  rw [← sub_zero (∫ z, (fwdDiff h)^[2] K z * u (x - z)), ← h0,
    ← integral_sub hint2 ((integrable_higherDiff hK 2 h).mul_const _)]
  calc ‖∫ z, ((fwdDiff h)^[2] K z * u (x - z) - (fwdDiff h)^[2] K z * u x)‖
      ≤ ∫ z, ‖(fwdDiff h)^[2] K z‖ * (M * (R + 2 * ‖h‖)) :=
        norm_integral_le_of_norm_le ((integrable_higherDiff hK 2 h).norm.mul_const _)
          (Eventually.of_forall fun z => by
            rw [← mul_sub, norm_mul]
            by_cases hz : (fwdDiff h)^[2] K z = 0
            · simp [hz]
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have hzR : ‖z‖ ≤ R + 2 * ‖h‖ := by
              rw [higherDiff_apply] at hz
              obtain ⟨l, hl, hl0⟩ : ∃ l ∈ Finset.range (2 + 1), K (z + (l : ℝ) • h) ≠ 0 := by
                by_contra hcon
                push Not at hcon
                exact hz (Finset.sum_eq_zero fun l hl => by rw [hcon l hl, mul_zero])
              have h1 : ‖z + (l : ℝ) • h‖ ≤ R := not_lt.1 fun h' => hl0 (hKR _ h')
              have hl' : (l : ℝ) ≤ 2 := by
                exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
              have h2 : ‖(l : ℝ) • h‖ ≤ 2 * ‖h‖ := by
                rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg l)]
                exact mul_le_mul_of_nonneg_right hl' (norm_nonneg h)
              calc ‖z‖ = ‖(z + (l : ℝ) • h) - (l : ℝ) • h‖ := by rw [add_sub_cancel_right]
                _ ≤ ‖z + (l : ℝ) • h‖ + ‖(l : ℝ) • h‖ := norm_sub_le _ _
                _ ≤ R + 2 * ‖h‖ := add_le_add h1 h2
            calc ‖u (x - z) - u x‖ ≤ M * ‖x - z - x‖ := hu _ _
              _ = M * ‖z‖ := by rw [sub_sub_cancel_left, norm_neg]
              _ ≤ M * (R + 2 * ‖h‖) := mul_le_mul_of_nonneg_left hzR hM)
    _ = M * (R + 2 * ‖h‖) * ∫ z, ‖(fwdDiff h)^[2] K z‖ := by
        rw [integral_mul_const]
        ring

end Lipschitz

namespace LocalMeansBump

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] (b : LocalMeansBump W)

/-- `∫ |m_{2^j}| = ∫ |m|`. -/
theorem integral_norm_scaled (L j : ℕ) :
    ∫ z, ‖b.scaled L j z‖ = ∫ z, ‖momentKernel b.toFun L z‖ := by
  have hm := integrable_momentKernel b.integrable L
  rw [integral_norm_eq_lintegral_eNorm (b.integrable_scaled L j).aestronglyMeasurable,
    integral_norm_eq_lintegral_eNorm hm.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_eNorm (b.integrable_scaled L j).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_eNorm hm.aestronglyMeasurable, b.eLpNorm_scaled_one]

/-- `∫ |Δ_v^L m_{2^j}| ≤ (2^j ‖v‖)^L ‖D^L m‖_1`, as real numbers. -/
theorem integral_norm_higherDiff_scaled_le (L j : ℕ) (v : W) :
    ∫ z, ‖(fwdDiff v)^[L] (b.scaled L j) z‖ ≤ (2 ^ j * ‖v‖) ^ L * (b.derivNorm L).toReal := by
  have hint := integrable_higherDiff (b.integrable_scaled L j) L v
  have hD : b.derivNorm L ≠ ∞ := lintegral_enorm_iteratedFDeriv_ne_top L _
  rw [integral_norm_eq_lintegral_eNorm hint.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_eNorm hint.aestronglyMeasurable]
  have h := b.eLpNorm_higherDiff_scaled_le L j v
  calc (eLpNorm ((fwdDiff v)^[L] (b.scaled L j)) 1 volume).toReal
      ≤ (ENNReal.ofReal (2 ^ j * ‖v‖) ^ L * b.derivNorm L).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hD) h
    _ = (2 ^ j * ‖v‖) ^ L * (b.derivNorm L).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

end LocalMeansBump

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V)

/-! ### The mollified graph -/

/-- The graph function on `H`, as a complex function. -/
noncomputable def graphFun (x' : Ω.hyperplane) : ℂ := (Ω.phi x' : ℂ)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The graph function is Lipschitz with constant `M` on `H`. -/
theorem norm_graphFun_sub_le (x' y' : Ω.hyperplane) :
    ‖Ω.graphFun x' - Ω.graphFun y'‖ ≤ Ω.M * ‖x' - y'‖ := by
  rw [graphFun, graphFun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h := Ω.lipschitz x' y'
  rwa [← Submodule.coe_sub, Submodule.norm_coe] at h

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The graph function is continuous. -/
theorem continuous_graphFun : Continuous Ω.graphFun :=
  Complex.continuous_ofReal.comp (Ω.continuous_phi.comp continuous_subtype_val)

/-- The mollifier on `H`: the centred bump of radius `1`. -/
noncomputable def graphBump : LocalMeansBump Ω.hyperplane := LocalMeansBump.centered one_pos

/-- The radius of the mollifier is `1`. -/
theorem graphBump_radius : Ω.graphBump.radius = 1 := rfl

/-- The `L_1` norm `‖ρ‖_1` of the mollifier `ρ`, the moment kernel of order `2`. -/
noncomputable def graphBumpNorm : ℝ := ∫ z, ‖momentKernel Ω.graphBump.toFun 2 z‖

/-- `‖ρ‖_1 ≥ 0`. -/
theorem graphBumpNorm_nonneg : 0 ≤ Ω.graphBumpNorm := integral_nonneg fun _ => norm_nonneg _

/-- The constant `‖D^2 ρ‖_1` of the second differences of the mollifier. -/
noncomputable def graphBumpDeriv : ℝ := (Ω.graphBump.derivNorm 2).toReal

/-- `‖D^2 ρ‖_1 ≥ 0`. -/
theorem graphBumpDeriv_nonneg : 0 ≤ Ω.graphBumpDeriv := ENNReal.toReal_nonneg

/-- The mollifier vanishes outside `closedBall(0, 2 · 2^(-j))`. -/
theorem graphBump_scaled_eq_zero (j : ℕ) (z : Ω.hyperplane) (hz : 2 / 2 ^ j < ‖z‖) :
    Ω.graphBump.scaled 2 j z = 0 :=
  Ω.graphBump.scaled_eq_zero_of_lt 2 j (by rw [graphBump_radius]; simpa using hz)

/-- The convolution integrals of the mollifiers with the graph function converge absolutely. -/
theorem integrable_graphBump_mul (j : ℕ) (v x : Ω.hyperplane) :
    Integrable (fun z => Ω.graphBump.scaled 2 j (z + v) * Ω.graphFun (x - z)) volume :=
  integrable_translate_mul_of_locallyIntegrable (Ω.graphBump.continuous_scaled 2 j)
    (Ω.graphBump.hasCompactSupport_scaled 2 j) Ω.continuous_graphFun.locallyIntegrable v x

/-- The **mollified graph** `φ_j = Re (ρ_{2^j} ⋆ φ)` on `H`. -/
noncomputable def smoothGraph (j : ℕ) (x' : Ω.hyperplane) : ℝ :=
  (conv (Ω.graphBump.scaled 2 j) Ω.graphFun volume x').re

/-- **The mollified graph is Lipschitz**: `|φ_j(x') - φ_j(y')| ≤ M ‖ρ‖_1 ‖x' - y'‖`. -/
theorem abs_smoothGraph_sub_le (j : ℕ) (x' y' : Ω.hyperplane) :
    |Ω.smoothGraph j x' - Ω.smoothGraph j y'| ≤ Ω.M * Ω.graphBumpNorm * ‖x' - y'‖ := by
  rw [smoothGraph, smoothGraph, ← Complex.sub_re, graphBumpNorm,
    ← Ω.graphBump.integral_norm_scaled 2 j]
  exact (Complex.abs_re_le_norm _).trans (norm_conv_sub_conv_le (Ω.graphBump.integrable_scaled 2 j)
    Ω.norm_graphFun_sub_le (fun x => by simpa using Ω.integrable_graphBump_mul j 0 x) x' y')

/-- **The mollified graph is close to the graph**: `|φ_j - φ| ≤ 2 M ‖ρ‖_1 2^(-j)`. -/
theorem abs_smoothGraph_sub_phi_le (j : ℕ) (x' : Ω.hyperplane) :
    |Ω.smoothGraph j x' - Ω.phi x'| ≤ 2 * Ω.M * Ω.graphBumpNorm / 2 ^ j := by
  have h1 : ∫ z, Ω.graphBump.scaled 2 j z = 1 := by
    rw [LocalMeansBump.scaled, integral_dilate _ (by positivity)]
    exact integral_momentKernel Ω.graphBump.integrable Ω.graphBump.integral_eq_one (by norm_num)
  have h := norm_conv_sub_self_le (Ω.graphBump.integrable_scaled 2 j) h1
    (Ω.graphBump_scaled_eq_zero j) Ω.M_nonneg Ω.norm_graphFun_sub_le
    (x := x') (by simpa using Ω.integrable_graphBump_mul j 0 x')
  rw [Ω.graphBump.integral_norm_scaled 2 j] at h
  have hre : Ω.smoothGraph j x' - Ω.phi x' =
      (conv (Ω.graphBump.scaled 2 j) Ω.graphFun volume x' - Ω.graphFun x').re := by
    rw [Complex.sub_re, smoothGraph, graphFun, Complex.ofReal_re]
  rw [hre]
  calc |(conv (Ω.graphBump.scaled 2 j) Ω.graphFun volume x' - Ω.graphFun x').re|
      ≤ Ω.M * (2 / 2 ^ j) * Ω.graphBumpNorm := (Complex.abs_re_le_norm _).trans h
    _ = 2 * Ω.M * Ω.graphBumpNorm / 2 ^ j := by ring

/-- **Second differences of the mollified graph**: for `‖h'‖ ≤ 2^(-j)`,
`|φ_j(x' + 2h') - 2 φ_j(x' + h') + φ_j(x')| ≤ 4 M ‖D^2 ρ‖_1 2^j ‖h'‖^2`. -/
theorem abs_second_smoothGraph_le (j : ℕ) {h' : Ω.hyperplane} (hh : ‖h'‖ ≤ 1 / 2 ^ j)
    (x' : Ω.hyperplane) :
    |Ω.smoothGraph j (x' + (2 : ℝ) • h') - 2 * Ω.smoothGraph j (x' + h') + Ω.smoothGraph j x'| ≤
      4 * Ω.M * Ω.graphBumpDeriv * 2 ^ j * ‖h'‖ ^ 2 := by
  have h := norm_higherDiff_two_conv_le (Ω.graphBump.integrable_scaled 2 j)
    (Ω.graphBump_scaled_eq_zero j) Ω.M_nonneg Ω.norm_graphFun_sub_le
    (Ω.integrable_graphBump_mul j) h' x'
  have hD := Ω.graphBump.integral_norm_higherDiff_scaled_le 2 j h'
  have hre : Ω.smoothGraph j (x' + (2 : ℝ) • h') - 2 * Ω.smoothGraph j (x' + h') +
      Ω.smoothGraph j x' = ((fwdDiff h')^[2] (conv (Ω.graphBump.scaled 2 j) Ω.graphFun volume)
        x').re := by
    rw [higherDiff_two_apply]
    simp [smoothGraph]
  rw [hre]
  have hR : 2 / 2 ^ j + 2 * ‖h'‖ ≤ 4 / 2 ^ j := by
    have h2 : 2 * ‖h'‖ ≤ 2 / 2 ^ j := by
      calc 2 * ‖h'‖ ≤ 2 * (1 / 2 ^ j) := by gcongr
        _ = 2 / 2 ^ j := by ring
    have h4 : (4 : ℝ) / 2 ^ j = 2 / 2 ^ j + 2 / 2 ^ j := by ring
    linarith
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  calc |((fwdDiff h')^[2] (conv (Ω.graphBump.scaled 2 j) Ω.graphFun volume) x').re|
      ≤ Ω.M * (2 / 2 ^ j + 2 * ‖h'‖) * ∫ z, ‖(fwdDiff h')^[2] (Ω.graphBump.scaled 2 j) z‖ :=
        (Complex.abs_re_le_norm _).trans h
    _ ≤ Ω.M * (4 / 2 ^ j) * ((2 ^ j * ‖h'‖) ^ 2 * Ω.graphBumpDeriv) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hR Ω.M_nonneg) hD
          (integral_nonneg fun _ => norm_nonneg _) (mul_nonneg Ω.M_nonneg (by positivity))
    _ = 4 * Ω.M * Ω.graphBumpDeriv * 2 ^ j * ‖h'‖ ^ 2 := by
        field_simp

/-- The mollified graph is continuous. -/
theorem continuous_smoothGraph (j : ℕ) : Continuous (Ω.smoothGraph j) := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨Ω.M * Ω.graphBumpNorm, mul_nonneg Ω.M_nonneg
    Ω.graphBumpNorm_nonneg⟩) fun x' y' => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact Ω.abs_smoothGraph_sub_le j x' y'

/-! ### The vertical cut-off -/

/-- The level `c = 2 M ‖ρ‖_1 + 1` of the profile, with `2^j |φ_j - φ| < c`. -/
noncomputable def cutoffLevel : ℝ := 2 * Ω.M * Ω.graphBumpNorm + 1

/-- The level of the profile is positive. -/
theorem cutoffLevel_pos : 0 < Ω.cutoffLevel := by
  have h := mul_nonneg (mul_nonneg zero_le_two Ω.M_nonneg) Ω.graphBumpNorm_nonneg
  rw [cutoffLevel]
  linarith

/-- The smooth bump of the profile: `1` on `[-c, c]`, `0` outside `(-(c + 1), c + 1)`. -/
noncomputable def profileBump : ContDiffBump (0 : ℝ) :=
  ⟨Ω.cutoffLevel, Ω.cutoffLevel + 1, Ω.cutoffLevel_pos, by linarith⟩

/-- The **profile** `χ` of the vertical cut-off. -/
noncomputable def profile (t : ℝ) : ℂ := ((Ω.profileBump t : ℝ) : ℂ)

/-- The profile is smooth. -/
theorem contDiff_profile : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ω.profile :=
  Complex.ofRealCLM.contDiff.comp Ω.profileBump.contDiff

/-- The profile has compact support. -/
theorem hasCompactSupport_profile : HasCompactSupport Ω.profile :=
  Ω.profileBump.hasCompactSupport.comp_left Complex.ofReal_zero

/-- `|χ| ≤ 1`. -/
theorem norm_profile_le (t : ℝ) : ‖Ω.profile t‖ ≤ 1 := by
  rw [profile, Complex.norm_real, Real.norm_of_nonneg Ω.profileBump.nonneg]
  exact Ω.profileBump.le_one

/-- `χ = 1` on `[-c, c]`. -/
theorem profile_eq_one {t : ℝ} (ht : |t| ≤ Ω.cutoffLevel) : Ω.profile t = 1 := by
  rw [profile, Ω.profileBump.one_of_mem_closedBall
    (by rwa [mem_closedBall, Real.dist_eq, sub_zero])]
  simp

/-- `χ = 0` outside `(-(c + 1), c + 1)`. -/
theorem profile_eq_zero {t : ℝ} (ht : Ω.cutoffLevel + 1 ≤ |t|) : Ω.profile t = 0 := by
  have h : t ∉ Function.support Ω.profileBump := by
    rw [Ω.profileBump.support_eq, mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact ht
  rw [profile, Function.notMem_support.1 h, Complex.ofReal_zero]

/-- The profile has bounded derivatives up to order `2`. -/
theorem exists_profile_bound :
    ∃ C : ℝ, ∀ l ≤ 2, ∀ t, ‖iteratedFDeriv ℝ l Ω.profile t‖ ≤ C :=
  exists_iteratedFDeriv_bound Ω.contDiff_profile Ω.hasCompactSupport_profile 2

/-- A bound `C` of the derivatives of the profile up to order `2`. -/
noncomputable def profileConst : ℝ := Classical.choose Ω.exists_profile_bound

/-- The derivatives of the profile up to order `2` are bounded by `C`. -/
theorem norm_iteratedFDeriv_profile_le {l : ℕ} (hl : l ≤ 2) (t : ℝ) :
    ‖iteratedFDeriv ℝ l Ω.profile t‖ ≤ Ω.profileConst :=
  Classical.choose_spec Ω.exists_profile_bound l hl t

/-- `C ≥ 0`. -/
theorem profileConst_nonneg : 0 ≤ Ω.profileConst :=
  (norm_nonneg _).trans (Ω.norm_iteratedFDeriv_profile_le (Nat.zero_le 2) 0)

/-- `|χ(b) - χ(a)| ≤ C |b - a|`. -/
theorem norm_profile_sub_le (a b : ℝ) : ‖Ω.profile b - Ω.profile a‖ ≤ Ω.profileConst * |b - a| := by
  have h := norm_higherDiff_le_of_iteratedFDeriv Ω.contDiff_profile (l := 1)
    (fun x => Ω.norm_iteratedFDeriv_profile_le (by norm_num) x) (b - a) a
  rwa [higherDiff_one_apply, add_sub_cancel, pow_one, Real.norm_eq_abs] at h

/-- `|χ(a + 2t) - 2 χ(a + t) + χ(a)| ≤ C t^2`. -/
theorem norm_profile_second_le (a t : ℝ) :
    ‖Ω.profile (a + 2 * t) - 2 * Ω.profile (a + t) + Ω.profile a‖ ≤ Ω.profileConst * t ^ 2 := by
  have h := norm_higherDiff_le_of_iteratedFDeriv Ω.contDiff_profile (l := 2)
    (fun x => Ω.norm_iteratedFDeriv_profile_le le_rfl x) t a
  rw [higherDiff_two_apply, Real.norm_eq_abs, sq_abs, smul_eq_mul] at h
  exact h

/-- The **vertical coordinate** `ψ_j(x) = 2^j (⟪x, e⟫ - φ_j(Px))`. -/
noncomputable def vertCoord (j : ℕ) (x : V) : ℝ :=
  2 ^ j * (inner ℝ x Ω.e - Ω.smoothGraph j (Ω.proj x))

/-- The **vertical cut-off** `v_j = χ ∘ ψ_j`. -/
noncomputable def vertCutoff (j : ℕ) (x : V) : ℂ := Ω.profile (Ω.vertCoord j x)

/-- The vertical coordinate is Lipschitz: `|ψ_j(x + h) - ψ_j(x)| ≤ 2^j (1 + M ‖ρ‖_1) ‖h‖`. -/
theorem abs_vertCoord_sub_le (j : ℕ) (x h : V) :
    |Ω.vertCoord j (x + h) - Ω.vertCoord j x| ≤ 2 ^ j * (1 + Ω.M * Ω.graphBumpNorm) * ‖h‖ := by
  have h1 : |inner ℝ (x + h) Ω.e - inner ℝ x Ω.e| ≤ ‖h‖ := by
    rw [inner_add_left, add_sub_cancel_left]
    exact (abs_real_inner_le_norm h Ω.e).trans (by rw [Ω.norm_e, mul_one])
  have h2 : |Ω.smoothGraph j (Ω.proj (x + h)) - Ω.smoothGraph j (Ω.proj x)| ≤
      Ω.M * Ω.graphBumpNorm * ‖h‖ := by
    refine (Ω.abs_smoothGraph_sub_le j _ _).trans ?_
    rw [map_add, add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left (Ω.norm_proj_le h)
      (mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg)
  have heq : Ω.vertCoord j (x + h) - Ω.vertCoord j x = 2 ^ j * ((inner ℝ (x + h) Ω.e -
      inner ℝ x Ω.e) - (Ω.smoothGraph j (Ω.proj (x + h)) - Ω.smoothGraph j (Ω.proj x))) := by
    simp only [vertCoord]
    ring
  rw [heq, abs_mul, abs_of_pos (by positivity)]
  calc 2 ^ j * |(inner ℝ (x + h) Ω.e - inner ℝ x Ω.e) -
        (Ω.smoothGraph j (Ω.proj (x + h)) - Ω.smoothGraph j (Ω.proj x))|
      ≤ 2 ^ j * (‖h‖ + Ω.M * Ω.graphBumpNorm * ‖h‖) :=
        mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (by positivity)
    _ = 2 ^ j * (1 + Ω.M * Ω.graphBumpNorm) * ‖h‖ := by ring

/-- **Second differences of the vertical coordinate**: for `‖h‖ ≤ 2^(-j)`,
`|ψ_j(x + 2h) - 2 ψ_j(x + h) + ψ_j(x)| ≤ 4 M ‖D^2 ρ‖_1 (2^j ‖h‖)^2`; the linear part `⟪x, e⟫` has
no second differences. -/
theorem abs_second_vertCoord_le (j : ℕ) {h : V} (hh : ‖h‖ ≤ 1 / 2 ^ j) (x : V) :
    |Ω.vertCoord j (x + (2 : ℝ) • h) - 2 * Ω.vertCoord j (x + h) + Ω.vertCoord j x| ≤
      4 * Ω.M * Ω.graphBumpDeriv * (2 ^ j * ‖h‖) ^ 2 := by
  have hP : ‖Ω.proj h‖ ≤ 1 / 2 ^ j := (Ω.norm_proj_le h).trans hh
  have h1 := Ω.abs_second_smoothGraph_le j hP (Ω.proj x)
  have heq : Ω.vertCoord j (x + (2 : ℝ) • h) - 2 * Ω.vertCoord j (x + h) + Ω.vertCoord j x =
      -(2 ^ j * (Ω.smoothGraph j (Ω.proj x + (2 : ℝ) • Ω.proj h) -
        2 * Ω.smoothGraph j (Ω.proj x + Ω.proj h) + Ω.smoothGraph j (Ω.proj x))) := by
    simp only [vertCoord, map_add, map_smul, inner_add_left, real_inner_smul_left]
    ring
  rw [heq, abs_neg, abs_mul, abs_of_pos (by positivity)]
  have hP2 : ‖Ω.proj h‖ ^ 2 ≤ ‖h‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (Ω.norm_proj_le h) 2
  have hc : 0 ≤ 4 * Ω.M * Ω.graphBumpDeriv * 2 ^ j :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Ω.M_nonneg) Ω.graphBumpDeriv_nonneg)
      (by positivity)
  calc 2 ^ j * |Ω.smoothGraph j (Ω.proj x + (2 : ℝ) • Ω.proj h) -
        2 * Ω.smoothGraph j (Ω.proj x + Ω.proj h) + Ω.smoothGraph j (Ω.proj x)|
      ≤ 2 ^ j * (4 * Ω.M * Ω.graphBumpDeriv * 2 ^ j * ‖Ω.proj h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 2 ^ j * (4 * Ω.M * Ω.graphBumpDeriv * 2 ^ j * ‖h‖ ^ 2) := by gcongr
    _ = 4 * Ω.M * Ω.graphBumpDeriv * (2 ^ j * ‖h‖) ^ 2 := by ring

/-- `|v_j| ≤ 1`. -/
theorem norm_vertCutoff_le (j : ℕ) (x : V) : ‖Ω.vertCutoff j x‖ ≤ 1 := Ω.norm_profile_le _

/-- **The vertical cut-off is `1` on the boundary**: `v_j(γ x') = 1`, since
`|ψ_j(γ x')| = 2^j |φ(x') - φ_j(x')| ≤ 2 M ‖ρ‖_1 < c`. -/
theorem vertCutoff_graphMap (j : ℕ) (x' : Ω.hyperplane) : Ω.vertCutoff j (Ω.graphMap x') = 1 := by
  apply Ω.profile_eq_one
  rw [vertCoord, Ω.inner_graphMap, Ω.proj_graphMap, abs_mul, abs_of_pos (by positivity),
    abs_sub_comm]
  have h := Ω.abs_smoothGraph_sub_phi_le j x'
  have hpos : (0 : ℝ) < 2 ^ j := by positivity
  calc 2 ^ j * |Ω.smoothGraph j x' - Ω.phi x'| ≤ 2 ^ j * (2 * Ω.M * Ω.graphBumpNorm / 2 ^ j) :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = 2 * Ω.M * Ω.graphBumpNorm := by field_simp
    _ ≤ Ω.cutoffLevel := by rw [cutoffLevel]; linarith

/-- **The vertical cut-off vanishes far from the smoothed graph**: `v_j(x) = 0` if
`|⟪x, e⟫ - φ_j(Px)| ≥ (c + 1) 2^(-j)`. -/
theorem vertCutoff_eq_zero (j : ℕ) {x : V}
    (hx : (Ω.cutoffLevel + 1) / 2 ^ j ≤ |inner ℝ x Ω.e - Ω.smoothGraph j (Ω.proj x)|) :
    Ω.vertCutoff j x = 0 := by
  apply Ω.profile_eq_zero
  rw [vertCoord, abs_mul, abs_of_pos (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hx
  linarith

/-- The vertical cut-off is continuous. -/
theorem continuous_vertCutoff (j : ℕ) : Continuous (Ω.vertCutoff j) :=
  Ω.contDiff_profile.continuous.comp (continuous_const.mul ((continuous_id.inner
    continuous_const).sub ((Ω.continuous_smoothGraph j).comp Ω.proj.continuous)))

/-- The constant `B` of the differences of the vertical cut-off. -/
noncomputable def vertCutoffConst : ℝ :=
  4 + Ω.profileConst * ((1 + Ω.M * Ω.graphBumpNorm) + 4 * Ω.M * Ω.graphBumpDeriv +
    (1 + Ω.M * Ω.graphBumpNorm) ^ 2)

/-- The constant of the vertical cut-off is at least `4`. -/
theorem four_le_vertCutoffConst : 4 ≤ Ω.vertCutoffConst := by
  have h1 : 0 ≤ Ω.M * Ω.graphBumpNorm := mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg
  have h2 : 0 ≤ 4 * Ω.M * Ω.graphBumpDeriv :=
    mul_nonneg (mul_nonneg (by norm_num) Ω.M_nonneg) Ω.graphBumpDeriv_nonneg
  have h3 : 0 ≤ Ω.profileConst * ((1 + Ω.M * Ω.graphBumpNorm) + 4 * Ω.M * Ω.graphBumpDeriv +
      (1 + Ω.M * Ω.graphBumpNorm) ^ 2) := mul_nonneg Ω.profileConst_nonneg (by positivity)
  rw [vertCutoffConst]
  linarith

/-- **First differences of the vertical cut-off**: `|v_j(x + h) - v_j(x)| ≤ B min(1, 2^j ‖h‖)`,
from the Lipschitz bounds of the profile and of the vertical coordinate. -/
theorem norm_vertCutoff_add_sub_le (j : ℕ) (h x : V) :
    ‖Ω.vertCutoff j (x + h) - Ω.vertCutoff j x‖ ≤ Ω.vertCutoffConst * min 1 (2 ^ j * ‖h‖) := by
  have hB := Ω.four_le_vertCutoffConst
  have hC := Ω.profileConst_nonneg
  have hMD : 0 ≤ 4 * Ω.M * Ω.graphBumpDeriv :=
    mul_nonneg (mul_nonneg (by norm_num) Ω.M_nonneg) Ω.graphBumpDeriv_nonneg
  set t := 2 ^ j * ‖h‖ with ht_def
  have ht : 0 ≤ t := by positivity
  rcases le_total t 1 with ht1 | ht1
  · rw [min_eq_right ht1]
    calc ‖Ω.vertCutoff j (x + h) - Ω.vertCutoff j x‖
        ≤ Ω.profileConst * |Ω.vertCoord j (x + h) - Ω.vertCoord j x| :=
          Ω.norm_profile_sub_le _ _
      _ ≤ Ω.profileConst * ((1 + Ω.M * Ω.graphBumpNorm) * t) := by
          refine mul_le_mul_of_nonneg_left ((Ω.abs_vertCoord_sub_le j x h).trans_eq ?_) hC
          rw [ht_def]
          ring
      _ ≤ Ω.vertCutoffConst * t := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ ht
          rw [vertCutoffConst]
          nlinarith [mul_nonneg hC hMD, mul_nonneg hC (sq_nonneg (1 + Ω.M * Ω.graphBumpNorm))]
  · rw [min_eq_left ht1, mul_one]
    calc ‖Ω.vertCutoff j (x + h) - Ω.vertCutoff j x‖
        ≤ ‖Ω.vertCutoff j (x + h)‖ + ‖Ω.vertCutoff j x‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Ω.norm_vertCutoff_le j _) (Ω.norm_vertCutoff_le j x)
      _ ≤ Ω.vertCutoffConst := by linarith

/-- **Second differences of the vertical cut-off**:
`|v_j(x + 2h) - 2 v_j(x + h) + v_j(x)| ≤ B min(1, (2^j ‖h‖)^2)`. For `t = ψ_1 - ψ_0` with
`ψ_l = ψ_j(x + lh)`, `Δ_h^2 v_j(x) = [χ(ψ_2) - χ(2ψ_1 - ψ_0)] + Δ_t^2 χ(ψ_0)`. -/
theorem norm_vertCutoff_second_le (j : ℕ) (h x : V) :
    ‖Ω.vertCutoff j (x + (2 : ℝ) • h) - 2 * Ω.vertCutoff j (x + h) + Ω.vertCutoff j x‖ ≤
      Ω.vertCutoffConst * min 1 ((2 ^ j * ‖h‖) ^ 2) := by
  have hB := Ω.four_le_vertCutoffConst
  have hC := Ω.profileConst_nonneg
  have hMK : 0 ≤ Ω.M * Ω.graphBumpNorm := mul_nonneg Ω.M_nonneg Ω.graphBumpNorm_nonneg
  have hMD : 0 ≤ 4 * Ω.M * Ω.graphBumpDeriv :=
    mul_nonneg (mul_nonneg (by norm_num) Ω.M_nonneg) Ω.graphBumpDeriv_nonneg
  set t := 2 ^ j * ‖h‖ with ht_def
  have ht : 0 ≤ t := by positivity
  rcases le_total t 1 with ht1 | ht1
  · rw [min_eq_right (pow_le_one₀ ht ht1)]
    have hh : ‖h‖ ≤ 1 / 2 ^ j := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact ht1
    set a₀ := Ω.vertCoord j x
    set a₁ := Ω.vertCoord j (x + h)
    set a₂ := Ω.vertCoord j (x + (2 : ℝ) • h)
    have hsplit : Ω.vertCutoff j (x + (2 : ℝ) • h) - 2 * Ω.vertCutoff j (x + h) +
        Ω.vertCutoff j x = (Ω.profile a₂ - Ω.profile (a₀ + 2 * (a₁ - a₀))) +
          (Ω.profile (a₀ + 2 * (a₁ - a₀)) - 2 * Ω.profile (a₀ + (a₁ - a₀)) +
            Ω.profile a₀) := by
      simp only [vertCutoff, a₀, a₁, a₂, add_sub_cancel]
      ring
    have hfirst : ‖Ω.profile a₂ - Ω.profile (a₀ + 2 * (a₁ - a₀))‖ ≤
        Ω.profileConst * (4 * Ω.M * Ω.graphBumpDeriv * t ^ 2) := by
      refine (Ω.norm_profile_sub_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have h2 := Ω.abs_second_vertCoord_le j hh x
      rw [show a₂ - (a₀ + 2 * (a₁ - a₀)) = a₂ - 2 * a₁ + a₀ by ring]
      exact h2
    have hsecond : ‖Ω.profile (a₀ + 2 * (a₁ - a₀)) - 2 * Ω.profile (a₀ + (a₁ - a₀)) +
        Ω.profile a₀‖ ≤ Ω.profileConst * ((1 + Ω.M * Ω.graphBumpNorm) ^ 2 * t ^ 2) := by
      refine (Ω.norm_profile_second_le a₀ (a₁ - a₀)).trans (mul_le_mul_of_nonneg_left ?_ hC)
      have h1 := Ω.abs_vertCoord_sub_le j x h
      rw [← sq_abs]
      calc |a₁ - a₀| ^ 2 ≤ (2 ^ j * (1 + Ω.M * Ω.graphBumpNorm) * ‖h‖) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (1 + Ω.M * Ω.graphBumpNorm) ^ 2 * t ^ 2 := by rw [ht_def]; ring
    rw [hsplit]
    calc ‖(Ω.profile a₂ - Ω.profile (a₀ + 2 * (a₁ - a₀))) +
          (Ω.profile (a₀ + 2 * (a₁ - a₀)) - 2 * Ω.profile (a₀ + (a₁ - a₀)) + Ω.profile a₀)‖
        ≤ Ω.profileConst * (4 * Ω.M * Ω.graphBumpDeriv * t ^ 2) +
            Ω.profileConst * ((1 + Ω.M * Ω.graphBumpNorm) ^ 2 * t ^ 2) :=
          (norm_add_le _ _).trans (add_le_add hfirst hsecond)
      _ ≤ Ω.vertCutoffConst * t ^ 2 := by
          rw [vertCutoffConst]
          nlinarith [mul_nonneg hC hMK, sq_nonneg t, mul_nonneg hC (sq_nonneg t),
            mul_nonneg (mul_nonneg hC (add_nonneg zero_le_one hMK)) (sq_nonneg t)]
  · rw [min_eq_left (one_le_pow₀ ht1), mul_one]
    calc ‖Ω.vertCutoff j (x + (2 : ℝ) • h) - 2 * Ω.vertCutoff j (x + h) + Ω.vertCutoff j x‖
        ≤ ‖Ω.vertCutoff j (x + (2 : ℝ) • h)‖ + ‖2 * Ω.vertCutoff j (x + h)‖ +
            ‖Ω.vertCutoff j x‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ 1 + 2 * 1 + 1 := by
          rw [norm_mul, Complex.norm_ofNat]
          gcongr
          · exact Ω.norm_vertCutoff_le j _
          · exact Ω.norm_vertCutoff_le j _
          · exact Ω.norm_vertCutoff_le j x
      _ ≤ Ω.vertCutoffConst := by linarith

/-- **Differences of the vertical cut-off**: `|Δ_h^m v_j| ≤ B min(1, (2^j ‖h‖)^m)` for
`m ≤ 2` (`Rd.LipschitzGraph.norm_vertCutoff_add_sub_le`,
`Rd.LipschitzGraph.norm_vertCutoff_second_le`). -/
theorem norm_higherDiff_vertCutoff_le (j : ℕ) {m : ℕ} (hm : m ≤ 2) (h x : V) :
    ‖(fwdDiff h)^[m] (Ω.vertCutoff j) x‖ ≤ Ω.vertCutoffConst * min 1 ((2 ^ j * ‖h‖) ^ m) := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl
  · rw [Function.iterate_zero, id, pow_zero, min_self, mul_one]
    exact (Ω.norm_vertCutoff_le j x).trans (by linarith [Ω.four_le_vertCutoffConst])
  · rw [higherDiff_one_apply, pow_one]
    exact Ω.norm_vertCutoff_add_sub_le j h x
  · rw [higherDiff_two_apply]
    exact Ω.norm_vertCutoff_second_le j h x

/-- The differences of the vertical cut-off in `ℝ≥0∞`. -/
theorem enorm_higherDiff_vertCutoff_le (j : ℕ) {m : ℕ} (hm : m ≤ 2) (h x : V) :
    ‖(fwdDiff h)^[m] (Ω.vertCutoff j) x‖ₑ ≤
      ENNReal.ofReal Ω.vertCutoffConst * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (m : ℝ)) := by
  have hB : 0 ≤ Ω.vertCutoffConst := by linarith [Ω.four_le_vertCutoffConst]
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (by positivity) (Nat.cast_nonneg m),
    Real.rpow_natCast, ← ENNReal.ofReal_one, ← ENNReal.ofReal_mono.map_min,
    ← ENNReal.ofReal_mul hB]
  exact ENNReal.ofReal_le_ofReal (Ω.norm_higherDiff_vertCutoff_le j hm h x)

end LipschitzGraph

end Rd
