/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.FeffermanStein
public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.VectorValuedSingularIntegrals
public import LeanPool.FunctionSpaces.Rd.Sobolev.DerivativeKernels

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Vector-valued singular integrals on the torus

Let `(θ_j)_{j ∈ ℕ}` be a Calderón–Zygmund family on `ℝ^d`, `d ≥ 1`, with overlap `B` and
Hörmander constant `H` (`Rd.IsCZFamily`), acting on the torus `𝕋^d` by
`(θ_j ⋆ f)(t) = ∫ θ_j(y) f(t - π y) dy` (`Torus.econv`). For `1 < p < ∞`, with the constant
`C = 3^{d/p} S_{d,p}(B, H) + D` (`Torus.periodicCZConst`), where `S_{d,p}(B, H)` is the strong
type constant on `ℝ^d` (`Rd.czConst`) and `D` bounds the **far mass**
`∫_{‖y‖ ≥ 1} ∑_j |θ_j(y)| dy` (`Torus.farMass`):

* **the analysis operator** (`Torus.eLpNorm_lqNorm_econv_le`):
  `‖ ‖((θ_j ⋆ f)(t))_j‖_{ℓ_2} ‖_{L_p(𝕋^d)} ≤ C ‖f‖_p` for every `f ∈ L_p(𝕋^d)`;
* **the synthesis operators** (`Torus.eLpNorm_sum_econv_le`):
  `‖∑_{j ∈ s} θ_j ⋆ g_j‖_{L_p(𝕋^d)} ≤ C ‖ ‖(g_j(t))_j‖_{ℓ_2} ‖_{L_p(𝕋^d)}` for every finite set
  `s` and all measurable `g_j ∈ L_p(𝕋^d)`.

The proof transfers the bounds of `ℝ^d` (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`,
`Rd.IsCZFamily.eLpNorm_sum_conv_le`) by localising the periodic lift, as for the
Fefferman–Stein inequality. At a point `x` of the period box `P_0 = (0, 1]^d`,
`(θ_j ⋆ f)(π x) = (θ_j ⋆ (f ∘ π))(x)`; the part of `f ∘ π` on the box `(-1, 2]^d` is a function
on `ℝ^d` with `L_p` norm `3^{d/p} ‖f‖_p` (`Torus.eLpNorm_indicator_tripleBox_comp_proj`), and the
rest is only seen by `θ_j` at points `‖y‖ ≥ 1` (`Torus.one_le_norm_of_sub_notMem_tripleBox`,
`Torus.enorm_econv_proj_sub_conv_le`). These far parts are bounded at every point by the
**far convolution** `∫_{‖y‖ ≥ 1} (∑_j |θ_j(y)|) G(t - π y) dy` (`Torus.farConv`), whose `L_p`
norm is at most the far mass times `‖G‖_p` by Young's inequality (`Torus.eLpNorm_farConv_le`).
For dilations `θ_j = (G_j)_{2^j}` of a uniform Schwartz family with bounds `A` the far mass is at
most `2 T_A`, with the tail constant `T_A = Rd.familyTailConst` (`Torus.farMass_dilate_le`); this
covers the blocks `ψ_j`, the synthesis kernels `psiDual_j` and the derivative families.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter
open scoped ENNReal TorusHaar SchwartzMap

open ENNReal (lqNorm)

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### The far mass -/

/-- The **far mass** `∫_{‖y‖ ≥ 1} ∑_j |θ_j(y)| dy` of a family of kernels on `ℝ^d`: the part of
the kernels that the localisation to the box `(-1, 2]^d` leaves over. -/
noncomputable def farMass (θ : ℕ → EuclideanSpace ℝ d → ℂ) : ℝ≥0∞ :=
  ∫⁻ y in {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖}, ∑' j, ‖θ j y‖ₑ

/-- **The far mass of a dilation family**: for a uniform Schwartz family `(G_j)_j` with bounds `A`,
the dilates `θ_j = (G_j)_{2^j}` have far mass at most `2 T_A`, with the tail constant
`T_A = Rd.familyTailConst (EuclideanSpace ℝ d) A 0 1`. Each dilate contributes at most
`T_A (1 + 2^j)⁻¹ ≤ T_A 2^{-j}` (`Rd.setLIntegral_enorm_dilate_schwartz_le`), and
`∑_j 2^{-j} = 2`. -/
theorem farMass_dilate_le {G : ℕ → 𝓢(EuclideanSpace ℝ d, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : Rd.IsUniformSchwartz G A) :
    farMass (fun j => Rd.dilate (2 ^ j) (G j)) ≤
      2 * Rd.familyTailConst (EuclideanSpace ℝ d) A 0 1 := by
  have hmeas : ∀ j, AEMeasurable (fun y => ‖Rd.dilate (2 ^ j) (G j : EuclideanSpace ℝ d → ℂ) y‖ₑ)
      (volume.restrict {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖}) := fun j =>
    (Rd.continuous_dilate (G j).continuous _).measurable.eNorm.aemeasurable
  rw [farMass, lintegral_tsum hmeas]
  calc ∑' j, ∫⁻ y in {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖},
        ‖Rd.dilate (2 ^ j) (G j : EuclideanSpace ℝ d → ℂ) y‖ₑ
      ≤ ∑' j : ℕ, Rd.familyTailConst (EuclideanSpace ℝ d) A 0 1 * (2⁻¹ : ℝ≥0∞) ^ j :=
        tsum_le_tsum fun j => (Rd.setLIntegral_enorm_dilate_schwartz_le (G j) 1 j 1).trans
          (mul_le_mul' (Rd.tailConst_le_familyTailConst h j 0 1)
            (Rd.inv_one_add_ofReal_two_pow_le j))
    _ = 2 * Rd.familyTailConst (EuclideanSpace ℝ d) A 0 1 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, mul_comm]

/-- The far mass of the Littlewood–Paley blocks `ψ_j = (psiBase j)_{2^j}` is at most `2 T_{A^ψ}`,
with the seminorm bounds `A^ψ = Rd.psiBaseBound`. -/
theorem farMass_psi_le :
    farMass (Rd.psi (V := EuclideanSpace ℝ d)) ≤
      2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.psiBaseBound (EuclideanSpace ℝ d)) 0 1 := by
  have h := farMass_dilate_le (Rd.isUniformSchwartz_psiBase (V := EuclideanSpace ℝ d))
  rwa [show (fun j => Rd.dilate (2 ^ j) (Rd.psiBase (V := EuclideanSpace ℝ d) j :
    EuclideanSpace ℝ d → ℂ)) = Rd.psi from funext Rd.dilate_psiBase] at h

/-- The far mass of the synthesis kernels `psiDual_j = (psiDualBase j)_{2^j}` is at most
`2 T_{Ã}`, with the seminorm bounds `Ã = Rd.psiDualBaseBound`. -/
theorem farMass_psiDual_le :
    farMass (Rd.psiDual (V := EuclideanSpace ℝ d)) ≤
      2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.psiDualBaseBound (EuclideanSpace ℝ d))
        0 1 := by
  have h := farMass_dilate_le (Rd.isUniformSchwartz_psiDualBase (V := EuclideanSpace ℝ d))
  rwa [show (fun j => Rd.dilate (2 ^ j) (Rd.psiDualBase (V := EuclideanSpace ℝ d) j :
    EuclideanSpace ℝ d → ℂ)) = Rd.psiDual from funext Rd.dilate_psiDualBase] at h

/-- The far mass of the derivative family `j ↦ (η_i)_{2^j}` of a multi-index `i` is at most
`2 T_{A^{η_i}}`, with the seminorm bounds `A^{η_i} = Rd.derivKernelBound i`. -/
theorem farMass_derivFamily_le {m : ℕ} (i : Fin m → Fin (Module.finrank ℝ (EuclideanSpace ℝ d))) :
    farMass (Rd.derivFamily i) ≤
      2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.derivKernelBound i) 0 1 :=
  farMass_dilate_le (Rd.isUniformSchwartz_derivKernel i)

/-- The far mass of the dual derivative family `j ↦ (∂^w psiDualBase_j)_{2^j}` of directions
`w ∈ (ℝ^d)^k` is at most `2 T_{A^w}`, with the seminorm bounds `A^w = Rd.derivDualBound w`. -/
theorem farMass_derivDualFamily_le {k : ℕ} (w : Fin k → EuclideanSpace ℝ d) :
    farMass (Rd.derivDualFamily w) ≤
      2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.derivDualBound w) 0 1 :=
  farMass_dilate_le (Rd.isUniformSchwartz_derivDualBase w)

/-! ### The far convolution -/

/-- The **far convolution** `t ↦ ∫_{‖y‖ ≥ 1} (∑_j |θ_j(y)|) G(t - π y) dy` of `G : 𝕋^d → [0, ∞]`
with the far parts of a family of kernels on `ℝ^d`; it bounds the far parts of the convolutions
`θ_j ⋆ g_j` at every point. -/
noncomputable def farConv (θ : ℕ → EuclideanSpace ℝ d → ℂ) (G : UnitAddTorus d → ℝ≥0∞)
    (t : UnitAddTorus d) : ℝ≥0∞ :=
  ∫⁻ y in {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖}, (∑' j, ‖θ j y‖ₑ) * G (t - proj y)

/-- The kernel `y ↦ ∑_j |θ_j(y)|` of the far parts is almost everywhere measurable for every
measure `ν` below the Lebesgue measure, such as its restriction to `{‖y‖ ≥ 1}`. -/
theorem aemeasurable_tsum_enorm {θ : ℕ → EuclideanSpace ℝ d → ℂ}
    (hθ : ∀ j, AEStronglyMeasurable (θ j) volume) (ν : Measure (EuclideanSpace ℝ d))
    (hν : ν ≤ volume) : AEMeasurable (fun y => ∑' j, ‖θ j y‖ₑ) ν :=
  AEMeasurable.tsum fun j => ((hθ j).mono_measure hν).eNorm

/-- **Young's inequality for kernels on `ℝ^d` acting on the torus**, for nonnegative functions:
for `1 ≤ q`, an s-finite measure `ν` on `ℝ^d`, an almost everywhere measurable
`a : ℝ^d → [0, ∞]` and a measurable `G : 𝕋^d → [0, ∞]`,
`∫_{𝕋^d} (∫ a(y) G(t - π y) dν(y))^q dt ≤ (∫ a dν)^q ∫_{𝕋^d} G^q`. This is the torus form of
`MeasureTheory.lintegral_rpow_lintegral_mul_le`: the kernel form
`MeasureTheory.lintegral_rpow_lintegral_kernel_le` for `K(t, y) = G(t - π y)`, with
`∫_{𝕋^d} G(t - π y)^q dt = ∫_{𝕋^d} G^q` by the translation invariance of the Haar measure. -/
theorem lintegral_rpow_lintegral_mul_comp_sub_proj_le {ν : Measure (EuclideanSpace ℝ d)}
    [SFinite ν] {q : ℝ} (hq1 : 1 ≤ q) {a : EuclideanSpace ℝ d → ℝ≥0∞} (ha : AEMeasurable a ν)
    {G : UnitAddTorus d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t, (∫⁻ y, a y * G (t - proj y) ∂ν) ^ q ≤ (∫⁻ y, a y ∂ν) ^ q * ∫⁻ t, G t ^ q :=
  lintegral_rpow_lintegral_kernel_le hq1 ha (K := fun t y => G (t - proj y))
    (hG.comp (measurable_fst.sub (measurable_proj.comp measurable_snd))).aemeasurable
    fun y => (lintegral_sub_right_eq_self (fun t => G t ^ q) (proj y)).le

/-- For almost everywhere strongly measurable kernels `θ_j` and measurable `G`, the far
convolution `Torus.farConv θ G` is almost everywhere measurable. -/
theorem aemeasurable_farConv {θ : ℕ → EuclideanSpace ℝ d → ℂ}
    (hθ : ∀ j, AEStronglyMeasurable (θ j) volume) {G : UnitAddTorus d → ℝ≥0∞} (hG : Measurable G) :
    AEMeasurable (farConv θ G) volume := by
  have hprod : AEMeasurable (Function.uncurry fun (t : UnitAddTorus d) y =>
      (∑' j, ‖θ j y‖ₑ) * G (t - proj y))
      (volume.prod (volume.restrict {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖})) :=
    (aemeasurable_tsum_enorm hθ _ Measure.restrict_le_self).comp_snd.mul
      (hG.comp (measurable_fst.sub (measurable_proj.comp measurable_snd))).aemeasurable
  exact hprod.lintegral_prod_right'

/-- **Young's inequality for the far convolution**: for almost everywhere strongly measurable
kernels `θ_j`, `1 ≤ p < ∞` and measurable `G : 𝕋^d → [0, ∞]`,
`‖t ↦ ∫_{‖y‖ ≥ 1} (∑_j |θ_j(y)|) G(t - π y) dy‖_p ≤ M_θ ‖G‖_p` with the far mass
`M_θ = Torus.farMass θ`. -/
theorem eLpNorm_farConv_le {θ : ℕ → EuclideanSpace ℝ d → ℂ}
    (hθ : ∀ j, AEStronglyMeasurable (θ j) volume) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {G : UnitAddTorus d → ℝ≥0∞} (hG : Measurable G) :
    eLpNorm (farConv θ G) p volume ≤ farMass θ * eLpNorm G p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  refine eLpNorm_le_of_lintegral_le (aemeasurable_farConv hθ hG).aestronglyMeasurable hp0 hp ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), eLpNorm_rpow_eq_lintegral hp0 hp
    hG.aemeasurable]
  simp only [eNorm_eq_self]
  exact lintegral_rpow_lintegral_mul_comp_sub_proj_le hq1
    (aemeasurable_tsum_enorm hθ _ Measure.restrict_le_self) hG

/-- **The far parts as a far convolution**: `∑_j ∫_{‖y‖ ≥ 1} |θ_j(y)| G(t - π y) dy` is the far
convolution of `G`, by monotone convergence. -/
theorem tsum_setLIntegral_eq_farConv {θ : ℕ → EuclideanSpace ℝ d → ℂ}
    (hθ : ∀ j, AEStronglyMeasurable (θ j) volume) {G : UnitAddTorus d → ℝ≥0∞} (hG : Measurable G)
    (t : UnitAddTorus d) :
    ∑' j, ∫⁻ y in {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖}, ‖θ j y‖ₑ * G (t - proj y) =
      farConv θ G t := by
  rw [farConv, ← lintegral_tsum (f := fun j y => ‖θ j y‖ₑ * G (t - proj y)) fun j =>
    (hθ j).restrict.eNorm.mul (hG.comp (measurable_const.sub measurable_proj)).aemeasurable]
  exact lintegral_congr fun y => ENNReal.tsum_mul_right

/-! ### Pointwise localisation -/

/-- **Localisation of a convolution**: at `x ∈ P_0 = (0, 1]^d`, if the convolution integral of
`θ` and `f` converges absolutely at `π x`, then
`|(θ ⋆ f)(π x) - (θ ⋆ 1_{(-1,2]^d} (f ∘ π))(x)| ≤ ∫_{‖y‖ ≥ 1} |θ(y)| |f(π x - π y)| dy`, with
the convolution on `ℝ^d` in the second term. The difference is the integral over the `y` with
`x - y ∉ (-1, 2]^d`, and these have `‖y‖ ≥ 1`. -/
theorem enorm_econv_proj_sub_conv_le {θ : EuclideanSpace ℝ d → ℂ} {f : UnitAddTorus d → ℂ}
    {x : EuclideanSpace ℝ d} (hx : x ∈ periodBox 0)
    (hint : Integrable fun y => θ y * f (proj x - proj y)) :
    ‖econv θ f (proj x) - Rd.conv θ (tripleBox.indicator (f ∘ proj)) volume x‖ₑ ≤
      ∫⁻ y in {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖}, ‖θ y‖ₑ * ‖f (proj x - proj y)‖ₑ := by
  set S : Set (EuclideanSpace ℝ d) := {y | x - y ∈ tripleBox}
  have hS : MeasurableSet S :=
    measurableSet_tripleBox.preimage (measurable_const.sub measurable_id)
  have hconv : Rd.conv θ (tripleBox.indicator (f ∘ proj)) volume x =
      ∫ y in S, θ y * f (proj x - proj y) := by
    rw [Rd.conv_apply, ← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    by_cases hy : x - y ∈ tripleBox
    · rw [indicator_of_mem hy, indicator_of_mem (show y ∈ S from hy), Function.comp_apply,
        map_sub]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show y ∉ S from hy), mul_zero]
  have hsplit := integral_add_compl hS hint
  rw [hconv, show econv θ f (proj x) = ∫ y, θ y * f (proj x - proj y) from rfl, ← hsplit,
    add_sub_cancel_left]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
  simp only [eNorm_mul]
  exact lintegral_mono_set fun y hy => one_le_norm_of_sub_notMem_tripleBox hx hy

/-- **The convolution integrals of lifts converge absolutely**: for integrable kernels `θ_j` and
measurable `g_j ∈ L_1(𝕋^d)`, for almost every `x ∈ ℝ^d` and every `j` the integral
`∫ θ_j(y) g_j(π x - π y) dy` converges absolutely (`Torus.ae_integrable_econv`, lifted by
`Torus.ae_comp_proj`). -/
theorem ae_integrable_econv_proj {θ : ℕ → EuclideanSpace ℝ d → ℂ} (hθ : ∀ j, Integrable (θ j))
    {g : ℕ → UnitAddTorus d → ℂ} (hg : ∀ j, Measurable (g j)) (hgi : ∀ j, Integrable (g j)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), ∀ j,
      Integrable fun y => θ j y * g j (proj x - proj y) :=
  ae_all_iff.2 fun j => ae_comp_proj (ae_integrable_econv (hθ j) (hg j) (hgi j))

/-- **Localisation of the analysis operator**: at `x ∈ P_0` where all convolution integrals
converge absolutely,
`‖((θ_j ⋆ f)(π x))_j‖_{ℓ_2} ≤ ‖((θ_j ⋆ 1_{(-1,2]^d} (f ∘ π))(x))_j‖_{ℓ_2} + F(π x)` with the far
convolution `F` of `|f|` (`Torus.farConv`): the triangle inequality in `ℓ_2`, and
`‖·‖_{ℓ_2} ≤ ‖·‖_{ℓ_1}` for the far parts. -/
theorem lqNorm_econv_proj_le {θ : ℕ → EuclideanSpace ℝ d → ℂ}
    (hθ : ∀ j, AEStronglyMeasurable (θ j) volume) {f : UnitAddTorus d → ℂ} (hf : Measurable f)
    {x : EuclideanSpace ℝ d} (hx : x ∈ periodBox 0)
    (hint : ∀ j, Integrable fun y => θ j y * f (proj x - proj y)) :
    lqNorm 2 (fun j => ‖econv (θ j) f (proj x)‖ₑ) ≤
      lqNorm 2 (fun j => ‖Rd.conv (θ j) (tripleBox.indicator (f ∘ proj)) volume x‖ₑ) +
        farConv θ (fun t => ‖f t‖ₑ) (proj x) := by
  have hj : ∀ j, ‖econv (θ j) f (proj x)‖ₑ ≤
      ‖Rd.conv (θ j) (tripleBox.indicator (f ∘ proj)) volume x‖ₑ +
        ∫⁻ y in {y : EuclideanSpace ℝ d | 1 ≤ ‖y‖}, ‖θ j y‖ₑ * ‖f (proj x - proj y)‖ₑ := by
    intro j
    calc ‖econv (θ j) f (proj x)‖ₑ
        = ‖Rd.conv (θ j) (tripleBox.indicator (f ∘ proj)) volume x +
            (econv (θ j) f (proj x) -
              Rd.conv (θ j) (tripleBox.indicator (f ∘ proj)) volume x)‖ₑ := by
          rw [add_sub_cancel]
      _ ≤ _ := (eNorm_add_le _ _).trans
          (add_le_add le_rfl (enorm_econv_proj_sub_conv_le hx (hint j)))
  refine (ENNReal.lqNorm_mono hj).trans ((ENNReal.lqNorm_add_le one_le_two _ _).trans ?_)
  refine add_le_add le_rfl ((ENNReal.lqNorm_le_lqNorm_one one_le_two _).trans_eq ?_)
  exact tsum_setLIntegral_eq_farConv hθ hf.eNorm (proj x)

/-- **Localisation of the synthesis operators**: at `x ∈ P_0` where all convolution integrals
converge absolutely, for every finite set `s`,
`|∑_{j ∈ s} (θ_j ⋆ g_j)(π x)| ≤ |∑_{j ∈ s} (θ_j ⋆ 1_{(-1,2]^d} (g_j ∘ π))(x)| + F(π x)` with the
far convolution `F` of `G(t) = ‖(g_j(t))_j‖_{ℓ_2}` (`Torus.farConv`), since `|g_j| ≤ G`. -/
theorem enorm_sum_econv_proj_le {θ : ℕ → EuclideanSpace ℝ d → ℂ}
    (hθ : ∀ j, AEStronglyMeasurable (θ j) volume) {g : ℕ → UnitAddTorus d → ℂ}
    (hg : ∀ j, Measurable (g j)) (s : Finset ℕ) {x : EuclideanSpace ℝ d} (hx : x ∈ periodBox 0)
    (hint : ∀ j, Integrable fun y => θ j y * g j (proj x - proj y)) :
    ‖∑ j ∈ s, econv (θ j) (g j) (proj x)‖ₑ ≤
      ‖∑ j ∈ s, Rd.conv (θ j) (tripleBox.indicator (g j ∘ proj)) volume x‖ₑ +
        farConv θ (fun t => lqNorm 2 fun j => ‖g j t‖ₑ) (proj x) := by
  set c : ℕ → ℂ := fun j => Rd.conv (θ j) (tripleBox.indicator (g j ∘ proj)) volume x
  have hG : Measurable fun t => lqNorm 2 fun j => ‖g j t‖ₑ :=
    measurable_lqNorm_comp (fun j => (hg j).eNorm) 2
  have hfar : ∑ j ∈ s, ‖econv (θ j) (g j) (proj x) - c j‖ₑ ≤
      farConv θ (fun t => lqNorm 2 fun j => ‖g j t‖ₑ) (proj x) := by
    rw [← tsum_setLIntegral_eq_farConv hθ hG]
    refine (Finset.sum_le_sum fun j _ => (enorm_econv_proj_sub_conv_le hx (hint j)).trans
      (lintegral_mono fun y => mul_le_mul_right ?_ _)).trans (sum_le_tsum s)
    exact ENNReal.le_lqNorm two_ne_zero (fun i => ‖g i (proj x - proj y)‖ₑ) j
  calc ‖∑ j ∈ s, econv (θ j) (g j) (proj x)‖ₑ
      = ‖∑ j ∈ s, c j + ∑ j ∈ s, (econv (θ j) (g j) (proj x) - c j)‖ₑ := by
        rw [← Finset.sum_add_distrib]
        simp only [add_sub_cancel]
    _ ≤ ‖∑ j ∈ s, c j‖ₑ + ∑ j ∈ s, ‖econv (θ j) (g j) (proj x) - c j‖ₑ :=
        (eNorm_add_le _ _).trans (add_le_add le_rfl (eNorm_sum_le _ _))
    _ ≤ _ := add_le_add le_rfl hfar

/-! ### The two bounds -/

variable (d) in
/-- The constant `3^{d/p} S_{d,p}(B, H) + D` of the vector-valued singular integrals on the
torus, with the strong type constant `S_{d,p}(B, H) = Rd.czConst` of `ℝ^d` and a bound `D` of the
far mass. -/
noncomputable def periodicCZConst (p B H D : ℝ≥0∞) : ℝ≥0∞ :=
  3 ^ ((Fintype.card d : ℝ) / p.toReal) * Rd.czConst (EuclideanSpace ℝ d) p B H + D

/-- The constant `Torus.periodicCZConst d p B H D` is finite for `1 < p < ∞` and finite `B`,
`H`, `D`. -/
theorem periodicCZConst_ne_top {p B H D : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hB : B ≠ ∞)
    (hH : H ≠ ∞) (hD : D ≠ ∞) : periodicCZConst d p B H D ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))
    (Rd.czConst_ne_top hp1 hp hB hH), hD⟩

/-- **The strong type of the analysis operator on the torus**: for `d ≥ 1`, a Calderón–Zygmund
family `(θ_j)_j` on `ℝ^d` with overlap `B`, Hörmander constant `H` and far mass at most `D`,
every `1 < p < ∞` and every `f ∈ L_p(𝕋^d)`,
`‖ ‖((θ_j ⋆ f)(t))_j‖_{ℓ_2} ‖_{L_p(𝕋^d)} ≤ C ‖f‖_p` with `C = Torus.periodicCZConst d p B H D`.
The lift splits into the part on `(-1, 2]^d`, bounded by the strong type on `ℝ^d`, and the far
part, bounded by Young's inequality for the far convolution. -/
theorem eLpNorm_lqNorm_econv_le [Nonempty d] {θ : ℕ → EuclideanSpace ℝ d → ℂ} {B H D : ℝ≥0∞}
    (h : Rd.IsCZFamily θ B H) (hD : farMass θ ≤ D) {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    eLpNorm (fun t => lqNorm 2 fun j => ‖econv (θ j) f t‖ₑ) p volume ≤
      periodicCZConst d p B H D * ‖f‖ₑ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hθ : ∀ j, AEStronglyMeasurable (θ j) volume := fun j => (h.integrable j).1
  have hfm : Measurable f := (Lp.stronglyMeasurable f).measurable
  have hF : AEMeasurable (fun t => lqNorm 2 fun j => ‖econv (θ j) f t‖ₑ) volume :=
    aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_econv (hθ j) hfm).eNorm) 2
  have hsplit := eLpNorm_le_of_comp_proj_le hp1.le hF (aemeasurable_farConv hθ hfm.eNorm)
    (A := fun x => lqNorm 2 fun j => ‖Rd.conv (θ j) (tripleBox.indicator (f ∘ proj)) volume x‖ₑ)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_periodBox 0), ae_restrict_of_ae
        (ae_integrable_econv_proj (g := fun _ => f) h.integrable (fun _ => hfm)
          fun _ => (Lp.memLp f).integrable hp1.le)]
        with x hx hint
      exact lqNorm_econv_proj_le hθ hfm hx hint)
  have hnear := h.eLpNorm_lqNorm_conv_le hp1 hp
    (memLp_indicator_tripleBox_comp_proj hp0 hp (Lp.memLp f))
  rw [eLpNorm_indicator_tripleBox_comp_proj hp0 hp (Lp.aestronglyMeasurable f)] at hnear
  refine hsplit.trans ?_
  rw [Lp.eNorm_def, periodicCZConst, add_mul]
  refine add_le_add (hnear.trans_eq (by ring)) ?_
  refine (eLpNorm_farConv_le hθ hp1.le hp hfm.eNorm).trans ?_
  rw [eLpNorm_eNorm _ (Lp.aestronglyMeasurable f)]
  gcongr

/-- **The strong type of the synthesis operators on the torus**: for `d ≥ 1`, a
Calderón–Zygmund family `(θ_j)_j` on `ℝ^d` with overlap `B`, Hörmander constant `H` and far mass
at most `D`, every `1 < p < ∞`, every finite set `s` and all measurable `g_j ∈ L_p(𝕋^d)`,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_{L_p(𝕋^d)} ≤ C ‖ ‖(g_j(t))_j‖_{ℓ_2} ‖_{L_p(𝕋^d)}` with
`C = Torus.periodicCZConst d p B H D`. -/
theorem eLpNorm_sum_econv_le [Nonempty d] {θ : ℕ → EuclideanSpace ℝ d → ℂ} {B H D : ℝ≥0∞}
    (h : Rd.IsCZFamily θ B H) (hD : farMass θ ≤ D) {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞)
    (s : Finset ℕ) {g : ℕ → UnitAddTorus d → ℂ} (hgm : ∀ j, Measurable (g j))
    (hg : ∀ j, MemLp (g j) p volume) :
    eLpNorm (fun t => ∑ j ∈ s, econv (θ j) (g j) t) p volume ≤
      periodicCZConst d p B H D * eLpNorm (fun t => lqNorm 2 fun j => ‖g j t‖ₑ) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hθ : ∀ j, AEStronglyMeasurable (θ j) volume := fun j => (h.integrable j).1
  have hG : Measurable fun t => lqNorm 2 fun j => ‖g j t‖ₑ :=
    measurable_lqNorm_comp (fun j => (hgm j).eNorm) 2
  have hsum : AEStronglyMeasurable (fun t => ∑ j ∈ s, econv (θ j) (g j) t) volume :=
    Finset.aestronglyMeasurable_fun_sum s fun j _ => aestronglyMeasurable_econv (hθ j) (hgm j)
  have hsplit := eLpNorm_le_of_comp_proj_le hp1.le hsum.eNorm (aemeasurable_farConv hθ hG)
    (A := fun x => ‖∑ j ∈ s, Rd.conv (θ j) (tripleBox.indicator (g j ∘ proj)) volume x‖ₑ)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_periodBox 0), ae_restrict_of_ae
        (ae_integrable_econv_proj h.integrable hgm fun j => (hg j).integrable hp1.le)]
        with x hx hint
      exact enorm_sum_econv_proj_le hθ hgm s hx hint)
  rw [eLpNorm_eNorm _ hsum, eLpNorm_eNorm _ (Finset.aestronglyMeasurable_fun_sum s fun j _ =>
    Rd.aestronglyMeasurable_conv (hθ j)
      (memLp_indicator_tripleBox_comp_proj hp0 hp (hg j)).aestronglyMeasurable)] at hsplit
  have hnear := h.eLpNorm_sum_conv_le hp1 hp s fun j =>
    memLp_indicator_tripleBox_comp_proj hp0 hp (hg j)
  have hfun : (fun x => lqNorm 2 fun j => ‖tripleBox.indicator (g j ∘ proj) x‖ₑ) =
      tripleBox.indicator fun y => lqNorm 2 fun j => ‖g j (proj y)‖ₑ := funext fun x => by
    simp only [eNorm_indicator_eq_indicator_eNorm]
    exact ENNReal.lqNorm_indicator 2 _ (fun j y => ‖(g j ∘ proj) y‖ₑ) x
  rw [hfun, eLpNorm_indicator_tripleBox hp0 hp hG.aemeasurable] at hnear
  refine hsplit.trans ?_
  rw [periodicCZConst, add_mul]
  exact add_le_add (hnear.trans_eq (by ring))
    ((eLpNorm_farConv_le hθ hp1.le hp hG).trans (by gcongr))

end Torus
