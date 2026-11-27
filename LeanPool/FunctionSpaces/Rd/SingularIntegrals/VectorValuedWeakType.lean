/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Maximal.CalderonZygmundSigned
public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.PlancherelBounds
public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The weak type `(1,1)` of vector-valued singular integrals

Let `V` have dimension `n ≥ 1` and let `(θ_j)_{j ∈ ℕ}` be a Calderón–Zygmund family with Fourier
overlap `B` and Hörmander constant `H` (`Rd.IsCZFamily`). With
`C = Rd.vectorWeakConst V B H = 4 · 2^n B + (2n)^n |B(0, 1)| + 4H`, for every `0 < t < ∞`:

* **the analysis operator** (`Rd.IsCZFamily.volume_lqNorm_conv_gt_le`): for integrable `f`,
  `|{x : ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} > t}| ≤ C t⁻¹ ∫ |f|`;
* **the synthesis operators** (`Rd.IsCZFamily.volume_enorm_sum_conv_gt_le`): for every finite
  set `s` and almost everywhere strongly measurable `g_j` with `G = ‖(g_j)_j‖_{ℓ_2}` and
  `∫ G < ∞`, `|{x : |∑_{j ∈ s} (θ_j ⋆ g_j)(x)| > t}| ≤ C t⁻¹ ∫ G`.

The proof splits `f` (resp. every `g_j`) by the signed Calderón–Zygmund decomposition of `|f|`
(resp. of `G`) at height `t`. The good part is handled by the Plancherel bounds and Chebyshev's
inequality. The bad pieces `b_Q` have mean zero on their cubes `Q` with centres `c_Q`, so
`(θ_j ⋆ b_Q)(x) = ∫_Q (θ_j(x - y) - θ_j(x - c_Q)) b_Q(y) dy`
(`Rd.IsCZFamily.lqNorm_conv_le_setLIntegral`, `Rd.IsCZFamily.enorm_sum_conv_le_setLIntegral`),
and off the enlarged exceptional set `Ω*` the Hörmander condition integrates these kernels
(`Rd.IsCZFamily.setLIntegral_compl_czEnlarged_tsum_le`). The general bookkeeping of the level
sets is `MeasureTheory.measure_lt_le_of_ae_le_add` of `FunctionSpaces.Analysis.Lp.Marcinkiewicz`.
-/

@[expose] public section

open MeasureTheory Module Metric Set Filter
open scoped ENNReal
open ENNReal (lqNorm)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {θ : ℕ → V → ℂ} {B H : ℝ≥0∞} {G : V → ℝ≥0∞} {t : ℝ≥0∞}

/-! ### The Hörmander condition around a cube -/

/-- **The Hörmander condition around a centre**: for a Calderón–Zygmund family with Hörmander
constant `H`, a centre `c`, a radius `ρ` and a point `y` with `‖y - c‖ ≤ ρ`,
`∫_{‖x - c‖ > 2ρ} ‖(θ_j(x - y) - θ_j(x - c))_j‖_{ℓ_2} dx ≤ H`. The translation `x ↦ x - c`
(Mathlib's `measurePreserving_sub_right`) turns the integral into the Hörmander integral at
`y - c` over a smaller set. -/
theorem IsCZFamily.setLIntegral_compl_closedBall_le (h : IsCZFamily θ B H) {c y : V} {ρ : ℝ}
    (hy : ‖y - c‖ ≤ ρ) :
    ∫⁻ x in (closedBall c (2 * ρ))ᶜ, lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) ≤ H := by
  have hsub : (closedBall c (2 * ρ))ᶜ ⊆ (fun x => x - c) ⁻¹' {x' : V | 2 * ‖y - c‖ < ‖x'‖} := by
    intro x hx
    simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hx
    change 2 * ‖y - c‖ < ‖x - c‖
    linarith
  calc ∫⁻ x in (closedBall c (2 * ρ))ᶜ, lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ)
      ≤ ∫⁻ x in (fun x => x - c) ⁻¹' {x' : V | 2 * ‖y - c‖ < ‖x'‖},
          lqNorm 2 (fun j => ‖θ j (x - c - (y - c)) - θ j (x - c)‖ₑ) := by
        simp only [sub_sub_sub_cancel_right]
        exact lintegral_mono_set hsub
    _ = ∫⁻ x' in {x' : V | 2 * ‖y - c‖ < ‖x'‖},
          lqNorm 2 (fun j => ‖θ j (x' - (y - c)) - θ j x'‖ₑ) :=
        (measurePreserving_sub_right volume c).setLIntegral_comp_preimage_emb
          (measurableEmbedding_subRight c) (fun x' =>
            lqNorm 2 (fun j => ‖θ j (x' - (y - c)) - θ j x'‖ₑ)) _
    _ ≤ H := h.hormander (y - c)

/-- The kernel `(x, y) ↦ ‖(θ_j(x - y) - θ_j(x - c))_j‖_{ℓ_2}` of a Calderón–Zygmund family is
measurable on `V × V`, since every `θ_j` is continuous. -/
theorem IsCZFamily.measurable_lqNorm_sub (h : IsCZFamily θ B H) (c : V) :
    Measurable fun p : V × V => lqNorm 2 (fun j => ‖θ j (p.1 - p.2) - θ j (p.1 - c)‖ₑ) :=
  measurable_lqNorm_comp (fun j => (((h.continuous j).comp (continuous_fst.sub continuous_snd)).sub
    ((h.continuous j).comp (continuous_fst.sub continuous_const))).measurable.eNorm) 2

/-- **The bad part off the doubled ball** (scalar mass): for a Calderón–Zygmund family with
Hörmander constant `H`, a measurable set `Q ⊆ closedBall(c, ρ)` and an almost everywhere
measurable mass
`m : V → [0, ∞]`,
`∫_{‖x - c‖ > 2ρ} ∫_Q ‖(θ_j(x - y) - θ_j(x - c))_j‖_{ℓ_2} m(y) dy dx ≤ H ∫_Q m`, by Tonelli's
theorem (Mathlib's `lintegral_lintegral_swap`) and
`Rd.IsCZFamily.setLIntegral_compl_closedBall_le` for each `y ∈ Q`. -/
theorem IsCZFamily.setLIntegral_compl_closedBall_setLIntegral_le (h : IsCZFamily θ B H) {c : V}
    {ρ : ℝ} {Q : Set V} (hQ : MeasurableSet Q) (hQc : Q ⊆ closedBall c ρ) {m : V → ℝ≥0∞}
    (hm : AEMeasurable m volume) :
    ∫⁻ x in (closedBall c (2 * ρ))ᶜ, ∫⁻ y in Q,
        lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) * m y ≤ H * ∫⁻ y in Q, m y := by
  have hF : AEMeasurable (Function.uncurry fun x y =>
      lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) * m y)
      ((volume.restrict (closedBall c (2 * ρ))ᶜ).prod (volume.restrict Q)) := by
    have h2 : AEMeasurable (fun p : V × V => m p.2)
        ((volume.restrict (closedBall c (2 * ρ))ᶜ).prod (volume.restrict Q)) :=
      hm.restrict.comp_snd
    exact (h.measurable_lqNorm_sub c).aemeasurable.mul h2
  rw [lintegral_lintegral_swap hF]
  have hx : ∀ y, Measurable fun x => lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) :=
    fun y => (h.measurable_lqNorm_sub c).comp (f := fun x : V => (x, y)) measurable_prodMk_right
  calc ∫⁻ y in Q, ∫⁻ x in (closedBall c (2 * ρ))ᶜ,
        lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) * m y
      = ∫⁻ y in Q, (∫⁻ x in (closedBall c (2 * ρ))ᶜ,
          lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ)) * m y :=
        lintegral_congr fun y => lintegral_mul_const _ (hx y)
    _ ≤ ∫⁻ y in Q, H * m y := by
        refine setLIntegral_mono' hQ fun y hy => ?_
        gcongr
        exact h.setLIntegral_compl_closedBall_le (mem_closedBall_iff_norm.1 (hQc hy))
    _ = H * ∫⁻ y in Q, m y := lintegral_const_mul'' H hm.restrict

/-! ### Convolutions of pieces with mean zero -/

/-- **A piece with mean zero against a bounded continuous kernel**: for `b` integrable,
vanishing outside a set `Q`, with `∫ b = 0`, and any points `c, x`,
`|(K ⋆ b)(x)| ≤ ∫_Q |K(x - y) - K(x - c)| |b(y)| dy`, since
`(K ⋆ b)(x) = ∫ (K(x - y) - K(x - c)) b(y) dy`. -/
theorem enorm_conv_le_setLIntegral_sub {K : V → ℂ} (hK : Continuous K)
    (hKb : BddAbove (Set.range fun z => ‖K z‖)) {Q : Set V} {b : V → ℂ} (hb : Integrable b)
    (hbQ : ∀ y ∉ Q, b y = 0) (hb0 : ∫ y, b y = 0) (c x : V) :
    ‖conv K b volume x‖ₑ ≤ ∫⁻ y in Q, ‖K (x - y) - K (x - c)‖ₑ * ‖b y‖ₑ := by
  obtain ⟨C, hC⟩ := hKb
  have hKb : Integrable (fun y => K (x - y) * b y) :=
    hb.bdd_mul (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => hC ⟨x - y, rfl⟩)
  have hconv : conv K b volume x = ∫ y, (K (x - y) - K (x - c)) * b y := by
    simp_rw [sub_mul]
    rw [integral_sub hKb (hb.const_mul _), integral_const_mul, hb0, mul_zero, sub_zero,
      conv_apply_eq_integral_sub]
  rw [hconv]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
  simp_rw [eNorm_mul]
  refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
  by_contra hyQ
  exact hy (by simp [hbQ y hyQ])

/-- **A piece with mean zero against a Calderón–Zygmund family**: for `b` integrable, vanishing
outside `Q`, with `∫ b = 0`, and any points `c, x`,
`‖((θ_j ⋆ b)(x))_j‖_{ℓ_2} ≤ ∫_Q ‖(θ_j(x - y) - θ_j(x - c))_j‖_{ℓ_2} |b(y)| dy`, by
`Rd.enorm_conv_le_setLIntegral_sub` for each `j` and Minkowski's integral inequality
(`MeasureTheory.lqNorm_lintegral_le`). -/
theorem IsCZFamily.lqNorm_conv_le_setLIntegral (h : IsCZFamily θ B H) {Q : Set V} {b : V → ℂ}
    (hb : Integrable b) (hbQ : ∀ y ∉ Q, b y = 0) (hb0 : ∫ y, b y = 0) (c x : V) :
    lqNorm 2 (fun j => ‖conv (θ j) b volume x‖ₑ) ≤
      ∫⁻ y in Q, lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) * ‖b y‖ₑ := by
  have hm : ∀ j, AEMeasurable (fun y => ‖θ j (x - y) - θ j (x - c)‖ₑ * ‖b y‖ₑ)
      (volume.restrict Q) := fun j =>
    (((h.continuous j).comp (continuous_const.sub continuous_id)).sub
      continuous_const).measurable.eNorm.aemeasurable.mul hb.1.eNorm.restrict
  calc lqNorm 2 (fun j => ‖conv (θ j) b volume x‖ₑ)
      ≤ lqNorm 2 (fun j => ∫⁻ y in Q, ‖θ j (x - y) - θ j (x - c)‖ₑ * ‖b y‖ₑ) :=
        ENNReal.lqNorm_mono fun j =>
          enorm_conv_le_setLIntegral_sub (h.continuous j) (h.bddAbove j) hb hbQ hb0 c x
    _ ≤ ∫⁻ y in Q, lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ * ‖b y‖ₑ) :=
        lqNorm_lintegral_le one_le_two hm
    _ = ∫⁻ y in Q, lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) * ‖b y‖ₑ :=
        lintegral_congr fun y => by
          simpa only [mul_comm] using ENNReal.lqNorm_const_mul (q := 2) ‖b y‖ₑ
            (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ)

/-- **Pieces with mean zero against a synthesis sum**: for integrable `b_j` vanishing outside `Q`
with `∫ b_j = 0`, a finite set `s` and any points `c, x`,
`|∑_{j ∈ s} (θ_j ⋆ b_j)(x)| ≤ ∫_Q ‖(θ_j(x - y) - θ_j(x - c))_j‖_{ℓ_2} ‖(b_j(y))_j‖_{ℓ_2} dy`,
by `Rd.enorm_conv_le_setLIntegral_sub` for each `j` and the Cauchy–Schwarz inequality
`ENNReal.sum_mul_le_lqNorm_two_mul` at each `y`. -/
theorem IsCZFamily.enorm_sum_conv_le_setLIntegral (h : IsCZFamily θ B H) (s : Finset ℕ)
    {Q : Set V} {b : ℕ → V → ℂ} (hb : ∀ j, Integrable (b j)) (hbQ : ∀ j, ∀ y ∉ Q, b j y = 0)
    (hb0 : ∀ j, ∫ y, b j y = 0) (c x : V) :
    ‖∑ j ∈ s, conv (θ j) (b j) volume x‖ₑ ≤
      ∫⁻ y in Q, lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - c)‖ₑ) *
        lqNorm 2 (fun j => ‖b j y‖ₑ) := by
  have hm : ∀ j ∈ s, AEMeasurable (fun y => ‖θ j (x - y) - θ j (x - c)‖ₑ * ‖b j y‖ₑ)
      (volume.restrict Q) := fun j _ =>
    (((h.continuous j).comp (continuous_const.sub continuous_id)).sub
      continuous_const).measurable.eNorm.aemeasurable.mul (hb j).1.eNorm.restrict
  calc ‖∑ j ∈ s, conv (θ j) (b j) volume x‖ₑ ≤ ∑ j ∈ s, ‖conv (θ j) (b j) volume x‖ₑ :=
        eNorm_sum_le _ _
    _ ≤ ∑ j ∈ s, ∫⁻ y in Q, ‖θ j (x - y) - θ j (x - c)‖ₑ * ‖b j y‖ₑ :=
        Finset.sum_le_sum fun j _ => enorm_conv_le_setLIntegral_sub (h.continuous j)
          (h.bddAbove j) (hb j) (hbQ j) (hb0 j) c x
    _ = ∫⁻ y in Q, ∑ j ∈ s, ‖θ j (x - y) - θ j (x - c)‖ₑ * ‖b j y‖ₑ :=
        (lintegral_finsetSum' s hm).symm
    _ ≤ _ := lintegral_mono fun y => ENNReal.sum_mul_le_lqNorm_two_mul s _ _

/-! ### The bad part -/

/-- **Convolution of the bad part, piece by piece**: for a continuous bounded kernel `K`, an
integrable `f` and the maximal big cubes of any `G` at any height `t`,
`(K ⋆ czBadC f)(x) = ∑_Q (K ⋆ czBadPart_Q f)(x)` at every point `x`. The proof bounds
`∑_Q ∫ |K(x - y)| |czBadPart_Q f(y)| dy` by `sup |K| · 2 ∫ |f|`
(`Rd.tsum_lintegral_enorm_czBadPart_le`), so sum and integral can be exchanged (Mathlib's
`hasSum_integral_of_summable_integral_norm`). -/
theorem hasSum_conv_czBadPart {K : V → ℂ} (hK : Continuous K)
    (hKb : BddAbove (Set.range fun z => ‖K z‖)) {f : V → ℂ} (hf : Integrable f) (x : V) :
    HasSum (fun km : czMaximal G t => conv K (czBadPart f km.1) volume x)
      (conv K (czBadC G t f) volume x) := by
  obtain ⟨C, hC⟩ := hKb
  have hint : ∀ km : czMaximal G t, Integrable (fun y => K (x - y) * czBadPart f km.1 y) :=
    fun km => (integrable_czBadPart hf.integrableOn).bdd_mul
      (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => hC ⟨x - y, rfl⟩)
  have hle : ∀ km : czMaximal G t, ∫⁻ y, ‖K (x - y) * czBadPart f km.1 y‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ y, ‖czBadPart f km.1 y‖ₑ := fun km => by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [eNorm_mul, ← ofReal_norm (K (x - y))]
    gcongr
    exact hC ⟨x - y, rfl⟩
  have hsum : ∑' km : czMaximal G t, ∫⁻ y, ‖K (x - y) * czBadPart f km.1 y‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C))
      (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf.2.ne))
      ((tsum_le_tsum hle).trans ?_)
    rw [ENNReal.tsum_mul_left]
    gcongr
    exact tsum_lintegral_enorm_czBadPart_le f
  have hnorm : (fun km : czMaximal G t => ∫ y, ‖K (x - y) * czBadPart f km.1 y‖) =
      fun km => (∫⁻ y, ‖K (x - y) * czBadPart f km.1 y‖ₑ).toReal :=
    funext fun km => integral_norm_eq_lintegral_eNorm (hint km).1
  have h1 := hasSum_integral_of_summable_integral_norm hint
    (hnorm ▸ ENNReal.summable_toReal hsum)
  have h2 : (fun km : czMaximal G t => conv K (czBadPart f km.1) volume x) =
      fun km => ∫ y, K (x - y) * czBadPart f km.1 y :=
    funext fun km => conv_apply_eq_integral_sub _ _ _
  have h3 : (fun y => K (x - y) * czBadC G t f y) =
      fun y => ∑' km : czMaximal G t, K (x - y) * czBadPart f km.1 y :=
    funext fun y => by rw [czBadC_eq_tsum, tsum_mul_left]
  rw [h2, conv_apply_eq_integral_sub, h3]
  exact h1

/-- **The bad part off the enlarged exceptional set, piece by piece**: for a Calderón–Zygmund
family with Hörmander constant `H`, the maximal big cubes `Q` of any `G` at any height `t`, with
centres `c_Q`, and almost everywhere measurable masses `m_Q : V → [0, ∞]`,
`∫_{V \ Ω*} ∑_Q ∫_Q ‖(θ_j(x - y) - θ_j(x - c_Q))_j‖_{ℓ_2} m_Q(y) dy dx ≤ H ∑_Q ∫_Q m_Q`. Every
`x ∉ Ω*` lies outside the ball of radius `2n 2^(-k)` around the centre of `Q = Q_{k,m}`, and
`Q` lies in the ball of radius `n 2^(-k)` (`Rd.zcell_subset_closedBall`), so
`Rd.IsCZFamily.setLIntegral_compl_closedBall_setLIntegral_le` bounds every term. -/
theorem IsCZFamily.setLIntegral_compl_czEnlarged_tsum_le (h : IsCZFamily θ B H)
    {m : czMaximal G t → V → ℝ≥0∞} (hm : ∀ km, AEMeasurable (m km) volume) :
    ∫⁻ x in (czEnlarged G t)ᶜ, ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2,
        lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - zcellCenter km.1.1 km.1.2)‖ₑ) * m km y ≤
      H * ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2, m km y := by
  have hmeas : ∀ km : czMaximal G t, AEMeasurable (fun x => ∫⁻ y in zcell km.1.1 km.1.2,
      lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - zcellCenter km.1.1 km.1.2)‖ₑ) * m km y)
      (volume.restrict (czEnlarged G t)ᶜ) := fun km => by
    have h2 : AEMeasurable (fun p : V × V => m km p.2)
        ((volume.restrict (czEnlarged G t)ᶜ).prod (volume.restrict (zcell km.1.1 km.1.2))) :=
      (hm km).restrict.comp_snd
    exact ((h.measurable_lqNorm_sub _).aemeasurable.mul h2).lintegral_prod_right'
  rw [lintegral_tsum hmeas, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun km => ?_
  have hsub : (czEnlarged G t)ᶜ ⊆
      (closedBall (zcellCenter km.1.1 km.1.2) (2 * (finrank ℝ V / 2 ^ km.1.1)))ᶜ :=
    compl_subset_compl.2 (subset_biUnion_of_mem (u := fun km : ℤ × (Fin (finrank ℝ V) → ℤ) =>
      closedBall (zcellCenter km.1 km.2) (2 * (finrank ℝ V / 2 ^ km.1))) km.2)
  exact (lintegral_mono_set hsub).trans (h.setLIntegral_compl_closedBall_setLIntegral_le
    (measurableSet_zcell _ _) (zcell_subset_closedBall _ _) (hm km))

/-- **The analysis operator on the bad part, off `Ω*`**: for a Calderón–Zygmund family with
Hörmander constant `H`, an integrable `f` and the cubes of any `G` at any height `t`,
`∫_{V \ Ω*} ‖((θ_j ⋆ czBadC f)(x))_j‖_{ℓ_2} dx ≤ 2H ∫ |f|`. At every `x` the sequence is the
series of the sequences of the pieces (`Rd.hasSum_conv_czBadPart`), whose `ℓ_2` norms add up
(`MeasureTheory.eLpNorm_tsum_le` for the counting measure) and are bounded by
`Rd.IsCZFamily.lqNorm_conv_le_setLIntegral`, since the pieces have mean zero. -/
theorem IsCZFamily.setLIntegral_lqNorm_conv_czBadC_le (h : IsCZFamily θ B H) {f : V → ℂ}
    (hf : Integrable f) :
    ∫⁻ x in (czEnlarged G t)ᶜ, lqNorm 2 (fun j => ‖conv (θ j) (czBadC G t f) volume x‖ₑ) ≤
      2 * H * ∫⁻ x, ‖f x‖ₑ := by
  have hpt : ∀ x, lqNorm 2 (fun j => ‖conv (θ j) (czBadC G t f) volume x‖ₑ) ≤
      ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2,
        lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - zcellCenter km.1.1 km.1.2)‖ₑ) *
          ‖czBadPart f km.1 y‖ₑ := fun x =>
    calc lqNorm 2 (fun j => ‖conv (θ j) (czBadC G t f) volume x‖ₑ)
        ≤ lqNorm 2 (fun j => ∑' km : czMaximal G t, ‖conv (θ j) (czBadPart f km.1) volume x‖ₑ) :=
          ENNReal.lqNorm_mono fun j => (hasSum_conv_czBadPart (h.continuous j) (h.bddAbove j)
            hf x).eNorm_le_of_bounded CompleteLattice.summable.hasSum fun _ => le_rfl
      _ ≤ ∑' km : czMaximal G t, lqNorm 2 (fun j => ‖conv (θ j) (czBadPart f km.1) volume x‖ₑ) :=
          eLpNorm_tsum_le one_le_two
      _ ≤ _ := tsum_le_tsum fun km => h.lqNorm_conv_le_setLIntegral
          (integrable_czBadPart hf.integrableOn) (fun y hy => czBadPart_of_notMem f hy)
          (integral_czBadPart f km.1) _ x
  calc ∫⁻ x in (czEnlarged G t)ᶜ, lqNorm 2 (fun j => ‖conv (θ j) (czBadC G t f) volume x‖ₑ)
      ≤ ∫⁻ x in (czEnlarged G t)ᶜ, ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2,
          lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - zcellCenter km.1.1 km.1.2)‖ₑ) *
            ‖czBadPart f km.1 y‖ₑ := lintegral_mono fun x => hpt x
    _ ≤ H * ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2, ‖czBadPart f km.1 y‖ₑ :=
        h.setLIntegral_compl_czEnlarged_tsum_le fun km =>
          (integrable_czBadPart hf.integrableOn).1.eNorm
    _ ≤ H * (2 * ∫⁻ x, ‖f x‖ₑ) := by
        gcongr
        exact (tsum_le_tsum fun km => setLIntegral_le_lintegral _ _).trans
          (tsum_lintegral_enorm_czBadPart_le f)
    _ = 2 * H * ∫⁻ x, ‖f x‖ₑ := by ring

/-- **The synthesis operator on the bad parts, off `Ω*`**: for a Calderón–Zygmund family with
Hörmander constant `H`, integrable `g_j`, a finite set `s` and the cubes of any `G` at any
height `t`,
`∫_{V \ Ω*} |∑_{j ∈ s} (θ_j ⋆ czBadC g_j)(x)| dx ≤ 2H ∫ ‖(g_j(x))_j‖_{ℓ_2} dx`, by
`Rd.hasSum_conv_czBadPart` for each `j`, `Rd.IsCZFamily.enorm_sum_conv_le_setLIntegral` for the
pieces on each cube and `Rd.tsum_lintegral_lqNorm_czBadPart_le`. -/
theorem IsCZFamily.setLIntegral_enorm_sum_conv_czBadC_le (h : IsCZFamily θ B H) (s : Finset ℕ)
    {g : ℕ → V → ℂ} (hg : ∀ j, Integrable (g j)) :
    ∫⁻ x in (czEnlarged G t)ᶜ, ‖∑ j ∈ s, conv (θ j) (czBadC G t (g j)) volume x‖ₑ ≤
      2 * H * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) := by
  have hpt : ∀ x, ‖∑ j ∈ s, conv (θ j) (czBadC G t (g j)) volume x‖ₑ ≤
      ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2,
        lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - zcellCenter km.1.1 km.1.2)‖ₑ) *
          lqNorm 2 (fun j => ‖czBadPart (g j) km.1 y‖ₑ) := fun x =>
    calc ‖∑ j ∈ s, conv (θ j) (czBadC G t (g j)) volume x‖ₑ
        ≤ ∑' km : czMaximal G t, ‖∑ j ∈ s, conv (θ j) (czBadPart (g j) km.1) volume x‖ₑ :=
          (hasSum_sum fun j _ => hasSum_conv_czBadPart (h.continuous j) (h.bddAbove j) (hg j)
            x).eNorm_le_of_bounded CompleteLattice.summable.hasSum fun _ => le_rfl
      _ ≤ _ := tsum_le_tsum fun km => h.enorm_sum_conv_le_setLIntegral s
          (fun j => integrable_czBadPart (hg j).integrableOn)
          (fun j y hy => czBadPart_of_notMem (g j) hy) (fun j => integral_czBadPart (g j) km.1) _ x
  calc ∫⁻ x in (czEnlarged G t)ᶜ, ‖∑ j ∈ s, conv (θ j) (czBadC G t (g j)) volume x‖ₑ
      ≤ ∫⁻ x in (czEnlarged G t)ᶜ, ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2,
          lqNorm 2 (fun j => ‖θ j (x - y) - θ j (x - zcellCenter km.1.1 km.1.2)‖ₑ) *
            lqNorm 2 (fun j => ‖czBadPart (g j) km.1 y‖ₑ) := lintegral_mono fun x => hpt x
    _ ≤ H * ∑' km : czMaximal G t, ∫⁻ y in zcell km.1.1 km.1.2,
          lqNorm 2 (fun j => ‖czBadPart (g j) km.1 y‖ₑ) :=
        h.setLIntegral_compl_czEnlarged_tsum_le fun km => aemeasurable_lqNorm_comp
          (fun j => (integrable_czBadPart (hg j).integrableOn).1.eNorm) 2
    _ ≤ H * (2 * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ)) := by
        gcongr
        exact (tsum_le_tsum fun km => setLIntegral_le_lintegral _ _).trans
          (tsum_lintegral_lqNorm_czBadPart_le one_le_two fun j => (hg j).1)
    _ = 2 * H * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) := by ring

/-! ### The good part and the splitting -/

/-- **The analysis operator on the good part**: in dimension `n ≥ 1`, for a Calderón–Zygmund
family with overlap `B`, an integrable `f` and `0 < t < ∞`, the good part `czGoodC f` for the
cubes of `|f|` at height `t` satisfies
`∫ ‖((θ_j ⋆ czGoodC f)(x))_j‖_{ℓ_2}² dx ≤ B 2^n t ∫ |f|`, by the Plancherel bound
`Rd.IsCZFamily.lintegral_lqNorm_conv_sq_le` and `Rd.lintegral_enorm_czGoodC_sq_le`. -/
theorem IsCZFamily.lintegral_lqNorm_conv_czGoodC_sq_le [Nontrivial V] (h : IsCZFamily θ B H)
    {f : V → ℂ} (hf : Integrable f) (ht0 : 0 < t) (ht : t ≠ ∞) :
    ∫⁻ x, lqNorm 2 (fun j => ‖conv (θ j) (czGoodC (fun y => ‖f y‖ₑ) t f) volume x‖ₑ) ^ 2 ≤
      B * 2 ^ finrank ℝ V * t * ∫⁻ x, ‖f x‖ₑ := by
  have hsq := lintegral_enorm_czGoodC_sq_le hf ht0
  have hL2 : MemLp (czGoodC (fun y => ‖f y‖ₑ) t f) 2 volume :=
    memLp_two_of_lintegral_enorm_sq_ne_top (aestronglyMeasurable_czGoodC hf.1)
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ht) hf.2.ne) hsq)
  calc _ ≤ B * ∫⁻ x, ‖czGoodC (fun y => ‖f y‖ₑ) t f x‖ₑ ^ 2 := h.lintegral_lqNorm_conv_sq_le hL2
    _ ≤ B * (2 ^ finrank ℝ V * t * ∫⁻ x, ‖f x‖ₑ) := by gcongr
    _ = B * 2 ^ finrank ℝ V * t * ∫⁻ x, ‖f x‖ₑ := by ring

/-- **The synthesis operator on the good parts**: in dimension `n ≥ 1`, for a Calderón–Zygmund
family with overlap `B`, a finite set `s`, almost everywhere strongly measurable `g_j` with
`G = ‖(g_j)_j‖_{ℓ_2}` integrable, and `0 < t < ∞`, the good parts `czGoodC g_j` for the cubes of
`G` at height `t` satisfy `∫ |∑_{j ∈ s} (θ_j ⋆ czGoodC g_j)(x)|² dx ≤ B 2^n t ∫ G`, by the
Plancherel bound `Rd.IsCZFamily.lintegral_enorm_sum_conv_sq_le` and
`Rd.lintegral_lqNorm_czGoodC_sq_le`. -/
theorem IsCZFamily.lintegral_enorm_sum_conv_czGoodC_sq_le [Nontrivial V] (h : IsCZFamily θ B H)
    (s : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (hG : ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) ≠ ∞) (ht0 : 0 < t) (ht : t ≠ ∞) :
    ∫⁻ x, ‖∑ j ∈ s, conv (θ j)
        (czGoodC (fun y => lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g j)) volume x‖ₑ ^ 2 ≤
      B * 2 ^ finrank ℝ V * t * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) := by
  have hsq := lintegral_lqNorm_czGoodC_sq_le one_le_two hg hG ht0
  have hfin : ∫⁻ x, lqNorm 2 (fun j =>
      ‖czGoodC (fun y => lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g j) x‖ₑ) ^ 2 ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ht) hG) hsq
  have hL2 : ∀ j, MemLp (czGoodC (fun y => lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g j)) 2 volume :=
    fun j => memLp_two_of_lintegral_enorm_sq_ne_top (aestronglyMeasurable_czGoodC (hg j))
      (ne_top_of_le_ne_top hfin (lintegral_mono fun x => by
        gcongr
        exact ENNReal.le_lqNorm two_ne_zero (fun i => ‖czGoodC (fun y =>
          lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g i) x‖ₑ) j))
  calc _ ≤ B * ∫⁻ x, lqNorm 2 (fun j =>
        ‖czGoodC (fun y => lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g j) x‖ₑ) ^ 2 :=
        h.lintegral_enorm_sum_conv_sq_le s hL2
    _ ≤ B * (2 ^ finrank ℝ V * t * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ)) := by gcongr
    _ = B * 2 ^ finrank ℝ V * t * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) := by ring

/-- **Splitting the analysis operator**: for a Calderón–Zygmund family, an integrable `f` and
the cubes of any `G` at any height `t`, almost every `x` satisfies
`‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ≤ ‖((θ_j ⋆ czGoodC f)(x))_j‖_{ℓ_2} + ‖((θ_j ⋆ czBadC f)(x))_j‖_{ℓ_2}`,
since `f = czGoodC f + czBadC f` with both parts integrable (`Rd.conv_add_ae`) and by
Minkowski's inequality in `ℓ_2`. -/
theorem IsCZFamily.ae_lqNorm_conv_le_add (h : IsCZFamily θ B H) {f : V → ℂ} (hf : Integrable f) :
    ∀ᵐ x, lqNorm 2 (fun j => ‖conv (θ j) f volume x‖ₑ) ≤
      lqNorm 2 (fun j => ‖conv (θ j) (czGoodC G t f) volume x‖ₑ) +
        lqNorm 2 (fun j => ‖conv (θ j) (czBadC G t f) volume x‖ₑ) := by
  have hae := ae_all_iff.2 fun j => conv_add_ae le_rfl ENNReal.one_ne_top (h.integrable j)
    (memLp_one_iff_integrable.2 (integrable_czGoodC (G := G) (t := t) hf))
    (memLp_one_iff_integrable.2 (integrable_czBadC (G := G) (t := t) hf))
  filter_upwards [hae] with x hx
  simp only [czGoodC_add_czBadC, Pi.add_apply] at hx
  refine (ENNReal.lqNorm_mono fun j => ?_).trans (ENNReal.lqNorm_add_le one_le_two _ _)
  rw [hx j]
  exact eNorm_add_le _ _

/-- **Splitting the synthesis operator**: for a Calderón–Zygmund family, integrable `g_j`, a
finite set `s` and the cubes of any `G` at any height `t`, almost every `x` satisfies
`|∑_{j ∈ s} (θ_j ⋆ g_j)(x)| ≤ |∑_{j ∈ s} (θ_j ⋆ czGoodC g_j)(x)| +
|∑_{j ∈ s} (θ_j ⋆ czBadC g_j)(x)|` (`Rd.conv_add_ae` for every `j`). -/
theorem IsCZFamily.ae_enorm_sum_conv_le_add (h : IsCZFamily θ B H) (s : Finset ℕ)
    {g : ℕ → V → ℂ} (hg : ∀ j, Integrable (g j)) :
    ∀ᵐ x, ‖∑ j ∈ s, conv (θ j) (g j) volume x‖ₑ ≤
      ‖∑ j ∈ s, conv (θ j) (czGoodC G t (g j)) volume x‖ₑ +
        ‖∑ j ∈ s, conv (θ j) (czBadC G t (g j)) volume x‖ₑ := by
  have hae := ae_all_iff.2 fun j => conv_add_ae le_rfl ENNReal.one_ne_top (h.integrable j)
    (memLp_one_iff_integrable.2 (integrable_czGoodC (G := G) (t := t) (hg j)))
    (memLp_one_iff_integrable.2 (integrable_czBadC (G := G) (t := t) (hg j)))
  filter_upwards [hae] with x hx
  simp only [czGoodC_add_czBadC, Pi.add_apply] at hx
  rw [Finset.sum_congr rfl fun j _ => hx j, Finset.sum_add_distrib]
  exact eNorm_add_le _ _

/-! ### The weak type `(1,1)` -/

variable (V) in
/-- The constant of the weak type `(1,1)` of a Calderón–Zygmund family with overlap `B` and
Hörmander constant `H`: `4 · 2^n B + (2n)^n |B(0, 1)| + 4H`, where `|B(0, 1)|` is the volume of
the unit ball of `V`, from the good part, the enlarged exceptional set and the bad part. -/
noncomputable def vectorWeakConst (B H : ℝ≥0∞) : ℝ≥0∞ :=
  4 * 2 ^ finrank ℝ V * B + (2 * finrank ℝ V) ^ finrank ℝ V * volume (ball (0 : V) 1) + 4 * H

/-- The weak type constant is finite for finite `B` and `H`. -/
theorem vectorWeakConst_ne_top (hB : B ≠ ∞) (hH : H ≠ ∞) : vectorWeakConst V B H ≠ ∞ := by
  have hball : volume (ball (0 : V) 1) ≠ ∞ := measure_ball_lt_top.ne
  unfold vectorWeakConst
  finiteness

/-- **The weak type `(1,1)` of the analysis operator**: in dimension `n ≥ 1`, for a
Calderón–Zygmund family with overlap `B` and Hörmander constant `H`, every integrable
`f : V → ℂ` and `0 < t < ∞`,
`|{x : ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} > t}| ≤ C t⁻¹ ∫ |f|` with `C = vectorWeakConst V B H`. The
Calderón–Zygmund decomposition of `|f|` at height `t` splits `f` into the good part, handled by
the Plancherel bound and Chebyshev's inequality, and the bad part, handled by the measure of the
enlarged exceptional set and the Hörmander condition off it
(`MeasureTheory.measure_lt_le_of_ae_le_add`). -/
theorem IsCZFamily.volume_lqNorm_conv_gt_le [Nontrivial V] (h : IsCZFamily θ B H) {f : V → ℂ}
    (hf : Integrable f) (ht0 : 0 < t) (ht : t ≠ ∞) :
    volume {x | t < lqNorm 2 (fun j => ‖conv (θ j) f volume x‖ₑ)} ≤
      vectorWeakConst V B H * t⁻¹ * ∫⁻ x, ‖f x‖ₑ := by
  have ha : AEMeasurable (fun x => lqNorm 2 (fun j =>
      ‖conv (θ j) (czGoodC (fun y => ‖f y‖ₑ) t f) volume x‖ₑ)) volume :=
    aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_conv (h.integrable j).1
      (aestronglyMeasurable_czGoodC hf.1)).eNorm) 2
  have hb : AEMeasurable (fun x => lqNorm 2 (fun j =>
      ‖conv (θ j) (czBadC (fun y => ‖f y‖ₑ) t f) volume x‖ₑ)) volume :=
    aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_conv (h.integrable j).1
      (integrable_czBadC hf).1).eNorm) 2
  refine (measure_lt_le_of_ae_le_add ha hb (h.ae_lqNorm_conv_le_add hf) measurableSet_czEnlarged
    ht0 ht (h.lintegral_lqNorm_conv_czGoodC_sq_le hf ht0 ht) volume_czEnlarged_le
    (h.setLIntegral_lqNorm_conv_czBadC_le hf)).trans_eq ?_
  rw [vectorWeakConst]
  ring

/-- **The weak type `(1,1)` of the synthesis operators**: in dimension `n ≥ 1`, for a
Calderón–Zygmund family with overlap `B` and Hörmander constant `H`, every finite set `s`, almost
everywhere strongly measurable `g_j : V → ℂ` with `G = ‖(g_j)_j‖_{ℓ_2}` integrable, and
`0 < t < ∞`, `|{x : |∑_{j ∈ s} (θ_j ⋆ g_j)(x)| > t}| ≤ C t⁻¹ ∫ G` with
`C = vectorWeakConst V B H`, by the Calderón–Zygmund decomposition of `G` at height `t`, whose
cubes serve every `g_j`. -/
theorem IsCZFamily.volume_enorm_sum_conv_gt_le [Nontrivial V] (h : IsCZFamily θ B H)
    (s : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, AEStronglyMeasurable (g j) volume)
    (hG : ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) ≠ ∞) (ht0 : 0 < t) (ht : t ≠ ∞) :
    volume {x | t < ‖∑ j ∈ s, conv (θ j) (g j) volume x‖ₑ} ≤
      vectorWeakConst V B H * t⁻¹ * ∫⁻ x, lqNorm 2 (fun j => ‖g j x‖ₑ) := by
  have hgi : ∀ j, Integrable (g j) := fun j => ⟨hg j, (lintegral_mono fun x =>
    ENNReal.le_lqNorm two_ne_zero (fun i => ‖g i x‖ₑ) j).trans_lt hG.lt_top⟩
  have ha : AEMeasurable (fun x => ‖∑ j ∈ s, conv (θ j)
      (czGoodC (fun y => lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g j)) volume x‖ₑ) volume :=
    (Finset.aestronglyMeasurable_fun_sum s fun j _ => aestronglyMeasurable_conv
      (h.integrable j).1 (aestronglyMeasurable_czGoodC (hg j))).eNorm
  have hb : AEMeasurable (fun x => ‖∑ j ∈ s, conv (θ j)
      (czBadC (fun y => lqNorm 2 (fun j => ‖g j y‖ₑ)) t (g j)) volume x‖ₑ) volume :=
    (Finset.aestronglyMeasurable_fun_sum s fun j _ => aestronglyMeasurable_conv
      (h.integrable j).1 (integrable_czBadC (hgi j)).1).eNorm
  refine (measure_lt_le_of_ae_le_add ha hb (h.ae_enorm_sum_conv_le_add s hgi)
    measurableSet_czEnlarged ht0 ht (h.lintegral_enorm_sum_conv_czGoodC_sq_le s hg hG ht0 ht)
    volume_czEnlarged_le (h.setLIntegral_enorm_sum_conv_czBadC_le s hgi)).trans_eq ?_
  rw [vectorWeakConst]
  ring

end Rd
