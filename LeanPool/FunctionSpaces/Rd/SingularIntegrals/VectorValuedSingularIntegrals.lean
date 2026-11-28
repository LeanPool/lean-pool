/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.VectorValuedWeakType
public import LeanPool.FunctionSpaces.Rd.SingularIntegrals.ConvolutionAdjoint
public import LeanPool.FunctionSpaces.Analysis.Lp.Marcinkiewicz
public import LeanPool.FunctionSpaces.Analysis.Lp.NormingFamily

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The strong type of vector-valued singular integrals for `1 < p < ∞`

Let `V` have dimension `n ≥ 1` and let `(θ_j)_{j ∈ ℕ}` be a Calderón–Zygmund family on `V`
with Fourier overlap `B` and Hörmander constant `H` (`Rd.IsCZFamily`). For every `1 < p < ∞`,
with the constant `C = Rd.czConst V p B H`:

* **the analysis operator** (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`):
  `‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_{L_p} ≤ C ‖f‖_p` for every `f ∈ L_p(V)`;
* **the synthesis operators** (`Rd.IsCZFamily.eLpNorm_sum_conv_le`):
  `‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ C ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_{L_p}` for every finite set `s` and all
  `g_j ∈ L_p(V)`.

For `p = 2` these are the Plancherel bounds with `C = B^{1/2}`, in every dimension
(`Rd.IsCZFamily.eLpNorm_lqNorm_conv_two_le`, `Rd.IsCZFamily.eLpNorm_sum_conv_two_le`). For
`1 < p < 2`, Marcinkiewicz interpolation between the weak type `(1,1)` and the
`L_2` bound gives `C = Rd.czConstBelow V p B H`: for the analysis operator in the terms of the
Carleson project (`Rd.IsCZFamily.hasStrongType_lqNorm_conv_of_lt`), for the synthesis operators
on the abstract input type of families of measurable functions
(`Rd.IsCZFamily.eLpNorm_sum_conv_le_of_lt_of_measurable`), extended to all families in `L_p` by
measurable representatives (`Rd.IsCZFamily.eLpNorm_sum_conv_le_of_lt`). For `2 < p < ∞`
duality with the conjugate exponent `p' < 2` exchanges the two operators of the adjoint family
`θ_j^*(x) = conj θ_j(-x)`, with `C = Rd.czConstBelow V p' B H`.

For `p > 2` the norms are bounded through their pairings with `L_{p'}`
(`MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le`,
`MeasureTheory.eLpNorm_le_of_forall_enorm_integral_mul_conj_le`), and the adjoint identity
`Rd.integral_conv_mul_conj` turns the pairings of one operator into pairings of the other
operator of the adjoint family (`Rd.IsCZFamily.enorm_sum_integral_conv_mul_conj_le`,
`Rd.IsCZFamily.enorm_integral_sum_conv_mul_conj_le`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal ComplexConjugate
open ENNReal (lqNorm)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {θ : ℕ → V → ℂ} {B H : ℝ≥0∞}

/-! ### The case `p = 2` -/

/-- **The analysis operator has strong type `(2, 2)`** with constant `B^{1/2}`, in the terms of
the Carleson project: for every `f ∈ L_2(V)` the function `x ↦ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2}` is
almost everywhere strongly measurable with `L_2` norm at most `B^{1/2} ‖f‖_2`, by the Plancherel
bound `Rd.IsCZFamily.lintegral_lqNorm_conv_sq_le`. -/
theorem IsCZFamily.hasStrongType_lqNorm_conv_two (h : IsCZFamily θ B H) :
    HasStrongType (fun f x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) 2 2 volume volume
      (B ^ (1 / 2 : ℝ)) := by
  intro f hf
  have hm : AEMeasurable (fun x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) volume :=
    aemeasurable_lqNorm_comp (fun j =>
      (aestronglyMeasurable_conv (h.integrable j).1 hf.aestronglyMeasurable).eNorm) 2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have h2 := eLpNorm_le_rpow_mul_of_lintegral_enorm_le (p := 2) (C := B) two_ne_zero
    ENNReal.ofNat_ne_top hm.aestronglyMeasurable hf.aestronglyMeasurable (by
      simpa only [eNorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two] using
        h.lintegral_lqNorm_conv_sq_le hf)
  simpa only [ENNReal.toReal_ofNat] using h2

/-- **The analysis bound in `L_2`**: `‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_2 ≤ B^{1/2} ‖f‖_2` for every
`f ∈ L_2(V)` (`Rd.IsCZFamily.hasStrongType_lqNorm_conv_two`). -/
theorem IsCZFamily.eLpNorm_lqNorm_conv_two_le (h : IsCZFamily θ B H) {f : V → ℂ}
    (hf : MemLp f 2 volume) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) 2 volume ≤
      B ^ (1 / 2 : ℝ) * eLpNorm f 2 volume :=
  (h.hasStrongType_lqNorm_conv_two f hf).2

/-- **The synthesis bound in `L_2`**: for every finite set `s` and all `g_j ∈ L_2(V)`,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_2 ≤ B^{1/2} ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_2`, by the Plancherel bound
`Rd.IsCZFamily.lintegral_enorm_sum_conv_sq_le`. -/
theorem IsCZFamily.eLpNorm_sum_conv_two_le (h : IsCZFamily θ B H) (s : Finset ℕ)
    {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) 2 volume) :
    eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) 2 volume ≤
      B ^ (1 / 2 : ℝ) * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) 2 volume := by
  have hm1 : AEStronglyMeasurable (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) volume :=
    Finset.aestronglyMeasurable_fun_sum s fun j _ =>
      aestronglyMeasurable_conv (h.integrable j).1 (hg j).aestronglyMeasurable
  have hm2 : AEMeasurable (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) volume :=
    aemeasurable_lqNorm_comp (fun j => (hg j).aestronglyMeasurable.eNorm) 2
  have h2 := eLpNorm_le_rpow_mul_of_lintegral_enorm_le (p := 2) (C := B) two_ne_zero
    ENNReal.ofNat_ne_top hm1 hm2.aestronglyMeasurable (by
      simpa only [eNorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_two] using
        h.lintegral_enorm_sum_conv_sq_le s hg)
  simpa only [ENNReal.toReal_ofNat] using h2

/-! ### The analysis operator for `1 < p < 2` -/

/-- **The analysis operator is subadditive** almost everywhere with constant `1` on
`L_1(V) ∪ L_2(V)`, in the terms of the Carleson project: convolution is additive almost
everywhere (`Rd.conv_add_ae_of_memLp`), and the `ℓ_2` norm satisfies Minkowski's inequality. -/
theorem IsCZFamily.aeSubadditiveOn_lqNorm_conv (h : IsCZFamily θ B H) :
    AESubadditiveOn (fun f x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ)
      (fun f => MemLp f 1 volume ∨ MemLp f 2 volume) 1 volume := by
  have hexp : ∀ {u : V → ℂ}, (MemLp u 1 volume ∨ MemLp u 2 volume) →
      ∃ r : ℝ≥0∞, 1 ≤ r ∧ r ≠ ∞ ∧ MemLp u r volume := by
    rintro u (hu | hu)
    exacts [⟨1, le_rfl, ENNReal.one_ne_top, hu⟩, ⟨2, one_le_two, ENNReal.ofNat_ne_top, hu⟩]
  intro f g hf hg
  obtain ⟨p, hp1, hp, hfp⟩ := hexp hf
  obtain ⟨r, hr1, hr, hgr⟩ := hexp hg
  filter_upwards [ae_all_iff.2 fun j =>
    conv_add_ae_of_memLp hp1 hp hr1 hr (h.integrable j) hfp hgr] with x hx
  simp only [eNorm_eq_self, one_mul]
  refine (ENNReal.lqNorm_mono fun j => ?_).trans (ENNReal.lqNorm_add_le one_le_two _ _)
  rw [hx j, Pi.add_apply]
  exact eNorm_add_le _ _

/-- **The analysis operator has weak type `(1,1)`** with constant `Rd.vectorWeakConst V B H`, in
the terms of the Carleson project, in dimension `n ≥ 1`: the level-set bound
`Rd.IsCZFamily.volume_lqNorm_conv_gt_le` at every level `t` bounds the weak `L_1` norm. -/
theorem IsCZFamily.hasWeakType_lqNorm_conv [Nontrivial V] (h : IsCZFamily θ B H) :
    HasWeakType (fun f x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) 1 1 volume volume
      (vectorWeakConst V B H) := by
  intro f hf
  have hfi : Integrable f := memLp_one_iff_integrable.1 hf
  refine ⟨(aemeasurable_lqNorm_comp (fun j =>
    (aestronglyMeasurable_conv (h.integrable j).1 hf.aestronglyMeasurable).eNorm)
      2).aestronglyMeasurable, ?_⟩
  rw [wnorm_ne_top ENNReal.one_ne_top, ENNReal.toReal_one, wnorm',
    eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable]
  refine iSup_le fun t => ?_
  rw [inv_one, ENNReal.rpow_one]
  rcases eq_or_ne (t : ℝ≥0∞) 0 with ht | ht
  · rw [ht, zero_mul]
    exact zero_le
  have hw := h.volume_lqNorm_conv_gt_le hfi (pos_iff_ne_zero.2 ht) ENNReal.coe_ne_top
  calc (t : ℝ≥0∞) * distribution (fun x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) t volume
      ≤ t * (vectorWeakConst V B H * (t : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖f x‖ₑ) := by
        gcongr
        simpa only [distribution, eNorm_eq_self] using hw
    _ = vectorWeakConst V B H * ∫⁻ x, ‖f x‖ₑ := by
        rw [mul_comm (vectorWeakConst V B H), mul_assoc, ← mul_assoc (t : ℝ≥0∞),
          ENNReal.mul_inv_cancel ht ENNReal.coe_ne_top, one_mul]

variable (V) in
/-- The constant of the strong type `(p, p)`, `1 < p < 2`, of a Calderón–Zygmund family with
overlap `B` and Hörmander constant `H`: `C^M_p(C_V(B, H), B)^{1/p}`, with the Marcinkiewicz
constant `C^M_p(C₁, C₂) = p (2 C₁/(p - 1) + 4 C₂/(2 - p))` (`MeasureTheory.marcinkiewiczConst`)
and the weak type constant `C_V(B, H)` (`Rd.vectorWeakConst`). -/
noncomputable def czConstBelow (p B H : ℝ≥0∞) : ℝ≥0∞ :=
  marcinkiewiczConst p.toReal (vectorWeakConst V B H) B ^ (1 / p.toReal)

/-- The constant `Rd.czConstBelow V p B H` is finite for `1 < p < 2` and finite `B`, `H`. -/
theorem czConstBelow_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) (hB : B ≠ ∞) (hH : H ≠ ∞) :
    czConstBelow V p B H ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg (by positivity) (marcinkiewiczConst_ne_top
    (ENNReal.one_lt_toReal hp1 (ne_top_of_lt hp2))
    (ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_ofNat]))
    (vectorWeakConst_ne_top hB hH) hB)

/-- **The analysis operator has strong type `(p, p)` for `1 < p < 2`**, in dimension `n ≥ 1`,
with constant `Rd.czConstBelow V p B H`: Marcinkiewicz interpolation in the terms of the
Carleson project (`MeasureTheory.hasStrongType_of_hasWeakType_one_of_hasStrongType_two` with
`A = 1`, `C₁ = C_V(B, H)`, `C₂ = B^{1/2}`) between the weak type `(1,1)` and the strong type
`(2,2)`. -/
theorem IsCZFamily.hasStrongType_lqNorm_conv_of_lt [Nontrivial V] (h : IsCZFamily θ B H)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) :
    HasStrongType (fun f x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) p p volume volume
      (czConstBelow V p B H) := by
  have hc : marcinkiewiczNormConst p ((1 : ℝ≥0) : ℝ≥0∞) (vectorWeakConst V B H)
      (B ^ (1 / 2 : ℝ)) = czConstBelow V p B H := by
    rw [marcinkiewiczNormConst, czConstBelow, ENNReal.coe_one, one_mul, one_pow, one_mul,
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [← hc]
  exact hasStrongType_of_hasWeakType_one_of_hasStrongType_two hp1 hp2
    (fun f hf => (aemeasurable_lqNorm_comp (fun j =>
      (aestronglyMeasurable_conv (h.integrable j).1 hf.aestronglyMeasurable).eNorm)
        2).aestronglyMeasurable)
    (by rw [ENNReal.coe_one]; exact h.aeSubadditiveOn_lqNorm_conv) h.hasWeakType_lqNorm_conv
    h.hasStrongType_lqNorm_conv_two

/-- **The analysis bound for `1 < p < 2`**, in dimension `n ≥ 1`:
`‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ Rd.czConstBelow V p B H ‖f‖_p` for every `f ∈ L_p(V)`
(`Rd.IsCZFamily.hasStrongType_lqNorm_conv_of_lt`). -/
theorem IsCZFamily.eLpNorm_lqNorm_conv_le_of_lt [Nontrivial V] (h : IsCZFamily θ B H)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) {f : V → ℂ} (hf : MemLp f p volume) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) p volume ≤
      czConstBelow V p B H * eLpNorm f p volume :=
  (h.hasStrongType_lqNorm_conv_of_lt hp1 hp2 f hf).2

/-! ### The synthesis operators for `1 < p < 2` -/

/-- **The synthesis bound for `1 < p < 2`, for measurable families**: in dimension `n ≥ 1`, for
every finite set `s` and measurable `g_j` with `‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p < ∞`,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ Rd.czConstBelow V p B H ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p`. Marcinkiewicz
interpolation on the abstract input type of measurable families
(`MeasureTheory.eLpNorm_le_of_weak_one_strong_two`) with the size `‖(g_j)_j‖_{ℓ_2}`, the
restriction `(1_S g_j)_j`, the weak type `(1,1)` `Rd.IsCZFamily.volume_enorm_sum_conv_gt_le`
and the Plancherel bound `Rd.IsCZFamily.lintegral_enorm_sum_conv_sq_le`. -/
theorem IsCZFamily.eLpNorm_sum_conv_le_of_lt_of_measurable [Nontrivial V] (h : IsCZFamily θ B H)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) (s : Finset ℕ) {g : ℕ → V → ℂ}
    (hg : ∀ j, Measurable (g j))
    (hG : eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume ≠ ∞) :
    eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) p volume ≤
      czConstBelow V p B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume := by
  classical
  have hp : p ≠ ∞ := ne_top_of_lt hp2
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  let X := {g : ℕ → V → ℂ // ∀ j, Measurable (g j)}
  let res : X → Set V → X := fun g S =>
    if hS : MeasurableSet S then ⟨fun j => S.indicator (g.1 j), fun j => (g.2 j).indicator hS⟩
    else g
  have hres : ∀ (g : X) (S : Set V), MeasurableSet S → (res g S).1 = fun j => S.indicator (g.1 j) :=
    fun g S hS => by simp only [res, hS, ↓reduceDIte]
  have h1 := eLpNorm_le_of_weak_one_strong_two (μ := volume) (ν := volume)
    (C₁ := vectorWeakConst V B H) (C₂ := B) (p := p)
    (fun g : X => fun x => lqNorm 2 fun j => ‖g.1 j x‖ₑ)
    (fun g : X => fun x => ‖∑ j ∈ s, conv (θ j) (g.1 j) volume x‖ₑ) res
    (fun g => measurable_lqNorm_comp (fun j => (g.2 j).eNorm) 2)
    (fun g => (Finset.aestronglyMeasurable_fun_sum s fun j _ => aestronglyMeasurable_conv
      (h.integrable j).1 (g.2 j).aestronglyMeasurable).eNorm)
    (fun g S hS => by
      funext x
      simp only [hres g S hS, eNorm_indicator_eq_indicator_eNorm]
      exact ENNReal.lqNorm_indicator 2 S (fun j y => ‖g.1 j y‖ₑ) x)
    (fun g S hS hfin => by
      have hgp : ∀ j, MemLp (g.1 j) p volume := fun j =>
        memLp_of_lintegral_lqNorm_rpow_ne_top hp0 hp (g.2 j).aestronglyMeasurable hfin
      filter_upwards [ae_all_iff.2 fun j => conv_add_ae hp1.le hp (h.integrable j)
        ((hgp j).indicator hS.nullMeasurableSet)
        ((hgp j).indicator hS.compl.nullMeasurableSet)] with x hx
      simp only [hres g S hS, hres g Sᶜ hS.compl]
      refine le_of_eq_of_le ?_ (eNorm_add_le _ _)
      rw [← Finset.sum_add_distrib]
      refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
      rw [← Pi.add_apply (conv (θ j) (S.indicator (g.1 j)) volume), ← hx j,
        Set.indicator_self_add_compl])
    (fun g hfin t ht0 ht => h.volume_enorm_sum_conv_gt_le s
      (fun j => (g.2 j).aestronglyMeasurable) hfin ht0 ht)
    (fun g hfin => h.lintegral_enorm_sum_conv_sq_le s fun j =>
      memLp_of_lintegral_lqNorm_rpow_ne_top two_ne_zero ENNReal.ofNat_ne_top
        (g.2 j).aestronglyMeasurable (by
          simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hfin))
    hp1 hp2 ⟨g, hg⟩ hG
  rwa [eLpNorm_eNorm _ (Finset.aestronglyMeasurable_fun_sum s fun j _ =>
    aestronglyMeasurable_conv (h.integrable j).1 (hg j).aestronglyMeasurable)] at h1

/-- **The synthesis bound for `1 < p < 2`**: in dimension `n ≥ 1`, for every finite set `s` and
all `g_j ∈ L_p(V)`,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ Rd.czConstBelow V p B H ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p`. Replace `g_j`
by a measurable representative for `j ∈ s` and by `0` otherwise; the sum is unchanged, the
`ℓ_2` norm is at most the original one, and it now lies in `L_p`
(`MeasureTheory.eLpNorm_lqNorm_ne_top_of_finite`), so
`Rd.IsCZFamily.eLpNorm_sum_conv_le_of_lt_of_measurable` applies. -/
theorem IsCZFamily.eLpNorm_sum_conv_le_of_lt [Nontrivial V] (h : IsCZFamily θ B H)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hp2 : p < 2) (s : Finset ℕ) {g : ℕ → V → ℂ}
    (hg : ∀ j, MemLp (g j) p volume) :
    eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) p volume ≤
      czConstBelow V p B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume := by
  classical
  let g' : ℕ → V → ℂ := fun j => if j ∈ s then (hg j).aestronglyMeasurable.mk (g j) else 0
  have hm : ∀ j, Measurable (g' j) := fun j => by
    by_cases hj : j ∈ s
    · simpa only [g', hj, ↓reduceIte] using
        (hg j).aestronglyMeasurable.stronglyMeasurable_mk.measurable
    · simpa only [g', hj, ↓reduceIte] using measurable_zero
  have hmem : ∀ j, MemLp (g' j) p volume := fun j => by
    by_cases hj : j ∈ s
    · simpa only [g', hj, ↓reduceIte] using (hg j).ae_eq (hg j).aestronglyMeasurable.ae_eq_mk
    · simpa only [g', hj, ↓reduceIte] using (MemLp.zero : MemLp (0 : V → ℂ) p volume)
  have hconv : ∀ j ∈ s, conv (θ j) (g' j) volume = conv (θ j) (g j) volume := fun j hj => by
    simp only [g', hj, ↓reduceIte]
    exact conv_congr_ae (hg j).aestronglyMeasurable.ae_eq_mk.symm
  have hle : eLpNorm (fun x => lqNorm 2 fun j => ‖g' j x‖ₑ) p volume ≤
      eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume := by
    refine eLpNorm_mono_eNorm_ae (aemeasurable_lqNorm_comp (fun j =>
      (hm j).eNorm.aemeasurable) 2).aestronglyMeasurable ?_
    filter_upwards [ae_all_iff.2 fun j => (hg j).aestronglyMeasurable.ae_eq_mk] with x hx
    simp only [eNorm_eq_self]
    refine ENNReal.lqNorm_mono fun j => ?_
    by_cases hj : j ∈ s
    · simp only [g', hj, ↓reduceIte]
      rw [← hx j]
    · simp only [g', hj, ↓reduceIte, Pi.zero_apply, eNorm_zero]
      exact zero_le
  have hfin := eLpNorm_lqNorm_ne_top_of_finite hp1.le s hmem fun j hj => by
    simp only [g', hj, ↓reduceIte]
  calc eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) p volume
      = eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g' j) volume x) p volume := by
        congr 1
        funext x
        exact Finset.sum_congr rfl fun j hj => by rw [hconv j hj]
    _ ≤ czConstBelow V p B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g' j x‖ₑ) p volume :=
        h.eLpNorm_sum_conv_le_of_lt_of_measurable hp1 hp2 s hm hfin
    _ ≤ czConstBelow V p B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume := by
        gcongr

/-! ### The case `2 < p < ∞` by duality -/

/-- **Pairing the analysis operator with a family**: in dimension `n ≥ 1`, for conjugate
exponents `p, q` with `1 < q < 2`, every `f ∈ L_p(V)`, every finite set `s` and all
`g_j ∈ L_q(V)`,
`|∑_{j ∈ s} ∫ (θ_j ⋆ f) conj g_j| ≤ Rd.czConstBelow V q B H ‖f‖_p ‖ ‖(g_j)_j‖_{ℓ_2} ‖_q`: the
adjoint identity `Rd.integral_conv_mul_conj` moves every `θ_j` to `g_j` as the adjoint kernel
`θ_j^*`, Hölder's inequality and the synthesis bound for the adjoint family at `q` finish. -/
theorem IsCZFamily.enorm_sum_integral_conv_mul_conj_le [Nontrivial V] (h : IsCZFamily θ B H)
    {p q : ℝ≥0∞} [p.HolderConjugate q] (hq1 : 1 < q) (hq2 : q < 2) {f : V → ℂ}
    (hf : MemLp f p volume) (s : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) q volume) :
    ‖∑ j ∈ s, ∫ x, conv (θ j) f volume x * conj (g j x)‖ₑ ≤
      czConstBelow V q B H * eLpNorm f p volume *
        eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) q volume := by
  have hp : p ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).2 hq1).ne
  have hq : q ≠ ∞ := ne_top_of_lt hq2
  have hS : MemLp (fun y => ∑ j ∈ s, conv (fun z => conj (θ j (-z))) (g j) volume y) q volume :=
    memLp_finsetSum s fun j _ => memLp_conv hq1.le (h.adjoint.integrable j) (hg j)
  calc ‖∑ j ∈ s, ∫ x, conv (θ j) f volume x * conj (g j x)‖ₑ
      = ‖∫ y, f y * conj (∑ j ∈ s, conv (fun z => conj (θ j (-z))) (g j) volume y)‖ₑ := by
        rw [Finset.sum_congr rfl fun j _ => integral_conv_mul_conj hp (h.integrable j) hf (hg j),
          ← integral_finsetSum (f := fun j y =>
            f y * conj (conv (fun z => conj (θ j (-z))) (g j) volume y)) s fun j _ =>
            hf.integrable_mul
            (memLp_conv hq1.le (h.adjoint.integrable j) (hg j)).star]
        simp only [map_sum, Finset.mul_sum]
    _ ≤ ∫⁻ y, ‖f y‖ₑ * ‖∑ j ∈ s, conv (fun z => conj (θ j (-z))) (g j) volume y‖ₑ := by
        refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
        simp only [eNorm_mul, RCLike.eNorm_conj]
    _ ≤ eLpNorm f p volume *
          eLpNorm (fun y => ∑ j ∈ s, conv (fun z => conj (θ j (-z))) (g j) volume y) q volume := by
        rw [← eLpNorm_eNorm _ hf.aestronglyMeasurable, ← eLpNorm_eNorm _ hS.aestronglyMeasurable]
        exact lintegral_mul_le_eLpNorm_mul_eLpNorm hp hq hf.aestronglyMeasurable.eNorm
          hS.aestronglyMeasurable.eNorm
    _ ≤ eLpNorm f p volume *
          (czConstBelow V q B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) q volume) := by
        gcongr
        exact h.adjoint.eLpNorm_sum_conv_le_of_lt hq1 hq2 s hg
    _ = _ := by ring

/-- **Pairing a synthesis sum with a function**: in dimension `n ≥ 1`, for conjugate exponents
`p, q` with `1 < q < 2`, every finite set `s`, all `g_j ∈ L_p(V)` and every
`u ∈ L_q(V)`,
`|∫ (∑_{j ∈ s} θ_j ⋆ g_j) conj u| ≤ Rd.czConstBelow V q B H ‖ ‖(g_j)_j‖_{ℓ_2} ‖_p ‖u‖_q`: the
adjoint identity `Rd.integral_conv_mul_conj` for every `j`, the Cauchy–Schwarz inequality over
`j ∈ s` at every point (`ENNReal.sum_mul_le_lqNorm_two_mul`), Hölder's inequality and the
analysis bound for the adjoint family at `q`. -/
theorem IsCZFamily.enorm_integral_sum_conv_mul_conj_le [Nontrivial V] (h : IsCZFamily θ B H)
    {p q : ℝ≥0∞} [p.HolderConjugate q] (hq1 : 1 < q) (hq2 : q < 2)
    (s : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) p volume) {u : V → ℂ}
    (hu : MemLp u q volume) :
    ‖∫ x, (∑ j ∈ s, conv (θ j) (g j) volume x) * conj (u x)‖ₑ ≤
      czConstBelow V q B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume *
        eLpNorm u q volume := by
  have hp : p ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).2 hq1).ne
  have hq : q ≠ ∞ := ne_top_of_lt hq2
  have hp1 : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hw : ∀ j, AEStronglyMeasurable (conv (fun z => conj (θ j (-z))) u volume) volume :=
    fun j => aestronglyMeasurable_conv (h.adjoint.integrable j).1 hu.aestronglyMeasurable
  have hGm : AEMeasurable (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) volume :=
    aemeasurable_lqNorm_comp (fun j => (hg j).aestronglyMeasurable.eNorm) 2
  have hWm : AEMeasurable
      (fun x => lqNorm 2 fun j => ‖conv (fun z => conj (θ j (-z))) u volume x‖ₑ) volume :=
    aemeasurable_lqNorm_comp (fun j => (hw j).eNorm) 2
  calc ‖∫ x, (∑ j ∈ s, conv (θ j) (g j) volume x) * conj (u x)‖ₑ
      = ‖∑ j ∈ s, ∫ y, g j y * conj (conv (fun z => conj (θ j (-z))) u volume y)‖ₑ := by
        simp_rw [Finset.sum_mul]
        rw [integral_finsetSum (f := fun j x => conv (θ j) (g j) volume x * conj (u x)) s
          fun j _ =>
          (memLp_conv hp1 (h.integrable j) (hg j)).integrable_mul hu.star]
        rw [Finset.sum_congr rfl fun j _ => integral_conv_mul_conj hp (h.integrable j) (hg j) hu]
    _ ≤ ∑ j ∈ s, ∫⁻ y, ‖g j y‖ₑ * ‖conv (fun z => conj (θ j (-z))) u volume y‖ₑ := by
        refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
        simp only [eNorm_mul, RCLike.eNorm_conj]
    _ = ∫⁻ y, ∑ j ∈ s, ‖g j y‖ₑ * ‖conv (fun z => conj (θ j (-z))) u volume y‖ₑ :=
        (lintegral_finsetSum' s fun j _ => (hg j).aestronglyMeasurable.eNorm.mul (hw j).eNorm).symm
    _ ≤ ∫⁻ y, (lqNorm 2 fun j => ‖g j y‖ₑ) *
          lqNorm 2 fun j => ‖conv (fun z => conj (θ j (-z))) u volume y‖ₑ :=
        lintegral_mono fun y => ENNReal.sum_mul_le_lqNorm_two_mul s _ _
    _ ≤ eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume *
          eLpNorm (fun x => lqNorm 2 fun j =>
            ‖conv (fun z => conj (θ j (-z))) u volume x‖ₑ) q volume :=
        lintegral_mul_le_eLpNorm_mul_eLpNorm hp hq hGm hWm
    _ ≤ eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume *
          (czConstBelow V q B H * eLpNorm u q volume) := by
        gcongr
        exact h.adjoint.eLpNorm_lqNorm_conv_le_of_lt hq1 hq2 hu
    _ = _ := by ring

/-- **The analysis bound for `2 < p < ∞`**, in dimension `n ≥ 1`:
`‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ Rd.czConstBelow V p' B H ‖f‖_p` for every `f ∈ L_p(V)`,
with the conjugate exponent `p' = p.conjExponent < 2`. For every `J`, the duality
`MeasureTheory.eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le` with
`Rd.IsCZFamily.enorm_sum_integral_conv_mul_conj_le` bounds the `ℓ_2` norm over `j < J`, and
these increase to the full `ℓ_2` norm (`ENNReal.lqNorm_eq_iSup_lqNorm_ite`). -/
theorem IsCZFamily.eLpNorm_lqNorm_conv_le_of_two_lt [Nontrivial V] (h : IsCZFamily θ B H)
    {p : ℝ≥0∞} (hp2 : 2 < p) (hp : p ≠ ∞) {f : V → ℂ} (hf : MemLp f p volume) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) p volume ≤
      czConstBelow V p.conjExponent B H * eLpNorm f p volume := by
  have hp1 : 1 < p := ENNReal.one_lt_two.trans hp2
  have : p.HolderConjugate p.conjExponent := ENNReal.HolderConjugate.conjExponent hp1.le
  have hq1 : 1 < p.conjExponent := (ENNReal.HolderConjugate.lt_top_iff_one_lt p _).1 hp.lt_top
  have hq2 : p.conjExponent < 2 := ENNReal.HolderConjugate.lt_two_of_two_lt hp2
  have hJ : ∀ J : ℕ, eLpNorm (fun x => lqNorm 2 fun j =>
      ‖(if j < J then conv (θ j) f volume x else 0)‖ₑ) p volume ≤
        czConstBelow V p.conjExponent B H * eLpNorm f p volume := fun J => by
    refine eLpNorm_lqNorm_le_of_forall_enorm_sum_integral_le (q := p.conjExponent) hp1 hp
      (Finset.range J)
      (u := fun j x => if j < J then conv (θ j) f volume x else 0) (fun j => ?_)
      (fun j hj => ?_) fun g hg => ?_
    · by_cases hj : j < J
      · simpa only [hj, ↓reduceIte] using memLp_conv hp1.le (h.integrable j) hf
      · simp [hj]
    · funext x
      simp only [Finset.mem_range.not.1 hj, ↓reduceIte, Pi.zero_apply]
    · have hs : ∀ j ∈ Finset.range J,
          (∫ x, (if j < J then conv (θ j) f volume x else 0) * conj (g j x)) =
            ∫ x, conv (θ j) f volume x * conj (g j x) := fun j hj => by
        simp only [Finset.mem_range.1 hj, ↓reduceIte]
      exact le_of_eq_of_le (congrArg _ (Finset.sum_congr rfl hs))
        (h.enorm_sum_integral_conv_mul_conj_le hq1 hq2 hf _ hg)
  have hpt : ∀ x, (lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) =
      ⨆ J : ℕ, lqNorm 2 fun j => if j < J then ‖conv (θ j) f volume x‖ₑ else 0 := fun x =>
    ENNReal.lqNorm_eq_iSup_lqNorm_ite _
  have hmono : Monotone fun (J : ℕ) (x : V) =>
      lqNorm 2 fun j => if j < J then ‖conv (θ j) f volume x‖ₑ else 0 := fun J J' hJJ' x =>
    ENNReal.lqNorm_mono fun j =>
      ENNReal.monotone_ite_lt (fun j => ‖conv (θ j) f volume x‖ₑ) hJJ' j
  have hm : ∀ J j : ℕ, AEMeasurable
      (fun x => if j < J then ‖conv (θ j) f volume x‖ₑ else 0) volume := fun J j => by
    split_ifs
    exacts [(aestronglyMeasurable_conv (h.integrable j).1 hf.aestronglyMeasurable).eNorm,
      aemeasurable_const]
  simp_rw [hpt]
  rw [eLpNorm_iSup_of_directed (fun J => aemeasurable_lqNorm_comp (hm J) 2) hmono.directed_le p]
  refine iSup_le fun J => le_of_eq_of_le ?_ (hJ J)
  congr 1
  funext x
  simp_rw [apply_ite (fun z : ℂ => ‖z‖ₑ), eNorm_zero]

/-- **The synthesis bound for `2 < p < ∞`**, in dimension `n ≥ 1`: for every finite set `s` and
all `g_j ∈ L_p(V)`,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ Rd.czConstBelow V p' B H ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p` with the
conjugate exponent `p' = p.conjExponent < 2`, by the duality
`MeasureTheory.eLpNorm_le_of_forall_enorm_integral_mul_conj_le` and
`Rd.IsCZFamily.enorm_integral_sum_conv_mul_conj_le`. -/
theorem IsCZFamily.eLpNorm_sum_conv_le_of_two_lt [Nontrivial V] (h : IsCZFamily θ B H)
    {p : ℝ≥0∞} (hp2 : 2 < p) (hp : p ≠ ∞) (s : Finset ℕ) {g : ℕ → V → ℂ}
    (hg : ∀ j, MemLp (g j) p volume) :
    eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) p volume ≤
      czConstBelow V p.conjExponent B H *
        eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume := by
  have hp1 : 1 < p := ENNReal.one_lt_two.trans hp2
  have : p.HolderConjugate p.conjExponent := ENNReal.HolderConjugate.conjExponent hp1.le
  have hq1 : 1 < p.conjExponent := (ENNReal.HolderConjugate.lt_top_iff_one_lt p _).1 hp.lt_top
  have hq2 : p.conjExponent < 2 := ENNReal.HolderConjugate.lt_two_of_two_lt hp2
  exact eLpNorm_le_of_forall_enorm_integral_mul_conj_le hp1 hp
    (memLp_finsetSum s fun j _ => memLp_conv hp1.le (h.integrable j) (hg j)) fun u hu =>
      h.enorm_integral_sum_conv_mul_conj_le hq1 hq2 s hg hu

/-! ### All `1 < p < ∞` -/

variable (V) in
/-- The constant of the strong type `(p, p)`, `1 < p < ∞`, of a Calderón–Zygmund family with
overlap `B` and Hörmander constant `H`: `B^{1/2}` for `p = 2`, `Rd.czConstBelow V p B H` for
`p < 2`, and `Rd.czConstBelow V p' B H` with the conjugate exponent `p'` for `p > 2`. -/
noncomputable def czConst (p B H : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 2 then B ^ (1 / 2 : ℝ) else if p < 2 then czConstBelow V p B H
  else czConstBelow V p.conjExponent B H

/-- The constant `Rd.czConst V p B H` is finite for `1 < p < ∞` and finite `B`, `H`. -/
theorem czConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hB : B ≠ ∞) (hH : H ≠ ∞) :
    czConst V p B H ≠ ∞ := by
  unfold czConst
  split_ifs with h2 hlt
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB
  · exact czConstBelow_ne_top hp1 hlt hB hH
  · have hgt : 2 < p := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm h2)
    have : p.HolderConjugate p.conjExponent := ENNReal.HolderConjugate.conjExponent hp1.le
    exact czConstBelow_ne_top ((ENNReal.HolderConjugate.lt_top_iff_one_lt p _).1 hp.lt_top)
      (ENNReal.HolderConjugate.lt_two_of_two_lt hgt) hB hH

/-- **The strong type of the analysis operator**: in dimension `n ≥ 1`, for a Calderón–Zygmund
family with overlap `B` and Hörmander constant `H`, every `1 < p < ∞` and every `f ∈ L_p(V)`,
`‖ ‖((θ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ Rd.czConst V p B H ‖f‖_p`: the Plancherel bound for `p = 2`,
Marcinkiewicz interpolation for `p < 2` and duality for `p > 2`. -/
theorem IsCZFamily.eLpNorm_lqNorm_conv_le [Nontrivial V] (h : IsCZFamily θ B H) {p : ℝ≥0∞}
    (hp1 : 1 < p) (hp : p ≠ ∞) {f : V → ℂ} (hf : MemLp f p volume) :
    eLpNorm (fun x => lqNorm 2 fun j => ‖conv (θ j) f volume x‖ₑ) p volume ≤
      czConst V p B H * eLpNorm f p volume := by
  rcases lt_trichotomy p 2 with hlt | rfl | hgt
  · simp only [czConst, hlt.ne, hlt, ↓reduceIte]
    exact h.eLpNorm_lqNorm_conv_le_of_lt hp1 hlt hf
  · simp only [czConst, ↓reduceIte]
    exact h.eLpNorm_lqNorm_conv_two_le hf
  · simp only [czConst, hgt.ne', not_lt.2 hgt.le, ↓reduceIte]
    exact h.eLpNorm_lqNorm_conv_le_of_two_lt hgt hp hf

/-- **The strong type of the synthesis operators**: in dimension `n ≥ 1`, for a
Calderón–Zygmund family with overlap `B` and Hörmander constant `H`, every `1 < p < ∞`, every
finite set `s` and all `g_j ∈ L_p(V)`,
`‖∑_{j ∈ s} θ_j ⋆ g_j‖_p ≤ Rd.czConst V p B H ‖ ‖(g_j(x))_j‖_{ℓ_2} ‖_p`: the Plancherel bound
for `p = 2`, Marcinkiewicz interpolation for `p < 2` and duality for `p > 2`. -/
theorem IsCZFamily.eLpNorm_sum_conv_le [Nontrivial V] (h : IsCZFamily θ B H) {p : ℝ≥0∞}
    (hp1 : 1 < p) (hp : p ≠ ∞) (s : Finset ℕ) {g : ℕ → V → ℂ} (hg : ∀ j, MemLp (g j) p volume) :
    eLpNorm (fun x => ∑ j ∈ s, conv (θ j) (g j) volume x) p volume ≤
      czConst V p B H * eLpNorm (fun x => lqNorm 2 fun j => ‖g j x‖ₑ) p volume := by
  rcases lt_trichotomy p 2 with hlt | rfl | hgt
  · simp only [czConst, hlt.ne, hlt, ↓reduceIte]
    exact h.eLpNorm_sum_conv_le_of_lt hp1 hlt s hg
  · simp only [czConst, ↓reduceIte]
    exact h.eLpNorm_sum_conv_two_le s hg
  · simp only [czConst, hgt.ne', not_lt.2 hgt.le, ↓reduceIte]
    exact h.eLpNorm_sum_conv_le_of_two_lt hgt hp s hg

end Rd
