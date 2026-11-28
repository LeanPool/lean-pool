/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.LipschitzGraph

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Rychkov's extension

Let `b` be a bump for local means with kernels `k_j` and dual kernels `η_j`, and `W ⊆ V`
measurable. For `f ∈ L_p(V)`, `1 ≤ p < ∞`, the **local extension**
(`Rd.LocalMeansBump.localExtension`) is `F = ∑_j η_j ⋆ 1_W (k_j ⋆ f)`. If the local means
quasi-norm on `W`, `‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q}` (`Rd.LocalMeansBump.localNormOn`), is
finite and `s > 0`, the series converges absolutely (`Rd.LocalMeansBump.summable_localExtTerm`;
a bound `2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X < ∞` suffices,
`Rd.LocalMeansBump.summable_localExtTerm_of_forall_le`), and by the synthesis estimate of local
means `‖F‖_p + ‖(2^(is) ω_L(F, 2^(-i))_p)_i‖_{ℓ_q}` is at most a constant times that quasi-norm
(`Rd.LocalMeansBump.modNorm_localExtension_le`). If `L ≥ 1` and `x - y ∈ W` for `x ∈ U` and
`η_j(y) ≠ 0`, then `F = f` on `U` (`Rd.LocalMeansBump.indicatorLp_localExtension`): by the
support principle for two sets (`Rd.indicatorLp_convLp_indicatorLp`), on `U` the partial sums are
those of the reproducing formula `∑_{j ≤ J} η_j ⋆ k_j ⋆ f → f`. The terms are linear in `f`
(`Rd.LocalMeansBump.localExtTerm_add`, `Rd.LocalMeansBump.localExtTerm_smul`).

**Rychkov's extension** (`Rd.LipschitzGraph.extension`) for a Lipschitz graph domain `Ω` with
cone `K` and `L ≥ 1` is the local extension of the cone bump for `W = Ω`,

`Ext f = ∑_j η_j ⋆ (1_Ω (k_j ⋆ f))`.

Its quasi-norm on `Ω` is the **intrinsic local means quasi-norm**
`‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}` (`Rd.LipschitzGraph.intrinsicNorm`), which depends only on
`f` on `Ω` (`Rd.LipschitzGraph.intrinsicNorm_congr`). The kernels of the cone bump are supported in
`-K`, so `x - y ∈ x + K ⊆ Ω` for `x ∈ Ω` and `η_j(y) ≠ 0`, and `Ext f = f` on `Ω`
(`Rd.LipschitzGraph.cutoff_extension`); for `0 < s < L`,
`‖Ext f‖_p + ‖(2^(is) ω_L(Ext f, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`
(`Rd.LipschitzGraph.modNorm_extension_le`).

**Restrictions** (`Rd.LipschitzGraph.exists_besov_extension_iff`): for `0 < s < L`, `f` agrees on
`Ω` with some `F ∈ L_p(V)` satisfying the Besov condition by differences iff the intrinsic
quasi-norm of `f` is finite, and `Ext f` is such an `F`. The construction does not depend on `s`:
one operator serves all `0 < s < L`.
-/

@[expose] public section

open MeasureTheory Filter Topology Module
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The local extension -/

namespace LocalMeansBump

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : LocalMeansBump V)

/-- The **local means quasi-norm on a set** `‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
noncomputable def localNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ) (s : ℝ)
    (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ)

/-- The terms `η_j ⋆ 1_W (k_j ⋆ f)` of the local extension. -/
noncomputable def localExtTerm (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) : Lp ℂ p (volume : Measure V) :=
  convLp hp (b.integrable_dual L j) (indicatorLp hW (b.localMean hp L j f))

/-- The terms of the local extension are additive in `f`. -/
theorem localExtTerm_add (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L j : ℕ)
    (f g : Lp ℂ p (volume : Measure V)) :
    b.localExtTerm hp hW L j (f + g) = b.localExtTerm hp hW L j f + b.localExtTerm hp hW L j g := by
  simp only [localExtTerm, map_add]

/-- The terms of the local extension commute with complex scalars. -/
theorem localExtTerm_smul (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L j : ℕ) (c : ℂ)
    (f : Lp ℂ p (volume : Measure V)) :
    b.localExtTerm hp hW L j (c • f) = c • b.localExtTerm hp hW L j f := by
  simp only [localExtTerm, map_smul]

/-- The **local extension** `∑_j η_j ⋆ 1_W (k_j ⋆ f)`. -/
noncomputable def localExtension (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    (f : Lp ℂ p (volume : Measure V)) : Lp ℂ p (volume : Measure V) :=
  ∑' j, b.localExtTerm hp hW L j f

/-- **The terms of the local extension from a bound on the weighted local means**: if
`2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X` for every `j`, then `‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 2^(-js) X`. -/
theorem enorm_localExtTerm_le_of_forall_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} {f : Lp ℂ p (volume : Measure V)} {X : ℝ≥0∞}
    (hX : ∀ j, dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ X) (j : ℕ) :
    ‖b.localExtTerm hp hW L j f‖ₑ ≤
      2 * eLpNorm (momentKernel b.toFun L) 1 volume * (dyadicWeight (-s) j * X) :=
  calc ‖b.localExtTerm hp hW L j f‖ₑ
      ≤ eLpNorm (b.dual L j) 1 volume * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ :=
        enorm_convLp_le hp _ _
    _ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume * (dyadicWeight (-s) j *
          (dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ)) := by
        rw [← mul_assoc (dyadicWeight (-s) j), ENNReal.dyadicWeight_neg_mul_self, one_mul]
        exact mul_le_mul' (b.eLpNorm_dual_one_le L j) le_rfl
    _ ≤ _ := by gcongr; exact hX j

/-- **The sum of the norms of the terms**: if `2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X` for every `j`, then
`∑_j ‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 (1 - 2^(-s))⁻¹ X`
(`Rd.LocalMeansBump.enorm_localExtTerm_le_of_forall_le`, `ENNReal.tsum_dyadicWeight_neg`). -/
theorem tsum_enorm_localExtTerm_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} {f : Lp ℂ p (volume : Measure V)} {X : ℝ≥0∞}
    (hX : ∀ j, dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ X) :
    ∑' j, ‖b.localExtTerm hp hW L j f‖ₑ ≤
      2 * eLpNorm (momentKernel b.toFun L) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * X := by
  refine (tsum_le_tsum (b.enorm_localExtTerm_le_of_forall_le hp hW L hX)).trans_eq ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_dyadicWeight_neg]
  ring

/-- **The local extension converges absolutely** for `s > 0` if
`2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X < ∞` for every `j`
(`Rd.LocalMeansBump.tsum_enorm_localExtTerm_le`). -/
theorem summable_localExtTerm_of_forall_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} (hs : 0 < s) {f : Lp ℂ p (volume : Measure V)} {X : ℝ≥0∞} (hXf : X ≠ ∞)
    (hX : ∀ j, dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ X) :
    Summable fun j => b.localExtTerm hp hW L j f := by
  have htsum : ∑' j, ‖b.localExtTerm hp hW L j f‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (eLpNorm_momentKernel_ne_top b.integrable L))
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs)) hXf) (b.tsum_enorm_localExtTerm_le hp hW L hX)
  exact Summable.of_eNorm htsum

/-- **The local extension converges absolutely** for `s > 0` and a finite local means
quasi-norm on `W`: `‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 2^(-js) ‖f‖_W`
(`Rd.LocalMeansBump.summable_localExtTerm_of_forall_le`). -/
theorem summable_localExtTerm (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ) {s : ℝ}
    (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.localNormOn hp hW L s q f < ∞) : Summable fun j => b.localExtTerm hp hW L j f :=
  b.summable_localExtTerm_of_forall_le hp hW L hs hf.ne fun j =>
    ENNReal.le_lqNorm (zero_lt_one.trans_le hq).ne'
      (fun j => dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ) j

/-- The partial sums of the local extension converge to it if its terms are summable. -/
theorem tendsto_sum_localExtTerm_of_summable (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {f : Lp ℂ p (volume : Measure V)}
    (hsum : Summable fun j => b.localExtTerm hp hW L j f) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), b.localExtTerm hp hW L j f) atTop
      (𝓝 (b.localExtension hp hW L f)) :=
  (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

/-- The partial sums of the local extension converge to it. -/
theorem tendsto_sum_localExtTerm (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.localNormOn hp hW L s q f < ∞) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), b.localExtTerm hp hW L j f) atTop
      (𝓝 (b.localExtension hp hW L f)) :=
  b.tendsto_sum_localExtTerm_of_summable hp hW L (b.summable_localExtTerm hp hW L hs hq hf)

/-- **The local extension satisfies the Besov condition by differences**: for `0 < s`,
`‖F‖_p + ‖(2^(is) ω_L(F, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖1_W (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
theorem modNorm_localExtension_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.localNormOn hp hW L s q f < ∞) :
    ‖b.localExtension hp hW L f‖ₑ +
        lqNorm q (fun i => dyadicWeight s i * lpModulus p L (b.localExtension hp hW L f) i) ≤
      b.synthConst L s * b.localNormOn hp hW L s q f :=
  b.modNorm_le_of_tendsto hp L s hq (b.tendsto_sum_localExtTerm hp hW L hs hq hf)

/-- **The local extension agrees with `f` on `U`** if its terms are summable and the dual kernels
at points of `U` only see `W`: on `U` the terms are those of the reproducing formula. -/
theorem indicatorLp_localExtension_of_summable (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W) {f : Lp ℂ p (volume : Measure V)}
    (hsum : Summable fun j => b.localExtTerm hp hW L j f) :
    indicatorLp hU (b.localExtension hp hW L f) = indicatorLp hU f := by
  have hsum' : ∀ J, indicatorLp hU (∑ j ∈ Finset.range (J + 1), b.localExtTerm hp hW L j f) =
      indicatorLp hU (∑ j ∈ Finset.range (J + 1),
        convLp hp (b.integrable_dual L j) (b.localMean hp L j f)) := fun J => by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      indicatorLp_convLp_indicatorLp hp _ hU hW (fun x hx y hy => hUW x hx j y hy) _
  have h1 : Tendsto (fun J => indicatorLp hU (∑ j ∈ Finset.range (J + 1),
      b.localExtTerm hp hW L j f)) atTop (𝓝 (indicatorLp hU (b.localExtension hp hW L f))) :=
    ((indicatorLp hU).continuous.tendsto _).comp
      (b.tendsto_sum_localExtTerm_of_summable hp hW L hsum)
  have h2 : Tendsto (fun J => indicatorLp hU (∑ j ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L j) (b.localMean hp L j f))) atTop (𝓝 (indicatorLp hU f)) :=
    ((indicatorLp hU).continuous.tendsto _).comp (b.tendsto_sum_dual_localMean hp hL f)
  simp_rw [hsum'] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The local extension agrees with `f` on `U`** if the dual kernels at points of `U` only see
`W`: on `U` the terms are those of the reproducing formula. -/
theorem indicatorLp_localExtension (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {U W : Set V}
    (hU : MeasurableSet U) (hW : MeasurableSet W)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} (hf : b.localNormOn hp hW L s q f < ∞) :
    indicatorLp hU (b.localExtension hp hW L f) = indicatorLp hU f :=
  b.indicatorLp_localExtension_of_summable hp hL hU hW hUW
    (b.summable_localExtTerm hp hW L hs hq hf)

end LocalMeansBump

/-! ### Rychkov's extension for Lipschitz graph domains -/

namespace LipschitzGraph

variable (Ω : LipschitzGraph V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The terms `η_j ⋆ (1_Ω (k_j ⋆ f))` of the extension: the terms of the local extension of the
cone bump for `W = Ω`. -/
noncomputable def extTerm (hp : p ≠ ∞) (L j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure V) :=
  Ω.coneBump.localExtTerm hp Ω.measurableSet_domain L j f

/-- The **intrinsic local means quasi-norm** `‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`: the local
means quasi-norm of the cone bump on `Ω`. -/
noncomputable def intrinsicNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  Ω.coneBump.localNormOn hp Ω.measurableSet_domain L s q f

/-- The intrinsic quasi-norm written with the cut-off:
`‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
theorem intrinsicNorm_def (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    Ω.intrinsicNorm hp L s q f =
      lqNorm q (fun j => dyadicWeight s j * ‖Ω.cutoff (Ω.coneBump.localMean hp L j f)‖ₑ) :=
  rfl

/-- **The intrinsic quasi-norm depends only on `f` on `Ω`**: the kernels `k_j` are supported in
`-K` (the support principle). -/
theorem intrinsicNorm_congr (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    {F f : Lp ℂ p (volume : Measure V)} (hFf : Ω.cutoff F = Ω.cutoff f) :
    Ω.intrinsicNorm hp L s q F = Ω.intrinsicNorm hp L s q f := by
  rw [intrinsicNorm_def, intrinsicNorm_def]
  congr 1
  funext j
  exact congrArg (fun g => dyadicWeight s j * ‖g‖ₑ)
    (Ω.cutoff_convLp_eq hp (Ω.coneBump.integrable_kernel L j) (Ω.coneSupported_kernel L j) hFf)

/-- The intrinsic quasi-norm is at most the local means quasi-norm. -/
theorem intrinsicNorm_le_localMeansNorm (hp : p ≠ ∞) (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    Ω.intrinsicNorm hp L s q f ≤ Ω.coneBump.localMeansNorm hp L s q f :=
  ENNReal.lqNorm_mono fun _ => mul_le_mul' le_rfl (enorm_indicatorLp_le _ _)

/-- **The extension converges absolutely** for `s > 0` and a finite intrinsic quasi-norm:
`‖η_j ⋆ (1_Ω (k_j ⋆ f))‖_p ≤ 2 ‖m‖_1 2^(-js) ‖f‖_intr`
(`Rd.LocalMeansBump.summable_localExtTerm`). -/
theorem summable_extTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    Summable fun j => Ω.extTerm hp L j f :=
  Ω.coneBump.summable_localExtTerm hp Ω.measurableSet_domain L hs hq hf

/-- **Rychkov's extension** `Ext f = ∑_j η_j ⋆ (1_Ω (k_j ⋆ f))`: the local extension of the cone
bump for `W = Ω`. -/
noncomputable def extension (hp : p ≠ ∞) (L : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ p (volume : Measure V) :=
  Ω.coneBump.localExtension hp Ω.measurableSet_domain L f

/-- The partial sums of the extension converge to it. -/
theorem tendsto_sum_extTerm (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), Ω.extTerm hp L j f) atTop
      (𝓝 (Ω.extension hp L f)) :=
  Ω.coneBump.tendsto_sum_localExtTerm hp Ω.measurableSet_domain L hs hq hf

/-- **The extension agrees with `f` on `Ω`**: `1_Ω Ext f = 1_Ω f`. The dual kernels at points of
`Ω` only see `Ω`, since they are supported in `-K` (`Rd.LocalMeansBump.indicatorLp_localExtension`
for `U = W = Ω`). -/
theorem cutoff_extension (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    Ω.cutoff (Ω.extension hp L f) = Ω.cutoff f :=
  Ω.coneBump.indicatorLp_localExtension hp hL Ω.measurableSet_domain Ω.measurableSet_domain
    (fun _ hx j _ hy => (Ω.coneSupported_dual L j).sub_mem hx hy) hs hq hf

/-- **The extension satisfies the Besov condition by differences**: for `0 < s < L`,
`‖Ext f‖_p + ‖(2^(is) ω_L(Ext f, 2^(-i))_p)_i‖_{ℓ_q} ≤ C ‖(2^(js) ‖1_Ω (k_j ⋆ f)‖_p)_j‖_{ℓ_q}`. -/
theorem modNorm_extension_le (hp : p ≠ ∞) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : Ω.intrinsicNorm hp L s q f < ∞) :
    ‖Ω.extension hp L f‖ₑ +
        lqNorm q (fun i => dyadicWeight s i * lpModulus p L (Ω.extension hp L f) i) ≤
      Ω.coneBump.synthConst L s * Ω.intrinsicNorm hp L s q f :=
  Ω.coneBump.modNorm_localExtension_le hp Ω.measurableSet_domain L hs hq hf

/-- **Restrictions of Besov spaces to Lipschitz graph domains**: for `1 ≤ p < ∞`, `0 < s < L` and
`1 ≤ q ≤ ∞`, `f` agrees on `Ω` with some `F ∈ L_p(V)` with
`‖F‖_p + ‖(2^(ks) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} < ∞` iff the intrinsic local means quasi-norm of `f`
is finite; `F = Ext f` is such a function. -/
theorem exists_besov_extension_iff (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s)
    (hsL : s < L) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (∃ F : Lp ℂ p (volume : Measure V), Ω.cutoff F = Ω.cutoff f ∧
        ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L F k) < ∞) ↔
      Ω.intrinsicNorm hp L s q f < ∞ := by
  constructor
  · rintro ⟨F, hFf, hF⟩
    rw [← Ω.intrinsicNorm_congr hp L s q hFf]
    exact (Ω.intrinsicNorm_le_localMeansNorm hp L s q F).trans_lt
      ((Ω.coneBump.localMeansNorm_le hp L s hq F).trans_lt
        (ENNReal.mul_lt_top (Ω.coneBump.upperConst_ne_top L s).lt_top hF))
  · intro hf
    exact ⟨Ω.extension hp L f, Ω.cutoff_extension hp hL hs hq hf,
      (Ω.modNorm_extension_le hp L hs hq hf).trans_lt
        (ENNReal.mul_lt_top (Ω.coneBump.synthConst_ne_top hs hsL).lt_top hf)⟩

end LipschitzGraph

end Rd
