/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.DivergenceKernels
public import LeanPool.FunctionSpaces.Domains.Lipschitz.BoundedLipschitz
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans
public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTriebelLizorkin
public import LeanPool.FunctionSpaces.Domains.Sobolev.LipschitzDomainH1
public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevJets
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeLeibniz

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bounded extensions of `W^1_p` by the local means of the gradient

Let `V` be a finite-dimensional real inner product space of dimension `n` and `1 ≤ p ≤ ∞`; the
bounds of the local extension need `1 < p < ∞`. This file holds the estimates behind the extension
theorem of Calderón and Stein in Rychkov's form: the local extension
`∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` of a Sobolev function `f` on an open set `T` lies in `W^1_p(V)`,
with a bound by `‖f‖_{L_p(T)} + ∑_i ‖∂_{e_i} f‖_{L_p(T)}`. The extension operators
(`Rd.SobolevExtensionOp`, `Rd.BoundedLipschitzDomain.exists_sobolevExtensionOp`) and the
extension theorem itself (`Rd.BoundedLipschitzDomain.exists_extendsSobolev`) are built from it.

* **Local means by the gradient**: for a bump with moment kernel `m` of order two, the local
  means kernels are divergences, `k_{j+1} = 2^(-j) ∑_i ∂_{e_i} (K_i)_{2^j}` with the divergence
  kernels `K_i` of `m` (`Rd.LocalMeansBump.divKernel`, `Rd.LocalMeansBump.kernel_two_succ_apply`).
  If `g_i = ∂_{e_i} f` weakly on an open set `T` and the kernels at `x` only see `T`, then
  `(k_{j+1} ⋆ 1_T f)(x) = 2^(-j) ∑_i ((K_i)_{2^j} ⋆ 1_T g_i)(x)`
  (`Rd.LocalMeansBump.conv_kernel_two_succ_eq`, by the general identity for kernels that are
  sums of derivatives, `Rd.conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp`), and the
  strong type of the Calderón–Zygmund
  families `((K_i)_{2^j})_j` bounds the local means quasi-norm of Triebel–Lizorkin type on a set
  (`Rd.LocalMeansBump.tlLocalNormOn`) by `‖f‖_{L_p(T)} + ∑_i ‖g_i‖_{L_p(T)}`
  (`Rd.LocalMeansBump.tlLocalNormOn_le_patchConst`). The step from a pointwise bound of the
  local means by convolutions with Schwartz kernels to the quasi-norm holds for every kernel family
  (`Rd.LocalMeansBump.tlLocalNormOn_le_of_pointwise`).
* **One patch**: the local extension lies in `F^1_{p,2}(V) = W^1_p(V)`
  (`Rd.LocalMeansBump.memTriebelLizorkin_localExtension_of_tlLocalNormOn`), agrees with `f` on the
  patch (`Rd.LocalMeansBump.ae_localExtension_eq_of_ae_eq_indicator`) and has the constant
  `Rd.LocalMeansBump.extensionConst`
  (`Rd.LocalMeansBump.enorm_localExtension_add_le_extensionConst`);
  `Rd.ExtendsSobolev p O U C` says that extensions from `U` exist with the constant `C`.
* **Pasting** (`Rd.extendsSobolev_of_cover`): a smooth resolution of unity subordinate to a finite
  cover pastes extensions in `W^1_p(V)`, by the product rule (`Rd.hasWeakLineDeriv_mulLp`), with
  the arithmetic of `Rd.pasting_bound`. Extensions also come from `L_p` bounds alone
  (`Rd.extendsSobolev_of_eLpNorm_le`).
* **Supports and cutoffs**: the dilates of the divergence kernels of a cone bump keep the patches
  inside the domain (`Rd.LipschitzGraph.patch_support_divKernel`), and the patches of a bounded
  Lipschitz domain have smooth cutoffs (`Rd.BoundedLipschitzDomain.exists_cutoff_boundary`,
  `Rd.BoundedLipschitzDomain.exists_cutoff_interior`), which serve the extensions by reflection and
  those of higher order.
* **Dimension zero**: for `n = 0`, every `f ∈ W^m_p(O)` agrees on `O` with `F = f` or `F = 0` in
  `W^m_p(V)` (`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric TopologicalSpace
open scoped ENNReal SchwartzMap FourierTransform LineDeriv Real BesselPotentialSpace

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Convolutions with sums of derivatives -/

/-- **A convolution with a sum of derivatives of dilated kernels**: let `g_i = ∂^{u_i} f` weakly
on an open set `T` with `f ∈ L_p(T)`, let `K_i` be Schwartz functions with compact support, `t ≠ 0`,
and let `κ = c ∑_i ∂^{u_i} (K_i)_t`. If `x - y ∈ T` for every `i` and every `y` in the support of
`(K_i)_t`, then `(κ ⋆ 1_T f)(x) = c ∑_i ((K_i)_t ⋆ 1_T g_i)(x)`: each derivative moves from the
kernel to `1_T f` (`Rd.conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv`). -/
theorem conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {ι : Type*} [Fintype ι] {k : ℕ} {T : Opens V} {f : V → ℂ} {g : ι → V → ℂ}
    {u : ι → Fin k → V} (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (u i) f (g i)) {K : ι → 𝓢(V, ℂ)}
    (hK : ∀ i, HasCompactSupport (K i : V → ℂ)) {t : ℝ} (ht : t ≠ 0) {κ : V → ℂ} {c : ℂ}
    (hκ : ∀ y, κ y = c * ∑ i, (∂^{u i} (schwartzDilate t ht (K i)) : 𝓢(V, ℂ)) y) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate t (K i : V → ℂ)), x - y ∈ T) :
    conv κ ((T : Set V).indicator f) volume x =
      c * ∑ i, conv (dilate t (K i : V → ℂ)) ((T : Set V).indicator (g i)) volume x := by
  have hT := T.isOpen.measurableSet
  have hKc : ∀ i, (schwartzDilate t ht (K i) : V → ℂ) = dilate t (K i) := fun i =>
    coe_schwartzDilate _ _ _
  have hcs : ∀ i, HasCompactSupport (schwartzDilate t ht (K i) : V → ℂ) :=
    fun i => by rw [hKc]; exact hasCompactSupport_dilate (hK i) ht
  have hloc : LocallyIntegrable ((T : Set V).indicator f) volume :=
    ((memLp_indicator_iff_restrict hT.nullMeasurableSet).2 hf).locallyIntegrable Fact.out
  have hfg' : ∀ i, HasWeakLineDeriv T (u i) ((T : Set V).indicator f)
      ((T : Set V).indicator (g i)) := fun i =>
    (hfg i).congr_ae (indicator_ae_eq_restrict hT.nullMeasurableSet).symm
      (indicator_ae_eq_restrict hT.nullMeasurableSet).symm
  have hstep : ∀ i, conv (dilate t (K i : V → ℂ)) ((T : Set V).indicator (g i)) volume x =
      conv (∂^{u i} (schwartzDilate t ht (K i)) : 𝓢(V, ℂ)) ((T : Set V).indicator f) volume x :=
    fun i => by
      rw [← hKc, conv_eq_conv_iteratedLineDerivOp_of_hasWeakLineDeriv (hfg' i) (hcs i)
        (by rw [hKc]; exact hx i)]
  have hint : ∀ i, Integrable fun y => (∂^{u i} (schwartzDilate t ht (K i)) : 𝓢(V, ℂ)) y *
      (T : Set V).indicator f (x - y) := fun i =>
    ((hcs i).mono' ((subset_tsupport _).trans (SchwartzMap.tsupport_iteratedLineDerivOp_subset _
      _))).convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
      (∂^{u i} (schwartzDilate t ht (K i))).continuous hloc x
  rw [Finset.sum_congr rfl fun i _ => hstep i]
  simp only [conv_apply]
  simp_rw [hκ, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]

/-! ### The local means kernels as divergences -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The moment kernel of order two of a bump of radius `R` vanishes outside the ball of radius
`2R`. -/
theorem momentKernel_two_eq_zero {z : V} (hz : 2 * b.radius < ‖z‖) :
    momentKernel b.toFun 2 z = 0 :=
  b.momentKernel_eq_zero 2 (by exact_mod_cast hz)

/-- The **divergence kernels** `K_i` of a bump: the divergence kernels (`Rd.divergenceSchwartz`) of
its moment kernel `m` of order two in the directions of the orthonormal basis `e_i = Rd.gridBasis`,
so that `∑_i ∂_{e_i} K_i = m_2 - m` (`Rd.sum_lineDerivOp_divergenceSchwartz`); at the dyadic scales
this writes the local means kernels as divergences (`Rd.LocalMeansBump.kernel_two_succ_apply`). -/
noncomputable def divKernel (i : Fin (finrank ℝ V)) : 𝓢(V, ℂ) :=
  divergenceSchwartz (b.contDiff_momentKernel 2) (fun _ hz => b.momentKernel_two_eq_zero hz)
    (gridBasis V i)

/-- The divergence kernels of a bump have compact support. -/
theorem hasCompactSupport_divKernel (i : Fin (finrank ℝ V)) :
    HasCompactSupport (b.divKernel i : V → ℂ) :=
  hasCompactSupport_divergenceKernel (fun _ hz => b.momentKernel_two_eq_zero hz) _

/-- The divergence kernels vanish at `y` if the moment kernel vanishes at every `t y`,
`t ∈ [1, 2]`. -/
theorem divKernel_eq_zero (i : Fin (finrank ℝ V)) {y : V}
    (hy : ∀ t : ℝ, 1 ≤ t → t ≤ 2 → momentKernel b.toFun 2 (t • y) = 0) : b.divKernel i y = 0 :=
  divergenceKernel_eq_zero _ hy

/-- **The local means kernels of order two at dyadic scales**: `k_{j+1} = (m_2 - m)_{2^j}`
(`Rd.LocalMeansBump.kernel_succ_eq_dilate`). -/
theorem kernel_two_succ (j : ℕ) :
    b.kernel 2 (j + 1) =
      dilate (2 ^ j) (fun y => dilate 2 (momentKernel b.toFun 2) y - momentKernel b.toFun 2 y) :=
  b.kernel_succ_eq_dilate 2 j

/-- **The local means kernels are divergences**: `k_{j+1} = 2^(-j) ∑_i ∂_{e_i} (K_i)_{2^j}`
(`Rd.sum_lineDerivOp_schwartzDilate_divergenceSchwartz`). -/
theorem kernel_two_succ_apply (j : ℕ) (y : V) :
    b.kernel 2 (j + 1) y = ((((2 : ℝ) ^ j)⁻¹ : ℝ) : ℂ) * ∑ i, (∂_{gridBasis V i}
      (schwartzDilate (2 ^ j) (by positivity) (b.divKernel i)) : 𝓢(V, ℂ)) y := by
  unfold divKernel
  rw [sum_lineDerivOp_schwartzDilate_divergenceSchwartz (gridBasis V), kernel_two_succ]
  have h : (((2 : ℝ) ^ j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos two_pos j).ne'
  push_cast
  field_simp

/-- **The moment kernel of order two of a bump has vanishing first moments**
(`Rd.integral_inner_mul_momentKernel_two`). -/
theorem integral_inner_mul_momentKernel (w : V) :
    ∫ x, (inner ℝ w x : ℂ) * momentKernel b.toFun 2 x = 0 :=
  integral_inner_mul_momentKernel_two w
    (((Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)).mul
      b.contDiff.continuous).integrable_of_hasCompactSupport b.hasCompactSupport.mul_left)

/-- **The divergence kernels form Calderón–Zygmund families**: the dilates `(K_i)_{2^j}` have the
Fourier overlap `Rd.meanZeroOverlap (K_i)` and the Hörmander constant `4 H_{K_i}`
(`Rd.isCZFamily_divergenceSchwartz`). -/
theorem isCZFamily_divKernel (i : Fin (finrank ℝ V)) :
    IsCZFamily (fun j => dilate (2 ^ j) (b.divKernel i : V → ℂ)) (meanZeroOverlap (b.divKernel i))
      (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i)) :=
  isCZFamily_divergenceSchwartz (b.contDiff_momentKernel 2)
    (fun _ hz => b.momentKernel_two_eq_zero hz) (b.integral_inner_mul_momentKernel (gridBasis V i))

/-! ### Local means by the gradient -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Local means of order two by the gradient, at one point**: let `g_i = ∂_{e_i} f` weakly on an
open set `T`, `f ∈ L_p(T)`, and let `x - y ∈ T` for every `y` in the support of every
`(K_i)_{2^j}`. Then `(k_{j+1} ⋆ 1_T f)(x) = 2^(-j) ∑_i ((K_i)_{2^j} ⋆ 1_T g_i)(x)`: the kernel is
`2^(-j) ∑_i ∂_{e_i} (K_i)_{2^j}` (`Rd.LocalMeansBump.kernel_two_succ_apply`), and each derivative
moves to `f` (`Rd.conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp`). -/
theorem conv_kernel_two_succ_eq {T : Opens V} {f : V → ℂ} {g : Fin (finrank ℝ V) → V → ℂ}
    (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i)) (j : ℕ) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    conv (b.kernel 2 (j + 1)) ((T : Set V).indicator f) volume x =
      ((((2 : ℝ) ^ j)⁻¹ : ℝ) : ℂ) * ∑ i, conv (dilate (2 ^ j) (b.divKernel i : V → ℂ))
        ((T : Set V).indicator (g i)) volume x :=
  conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp hf hfg b.hasCompactSupport_divKernel
    (by positivity) (b.kernel_two_succ_apply j) hx

/-- The constant `∑_i C_{p}(K_i)` of the gradient bound of the local means, with the constants
`C_p(K_i) = Rd.czConst V p B_i H_i` of the Calderón–Zygmund families of the divergence kernels
(`Rd.LocalMeansBump.isCZFamily_divKernel`). -/
noncomputable def gradientConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, czConst V p (meanZeroOverlap (b.divKernel i))
    (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i))

/-- The constant of the gradient bound is finite for `1 < p < ∞`. -/
theorem gradientConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : b.gradientConst p ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ => czConst_ne_top hp1 hp (meanZeroOverlap_ne_top _)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

/-! ### Local means of Triebel–Lizorkin type on a set -/

/-- The **local means quasi-norm of Triebel–Lizorkin type on a set** `W`,
`‖ x ↦ ‖(2^(js) |1_W (k_j ⋆ f)(x)|)_j‖_{ℓ_q} ‖_p`. -/
noncomputable def tlLocalNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ) (s : ℝ)
    (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j *
    ‖(indicatorLp hW (b.localMean hp L j f) : V → ℂ) x‖ₑ)) p volume

/-- The local means on `W` are bounded by the local means quasi-norm of Triebel–Lizorkin type:
`‖1_W (k_j ⋆ f)‖_p ≤ 2^(-js) X` with `X = Rd.LocalMeansBump.tlLocalNormOn`. -/
theorem enorm_indicatorLp_localMean_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0) (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤
      dyadicWeight (-s) j * b.tlLocalNormOn hp hW L s q f :=
  enorm_le_dyadicWeight_neg_mul_eLpNorm_lqNorm hq s
    (fun j => indicatorLp hW (b.localMean hp L j f)) j

/-- The weighted local means on `W` are bounded by the local means quasi-norm of Triebel–Lizorkin
type: `2^(js) ‖1_W (k_j ⋆ f)‖_p ≤ X` with `X = Rd.LocalMeansBump.tlLocalNormOn`
(`Rd.LocalMeansBump.enorm_indicatorLp_localMean_le`). -/
theorem dyadicWeight_mul_enorm_indicatorLp_localMean_le (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) (L : ℕ) {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0)
    (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ ≤ b.tlLocalNormOn hp hW L s q f :=
  calc dyadicWeight s j * ‖indicatorLp hW (b.localMean hp L j f)‖ₑ
      ≤ dyadicWeight s j * (dyadicWeight (-s) j * b.tlLocalNormOn hp hW L s q f) := by
        gcongr
        exact b.enorm_indicatorLp_localMean_le hp hW L hq f j
    _ = b.tlLocalNormOn hp hW L s q f := by
        rw [← mul_assoc, ENNReal.dyadicWeight_mul_neg_self, one_mul]

/-- The terms of the local extension: `‖η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 2^(-js) X` with
`X = Rd.LocalMeansBump.tlLocalNormOn` (`Rd.LocalMeansBump.enorm_localExtTerm_le_of_forall_le`). -/
theorem enorm_localExtTerm_le (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) (L : ℕ)
    {s : ℝ} {q : ℝ≥0∞} (hq : q ≠ 0) (f : Lp ℂ p (volume : Measure V)) (j : ℕ) :
    ‖b.localExtTerm hp hW L j f‖ₑ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume *
      (dyadicWeight (-s) j * b.tlLocalNormOn hp hW L s q f) :=
  b.enorm_localExtTerm_le_of_forall_le hp hW L
    (b.dyadicWeight_mul_enorm_indicatorLp_localMean_le hp hW L hq f) j

/-- **The local extension converges absolutely** for `s > 0` and a finite local means quasi-norm
of Triebel–Lizorkin type on `W` (`Rd.LocalMeansBump.summable_localExtTerm_of_forall_le`). -/
theorem summable_localExtTerm_of_tlLocalNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : q ≠ 0) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.tlLocalNormOn hp hW L s q f < ∞) : Summable fun j => b.localExtTerm hp hW L j f :=
  b.summable_localExtTerm_of_forall_le hp hW L hs hf.ne
    (b.dyadicWeight_mul_enorm_indicatorLp_localMean_le hp hW L hq f)

/-- **The local extension in `L_p`**: for `s > 0`,
`‖∑_j η_j ⋆ 1_W (k_j ⋆ f)‖_p ≤ 2 ‖m‖_1 (1 - 2^(-s))⁻¹ X` with
`X = Rd.LocalMeansBump.tlLocalNormOn` (`Rd.LocalMeansBump.tsum_enorm_localExtTerm_le`). -/
theorem enorm_localExtension_le_of_tlLocalNormOn (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : q ≠ 0) {f : Lp ℂ p (volume : Measure V)}
    (hf : b.tlLocalNormOn hp hW L s q f < ∞) :
    ‖b.localExtension hp hW L f‖ₑ ≤ 2 * eLpNorm (momentKernel b.toFun L) 1 volume *
      (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * b.tlLocalNormOn hp hW L s q f := by
  have h1 : ‖b.localExtension hp hW L f‖ₑ ≤ ∑' j, ‖b.localExtTerm hp hW L j f‖ₑ :=
    ENNReal.le_tsum_of_tendsto_sum (C := 1) ENNReal.one_ne_top (fun x y => eNorm_add_le x y)
      (fun x => by rw [one_mul])
      (b.tendsto_sum_localExtTerm_of_summable hp hW L
        (b.summable_localExtTerm_of_tlLocalNormOn hp hW L hs hq hf))
  exact h1.trans (b.tsum_enorm_localExtTerm_le hp hW L
    (b.dyadicWeight_mul_enorm_indicatorLp_localMean_le hp hW L hq f))

/-- **The local extension lies in `F^s_{p,q}`**: for `1 < p < ∞`, `1 < q ≤ ∞`, `s > 0` and a
finite local means quasi-norm of Triebel–Lizorkin type on `W`,
`‖∑_j η_j ⋆ 1_W (k_j ⋆ f)‖_{F^s_{p,q}} ≤ C X` with `C = Rd.LocalMeansBump.tlUpperConst L p q s`
(`Rd.LocalMeansBump.triebelLizorkinNorm_le_of_tendsto_sum_dual`). -/
theorem triebelLizorkinNorm_localExtension_le (hp1 : 1 < p) (hp : p ≠ ∞) {W : Set V}
    (hW : MeasurableSet W) (L : ℕ) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq1 : 1 < q)
    {f : Lp ℂ p (volume : Measure V)} (hf : b.tlLocalNormOn hp hW L s q f < ∞) :
    triebelLizorkinNorm s q (b.localExtension hp hW L f) ≤
      b.tlUpperConst L p q s * b.tlLocalNormOn hp hW L s q f :=
  b.triebelLizorkinNorm_le_of_tendsto_sum_dual L hp1 hp hq1 s
    (b.tendsto_sum_localExtTerm_of_summable hp hW L
      (b.summable_localExtTerm_of_tlLocalNormOn hp hW L hs (zero_lt_one.trans hq1).ne' hf))

/-! ### The Triebel–Lizorkin local means from a pointwise bound -/

/-- **The local means from a pointwise bound, almost everywhere**: let `F = φ` almost
everywhere, and let `2^{(j+1)s} |(k_{j+1} ⋆ φ)(x)| ≤ c ∑_i |((K_i)_{2^j} ⋆ h_i)(x)|` for the local
means kernels `k_j` of order `L`, every `x ∈ W` and every level `j`, with Schwartz kernels `K_i`
and functions `h_i`. Then almost everywhere
`‖(2^{js} |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ≤ |1_W (k_0 ⋆ F)(x)| +
c ∑_i ‖(((K_i)_{2^j} ⋆ h_i)(x))_j‖_{ℓ_2}`. -/
theorem ae_lqNorm_le_of_pointwise (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {W : Set V}
    (hW : MeasurableSet W) {φ : V → ℂ} {ι : Type*} [Fintype ι] (K : ι → 𝓢(V, ℂ))
    (h : ι → V → ℂ) (c : ℝ≥0∞)
    (hpt : ∀ x ∈ W, ∀ j, dyadicWeight s (j + 1) * ‖conv (b.kernel L (j + 1)) φ volume x‖ₑ ≤
      c * ∑ i, ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] φ) :
    ∀ᵐ x ∂volume, lqNorm 2 (fun j => dyadicWeight s j *
        ‖(indicatorLp hW (b.localMean hp L j F) : V → ℂ) x‖ₑ) ≤
      ‖(indicatorLp hW (b.localMean hp L 0 F) : V → ℂ) x‖ₑ + c * ∑ i, lqNorm 2 (fun j =>
        ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ) := by
  have hae : ∀ᵐ x ∂volume, ∀ j, (indicatorLp hW (b.localMean hp L j F) : V → ℂ) x =
      W.indicator (conv (b.kernel L j) φ volume) x := ae_all_iff.2 fun j => by
    filter_upwards [indicatorLp_apply_ae hW (b.localMean hp L j F), b.localMean_ae_eq hp L j F]
      with x h1 h2
    rw [h1, ← conv_congr_ae hF]
    by_cases hxW : x ∈ W
    · rw [Set.indicator_of_mem hxW, Set.indicator_of_mem hxW, h2]
    · rw [Set.indicator_of_notMem hxW, Set.indicator_of_notMem hxW]
  filter_upwards [hae] with x hx
  refine (ENNReal.lqNorm_le_head_add_shift one_le_two _).trans ?_
  rw [ENNReal.dyadicWeight_zero_right, one_mul]
  gcongr
  calc lqNorm 2 (fun j => dyadicWeight s (j + 1) *
        ‖(indicatorLp hW (b.localMean hp L (j + 1) F) : V → ℂ) x‖ₑ)
      ≤ lqNorm 2 (fun j => c * ∑ i, ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ) :=
        ENNReal.lqNorm_mono fun j => by
          rw [hx (j + 1)]
          by_cases hxW : x ∈ W
          · rw [Set.indicator_of_mem hxW]
            exact hpt x hxW j
          · simp [Set.indicator_of_notMem hxW]
    _ = c * lqNorm 2 (fun j => ∑ i, ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ) :=
        ENNReal.lqNorm_const_mul _ _
    _ ≤ _ := by
        gcongr
        exact ENNReal.lqNorm_sum_le one_le_two _ fun i j =>
          ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ

/-- **The local means of Triebel–Lizorkin type from a pointwise bound**: under the hypotheses of
`Rd.LocalMeansBump.ae_lqNorm_le_of_pointwise`, with almost everywhere strongly measurable `h_i`,
`‖ x ↦ ‖(2^{js} |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ ‖m_L‖_1 ‖F‖_p +
c ∑_i ‖ x ↦ ‖(((K_i)_{2^j} ⋆ h_i)(x))_j‖_{ℓ_2} ‖_p`, with the moment kernel `m_L` of order `L`. -/
theorem tlLocalNormOn_le_of_pointwise (hp : p ≠ ∞) (L : ℕ) (s : ℝ) {W : Set V}
    (hW : MeasurableSet W) {φ : V → ℂ} {ι : Type*} [Fintype ι] (K : ι → 𝓢(V, ℂ))
    (h : ι → V → ℂ) (hh : ∀ i, AEStronglyMeasurable (h i) volume) (c : ℝ≥0∞)
    (hpt : ∀ x ∈ W, ∀ j, dyadicWeight s (j + 1) * ‖conv (b.kernel L (j + 1)) φ volume x‖ₑ ≤
      c * ∑ i, ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] φ) :
    b.tlLocalNormOn hp hW L s 2 F ≤ eLpNorm (momentKernel b.toFun L) 1 volume * ‖F‖ₑ +
      c * ∑ i, eLpNorm (fun x => lqNorm 2 (fun j =>
        ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)) p volume := by
  have hΛ : ∀ i, AEMeasurable (fun x => lqNorm 2 (fun j =>
      ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)) volume := fun i =>
    aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_conv
      (continuous_dilate (K i).continuous _).aestronglyMeasurable (hh i)).eNorm) 2
  have h1 : b.tlLocalNormOn hp hW L s 2 F ≤
      eLpNorm (fun x => ‖(indicatorLp hW (b.localMean hp L 0 F) : V → ℂ) x‖ₑ) p volume +
        eLpNorm (fun x => c * ∑ i, lqNorm 2 (fun j =>
          ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)) p volume := by
    refine (eLpNorm_mono_eNorm_ae
      (aemeasurable_lqNorm_comp (fun j => ((Lp.aestronglyMeasurable _).eNorm.const_mul _))
        2).aestronglyMeasurable ?_).trans (eLpNorm_add_le Fact.out)
    filter_upwards [b.ae_lqNorm_le_of_pointwise hp L s hW K h c hpt hF] with x hx
    simpa only [eNorm_eq_self, Pi.add_apply] using hx
  have h2 : eLpNorm (fun x => c * ∑ i, lqNorm 2 (fun j =>
      ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)) p volume ≤
      c * ∑ i, eLpNorm (fun x => lqNorm 2 (fun j =>
        ‖conv (dilate (2 ^ j) (K i : V → ℂ)) (h i) volume x‖ₑ)) p volume := by
    rw [eLpNorm_const_mul_ennreal
      (Finset.aemeasurable_fun_sum _ fun i _ => hΛ i).aestronglyMeasurable]
    gcongr
    simpa only [Finset.sum_fn] using eLpNorm_sum_le (p := p) (μ := volume) Fact.out
  have h3 : eLpNorm (fun x => ‖(indicatorLp hW (b.localMean hp L 0 F) : V → ℂ) x‖ₑ) p volume ≤
      eLpNorm (momentKernel b.toFun L) 1 volume * ‖F‖ₑ := by
    rw [eLpNorm_eNorm _ (Lp.aestronglyMeasurable _), ← Lp.eNorm_def]
    exact b.enorm_indicatorLp_localMean_zero_le hp hW L F
  exact h1.trans (add_le_add h3 h2)

/-! ### The Triebel–Lizorkin local means of order two by the gradient -/

/-- **One local mean by the gradient**: under the hypotheses of
`Rd.LocalMeansBump.conv_kernel_two_succ_eq`,
`2^(j+1) |(k_{j+1} ⋆ 1_T f)(x)| ≤ 2 ∑_i |((K_i)_{2^j} ⋆ 1_T g_i)(x)|`. -/
theorem dyadicWeight_mul_enorm_conv_kernel_le {T : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i)) (j : ℕ) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T) :
    dyadicWeight 1 (j + 1) * ‖conv (b.kernel 2 (j + 1)) ((T : Set V).indicator f) volume x‖ₑ ≤
      2 * ∑ i, ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i))
        volume x‖ₑ := by
  have hw : dyadicWeight 1 (j + 1) * ‖(((((2 : ℝ) ^ j)⁻¹ : ℝ) : ℂ))‖ₑ = 2 := by
    rw [ENNReal.dyadicWeight_succ, ENNReal.dyadicWeight_eq_pow, ENNReal.rpow_one,
      ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat, mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero)
        (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), mul_one]
  rw [b.conv_kernel_two_succ_eq hf hfg j hx, eNorm_mul, ← mul_assoc, hw]
  gcongr
  exact eNorm_sum_le _ _

/-- **The local means of order two by the gradient, pointwise**: if `x - y ∈ T` for `x ∈ W`, every
level `j` and every `y` in the support of `(K_i)_{2^j}`, and `F = 1_T f` in `L_p`, then almost
everywhere `‖(2^j |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ≤ |1_W (k_0 ⋆ F)(x)| +
2 ∑_i ‖(((K_i)_{2^j} ⋆ 1_T g_i)(x))_j‖_{ℓ_2}` (`Rd.LocalMeansBump.ae_lqNorm_le_of_pointwise`). -/
theorem ae_lqNorm_le_of_hasWeakLineDeriv (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W)
    {T : Opens V} {f : V → ℂ} {g : Fin (finrank ℝ V) → V → ℂ}
    (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    ∀ᵐ x ∂volume, lqNorm 2 (fun j => dyadicWeight 1 j *
        ‖(indicatorLp hW (b.localMean hp 2 j F) : V → ℂ) x‖ₑ) ≤
      ‖(indicatorLp hW (b.localMean hp 2 0 F) : V → ℂ) x‖ₑ + 2 * ∑ i, lqNorm 2 (fun j =>
        ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ((T : Set V).indicator (g i)) volume
          x‖ₑ) :=
  b.ae_lqNorm_le_of_pointwise hp 2 1 hW b.divKernel (fun i => (T : Set V).indicator (g i)) 2
    (fun x hx j => b.dyadicWeight_mul_enorm_conv_kernel_le hf hfg j (hsupp x hx j)) hF

omit [Fact (1 ≤ p)] in
/-- The square functions of the divergence kernels: for `1 < p < ∞`,
`‖ x ↦ ‖(((K_i)_{2^j} ⋆ 1_T g)(x))_j‖_{ℓ_2} ‖_p ≤ C_p(K_i) ‖g‖_{L_p(T)}`
(`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`). -/
theorem eLpNorm_lqNorm_conv_divKernel_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {T : Opens V} {g : V → ℂ} (hg : MemLp g p (volume.restrict T)) (i : Fin (finrank ℝ V)) :
    eLpNorm (fun x => lqNorm 2 (fun j => ‖conv (dilate (2 ^ j) (b.divKernel i : V → ℂ))
        ((T : Set V).indicator g) volume x‖ₑ)) p volume ≤
      czConst V p (meanZeroOverlap (b.divKernel i))
        (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i)) *
        eLpNorm g p (volume.restrict T) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict T.isOpen.measurableSet.nullMeasurableSet]
  exact (b.isCZFamily_divKernel i).eLpNorm_lqNorm_conv_le hp1 hp
    ((memLp_indicator_iff_restrict T.isOpen.measurableSet.nullMeasurableSet).2 hg)

/-- **The local means of Triebel–Lizorkin type by the gradient**: let `g_i = ∂_{e_i} f` weakly on
an open set `T` with `f, g_i ∈ L_p(T)`, `1 < p < ∞`, let `x - y ∈ T` for every `x ∈ W`, every level
`j` and every `y` in the support of `(K_i)_{2^j}`, and let `F = 1_T f` in `L_p`. Then
`‖ x ↦ ‖(2^j |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ ‖m‖_1 ‖f‖_{L_p(T)} +
2 ∑_i C_p(K_i) ‖g_i‖_{L_p(T)}` (`Rd.LocalMeansBump.tlLocalNormOn_le_of_pointwise`). -/
theorem tlLocalNormOn_le_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hg : ∀ i, MemLp (g i) p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    b.tlLocalNormOn hp hW 2 1 2 F ≤ eLpNorm (momentKernel b.toFun 2) 1 volume *
      eLpNorm f p (volume.restrict T) + 2 * ∑ i, czConst V p (meanZeroOverlap (b.divKernel i))
        (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.divKernel i)) *
        eLpNorm (g i) p (volume.restrict T) := by
  have hT := T.isOpen.measurableSet
  have hFn : ‖F‖ₑ = eLpNorm f p (volume.restrict T) := by
    rw [Lp.eNorm_def, eLpNorm_congr_ae hF,
      eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet]
  refine (b.tlLocalNormOn_le_of_pointwise hp 2 1 hW b.divKernel
    (fun i => (T : Set V).indicator (g i))
    (fun i => ((memLp_indicator_iff_restrict hT.nullMeasurableSet).2 (hg i)).aestronglyMeasurable) 2
    (fun x hx j => b.dyadicWeight_mul_enorm_conv_kernel_le hf hfg j (hsupp x hx j)) hF).trans ?_
  rw [hFn]
  gcongr with i
  exact b.eLpNorm_lqNorm_conv_divKernel_le hp1 hp (hg i) i

end LocalMeansBump

/-! ### Bounded extensions from a set -/

variable {p : ℝ≥0∞}

variable (p) in
/-- **Sobolev functions on `O` extend from `U` with constant `C`**: for every `f ∈ L_p(O)` with
weak derivatives `g_i = ∂_{e_i} f ∈ L_p(O)` along the orthonormal basis `e_i = Rd.gridBasis V i`
there are `F ∈ W^1_p(V)` with `F = f` almost everywhere on `U` and weak derivatives
`G_i = ∂_{e_i} F ∈ L_p(V)` with `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`. -/
def ExtendsSobolev (O : Opens V) (U : Set V) (C : ℝ≥0∞) : Prop :=
  ∀ (f : V → ℂ) (g : Fin (finrank ℝ V) → V → ℂ), MemLp f p (volume.restrict O) →
    (∀ i, MemLp (g i) p (volume.restrict O)) →
    (∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) f (g i)) →
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev 1 F ∧ (∀ᵐ x ∂volume, x ∈ U → F x = f x) ∧
      ∃ G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V),
        (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) F (G i)) ∧
        ‖F‖ₑ + ∑ i, ‖G i‖ₑ ≤
          C * (eLpNorm f p (volume.restrict O) + ∑ i, eLpNorm (g i) p (volume.restrict O))

/-- **Larger domains**: an extension from `U` for Sobolev functions on `T` serves for Sobolev
functions on every open `O ⊇ T`, with the same constant, since `‖h‖_{L_p(T)} ≤ ‖h‖_{L_p(O)}` and
weak derivatives restrict to `T` (`Rd.HasWeakLineDeriv.mono`). -/
theorem ExtendsSobolev.of_le {T O : Opens V} {U : Set V} {C : ℝ≥0∞}
    (h : ExtendsSobolev p T U C) (hTO : T ≤ O) : ExtendsSobolev p O U C := by
  intro f g hf hg hfg
  have hμ : volume.restrict (T : Set V) ≤ volume.restrict O :=
    Measure.restrict_mono (show (T : Set V) ⊆ O from hTO) le_rfl
  obtain ⟨F, hF, hFf, G, hG, hb⟩ := h f g (hf.mono_measure hμ) (fun i => (hg i).mono_measure hμ)
    fun i => (hfg i).mono hTO
  refine ⟨F, hF, hFf, G, hG, hb.trans ?_⟩
  gcongr

/-- **Finiteness from a bound**: if `‖F‖_p + ∑_i ‖G_i‖_p ≤ C X` with finite `C` and `X`, then `F`
and every `G_i` lie in `L_p(V)`. -/
theorem memLp_of_eLpNorm_add_sum_le {ι : Type*} [Fintype ι] {F : V → ℂ} {G : ι → V → ℂ}
    {C X : ℝ≥0∞} (hC : C ≠ ∞) (hX : X ≠ ∞)
    (hb : eLpNorm F p volume + ∑ i, eLpNorm (G i) p volume ≤ C * X) :
    MemLp F p volume ∧ ∀ i, MemLp (G i) p volume := by
  have hfin : C * X < ∞ := ENNReal.mul_lt_top hC.lt_top hX.lt_top
  refine ⟨memLp_iff.2 ((le_self_add.trans hb).trans_lt hfin), fun i => memLp_iff.2 ?_⟩
  exact (((Finset.single_le_sum (f := fun j => eLpNorm (G j) p volume) (fun j _ => zero_le)
    (Finset.mem_univ i)).trans le_add_self).trans hb).trans_lt hfin

/-- **Extensions from `L_p` bounds**: Sobolev functions on `O` extend from `U` with constant `C`
(`Rd.ExtendsSobolev`) as soon as every `f ∈ L_p(O)` with weak derivatives `g_i = ∂_{e_i} f` in
`L_p(O)` agrees almost everywhere on `U` with a function `F` on `V` with weak derivatives
`G_i = ∂_{e_i} F` on `V` and `‖F‖_p + ∑_i ‖G_i‖_p ≤ C (‖f‖_{L_p(O)} + ∑_i ‖g_i‖_{L_p(O)})`;
the bound puts `F` and the `G_i` into `L_p(V)` (`Rd.memLp_of_eLpNorm_add_sum_le`, Mathlib's
`MemLp.toLp`). -/
theorem extendsSobolev_of_eLpNorm_le [Fact (1 ≤ p)] {O : Opens V} {U : Set V} {C : ℝ≥0∞}
    (hC : C ≠ ∞)
    (h : ∀ (f : V → ℂ) (g : Fin (finrank ℝ V) → V → ℂ), MemLp f p (volume.restrict O) →
      (∀ i, MemLp (g i) p (volume.restrict O)) →
      (∀ i, HasWeakLineDeriv O (fun _ : Fin 1 => gridBasis V i) f (g i)) →
      ∃ (F : V → ℂ) (G : Fin (finrank ℝ V) → V → ℂ),
        (∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) F (G i)) ∧
        (∀ᵐ x ∂volume, x ∈ U → F x = f x) ∧
        eLpNorm F p volume + ∑ i, eLpNorm (G i) p volume ≤
          C * (eLpNorm f p (volume.restrict O) + ∑ i, eLpNorm (g i) p (volume.restrict O))) :
    ExtendsSobolev p O U C := by
  intro f g hf hg hfg
  obtain ⟨F, G, hG, hFf, hb⟩ := h f g hf hg hfg
  obtain ⟨hFm, hGm⟩ := memLp_of_eLpNorm_add_sum_le hC
    (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, ENNReal.sum_ne_top.2 fun i _ =>
      (hg i).eLpNorm_ne_top⟩) hb
  have hW : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i) (hFm.toLp F)
      ((hGm i).toLp (G i)) := fun i =>
    (hG i).congr_ae (by rw [volume_restrict_top]; exact hFm.coeFn_toLp.symm)
      (by rw [volume_restrict_top]; exact (hGm i).coeFn_toLp.symm)
  refine ⟨hFm.toLp F, memSobolev_one_of_forall_gridBasis hW, ?_, fun i => (hGm i).toLp (G i), hW,
    ?_⟩
  · filter_upwards [hFm.coeFn_toLp, hFf] with x h1 h2 hx
    rw [h1, h2 hx]
  · simpa only [Lp.eNorm_toLp] using hb

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The constant `‖m‖_1 + 2 ∑_i C_p(K_i)` of the local means of a bump by the gradient. -/
noncomputable def patchConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (momentKernel b.toFun 2) 1 volume + 2 * b.gradientConst p

/-- The constant of the local means by the gradient is finite for `1 < p < ∞`. -/
theorem patchConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : b.patchConst p ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨eLpNorm_momentKernel_ne_top b.integrable 2,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (b.gradientConst_ne_top hp1 hp)⟩

/-- **The local means of Triebel–Lizorkin type by the gradient, with one constant**: under the
hypotheses of `Rd.LocalMeansBump.tlLocalNormOn_le_of_hasWeakLineDeriv`,
`‖ x ↦ ‖(2^j |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ C (‖f‖_{L_p(T)} + ∑_i ‖g_i‖_{L_p(T)})` with
`C = Rd.LocalMeansBump.patchConst b p`. -/
theorem tlLocalNormOn_le_patchConst [Fact (1 ≤ p)] [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {W : Set V} (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ}
    {g : Fin (finrank ℝ V) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hg : ∀ i, MemLp (g i) p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun _ : Fin 1 => gridBasis V i) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    b.tlLocalNormOn hp hW 2 1 2 F ≤ b.patchConst p *
      (eLpNorm f p (volume.restrict T) + ∑ i, eLpNorm (g i) p (volume.restrict T)) := by
  refine (b.tlLocalNormOn_le_of_hasWeakLineDeriv hp1 hp hW hf hg hfg hsupp hF).trans ?_
  rw [patchConst, add_mul, mul_assoc 2]
  refine add_le_add (mul_le_mul_right le_self_add _) (mul_le_mul_right ?_ 2)
  exact (ENNReal.sum_mul_le_sum_mul_sum _ _ _).trans (mul_le_mul_right le_add_self _)

/-- The constant `(2 ‖m‖_1 (1 - 2^(-1))⁻¹ + (∑_i C_i) A) C_b` of the extension from one patch, with
the constants `C_i = Rd.tlToSobolevConst p e_i` of the weak derivatives of `F^1_{p,2}` functions,
`A = Rd.LocalMeansBump.tlUpperConst b 2 p 2 1` and `C_b = Rd.LocalMeansBump.patchConst b p`. -/
noncomputable def extensionConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  (2 * eLpNorm (momentKernel b.toFun 2) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-(1 : ℝ)))⁻¹ +
    (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) * b.tlUpperConst 2 p 2 1) *
    b.patchConst p

/-- The constant of the extension from one patch is finite for `1 < p < ∞`. -/
theorem extensionConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) : b.extensionConst p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofNat_ne_top (eLpNorm_momentKernel_ne_top b.integrable 2))
      (ENNReal.one_sub_two_rpow_neg_inv_ne_top one_pos),
    ENNReal.mul_ne_top (ENNReal.sum_ne_top.2 fun _ _ => tlToSobolevConst_ne_top hp1 hp _)
      (b.tlUpperConst_ne_top 2 hp1 hp ENNReal.one_lt_two one_pos)⟩) (b.patchConst_ne_top hp1 hp)

/-- **The local extension lies in `F^1_{p,2}(V)`** if the local means quasi-norm of
Triebel–Lizorkin type of `F` on `W` is finite
(`Rd.LocalMeansBump.triebelLizorkinNorm_localExtension_le`). -/
theorem memTriebelLizorkin_localExtension_of_tlLocalNormOn [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) {F : Lp ℂ p (volume : Measure V)}
    (hXf : b.tlLocalNormOn hp hW 2 1 2 F < ∞) :
    MemTriebelLizorkin ((1 : ℕ) : ℝ) 2 (b.localExtension hp hW 2 F) := by
  rw [Nat.cast_one]
  exact (b.triebelLizorkinNorm_localExtension_le hp1 hp hW 2 one_pos ENNReal.one_lt_two
    hXf).trans_lt (ENNReal.mul_lt_top
      (b.tlUpperConst_ne_top 2 hp1 hp ENNReal.one_lt_two one_pos).lt_top hXf)

/-- **The local extension agrees with `f` on `U`**: if `F = 1_T f` almost everywhere, `U ⊆ T`, the
dual kernels of order `L ≥ 1` at points of `U` only see `W` and the series of the local extension
converges, then `∑_j η_j ⋆ 1_W (k_j ⋆ F) = f` almost everywhere on `U`
(`Rd.LocalMeansBump.indicatorLp_localExtension_of_summable`). -/
theorem ae_localExtension_eq_of_ae_eq_indicator [Fact (1 ≤ p)] (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    {U W T : Set V} (hU : MeasurableSet U) (hW : MeasurableSet W) (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dual L j y ≠ 0 → x - y ∈ W) {F : Lp ℂ p (volume : Measure V)}
    {f : V → ℂ} (hF : (F : V → ℂ) =ᵐ[volume] T.indicator f)
    (hsum : Summable fun j => b.localExtTerm hp hW L j F) :
    ∀ᵐ x ∂volume, x ∈ U → b.localExtension hp hW L F x = f x := by
  have heq := b.indicatorLp_localExtension_of_summable hp hL hU hW hUW hsum
  filter_upwards [Lp.ext_iff.1 heq, indicatorLp_apply_ae hU (b.localExtension hp hW L F),
    indicatorLp_apply_ae hU F, hF] with x h1 h2 h3 h4 hxU
  rw [h2, h3, Set.indicator_of_mem hxU, Set.indicator_of_mem hxU] at h1
  rw [h1, h4, Set.indicator_of_mem (hUT hxU)]

/-- **The bound of the local extension**: if the local means quasi-norm of Triebel–Lizorkin type
of `F` on `W` is finite and at most `C_b Y`, `C_b = Rd.LocalMeansBump.patchConst b p`, then the
local extension `E = ∑_j η_j ⋆ 1_W (k_j ⋆ F)` and every family of weak derivatives
`G_i = ∂_{e_i} E ∈ L_p(V)` satisfy `‖E‖_p + ∑_i ‖G_i‖_p ≤ C Y` with
`C = Rd.LocalMeansBump.extensionConst b p` (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`). -/
theorem enorm_localExtension_add_le_extensionConst [Fact (1 ≤ p)] [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) {W : Set V} (hW : MeasurableSet W) {F : Lp ℂ p (volume : Measure V)}
    {Y : ℝ≥0∞} (hX : b.tlLocalNormOn hp hW 2 1 2 F ≤ b.patchConst p * Y)
    (hXf : b.tlLocalNormOn hp hW 2 1 2 F < ∞)
    {G : Fin (finrank ℝ V) → Lp ℂ p (volume : Measure V)}
    (hG : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => gridBasis V i)
      (b.localExtension hp hW 2 F) (G i)) :
    ‖b.localExtension hp hW 2 F‖ₑ + ∑ i, ‖G i‖ₑ ≤ b.extensionConst p * Y := by
  have hTL := b.triebelLizorkinNorm_localExtension_le hp1 hp hW 2 one_pos ENNReal.one_lt_two hXf
  have hmem := b.memTriebelLizorkin_localExtension_of_tlLocalNormOn hp1 hp hW hXf
  have hFn := b.enorm_localExtension_le_of_tlLocalNormOn hp hW 2 one_pos two_ne_zero hXf
  have hGs : ∑ i, ‖G i‖ₑ ≤ (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) *
      b.tlUpperConst 2 p 2 1 * b.tlLocalNormOn hp hW 2 1 2 F := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨G', hG', hG'n⟩ := exists_hasWeakLineDeriv_of_memTriebelLizorkin hp1 hp
      (fun _ : Fin 1 => gridBasis V i) hmem
    rw [(hG i).eq_of_top hG']
    refine hG'n.trans ?_
    rw [Nat.cast_one, mul_assoc]
    exact mul_le_mul_right hTL _
  calc _ ≤ _ := add_le_add hFn hGs
    _ = (2 * eLpNorm (momentKernel b.toFun 2) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-(1 : ℝ)))⁻¹ +
        (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) * b.tlUpperConst 2 p 2 1) *
        b.tlLocalNormOn hp hW 2 1 2 F := by ring
    _ ≤ (2 * eLpNorm (momentKernel b.toFun 2) 1 volume * (1 - (2 : ℝ≥0∞) ^ (-(1 : ℝ)))⁻¹ +
        (∑ i, tlToSobolevConst p (fun _ : Fin 1 => gridBasis V i)) * b.tlUpperConst 2 p 2 1) *
        (b.patchConst p * Y) := mul_le_mul_right hX _
    _ = _ := by rw [extensionConst]; ring

end LocalMeansBump

/-! ### Pasting in `W^1_p(V)` -/

/-- **The arithmetic of the pasting bound**: if `‖F‖ ≤ ∑_k a_k x_k`,
`‖G_i‖ ≤ ∑_k (a_k y_{k,i} + d_{k,i} x_k)` and `x_k + ∑_i y_{k,i} ≤ C_k Y`, then
`‖F‖ + ∑_i ‖G_i‖ ≤ (∑_k (a_k + ∑_i d_{k,i}) C_k) Y`. -/
theorem pasting_bound {ι κ : Type*} [Fintype ι] [Fintype κ] {nF : ℝ≥0∞}
    {nG : κ → ℝ≥0∞} {a x C : ι → ℝ≥0∞} {d y : ι → κ → ℝ≥0∞} {Y : ℝ≥0∞}
    (hF : nF ≤ ∑ k, a k * x k) (hG : ∀ i, nG i ≤ ∑ k, (a k * y k i + d k i * x k))
    (hxy : ∀ k, x k + ∑ i, y k i ≤ C k * Y) :
    nF + ∑ i, nG i ≤ (∑ k, (a k + ∑ i, d k i) * C k) * Y := by
  calc nF + ∑ i, nG i ≤ ∑ k, a k * x k + ∑ i, ∑ k, (a k * y k i + d k i * x k) :=
        add_le_add hF (Finset.sum_le_sum fun i _ => hG i)
    _ = ∑ k, (a k * (x k + ∑ i, y k i) + (∑ i, d k i) * x k) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.sum_mul]
        ring
    _ ≤ ∑ k, (a k + ∑ i, d k i) * (C k * Y) := Finset.sum_le_sum fun k _ => by
        calc a k * (x k + ∑ i, y k i) + (∑ i, d k i) * x k
            ≤ a k * (x k + ∑ i, y k i) + (∑ i, d k i) * (x k + ∑ i, y k i) := by
              gcongr
              exact le_self_add
          _ = (a k + ∑ i, d k i) * (x k + ∑ i, y k i) := by ring
          _ ≤ _ := mul_le_mul_right (hxy k) _
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring

/-- **Pasting bounded extensions**: let `(U_k)` be a finite cover of `Ō` by bounded open sets and
let Sobolev functions on `O` extend from every `O ∩ U_k` with finite constants. Then they extend
from `O` with a finite constant: for a smooth resolution of unity `(ψ_k)` subordinate to `(U_k)`
(`Rd.exists_smooth_partition`), `F = ∑_k ψ_k F_k` agrees with `f` on `O` (`Rd.ae_sum_mul_eq`),
lies in `W^1_p(V)` (`Rd.MemSobolev.mulLp`) and has the weak derivatives
`∑_k (ψ_k ∂_{e_i} F_k + (∂_{e_i} ψ_k) F_k)`
(`Rd.hasWeakLineDeriv_mulLp`). -/
theorem extendsSobolev_of_cover [Fact (1 ≤ p)] {ι : Type*} [Finite ι] {O : Opens V} (U : ι → Set V)
    (hUo : ∀ k, IsOpen (U k)) (hUb : ∀ k, Bornology.IsBounded (U k))
    (hcov : closure (O : Set V) ⊆ ⋃ k, U k) {C : ι → ℝ≥0∞} (hC : ∀ k, C k ≠ ∞)
    (hext : ∀ k, ExtendsSobolev p O ((O : Set V) ∩ U k) (C k)) :
    ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ ExtendsSobolev p O O C' := by
  let := Fintype.ofFinite ι
  classical
  obtain ⟨ψ, hψ, hψU, hψ1, -⟩ := exists_smooth_partition isClosed_closure U hUo hcov
  have hcs : ∀ k, HasCompactSupport (ψ k) := fun k =>
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hUb k).subset (hψU k))
  have hc : ∀ k, Continuous fun x => ((ψ k x : ℝ) : ℂ) := fun k =>
    Complex.continuous_ofReal.comp (hψ k).continuous
  have hc' : ∀ k i, Continuous fun x => ((fderiv ℝ (ψ k) x (gridBasis V i) : ℝ) : ℂ) :=
    fun k i => Complex.continuous_ofReal.comp
      (((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const)
  choose a ha using fun k =>
    (hc k).bounded_above_of_compact_support ((hcs k).comp_left Complex.ofReal_zero)
  choose d hd using fun k i => (hc' k i).bounded_above_of_compact_support
    (((hcs k).fderiv_apply (𝕜 := ℝ) (gridBasis V i)).comp_left Complex.ofReal_zero)
  refine ⟨∑ k, (ENNReal.ofReal (a k) + ∑ i, ENNReal.ofReal (d k i)) * C k,
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top⟩) (hC k), ?_⟩
  intro f g hf hg hfg
  choose F hF hFf G hG hb using fun k => hext k f g hf hg hfg
  refine ⟨∑ k, mulLp (hc k) (ha k) (F k), MemSobolev.sum _ fun k _ =>
    (hF k).mulLp (hψ k) (hcs k) (hc k) (ha k), ?_,
    fun i => ∑ k, (mulLp (hc k) (ha k) (G k i) + mulLp (hc' k i) (hd k i) (F k)), fun i => ?_, ?_⟩
  · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun k => mulLp (hc k) (ha k) (F k),
      ae_all_iff.2 fun k => mulLp_apply_ae (hc k) (ha k) (F k),
      ae_sum_mul_eq hψU (fun x hx => hψ1 x (subset_closure hx)) hFf] with x h1 h2 h3 hxO
    rw [h1, ← h3 hxO]
    exact Finset.sum_congr rfl fun k _ => h2 k
  · refine (HasWeakLineDeriv.sum (s := Finset.univ) fun k _ => hasWeakLineDeriv_mulLp (hG k i)
      (hψ k) (hc k) (ha k) (hc' k i) (hd k i)).congr_ae ?_ ?_ <;> rw [volume_restrict_top]
    · exact (Lp.coeFn_finsetSum _ _).symm
    · exact (Lp.coeFn_finsetSum _ _).symm
  · refine pasting_bound (x := fun k => ‖F k‖ₑ) (y := fun k i => ‖G k i‖ₑ)
      ((eNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => enorm_mulLp_le _ _ _))
      (fun i => (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (eNorm_add_le _ _).trans
        (add_le_add (enorm_mulLp_le _ _ _) (enorm_mulLp_le _ _ _)))) hb

/-! ### The supports of the divergence kernels -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- If a divergence kernel is nonzero at `y`, the moment kernel is nonzero at some `t y` with
`t ∈ [1, 2]` (`Rd.LocalMeansBump.divKernel_eq_zero`). -/
theorem exists_momentKernel_ne_zero_of_divKernel_ne_zero (i : Fin (finrank ℝ V)) {y : V}
    (hy : b.divKernel i y ≠ 0) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ 2 ∧ momentKernel b.toFun 2 (t • y) ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (b.divKernel_eq_zero i h)

/-- **The supports of the dilated divergence kernels**: if the divergence kernel `K_i` vanishes
outside a closed set `S` with `c y ∈ S ⇒ y ∈ S` for `c ≥ 1`, then every dilate `(K_i)_{2^j}` is
supported in `S` (`Rd.tsupport_dilate_two_pow_subset`). -/
theorem tsupport_dilate_divKernel_subset (i : Fin (finrank ℝ V)) {S : Set V} (hS : IsClosed S)
    (hK : ∀ y, b.divKernel i y ≠ 0 → y ∈ S) (hscale : ∀ c : ℝ, 1 ≤ c → ∀ y, c • y ∈ S → y ∈ S)
    (j : ℕ) : tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ⊆ S :=
  tsupport_dilate_two_pow_subset hS hK hscale j

/-- The divergence kernels of a bump of radius `R` and their dilates `(K_i)_{2^j}` are supported
in the closed ball of radius `2R`. -/
theorem tsupport_dilate_divKernel_subset_closedBall (i : Fin (finrank ℝ V)) (j : ℕ) :
    tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ⊆ closedBall 0 (2 * b.radius) := by
  refine b.tsupport_dilate_divKernel_subset i isClosed_closedBall (fun y hy => ?_)
    (fun c hc y hy => ?_) j
  · obtain ⟨t, ht1, -, ht⟩ := b.exists_momentKernel_ne_zero_of_divKernel_ne_zero i hy
    have h := not_lt.1 fun h => ht (b.momentKernel_two_eq_zero h)
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ht1)] at h
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg y]
  · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (zero_le_one.trans hc)]
      at hy
    rw [mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg y]

end LocalMeansBump

namespace LipschitzGraph

variable (G : LipschitzGraph V)

/-- **The divergence kernels of a cone-supported bump lie in the reflected closed cone**: for a bump
of radius `R` supported in `-K`, every dilate `(K_i)_{2^j}` of its divergence kernels is supported
in `{y : -y ∈ KBar, ‖y‖ ≤ 2R}`. -/
theorem tsupport_dilate_divKernel_subset {b : LocalMeansBump V} (hb : G.ConeSupported b.toFun)
    (i : Fin (finrank ℝ V)) (j : ℕ) :
    tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)) ⊆
      {y | -y ∈ G.closedCone} ∩ closedBall 0 (2 * b.radius) := by
  refine Set.subset_inter (b.tsupport_dilate_divKernel_subset i
    (G.isClosed_closedCone.preimage continuous_neg) (fun y hy => ?_) (fun c hc y hy => ?_) j)
    (b.tsupport_dilate_divKernel_subset_closedBall i j)
  · obtain ⟨t, ht1, -, ht⟩ := b.exists_momentKernel_ne_zero_of_divKernel_ne_zero i hy
    have h := G.smul_mem_closedCone (inv_nonneg.2 (zero_le_one.trans ht1))
      (G.cone_subset_closedCone (G.coneSupported_momentKernel_of hb 2 _ ht))
    rwa [smul_neg, inv_smul_smul₀ (zero_lt_one.trans_le ht1).ne'] at h
  · have h := G.smul_mem_closedCone (inv_nonneg.2 (zero_le_one.trans hc)) hy
    rwa [smul_neg, inv_smul_smul₀ (zero_lt_one.trans_le hc).ne'] at h

/-- **Boundary patches, the support condition for the divergence kernels**: for a bump supported in
`-K` with `2R ≤ ε`, `x - y ∈ Ω ∩ B(c, ρ)` for `x ∈ Ω ∩ B(c, ρ - ε)` and `y` in the support of a
dilated divergence kernel (`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`). -/
theorem patch_support_divKernel {b : LocalMeansBump V} (hb : G.ConeSupported b.toFun)
    {ε ρ : ℝ} {c : V} (hR : 2 * b.radius ≤ ε) :
    ∀ x ∈ G.domain ∩ ball c (ρ - ε), ∀ (j : ℕ) (i : Fin (finrank ℝ V)),
      ∀ y ∈ tsupport (dilate (2 ^ j) (b.divKernel i : V → ℂ)), x - y ∈ G.domain ∩ ball c ρ := by
  intro x hx j i y hy
  obtain ⟨hyK, hyR⟩ := G.tsupport_dilate_divKernel_subset hb i j hy
  rw [mem_closedBall, dist_zero_right] at hyR
  exact G.sub_mem_patch_of_mem_closedCone hx hyK (hyR.trans hR)

end LipschitzGraph

/-! ### Dimension zero -/

/-- **Extension in dimension `0`**: if `V` is a single point, every `f ∈ W^m_p(O)` on an open set
`O`, of every order `m`, agrees almost everywhere on `O` with some `F ∈ W^m_p(V)`. Here `O` is
empty, and `F = 0` serves, or `O = V`, and `F = f` serves (Mathlib's
`Subsingleton.eq_univ_of_nonempty`). -/
theorem exists_memSobolev_of_memWeakSobolev_of_subsingleton [Subsingleton V] {O : Opens V}
    {m : ℕ} {f : V → ℂ} (hf : MemWeakSobolev O m p f) :
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev m F ∧ (F : V → ℂ) =ᵐ[volume.restrict O] f := by
  rcases (O : Set V).eq_empty_or_nonempty with h | h
  · refine ⟨0, zero_memSobolev, ?_⟩
    rw [h, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  · obtain rfl : O = ⊤ :=
      Opens.ext ((Subsingleton.eq_univ_of_nonempty h).trans Opens.coe_top.symm)
    have hf1 : MemLp f p volume := volume_restrict_top (V := V) ▸ hf.1
    refine ⟨hf1.toLp f, hf.congr_ae ?_, ?_⟩ <;> rw [volume_restrict_top]
    · exact hf1.coeFn_toLp.symm
    · exact hf1.coeFn_toLp

/-! ### The cutoffs of the patches -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The cutoff of a boundary patch**: for `ε > 0` and every `j` there is a smooth `χ` with values
in `[0, 1]`, compact closed support in the boundary ball `B(c_j, ρ_j)` and `χ = 1` near
`closedBall(c_j, ρ_j - 2ε)` (`Rd.exists_contDiff_eventuallyEq_one`). -/
theorem exists_cutoff_boundary {ε : ℝ} (hε : 0 < ε) (j : Fin Ω.N) :
    ∃ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball (Ω.center j) (Ω.radius j) ∧ (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᶠ x in 𝓝ˢ (closedBall (Ω.center j) (Ω.radius j - 2 * ε)), χ x = 1 :=
  exists_contDiff_eventuallyEq_one (isCompact_closedBall _ _) isOpen_ball
    (closedBall_subset_ball (by linarith))

omit [MeasurableSpace V] [BorelSpace V] in
/-- **The cutoff of the inner patch**: for `δ > 0` there is a smooth `χ` with values in `[0, 1]`,
compact closed support in `Ω` and `χ = 1` near the compact set `{infDist(·, Ωᶜ) ≥ 2δ} ⊆ Ω`
(`Rd.exists_contDiff_eventuallyEq_one`). -/
theorem exists_cutoff_interior {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ω.carrier ∧ (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ᶠ x in 𝓝ˢ {x : V | 2 * δ ≤ infDist x Ω.carrierᶜ}, χ x = 1 := by
  have hKΩ : {x : V | 2 * δ ≤ infDist x Ω.carrierᶜ} ⊆ Ω.carrier := fun x hx =>
    setOf_lt_infDist_compl_subset Ω.carrier hδ.le
      (show δ < infDist x Ω.carrierᶜ from (lt_two_mul_self hδ).trans_le hx)
  exact exists_contDiff_eventuallyEq_one
    (isCompact_of_isClosed_isBounded (isClosed_le continuous_const (continuous_infDist_pt _))
      (Ω.isBounded.subset hKΩ)) Ω.isOpen hKΩ

end BoundedLipschitzDomain

end Rd
