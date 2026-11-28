/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTriebelLizorkin
public import LeanPool.FunctionSpaces.MeasureSpaces.Besov.Nikolskii
public import LeanPool.FunctionSpaces.Analysis.Lp.Interpolation
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev and Besov embeddings on `V`

Let `V` have dimension `n`, `1 ≤ p < ∞` and `α(n, p, r) = n (1/p - 1/r)` for `p ≤ r ≤ ∞`
(`nikolskiiExponent`). The embeddings come directly from the Littlewood–Paley blocks
`ψ_j ⋆ f` (`Rd.blockFun`).

* **Convolutions with integrable bounded kernels are continuous** on `L_p`
  (`Rd.continuous_conv_of_enorm_le`, for Schwartz kernels `Rd.continuous_conv_schwartz`):
  uniform limits of convolutions with continuous functions of compact support. Hence every block
  is continuous (`Rd.continuous_blockFun`).
* **The Nikolskii inequality for blocks** (`Rd.enorm_blockFun_le_nikolskii`,
  `Rd.eLpNorm_blockFun_le_nikolskii`): the block is band-limited, `Θ_j ⋆ (ψ_j ⋆ f) = ψ_j ⋆ f`,
  so `|(ψ_j ⋆ f)(x)| ≤ N_p 2^(jn/p) ‖ψ_j ⋆ f‖_p` at every point, and interpolation gives
  `‖ψ_j ⋆ f‖_r ≤ N_p^(1-p/r) 2^(j α(n,p,r)) ‖ψ_j ⋆ f‖_p` (`Rd.nikolskiiBlockConst`).
* **Besov into `L_r`** (`Rd.exists_memLp_ae_eq_of_memApprox`): for `1 ≤ q ≤ ∞` and
  `s > α(n, p, r)` every `f ∈ B^s_{p,q}` has a representative `g ∈ L_r` with
  `‖g‖_r ≤ K ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}` (`Rd.besovEmbeddingConst`); the series of the blocks
  converges absolutely in `L_r` and almost everywhere to `f` (`Rd.ae_hasSum_blockFun`).
* **Besov into bounded continuous functions** (`Rd.exists_boundedContinuous_ae_eq_of_memApprox`):
  for `1 ≤ q ≤ ∞` and `s > n/p` the series of the blocks converges uniformly to a bounded
  continuous representative `a` of `f` with `sup |a| ≤ K ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}`.
* **Sobolev embeddings** (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv`,
  `Rd.exists_boundedContinuous_ae_eq_of_hasWeakLineDeriv`, `Rd.exists_memLp_ae_eq_of_memSobolev`,
  `Rd.exists_boundedContinuous_ae_eq_of_memSobolev`): for `n ≥ 1` and `1 < p < ∞`, the bound
  `‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖∂^α f‖_p` bounds the Littlewood–Paley quasi-norm
  of `B^m_{p,max(p,2)}`, which gives `W^m_p ↪ L_r` for `m > n(1/p - 1/r)` and `W^m_p ↪ C_b` for
  `m > n/p`, with named constants, formulas in norms and Schwartz seminorms of fixed kernels
  that are proved finite. The critical case `1/r = 1/p - m/n` with `r < ∞` (Sobolev's
  inequality) is in `FunctionSpaces.Rd.Sobolev.CriticalSobolevEmbedding`
  (`Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`), and for `p = 1` in
  `FunctionSpaces.Rd.Sobolev.GagliardoNirenbergSobolev`
  (`Rd.exists_memLp_ae_eq_of_memSobolev_one_of_eq`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal Topology SchwartzMap BoundedContinuousFunction
open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Convolutions with integrable bounded kernels are continuous -/

/-- **The convolution integrand of an integrable bounded kernel and an `L_p` function is
integrable**: for `1 ≤ p ≤ ∞`, an integrable `K` with `|K| ≤ B < ∞`, `f ∈ L_p(V)` and every `x`,
`y ↦ K(y) f(x - y)` is integrable, by Hölder's inequality (Mathlib's `MemLp.integrable_mul`) with
`K ∈ L_{p'}`, since `K ∈ L_1 ∩ L_∞` (`MeasureTheory.MemLp.mono_exponent_of_enorm_le`). -/
theorem integrable_mul_sub_of_enorm_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K : V → ℂ} (hK : Integrable K)
    {B : ℝ≥0∞} (hB : ∀ y, ‖K y‖ₑ ≤ B) (hBtop : B ≠ ∞) {f : V → ℂ} (hf : MemLp f p volume)
    (x : V) : Integrable (fun y => K y * f (x - y)) volume := by
  have : p.HolderConjugate p.conjExponent := ENNReal.HolderConjugate.conjExponent hp1
  have : p.conjExponent.HolderConjugate p := ENNReal.HolderConjugate.symm
  have hfx : MemLp (fun y => f (x - y)) p volume :=
    hf.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hK' : MemLp K p.conjExponent volume :=
    (memLp_one_iff_integrable.2 hK).mono_exponent_of_enorm_le (ae_of_all _ hB) hBtop one_ne_zero
      (by rw [ENNReal.conjExponent]; exact le_self_add)
  exact hK'.integrable_mul hfx

/-- **Convolution with an integrable bounded kernel respects differences at every point** on
`L_p`: `(K ⋆ f)(x) - (K ⋆ g)(x) = (K ⋆ (f - g))(x)` for `1 ≤ p ≤ ∞`, an integrable `K` with
`|K| ≤ B < ∞` and `f, g ∈ L_p(V)`. -/
theorem conv_sub_apply_of_enorm_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K : V → ℂ} (hK : Integrable K)
    {B : ℝ≥0∞} (hB : ∀ y, ‖K y‖ₑ ≤ B) (hBtop : B ≠ ∞) {f g : V → ℂ}
    (hf : MemLp f p volume) (hg : MemLp g p volume) (x : V) :
    conv K f volume x - conv K g volume x = conv K (f - g) volume x := by
  rw [conv_apply, conv_apply, conv_apply,
    ← integral_sub (integrable_mul_sub_of_enorm_le hp1 hK hB hBtop hf x)
      (integrable_mul_sub_of_enorm_le hp1 hK hB hBtop hg x)]
  congr 1
  funext y
  simp [mul_sub]

/-- **Convolutions of integrable bounded kernels with `L_p` functions are continuous**, for
`1 ≤ p < ∞`, an integrable `K` with `|K| ≤ B < ∞` and `f ∈ L_p(V)`. Continuous functions of
compact support `g_k` approximate `f` in `L_p` (Mathlib's
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), each `K ⋆ g_k` is continuous (Mathlib's
`HasCompactSupport.continuous_convolution_right`), and the pointwise bound
`|(K ⋆ (f - g_k))(x)| ≤ ‖K‖_1^(1-1/p) B^(1/p) ‖f - g_k‖_p` (`Rd.enorm_conv_le_of_enorm_le`) makes
the convergence `K ⋆ g_k → K ⋆ f` uniform. -/
theorem continuous_conv_of_enorm_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K : V → ℂ}
    (hK : Integrable K) {B : ℝ≥0∞} (hB : ∀ y, ‖K y‖ₑ ≤ B) (hBtop : B ≠ ∞) {f : V → ℂ}
    (hf : MemLp f p volume) : Continuous (conv K f volume) := by
  have hC : eLpNorm K 1 volume ^ (1 - 1 / p.toReal) * B ^ (1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (one_sub_one_div_toReal_nonneg hp1)
      (memLp_one_iff_integrable.2 hK).eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hBtop)
  choose g hgs hgle hgc hgm using fun k : ℕ => hf.exists_hasCompactSupport_eLpNorm_sub_le hp
    (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top k))
  refine TendstoUniformly.continuous (F := fun k => conv K (g k) volume) (p := atTop) ?_
    (Frequently.of_forall fun k => by
      exact (hgs k).continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
        hK.locallyIntegrable (hgc k))
  rw [EMetric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => eLpNorm K 1 volume ^ (1 - 1 / p.toReal) *
      B ^ (1 / p.toReal) * (k : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with k hk x
  rw [eDist_eq_eNorm_sub, conv_sub_apply_of_enorm_le hp1 hK hB hBtop hf (hgm k) x]
  refine lt_of_le_of_lt ?_ hk
  calc ‖conv K (f - g k) volume x‖ₑ
      ≤ eLpNorm K 1 volume ^ (1 - 1 / p.toReal) * B ^ (1 / p.toReal) *
          eLpNorm (f - g k) p volume :=
        enorm_conv_le_of_enorm_le hp1 hp hK.aestronglyMeasurable hB
          (hf.aestronglyMeasurable.sub (hgm k).aestronglyMeasurable) x
    _ ≤ _ := by gcongr; exact hgle k

/-- **Convolutions of Schwartz functions with `L_p` functions are continuous**, for
`1 ≤ p < ∞`: a Schwartz function `G` is integrable and bounded by its decay constant
`Rd.schwartzDecayConst G 0 0` (`Rd.enorm_schwartz_le`), so `Rd.continuous_conv_of_enorm_le`
applies. -/
theorem continuous_conv_schwartz {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) (G : 𝓢(V, ℂ))
    {f : V → ℂ} (hf : MemLp f p volume) : Continuous (conv G f volume) :=
  continuous_conv_of_enorm_le hp1 hp G.integrable (fun y => by simpa using enorm_schwartz_le G 0 y)
    (schwartzDecayConst_ne_top G 0 0) hf

/-- The Littlewood–Paley kernel `ψ_j` is the Schwartz function `(psiBase j)_{2^j}`
(`Rd.dilate_psiBase`). -/
theorem coe_schwartzDilate_psiBase (j : ℕ) :
    (schwartzDilate ((2 : ℝ) ^ j) (by positivity) (psiBase (V := V) j) : V → ℂ) = psi j :=
  (coe_schwartzDilate _ _ _).trans (dilate_psiBase j)

/-- The band-limiting kernel `Θ_j` is the Schwartz function `Θ_{2^j}`. -/
theorem coe_schwartzDilate_bandKernelS (j : ℕ) :
    (schwartzDilate ((2 : ℝ) ^ j) (by positivity) (bandKernelS (V := V)) : V → ℂ) = Theta j :=
  coe_schwartzDilate _ _ _

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The blocks are continuous**: for `1 ≤ p < ∞` and `f ∈ L_p(V)`, `ψ_j ⋆ f` is continuous,
since `ψ_j` is a Schwartz function (`Rd.continuous_conv_schwartz`). -/
theorem continuous_blockFun (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Continuous (blockFun j f) := by
  rw [blockFun, ← coe_schwartzDilate_psiBase]
  exact continuous_conv_schwartz Fact.out hp _ (Lp.memLp f)

/-! ### The Nikolskii inequality for blocks -/

/-- The supremum `sup |Θ|` of the band-limiting kernel is finite (`Rd.bddAbove_bandKernel`). -/
theorem iSup_enorm_bandKernel_lt_top : (⨆ y, ‖bandKernel (V := V) y‖ₑ) < ∞ :=
  iSup_enorm_lt_top_of_bddAbove bddAbove_bandKernel

variable (V) in
/-- The **Nikolskii constant** `N_p = ‖Θ‖_1^(1-1/p) (sup |Θ|)^(1/p)` of the blocks, built from the
band-limiting kernel `Θ`. -/
noncomputable def nikolskiiBlockConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (bandKernel (V := V)) 1 volume ^ (1 - 1 / p.toReal) *
    (⨆ y, ‖bandKernel (V := V) y‖ₑ) ^ (1 / p.toReal)

/-- The Nikolskii constant `N_p` is finite for `p ≥ 1`. -/
theorem nikolskiiBlockConst_ne_top : nikolskiiBlockConst V p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (one_sub_one_div_toReal_nonneg Fact.out)
      eLpNorm_bandKernel_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) iSup_enorm_bandKernel_lt_top.ne)

/-- `|Θ_j(y)| ≤ 2^(jn) sup |Θ|` for every `y`, since `Θ_j(y) = 2^(jn) Θ(2^j y)`. -/
theorem enorm_Theta_le (j : ℕ) (y : V) :
    ‖Theta (V := V) j y‖ₑ ≤ 2 ^ (j * finrank ℝ V) * ⨆ z, ‖bandKernel (V := V) z‖ₑ := by
  rw [Theta, enorm_dilate_two_pow]
  gcongr
  exact le_iSup (fun z => ‖bandKernel (V := V) z‖ₑ) _

/-- **The blocks are band-limited at every point**: `Θ_j ⋆ (ψ_j ⋆ f) = ψ_j ⋆ f` for
`1 ≤ p < ∞` and `f ∈ L_p(V)`. Almost everywhere this is associativity and `Θ_j ⋆ ψ_j = ψ_j`
(`Rd.conv_conv_ae`, `Rd.conv_Theta_psi`); both sides are continuous
(`Rd.continuous_conv_schwartz`), so they agree everywhere (Mathlib's
`Continuous.ae_eq_iff_eq`). -/
theorem conv_Theta_blockFun (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    conv (Theta j) (blockFun j f) volume = blockFun j f := by
  have hae : conv (Theta j) (blockFun j f) volume =ᵐ[volume] blockFun j f := by
    have h := conv_conv_ae Fact.out hp (integrable_Theta (V := V) j) (integrable_psi j)
      (Lp.memLp f)
    rw [conv_Theta_psi] at h
    exact h.symm
  refine (Continuous.ae_eq_iff_eq volume ?_ (continuous_blockFun hp j f)).1 hae
  rw [← coe_schwartzDilate_bandKernelS]
  exact continuous_conv_schwartz Fact.out hp _ (memLp_blockFun j f)

/-- **The Nikolskii inequality for blocks at every point**: for `1 ≤ p < ∞`, `f ∈ L_p(V)` and
every `x`, `|(ψ_j ⋆ f)(x)| ≤ N_p 2^(jn/p) ‖ψ_j ⋆ f‖_p`. The block is `Θ_j ⋆ (ψ_j ⋆ f)`
(`Rd.conv_Theta_blockFun`), and the pointwise bound of convolutions with `‖Θ_j‖_1 = ‖Θ‖_1` and
`|Θ_j| ≤ 2^(jn) sup |Θ|` gives the factor `2^(jn/p)` (`ENNReal.two_pow_rpow_eq_dyadicWeight`). -/
theorem enorm_blockFun_le_nikolskii (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V))
    (x : V) :
    ‖blockFun j f x‖ₑ ≤ nikolskiiBlockConst V p *
      dyadicWeight (nikolskiiExponent (finrank ℝ V) p ∞) j * eLpNorm (blockFun j f) p volume := by
  calc ‖blockFun j f x‖ₑ = ‖conv (Theta j) (blockFun j f) volume x‖ₑ := by
        rw [conv_Theta_blockFun hp j f]
    _ ≤ eLpNorm (Theta (V := V) j) 1 volume ^ (1 - 1 / p.toReal) *
          (2 ^ (j * finrank ℝ V) * ⨆ z, ‖bandKernel (V := V) z‖ₑ) ^ (1 / p.toReal) *
          eLpNorm (blockFun j f) p volume :=
        enorm_conv_le_of_enorm_le Fact.out hp (integrable_Theta j).aestronglyMeasurable
          (enorm_Theta_le j) (aestronglyMeasurable_blockFun j f) x
    _ = _ := by
        rw [eLpNorm_Theta_one, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ENNReal.two_pow_rpow_eq_dyadicWeight, nikolskiiExponent_top, nikolskiiBlockConst, one_div]
        ring

/-- **The Nikolskii inequality for blocks**: for `1 ≤ p ≤ r ≤ ∞`, `p < ∞` and `f ∈ L_p(V)`,
`‖ψ_j ⋆ f‖_r ≤ N_p^(1-p/r) 2^(j α) ‖ψ_j ⋆ f‖_p` with `α = n(1/p - 1/r)`. For `r = ∞` this is
`Rd.enorm_blockFun_le_nikolskii`; for `r < ∞` interpolation
(`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow`) gives the exponent `(n/p)(1 - p/r) = α`. -/
theorem eLpNorm_blockFun_le_nikolskii (hp : p ≠ ∞) {r : ℝ≥0∞} (hpr : p ≤ r) (j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (blockFun j f) r volume ≤ nikolskiiBlockConst V p ^ (1 - p.toReal / r.toReal) *
      dyadicWeight (nikolskiiExponent (finrank ℝ V) p r) j * eLpNorm (blockFun j f) p volume := by
  have hb := enorm_blockFun_le_nikolskii hp j f
  rcases eq_or_ne r ∞ with rfl | hr
  · rw [ENNReal.toReal_top, div_zero, sub_zero, ENNReal.rpow_one,
      eLpNorm_exponent_top (aestronglyMeasurable_blockFun j f)]
    exact eLpNormEssSup_le_of_ae_eNorm_bound (ae_of_all _ hb)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hpp : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hrr : 0 < r.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le ((Fact.out : 1 ≤ p).trans hpr)).ne' hr
  have h1 : 0 ≤ 1 - p.toReal / r.toReal := ENNReal.one_sub_toReal_div_nonneg hpr
  have hθ : 0 ≤ p.toReal / r.toReal := by positivity
  have hexp : (finrank ℝ V : ℝ) * p.toReal⁻¹ * (1 - p.toReal / r.toReal) =
      nikolskiiExponent (finrank ℝ V) p r := by
    unfold nikolskiiExponent
    field_simp
  calc eLpNorm (blockFun j f) r volume
      ≤ (nikolskiiBlockConst V p * dyadicWeight (nikolskiiExponent (finrank ℝ V) p ∞) j *
          eLpNorm (blockFun j f) p volume) ^ (1 - p.toReal / r.toReal) *
          eLpNorm (blockFun j f) p volume ^ (p.toReal / r.toReal) :=
        eLpNorm_le_rpow_mul_eLpNorm_rpow (aestronglyMeasurable_blockFun j f) (ae_of_all _ hb)
          hp0 hpr hr
    _ = nikolskiiBlockConst V p ^ (1 - p.toReal / r.toReal) *
          dyadicWeight (nikolskiiExponent (finrank ℝ V) p ∞) j ^ (1 - p.toReal / r.toReal) *
          (eLpNorm (blockFun j f) p volume ^ (1 - p.toReal / r.toReal) *
            eLpNorm (blockFun j f) p volume ^ (p.toReal / r.toReal)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1, ENNReal.mul_rpow_of_nonneg _ _ h1]
        ring
    _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ h1 hθ, sub_add_cancel, ENNReal.rpow_one,
          ENNReal.dyadicWeight_rpow, nikolskiiExponent_top, hexp]

/-- **The blocks lie in `L_r`** for `1 ≤ p ≤ r ≤ ∞`, `p < ∞` and `f ∈ L_p(V)`, by the Nikolskii
inequality for blocks (`Rd.eLpNorm_blockFun_le_nikolskii`). -/
theorem memLp_blockFun_of_le (hp : p ≠ ∞) {r : ℝ≥0∞} (hpr : p ≤ r) (j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) : MemLp (blockFun j f) r volume :=
  memLp_iff.2 <| (eLpNorm_blockFun_le_nikolskii hp hpr j f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg
      (ENNReal.one_sub_toReal_div_nonneg hpr) nikolskiiBlockConst_ne_top)
      (ENNReal.dyadicWeight_lt_top _ _)) (memLp_blockFun j f).eLpNorm_lt_top)

/-! ### Besov embeddings -/

/-- **The series of the blocks converges almost everywhere**: for `1 ≤ p < ∞`, `s > 0`,
`1 ≤ q ≤ ∞` and `f ∈ L_p(V)` with a finite Littlewood–Paley quasi-norm, `∑_j (ψ_j ⋆ f)(x) = f(x)`
for almost every `x`. The norms `‖Δ_j f‖_p` are summable (`ENNReal.tsum_le_lqNorm_dyadicWeight`),
`f = ∑_j Δ_j f` in `L_p` (`Rd.hasSum_lpBlock`), and an absolutely convergent series in `L_p`
converges almost everywhere (Mathlib's `MeasureTheory.Lp.hasSum_coeFn_tsum`). -/
theorem ae_hasSum_blockFun (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : littlewoodPaleyNorm hp s q f < ∞) :
    ∀ᵐ x ∂volume, HasSum (fun j => blockFun j f x) (f x) := by
  have htsum : ∑' j, ‖lpBlock hp j f‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs) hf.ne)
      (ENNReal.tsum_le_lqNorm_dyadicWeight hq s _)
  have h1 := Lp.hasSum_coeFn_tsum htsum
  rw [(hasSum_lpBlock hp hs hq hf).tsum_eq] at h1
  have h2 : ∀ᵐ x ∂volume, ∀ j, lpBlock hp j f x = blockFun j f x :=
    ae_all_iff.2 fun j => lpBlock_ae_eq_blockFun hp j f
  filter_upwards [h1, h2] with x hx1 hx2
  simpa only [hx2] using hx1

variable (V) in
/-- The **constant of the Besov embedding** into `L_r`,
`K_{V,p,r,s} = N_p^(1-p/r) (1 - 2^(-(s - α)))⁻¹` with `α = n(1/p - 1/r)`. -/
noncomputable def besovEmbeddingConst (p r : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  nikolskiiBlockConst V p ^ (1 - p.toReal / r.toReal) *
    (1 - (2 : ℝ≥0∞) ^ (-(s - nikolskiiExponent (finrank ℝ V) p r)))⁻¹

/-- The constant of the Besov embedding is finite for `p ≤ r` and `s > n(1/p - 1/r)`. -/
theorem besovEmbeddingConst_ne_top {r : ℝ≥0∞} (hpr : p ≤ r) {s : ℝ}
    (hs : nikolskiiExponent (finrank ℝ V) p r < s) : besovEmbeddingConst V p r s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (ENNReal.one_sub_toReal_div_nonneg hpr)
    nikolskiiBlockConst_ne_top) (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 hs))

/-- **The Nikolskii bounds are summable**: for `1 ≤ p < ∞`, every `r`, `s ∈ ℝ`, `1 ≤ q ≤ ∞` and
`f ∈ L_p(V)`,
`∑_j N_p^(1-p/r) 2^(jα) ‖ψ_j ⋆ f‖_p ≤ K_{V,p,r,s} ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`, since the weights
`2^(-j(s-α))` absorb the `ℓ_q` norm (`ENNReal.tsum_le_lqNorm_dyadicWeight`). -/
theorem tsum_nikolskii_le (hp : p ≠ ∞) {r : ℝ≥0∞} (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f : Lp ℂ p (volume : Measure V)) :
    ∑' j, nikolskiiBlockConst V p ^ (1 - p.toReal / r.toReal) *
      dyadicWeight (nikolskiiExponent (finrank ℝ V) p r) j * eLpNorm (blockFun j f) p volume ≤
      besovEmbeddingConst V p r s * littlewoodPaleyNorm hp s q f := by
  set α := nikolskiiExponent (finrank ℝ V) p r
  set K := nikolskiiBlockConst V p ^ (1 - p.toReal / r.toReal)
  have hw : (fun j => dyadicWeight (s - α) j *
      (dyadicWeight α j * eLpNorm (blockFun j f) p volume)) =
      fun j => dyadicWeight s j * ‖lpBlock hp j f‖ₑ := by
    funext j
    rw [← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel,
      enorm_lpBlock_eq_eLpNorm_blockFun]
  calc ∑' j, K * dyadicWeight α j * eLpNorm (blockFun j f) p volume
      = K * ∑' j, dyadicWeight α j * eLpNorm (blockFun j f) p volume := by
        simp_rw [mul_assoc]
        exact ENNReal.tsum_mul_left
    _ ≤ K * ((1 - (2 : ℝ≥0∞) ^ (-(s - α)))⁻¹ * lqNorm q (fun j => dyadicWeight (s - α) j *
          (dyadicWeight α j * eLpNorm (blockFun j f) p volume))) := by
        gcongr
        exact ENNReal.tsum_le_lqNorm_dyadicWeight hq (s - α) _
    _ = besovEmbeddingConst V p r s * littlewoodPaleyNorm hp s q f := by
        rw [hw, besovEmbeddingConst, littlewoodPaleyNorm, mul_assoc]

/-- **The `L_r` norms of the blocks are summable**: for `1 ≤ p ≤ r ≤ ∞`, `p < ∞`, `s ∈ ℝ`,
`1 ≤ q ≤ ∞` and `f ∈ L_p(V)`,
`∑_j ‖ψ_j ⋆ f‖_r ≤ K_{V,p,r,s} ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}` (the Nikolskii inequality for
blocks and `Rd.tsum_nikolskii_le`). -/
theorem tsum_eLpNorm_blockFun_le (hp : p ≠ ∞) {r : ℝ≥0∞} (hpr : p ≤ r) (s : ℝ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    ∑' j, eLpNorm (blockFun j f) r volume ≤
      besovEmbeddingConst V p r s * littlewoodPaleyNorm hp s q f :=
  (tsum_le_tsum fun j => eLpNorm_blockFun_le_nikolskii hp hpr j f).trans
    (tsum_nikolskii_le hp s hq f)

/-- **The Besov embedding into `L_r`**: for `1 ≤ p ≤ r ≤ ∞`, `p < ∞`,
`s > α = n(1/p - 1/r)`, `1 ≤ q ≤ ∞` and `f ∈ B^s_{p,q}` (band-limited approximation in `L_p`),
there is `g ∈ L_r(V)` with `g = f` almost everywhere and
`‖g‖_r ≤ K_{V,p,r,s} ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`. The blocks lie in `L_r`, their series
converges absolutely in `L_r` (`Rd.tsum_eLpNorm_blockFun_le`), its sum `g` is the almost
everywhere limit of the series (Mathlib's `MeasureTheory.Lp.hasSum_coeFn_tsum`), and so is `f`
(`Rd.ae_hasSum_blockFun`). -/
theorem exists_memLp_ae_eq_of_memApprox (hp : p ≠ ∞) {r : ℝ≥0∞} (hpr : p ≤ r)
    {s : ℝ} (hs : nikolskiiExponent (finrank ℝ V) p r < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : (bandScheme hp).MemApprox s q f) :
    ∃ g : Lp ℂ r (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f ∧
      ‖g‖ₑ ≤ besovEmbeddingConst V p r s * littlewoodPaleyNorm hp s q f := by
  have : Fact (1 ≤ r) := ⟨(Fact.out : 1 ≤ p).trans hpr⟩
  have hs0 : 0 < s :=
    (nikolskiiExponent_nonneg (Nat.cast_nonneg _) Fact.out hpr).trans_lt hs
  have hLP : littlewoodPaleyNorm hp s q f < ∞ := (memApprox_bandScheme_iff hp hs0 hq).1 hf
  set u : ℕ → Lp ℂ r (volume : Measure V) := fun j => (memLp_blockFun_of_le hp hpr j f).toLp _
  have htsum : ∑' j, ‖u j‖ₑ ≤ besovEmbeddingConst V p r s * littlewoodPaleyNorm hp s q f := by
    simp only [u, Lp.eNorm_toLp]
    exact tsum_eLpNorm_blockFun_le hp hpr s hq f
  have hfin : ∑' j, ‖u j‖ₑ ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (besovEmbeddingConst_ne_top hpr hs) hLP.ne) htsum
  refine ⟨∑' j, u j, ?_, eNorm_tsum_le_tsum_eNorm.trans htsum⟩
  have h2 : ∀ᵐ x ∂volume, ∀ j, u j x = blockFun j f x :=
    ae_all_iff.2 fun j => MemLp.coeFn_toLp _
  filter_upwards [Lp.hasSum_coeFn_tsum hfin, h2, ae_hasSum_blockFun hp hs0 hq hLP]
    with x hx1 hx2 hx3
  simp only [hx2] at hx1
  exact hx1.unique hx3

/-- **The Besov embedding into bounded continuous functions**: for `1 ≤ p < ∞`, `s > n/p`,
`1 ≤ q ≤ ∞` and `f ∈ B^s_{p,q}` (band-limited approximation in `L_p`), there is a bounded
continuous function `a` with `a = f` almost everywhere and
`sup |a| ≤ K_{V,p,∞,s} ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q}`. The blocks are continuous
(`Rd.continuous_blockFun`) and bounded at every point by the summable Nikolskii bounds
(`Rd.enorm_blockFun_le_nikolskii`, `Rd.tsum_nikolskii_le`), so their series converges uniformly
to a continuous function (Mathlib's `continuous_tsum`), which is `f` almost everywhere
(`Rd.ae_hasSum_blockFun`); its sup norm is the supremum of `|a(x)|` (Mathlib's
`BoundedContinuousFunction.eNorm_eq_iSup_eNorm`). -/
theorem exists_boundedContinuous_ae_eq_of_memApprox (hp : p ≠ ∞) {s : ℝ}
    (hs : (finrank ℝ V : ℝ) / p.toReal < s) {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} (hf : (bandScheme hp).MemApprox s q f) :
    ∃ a : V →ᵇ ℂ, (a : V → ℂ) =ᵐ[volume] f ∧
      ‖a‖ₑ ≤ besovEmbeddingConst V p ∞ s * littlewoodPaleyNorm hp s q f := by
  have hα : nikolskiiExponent (finrank ℝ V) p ∞ < s := by
    rwa [nikolskiiExponent_top, ← div_eq_mul_inv]
  have hs0 : 0 < s := (nikolskiiExponent_nonneg (Nat.cast_nonneg _) Fact.out le_top).trans_lt hα
  have hLP : littlewoodPaleyNorm hp s q f < ∞ := (memApprox_bandScheme_iff hp hs0 hq).1 hf
  set b : ℕ → ℝ≥0∞ := fun j => nikolskiiBlockConst V p ^ (1 - p.toReal / (∞ : ℝ≥0∞).toReal) *
    dyadicWeight (nikolskiiExponent (finrank ℝ V) p ∞) j * eLpNorm (blockFun j f) p volume
  have htsum : ∑' j, b j ≤ besovEmbeddingConst V p ∞ s * littlewoodPaleyNorm hp s q f :=
    tsum_nikolskii_le hp s hq f
  have hfin : ∑' j, b j ≠ ∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (besovEmbeddingConst_ne_top le_top hα) hLP.ne) htsum
  have hb : ∀ j x, ‖blockFun j f x‖ₑ ≤ b j := fun j x =>
    (enorm_blockFun_le_nikolskii hp j f x).trans_eq (by
      simp only [b, ENNReal.toReal_top, div_zero, sub_zero, ENNReal.rpow_one])
  have hnorm : ∀ j x, ‖blockFun j f x‖ ≤ (b j).toReal := fun j x => by
    rw [← toReal_eNorm]
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (le_tsum _ j)) (hb j x)
  have hsum : Summable fun j => (b j).toReal := ENNReal.summable_toReal hfin
  have hac : Continuous fun x => ∑' j, blockFun j f x :=
    continuous_tsum (fun j => continuous_blockFun hp j f) hsum hnorm
  have hab : ∀ x, ‖∑' j, blockFun j f x‖ ≤ ∑' j, (b j).toReal := fun x =>
    tsum_of_norm_bounded hsum.hasSum fun j => hnorm j x
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hac _ hab, ?_, ?_⟩
  · filter_upwards [ae_hasSum_blockFun hp hs0 hq hLP] with x hx
    exact hx.tsum_eq
  · rw [BoundedContinuousFunction.eNorm_eq_iSup_eNorm]
    exact iSup_le fun x => eNorm_tsum_le_tsum_eNorm.trans
      ((tsum_le_tsum fun j => hb j x).trans htsum)

/-! ### Sobolev embeddings -/

/-- **The Sobolev embedding into `L_r` with named constants**: let `n ≥ 1`, `1 < p ≤ r ≤ ∞`,
`p < ∞` and `m > n(1/p - 1/r)`, and let `f ∈ L_p(V)` have weak derivatives `g_α ∈ L_p(V)` of
order `m` along the basis `e` of `Rd.gridBasis` for every multi-index `α`. Then there is
`u ∈ L_r(V)` with `u = f` almost everywhere and
`‖u‖_r ≤ K_{V,p,r,m} (‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p)` with `K_α = Rd.sobolevToTLConst V p α`.
The bound of `‖f‖_{F^m_{p,2}}` (`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`) bounds the
Littlewood–Paley quasi-norm of `B^m_{p,max(p,2)}`
(`Rd.littlewoodPaleyNorm_max_le_triebelLizorkinNorm`), and the Besov embedding
(`Rd.exists_memLp_ae_eq_of_memApprox`) applies. The critical case `1/r = 1/p - m/n` with `r < ∞`
(Sobolev's inequality) is `Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_of_eq`; for `m = 1` and
every `1 ≤ p`, `p = 1` included, it is `Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_one`. -/
theorem exists_memLp_ae_eq_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {r : ℝ≥0∞} (hpr : p ≤ r) {m : ℕ} (hs : nikolskiiExponent (finrank ℝ V) p r < m)
    {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∃ u : Lp ℂ r (volume : Measure V), (u : V → ℂ) =ᵐ[volume] f ∧
      ‖u‖ₑ ≤ besovEmbeddingConst V p r m * (eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ) := by
  have hm : 1 ≤ m := one_le_of_nikolskiiExponent_lt (Nat.cast_nonneg _) Fact.out hpr hs
  obtain ⟨u, hu, hn⟩ := exists_memLp_ae_eq_of_memApprox hp hpr hs
    (one_le_two.trans (le_max_right _ _)) (memApprox_of_memTriebelLizorkin hp
      (Nat.cast_pos.2 hm) one_le_two (memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg))
  refine ⟨u, hu, hn.trans ?_⟩
  gcongr
  exact (littlewoodPaleyNorm_max_le_triebelLizorkinNorm hp one_le_two f).trans
    (triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg)

/-- **The Sobolev embedding into bounded continuous functions with named constants**: let
`n ≥ 1`, `1 < p < ∞` and `m > n/p`, and let `f ∈ L_p(V)` have weak derivatives `g_α ∈ L_p(V)` of
order `m` along the basis `e` of `Rd.gridBasis` for every multi-index `α`. Then there is a
bounded continuous function `a` with `a = f` almost everywhere and
`sup |a| ≤ K_{V,p,∞,m} (‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p)` with
`K_α = Rd.sobolevToTLConst V p α`, by the same argument as
`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv` with the Besov embedding into bounded continuous
functions (`Rd.exists_boundedContinuous_ae_eq_of_memApprox`). -/
theorem exists_boundedContinuous_ae_eq_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) {m : ℕ} (hs : (finrank ℝ V : ℝ) / p.toReal < m)
    {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∃ a : V →ᵇ ℂ, (a : V → ℂ) =ᵐ[volume] f ∧
      ‖a‖ₑ ≤ besovEmbeddingConst V p ∞ m * (eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ) := by
  have hα : nikolskiiExponent (finrank ℝ V) p ∞ < m := by
    rwa [nikolskiiExponent_top, ← div_eq_mul_inv]
  have hm : 1 ≤ m := one_le_of_nikolskiiExponent_lt (Nat.cast_nonneg _) Fact.out le_top hα
  obtain ⟨a, ha, hn⟩ := exists_boundedContinuous_ae_eq_of_memApprox hp hs
    (one_le_two.trans (le_max_right _ _)) (memApprox_of_memTriebelLizorkin hp
      (Nat.cast_pos.2 hm) one_le_two (memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg))
  refine ⟨a, ha, hn.trans ?_⟩
  gcongr
  exact (littlewoodPaleyNorm_max_le_triebelLizorkinNorm hp one_le_two f).trans
    (triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg)

/-- **The Sobolev embedding into `L_r`**: let `n ≥ 1`, `1 < p ≤ r ≤ ∞`, `p < ∞` and
`m > n(1/p - 1/r)`. Every `f ∈ W^m_p(V)` has a representative in `L_r(V)`: there is
`g ∈ L_r(V)` with `g = f` almost everywhere. This is `W^m_p ⊆ B^m_{p,max(p,2)}`
(`Rd.memApprox_of_memSobolev`) and the Besov embedding (`Rd.exists_memLp_ae_eq_of_memApprox`);
`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv` adds the norm bound. The critical case
`1/r = 1/p - m/n` with `r < ∞` (Sobolev's inequality) is
`Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`, and for `p = 1`
`Rd.exists_memLp_ae_eq_of_memSobolev_one_of_eq`. -/
theorem exists_memLp_ae_eq_of_memSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {r : ℝ≥0∞} (hpr : p ≤ r) {m : ℕ}
    (hs : nikolskiiExponent (finrank ℝ V) p r < m) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemSobolev m f) : ∃ g : Lp ℂ r (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f := by
  have hm : 1 ≤ m := one_le_of_nikolskiiExponent_lt (Nat.cast_nonneg _) Fact.out hpr hs
  obtain ⟨g, hg, -⟩ := exists_memLp_ae_eq_of_memApprox hp hpr hs
    (one_le_two.trans (le_max_right _ _)) (memApprox_of_memSobolev hp1 hp hm hf)
  exact ⟨g, hg⟩

/-- **The Sobolev embedding into bounded continuous functions**: let `n ≥ 1`, `1 < p < ∞` and
`m > n/p`. Every `f ∈ W^m_p(V)` has a bounded continuous representative. This is
`W^m_p ⊆ B^m_{p,max(p,2)}` (`Rd.memApprox_of_memSobolev`) and the Besov embedding into bounded
continuous functions (`Rd.exists_boundedContinuous_ae_eq_of_memApprox`);
`Rd.exists_boundedContinuous_ae_eq_of_hasWeakLineDeriv` adds the norm bound. -/
theorem exists_boundedContinuous_ae_eq_of_memSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} (hs : (finrank ℝ V : ℝ) / p.toReal < m) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemSobolev m f) : ∃ a : V →ᵇ ℂ, (a : V → ℂ) =ᵐ[volume] f := by
  have hα : nikolskiiExponent (finrank ℝ V) p ∞ < m := by
    rwa [nikolskiiExponent_top, ← div_eq_mul_inv]
  have hm : 1 ≤ m := one_le_of_nikolskiiExponent_lt (Nat.cast_nonneg _) Fact.out le_top hα
  obtain ⟨a, ha, -⟩ := exists_boundedContinuous_ae_eq_of_memApprox hp hs
    (one_le_two.trans (le_max_right _ _)) (memApprox_of_memSobolev hp1 hp hm hf)
  exact ⟨a, ha⟩

end Rd
