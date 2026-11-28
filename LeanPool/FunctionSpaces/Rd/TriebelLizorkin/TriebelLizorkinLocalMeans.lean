/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkin
public import LeanPool.FunctionSpaces.Rd.LocalMeans.KernelMajorants
public import LeanPool.FunctionSpaces.Analysis.Maximal.FeffermanStein

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Local means for Triebel–Lizorkin spaces

For a bump `b` of radius `R` and an order `L`, the local means `k_j ⋆ f` of
`FunctionSpaces.Rd.LocalMeans.LocalMeans` define the quasi-norm

`‖f‖_{F^s_{p,q}}^{b,L} = ‖ x ↦ ‖(2^(js) |k_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`

(`Rd.LocalMeansBump.tlLocalMeansNorm`). For `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L` it is
equivalent to the Triebel–Lizorkin quasi-norm, with explicit constants
(`Rd.LocalMeansBump.triebelLizorkinNorm_le_tlLocalMeansNorm`,
`Rd.LocalMeansBump.tlLocalMeansNorm_le_triebelLizorkinNorm`), so `F^s_{p,q}` is described by
local means (`Rd.LocalMeansBump.memTriebelLizorkin_iff_tlLocalMeans`), and every bump and every
order `L > s` give the same space (`Rd.LocalMeansBump.tlLocalMeansNorm_lt_top_iff`).

The proof is pointwise in `x`. The reproducing formula `f = ∑_i η_i ⋆ k_i ⋆ f` and the cross
kernels `ψ_j ⋆ η_i` of `FunctionSpaces.Rd.LocalMeans.KernelMajorants` give
`|ψ_j ⋆ f(x)| ≤ C ∑_i c_{ji} M(k_i ⋆ f)(x)` almost everywhere
(`Rd.LocalMeansBump.enorm_blockFun_le_tsum_maximal`); the decomposition `f = ∑_i ψ_i ⋆ f`
and the cross kernels `k_j ⋆ Θ_i` give `|k_j ⋆ f(x)| ≤ C ∑_i c_{ji} M(ψ_i ⋆ f)(x)`
(`Rd.LocalMeansBump.enorm_localMean_le_tsum_maximal`). The factors `c_{ji}` decay geometrically
below the diagonal, so the almost diagonal estimate in `ℓ_q`
(`ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le`) and the Fefferman–Stein inequality
(`Rd.feffermanStein`) finish. The partial sums of the two decompositions converge in `L_p`, and
the pointwise bounds pass to the limit by `MeasureTheory.ae_enorm_le_of_tendsto_Lp`.

The first half works for every synthesis sum: if `F = ∑_i η_i ⋆ h_i` in `L_p`, then
`‖F‖_{F^s_{p,q}} ≤ C ‖ x ↦ ‖(2^(is) |h_i(x)|)_i‖_{ℓ_q} ‖_p`
(`Rd.LocalMeansBump.triebelLizorkinNorm_le_of_tendsto_sum_dual`).
-/

@[expose] public section

open MeasureTheory Module Filter Topology
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Sequences and maximal functions -/

/-- The weights `c_{ji} = 2^(-(j-i)L)` for `i ≤ j` and `c_{ji} = 1` for `i > j` are finite. -/
theorem ite_dyadicWeight_ne_top (L : ℝ) (i j : ℕ) :
    (if i ≤ j then dyadicWeight (-L) (j - i) else 1) ≠ ∞ := by
  split_ifs
  · exact ENNReal.dyadicWeight_ne_top _ _
  · exact ENNReal.one_ne_top

/-- The weights go inside the maximal function: `2^(is) M g(x) = M(2^(is) g)(x)`. -/
theorem dyadicWeight_mul_maximal (s : ℝ) (i : ℕ) (g : V → ℝ≥0∞) (x : V) :
    dyadicWeight s i * maximal g x = maximal (fun y => dyadicWeight s i * g y) x :=
  (maximal_const_mul (ENNReal.dyadicWeight_ne_top s i) g x).symm

omit [Fact (1 ≤ p)] in
/-- **From pointwise maximal bounds to `L_p(ℓ_q)`**: for `1 < p < ∞` and `1 < q ≤ ∞`, if
`F ≤ C ‖(M g_i)_i‖_{ℓ_q}` almost everywhere, with almost everywhere measurable `F` and `g_i`,
then
`‖F‖_p ≤ C C_{FS} ‖ x ↦ ‖(g_i(x))_i‖_{ℓ_q} ‖_p` with the Fefferman–Stein constant
`C_{FS} = Rd.feffermanSteinConst V p q`. -/
theorem eLpNorm_le_of_le_lqNorm_maximal (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q)
    {F : V → ℝ≥0∞} (hF : AEMeasurable F volume) {g : ℕ → V → ℝ≥0∞}
    (hg : ∀ i, AEMeasurable (g i) volume) {C : ℝ≥0∞}
    (h : ∀ᵐ x ∂volume, F x ≤ C * lqNorm q (fun i => maximal (g i) x)) :
    eLpNorm F p volume ≤
      C * feffermanSteinConst V p q * eLpNorm (fun x => lqNorm q (fun i => g i x)) p volume :=
  calc eLpNorm F p volume
      ≤ eLpNorm (fun x => C * lqNorm q (fun i => maximal (g i) x)) p volume :=
        eLpNorm_mono_eNorm_ae hF.aestronglyMeasurable (h.mono fun x hx => by
          simpa only [eNorm_eq_self] using hx)
    _ = C * eLpNorm (fun x => lqNorm q (fun i => maximal (g i) x)) p volume :=
        eLpNorm_const_mul_ennreal (c := C) (aemeasurable_lqNorm_comp
          (fun i => (measurable_maximal (g i)).aemeasurable) q).aestronglyMeasurable
    _ ≤ C * (feffermanSteinConst V p q *
          eLpNorm (fun x => lqNorm q (fun i => g i x)) p volume) := by
        gcongr
        exact feffermanStein hp1 hp hq1 g hg
    _ = _ := by rw [mul_assoc]

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-! ### The local means quasi-norm -/

/-- The **local means quasi-norm of Triebel–Lizorkin type**
`‖ x ↦ ‖(2^(js) |k_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`, with the local means kernels `k_j` of the bump `b`
and the order `L`: the `ℓ_q` norm at each point, then the `L_p` norm. -/
noncomputable def tlLocalMeansNorm (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ))
    p volume

/-- The local means `k_j ⋆ f ∈ L_p` are represented by the pointwise convolutions. -/
theorem localMean_ae_eq (hp : p ≠ ∞) (L j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    b.localMean hp L j f =ᵐ[volume] conv (b.kernel L j) f volume :=
  convLp_apply_ae hp (b.integrable_kernel L j) f

/-- The pointwise local means `k_j ⋆ f` are continuous, since `k_j` is continuous with compact
support and `f` is locally integrable. -/
theorem continuous_conv_kernel (L j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    Continuous (conv (b.kernel L j) f volume) :=
  (b.hasCompactSupport_kernel L j).continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
    (b.continuous_kernel L j) ((Lp.memLp f).locallyIntegrable Fact.out)

/-- The weighted local means `2^(js) |k_j ⋆ f|` are measurable. -/
theorem measurable_dyadicWeight_mul_conv_kernel (L : ℕ) (s : ℝ) (j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    Measurable fun y => dyadicWeight s j * ‖conv (b.kernel L j) f volume y‖ₑ :=
  (b.continuous_conv_kernel L j f).measurable.eNorm.const_mul _

/-- The pointwise `ℓ_q` norm of the weighted local means is measurable. -/
theorem aemeasurable_lqNorm_conv_kernel (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    AEMeasurable (fun x => lqNorm q (fun j => dyadicWeight s j *
      ‖conv (b.kernel L j) f volume x‖ₑ)) volume :=
  aemeasurable_lqNorm_comp
    (fun j => (b.measurable_dyadicWeight_mul_conv_kernel L s j f).aemeasurable) q

/-! ### Blocks by local means -/

/-- The constant `C_{L,L',n+1} C_{n,n+1}` of the bound of the blocks by local means: the constant
of the cross kernels `ψ_j ⋆ η_i` (`Rd.LocalMeansBump.psiDualConst`) at the decay order `n + 1`
times the constant of the maximal function bound (`Rd.decayMaximalConst`). -/
noncomputable def blockByLocalMeansConst (L L' : ℕ) : ℝ≥0∞ :=
  b.psiDualConst L L' (finrank ℝ V + 1) * decayMaximalConst V (finrank ℝ V + 1)

/-- The constant of the bound of the blocks by local means is finite. -/
theorem blockByLocalMeansConst_ne_top (L L' : ℕ) : b.blockByLocalMeansConst L L' ≠ ∞ :=
  ENNReal.mul_ne_top (b.psiDualConst_ne_top L L' (Nat.lt_succ_self _))
    (decayMaximalConst_ne_top (Nat.lt_succ_self _))

/-- **One term of the reproducing formula under a block**: for `L' ≥ 1`, all levels `i, j`, every
function `h` and every `x`, `|((ψ_j ⋆ η_i) ⋆ h)(x)| ≤ C c_{ji} M|h|(x)` with
`c_{ji} = 2^(-(j-i)L')` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`. -/
theorem enorm_conv_conv_psi_dual_le (L : ℕ) {L' : ℕ} (hL' : 1 ≤ L') (i j : ℕ) (h : V → ℂ)
    (x : V) :
    ‖conv (conv (psi j) (b.dual L i) volume) h volume x‖ₑ ≤
      b.blockByLocalMeansConst L L' * ((if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i) else 1) *
        maximal (fun y => ‖h y‖ₑ) x) := by
  have hC : b.psiDualConst L L' (finrank ℝ V + 1) *
      (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i) else 1) ≠ ∞ :=
    ENNReal.mul_ne_top (b.psiDualConst_ne_top L L' (Nat.lt_succ_self _))
      (ite_dyadicWeight_ne_top _ i j)
  refine (enorm_conv_le_maximal_of_decay (Nat.lt_succ_self _) hC
    (b.enorm_conv_psi_dual_le L hL' (finrank ℝ V + 1) i j) h x).trans (le_of_eq ?_)
  rw [blockByLocalMeansConst]
  ring

/-! ### Synthesis with the dual kernels -/

/-- **A block of a partial synthesis sum**: for every family `h_i ∈ L_p`, almost everywhere,
`Δ_j (∑_{i ≤ J} η_i ⋆ h_i) = ∑_{i ≤ J} (ψ_j ⋆ η_i) ⋆ h_i`, with pointwise convolutions on the
right. -/
theorem lpBlock_sum_dual_ae (hp : p ≠ ∞) (L J j : ℕ) (h : ℕ → Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, lpBlock hp j (∑ i ∈ Finset.range (J + 1),
        convLp hp (b.integrable_dual L i) (h i)) x =
      ∑ i ∈ Finset.range (J + 1), conv (conv (psi j) (b.dual L i) volume) (h i) volume x := by
  simp only [map_sum, lpBlock, convLp_convLp]
  have hall := ae_all_iff.2 fun i => convLp_apply_ae hp
    (integrable_conv (integrable_psi j) (b.integrable_dual L i)) (h i)
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range (J + 1)) fun i => convLp hp
    (integrable_conv (integrable_psi j) (b.integrable_dual L i)) (h i), hall] with x hx hi
  rw [hx]
  exact Finset.sum_congr rfl fun i _ => hi i

/-- The bound of the blocks of a partial synthesis sum: for `L' ≥ 1`, every `J` and every family
`h_i ∈ L_p`, almost everywhere, `|Δ_j (∑_{i ≤ J} η_i ⋆ h_i)| ≤ C ∑_i c_{ji} M|h_i|` with
`c_{ji} = 2^(-(j-i)L')` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`. -/
theorem ae_enorm_lpBlock_sum_dual_le_tsum_maximal (hp : p ≠ ∞) (L : ℕ) {L' : ℕ} (hL' : 1 ≤ L')
    (J j : ℕ) (h : ℕ → Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ‖lpBlock hp j (∑ i ∈ Finset.range (J + 1),
        convLp hp (b.integrable_dual L i) (h i)) x‖ₑ ≤
      b.blockByLocalMeansConst L L' * ∑' i, (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i)
        else 1) * maximal (fun y => ‖h i y‖ₑ) x := by
  filter_upwards [b.lpBlock_sum_dual_ae hp L J j h] with x hx
  rw [hx]
  refine (eNorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ =>
    b.enorm_conv_conv_psi_dual_le L hL' i j _ x).trans ?_)
  rw [← Finset.mul_sum]
  gcongr
  exact sum_le_tsum _

/-- **The blocks of a synthesis sum, pointwise**: if `F = ∑_i η_i ⋆ h_i` in `L_p` (as the limit
of the partial sums), then for `L' ≥ 1`, almost everywhere and for all levels `j`,
`|ψ_j ⋆ F(x)| ≤ C ∑_i c_{ji} M|h_i|(x)` with `c_{ji} = 2^(-(j-i)L')` for `i ≤ j`, `c_{ji} = 1` for
`i > j`, and `C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`
(`MeasureTheory.ae_enorm_le_of_tendsto_Lp`). -/
theorem enorm_blockFun_le_tsum_maximal_of_tendsto (hp : p ≠ ∞) (L : ℕ) {L' : ℕ} (hL' : 1 ≤ L')
    {F : Lp ℂ p (volume : Measure V)} {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hrep : Tendsto (fun J => ∑ i ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L i) (h i)) atTop (𝓝 F)) :
    ∀ᵐ x ∂volume, ∀ j, ‖blockFun j F x‖ₑ ≤ b.blockByLocalMeansConst L L' *
      ∑' i, (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i) else 1) *
        maximal (fun y => ‖h i y‖ₑ) x := by
  refine ae_all_iff.2 fun j => ?_
  have hlim := ae_enorm_le_of_tendsto_Lp (((lpBlock hp j).continuous.tendsto F).comp hrep)
    (fun J => b.ae_enorm_lpBlock_sum_dual_le_tsum_maximal hp L hL' J j h)
  filter_upwards [hlim, lpBlock_ae_eq_blockFun hp j F] with x hx hb
  rwa [← hb]

/-- **A block of a partial sum of the reproducing formula**: almost everywhere,
`Δ_j (∑_{i ≤ J} η_i ⋆ k_i ⋆ f) = ∑_{i ≤ J} (ψ_j ⋆ η_i) ⋆ (k_i ⋆ f)`, with pointwise
convolutions on the right (`Rd.LocalMeansBump.lpBlock_sum_dual_ae`). -/
theorem lpBlock_sum_dual_localMean_ae (hp : p ≠ ∞) (L J j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, lpBlock hp j (∑ i ∈ Finset.range (J + 1),
        convLp hp (b.integrable_dual L i) (b.localMean hp L i f)) x =
      ∑ i ∈ Finset.range (J + 1),
        conv (conv (psi j) (b.dual L i) volume) (conv (b.kernel L i) f volume) volume x := by
  filter_upwards [b.lpBlock_sum_dual_ae hp L J j fun i => b.localMean hp L i f] with x hx
  rw [hx]
  exact Finset.sum_congr rfl fun i _ => by rw [conv_congr_ae (b.localMean_ae_eq hp L i f)]

/-- The maximal function of a local mean is that of the pointwise convolution `k_i ⋆ f`
(`Rd.maximal_congr_ae`). -/
theorem maximal_enorm_localMean (hp : p ≠ ∞) (L i : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    maximal (fun y => ‖(b.localMean hp L i f : V → ℂ) y‖ₑ) =
      maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) :=
  maximal_congr_ae ((b.localMean_ae_eq hp L i f).mono fun y hy => by simp only [hy])

/-- The bound of the blocks by local means for the partial sums of the reproducing formula: for
`L' ≥ 1` and every `J`, almost everywhere,
`|Δ_j (∑_{i ≤ J} η_i ⋆ k_i ⋆ f)| ≤ C ∑_i c_{ji} M(k_i ⋆ f)` with `c_{ji} = 2^(-(j-i)L')` for
`i ≤ j`, `c_{ji} = 1` for `i > j`, and `C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`
(`Rd.LocalMeansBump.ae_enorm_lpBlock_sum_dual_le_tsum_maximal`). -/
theorem ae_enorm_lpBlock_sum_dual_le (hp : p ≠ ∞) (L : ℕ) {L' : ℕ} (hL' : 1 ≤ L') (J j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ‖lpBlock hp j (∑ i ∈ Finset.range (J + 1),
        convLp hp (b.integrable_dual L i) (b.localMean hp L i f)) x‖ₑ ≤
      b.blockByLocalMeansConst L L' * ∑' i, (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i)
        else 1) * maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) x := by
  simpa only [b.maximal_enorm_localMean hp L] using
    b.ae_enorm_lpBlock_sum_dual_le_tsum_maximal hp L hL' J j fun i => b.localMean hp L i f

/-- **The blocks by local means, pointwise**: for `L ≥ 1`, `L' ≥ 1`, `1 ≤ p < ∞` and
`f ∈ L_p`, almost everywhere and for all levels `j`,
`|ψ_j ⋆ f(x)| ≤ C ∑_i c_{ji} M(k_i ⋆ f)(x)` with `c_{ji} = 2^(-(j-i)L')` for `i ≤ j`,
`c_{ji} = 1` for `i > j`, and `C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`. The reproducing
formula `f = ∑_i η_i ⋆ k_i ⋆ f` holds in `L_p`
(`Rd.LocalMeansBump.enorm_blockFun_le_tsum_maximal_of_tendsto`). -/
theorem enorm_blockFun_le_tsum_maximal {L : ℕ} (hL : 1 ≤ L) {L' : ℕ} (hL' : 1 ≤ L')
    (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ∀ j, ‖blockFun j f x‖ₑ ≤ b.blockByLocalMeansConst L L' *
      ∑' i, (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i) else 1) *
        maximal (fun y => ‖conv (b.kernel L i) f volume y‖ₑ) x := by
  simpa only [b.maximal_enorm_localMean hp L] using
    b.enorm_blockFun_le_tsum_maximal_of_tendsto hp L hL' (b.tendsto_sum_dual_localMean hp hL f)

/-! ### Local means by blocks -/

/-- The constant `C^Θ_{L,n+1} C_{n,n+1}` of the bound of the local means by blocks: the constant
of the cross kernels `k_j ⋆ Θ_i` (`Rd.LocalMeansBump.kernelThetaConst`) at the decay order
`n + 1` times the constant of the maximal function bound (`Rd.decayMaximalConst`). -/
noncomputable def localMeansByBlockConst (L : ℕ) : ℝ≥0∞ :=
  b.kernelThetaConst L (finrank ℝ V + 1) * decayMaximalConst V (finrank ℝ V + 1)

/-- The constant of the bound of the local means by blocks is finite. -/
theorem localMeansByBlockConst_ne_top (L : ℕ) : b.localMeansByBlockConst L ≠ ∞ :=
  ENNReal.mul_ne_top (b.kernelThetaConst_ne_top L _)
    (decayMaximalConst_ne_top (Nat.lt_succ_self _))

/-- **One term of the block decomposition under a local mean**: for all levels `i, j`, every
function `h` and every `x`, `|((k_j ⋆ Θ_i) ⋆ h)(x)| ≤ C c_{ji} M|h|(x)` with
`c_{ji} = 2^(-(j-i)L)` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.localMeansByBlockConst L`. -/
theorem enorm_conv_conv_kernel_Theta_le (L i j : ℕ) (h : V → ℂ) (x : V) :
    ‖conv (conv (b.kernel L j) (Theta i) volume) h volume x‖ₑ ≤
      b.localMeansByBlockConst L * ((if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) *
        maximal (fun y => ‖h y‖ₑ) x) := by
  have hC : b.kernelThetaConst L (finrank ℝ V + 1) *
      (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) ≠ ∞ :=
    ENNReal.mul_ne_top (b.kernelThetaConst_ne_top L _) (ite_dyadicWeight_ne_top _ i j)
  refine (enorm_conv_le_maximal_of_decay (Nat.lt_succ_self _) hC
    (b.enorm_conv_kernel_Theta_le L (finrank ℝ V + 1) i j) h x).trans (le_of_eq ?_)
  rw [localMeansByBlockConst]
  ring

/-- A local mean of a block is the block convolved with the cross kernel:
`k_j ⋆ Δ_i f = (k_j ⋆ Θ_i) ⋆ Δ_i f` in `L_p`, since `Θ_i ⋆ ψ_i = ψ_i`. -/
theorem localMean_lpBlock (hp : p ≠ ∞) (L i j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    b.localMean hp L j (lpBlock hp i f) =
      convLp hp (integrable_conv (b.integrable_kernel L j) (integrable_Theta i))
        (lpBlock hp i f) := by
  have hT : convLp hp (integrable_Theta i) (lpBlock hp i f) = lpBlock hp i f :=
    convLp_convLp_of_eq hp (integrable_Theta i) (integrable_psi i) (integrable_psi i)
      (conv_Theta_psi i) f
  calc b.localMean hp L j (lpBlock hp i f)
      = convLp hp (b.integrable_kernel L j)
          (convLp hp (integrable_Theta i) (lpBlock hp i f)) := by rw [hT]; rfl
    _ = _ := convLp_convLp hp _ _ _

/-- **A local mean of a partial sum of blocks**: almost everywhere,
`k_j ⋆ (∑_{i < J} Δ_i f) = ∑_{i < J} (k_j ⋆ Θ_i) ⋆ (ψ_i ⋆ f)`, with pointwise convolutions on
the right. -/
theorem localMean_sum_lpBlock_ae (hp : p ≠ ∞) (L J j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, b.localMean hp L j (∑ i ∈ Finset.range J, lpBlock hp i f) x =
      ∑ i ∈ Finset.range J,
        conv (conv (b.kernel L j) (Theta i) volume) (blockFun i f) volume x := by
  simp only [map_sum, b.localMean_lpBlock hp L _ j f]
  have hall := ae_all_iff.2 fun i => convLp_apply_ae hp
    (integrable_conv (b.integrable_kernel L j) (integrable_Theta i)) (lpBlock hp i f)
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range J) fun i => convLp hp
    (integrable_conv (b.integrable_kernel L j) (integrable_Theta i)) (lpBlock hp i f), hall]
    with x hx hi
  rw [hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hi i, conv_congr_ae (lpBlock_ae_eq_blockFun hp i f)]

/-- The bound of the local means by blocks for the partial sums of the block decomposition: for
every `J`, almost everywhere, `|k_j ⋆ (∑_{i < J} Δ_i f)| ≤ C ∑_i c_{ji} M(ψ_i ⋆ f)` with
`c_{ji} = 2^(-(j-i)L)` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.localMeansByBlockConst L`. -/
theorem ae_enorm_localMean_sum_lpBlock_le (hp : p ≠ ∞) (L J j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ‖b.localMean hp L j (∑ i ∈ Finset.range J, lpBlock hp i f) x‖ₑ ≤
      b.localMeansByBlockConst L * ∑' i, (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i)
        else 1) * maximal (fun y => ‖blockFun i f y‖ₑ) x := by
  filter_upwards [b.localMean_sum_lpBlock_ae hp L J j f] with x hx
  rw [hx]
  refine (eNorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ =>
    b.enorm_conv_conv_kernel_Theta_le L i j _ x).trans ?_)
  rw [← Finset.mul_sum]
  gcongr
  exact sum_le_tsum _

/-- **The local means by blocks, pointwise**: for every order `L`, `1 ≤ p < ∞` and `f ∈ L_p`,
almost everywhere and for all levels `j`, `|k_j ⋆ f(x)| ≤ C ∑_i c_{ji} M(ψ_i ⋆ f)(x)` with
`c_{ji} = 2^(-(j-i)L)` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.localMeansByBlockConst L`. The decomposition `f = ∑_i Δ_i f` holds in
`L_p`, and the bound passes from its partial sums to `f`
(`MeasureTheory.ae_enorm_le_of_tendsto_Lp`). -/
theorem enorm_localMean_le_tsum_maximal (L : ℕ) (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ∀ j, ‖conv (b.kernel L j) f volume x‖ₑ ≤ b.localMeansByBlockConst L *
      ∑' i, (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i) else 1) *
        maximal (fun y => ‖blockFun i f y‖ₑ) x := by
  refine ae_all_iff.2 fun j => ?_
  have h := ae_enorm_le_of_tendsto_Lp
    (((b.localMean hp L j).continuous.tendsto f).comp (tendsto_sum_lpBlock hp f))
    (fun J => b.ae_enorm_localMean_sum_lpBlock_le hp L J j f)
  filter_upwards [h, b.localMean_ae_eq hp L j f] with x hx hb
  rwa [← hb]

/-! ### The almost diagonal step -/

/-- **The blocks by local means in `ℓ_q`**: for `L ≥ 1`, `L' ≥ 1`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`s ∈ ℝ` and `f ∈ L_p`, almost everywhere,
`‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ≤ C A_{s,L'} ‖(M(2^(is) |k_i ⋆ f|)(x))_i‖_{ℓ_q}` with
`C = Rd.LocalMeansBump.blockByLocalMeansConst L L'` and
`A_{s,L'} = ENNReal.almostDiagonalConst s L'`, finite for `0 < s < L'`. -/
theorem lqNorm_blockFun_le_lqNorm_maximal {L : ℕ} (hL : 1 ≤ L) {L' : ℕ} (hL' : 1 ≤ L')
    (hp : p ≠ ∞) {q : ℝ≥0∞} (hq : 1 ≤ q) (s : ℝ) (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, lqNorm q (fun j => dyadicWeight s j * ‖blockFun j f x‖ₑ) ≤
      b.blockByLocalMeansConst L L' * ENNReal.almostDiagonalConst s L' *
        lqNorm q (fun i => maximal (fun y => dyadicWeight s i *
          ‖conv (b.kernel L i) f volume y‖ₑ) x) := by
  filter_upwards [b.enorm_blockFun_le_tsum_maximal hL hL' hp f] with x hx
  refine (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq s L' hx).trans_eq ?_
  simp only [dyadicWeight_mul_maximal]

/-- **The local means by blocks in `ℓ_q`**: for every order `L`, `1 ≤ p < ∞`, `1 ≤ q ≤ ∞`,
`s ∈ ℝ` and `f ∈ L_p`, almost everywhere,
`‖(2^(js) |k_j ⋆ f(x)|)_j‖_{ℓ_q} ≤ C A_{s,L} ‖(M(2^(is) |ψ_i ⋆ f|)(x))_i‖_{ℓ_q}` with
`C = Rd.LocalMeansBump.localMeansByBlockConst L` and `A_{s,L} = ENNReal.almostDiagonalConst s L`,
finite for `0 < s < L`. -/
theorem lqNorm_localMean_le_lqNorm_maximal (L : ℕ) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (s : ℝ) (f : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, lqNorm q (fun j => dyadicWeight s j * ‖conv (b.kernel L j) f volume x‖ₑ) ≤
      b.localMeansByBlockConst L * ENNReal.almostDiagonalConst s L *
        lqNorm q (fun i => maximal (fun y => dyadicWeight s i * ‖blockFun i f y‖ₑ) x) := by
  filter_upwards [b.enorm_localMean_le_tsum_maximal L hp f] with x hx
  refine (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq s L hx).trans_eq ?_
  simp only [dyadicWeight_mul_maximal]

/-! ### The characterisation -/

/-- The constant `C A_{s,L'} C_{FS}` of the bound of the Triebel–Lizorkin quasi-norm by local
means, with `L' = ⌈s⌉₊ + 1`, the natural ceiling of `s` plus one, so `L' ≥ 1` and `L' > s`:
`C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`,
`A_{s,L'} = ENNReal.almostDiagonalConst s L'` and the Fefferman–Stein constant
`C_{FS} = Rd.feffermanSteinConst V p q`. -/
noncomputable def tlUpperConst (L : ℕ) (p q : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  b.blockByLocalMeansConst L (⌈s⌉₊ + 1) * ENNReal.almostDiagonalConst s ((⌈s⌉₊ + 1 : ℕ) : ℝ) *
    feffermanSteinConst V p q

/-- The constant of the bound of the Triebel–Lizorkin quasi-norm by local means is finite for
`1 < p < ∞`, `1 < q ≤ ∞` and `s > 0`. -/
theorem tlUpperConst_ne_top (L : ℕ) {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    {s : ℝ} (hs : 0 < s) : b.tlUpperConst L p q s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.blockByLocalMeansConst_ne_top L _)
    (ENNReal.almostDiagonalConst_ne_top hs
      (by push_cast; exact (Nat.le_ceil s).trans_lt (lt_add_one _))))
    (feffermanSteinConst_ne_top hp1 hp hq1)

/-- The constant `C A_{s,L} C_{FS}` of the bound of the local means by the Triebel–Lizorkin
quasi-norm: `C = Rd.LocalMeansBump.localMeansByBlockConst L`,
`A_{s,L} = ENNReal.almostDiagonalConst s L` and `C_{FS} = Rd.feffermanSteinConst V p q`. -/
noncomputable def tlLowerConst (L : ℕ) (p q : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  b.localMeansByBlockConst L * ENNReal.almostDiagonalConst s L * feffermanSteinConst V p q

/-- The constant of the bound of the local means by the Triebel–Lizorkin quasi-norm is finite
for `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L`. -/
theorem tlLowerConst_ne_top {L : ℕ} {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    {s : ℝ} (hs : 0 < s) (hsL : s < L) : b.tlLowerConst L p q s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.localMeansByBlockConst_ne_top L)
    (ENNReal.almostDiagonalConst_ne_top hs hsL)) (feffermanSteinConst_ne_top hp1 hp hq1)

/-- **The Triebel–Lizorkin quasi-norm by local means**: for `L ≥ 1`, `1 < p < ∞`, `1 < q ≤ ∞`,
`s ∈ ℝ` and `f ∈ L_p`, `‖f‖_{F^s_{p,q}} ≤ C ‖f‖_{F^s_{p,q}}^{b,L}` with
`C = Rd.LocalMeansBump.tlUpperConst L p q s`, finite for `s > 0`. Pointwise the blocks are
bounded by maximal functions of the local means in `ℓ_q`, and the Fefferman–Stein inequality
bounds those in `L_p(ℓ_q)`. -/
theorem triebelLizorkinNorm_le_tlLocalMeansNorm {L : ℕ} (hL : 1 ≤ L) (hp1 : 1 < p)
    (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ) (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm s q f ≤ b.tlUpperConst L p q s * b.tlLocalMeansNorm L s q f :=
  eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (aemeasurable_lqNorm_blockFun s q f)
    (fun i => (b.measurable_dyadicWeight_mul_conv_kernel L s i f).aemeasurable)
    (b.lqNorm_blockFun_le_lqNorm_maximal hL (Nat.le_add_left 1 _) hp hq1.le s f)

/-- **The local means by the Triebel–Lizorkin quasi-norm**: for every order `L`, `1 < p < ∞`,
`1 < q ≤ ∞`, `s ∈ ℝ` and `f ∈ L_p`, `‖f‖_{F^s_{p,q}}^{b,L} ≤ C ‖f‖_{F^s_{p,q}}` with
`C = Rd.LocalMeansBump.tlLowerConst L p q s`, finite for `0 < s < L`. -/
theorem tlLocalMeansNorm_le_triebelLizorkinNorm (L : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) (s : ℝ) (f : Lp ℂ p (volume : Measure V)) :
    b.tlLocalMeansNorm L s q f ≤ b.tlLowerConst L p q s * triebelLizorkinNorm s q f :=
  eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (b.aemeasurable_lqNorm_conv_kernel L s q f)
    (fun i => ((aestronglyMeasurable_blockFun i f).eNorm.const_mul _))
    (b.lqNorm_localMean_le_lqNorm_maximal L hp hq1.le s f)

/-- **The local means characterisation of Triebel–Lizorkin spaces**: for a bump `b`, an order
`L`, `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L`, `f ∈ F^s_{p,q}` iff
`‖f‖_{F^s_{p,q}}^{b,L} < ∞`. The order satisfies `L ≥ 1` since `0 < s < L`. -/
theorem memTriebelLizorkin_iff_tlLocalMeans {L : ℕ} (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    {f : Lp ℂ p (volume : Measure V)} :
    MemTriebelLizorkin s q f ↔ b.tlLocalMeansNorm L s q f < ∞ :=
  have hL : 1 ≤ L := Nat.cast_pos.1 (hs.trans hsL)
  ⟨fun h => (b.tlLocalMeansNorm_le_triebelLizorkinNorm L hp1 hp hq1 s f).trans_lt
      (ENNReal.mul_lt_top (b.tlLowerConst_ne_top hp1 hp hq1 hs hsL).lt_top h),
    fun h => (b.triebelLizorkinNorm_le_tlLocalMeansNorm hL hp1 hp hq1 s f).trans_lt
      (ENNReal.mul_lt_top (b.tlUpperConst_ne_top L hp1 hp hq1 hs).lt_top h)⟩

/-- **Change of bump and order**: for two bumps `b, b'`, orders `L ≥ 1` and `L'`,
`1 < p < ∞`, `1 < q ≤ ∞`, `s ∈ ℝ` and `f ∈ L_p`,
`‖f‖_{F^s_{p,q}}^{b',L'} ≤ C' C ‖f‖_{F^s_{p,q}}^{b,L}` with
`C' = Rd.LocalMeansBump.tlLowerConst` of `b', L'` and `C = Rd.LocalMeansBump.tlUpperConst` of
`b, L`, both finite for `0 < s < L'`. -/
theorem tlLocalMeansNorm_le_tlLocalMeansNorm (b' : LocalMeansBump V) {L : ℕ} (hL : 1 ≤ L)
    (L' : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ)
    (f : Lp ℂ p (volume : Measure V)) :
    b'.tlLocalMeansNorm L' s q f ≤
      b'.tlLowerConst L' p q s * b.tlUpperConst L p q s * b.tlLocalMeansNorm L s q f := by
  rw [mul_assoc]
  exact (b'.tlLocalMeansNorm_le_triebelLizorkinNorm L' hp1 hp hq1 s f).trans
    (by gcongr; exact b.triebelLizorkinNorm_le_tlLocalMeansNorm hL hp1 hp hq1 s f)

/-- **The local means quasi-norms are equivalent**: for two bumps `b, b'`, orders `L, L'`,
`1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < min(L, L')`, `‖f‖_{F^s_{p,q}}^{b,L} < ∞` iff
`‖f‖_{F^s_{p,q}}^{b',L'} < ∞`. -/
theorem tlLocalMeansNorm_lt_top_iff (b' : LocalMeansBump V) {L L' : ℕ} (hp1 : 1 < p)
    (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q) {s : ℝ} (hs : 0 < s) (hsL : s < L) (hsL' : s < L')
    {f : Lp ℂ p (volume : Measure V)} :
    b.tlLocalMeansNorm L s q f < ∞ ↔ b'.tlLocalMeansNorm L' s q f < ∞ := by
  rw [← b.memTriebelLizorkin_iff_tlLocalMeans hp1 hp hq1 hs hsL,
    ← b'.memTriebelLizorkin_iff_tlLocalMeans hp1 hp hq1 hs hsL']

/-! ### Synthesis in Triebel–Lizorkin spaces -/

/-- **Synthesis in Triebel–Lizorkin spaces**: if `F = ∑_i η_i ⋆ h_i` in `L_p` (as the limit of
the partial sums) for a family `h_i ∈ L_p`, then for `1 < p < ∞`, `1 < q ≤ ∞` and `s ∈ ℝ`,
`‖F‖_{F^s_{p,q}} ≤ C ‖ x ↦ ‖(2^(is) |h_i(x)|)_i‖_{ℓ_q} ‖_p` with
`C = Rd.LocalMeansBump.tlUpperConst L p q s`, finite for `s > 0`. The blocks of `F` are bounded by
maximal functions of the `h_i` (`Rd.LocalMeansBump.enorm_blockFun_le_tsum_maximal_of_tendsto`),
then the almost diagonal estimate and the Fefferman–Stein inequality finish. -/
theorem triebelLizorkinNorm_le_of_tendsto_sum_dual (L : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ) {F : Lp ℂ p (volume : Measure V)}
    {h : ℕ → Lp ℂ p (volume : Measure V)}
    (hrep : Tendsto (fun J => ∑ i ∈ Finset.range (J + 1),
      convLp hp (b.integrable_dual L i) (h i)) atTop (𝓝 F)) :
    triebelLizorkinNorm s q F ≤ b.tlUpperConst L p q s *
      eLpNorm (fun x => lqNorm q (fun i => dyadicWeight s i * ‖h i x‖ₑ)) p volume := by
  refine eLpNorm_le_of_le_lqNorm_maximal hp1 hp hq1 (aemeasurable_lqNorm_blockFun s q F)
    (fun i => ((Lp.aestronglyMeasurable (h i)).eNorm.const_mul _)) ?_
  filter_upwards [b.enorm_blockFun_le_tsum_maximal_of_tendsto hp L (Nat.le_add_left 1 ⌈s⌉₊) hrep]
    with x hx
  refine (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq1.le s _ hx).trans_eq ?_
  simp only [dyadicWeight_mul_maximal]

end LocalMeansBump

end Rd
