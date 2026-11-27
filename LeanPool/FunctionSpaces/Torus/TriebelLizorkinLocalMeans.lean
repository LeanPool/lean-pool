/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.TriebelLizorkin
public import LeanPool.FunctionSpaces.Torus.FeffermanStein
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Local means for Triebel–Lizorkin spaces on the torus

For a bump `b` on `ℝ^d` and an order `L`, the local means kernels `k_j` of `ℝ^d` act on the torus
by `Torus.econv` and define the quasi-norm

`‖f‖_{F^s_{p,q}(𝕋^d)}^{b,L} = ‖ t ↦ ‖(2^(js) |k_j ⋆ f(t)|)_j‖_{ℓ_q} ‖_{L_p(𝕋^d)}`

(`Torus.tlLocalMeansNorm`). For `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L` it is equivalent to the
Triebel–Lizorkin quasi-norm of the torus, with explicit constants
(`Torus.triebelLizorkinNorm_le_tlLocalMeansNorm`, `Torus.tlLocalMeansNorm_le_triebelLizorkinNorm`),
so `F^s_{p,q}(𝕋^d)` is described by local means (`Torus.memTriebelLizorkin_iff_tlLocalMeans`).

The proof transfers the one on `ℝ^d` (`FunctionSpaces.Rd.TriebelLizorkin.TriebelLizorkinLocalMeans`)
by the periodic lift. The operator identities, the reproducing formula `f = ∑_i η_i ⋆ k_i ⋆ f`
(`Torus.sum_econvLp_dual_kernel`, `Torus.tendsto_sum_econvLp_dual_kernel`) and
`k_j ⋆ Δ_i f = (k_j ⋆ Θ_i) ⋆ Δ_i f`, hold on the torus as identities of Fourier multipliers. At a
lifted point, `(K ⋆ h)(π x) = (K ⋆ (h ∘ π))(x)` is a convolution on `ℝ^d`, to which the pointwise
bounds of the cross kernels apply for every function `h`; this gives, for almost every `x` in the
period box `P_0 = (0, 1]^d`, `|ψ_j ⋆ f(π x)| ≤ C ∑_i c_{ji} M(|k_i ⋆ f| ∘ π)(x)`
(`Torus.enorm_blockFun_proj_le_tsum_maximal`) and
`|k_j ⋆ f(π x)| ≤ C ∑_i c_{ji} M(|ψ_i ⋆ f| ∘ π)(x)`
(`Torus.enorm_econv_kernel_proj_le_tsum_maximal`), with `c_{ji} = 2^(-(j-i)L')` for `i ≤ j`,
`c_{ji} = 1` for `i > j`, and explicit constants `C`. The bounds pass from the partial sums to their
limits in `L_p(𝕋^d)` on `P_0` (`Torus.ae_enorm_comp_proj_le_of_tendsto_Lp`). The almost diagonal
estimate and the Fefferman–Stein inequality for periodic lifts (`Torus.feffermanStein_periodic`)
finish, since `L_p(𝕋^d)` norms are `L_p(P_0)` norms of lifts.
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set Filter Topology Module
open scoped ENNReal TorusHaar

open ENNReal (lqNorm dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (b : Rd.LocalMeansBump (EuclideanSpace ℝ d))

/-! ### The local means quasi-norm -/

/-- The **local means quasi-norm of Triebel–Lizorkin type on the torus**
`‖ t ↦ ‖(2^(js) |k_j ⋆ f(t)|)_j‖_{ℓ_q} ‖_p`, with the local means kernels `k_j` on `ℝ^d` of the
bump `b` and the order `L` acting on the torus: the `ℓ_q` norm at each point, then the `L_p`
norm. -/
noncomputable def tlLocalMeansNorm (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) : ℝ≥0∞ :=
  eLpNorm (fun t => lqNorm q (fun j => dyadicWeight s j * ‖econv (b.kernel L j) f t‖ₑ)) p volume

omit [Fact (1 ≤ p)] in
/-- The weighted local means `2^(js) |k_j ⋆ f|` on the torus are almost everywhere
measurable. -/
theorem aemeasurable_dyadicWeight_mul_econv_kernel (L : ℕ) (s : ℝ) (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    AEMeasurable (fun t => dyadicWeight s j * ‖econv (b.kernel L j) f t‖ₑ) volume :=
  (aestronglyMeasurable_econv (b.integrable_kernel L j).aestronglyMeasurable
    (Lp.stronglyMeasurable f).measurable).eNorm.const_mul _

omit [Fact (1 ≤ p)] in
/-- The pointwise `ℓ_q` norm of the weighted local means on the torus is almost everywhere
measurable. -/
theorem aemeasurable_lqNorm_econv_kernel (L : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    AEMeasurable (fun t => lqNorm q (fun j => dyadicWeight s j *
      ‖econv (b.kernel L j) f t‖ₑ)) volume :=
  aemeasurable_lqNorm_comp (fun j => aemeasurable_dyadicWeight_mul_econv_kernel b L s j f) q

/-! ### Operator identities -/

/-- **The reproducing formula on the torus, partial sums**:
`∑_{j ≤ J} η_j ⋆ k_j ⋆ f = m_{2^J} ⋆ m_{2^J} ⋆ f` on `L_p(𝕋^d)`, from `a² - b² = (a - b)(a + b)`
for the commuting operators `a = m_{2^(J+1)} ⋆`, `b = m_{2^J} ⋆`. -/
theorem sum_econvLp_dual_kernel (hp : p ≠ ∞) (L J : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∑ j ∈ Finset.range (J + 1),
        econvLp hp (b.integrable_dual L j) (econvLp hp (b.integrable_kernel L j) f) =
      econvLp hp (b.integrable_scaled L J) (econvLp hp (b.integrable_scaled L J) f) := by
  induction J with
  | zero =>
    rw [Finset.sum_range_one]
    rfl
  | succ J ih =>
    have hk : econvLp hp (b.integrable_kernel L (J + 1)) f =
        econvLp hp (b.integrable_scaled L (J + 1)) f - econvLp hp (b.integrable_scaled L J) f :=
      econvLp_sub_kernel hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J) f
    have hd : ∀ g : Lp ℂ p (volume : Measure (UnitAddTorus d)),
        econvLp hp (b.integrable_dual L (J + 1)) g =
          econvLp hp (b.integrable_scaled L (J + 1)) g + econvLp hp (b.integrable_scaled L J) g :=
      fun g => econvLp_add_kernel hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J) g
    rw [Finset.sum_range_succ, ih, hd, hk, map_sub, map_sub,
      econvLp_comm hp (b.integrable_scaled L (J + 1)) (b.integrable_scaled L J)]
    abel

/-- **The reproducing formula on the torus**: `∑_j η_j ⋆ k_j ⋆ f = f` in `L_p(𝕋^d)` for `L ≥ 1`,
since `m_{2^J} ⋆ m_{2^J} ⋆ f → f` (`m` is an approximate identity on the torus,
`Torus.tendsto_econvLp_dilate`, and the operators `m_{2^J} ⋆` are uniformly bounded,
`Rd.tendsto_apply_apply_of_tendsto`). -/
theorem tendsto_sum_econvLp_dual_kernel (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Tendsto (fun J => ∑ j ∈ Finset.range (J + 1),
      econvLp hp (b.integrable_dual L j) (econvLp hp (b.integrable_kernel L j) f)) atTop
        (𝓝 f) := by
  simp_rw [sum_econvLp_dual_kernel b hp L]
  have h : Tendsto (fun J => econvLp hp (b.integrable_scaled L J) f) atTop (𝓝 f) :=
    tendsto_econvLp_dilate hp (Rd.integrable_momentKernel b.integrable L)
      (Rd.integral_momentKernel b.integrable b.integral_eq_one hL) (c := fun J : ℕ => (2 : ℝ) ^ J)
      (fun J => by positivity) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) f
  have hm : eLpNorm (Rd.momentKernel b.toFun L) 1 volume ≠ ∞ :=
    (memLp_one_iff_integrable.2 (Rd.integrable_momentKernel b.integrable L)).eLpNorm_ne_top
  refine Rd.tendsto_apply_apply_of_tendsto (T := fun J => econvLp hp (b.integrable_scaled L J))
    (fun J g => norm_econvLp_le hp _ hm (by
      rw [← eLpNorm_one_eq_lintegral_eNorm (b.integrable_scaled L J).1, b.eLpNorm_scaled_one]) g) h

/-- A local mean of a block on the torus is the block convolved with the cross kernel:
`k_j ⋆ Δ_i f = (k_j ⋆ Θ_i) ⋆ Δ_i f` in `L_p(𝕋^d)`, since `Θ_i ⋆ ψ_i = ψ_i`. -/
theorem econvLp_kernel_lpBlock (hp : p ≠ ∞) (L i j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    econvLp hp (b.integrable_kernel L j) (lpBlock hp i f) =
      econvLp hp (Rd.integrable_conv (b.integrable_kernel L j) (Rd.integrable_Theta i))
        (lpBlock hp i f) := by
  have hT : econvLp hp (Rd.integrable_Theta i) (lpBlock hp i f) = lpBlock hp i f :=
    econvLp_comp_econvLp_of_eq hp _ _ (Rd.integrable_psi i) (Rd.conv_Theta_psi i) f
  calc econvLp hp (b.integrable_kernel L j) (lpBlock hp i f)
      = econvLp hp (b.integrable_kernel L j)
          (econvLp hp (Rd.integrable_Theta i) (lpBlock hp i f)) := by rw [hT]
    _ = _ := econvLp_comp_econvLp hp _ _ _

/-! ### Limits on the lift -/

/-- **Pointwise bounds on the lift pass to limits in `L_p(𝕋^d)`**: if `G_J → g` in `L_p(𝕋^d)`
and `|G_J(π x)| ≤ v(x)` for every `J` and almost every `x` in the period box `P_a`, then
`|g(π x)| ≤ v(x)` for almost every `x ∈ P_a`. Composition with `π` is an isometry from
`L_p(𝕋^d)` to `L_p(P_a)` (Mathlib's `Lp.isometry_compMeasurePreserving`), and
`MeasureTheory.ae_enorm_le_of_tendsto_Lp` applies on `P_a`. -/
theorem ae_enorm_comp_proj_le_of_tendsto_Lp {a : d → ℝ}
    {G : ℕ → Lp ℂ p (volume : Measure (UnitAddTorus d))} {g : Lp ℂ p volume}
    (hG : Tendsto G atTop (𝓝 g)) {v : EuclideanSpace ℝ d → ℝ≥0∞}
    (h : ∀ J, ∀ᵐ x ∂(volume.restrict (periodBox a)), ‖G J (proj x)‖ₑ ≤ v x) :
    ∀ᵐ x ∂(volume.restrict (periodBox a)), ‖g (proj x)‖ₑ ≤ v x := by
  have hmp := measurePreserving_proj_periodBox a
  have hlim := ((Lp.isometry_compMeasurePreserving (E := ℂ) (p := p) hmp).continuous.tendsto _).comp
    hG
  have h' := ae_enorm_le_of_tendsto_Lp hlim fun J => by
    filter_upwards [Lp.coeFn_compMeasurePreserving (G J) hmp, h J] with x h1 h2
    simp only [Function.comp_apply] at h1 ⊢
    rw [h1]
    exact h2
  filter_upwards [h', Lp.coeFn_compMeasurePreserving g hmp] with x hx h1
  rw [← Function.comp_apply (f := ⇑g), ← h1]
  exact hx

/-! ### Blocks by local means -/

/-- **A block of a partial sum of the reproducing formula on the torus**: almost everywhere,
`Δ_j (∑_{i ≤ J} η_i ⋆ k_i ⋆ f) = ∑_{i ≤ J} (ψ_j ⋆ η_i) ⋆ (k_i ⋆ f)`, with the representatives of
`k_i ⋆ f ∈ L_p(𝕋^d)` on the right. -/
theorem lpBlock_sum_econvLp_dual_ae (hp : p ≠ ∞) (L J j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ t ∂volume, lpBlock hp j (∑ i ∈ Finset.range (J + 1),
        econvLp hp (b.integrable_dual L i) (econvLp hp (b.integrable_kernel L i) f)) t =
      ∑ i ∈ Finset.range (J + 1), econv (Rd.conv (Rd.psi j) (b.dual L i) volume)
        (econvLp hp (b.integrable_kernel L i) f) t := by
  have hsum : lpBlock hp j (∑ i ∈ Finset.range (J + 1),
      econvLp hp (b.integrable_dual L i) (econvLp hp (b.integrable_kernel L i) f)) =
      ∑ i ∈ Finset.range (J + 1),
        econvLp hp (Rd.integrable_conv (Rd.integrable_psi j) (b.integrable_dual L i))
          (econvLp hp (b.integrable_kernel L i) f) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => econvLp_comp_econvLp hp _ _ _
  rw [hsum]
  exact coeFn_sum_econvLp_ae hp _ _ _

/-- The maximal function of the lift of `k_i ⋆ f ∈ L_p(𝕋^d)` is that of the lift of the pointwise
convolution `k_i ⋆ f`. -/
theorem maximal_econvLp_kernel_proj (hp : p ≠ ∞) (L i : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Rd.maximal (fun y => ‖econvLp hp (b.integrable_kernel L i) f (proj y)‖ₑ) =
      Rd.maximal (fun y => ‖econv (b.kernel L i) f (proj y)‖ₑ) :=
  maximal_enorm_comp_proj_congr_ae (econvLp_apply_ae hp (b.integrable_kernel L i) f)

/-- The bound of the blocks by local means for the partial sums of the reproducing formula, at
lifted points: for `L' ≥ 1` and every `J`, for almost every `x ∈ ℝ^d`,
`|Δ_j (∑_{i ≤ J} η_i ⋆ k_i ⋆ f)(π x)| ≤ C ∑_i c_{ji} M(|k_i ⋆ f| ∘ π)(x)` with
`c_{ji} = 2^(-(j-i)L')` for `i ≤ j`, `c_{ji} = 1` for `i > j`, and
`C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`. -/
theorem ae_enorm_lpBlock_sum_proj_le (hp : p ≠ ∞) (L : ℕ) {L' : ℕ} (hL' : 1 ≤ L') (J j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)), ‖lpBlock hp j (∑ i ∈ Finset.range (J + 1),
        econvLp hp (b.integrable_dual L i) (econvLp hp (b.integrable_kernel L i) f)) (proj x)‖ₑ ≤
      b.blockByLocalMeansConst L L' * ∑' i, (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i)
        else 1) * Rd.maximal (fun y => ‖econv (b.kernel L i) f (proj y)‖ₑ) x := by
  filter_upwards [ae_comp_proj (lpBlock_sum_econvLp_dual_ae b hp L J j f)] with x hx
  have hterm : ∀ i, ‖econv (Rd.conv (Rd.psi j) (b.dual L i) volume)
      (econvLp hp (b.integrable_kernel L i) f) (proj x)‖ₑ ≤
        b.blockByLocalMeansConst L L' * ((if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i)
          else 1) * Rd.maximal (fun y => ‖econv (b.kernel L i) f (proj y)‖ₑ) x) := fun i => by
    rw [econv_proj, ← maximal_econvLp_kernel_proj b hp L i f]
    exact b.enorm_conv_conv_psi_dual_le L hL' i j _ x
  rw [hx]
  refine (eNorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans ?_)
  rw [← Finset.mul_sum]
  gcongr
  exact sum_le_tsum _

/-- **The blocks by local means on the torus, pointwise on the lift**: for `L ≥ 1`, `L' ≥ 1`,
`1 ≤ p < ∞` and `f ∈ L_p(𝕋^d)`, for almost every `x` in the period box `P_0 = (0, 1]^d` and all
levels `j`, `|ψ_j ⋆ f(π x)| ≤ C ∑_i c_{ji} M(|k_i ⋆ f| ∘ π)(x)` with `c_{ji} = 2^(-(j-i)L')` for
`i ≤ j`, `c_{ji} = 1` for `i > j`, and `C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`. The
reproducing formula holds in `L_p(𝕋^d)`, and the bound passes from the partial sums to `f`
(`Torus.ae_enorm_comp_proj_le_of_tendsto_Lp`). -/
theorem enorm_blockFun_proj_le_tsum_maximal {L : ℕ} (hL : 1 ≤ L) {L' : ℕ} (hL' : 1 ≤ L')
    (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ x ∂(volume.restrict (periodBox 0)), ∀ j, ‖blockFun j f (proj x)‖ₑ ≤
      b.blockByLocalMeansConst L L' * ∑' i, (if i ≤ j then dyadicWeight (-(L' : ℝ)) (j - i)
        else 1) * Rd.maximal (fun y => ‖econv (b.kernel L i) f (proj y)‖ₑ) x := by
  refine ae_all_iff.2 fun j => ?_
  have h := ae_enorm_comp_proj_le_of_tendsto_Lp (a := 0)
    (((lpBlock hp j).continuous.tendsto f).comp (tendsto_sum_econvLp_dual_kernel b hp hL f))
    fun J => ae_restrict_of_ae (ae_enorm_lpBlock_sum_proj_le b hp L hL' J j f)
  filter_upwards [h, ae_restrict_of_ae (ae_comp_proj (lpBlock_ae_eq_blockFun hp j f))]
    with x hx h2
  rw [← h2]
  exact hx

/-! ### Local means by blocks -/

/-- **A local mean of a partial sum of blocks on the torus**: almost everywhere,
`k_j ⋆ (∑_{i < J} Δ_i f) = ∑_{i < J} (k_j ⋆ Θ_i) ⋆ Δ_i f`, with the representatives of
`Δ_i f ∈ L_p(𝕋^d)` on the right. -/
theorem econvLp_kernel_sum_lpBlock_ae (hp : p ≠ ∞) (L J j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ t ∂volume, econvLp hp (b.integrable_kernel L j) (∑ i ∈ Finset.range J, lpBlock hp i f) t =
      ∑ i ∈ Finset.range J, econv (Rd.conv (b.kernel L j) (Rd.Theta i) volume)
        (lpBlock hp i f) t := by
  simp only [map_sum, econvLp_kernel_lpBlock b hp L _ j f]
  exact coeFn_sum_econvLp_ae hp _ _ _

/-- The maximal function of the lift of `Δ_i f ∈ L_p(𝕋^d)` is that of the lift of the pointwise
block `ψ_i ⋆ f`. -/
theorem maximal_lpBlock_proj (hp : p ≠ ∞) (i : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    Rd.maximal (fun y => ‖lpBlock hp i f (proj y)‖ₑ) =
      Rd.maximal (fun y => ‖blockFun i f (proj y)‖ₑ) :=
  maximal_enorm_comp_proj_congr_ae (lpBlock_ae_eq_blockFun hp i f)

/-- The bound of the local means by blocks for the partial sums of the block decomposition, at
lifted points: for every `J`, for almost every `x ∈ ℝ^d`,
`|k_j ⋆ (∑_{i < J} Δ_i f)(π x)| ≤ C ∑_i c_{ji} M(|ψ_i ⋆ f| ∘ π)(x)` with `c_{ji} = 2^(-(j-i)L)` for
`i ≤ j`, `c_{ji} = 1` for `i > j`, and `C = Rd.LocalMeansBump.localMeansByBlockConst L`. -/
theorem ae_enorm_econvLp_kernel_sum_proj_le (hp : p ≠ ∞) (L J j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ d)),
      ‖econvLp hp (b.integrable_kernel L j) (∑ i ∈ Finset.range J, lpBlock hp i f) (proj x)‖ₑ ≤
        b.localMeansByBlockConst L * ∑' i, (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i)
          else 1) * Rd.maximal (fun y => ‖blockFun i f (proj y)‖ₑ) x := by
  filter_upwards [ae_comp_proj (econvLp_kernel_sum_lpBlock_ae b hp L J j f)] with x hx
  have hterm : ∀ i, ‖econv (Rd.conv (b.kernel L j) (Rd.Theta i) volume)
      (lpBlock hp i f) (proj x)‖ₑ ≤
        b.localMeansByBlockConst L * ((if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i)
          else 1) * Rd.maximal (fun y => ‖blockFun i f (proj y)‖ₑ) x) := fun i => by
    rw [econv_proj, ← maximal_lpBlock_proj hp i f]
    exact b.enorm_conv_conv_kernel_Theta_le L i j _ x
  rw [hx]
  refine (eNorm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans ?_)
  rw [← Finset.mul_sum]
  gcongr
  exact sum_le_tsum _

/-- **The local means by blocks on the torus, pointwise on the lift**: for every order `L`,
`1 ≤ p < ∞` and `f ∈ L_p(𝕋^d)`, for almost every `x` in the period box `P_0 = (0, 1]^d` and all
levels `j`, `|k_j ⋆ f(π x)| ≤ C ∑_i c_{ji} M(|ψ_i ⋆ f| ∘ π)(x)` with `c_{ji} = 2^(-(j-i)L)` for
`i ≤ j`, `c_{ji} = 1` for `i > j`, and `C = Rd.LocalMeansBump.localMeansByBlockConst L`. The
decomposition `f = ∑_i Δ_i f` holds in `L_p(𝕋^d)`, and the bound passes from its partial sums to
`f` (`Torus.ae_enorm_comp_proj_le_of_tendsto_Lp`). -/
theorem enorm_econv_kernel_proj_le_tsum_maximal (L : ℕ) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ x ∂(volume.restrict (periodBox 0)), ∀ j, ‖econv (b.kernel L j) f (proj x)‖ₑ ≤
      b.localMeansByBlockConst L * ∑' i, (if i ≤ j then dyadicWeight (-(L : ℝ)) (j - i)
        else 1) * Rd.maximal (fun y => ‖blockFun i f (proj y)‖ₑ) x := by
  refine ae_all_iff.2 fun j => ?_
  have h := ae_enorm_comp_proj_le_of_tendsto_Lp (a := 0)
    (((econvLp hp (b.integrable_kernel L j)).continuous.tendsto f).comp (tendsto_sum_lpBlock hp f))
    fun J => ae_restrict_of_ae (ae_enorm_econvLp_kernel_sum_proj_le b hp L J j f)
  filter_upwards [h,
    ae_restrict_of_ae (ae_comp_proj (econvLp_apply_ae hp (b.integrable_kernel L j) f))]
    with x hx h2
  rw [← h2]
  exact hx

/-! ### The almost diagonal step -/

/-- **The blocks by local means in `ℓ_q` on the torus**: for `L ≥ 1`, `L' ≥ 1`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `s ∈ ℝ` and `f ∈ L_p(𝕋^d)`, for almost every `x ∈ P_0`,
`‖(2^(js) |ψ_j ⋆ f(π x)|)_j‖_{ℓ_q} ≤ C A_{s,L'} ‖(M(2^(is) |k_i ⋆ f| ∘ π)(x))_i‖_{ℓ_q}` with
`C = Rd.LocalMeansBump.blockByLocalMeansConst L L'` and
`A_{s,L'} = ENNReal.almostDiagonalConst s L'`. -/
theorem lqNorm_blockFun_proj_le_lqNorm_maximal {L : ℕ} (hL : 1 ≤ L) {L' : ℕ} (hL' : 1 ≤ L')
    (hp : p ≠ ∞) {q : ℝ≥0∞} (hq : 1 ≤ q) (s : ℝ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ x ∂(volume.restrict (periodBox 0)),
      lqNorm q (fun j => dyadicWeight s j * ‖blockFun j f (proj x)‖ₑ) ≤
        b.blockByLocalMeansConst L L' * ENNReal.almostDiagonalConst s L' *
          lqNorm q (fun i => Rd.maximal (fun y => dyadicWeight s i *
            ‖econv (b.kernel L i) f (proj y)‖ₑ) x) := by
  filter_upwards [enorm_blockFun_proj_le_tsum_maximal b hL hL' hp f] with x hx
  refine (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq s L' hx).trans_eq ?_
  simp only [Rd.dyadicWeight_mul_maximal]

/-- **The local means by blocks in `ℓ_q` on the torus**: for every order `L`, `1 ≤ p < ∞`,
`1 ≤ q ≤ ∞`, `s ∈ ℝ` and `f ∈ L_p(𝕋^d)`, for almost every `x ∈ P_0`,
`‖(2^(js) |k_j ⋆ f(π x)|)_j‖_{ℓ_q} ≤ C A_{s,L} ‖(M(2^(is) |ψ_i ⋆ f| ∘ π)(x))_i‖_{ℓ_q}` with
`C = Rd.LocalMeansBump.localMeansByBlockConst L` and `A_{s,L} = ENNReal.almostDiagonalConst s L`. -/
theorem lqNorm_econv_kernel_proj_le_lqNorm_maximal (L : ℕ) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (s : ℝ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ∀ᵐ x ∂(volume.restrict (periodBox 0)),
      lqNorm q (fun j => dyadicWeight s j * ‖econv (b.kernel L j) f (proj x)‖ₑ) ≤
        b.localMeansByBlockConst L * ENNReal.almostDiagonalConst s L *
          lqNorm q (fun i => Rd.maximal (fun y => dyadicWeight s i *
            ‖blockFun i f (proj y)‖ₑ) x) := by
  filter_upwards [enorm_econv_kernel_proj_le_tsum_maximal b L hp f] with x hx
  refine (ENNReal.lqNorm_le_almostDiagonalConst_mul_of_le hq s L hx).trans_eq ?_
  simp only [Rd.dyadicWeight_mul_maximal]

omit [Fact (1 ≤ p)] in
/-- **From pointwise maximal bounds on the lift to `L_p(ℓ_q)` on the torus**: for `1 < p < ∞`
and `1 < q ≤ ∞`, if `F(π x) ≤ C ‖(M(g_i ∘ π)(x))_i‖_{ℓ_q}` for almost every `x ∈ P_0`, with
almost everywhere measurable `F` and `g_i` on `𝕋^d`, then
`‖F‖_p ≤ C C_P ‖ t ↦ ‖(g_i(t))_i‖_{ℓ_q} ‖_p` with `C_P = Torus.periodicFSConst d p q`. -/
theorem eLpNorm_le_of_le_lqNorm_maximal_proj (hp1 : 1 < p) (hp : p ≠ ∞) {q : ℝ≥0∞}
    (hq1 : 1 < q) {F : UnitAddTorus d → ℝ≥0∞} (hF : AEMeasurable F volume)
    {g : ℕ → UnitAddTorus d → ℝ≥0∞} (hg : ∀ i, AEMeasurable (g i) volume) {C : ℝ≥0∞}
    (h : ∀ᵐ x ∂(volume.restrict (periodBox 0)),
      F (proj x) ≤ C * lqNorm q (fun i => Rd.maximal (fun y => g i (proj y)) x)) :
    eLpNorm F p volume ≤
      C * periodicFSConst d p q * eLpNorm (fun t => lqNorm q (fun i => g i t)) p volume := by
  have hmp := measurePreserving_proj_periodBox (d := d) 0
  calc eLpNorm F p volume = eLpNorm (F ∘ proj) p (volume.restrict (periodBox 0)) :=
        (eLpNorm_comp_proj_periodBox 0 hF.aestronglyMeasurable p).symm
    _ ≤ eLpNorm (fun x => C * lqNorm q (fun i => Rd.maximal (fun y => g i (proj y)) x)) p
          (volume.restrict (periodBox 0)) :=
        eLpNorm_mono_eNorm_ae
          (hF.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving).aestronglyMeasurable
          (h.mono fun x hx => by simpa only [eNorm_eq_self, Function.comp_apply] using hx)
    _ = C * eLpNorm (fun x => lqNorm q (fun i => Rd.maximal (fun y => g i (proj y)) x)) p
          (volume.restrict (periodBox 0)) :=
        eLpNorm_const_mul_ennreal (c := C)
          (measurable_lqNorm_comp (fun i => Rd.measurable_maximal _) q).aestronglyMeasurable
    _ ≤ C * (periodicFSConst d p q * eLpNorm (fun t => lqNorm q (fun i => g i t)) p volume) := by
        gcongr
        exact feffermanStein_periodic hp1 hp hq1 g hg
    _ = _ := by rw [mul_assoc]

/-! ### The characterisation -/

/-- The constant `C A_{s,L'} C_P` of the bound of the Triebel–Lizorkin quasi-norm on the torus by
local means, with `L' = ⌈s⌉₊ + 1`: `C = Rd.LocalMeansBump.blockByLocalMeansConst L L'`,
`A_{s,L'} = ENNReal.almostDiagonalConst s L'` and `C_P = Torus.periodicFSConst d p q`. -/
noncomputable def tlUpperConst (L : ℕ) (p q : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  b.blockByLocalMeansConst L (⌈s⌉₊ + 1) * ENNReal.almostDiagonalConst s ((⌈s⌉₊ + 1 : ℕ) : ℝ) *
    periodicFSConst d p q

/-- The constant of the bound of the Triebel–Lizorkin quasi-norm on the torus by local means is
finite for `1 < p < ∞`, `1 < q ≤ ∞` and `s > 0`. -/
theorem tlUpperConst_ne_top (L : ℕ) {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    {s : ℝ} (hs : 0 < s) : tlUpperConst b L p q s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.blockByLocalMeansConst_ne_top L _)
    (ENNReal.almostDiagonalConst_ne_top hs
      (by push_cast; exact (Nat.le_ceil s).trans_lt (lt_add_one _))))
    (periodicFSConst_ne_top hp1 hp hq1)

/-- The constant `C A_{s,L} C_P` of the bound of the local means on the torus by the
Triebel–Lizorkin quasi-norm: `C = Rd.LocalMeansBump.localMeansByBlockConst L`,
`A_{s,L} = ENNReal.almostDiagonalConst s L` and `C_P = Torus.periodicFSConst d p q`. -/
noncomputable def tlLowerConst (L : ℕ) (p q : ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  b.localMeansByBlockConst L * ENNReal.almostDiagonalConst s L * periodicFSConst d p q

/-- The constant of the bound of the local means on the torus by the Triebel–Lizorkin quasi-norm
is finite for `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L`. -/
theorem tlLowerConst_ne_top {L : ℕ} {p q : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) (hq1 : 1 < q)
    {s : ℝ} (hs : 0 < s) (hsL : s < L) : tlLowerConst b L p q s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (b.localMeansByBlockConst_ne_top L)
    (ENNReal.almostDiagonalConst_ne_top hs hsL)) (periodicFSConst_ne_top hp1 hp hq1)

/-- **The Triebel–Lizorkin quasi-norm on the torus by local means**: for `L ≥ 1`, `1 < p < ∞`,
`1 < q ≤ ∞`, `s ∈ ℝ` and `f ∈ L_p(𝕋^d)`, `‖f‖_{F^s_{p,q}} ≤ C ‖f‖_{F^s_{p,q}}^{b,L}` with
`C = Torus.tlUpperConst b L p q s`, finite for `s > 0`. -/
theorem triebelLizorkinNorm_le_tlLocalMeansNorm {L : ℕ} (hL : 1 ≤ L) (hp1 : 1 < p)
    (hp : p ≠ ∞) {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    triebelLizorkinNorm s q f ≤ tlUpperConst b L p q s * tlLocalMeansNorm b L s q f :=
  eLpNorm_le_of_le_lqNorm_maximal_proj hp1 hp hq1 (aemeasurable_lqNorm_blockFun s q f)
    (fun i => aemeasurable_dyadicWeight_mul_econv_kernel b L s i f)
    (lqNorm_blockFun_proj_le_lqNorm_maximal b hL (Nat.le_add_left 1 _) hp hq1.le s f)

/-- **The local means on the torus by the Triebel–Lizorkin quasi-norm**: for every order `L`,
`1 < p < ∞`, `1 < q ≤ ∞`, `s ∈ ℝ` and `f ∈ L_p(𝕋^d)`,
`‖f‖_{F^s_{p,q}}^{b,L} ≤ C ‖f‖_{F^s_{p,q}}` with `C = Torus.tlLowerConst b L p q s`, finite for
`0 < s < L`. -/
theorem tlLocalMeansNorm_le_triebelLizorkinNorm (L : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) (s : ℝ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    tlLocalMeansNorm b L s q f ≤ tlLowerConst b L p q s * triebelLizorkinNorm s q f :=
  eLpNorm_le_of_le_lqNorm_maximal_proj hp1 hp hq1 (aemeasurable_lqNorm_econv_kernel b L s q f)
    (fun i => (aestronglyMeasurable_blockFun i f).eNorm.const_mul _)
    (lqNorm_econv_kernel_proj_le_lqNorm_maximal b L hp hq1.le s f)

/-- **The local means characterisation of Triebel–Lizorkin spaces on the torus**: for a bump
`b` on `ℝ^d`, an order `L`, `1 < p < ∞`, `1 < q ≤ ∞` and `0 < s < L`, `f ∈ F^s_{p,q}(𝕋^d)`
iff `‖f‖_{F^s_{p,q}}^{b,L} < ∞`. The order satisfies `L ≥ 1` since `0 < s < L`. -/
theorem memTriebelLizorkin_iff_tlLocalMeans {L : ℕ} (hp1 : 1 < p) (hp : p ≠ ∞)
    {q : ℝ≥0∞} (hq1 : 1 < q) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} :
    MemTriebelLizorkin s q f ↔ tlLocalMeansNorm b L s q f < ∞ :=
  have hL : 1 ≤ L := Nat.cast_pos.1 (hs.trans hsL)
  ⟨fun h => (tlLocalMeansNorm_le_triebelLizorkinNorm b L hp1 hp hq1 s f).trans_lt
      (ENNReal.mul_lt_top (tlLowerConst_ne_top b hp1 hp hq1 hs hsL).lt_top h),
    fun h => (triebelLizorkinNorm_le_tlLocalMeansNorm b hL hp1 hp hq1 s f).trans_lt
      (ENNReal.mul_lt_top (tlUpperConst_ne_top b L hp1 hp hq1 hs).lt_top h)⟩

end Torus
