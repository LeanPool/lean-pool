/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.DerivativeKernels
public import LeanPool.FunctionSpaces.Rd.TriebelLizorkin.SquareFunction

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev spaces `W^m_p = F^m_{p,2}`

Let `V` have dimension `n ≥ 1`, `1 < p < ∞` and `m ∈ ℕ`. A function `f ∈ L_p(V)` lies in the
Sobolev space `W^m_p(V)` (`Rd.MemSobolev`: all weak derivatives `∂^w f` of order `k ≤ m` exist
and lie in `L_p(V)`) iff it lies in the Triebel–Lizorkin space `F^m_{p,2}(V)`
(`Rd.MemTriebelLizorkin`: `‖ x ↦ ‖(2^{jm} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p < ∞`), see
`Rd.memSobolev_iff_memTriebelLizorkin`. Both directions have named constants
(`Rd.sobolevToTLConst`, `Rd.tlToSobolevConst`), formulas in the Schwartz seminorms of fixed
kernels that are proved finite.

* **`W^m_p ⊆ F^m_{p,2}`** (`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`,
  `Rd.memTriebelLizorkin_of_hasWeakLineDeriv`): with the weak
  derivatives `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal basis `e` of
  `Rd.gridBasis`, `‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p`
  (`Rd.sobolevToTLConst`). Young's inequality bounds `ψ_0 ⋆ f`; the dilated derivative kernels
  give `2^{jm} ψ_{j+1} ⋆ f = ∑_α (η_α)_{2^j} ⋆ g_α` (`Rd.two_pow_mul_blockFun_succ_ae`), and the
  analysis bound of the Calderón–Zygmund families `((η_α)_{2^j})_j` bounds each sum.
* **`F^m_{p,2} ⊆ W^m_p`** (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin`): for
  `f ∈ F^k_{p,2}(V)` and directions `w ∈ V^k`, the partial sums
  `∑_{j < J} (∂^w ψTilde_j) ⋆ (ψ_j ⋆ f)` (`Rd.derivSynthesisSum`) are a Cauchy sequence in `L_p`, by
  the synthesis bound of the Calderón–Zygmund family `((∂^w GTilde_j)_{2^j})_j` and the tails of the
  coefficients `2^{jk} ψ_j ⋆ f` in `L_p(ℓ_2)`. They are the weak derivatives `∂^w` of the
  reproducing sums `∑_{j < J} ψTilde_j ⋆ (ψ_j ⋆ f) → f`, so their limit `g` is the weak derivative
  `∂^w f`, with `‖g‖_p ≤ C_w ‖f‖_{F^k_{p,2}}` (`Rd.tlToSobolevConst`). For `k ≤ m`,
  `F^m_{p,2} ⊆ F^k_{p,2}`.
* **Synthesis sums**: for Schwartz kernels `K_j` with the synthesis bound
  `‖∑_{j ∈ t} K_j ⋆ (ψ_j ⋆ f)‖_p ≤ C ‖ x ↦ ‖(1_t(j) 2^{jσ} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p`, the
  partial sums converge in `L_p` for `f ∈ F^σ_{p,2}` (`Rd.cauchySeq_toLp_sum_conv_blockFun`,
  `Rd.exists_tendsto_sum_conv_blockFun`); a Calderón–Zygmund family with the coefficients
  `|c_j| = 2^{jσ}` has this bound (`Rd.IsCZFamily.eLpNorm_sum_conv_smul_le` for every family
  in `L_p`, `Rd.IsCZFamily.eLpNorm_sum_conv_smul_blockFun_le` for the blocks). The
  Bessel potentials of `FunctionSpaces.Rd.BesselPotentials.BesselPotentialLifting` use the same
  sums.

With the Besov sandwich of the Triebel–Lizorkin spaces, `B^m_{p,min(p,2)} ⊆ W^m_p` and, for
`m ≥ 1`, `W^m_p ⊆ B^m_{p,max(p,2)}` (`Rd.memSobolev_of_memApprox`, `Rd.memApprox_of_memSobolev`,
with norm bounds in `Rd.exists_hasWeakLineDeriv_of_memApprox` and
`Rd.approxNormDyadic_le_of_hasWeakLineDeriv`), and `W^m_2 = B^m_{2,2}` for `m ≥ 1`
(`Rd.memSobolev_two_iff_memApprox`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal Topology SchwartzMap LineDeriv
open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### `W^m_p ⊆ F^m_{p,2}` -/

variable (V) in
/-- The constant `K_α = S_{V,p}(2, 4 H_{A^α})` of the bound `W^m_p ⊆ F^m_{p,2}` for the
multi-index `α`: the strong type constant `Rd.czConst` of the Calderón–Zygmund family of the
dilated derivative kernels `(η_α)_{2^j}`, with overlap `2` and Hörmander constant `4 H_{A^α}`
(`Rd.isCZFamily_derivFamily`). -/
noncomputable def sobolevToTLConst (p : ℝ≥0∞) {m : ℕ} (i : Fin m → Fin (finrank ℝ V)) : ℝ≥0∞ :=
  czConst V p 2 (4 * familyHormanderConst V (derivKernelBound i))

/-- The constant `Rd.sobolevToTLConst V p α` is finite for `1 < p < ∞`. -/
theorem sobolevToTLConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ V)) : sobolevToTLConst V p i ≠ ∞ :=
  czConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

/-- **The blocks of `f` as convolutions with its derivatives**: for `1 ≤ p < ∞`, if
`g_α ∈ L_p(V)` is the weak derivative `∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` for every multi-index
`α`, then for almost every `x` and every `j`,
`2^{jm} (ψ_{j+1} ⋆ f)(x) = ∑_α ((η_α)_{2^j} ⋆ g_α)(x)`.
This is the dilated identity `2^{jm} ψ_{j+1} = ∑_α ∂^α ((η_α)_{2^j})`
(`Rd.two_pow_smul_psi_succ_eq_sum`) with each derivative moved from the kernel to `f`
(`Rd.conv_eq_conv_iteratedLineDerivOp`). -/
theorem two_pow_mul_blockFun_succ_ae (hp : p ≠ ∞) {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∀ᵐ x ∂volume, ∀ j, (2 : ℂ) ^ (j * m) * blockFun (j + 1) f x =
      ∑ i, conv (derivFamily i j) (g i) volume x := by
  refine ae_all_iff.2 fun j => ?_
  set K : (Fin m → Fin (finrank ℝ V)) → 𝓢(V, ℂ) := fun i =>
    ∂^{fun k => gridBasis V (i k)} (schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero)
      (derivKernel i)) with hKdef
  have hsum : (fun y => ∑ i, (1 : ℂ) * K i y) = (2 : ℂ) ^ (j * m) • psi (V := V) (j + 1) := by
    rw [two_pow_smul_psi_succ_eq_sum]
    funext y
    simp [K, Finset.sum_apply]
  have h := conv_finsetSum_kernel_ae Fact.out hp Finset.univ (fun _ => (1 : ℂ))
    (K := fun i => ⇑(K i)) (fun i _ => (K i).integrable) (Lp.memLp f)
  rw [hsum, smul_conv] at h
  filter_upwards [h] with x hx
  simp only [Pi.smul_apply, smul_eq_mul, one_mul] at hx
  rw [blockFun, hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hKdef, ← conv_eq_conv_iteratedLineDerivOp (hg i), coe_schwartzDilate]
  rfl

/-- **The pointwise bound of the higher blocks**: for `1 ≤ p < ∞`, under the hypotheses of
`Rd.two_pow_mul_blockFun_succ_ae`, for almost every `x`,
`‖(2^{(j+1)m} (ψ_{j+1} ⋆ f)(x))_j‖_{ℓ_2} ≤ 2^m ∑_α ‖(((η_α)_{2^j} ⋆ g_α)(x))_j‖_{ℓ_2}`, by
Minkowski's inequality in `ℓ_2` (`ENNReal.lqNorm_dyadicWeight_succ_le_sum`). -/
theorem lqNorm_blockFun_succ_le_sum_ae (hp : p ≠ ∞) {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∀ᵐ x ∂volume,
      lqNorm 2 (fun n => dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f x‖ₑ) ≤
        2 ^ m * ∑ i, lqNorm 2 (fun n => ‖conv (derivFamily i n) (g i) volume x‖ₑ) := by
  filter_upwards [two_pow_mul_blockFun_succ_ae hp hg] with x hx
  refine ENNReal.lqNorm_dyadicWeight_succ_le_sum one_le_two Finset.univ fun n => ?_
  rw [← enorm_two_pow_complex, ← eNorm_mul, hx n]
  exact eNorm_sum_le _ _

/-- **The higher blocks in `L_p(ℓ_2)`**: in dimension `n ≥ 1`, for `1 < p < ∞`, under the
hypotheses of `Rd.two_pow_mul_blockFun_succ_ae`,
`‖ x ↦ ‖(2^{(j+1)m} (ψ_{j+1} ⋆ f)(x))_j‖_{ℓ_2} ‖_p ≤ 2^m ∑_α K_α ‖g_α‖_p` with
`K_α = Rd.sobolevToTLConst V p α`: the pointwise bound `Rd.lqNorm_blockFun_succ_le_sum_ae`,
Minkowski's inequality in `L_p` (`MeasureTheory.eLpNorm_le_const_mul_sum_of_ae_le`), and the
analysis bound of the families `((η_α)_{2^j})_j` (`Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`). -/
theorem eLpNorm_lqNorm_blockFun_succ_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    eLpNorm (fun x => lqNorm 2 (fun n =>
        dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f x‖ₑ)) p volume ≤
      2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ := by
  have hF : ∀ i, AEMeasurable
      (fun x => lqNorm 2 (fun n => ‖conv (derivFamily i n) (g i) volume x‖ₑ)) volume :=
    fun i => aemeasurable_lqNorm_comp (fun n => (aestronglyMeasurable_conv
      ((isCZFamily_derivFamily i).integrable n).aestronglyMeasurable
      (Lp.aestronglyMeasurable (g i))).eNorm) 2
  refine (eLpNorm_le_const_mul_sum_of_ae_le (p := p) Fact.out Finset.univ
    (aemeasurable_lqNorm_comp (fun n =>
      (aestronglyMeasurable_blockFun (n + 1) f).eNorm.const_mul _) 2)
    (fun i _ => hF i) _ (lqNorm_blockFun_succ_le_sum_ae hp hg)).trans ?_
  gcongr with i
  rw [Lp.eNorm_def]
  exact (isCZFamily_derivFamily i).eLpNorm_lqNorm_conv_le hp1 hp (Lp.memLp (g i))

/-- **`W^m_p ⊆ F^m_{p,2}` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞` and
`f ∈ L_p(V)` whose weak derivatives `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal
basis `e` of `Rd.gridBasis` lie in `L_p(V)` for every multi-index `α`,
`‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p` with `K_α = Rd.sobolevToTLConst V p α`.
The block `j = 0` is split off from the `ℓ_2` norm
(`MeasureTheory.eLpNorm_lqNorm_dyadicWeight_le_zero_add_succ`) and bounded by Young's inequality
(`Rd.eLpNorm_blockFun_zero_le`); the other blocks by `Rd.eLpNorm_lqNorm_blockFun_succ_le`. -/
theorem triebelLizorkinNorm_le_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    triebelLizorkinNorm (m : ℝ) 2 f ≤
      eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ := by
  refine (eLpNorm_lqNorm_dyadicWeight_le_zero_add_succ (p := p) Fact.out one_le_two _
    fun j => (aestronglyMeasurable_blockFun j f).eNorm).trans ?_
  gcongr
  · rw [eLpNorm_eNorm _ (aestronglyMeasurable_blockFun 0 f)]
    exact eLpNorm_blockFun_zero_le f
  · exact eLpNorm_lqNorm_blockFun_succ_le hp1 hp hg

/-- **The weak derivatives of order `m` along the basis vectors give `f ∈ F^m_{p,2}`**: in
dimension `n ≥ 1`, for `1 < p < ∞`, if the weak derivatives `g_α = ∂^α f` of order `m` along the
basis `e` of `Rd.gridBasis` lie in `L_p(V)` for every multi-index `α`, then `f ∈ F^m_{p,2}(V)`,
since the bound `Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv` is finite. -/
theorem memTriebelLizorkin_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    MemTriebelLizorkin (m : ℝ) 2 f :=
  (triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg).trans_lt
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
      eLpNorm_lpKernel_lt_top eNorm_lt_top,
      ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) (ENNReal.sum_lt_top.2 fun i _ =>
        ENNReal.mul_lt_top (sobolevToTLConst_ne_top hp1 hp i).lt_top eNorm_lt_top)⟩)

/-- **`W^m_p ⊆ F^m_{p,2}`**: in dimension `n ≥ 1`, for `1 < p < ∞`, every `f ∈ W^m_p(V)` lies in
`F^m_{p,2}(V)`; the weak derivatives of order `m` along the basis vectors suffice
(`Rd.memTriebelLizorkin_of_hasWeakLineDeriv`). -/
theorem memTriebelLizorkin_of_memSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev m f) : MemTriebelLizorkin (m : ℝ) 2 f := by
  have hd : ∀ i : Fin m → Fin (finrank ℝ V), ∃ g : Lp ℂ p (volume : Measure V),
      HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f g := fun i =>
    (memSobolev_iff_exists_hasWeakLineDeriv f).1 hf m le_rfl _
  choose g hg using hd
  exact memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg

/-! ### `F^m_{p,2} ⊆ W^m_p` -/

/-- The constant `C_w = S_{V,p}(4 ((8π)^k ∏_l ‖w_l‖)², 4 H_{Ã^w})` of the bound
`F^k_{p,2} ⊆ W^k_p` for the directions `w ∈ V^k`: the strong type constant `Rd.czConst` of the
Calderón–Zygmund family `((∂^w GTilde_j)_{2^j})_j` of the rescaled derivatives of the synthesis
kernels (`Rd.isCZFamily_derivDualFamily`). -/
noncomputable def tlToSobolevConst (p : ℝ≥0∞) {k : ℕ} (w : Fin k → V) : ℝ≥0∞ :=
  czConst V p (derivDualOverlap w) (4 * familyHormanderConst V (derivDualBound w))

/-- The constant `Rd.tlToSobolevConst p w` is finite for `1 < p < ∞`. -/
theorem tlToSobolevConst_ne_top {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V) :
    tlToSobolevConst p w ≠ ∞ :=
  czConst_ne_top hp1 hp (derivDualOverlap_ne_top w)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

omit [Fact (1 ≤ p)] in
/-- **The synthesis bound with scaled coefficients**: in dimension `n ≥ 1`, for `1 < p < ∞`, a
Calderón–Zygmund family `(θ_j)_j` with overlap `B` and Hörmander constant `H`, coefficients
`c_j ∈ ℂ` with `|c_j| = 2^{jσ}`, every finite set `t ⊆ ℕ` and functions `g_j ∈ L_p(V)`,
`‖∑_{j ∈ t} θ_j ⋆ (c_j g_j)‖_p ≤ S ‖ x ↦ ‖(1_t(j) 2^{jσ} |g_j(x)|)_j‖_{ℓ_2} ‖_p` with
`S = Rd.czConst V p B H`: the synthesis bound of the family
(`Rd.IsCZFamily.eLpNorm_sum_conv_le`) for the functions `1_t(j) c_j g_j`. -/
theorem IsCZFamily.eLpNorm_sum_conv_smul_le [Nontrivial V] {θ : ℕ → V → ℂ} {B H : ℝ≥0∞}
    (hθ : IsCZFamily θ B H) (hp1 : 1 < p) (hp : p ≠ ∞) {σ : ℝ} {c : ℕ → ℂ}
    (hc : ∀ j, ‖c j‖ₑ = dyadicWeight σ j) (t : Finset ℕ) {g : ℕ → V → ℂ}
    (hg : ∀ j, MemLp (g j) p volume) :
    eLpNorm (fun x => ∑ j ∈ t, conv (θ j) (c j • g j) volume x) p volume ≤
      czConst V p B H * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖g j x‖ₑ else 0) p volume := by
  set a : ℕ → V → ℂ := fun j => (if j ∈ t then c j else 0) • g j
  have ha : ∀ j, MemLp (a j) p volume := fun j => (hg j).const_smul _
  have hsum : (fun x => ∑ j ∈ t, conv (θ j) (c j • g j) volume x) =
      fun x => ∑ j ∈ t, conv (θ j) (a j) volume x := by
    funext x
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [a, hj, ↓reduceIte]
  have hnorm : (fun x => lqNorm 2 fun j => ‖a j x‖ₑ) = fun x => lqNorm 2 fun j =>
      if j ∈ t then dyadicWeight σ j * ‖g j x‖ₑ else 0 := by
    funext x
    congr 1
    funext j
    by_cases h : j ∈ t
    · simp only [a, h, ↓reduceIte, Pi.smul_apply, smul_eq_mul, eNorm_mul, hc]
    · simp only [a, h, ↓reduceIte, zero_smul, Pi.zero_apply, eNorm_zero]
  rw [hsum, ← hnorm]
  exact hθ.eLpNorm_sum_conv_le hp1 hp t ha

/-- **The synthesis bound with scaled blocks**: in dimension `n ≥ 1`, for `1 < p < ∞`, a
Calderón–Zygmund family `(θ_j)_j` with overlap `B` and Hörmander constant `H`, coefficients
`c_j ∈ ℂ` with `|c_j| = 2^{jσ}`, every finite set `t ⊆ ℕ` and `f ∈ L_p(V)`,
`‖∑_{j ∈ t} θ_j ⋆ (c_j ψ_j ⋆ f)‖_p ≤ S ‖ x ↦ ‖(1_t(j) 2^{jσ} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p` with
`S = Rd.czConst V p B H`: `Rd.IsCZFamily.eLpNorm_sum_conv_smul_le` for the blocks `ψ_j ⋆ f`,
which lie in `L_p(V)` (`Rd.memLp_blockFun`). -/
theorem IsCZFamily.eLpNorm_sum_conv_smul_blockFun_le [Nontrivial V] {θ : ℕ → V → ℂ}
    {B H : ℝ≥0∞} (hθ : IsCZFamily θ B H) (hp1 : 1 < p) (hp : p ≠ ∞) {σ : ℝ} {c : ℕ → ℂ}
    (hc : ∀ j, ‖c j‖ₑ = dyadicWeight σ j) (t : Finset ℕ) (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (fun x => ∑ j ∈ t, conv (θ j) (c j • blockFun j f) volume x) p volume ≤
      czConst V p B H * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖blockFun j f x‖ₑ else 0) p volume :=
  hθ.eLpNorm_sum_conv_smul_le hp1 hp hc t fun j => memLp_blockFun j f

/-- **The synthesis bound for derivatives of the synthesis kernels**: in dimension `n ≥ 1`, for
`1 < p < ∞`, directions `w ∈ V^k`, every finite set `s ⊆ ℕ` and `f ∈ L_p(V)`,
`‖∑_{j ∈ s} (∂^w ψTilde_j) ⋆ (ψ_j ⋆ f)‖_p ≤ C_w ‖ x ↦ ‖(1_s(j) 2^{jk} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p`
with `C_w = Rd.tlToSobolevConst p w`. Since `∂^w ψTilde_j = 2^{jk} (∂^w GTilde_j)_{2^j}`
(`Rd.iteratedLineDerivOp_psiDualS`), this is the synthesis bound of the family
`((∂^w GTilde_j)_{2^j})_j` with the coefficients `2^{jk}`, `|2^{jk}| = 2^{jk}`
(`Rd.IsCZFamily.eLpNorm_sum_conv_smul_blockFun_le`). -/
theorem eLpNorm_sum_conv_derivDual_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → V) (s : Finset ℕ) (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (fun x => ∑ j ∈ s, conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x)
        p volume ≤
      tlToSobolevConst p w * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ s then dyadicWeight (k : ℝ) j * ‖blockFun j f x‖ₑ else 0) p volume := by
  have hsum :
      (fun x => ∑ j ∈ s, conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x) =
        fun x => ∑ j ∈ s, conv (derivDualFamily w j) (((2 : ℂ) ^ (j * k)) • blockFun j f)
          volume x := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [iteratedLineDerivOp_psiDualS, smul_conv, conv_smul, Pi.smul_apply]
  rw [hsum]
  exact (isCZFamily_derivDualFamily w).eLpNorm_sum_conv_smul_blockFun_le hp1 hp
    (c := fun j => (2 : ℂ) ^ (j * k))
    (fun j => by rw [ENNReal.dyadicWeight_natCast]; exact enorm_two_pow_complex _) s f

/-- The **synthesis sums** `∑_{j ∈ t} K_j ⋆ (ψ_j ⋆ f)` of Schwartz kernels `K_j` and the blocks of
`f ∈ L_p(V)` lie in `L_p(V)` for `1 ≤ p ≤ ∞`, by Young's inequality. -/
theorem memLp_sum_conv_blockFun (K : ℕ → 𝓢(V, ℂ))
    (f : Lp ℂ p (volume : Measure V)) (t : Finset ℕ) :
    MemLp (fun x => ∑ j ∈ t, conv (K j) (blockFun j f) volume x) p volume :=
  memLp_finsetSum _ fun j _ => memLp_conv Fact.out (K j).integrable (memLp_blockFun j f)

omit [Fact (1 ≤ p)] in
/-- **Differences of synthesis sums**: let `σ` be real and `K_j` Schwartz kernels with
`‖∑_{j ∈ t} K_j ⋆ (ψ_j ⋆ f)‖_p ≤ C ‖ x ↦ ‖(1_t(j) 2^{jσ} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p` for every
finite `t`. For `N ≤ N'` the difference of the partial sums `∑_{j < J} K_j ⋆ (ψ_j ⋆ f)` at `N'`
and at `N` is the sum over `{N, …, N' - 1}`, so its `L_p` norm is at most
`C ‖ x ↦ ‖(2^{jσ} (ψ_j ⋆ f)(x))_{j ≥ N}‖_{ℓ_2} ‖_p` (`MeasureTheory.eLpNorm_lqNorm_ite_mono`). -/
theorem eLpNorm_sum_conv_blockFun_sub_le {σ : ℝ} {K : ℕ → 𝓢(V, ℂ)} {C : ℝ≥0∞}
    {f : Lp ℂ p (volume : Measure V)}
    (hK : ∀ t : Finset ℕ, eLpNorm (fun x => ∑ j ∈ t, conv (K j) (blockFun j f) volume x)
      p volume ≤ C * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖blockFun j f x‖ₑ else 0) p volume)
    {N N' : ℕ} (hNN' : N ≤ N') :
    eLpNorm ((fun x => ∑ j ∈ Finset.range N', conv (K j) (blockFun j f) volume x) -
        fun x => ∑ j ∈ Finset.range N, conv (K j) (blockFun j f) volume x) p volume ≤
      C * eLpNorm (fun x => lqNorm 2 fun j =>
        if N ≤ j then dyadicWeight σ j * ‖blockFun j f x‖ₑ else 0) p volume := by
  have hd : (fun x => ∑ j ∈ Finset.range N', conv (K j) (blockFun j f) volume x) -
      (fun x => ∑ j ∈ Finset.range N, conv (K j) (blockFun j f) volume x) =
      fun x => ∑ j ∈ Finset.Ico N N', conv (K j) (blockFun j f) volume x := by
    funext x
    rw [Pi.sub_apply, Finset.sum_Ico_eq_sub _ hNN']
  rw [hd]
  refine (hK _).trans ?_
  gcongr
  exact eLpNorm_lqNorm_ite_mono (P := (· ∈ Finset.Ico N N')) (Q := (N ≤ ·))
    (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _)
    fun j hj => (Finset.mem_Ico.1 hj).1

/-- **Cauchy synthesis sums**: let `1 ≤ p < ∞`, `σ` real, `f ∈ F^σ_{p,2}(V)` and `K_j` Schwartz
kernels with
`‖∑_{j ∈ t} K_j ⋆ (ψ_j ⋆ f)‖_p ≤ C ‖ x ↦ ‖(1_t(j) 2^{jσ} (ψ_j ⋆ f)(x))_j‖_{ℓ_2} ‖_p` for every
finite `t` and some finite `C`. Then the classes of the partial sums
`∑_{j < J} K_j ⋆ (ψ_j ⋆ f)` form a Cauchy sequence in `L_p(V)`: their differences are bounded by
the tails of the weighted blocks (`Rd.eLpNorm_sum_conv_blockFun_sub_le`), which tend to zero
(`MeasureTheory.cauchySeq_of_edist_le_lqNorm_ite`). -/
theorem cauchySeq_toLp_sum_conv_blockFun (hp : p ≠ ∞) {σ : ℝ} {K : ℕ → 𝓢(V, ℂ)} {C : ℝ≥0∞}
    (hC : C ≠ ∞) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin σ 2 f)
    (hK : ∀ t : Finset ℕ, eLpNorm (fun x => ∑ j ∈ t, conv (K j) (blockFun j f) volume x)
      p volume ≤ C * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖blockFun j f x‖ₑ else 0) p volume) :
    CauchySeq fun J => (memLp_sum_conv_blockFun K f (Finset.range J)).toLp _ :=
  cauchySeq_of_edist_le_lqNorm_ite (p := p) (q := 2)
    (g := fun j x => dyadicWeight σ j * ‖blockFun j f x‖ₑ) hC
    (zero_lt_one.trans_le Fact.out).ne' hp two_ne_zero ENNReal.ofNat_ne_top
    (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _) hf.ne fun N N' hNN' => by
      simp only [Lp.edist_toLp_toLp]
      exact eLpNorm_sum_conv_blockFun_sub_le hK hNN'

/-- **Convergent synthesis sums**: under the hypotheses of
`Rd.cauchySeq_toLp_sum_conv_blockFun`, the partial sums `∑_{j < J} K_j ⋆ (ψ_j ⋆ f)` converge in
`L_p(V)` to some `g` with `‖g‖_p ≤ C ‖f‖_{F^σ_{p,2}}`. -/
theorem exists_tendsto_sum_conv_blockFun (hp : p ≠ ∞) {σ : ℝ} {K : ℕ → 𝓢(V, ℂ)} {C : ℝ≥0∞}
    (hC : C ≠ ∞) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin σ 2 f)
    (hK : ∀ t : Finset ℕ, eLpNorm (fun x => ∑ j ∈ t, conv (K j) (blockFun j f) volume x)
      p volume ≤ C * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖blockFun j f x‖ₑ else 0) p volume) :
    ∃ g : Lp ℂ p (volume : Measure V),
      Tendsto (fun J => eLpNorm ((fun x => ∑ j ∈ Finset.range J,
        conv (K j) (blockFun j f) volume x) - ⇑g) p volume) atTop (𝓝 0) ∧
      ‖g‖ₑ ≤ C * triebelLizorkinNorm σ 2 f := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_toLp_sum_conv_blockFun hp hC hf hK)
  refine ⟨g, ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ g).1 hg).congr fun J =>
    eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub EventuallyEq.rfl), le_of_tendsto' hg.eNorm
    fun J => ?_⟩
  rw [Lp.eNorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  refine (hK _).trans ?_
  gcongr
  exact eLpNorm_lqNorm_ite_blockFun_le _ _ f

omit [Fact (1 ≤ p)] in
/-- The **partial sums of the derivative** `∂^w f`: `∑_{j < J} (∂^w ψTilde_j) ⋆ (ψ_j ⋆ f)`, the
derivatives of the reproducing sums `∑_{j < J} ψTilde_j ⋆ (ψ_j ⋆ f)`. -/
noncomputable def derivSynthesisSum {k : ℕ} (w : Fin k → V) (f : Lp ℂ p (volume : Measure V))
    (J : ℕ) : V → ℂ :=
  fun x => ∑ j ∈ Finset.range J, conv (∂^{w} (psiDualS j) : 𝓢(V, ℂ)) (blockFun j f) volume x

/-- The partial sums of the derivative lie in `L_p(V)` for `1 ≤ p ≤ ∞`, by Young's inequality
(`Rd.memLp_sum_conv_blockFun`). -/
theorem memLp_derivSynthesisSum {k : ℕ} (w : Fin k → V)
    (f : Lp ℂ p (volume : Measure V)) (J : ℕ) : MemLp (derivSynthesisSum w f J) p volume :=
  memLp_sum_conv_blockFun (fun j => ∂^{w} (psiDualS j)) f (Finset.range J)

/-- **Differences of partial sums**: in dimension `n ≥ 1`, for `1 < p < ∞` and `N ≤ N'`, the
difference of the partial sums `Rd.derivSynthesisSum` at `N'` and at `N` has `L_p` norm at most
`C_w ‖ x ↦ ‖(2^{jk} (ψ_j ⋆ f)(x))_{j ≥ N}‖_{ℓ_2} ‖_p` (`Rd.eLpNorm_sum_conv_blockFun_sub_le` with
the synthesis bound `Rd.eLpNorm_sum_conv_derivDual_le`). -/
theorem eLpNorm_derivSynthesisSum_sub_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → V) (f : Lp ℂ p (volume : Measure V)) {N N' : ℕ} (hNN' : N ≤ N') :
    eLpNorm (derivSynthesisSum w f N' - derivSynthesisSum w f N) p volume ≤
      tlToSobolevConst p w * eLpNorm (fun x => lqNorm 2 fun j =>
        if N ≤ j then dyadicWeight (k : ℝ) j * ‖blockFun j f x‖ₑ else 0) p volume :=
  eLpNorm_sum_conv_blockFun_sub_le (K := fun j => (∂^{w} (psiDualS j) : 𝓢(V, ℂ)))
    (fun t => eLpNorm_sum_conv_derivDual_le hp1 hp w t f) hNN'

/-- **The partial sums of the derivative converge**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`w ∈ V^k` and `f ∈ F^k_{p,2}(V)`, the classes in `L_p(V)` of the partial sums
`Rd.derivSynthesisSum w f J` form a Cauchy sequence (`Rd.cauchySeq_toLp_sum_conv_blockFun` with
the synthesis bound `Rd.eLpNorm_sum_conv_derivDual_le`). -/
theorem cauchySeq_toLp_derivSynthesisSum [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin (k : ℝ) 2 f) :
    CauchySeq fun J => (memLp_derivSynthesisSum w f J).toLp :=
  cauchySeq_toLp_sum_conv_blockFun hp (K := fun j => (∂^{w} (psiDualS j) : 𝓢(V, ℂ)))
    (tlToSobolevConst_ne_top hp1 hp w) hf fun t => eLpNorm_sum_conv_derivDual_le hp1 hp w t f

/-- **The partial sums are weak derivatives**: for `1 ≤ p < ∞`, `w ∈ V^k` and `f ∈ L_p(V)`,
`Rd.derivSynthesisSum w f J` is the weak derivative `∂^w` of the reproducing sum
`∑_{j < J} ψTilde_j ⋆ (ψ_j ⋆ f)` on `V` (`Rd.hasWeakLineDeriv_conv` for each term,
`Rd.HasWeakLineDeriv.sum`). -/
theorem hasWeakLineDeriv_sum_conv_psiDual (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V)
    (f : Lp ℂ p (volume : Measure V)) (J : ℕ) :
    HasWeakLineDeriv ⊤ w
      (fun x => ∑ j ∈ Finset.range J, conv (psiDual j) (blockFun j f) volume x)
      (derivSynthesisSum w f J) := by
  have h := HasWeakLineDeriv.sum (s := Finset.range J) fun j _ =>
    hasWeakLineDeriv_conv Fact.out hp (memLp_blockFun j f) (psiDualS j) w
  simp only [coe_psiDualS] at h
  rw [Finset.sum_fn, Finset.sum_fn] at h
  exact h

/-- **`F^k_{p,2} ⊆ W^k_p` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞`,
directions `w ∈ V^k` and `f ∈ F^k_{p,2}(V)`, the weak derivative `∂^w f` exists on `V` as a
class `g ∈ L_p(V)` with `‖g‖_p ≤ C_w ‖f‖_{F^k_{p,2}}`, `C_w = Rd.tlToSobolevConst p w`.
The function `g` is the limit of the partial sums `Rd.derivSynthesisSum w f J`
(`Rd.exists_tendsto_sum_conv_blockFun` with the synthesis bound
`Rd.eLpNorm_sum_conv_derivDual_le`), the weak derivatives of the reproducing sums, which tend to
`f` (`Rd.tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub`); weak derivatives pass to the limit
(`Rd.HasWeakLineDeriv.of_tendsto`). -/
theorem exists_hasWeakLineDeriv_of_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) {k : ℕ} (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemTriebelLizorkin (k : ℝ) 2 f) :
    ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst p w * triebelLizorkinNorm (k : ℝ) 2 f := by
  obtain ⟨g, hS, hg⟩ := exists_tendsto_sum_conv_blockFun hp
    (K := fun j => (∂^{w} (psiDualS j) : 𝓢(V, ℂ))) (tlToSobolevConst_ne_top hp1 hp w) hf
    fun t => eLpNorm_sum_conv_derivDual_le hp1 hp w t f
  refine ⟨g, ?_, hg⟩
  refine HasWeakLineDeriv.of_tendsto (p := p) (r := p) (l := atTop) Fact.out Fact.out
    (fun J => hasWeakLineDeriv_sum_conv_psiDual hp w f J) ?_ ?_ ?_ ?_ <;>
    rw [volume_restrict_top]
  exacts [Lp.memLp f, Lp.memLp g, tendsto_eLpNorm_sum_conv_psiDual_blockFun_sub hp f, hS]

/-- **`F^m_{p,2} ⊆ W^m_p` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`k ≤ m`, directions `w ∈ V^k` and `f ∈ F^m_{p,2}(V)`, the weak derivative `∂^w f` exists on `V`
as a class `g ∈ L_p(V)` with `‖g‖_p ≤ C_w ‖f‖_{F^m_{p,2}}`, `C_w = Rd.tlToSobolevConst p w`
(`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin` and
`‖f‖_{F^k_{p,2}} ≤ ‖f‖_{F^m_{p,2}}`, `Rd.triebelLizorkinNorm_mono_smoothness`). -/
theorem exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) {k m : ℕ} (hkm : k ≤ m) (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemTriebelLizorkin (m : ℝ) 2 f) :
    ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst p w * triebelLizorkinNorm (m : ℝ) 2 f := by
  have hkm' : (k : ℝ) ≤ m := Nat.cast_le.2 hkm
  obtain ⟨g, hg, hgn⟩ :=
    exists_hasWeakLineDeriv_of_memTriebelLizorkin hp1 hp w (hf.mono_smoothness hkm')
  refine ⟨g, hg, hgn.trans ?_⟩
  gcongr
  exact triebelLizorkinNorm_mono_smoothness hkm' 2 f

/-- **`F^m_{p,2} ⊆ W^m_p`**: in dimension `n ≥ 1`, for `1 < p < ∞`, every `f ∈ F^m_{p,2}(V)` lies
in `W^m_p(V)` (`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le`). -/
theorem memSobolev_of_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin (m : ℝ) 2 f) : MemSobolev m f :=
  (memSobolev_iff_exists_hasWeakLineDeriv f).2 fun _ hk w =>
    (exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hk w hf).imp fun _ hg => hg.1

/-- **`W^m_p = F^m_{p,2}`**: in dimension `n ≥ 1`, for `1 < p < ∞`, `m ∈ ℕ` and `f ∈ L_p(V)`,
`f ∈ W^m_p(V)` iff `f ∈ F^m_{p,2}(V)`. The norm bounds are
`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv` and
`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le`. -/
theorem memSobolev_iff_memTriebelLizorkin [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (f : Lp ℂ p (volume : Measure V)) : MemSobolev m f ↔ MemTriebelLizorkin (m : ℝ) 2 f :=
  ⟨memTriebelLizorkin_of_memSobolev hp1 hp, memSobolev_of_memTriebelLizorkin hp1 hp⟩

/-! ### The Besov sandwich -/

/-- **`W^m_p ⊆ B^m_{p,max(p,2)}`**: in dimension `n ≥ 1`, for `1 < p < ∞` and `m ≥ 1`, every
`f ∈ W^m_p(V)` lies in the approximation space `A^m_{max(p,2)}` of the band-limited scheme, the
Besov space `B^m_{p,max(p,2)}(V)` (`Rd.memApprox_of_memTriebelLizorkin`). -/
theorem memApprox_of_memSobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ} (hm : 1 ≤ m)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev m f) :
    (bandScheme hp).MemApprox (m : ℝ) (max p 2) f :=
  memApprox_of_memTriebelLizorkin hp (Nat.cast_pos.2 hm) one_le_two
    (memTriebelLizorkin_of_memSobolev hp1 hp hf)

/-- **`B^m_{p,min(p,2)} ⊆ W^m_p`**: in dimension `n ≥ 1`, for `1 < p < ∞` and `m ∈ ℕ`, every
`f` in the approximation space `A^m_{min(p,2)}` of the band-limited scheme, the Besov space
`B^m_{p,min(p,2)}(V)`, lies in `W^m_p(V)` (`Rd.memTriebelLizorkin_two_of_memApprox`). -/
theorem memSobolev_of_memApprox [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : (bandScheme hp).MemApprox (m : ℝ) (min p 2) f) :
    MemSobolev m f :=
  memSobolev_of_memTriebelLizorkin hp1 hp
    (memTriebelLizorkin_two_of_memApprox hp1 hp (Nat.cast_nonneg m) hf)

/-- **`W^m_2 = B^m_{2,2}`**: for `p = 2` and every order `m ≥ 1`, in dimension `n ≥ 1`,
`f ∈ L_2(V)` lies in `W^m_2(V)` iff `f` lies in the approximation space `A^m_2` of the
band-limited scheme, the Besov space `B^m_{2,2}(V)`, since `F^m_{2,2} = B^m_{2,2}`
(`Rd.memTriebelLizorkin_iff_memApprox`). The case `m = 1` holds in every dimension
(`Rd.memSobolev_one_iff_memApprox`). -/
theorem memSobolev_two_iff_memApprox [Nontrivial V] {m : ℕ} (hm : 1 ≤ m)
    (f : Lp ℂ 2 (volume : Measure V)) :
    MemSobolev m f ↔ (bandScheme (V := V) two_ne_top).MemApprox (m : ℝ) 2 f := by
  rw [memSobolev_iff_memTriebelLizorkin ENNReal.one_lt_two two_ne_top,
    memTriebelLizorkin_iff_memApprox two_ne_top (Nat.cast_pos.2 hm)]

/-- **`W^m_p ⊆ B^m_{p,max(p,2)}` with named constants**: under the hypotheses of
`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv` and `m ≥ 1`, the approximation norm of `f` in
`A^m_{max(p,2)}` of the band-limited scheme is at most
`2 (1 - 2^{-m})⁻¹ (‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p)`
(`Rd.approxNormDyadic_le_triebelLizorkinNorm`). -/
theorem approxNormDyadic_le_of_hasWeakLineDeriv [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} (hm : 1 ≤ m) {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    (bandScheme hp).approxNormDyadic (m : ℝ) (max p 2) f ≤
      2 * (1 - (2 : ℝ≥0∞) ^ (-(m : ℝ)))⁻¹ * (eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ) :=
  (approxNormDyadic_le_triebelLizorkinNorm hp (Nat.cast_pos.2 hm) one_le_two f).trans
    (by gcongr; exact triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg)

/-- **`B^m_{p,min(p,2)} ⊆ W^m_p` with named constants**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`m ∈ ℕ`, `k ≤ m`, directions `w ∈ V^k` and `f` in the approximation space `A^m_{min(p,2)}` of
the band-limited scheme, the weak derivative `∂^w f` is a class `g ∈ L_p(V)` with
`‖g‖_p ≤ C_w · 8 · 2^{3m} ‖Φ‖_1 ‖f‖_{A^m_{min(p,2)}}`, `C_w = Rd.tlToSobolevConst p w`
(`Rd.triebelLizorkinNorm_le_approxNormDyadic`). -/
theorem exists_hasWeakLineDeriv_of_memApprox [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {k m : ℕ} (hkm : k ≤ m) (w : Fin k → V) {f : Lp ℂ p (volume : Measure V)}
    (hf : (bandScheme hp).MemApprox (m : ℝ) (min p 2) f) :
    ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst p w * (8 * dyadicWeight (m : ℝ) 3 *
        eLpNorm (lpKernel (V := V)) 1 volume *
          (bandScheme hp).approxNormDyadic (m : ℝ) (min p 2) f) := by
  obtain ⟨g, hg, hgn⟩ := exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hkm w
    (memTriebelLizorkin_two_of_memApprox hp1 hp (Nat.cast_nonneg m) hf)
  refine ⟨g, hg, hgn.trans ?_⟩
  gcongr
  exact triebelLizorkinNorm_le_approxNormDyadic hp (Nat.cast_nonneg m) one_le_two f

end Rd
