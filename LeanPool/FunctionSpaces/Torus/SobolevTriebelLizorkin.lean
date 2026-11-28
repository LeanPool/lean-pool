/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.LpWeakDerivatives
public import LeanPool.FunctionSpaces.Torus.SquareFunction
public import LeanPool.FunctionSpaces.Torus.TriebelLizorkinLocalMeans

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev spaces `W^m_p = F^m_{p,2}` on the torus

Let `d ≥ 1`, `1 < p < ∞` and `m ∈ ℕ`. A function `f ∈ L_p(𝕋^d)` lies in the Sobolev space
`W^m_p(𝕋^d)` (`Torus.MemSobolev`: all weak derivatives `∂^α f` of order `|α| ≤ m` lie in
`L_p(𝕋^d)`) iff it lies in the Triebel–Lizorkin space `F^m_{p,2}(𝕋^d)`
(`Torus.MemTriebelLizorkin`), see `Torus.memSobolev_iff_memTriebelLizorkin`. Both directions have
named constants (`Torus.sobolevToTLConst`, `Torus.tlToSobolevConst`): constants
`Torus.periodicCZConst` of the vector-valued singular integrals on the torus, applied to the
Calderón–Zygmund families of `FunctionSpaces.Rd.Sobolev.DerivativeKernels`.

* **`W^m_p ⊆ F^m_{p,2}`** (`Torus.triebelLizorkinNorm_le_of_hasWeakLineDeriv`): with the weak
  derivatives `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the orthonormal basis
  `e = Rd.gridBasis` of `ℝ^d`, `‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p`. The dilated
  derivative kernels give `2^{jm} ψ_{j+1} ⋆ f = ∑_α (η_α)_{2^j} ⋆ g_α`
  (`Torus.two_pow_mul_blockFun_succ_ae`; on the Fourier side,
  `Torus.fourier_two_pow_smul_psi_succ`), and the analysis bound on the torus
  (`Torus.eLpNorm_lqNorm_econv_le`) bounds each sum.
* **`F^m_{p,2} ⊆ W^m_p`** (`Torus.exists_hasWeakLineDeriv_of_memTriebelLizorkin`): for
  `f ∈ F^k_{p,2}(𝕋^d)` and directions `w ∈ (ℝ^d)^k`, the partial sums
  `∑_{j < J} (∂^w ψTilde_j) ⋆ Δ_j f` (`Torus.derivSynthesisSum`) are the weak derivatives `∂^w` of
  `∑_{j < J} Δ_j f → f`, and a Cauchy sequence in `L_p(𝕋^d)` by the synthesis bound on the torus
  (`Torus.eLpNorm_sum_econv_le`); their limit `g` is `∂^w f`, with `‖g‖_p ≤ C_w ‖f‖_{F^k_{p,2}}`.

With the Besov sandwich, `B^m_{p,min(p,2)}(𝕋^d) ⊆ W^m_p(𝕋^d)` and, for `m ≥ 1`,
`W^m_p(𝕋^d) ⊆ B^m_{p,max(p,2)}(𝕋^d)` (`Torus.memSobolev_of_memBesov`,
`Torus.memBesov_of_memSobolev`, with norm bounds in `Torus.exists_hasWeakLineDeriv_of_memBesov`
and `Torus.approxNormDyadic_le_of_hasWeakLineDeriv`), and `W^m_p(𝕋^d)` is described by local
means (`Torus.memSobolev_iff_tlLocalMeans`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Filter Module
open scoped ENNReal TorusHaar Topology SchwartzMap LineDeriv FourierTransform

open ENNReal (lqNorm dyadicWeight)

namespace Torus

variable {d : Type*} [Fintype d]

/-! ### The blocks through derivatives -/

/-- **The dilated derivative identity on the Fourier side**: for all `m, j ∈ ℕ` and `ξ ∈ ℝ^d`,
`2^{jm} 𝓕ψ_{j+1}(ξ) = ∑_α (∏_l 2πi ⟪ξ, e_{α_l}⟫) 𝓕(η_α)_{2^j}(ξ)`, the Fourier transform of
`Rd.two_pow_smul_psi_succ_eq_sum`. -/
theorem fourier_two_pow_smul_psi_succ (m j : ℕ) (ξ : EuclideanSpace ℝ d) :
    (2 : ℂ) ^ (j * m) * 𝓕 (Rd.psi (V := EuclideanSpace ℝ d) (j + 1)) ξ =
      ∑ i : Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d)),
        (∏ l, 2 * Real.pi * Complex.I *
          (inner ℝ ξ (Rd.gridBasis (EuclideanSpace ℝ d) (i l)) : ℂ)) *
          𝓕 (Rd.derivFamily i j) ξ := by
  have h := congrFun (congrArg 𝓕
    (Rd.two_pow_smul_psi_succ_eq_sum (V := EuclideanSpace ℝ d) m j)) ξ
  have hs : 𝓕 ((2 : ℂ) ^ (j * m) • Rd.psi (V := EuclideanSpace ℝ d) (j + 1)) ξ =
      (2 : ℂ) ^ (j * m) * 𝓕 (Rd.psi (V := EuclideanSpace ℝ d) (j + 1)) ξ :=
    congrFun (VectorFourier.fourierIntegral_const_smul _ _ _ _ _) ξ
  rw [hs] at h
  set K : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) → 𝓢(EuclideanSpace ℝ d, ℂ) :=
    fun i => ∂^{fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)}
      (Rd.schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (Rd.derivKernel i)) with hK
  have hc : (∑ i, ⇑(K i)) = ⇑(∑ i, K i) := funext fun x => by rw [sum_apply, Finset.sum_apply]
  rw [h, hc, ← SchwartzMap.fourier_coe, FourierTransform.fourier_sum, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hK]
  rw [SchwartzMap.fourier_iteratedLineDerivOp_apply, smul_eq_mul,
    SchwartzMap.fourier_coe, Rd.coe_schwartzDilate]
  rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The blocks of `f` through its derivatives, in `L_p(𝕋^d)`**: for `1 ≤ p < ∞`, if
`g_α ∈ L_p(𝕋^d)` is the weak derivative `∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` for every multi-index
`α`, then `2^{jm} Δ_{j+1} f = ∑_α (η_α)_{2^j} ⋆ g_α` for every `j`. Both sides have the Fourier
coefficients `2^{jm} 𝓕ψ_{j+1}(k) f̂(k)` (`Torus.fourier_two_pow_smul_psi_succ`). -/
theorem two_pow_smul_lpBlock_succ (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i))
    (j : ℕ) :
    (2 : ℂ) ^ (j * m) • lpBlock hp (j + 1) f =
      ∑ i, econvLp hp ((Rd.isCZFamily_derivFamily i).integrable j) (g i) :=
  eq_of_mFourierCoeff_eq fun n => by
    rw [mFourierCoeff_smul, lpBlock, mFourierCoeff_econvLp, mFourierCoeff_sum, ← mul_assoc,
      fourier_two_pow_smul_psi_succ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mFourierCoeff_econvLp, hg i n, lineSymbol]
    ring

/-- **The blocks of `f` through its derivatives at every point**: under the hypotheses of
`Torus.two_pow_smul_lpBlock_succ`, for almost every `t ∈ 𝕋^d` and every `j`,
`2^{jm} (ψ_{j+1} ⋆ f)(t) = ∑_α ((η_α)_{2^j} ⋆ g_α)(t)`. -/
theorem two_pow_mul_blockFun_succ_ae (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i)) :
    ∀ᵐ t ∂volume, ∀ j, (2 : ℂ) ^ (j * m) * blockFun (j + 1) f t =
      ∑ i, econv (Rd.derivFamily i j) (g i) t := by
  refine ae_all_iff.2 fun j => ?_
  filter_upwards [Lp.coeFn_smul ((2 : ℂ) ^ (j * m)) (lpBlock hp (j + 1) f),
    lpBlock_ae_eq_blockFun hp (j + 1) f,
    coeFn_sum_econvLp_ae hp Finset.univ (fun i => (Rd.isCZFamily_derivFamily i).integrable j) g]
    with t h1 h2 h3
  rw [← h2, ← smul_eq_mul, ← Pi.smul_apply ((2 : ℂ) ^ (j * m)) (⇑(lpBlock hp (j + 1) f)), ← h1,
    two_pow_smul_lpBlock_succ hp hg j, h3]

/-- **The pointwise bound of the higher blocks**: under the hypotheses of
`Torus.two_pow_smul_lpBlock_succ`, for almost every `t`,
`‖(2^{(j+1)m} (ψ_{j+1} ⋆ f)(t))_j‖_{ℓ_2} ≤ 2^m ∑_α ‖(((η_α)_{2^j} ⋆ g_α)(t))_j‖_{ℓ_2}`, by
Minkowski's inequality in `ℓ_2` (`ENNReal.lqNorm_dyadicWeight_succ_le_sum`). -/
theorem lqNorm_blockFun_succ_le_sum_ae (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i)) :
    ∀ᵐ t ∂volume,
      lqNorm 2 (fun n => dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f t‖ₑ) ≤
        2 ^ m * ∑ i, lqNorm 2 (fun n => ‖econv (Rd.derivFamily i n) (g i) t‖ₑ) := by
  filter_upwards [two_pow_mul_blockFun_succ_ae hp hg] with t ht
  refine ENNReal.lqNorm_dyadicWeight_succ_le_sum one_le_two Finset.univ fun n => ?_
  rw [← Rd.enorm_two_pow_complex, ← eNorm_mul, ht n]
  exact eNorm_sum_le _ _

/-! ### `W^m_p ⊆ F^m_{p,2}` -/

variable (d) in
/-- The constant `K_α` of the bound `W^m_p ⊆ F^m_{p,2}` on the torus for the multi-index `α`: the
constant `Torus.periodicCZConst d p 2 (4 H_{A^α}) (2 T_{A^α})` of the Calderón–Zygmund family of
the dilated derivative kernels `(η_α)_{2^j}` (`Rd.isCZFamily_derivFamily`), with the far mass
bound `2 T_{A^α}` (`Torus.farMass_derivFamily_le`), where `A^α = Rd.derivKernelBound α`. -/
noncomputable def sobolevToTLConst (p : ℝ≥0∞) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) : ℝ≥0∞ :=
  periodicCZConst d p 2
    (4 * Rd.familyHormanderConst (EuclideanSpace ℝ d) (Rd.derivKernelBound i))
    (2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.derivKernelBound i) 0 1)

omit [Fact (1 ≤ p)] in
/-- The constant `Torus.sobolevToTLConst d p α` is finite for `1 < p < ∞`. -/
theorem sobolevToTLConst_ne_top (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (i : Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) : sobolevToTLConst d p i ≠ ∞ :=
  periodicCZConst_ne_top hp1 hp ENNReal.ofNat_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyHormanderConst_ne_top _))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyTailConst_ne_top _ _ _))

/-- **The higher blocks in `L_p(ℓ_2)`**: for `d ≥ 1`, `1 < p < ∞` and weak derivatives `g_α` as in
`Torus.two_pow_smul_lpBlock_succ`,
`‖ t ↦ ‖(2^{(j+1)m} (ψ_{j+1} ⋆ f)(t))_j‖_{ℓ_2} ‖_p ≤ 2^m ∑_α K_α ‖g_α‖_p` with
`K_α = Torus.sobolevToTLConst d p α`: the pointwise bound, Minkowski's inequality in `L_p`
(`MeasureTheory.eLpNorm_le_const_mul_sum_of_ae_le`), and the analysis bound on the torus
(`Torus.eLpNorm_lqNorm_econv_le`). -/
theorem eLpNorm_lqNorm_blockFun_succ_le [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i)) :
    eLpNorm (fun t => lqNorm 2 (fun n =>
        dyadicWeight (m : ℝ) (n + 1) * ‖blockFun (n + 1) f t‖ₑ)) p volume ≤
      2 ^ m * ∑ i, sobolevToTLConst d p i * ‖g i‖ₑ := by
  have hF : ∀ i, AEMeasurable
      (fun t => lqNorm 2 (fun n => ‖econv (Rd.derivFamily i n) (g i) t‖ₑ)) volume :=
    fun i => aemeasurable_lqNorm_comp (fun n => (aestronglyMeasurable_econv
      ((Rd.isCZFamily_derivFamily i).integrable n).aestronglyMeasurable
      (Lp.stronglyMeasurable (g i)).measurable).eNorm) 2
  refine (eLpNorm_le_const_mul_sum_of_ae_le (p := p) Fact.out Finset.univ
    (aemeasurable_lqNorm_comp (fun n =>
      (aestronglyMeasurable_blockFun (n + 1) f).eNorm.const_mul _) 2)
    (fun i _ => hF i) _ (lqNorm_blockFun_succ_le_sum_ae hp hg)).trans ?_
  gcongr with i
  exact eLpNorm_lqNorm_econv_le (Rd.isCZFamily_derivFamily i) (farMass_derivFamily_le i)
    hp1 hp (g i)

/-- **`W^m_p(𝕋^d) ⊆ F^m_{p,2}(𝕋^d)` with named constants**: for `d ≥ 1`, `1 < p < ∞` and
`f ∈ L_p(𝕋^d)` whose weak derivatives `g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the
orthonormal basis `e = Rd.gridBasis` of `ℝ^d` lie in `L_p(𝕋^d)` for every multi-index `α`,
`‖f‖_{F^m_{p,2}} ≤ ‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p` with `K_α = Torus.sobolevToTLConst d p α`.
The block `j = 0` is split off from the `ℓ_2` norm
(`MeasureTheory.eLpNorm_lqNorm_dyadicWeight_le_zero_add_succ`) and bounded by Young's inequality
(`Torus.eLpNorm_blockFun_zero_le`); the other blocks by `Torus.eLpNorm_lqNorm_blockFun_succ_le`. -/
theorem triebelLizorkinNorm_le_of_hasWeakLineDeriv [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i)) :
    triebelLizorkinNorm (m : ℝ) 2 f ≤
      eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst d p i * ‖g i‖ₑ := by
  refine (eLpNorm_lqNorm_dyadicWeight_le_zero_add_succ (p := p) Fact.out one_le_two _
    fun j => (aestronglyMeasurable_blockFun j f).eNorm).trans ?_
  gcongr
  · rw [eLpNorm_eNorm _ (aestronglyMeasurable_blockFun 0 f)]
    exact eLpNorm_blockFun_zero_le hp f
  · exact eLpNorm_lqNorm_blockFun_succ_le hp1 hp hg

/-- **The weak derivatives of order `m` along the basis vectors give `f ∈ F^m_{p,2}(𝕋^d)`**: for
`d ≥ 1` and `1 < p < ∞`, since the bound `Torus.triebelLizorkinNorm_le_of_hasWeakLineDeriv` is
finite. -/
theorem memTriebelLizorkin_of_hasWeakLineDeriv [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i)) :
    MemTriebelLizorkin (m : ℝ) 2 f :=
  (triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg).trans_lt
    (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top
      Rd.eLpNorm_lpKernel_lt_top eNorm_lt_top,
      ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofNat_lt_top) (ENNReal.sum_lt_top.2 fun i _ =>
        ENNReal.mul_lt_top (sobolevToTLConst_ne_top hp1 hp i).lt_top eNorm_lt_top)⟩)

/-- **`W^m_p(𝕋^d) ⊆ F^m_{p,2}(𝕋^d)`**: for `d ≥ 1` and `1 < p < ∞`, every `f ∈ W^m_p(𝕋^d)` lies in
`F^m_{p,2}(𝕋^d)`; the weak derivatives of order `m` along the basis vectors suffice
(`Torus.memTriebelLizorkin_of_hasWeakLineDeriv`). -/
theorem memTriebelLizorkin_of_memSobolev [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemSobolev m f) :
    MemTriebelLizorkin (m : ℝ) 2 f := by
  have hd : ∀ i : Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d)),
      ∃ g : Lp ℂ p (volume : Measure (UnitAddTorus d)),
        HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f g := fun i =>
    memSobolev_iff_exists_hasWeakLineDeriv.1 hf m le_rfl _
  choose g hg using hd
  exact memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg

/-! ### `F^m_{p,2} ⊆ W^m_p` -/

variable (d) in
/-- The constant `C_w` of the bound `F^k_{p,2} ⊆ W^k_p` on the torus for the directions
`w ∈ (ℝ^d)^k`: the constant `Torus.periodicCZConst d p B (4 H_{Ã^w}) (2 T_{Ã^w})` of the
Calderón–Zygmund family `((∂^w GTilde_j)_{2^j})_j` (`Rd.isCZFamily_derivDualFamily`), with the
overlap
`B = 4 ((8π)^k ∏_l ‖w_l‖)²` (`Rd.derivDualOverlap`) and the far mass bound `2 T_{Ã^w}`
(`Torus.farMass_derivDualFamily_le`), where `Ã^w = Rd.derivDualBound w`. -/
noncomputable def tlToSobolevConst (p : ℝ≥0∞) {k : ℕ} (w : Fin k → EuclideanSpace ℝ d) :
    ℝ≥0∞ :=
  periodicCZConst d p (Rd.derivDualOverlap w)
    (4 * Rd.familyHormanderConst (EuclideanSpace ℝ d) (Rd.derivDualBound w))
    (2 * Rd.familyTailConst (EuclideanSpace ℝ d) (Rd.derivDualBound w) 0 1)

omit [Fact (1 ≤ p)] in
/-- The constant `Torus.tlToSobolevConst d p w` is finite for `1 < p < ∞`. -/
theorem tlToSobolevConst_ne_top (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ d) : tlToSobolevConst d p w ≠ ∞ :=
  periodicCZConst_ne_top hp1 hp (Rd.derivDualOverlap_ne_top w)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyHormanderConst_ne_top _))
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (Rd.familyTailConst_ne_top _ _ _))

/-- **The synthesis bound for derivatives of the synthesis kernels on the torus**: for `d ≥ 1`,
`1 < p < ∞`, directions `w ∈ (ℝ^d)^k`, every finite set `s ⊆ ℕ` and `f ∈ L_p(𝕋^d)`,
`‖∑_{j ∈ s} (∂^w ψTilde_j) ⋆ Δ_j f‖_p ≤ C_w ‖ t ↦ ‖(1_s(j) 2^{jk} (ψ_j ⋆ f)(t))_j‖_{ℓ_2} ‖_p` with
`C_w = Torus.tlToSobolevConst d p w`. Since `∂^w ψTilde_j = 2^{jk} (∂^w GTilde_j)_{2^j}`
(`Rd.iteratedLineDerivOp_psiDualS`), this is the synthesis bound on the torus
(`Torus.eLpNorm_sum_econv_le`) with the coefficients `1_s(j) 2^{jk} Δ_j f`. -/
theorem enorm_sum_econvLp_derivDual_le [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ d) (s : Finset ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    ‖∑ j ∈ s, econvLp hp (∂^{w} (Rd.psiDualS (V := EuclideanSpace ℝ d) j)).integrable
        (lpBlock hp j f)‖ₑ ≤
      tlToSobolevConst d p w * eLpNorm (fun t => lqNorm 2 fun j =>
        if j ∈ s then dyadicWeight (k : ℝ) j * ‖blockFun j f t‖ₑ else 0) p volume := by
  set a : ℕ → UnitAddTorus d → ℂ :=
    fun j => (if j ∈ s then (2 : ℂ) ^ (j * k) else 0) • ⇑(lpBlock hp j f)
  have hsum : ⇑(∑ j ∈ s, econvLp hp (∂^{w} (Rd.psiDualS (V := EuclideanSpace ℝ d) j)).integrable
      (lpBlock hp j f)) =ᵐ[volume] fun t => ∑ j ∈ s, econv (Rd.derivDualFamily w j) (a j) t := by
    filter_upwards [coeFn_sum_econvLp_ae hp s
      (fun j => (∂^{w} (Rd.psiDualS (V := EuclideanSpace ℝ d) j)).integrable)
      fun j => lpBlock hp j f] with t h
    rw [h]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Rd.iteratedLineDerivOp_psiDualS, econv_smul_kernel]
    simp only [a, hj, ↓reduceIte]
  have hnorm : (fun t => lqNorm 2 fun j => ‖a j t‖ₑ) =ᵐ[volume] fun t => lqNorm 2 fun j =>
      if j ∈ s then dyadicWeight (k : ℝ) j * ‖blockFun j f t‖ₑ else 0 := by
    filter_upwards [ae_all_iff.2 fun j => lpBlock_ae_eq_blockFun hp j f] with t ht
    congr 1
    funext j
    simp only [a, Pi.smul_apply, smul_eq_mul, eNorm_mul, ht j]
    split_ifs
    · rw [Rd.enorm_two_pow_complex, ENNReal.dyadicWeight_natCast]
    · rw [eNorm_zero, zero_mul]
  rw [Lp.eNorm_def, eLpNorm_congr_ae hsum, ← eLpNorm_congr_ae hnorm]
  exact eLpNorm_sum_econv_le (Rd.isCZFamily_derivDualFamily w) (farMass_derivDualFamily_le w)
    hp1 hp s (fun j => (Lp.stronglyMeasurable _).measurable.const_smul _)
    fun j => (Lp.memLp _).const_smul _

/-- The **partial sums of the derivative** `∂^w f` on the torus:
`∑_{j < J} (∂^w ψTilde_j) ⋆ Δ_j f ∈ L_p(𝕋^d)`, the derivatives of the partial sums
`∑_{j < J} Δ_j f` (`Torus.hasWeakLineDeriv_sum_lpBlock`). -/
noncomputable def derivSynthesisSum (hp : p ≠ ∞) {k : ℕ} (w : Fin k → EuclideanSpace ℝ d)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (J : ℕ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  ∑ j ∈ Finset.range J, econvLp hp (∂^{w} (Rd.psiDualS (V := EuclideanSpace ℝ d) j)).integrable
    (lpBlock hp j f)

/-- **The partial sums are weak derivatives**: for `1 ≤ p < ∞`, `w ∈ (ℝ^d)^k` and
`f ∈ L_p(𝕋^d)`, `Torus.derivSynthesisSum hp w f J = ∂^w (∑_{j < J} Δ_j f)`. Each term is
`∂^w (ψTilde_j ⋆ Δ_j f)` (`Torus.hasWeakLineDeriv_econvLp`), and `ψTilde_j ⋆ Δ_j f = Δ_j f`
(`Torus.econvLp_psiDual_lpBlock`). -/
theorem hasWeakLineDeriv_sum_lpBlock (hp : p ≠ ∞) {k : ℕ} (w : Fin k → EuclideanSpace ℝ d)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (J : ℕ) :
    HasWeakLineDeriv w (∑ j ∈ Finset.range J, lpBlock hp j f) (derivSynthesisSum hp w f J) :=
  HasWeakLineDeriv.sum _ fun j _ => by
    have h := hasWeakLineDeriv_econvLp hp w (Rd.psiDualS (V := EuclideanSpace ℝ d) j)
      (lpBlock hp j f)
    rwa [econvLp_congr_kernel hp _ (Rd.integrable_psiDual j) (Rd.coe_psiDualS j),
      econvLp_psiDual_lpBlock] at h

/-- **Differences of partial sums**: for `d ≥ 1`, `1 < p < ∞` and `N ≤ N'`,
`‖Torus.derivSynthesisSum hp w f N' - Torus.derivSynthesisSum hp w f N‖_p` is at most
`C_w ‖ t ↦ ‖(2^{jk} (ψ_j ⋆ f)(t))_{j ≥ N}‖_{ℓ_2} ‖_p` (`Torus.enorm_sum_econvLp_derivDual_le`
for the set `{N, …, N' - 1}`; `MeasureTheory.eLpNorm_lqNorm_ite_mono`). -/
theorem enorm_derivSynthesisSum_sub_le [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ d) (f : Lp ℂ p (volume : Measure (UnitAddTorus d)))
    {N N' : ℕ} (hNN' : N ≤ N') :
    ‖derivSynthesisSum hp w f N' - derivSynthesisSum hp w f N‖ₑ ≤
      tlToSobolevConst d p w * eLpNorm (fun t => lqNorm 2 fun j =>
        if N ≤ j then dyadicWeight (k : ℝ) j * ‖blockFun j f t‖ₑ else 0) p volume := by
  rw [derivSynthesisSum, derivSynthesisSum, ← Finset.sum_Ico_eq_sub _ hNN']
  refine (enorm_sum_econvLp_derivDual_le hp1 hp w _ f).trans ?_
  gcongr
  exact eLpNorm_lqNorm_ite_mono (P := (· ∈ Finset.Ico N N')) (Q := (N ≤ ·))
    (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _)
    fun j hj => (Finset.mem_Ico.1 hj).1

/-- **The partial sums of the derivative converge**: for `d ≥ 1`, `1 < p < ∞`, `w ∈ (ℝ^d)^k` and
`f ∈ F^k_{p,2}(𝕋^d)`, the partial sums `Torus.derivSynthesisSum hp w f J` form a Cauchy sequence
in `L_p(𝕋^d)`: their differences are bounded by the tails of the weighted blocks
(`Torus.enorm_derivSynthesisSum_sub_le`), which tend to zero
(`MeasureTheory.cauchySeq_of_edist_le_lqNorm_ite`). -/
theorem cauchySeq_derivSynthesisSum [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ d) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : MemTriebelLizorkin (k : ℝ) 2 f) : CauchySeq (derivSynthesisSum hp w f) :=
  cauchySeq_of_edist_le_lqNorm_ite (p := p) (q := 2)
    (g := fun j t => dyadicWeight (k : ℝ) j * ‖blockFun j f t‖ₑ)
    (tlToSobolevConst_ne_top hp1 hp w) (zero_lt_one.trans_le Fact.out).ne' hp two_ne_zero
    ENNReal.ofNat_ne_top (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _) hf.ne
    fun N N' hNN' => by
      rw [eDist_eq_eNorm_sub]
      exact enorm_derivSynthesisSum_sub_le hp1 hp w f hNN'

/-- **`F^k_{p,2}(𝕋^d) ⊆ W^k_p(𝕋^d)` with named constants**: for `d ≥ 1`, `1 < p < ∞`,
directions `w ∈ (ℝ^d)^k` and `f ∈ F^k_{p,2}(𝕋^d)`, the weak derivative `∂^w f` exists as a class
`g ∈ L_p(𝕋^d)` with `‖g‖_p ≤ C_w ‖f‖_{F^k_{p,2}}`, `C_w = Torus.tlToSobolevConst d p w`. The class
`g` is the limit of the partial sums `Torus.derivSynthesisSum hp w f J`
(`Torus.cauchySeq_derivSynthesisSum`), the weak derivatives of `∑_{j < J} Δ_j f → f`
(`Torus.tendsto_sum_lpBlock`); weak derivatives pass to the limit
(`Torus.HasWeakLineDeriv.of_tendsto`). -/
theorem exists_hasWeakLineDeriv_of_memTriebelLizorkin [Nonempty d] (hp1 : 1 < p)
    (hp : p ≠ ∞) {k : ℕ} (w : Fin k → EuclideanSpace ℝ d)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemTriebelLizorkin (k : ℝ) 2 f) :
    ∃ g : Lp ℂ p (volume : Measure (UnitAddTorus d)), HasWeakLineDeriv w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst d p w * triebelLizorkinNorm (k : ℝ) 2 f := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_derivSynthesisSum hp1 hp w hf)
  refine ⟨g, HasWeakLineDeriv.of_tendsto (tendsto_sum_lpBlock hp f) hg
    (Eventually.of_forall fun J => hasWeakLineDeriv_sum_lpBlock hp w f J),
    le_of_tendsto' hg.eNorm fun J => ?_⟩
  refine (enorm_sum_econvLp_derivDual_le hp1 hp w _ f).trans ?_
  gcongr
  exact eLpNorm_lqNorm_ite_blockFun_le _ _ f

/-- **`F^m_{p,2}(𝕋^d) ⊆ W^m_p(𝕋^d)` with named constants**: for `d ≥ 1`, `1 < p < ∞`, `k ≤ m`,
directions `w ∈ (ℝ^d)^k` and `f ∈ F^m_{p,2}(𝕋^d)`, the weak derivative `∂^w f` is a class
`g ∈ L_p(𝕋^d)` with `‖g‖_p ≤ C_w ‖f‖_{F^m_{p,2}}`, `C_w = Torus.tlToSobolevConst d p w`
(`Torus.exists_hasWeakLineDeriv_of_memTriebelLizorkin` and
`Torus.triebelLizorkinNorm_mono_smoothness`). -/
theorem exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le [Nonempty d] (hp1 : 1 < p)
    (hp : p ≠ ∞) {k m : ℕ} (hkm : k ≤ m) (w : Fin k → EuclideanSpace ℝ d)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemTriebelLizorkin (m : ℝ) 2 f) :
    ∃ g : Lp ℂ p (volume : Measure (UnitAddTorus d)), HasWeakLineDeriv w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst d p w * triebelLizorkinNorm (m : ℝ) 2 f := by
  have hkm' : (k : ℝ) ≤ m := Nat.cast_le.2 hkm
  obtain ⟨g, hg, hgn⟩ :=
    exists_hasWeakLineDeriv_of_memTriebelLizorkin hp1 hp w (hf.mono_smoothness hkm')
  refine ⟨g, hg, hgn.trans ?_⟩
  gcongr
  exact triebelLizorkinNorm_mono_smoothness hkm' 2 f

/-- **`F^m_{p,2}(𝕋^d) ⊆ W^m_p(𝕋^d)`**: for `d ≥ 1` and `1 < p < ∞`, every `f ∈ F^m_{p,2}(𝕋^d)`
lies in `W^m_p(𝕋^d)` (`Torus.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le` and
`Torus.memSobolev_iff_exists_hasWeakLineDeriv`). -/
theorem memSobolev_of_memTriebelLizorkin [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemTriebelLizorkin (m : ℝ) 2 f) :
    MemSobolev m f :=
  memSobolev_iff_exists_hasWeakLineDeriv.2 fun _ hk w =>
    (exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hk w hf).imp fun _ hg => hg.1

/-- **`W^m_p(𝕋^d) = F^m_{p,2}(𝕋^d)`**: for `d ≥ 1`, `1 < p < ∞`, `m ∈ ℕ` and `f ∈ L_p(𝕋^d)`,
`f ∈ W^m_p(𝕋^d)` iff `f ∈ F^m_{p,2}(𝕋^d)`. The norm bounds are
`Torus.triebelLizorkinNorm_le_of_hasWeakLineDeriv` and
`Torus.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le`. For `p = 2` and `m ≥ 1`, together
with `F^m_{2,2} = B^m_{2,2}` (`Torus.memTriebelLizorkin_iff_memBesov`), this gives
`W^m_2 = B^m_{2,2}` once more (`Torus.memSobolev_iff_memBesov`). -/
theorem memSobolev_iff_memTriebelLizorkin [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    MemSobolev m f ↔ MemTriebelLizorkin (m : ℝ) 2 f :=
  ⟨memTriebelLizorkin_of_memSobolev hp1 hp, memSobolev_of_memTriebelLizorkin hp1 hp⟩

/-! ### The Besov sandwich and local means -/

/-- **`W^m_p(𝕋^d) ⊆ B^m_{p,max(p,2)}(𝕋^d)`**: for `d ≥ 1`, `1 < p < ∞` and `m ≥ 1`, every
`f ∈ W^m_p(𝕋^d)` lies in the Besov space `B^m_{p,max(p,2)}(𝕋^d)` of the scheme of trigonometric
polynomials (`Torus.trigScheme`), by `Torus.memBesov_of_memTriebelLizorkin`. -/
theorem memBesov_of_memSobolev [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ} (hm : 1 ≤ m)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemSobolev m f) :
    (trigScheme d).MemBesov volume p (m : ℝ) (max p 2) f :=
  memBesov_of_memTriebelLizorkin hp (Nat.cast_pos.2 hm) one_le_two
    (memTriebelLizorkin_of_memSobolev hp1 hp hf)

/-- **`B^m_{p,min(p,2)}(𝕋^d) ⊆ W^m_p(𝕋^d)`**: for `d ≥ 1`, `1 < p < ∞` and `m ∈ ℕ`, every `f` in
the Besov space `B^m_{p,min(p,2)}(𝕋^d)` lies in `W^m_p(𝕋^d)`
(`Torus.memTriebelLizorkin_two_of_memBesov`). -/
theorem memSobolev_of_memBesov [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : (trigScheme d).MemBesov volume p (m : ℝ) (min p 2) f) : MemSobolev m f :=
  memSobolev_of_memTriebelLizorkin hp1 hp
    (memTriebelLizorkin_two_of_memBesov hp1 hp (Nat.cast_nonneg m) hf)

/-- **`W^m_p(𝕋^d) ⊆ B^m_{p,max(p,2)}(𝕋^d)` with named constants**: under the hypotheses of
`Torus.triebelLizorkinNorm_le_of_hasWeakLineDeriv` and `m ≥ 1`, the approximation norm of `f` in
`A^m_{max(p,2)}` of the trigonometric polynomials is at most
`2 · 2^m (1 - 2^{-m})⁻¹ (‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p)`
(`Torus.approxNormDyadic_le_triebelLizorkinNorm`). -/
theorem approxNormDyadic_le_of_hasWeakLineDeriv [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} (hm : 1 ≤ m) {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    {g : (Fin m → Fin (finrank ℝ (EuclideanSpace ℝ d))) →
      Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hg : ∀ i, HasWeakLineDeriv (fun k => Rd.gridBasis (EuclideanSpace ℝ d) (i k)) f (g i)) :
    ((trigScheme d).toLp volume p).approxNormDyadic (m : ℝ) (max p 2) f ≤
      2 * dyadicWeight (m : ℝ) 1 * (1 - (2 : ℝ≥0∞) ^ (-(m : ℝ)))⁻¹ *
        (eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume * ‖f‖ₑ +
          2 ^ m * ∑ i, sobolevToTLConst d p i * ‖g i‖ₑ) :=
  (approxNormDyadic_le_triebelLizorkinNorm hp (Nat.cast_pos.2 hm) one_le_two f).trans
    (by gcongr; exact triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg)

/-- **`B^m_{p,min(p,2)}(𝕋^d) ⊆ W^m_p(𝕋^d)` with named constants**: for `d ≥ 1`, `1 < p < ∞`,
`k ≤ m`, directions `w ∈ (ℝ^d)^k` and `f ∈ B^m_{p,min(p,2)}(𝕋^d)`, the weak derivative `∂^w f` is
a class `g ∈ L_p(𝕋^d)` with
`‖g‖_p ≤ C_w · 2 (#d + 1) 2^{(#d + 1) m} ‖Φ‖_1 ‖f‖_{A^m_{min(p,2)}}`,
`C_w = Torus.tlToSobolevConst d p w` (`Torus.triebelLizorkinNorm_le_approxNormDyadic`). -/
theorem exists_hasWeakLineDeriv_of_memBesov [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞)
    {k m : ℕ} (hkm : k ≤ m) (w : Fin k → EuclideanSpace ℝ d)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))}
    (hf : (trigScheme d).MemBesov volume p (m : ℝ) (min p 2) f) :
    ∃ g : Lp ℂ p (volume : Measure (UnitAddTorus d)), HasWeakLineDeriv w f g ∧
      ‖g‖ₑ ≤ tlToSobolevConst d p w * (2 * ((Fintype.card d : ℝ≥0∞) + 1) *
        dyadicWeight (m : ℝ) (Fintype.card d + 1) *
          eLpNorm (Rd.lpKernel (V := EuclideanSpace ℝ d)) 1 volume *
            ((trigScheme d).toLp volume p).approxNormDyadic (m : ℝ) (min p 2) f) := by
  obtain ⟨g, hg, hgn⟩ := exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hkm w
    (memTriebelLizorkin_two_of_memBesov hp1 hp (Nat.cast_nonneg m) hf)
  refine ⟨g, hg, hgn.trans ?_⟩
  gcongr
  exact triebelLizorkinNorm_le_approxNormDyadic hp (Nat.cast_nonneg m) one_le_two f

/-- **`W^m_p(𝕋^d)` by local means**: for `d ≥ 1`, `1 < p < ∞`, a bump `b` on `ℝ^d` and orders
`1 ≤ m < L`, `f ∈ W^m_p(𝕋^d)` iff `‖f‖_{F^m_{p,2}}^{b,L} < ∞`, through `W^m_p = F^m_{p,2}` and
the local means characterisation of `F^m_{p,2}(𝕋^d)` (`Torus.memTriebelLizorkin_iff_tlLocalMeans`
with `q = 2`). -/
theorem memSobolev_iff_tlLocalMeans [Nonempty d] (b : Rd.LocalMeansBump (EuclideanSpace ℝ d))
    (hp1 : 1 < p) (hp : p ≠ ∞) {m L : ℕ} (hm : 1 ≤ m) (hmL : m < L)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    MemSobolev m f ↔ tlLocalMeansNorm b L (m : ℝ) 2 f < ∞ :=
  (memSobolev_iff_memTriebelLizorkin hp1 hp f).trans
    (memTriebelLizorkin_iff_tlLocalMeans b hp1 hp ENNReal.one_lt_two (Nat.cast_pos.2 hm)
      (Nat.cast_lt.2 hmL))

end Torus
