/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.LittlewoodPaley.LittlewoodPaley
public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences
public import LeanPool.FunctionSpaces.Analysis.Lp.MixedNorms

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Triebel–Lizorkin spaces on `V`

For `1 ≤ p < ∞`, `s ∈ ℝ`, `1 ≤ q ≤ ∞` and `f ∈ L_p(V)`, the **Triebel–Lizorkin quasi-norm**

`‖f‖_{F^s_{p,q}} = ‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p`

(`Rd.triebelLizorkinNorm`) takes the `ℓ_q` norm of the Littlewood–Paley blocks at every point
before the `L_p` norm, the reverse of the order in the Littlewood–Paley quasi-norm of the Besov
spaces (`Rd.littlewoodPaleyNorm`). The blocks are the pointwise convolutions `ψ_j ⋆ f`
(`Rd.blockFun`), bounded at every point by the weighted Jensen inequality
(`Rd.enorm_conv_le_of_enorm_le`, `Rd.enorm_blockFun_le`) with a finite constant
(`Rd.eLpNorm_psi_mul_iSup_psi_ne_top`), and they lie in `L_p` by Young's inequality
(`Rd.memLp_blockFun`, `Rd.eLpNorm_blockFun_zero_le`). The space `F^s_{p,q}` consists of the
`f` with a finite quasi-norm (`Rd.MemTriebelLizorkin`); it is a subspace of `L_p` for
`1 ≤ q ≤ ∞` (`Rd.triebelLizorkinSpace`), increasing in `q` and decreasing in `s`. Setting
terms of the weighted blocks to zero keeps them below the quasi-norm, and for `q < ∞` and
`f ∈ F^s_{p,q}` their tails `‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_{j ≥ N}‖_{ℓ_q} ‖_p` tend to zero
(`Rd.eLpNorm_lqNorm_ite_blockFun_le`, `Rd.tendsto_eLpNorm_lqNorm_blockFun_tail`).

The mixed-norm comparisons of `FunctionSpaces.Analysis.Lp.MixedNorms` give, for every `s ∈ ℝ`,
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖f‖_{F^s_{p,q}} ≤ ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{min(p,q)}}`,
with equality for `q = p` (`Rd.littlewoodPaleyNorm_max_le_triebelLizorkinNorm`,
`Rd.triebelLizorkinNorm_le_littlewoodPaleyNorm_min`,
`Rd.triebelLizorkinNorm_eq_littlewoodPaleyNorm`).
For `s > 0` this gives:

* `F^s_{p,p} = B^s_{p,p}` (`Rd.memTriebelLizorkin_iff_memApprox`), also described by moduli of
  smoothness (`Rd.memTriebelLizorkin_iff_modulus`);
* the **Besov sandwich** `B^s_{p,min(p,q)} ⊆ F^s_{p,q} ⊆ B^s_{p,max(p,q)}`, with explicit finite
  constants (`Rd.approxNormDyadic_le_triebelLizorkinNorm`,
  `Rd.triebelLizorkinNorm_le_approxNormDyadic`,
  `Rd.eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top`, `Rd.memApprox_of_memTriebelLizorkin`,
  `Rd.memTriebelLizorkin_of_memApprox`). For `q = 2`,
  `F^s_{p,2}` lies between `B^s_{p,min(p,2)}` and `B^s_{p,max(p,2)}`.

Besov spaces on `V` are the approximation spaces of the band-limited scheme (`Rd.bandScheme`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Pointwise bounds of convolutions -/

/-- **A bounded function has a finite supremum in `[0, ∞]`**: if the norms `‖K y‖` are bounded
above, then `sup_y ‖K y‖ₑ < ∞` (Mathlib's `ENNReal.iSup_coe_lt_top`). This is the constant `B` of
the pointwise bound of convolutions with a bounded kernel. -/
theorem iSup_enorm_lt_top_of_bddAbove {α E : Type*} [SeminormedAddCommGroup E] {K : α → E}
    (h : BddAbove (Set.range fun y => ‖K y‖)) : (⨆ y, ‖K y‖ₑ) < ∞ := by
  refine ENNReal.iSup_coe_lt_top.2 ?_
  obtain ⟨A, hA⟩ := h
  refine ⟨⟨max A 0, le_max_right _ _⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (le_max_left _ _).trans' (hA ⟨y, rfl⟩)

omit [Fact (1 ≤ p)] in
/-- **Pointwise bound of a convolution with a bounded kernel**: for `1 ≤ p < ∞`, a measurable
kernel `K` with `|K| ≤ B` and a measurable `f`, at every point `x`,
`|(K ⋆ f)(x)| ≤ ‖K‖_1^(1-1/p) B^(1/p) ‖f‖_p`. This is the weighted Jensen inequality with the
weight `|K|`, followed by `|K| ≤ B` and the translation invariance of `‖f‖_p`; it covers `p = 1`,
where the bound is `B ‖f‖_1`. -/
theorem enorm_conv_le_of_enorm_le (hp1 : 1 ≤ p) (hp : p ≠ ∞) {K f : V → ℂ}
    (hK : AEStronglyMeasurable K volume) {B : ℝ≥0∞} (hB : ∀ y, ‖K y‖ₑ ≤ B)
    (hf : AEStronglyMeasurable f volume) (x : V) :
    ‖conv K f volume x‖ₑ ≤
      eLpNorm K 1 volume ^ (1 - 1 / p.toReal) * B ^ (1 / p.toReal) * eLpNorm f p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp1 hp
  have hr0 : 0 < p.toReal := zero_lt_one.trans_le hr
  have h1r : 0 ≤ 1 / p.toReal := one_div_nonneg.2 hr0.le
  have hg : AEMeasurable (fun y => ‖f (x - y)‖ₑ) volume :=
    (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)).eNorm
  have hpow : (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ) ^ p.toReal ≤
      (∫⁻ y, ‖K y‖ₑ) ^ (p.toReal - 1) * (B * eLpNorm f p volume ^ p.toReal) :=
    calc (∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ) ^ p.toReal
        ≤ (∫⁻ y, ‖K y‖ₑ) ^ (p.toReal - 1) * ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ ^ p.toReal :=
          lintegral_mul_rpow_le hr hK.eNorm hg
      _ ≤ (∫⁻ y, ‖K y‖ₑ) ^ (p.toReal - 1) * ∫⁻ y, B * ‖f (x - y)‖ₑ ^ p.toReal := by
          gcongr with y
          exact hB y
      _ = (∫⁻ y, ‖K y‖ₑ) ^ (p.toReal - 1) * (B * eLpNorm f p volume ^ p.toReal) := by
          rw [lintegral_const_mul'' B (hg.pow_const _),
            lintegral_sub_left_eq_self (fun z => ‖f z‖ₑ ^ p.toReal) x,
            eLpNorm_rpow_eq hf hp0 hp]
  calc ‖conv K f volume x‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ := enorm_conv_le_lintegral K f x
    _ = ((∫⁻ y, ‖K y‖ₑ * ‖f (x - y)‖ₑ) ^ p.toReal) ^ (1 / p.toReal) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]
    _ ≤ ((∫⁻ y, ‖K y‖ₑ) ^ (p.toReal - 1) * (B * eLpNorm f p volume ^ p.toReal)) ^
          (1 / p.toReal) := ENNReal.rpow_le_rpow hpow h1r
    _ = eLpNorm K 1 volume ^ (1 - 1 / p.toReal) * B ^ (1 / p.toReal) * eLpNorm f p volume := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1r, ENNReal.mul_rpow_of_nonneg _ _ h1r,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one,
          eLpNorm_one_eq_lintegral_eNorm, ← mul_assoc, sub_mul, one_mul, mul_one_div_cancel hr0.ne']
        exact hK

/-! ### The blocks at every point -/

/-- The **Littlewood–Paley block at every point**, `x ↦ (ψ_j ⋆ f)(x)`, the convolution integral
of the kernel `ψ_j` with a representative of `f ∈ L_p`. Its class in `L_p` is the block
`Rd.lpBlock` (`Rd.lpBlock_ae_eq_blockFun`). -/
noncomputable def blockFun (j : ℕ) (f : Lp ℂ p (volume : Measure V)) : V → ℂ :=
  conv (psi j) f volume

/-- The block `Δ_j f ∈ L_p` is represented by the pointwise convolution `ψ_j ⋆ f`. -/
theorem lpBlock_ae_eq_blockFun (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    lpBlock hp j f =ᵐ[volume] blockFun j f :=
  convLp_apply_ae hp (integrable_psi j) f

omit [Fact (1 ≤ p)] in
/-- The pointwise blocks are measurable. -/
theorem aestronglyMeasurable_blockFun (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    AEStronglyMeasurable (blockFun j f) volume :=
  aestronglyMeasurable_conv (integrable_psi j).aestronglyMeasurable (Lp.aestronglyMeasurable f)

/-- The pointwise blocks `ψ_j ⋆ f` of `f ∈ L_p(V)` lie in `L_p(V)`, for `1 ≤ p ≤ ∞`, by Young's
inequality (`Rd.memLp_conv`). -/
theorem memLp_blockFun (j : ℕ) (f : Lp ℂ p (volume : Measure V)) :
    MemLp (blockFun j f) p volume :=
  memLp_conv Fact.out (integrable_psi j) (Lp.memLp f)

/-- **The first block**: `‖ψ_0 ⋆ f‖_p ≤ ‖Φ‖_1 ‖f‖_p` for `1 ≤ p ≤ ∞`, by Young's inequality,
since `ψ_0 = Φ_0` and `‖Φ_0‖_1 = ‖Φ‖_1`. -/
theorem eLpNorm_blockFun_zero_le (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (blockFun 0 f) p volume ≤ eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ := by
  rw [Lp.eNorm_def, ← eLpNorm_Phi_one 0]
  exact eLpNorm_conv_le Fact.out (integrable_Phi 0).aestronglyMeasurable
    (Lp.aestronglyMeasurable f)

/-- `‖Δ_j f‖_p` is the `L_p` norm of the pointwise block `ψ_j ⋆ f`. -/
theorem enorm_lpBlock_eq_eLpNorm_blockFun (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure V)) : ‖lpBlock hp j f‖ₑ = eLpNorm (blockFun j f) p volume := by
  rw [Lp.eNorm_def]
  exact eLpNorm_congr_ae (lpBlock_ae_eq_blockFun hp j f)

/-- The supremum `sup |ψ_j|` of the Littlewood–Paley kernel `ψ_j` is finite, since `ψ_j` is
bounded (`Rd.bddAbove_psi`). -/
theorem iSup_enorm_psi_lt_top (j : ℕ) : (⨆ y, ‖psi (V := V) j y‖ₑ) < ∞ :=
  iSup_enorm_lt_top_of_bddAbove (bddAbove_psi j)

/-- The constant `‖ψ_j‖_1^(1-1/p) (sup |ψ_j|)^(1/p)` of the pointwise bound of the blocks is
finite for `1 ≤ p < ∞`, since `ψ_j` is integrable (`Rd.integrable_psi`) and bounded
(`Rd.iSup_enorm_psi_lt_top`). -/
theorem eLpNorm_psi_mul_iSup_psi_ne_top (hp : p ≠ ∞) (j : ℕ) :
    eLpNorm (psi (V := V) j) 1 volume ^ (1 - 1 / p.toReal) *
      (⨆ y, ‖psi (V := V) j y‖ₑ) ^ (1 / p.toReal) ≠ ∞ := by
  have hr : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le Fact.out hp
  have h1r : 0 ≤ 1 / p.toReal := one_div_nonneg.2 (zero_le_one.trans hr)
  have h1r' : 0 ≤ 1 - 1 / p.toReal :=
    sub_nonneg.2 ((one_div_le_one_div_of_le zero_lt_one hr).trans_eq one_div_one)
  exact ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg h1r'
      (memLp_one_iff_integrable.2 (integrable_psi j)).eLpNorm_lt_top.ne)
    (ENNReal.rpow_ne_top_of_nonneg h1r (iSup_enorm_psi_lt_top j).ne)

/-- **The blocks are bounded at every point**: for `1 ≤ p < ∞`,
`|(ψ_j ⋆ f)(x)| ≤ ‖ψ_j‖_1^(1-1/p) (sup |ψ_j|)^(1/p) ‖f‖_p`, with a finite constant
(`Rd.eLpNorm_psi_mul_iSup_psi_ne_top`). -/
theorem enorm_blockFun_le (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure V)) (x : V) :
    ‖blockFun j f x‖ₑ ≤ eLpNorm (psi (V := V) j) 1 volume ^ (1 - 1 / p.toReal) *
      (⨆ y, ‖psi (V := V) j y‖ₑ) ^ (1 / p.toReal) * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact enorm_conv_le_of_enorm_le Fact.out hp (integrable_psi j).aestronglyMeasurable
    (fun y => le_iSup (fun y => ‖psi (V := V) j y‖ₑ) y) (Lp.aestronglyMeasurable f) x

/-- The block of a sum is the sum of the blocks, almost everywhere and for all levels at once. -/
theorem blockFun_add_ae (hp : p ≠ ∞) (f g : Lp ℂ p (volume : Measure V)) :
    ∀ᵐ x ∂volume, ∀ j, blockFun j (f + g) x = blockFun j f x + blockFun j g x := by
  rw [ae_all_iff]
  intro j
  have h : blockFun j (f + g) = conv (psi j) (⇑f + ⇑g) volume := conv_congr_ae (Lp.coeFn_add f g)
  rw [h]
  exact conv_add_ae Fact.out hp (integrable_psi j) (Lp.memLp f) (Lp.memLp g)

omit [Fact (1 ≤ p)] in
/-- The block of a complex multiple is the multiple of the block, at every point. -/
theorem blockFun_smul (j : ℕ) (c : ℂ) (f : Lp ℂ p (volume : Measure V)) (x : V) :
    blockFun j (c • f) x = c * blockFun j f x := by
  have h : blockFun j (c • f) = conv (psi j) (c • ⇑f) volume := conv_congr_ae (Lp.coeFn_smul c f)
  rw [h, conv_smul]
  rfl

omit [Fact (1 ≤ p)] in
/-- The blocks of two `L_p` classes with almost everywhere equal representatives agree at every
point, for possibly different exponents (`Rd.conv_congr_ae`). -/
theorem blockFun_eq_of_ae_eq {r : ℝ≥0∞} {f : Lp ℂ p (volume : Measure V)}
    {g : Lp ℂ r (volume : Measure V)} (h : (g : V → ℂ) =ᵐ[volume] f) (j : ℕ) :
    blockFun j g = blockFun j f :=
  conv_congr_ae h

/-! ### The Triebel–Lizorkin quasi-norm -/

/-- The **Triebel–Lizorkin quasi-norm** `‖ x ↦ ‖(2^(js) |ψ_j ⋆ f(x)|)_j‖_{ℓ_q} ‖_p` of
`f ∈ L_p`: the `ℓ_q` norm of the weighted blocks at each point, then the `L_p` norm. The
Littlewood–Paley quasi-norm of the Besov spaces (`Rd.littlewoodPaleyNorm`) takes the two norms in
the other order. For `q = 0` the quasi-norm is `0`; the results assume `1 ≤ q`. -/
noncomputable def triebelLizorkinNorm (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) :
    ℝ≥0∞ :=
  eLpNorm (fun x => lqNorm q (fun j => dyadicWeight s j * ‖blockFun j f x‖ₑ)) p volume

/-- `f ∈ F^s_{p,q}`: the Triebel–Lizorkin quasi-norm of `f` is finite. The space is defined
directly by this quasi-norm, which is why it has a predicate of its own beside the approximation
spaces that describe the Besov spaces. -/
def MemTriebelLizorkin (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) : Prop :=
  triebelLizorkinNorm s q f < ∞

omit [Fact (1 ≤ p)] in
/-- The pointwise `ℓ_q` norm of the weighted blocks is measurable. -/
theorem aemeasurable_lqNorm_blockFun (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) :
    AEMeasurable (fun x => lqNorm q (fun j => dyadicWeight s j * ‖blockFun j f x‖ₑ)) volume :=
  aemeasurable_lqNorm_comp (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _) q

/-- **The quasi-norm is subadditive**: for `1 ≤ q ≤ ∞`,
`‖f + g‖_{F^s_{p,q}} ≤ ‖f‖_{F^s_{p,q}} + ‖g‖_{F^s_{p,q}}`, by the triangle inequalities in
`ℓ_q` at every point and in `L_p`. -/
theorem triebelLizorkinNorm_add_le (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (f g : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm s q (f + g) ≤ triebelLizorkinNorm s q f + triebelLizorkinNorm s q g :=
  eLpNorm_lqNorm_le_add Fact.out hq
    (fun j => (aestronglyMeasurable_blockFun j (f + g)).eNorm.const_mul _) <| by
      filter_upwards [blockFun_add_ae hp f g] with x hx j
      rw [hx j, ← mul_add]
      gcongr
      exact eNorm_add_le _ _

omit [Fact (1 ≤ p)] in
/-- **The quasi-norm is homogeneous**: `‖c f‖_{F^s_{p,q}} = |c| ‖f‖_{F^s_{p,q}}` for `c ∈ ℂ`. -/
theorem triebelLizorkinNorm_smul (s : ℝ) (q : ℝ≥0∞) (c : ℂ) (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm s q (c • f) = ‖c‖ₑ * triebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_eq_const_mul _ (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _)
    (ae_of_all _ fun x j => by rw [blockFun_smul, eNorm_mul, mul_left_comm])

omit [Fact (1 ≤ p)] in
/-- The zero function has quasi-norm `0`. -/
theorem triebelLizorkinNorm_zero (s : ℝ) (q : ℝ≥0∞) :
    triebelLizorkinNorm s q (0 : Lp ℂ p (volume : Measure V)) = 0 := by
  simpa using triebelLizorkinNorm_smul s q (0 : ℂ) (0 : Lp ℂ p (volume : Measure V))

omit [Fact (1 ≤ p)] in
/-- **Smoothness `0`**: `‖f‖_{F^0_{p,q}} = ‖ x ↦ ‖((ψ_j ⋆ f)(x))_j‖_{ℓ_q} ‖_p` for every `q`,
since the weights `2^(j·0)` are `1`. -/
theorem triebelLizorkinNorm_zero_left (q : ℝ≥0∞) (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm 0 q f =
      eLpNorm (fun x => lqNorm q fun j => ‖blockFun j f x‖ₑ) p volume :=
  eLpNorm_lqNorm_dyadicWeight_zero_left _

omit [Fact (1 ≤ p)] in
/-- **The quasi-norm decreases in `q`**: `‖f‖_{F^s_{p,r}} ≤ ‖f‖_{F^s_{p,q}}` for
`1 ≤ q ≤ r ≤ ∞`, since `‖·‖_{ℓ_r} ≤ ‖·‖_{ℓ_q}` at every point. -/
theorem triebelLizorkinNorm_mono_exponent {s : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    (f : Lp ℂ p (volume : Measure V)) : triebelLizorkinNorm s r f ≤ triebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_mono_exponent (zero_lt_one.trans_le hq).ne' hqr fun j =>
    (aestronglyMeasurable_blockFun j f).eNorm.const_mul _

omit [Fact (1 ≤ p)] in
/-- **The quasi-norm increases in `s`**: `‖f‖_{F^s_{p,q}} ≤ ‖f‖_{F^t_{p,q}}` for `s ≤ t`, since
`2^(js) ≤ 2^(jt)`. -/
theorem triebelLizorkinNorm_mono_smoothness {s t : ℝ} (hst : s ≤ t) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) : triebelLizorkinNorm s q f ≤ triebelLizorkinNorm t q f :=
  eLpNorm_lqNorm_dyadicWeight_mono_smoothness hst fun j =>
    (aestronglyMeasurable_blockFun j f).eNorm

omit [Fact (1 ≤ p)] in
/-- **Weighted blocks with terms set to zero**: for every predicate `P` on `ℕ`,
`‖ x ↦ ‖(1_P(j) 2^{js} |(ψ_j ⋆ f)(x)|)_j‖_{ℓ_q} ‖_p ≤ ‖f‖_{F^s_{p,q}}`, where the terms with `P j`
false are `0` (`MeasureTheory.eLpNorm_lqNorm_ite_le`). -/
theorem eLpNorm_lqNorm_ite_blockFun_le {P : ℕ → Prop} [DecidablePred P] (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    eLpNorm (fun x => lqNorm q fun j =>
      if P j then dyadicWeight s j * ‖blockFun j f x‖ₑ else 0) p volume ≤
      triebelLizorkinNorm s q f :=
  eLpNorm_lqNorm_ite_le fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _

open Filter Topology in
/-- **The tails of the weighted blocks tend to zero**: for `1 ≤ p < ∞`, `0 < q < ∞`, `s ∈ ℝ` and
`f ∈ F^s_{p,q}(V)`, `‖ x ↦ ‖(2^{js} (ψ_j ⋆ f)(x))_{j ≥ N}‖_{ℓ_q} ‖_p → 0` as `N → ∞`, where the
terms `j < N` are `0` (`MeasureTheory.tendsto_eLpNorm_lqNorm_ite_le`). -/
theorem tendsto_eLpNorm_lqNorm_blockFun_tail (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin s q f) :
    Tendsto (fun N => eLpNorm (fun x => lqNorm q fun j =>
      if N ≤ j then dyadicWeight s j * ‖blockFun j f x‖ₑ else 0) p volume) atTop (𝓝 0) :=
  tendsto_eLpNorm_lqNorm_ite_le (zero_lt_one.trans_le Fact.out).ne' hp hq0 hq
    (fun j => (aestronglyMeasurable_blockFun j f).eNorm.const_mul _) hf.ne

/-! ### The spaces `F^s_{p,q}` -/

omit [Fact (1 ≤ p)] in
/-- **`F^s_{p,q}` increases in `q`**: `F^s_{p,q} ⊆ F^s_{p,r}` for `1 ≤ q ≤ r ≤ ∞`. -/
theorem MemTriebelLizorkin.mono_exponent {s : ℝ} {q r : ℝ≥0∞} (hq : 1 ≤ q) (hqr : q ≤ r)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin s q f) :
    MemTriebelLizorkin s r f :=
  (triebelLizorkinNorm_mono_exponent hq hqr f).trans_lt hf

omit [Fact (1 ≤ p)] in
/-- **`F^s_{p,q}` decreases in `s`**: `F^t_{p,q} ⊆ F^s_{p,q}` for `s ≤ t`. -/
theorem MemTriebelLizorkin.mono_smoothness {s t : ℝ} (hst : s ≤ t) {q : ℝ≥0∞}
    {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin t q f) :
    MemTriebelLizorkin s q f :=
  (triebelLizorkinNorm_mono_smoothness hst q f).trans_lt hf

/-- `F^s_{p,q}` is closed under addition, for `1 ≤ q ≤ ∞`. -/
theorem MemTriebelLizorkin.add (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f g : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin s q f)
    (hg : MemTriebelLizorkin s q g) : MemTriebelLizorkin s q (f + g) :=
  (triebelLizorkinNorm_add_le hp hq f g).trans_lt (ENNReal.add_lt_top.2 ⟨hf, hg⟩)

omit [Fact (1 ≤ p)] in
/-- `F^s_{p,q}` is closed under complex multiples. -/
theorem MemTriebelLizorkin.smul {s : ℝ} {q : ℝ≥0∞} (c : ℂ) {f : Lp ℂ p (volume : Measure V)}
    (hf : MemTriebelLizorkin s q f) : MemTriebelLizorkin s q (c • f) := by
  rw [MemTriebelLizorkin, triebelLizorkinNorm_smul]
  exact ENNReal.mul_lt_top eNorm_lt_top hf

/-- The **Triebel–Lizorkin space** `F^s_{p,q}` as a subspace of `L_p`, for `1 ≤ p < ∞`, `s ∈ ℝ`
and `1 ≤ q ≤ ∞`, with real scalars as `FunctionScheme.besovSpace`. -/
noncomputable def triebelLizorkinSpace (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    Submodule ℝ (Lp ℂ p (volume : Measure V)) where
  carrier := {f | MemTriebelLizorkin s q f}
  add_mem' hf hg := hf.add hp hq hg
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, MemTriebelLizorkin, triebelLizorkinNorm_zero]
    exact ENNReal.zero_lt_top
  smul_mem' r f hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r f]
    exact hf.smul _

/-- Membership in the subspace `F^s_{p,q}` is a finite Triebel–Lizorkin quasi-norm. -/
theorem mem_triebelLizorkinSpace (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    f ∈ triebelLizorkinSpace hp s q hq ↔ MemTriebelLizorkin s q f :=
  Iff.rfl

/-! ### Comparison with the Besov spaces -/

/-- The Littlewood–Paley quasi-norm of the Besov spaces in terms of the pointwise blocks:
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_q} = ‖(2^(js) ‖ψ_j ⋆ f‖_p)_j‖_{ℓ_q}`. -/
theorem littlewoodPaleyNorm_eq_lqNorm_eLpNorm (hp : p ≠ ∞) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    littlewoodPaleyNorm hp s q f =
      lqNorm q (fun j => dyadicWeight s j * eLpNorm (blockFun j f) p volume) := by
  simp only [littlewoodPaleyNorm, enorm_lpBlock_eq_eLpNorm_blockFun hp]

/-- **For `q = p` the two quasi-norms agree**: for every `s ∈ ℝ`,
`‖f‖_{F^s_{p,p}} = ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_p}`, by Tonelli's theorem (`L_p(ℓ_p) = ℓ_p(L_p)`). -/
theorem triebelLizorkinNorm_eq_littlewoodPaleyNorm (hp : p ≠ ∞) (s : ℝ)
    (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm s p f = littlewoodPaleyNorm hp s p f := by
  rw [littlewoodPaleyNorm_eq_lqNorm_eLpNorm]
  exact eLpNorm_lqNorm_dyadicWeight_eq (zero_lt_one.trans_le Fact.out).ne' hp
    fun j => aestronglyMeasurable_blockFun j f

/-- **`F^s_{p,p} = B^s_{p,p}`**: for `1 ≤ p < ∞` and `s > 0`, `f ∈ F^s_{p,p}` iff `f` lies in the
approximation space `A^s_p` of the band-limited scheme, the Besov space `B^s_{p,p}`. -/
theorem memTriebelLizorkin_iff_memApprox (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s)
    {f : Lp ℂ p (volume : Measure V)} :
    MemTriebelLizorkin s p f ↔ (bandScheme hp).MemApprox s p f := by
  rw [memApprox_bandScheme_iff hp hs Fact.out, MemTriebelLizorkin,
    triebelLizorkinNorm_eq_littlewoodPaleyNorm hp]

/-- **The lower bound of the Triebel–Lizorkin quasi-norm**, behind `F^s_{p,q} ⊆ B^s_{p,max(p,q)}`:
for `1 ≤ p < ∞`, `s ∈ ℝ` and `1 ≤ q ≤ ∞`,
`‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{max(p,q)}} ≤ ‖f‖_{F^s_{p,q}}`. For `q = 2`: the Littlewood–Paley
quasi-norm of `B^s_{p,max(p,2)}` is at most the quasi-norm of `F^s_{p,2}`. -/
theorem littlewoodPaleyNorm_max_le_triebelLizorkinNorm (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    littlewoodPaleyNorm hp s (max p q) f ≤ triebelLizorkinNorm s q f := by
  rw [littlewoodPaleyNorm_eq_lqNorm_eLpNorm]
  exact lqNorm_max_dyadicWeight_le Fact.out hp hq fun j => aestronglyMeasurable_blockFun j f

/-- **The upper bound of the Triebel–Lizorkin quasi-norm**, behind `B^s_{p,min(p,q)} ⊆ F^s_{p,q}`:
for `1 ≤ p < ∞`, `s ∈ ℝ` and `1 ≤ q ≤ ∞`,
`‖f‖_{F^s_{p,q}} ≤ ‖(2^(js) ‖Δ_j f‖_p)_j‖_{ℓ_{min(p,q)}}`. For `q = 2`: the quasi-norm of
`F^s_{p,2}` is at most the Littlewood–Paley quasi-norm of `B^s_{p,min(p,2)}`. -/
theorem triebelLizorkinNorm_le_littlewoodPaleyNorm_min (hp : p ≠ ∞) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm s q f ≤ littlewoodPaleyNorm hp s (min p q) f := by
  rw [littlewoodPaleyNorm_eq_lqNorm_eLpNorm]
  exact eLpNorm_lqNorm_dyadicWeight_le_min Fact.out hp hq fun j => aestronglyMeasurable_blockFun j f

/-- **`F^s_{p,q} ⊆ B^s_{p,max(p,q)}` with a constant**: for `1 ≤ p < ∞`, `s > 0` and
`1 ≤ q ≤ ∞`, the approximation norm of `f` in `A^s_{max(p,q)}` of the band-limited scheme is at
most `2 (1 - 2^(-s))⁻¹ ‖f‖_{F^s_{p,q}}`. -/
theorem approxNormDyadic_le_triebelLizorkinNorm (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).approxNormDyadic s (max p q) f ≤
      2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ * triebelLizorkinNorm s q f :=
  (approxNormDyadic_bandScheme_le hp hs (le_max_of_le_right hq) f).trans
    (by gcongr; exact littlewoodPaleyNorm_max_le_triebelLizorkinNorm hp hq f)

/-- **`B^s_{p,min(p,q)} ⊆ F^s_{p,q}` with a constant**: for `1 ≤ p < ∞`, `s ≥ 0` and
`1 ≤ q ≤ ∞`, `‖f‖_{F^s_{p,q}} ≤ 8 · 2^(3s) ‖Φ‖_1` times the approximation norm of `f` in
`A^s_{min(p,q)}` of the band-limited scheme. -/
theorem triebelLizorkinNorm_le_approxNormDyadic (hp : p ≠ ∞) {s : ℝ} (hs : 0 ≤ s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    triebelLizorkinNorm s q f ≤
      8 * dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume *
        (bandScheme hp).approxNormDyadic s (min p q) f :=
  (triebelLizorkinNorm_le_littlewoodPaleyNorm_min hp hq f).trans
    (littlewoodPaleyNorm_le_approxNormDyadic hp hs (le_min Fact.out hq) f)

/-- The constant `8 · 2^{3s} ‖Φ‖_1` of `Rd.triebelLizorkinNorm_le_approxNormDyadic` is finite. -/
theorem eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top (s : ℝ) :
    8 * dyadicWeight s 3 * eLpNorm (lpKernel (V := V)) 1 volume ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.dyadicWeight_ne_top _ _))
    eLpNorm_lpKernel_ne_top

/-- **`F^s_{p,q} ⊆ B^s_{p,max(p,q)}`**: for `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, every
`f ∈ F^s_{p,q}` lies in the approximation space `A^s_{max(p,q)}` of the band-limited scheme. For
`q = 2`: `F^s_{p,2} ⊆ B^s_{p,max(p,2)}`. -/
theorem memApprox_of_memTriebelLizorkin (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} (hf : MemTriebelLizorkin s q f) :
    (bandScheme hp).MemApprox s (max p q) f :=
  (memApprox_bandScheme_iff hp hs (le_max_of_le_right hq)).2
    ((littlewoodPaleyNorm_max_le_triebelLizorkinNorm hp hq f).trans_lt hf)

/-- **`B^s_{p,min(p,q)} ⊆ F^s_{p,q}`**: for `1 ≤ p < ∞`, `s > 0` and `1 ≤ q ≤ ∞`, every `f` in
the approximation space `A^s_{min(p,q)}` of the band-limited scheme lies in `F^s_{p,q}`. For
`q = 2`: `B^s_{p,min(p,2)} ⊆ F^s_{p,2}`. -/
theorem memTriebelLizorkin_of_memApprox (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)}
    (hf : (bandScheme hp).MemApprox s (min p q) f) : MemTriebelLizorkin s q f :=
  (triebelLizorkinNorm_le_littlewoodPaleyNorm_min hp hq f).trans_lt
    ((memApprox_bandScheme_iff hp hs (le_min Fact.out hq)).1 hf)

/-- **`F^s_{p,p}` by differences**: for `1 ≤ p < ∞` and `0 < s < r`, `f ∈ F^s_{p,p}` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_p} < ∞`. -/
theorem memTriebelLizorkin_iff_modulus (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s) (hsr : s < r)
    (f : Lp ℂ p (volume : Measure V)) :
    MemTriebelLizorkin s p f ↔
      ‖f‖ₑ + lqNorm p (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ := by
  rw [MemTriebelLizorkin, triebelLizorkinNorm_eq_littlewoodPaleyNorm hp]
  exact littlewoodPaleyNorm_lt_top_iff_modulus hp hs hsr Fact.out f

end Rd
