/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevEmbedding

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The critical Sobolev embedding

Let `V` have dimension `n ≥ 1`, `1 ≤ p₀ < p₁ < ∞`, `θ = p₀/p₁` and
`α = n(1/p₀ - 1/p₁)` (`nikolskiiExponent`). This file proves the critical embedding
`F^α_{p₀,∞} ↪ L_{p₁}` directly from the Littlewood–Paley blocks `ψ_j ⋆ f` (`Rd.blockFun`),
following Johnsen–Sickel (2007, Proposition 1):

* **the Nikolskii inequality in supremum form** (`Rd.iSup_dyadicWeight_enorm_blockFun_le`):
  `sup_j 2^(j(s - n/p₀)) |(ψ_j ⋆ f)(x)| ≤ N_{p₀} ‖(2^(js) ‖ψ_j ⋆ f‖_{p₀})_j‖_{ℓ_∞}` at every `x`;
* **the pointwise bound** (`Rd.tsum_dyadicWeight_enorm_blockFun_le`): for `s₀ - s₁ = α`,
  the interpolation inequality for dyadic suprema (`ENNReal.tsum_dyadicWeight_mul_le_iSup`) gives
  `∑_j 2^(js₁) |(ψ_j ⋆ f)(x)| ≤ c G(x)^θ (N_{p₀} ‖f‖_{B^{s₀}_{p₀,∞}})^(1-θ)` with
  `G(x) = sup_j 2^(js₀) |(ψ_j ⋆ f)(x)|`;
* **integration** (`Rd.eLpNorm_tsum_dyadicWeight_enorm_blockFun_le`): since `‖G^θ‖_{p₁} =
  ‖G‖_{p₀}^θ = ‖f‖_{F^{s₀}_{p₀,∞}}^θ`, the `L_{p₁}` norm of the left side is at most
  `K ‖f‖_{F^{s₀}_{p₀,∞}}` with `K = Rd.criticalEmbeddingConst V p₀ p₁`;
* **`F^α_{p₀,∞} ↪ L_{p₁}`** (`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`,
  `Rd.exists_memLp_ae_eq_of_memTriebelLizorkin`), for `p₀ = 1` as well, and
  `F^s_{p₀,q} ↪ L_{p₁}` for `p₀ ≤ p₁` and `s ≥ α`
  (`Rd.exists_memLp_ae_eq_of_memTriebelLizorkin_of_le`);
* **Jawerth's embedding** `F^{s₀}_{p₀,∞} ↪ F^{s₁}_{p₁,q}` for `s₁ ≥ 0`, `s₀ - s₁ = α` and every
  `1 ≤ q ≤ ∞` (`Rd.exists_triebelLizorkinNorm_le_of_nikolskiiExponent`);
* **the critical Sobolev embedding** `W^m_p ↪ L_r` for `1 < p < ∞`, `r < ∞` and
  `m = n(1/p - 1/r)` with named constants (`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_of_eq`,
  `Rd.exists_memLp_ae_eq_of_memSobolev_of_eq`), and `W^m_p ↪ L_r` for every `p ≤ r < ∞` with
  `n(1/p - 1/r) ≤ m` (`Rd.exists_memLp_ae_eq_of_memSobolev_of_le`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight dyadicInterpConst)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)]

/-! ### The pointwise bound -/

/-- **The Nikolskii inequality in supremum form**: for `1 ≤ p₀ < ∞`, `s ∈ ℝ`, `f ∈ L_{p₀}(V)` and
every `x`,
`sup_j 2^(j(s - n/p₀)) |(ψ_j ⋆ f)(x)| ≤ N_{p₀} ‖(2^(js) ‖ψ_j ⋆ f‖_{p₀})_j‖_{ℓ_∞}`. Each term is
at most `N_{p₀} 2^(js) ‖ψ_j ⋆ f‖_{p₀}` by the Nikolskii inequality for blocks
(`Rd.enorm_blockFun_le_nikolskii`). -/
theorem iSup_dyadicWeight_enorm_blockFun_le (hp₀ : p₀ ≠ ∞) (s : ℝ)
    (f : Lp ℂ p₀ (volume : Measure V)) (x : V) :
    ⨆ j, dyadicWeight (s - (finrank ℝ V : ℝ) / p₀.toReal) j * ‖blockFun j f x‖ₑ ≤
      nikolskiiBlockConst V p₀ * littlewoodPaleyNorm hp₀ s ∞ f := by
  rw [littlewoodPaleyNorm_eq_lqNorm_eLpNorm, ENNReal.lqNorm_top, ENNReal.mul_iSup]
  refine iSup_le fun j => le_iSup_of_le j ?_
  calc dyadicWeight (s - (finrank ℝ V : ℝ) / p₀.toReal) j * ‖blockFun j f x‖ₑ
      ≤ dyadicWeight (s - (finrank ℝ V : ℝ) / p₀.toReal) j * (nikolskiiBlockConst V p₀ *
          dyadicWeight (nikolskiiExponent (finrank ℝ V) p₀ ∞) j *
          eLpNorm (blockFun j f) p₀ volume) :=
        mul_le_mul' le_rfl (enorm_blockFun_le_nikolskii hp₀ j f x)
    _ = nikolskiiBlockConst V p₀ * (dyadicWeight s j * eLpNorm (blockFun j f) p₀ volume) := by
        rw [nikolskiiExponent_top, ← div_eq_mul_inv]
        conv_rhs => rw [← sub_add_cancel s ((finrank ℝ V : ℝ) / p₀.toReal),
          ENNReal.dyadicWeight_add]
        ring

/-- **The pointwise bound of the weighted blocks** (Johnsen–Sickel 2007, (8)–(9)): let `n ≥ 1`,
`1 ≤ p₀ < p₁ < ∞`, `θ = p₀/p₁` and `s₀ - s₁ = n(1/p₀ - 1/p₁)`. For `f ∈ L_{p₀}(V)` and every `x`,

`∑_j 2^(js₁) |(ψ_j ⋆ f)(x)| ≤ c(n/p₀, θ) G(x)^θ (N_{p₀} ‖(2^(js₀) ‖ψ_j ⋆ f‖_{p₀})_j‖_{ℓ_∞})^(1-θ)`

with `G(x) = sup_j 2^(js₀) |(ψ_j ⋆ f)(x)|`: the interpolation inequality for dyadic suprema
(`ENNReal.tsum_dyadicWeight_mul_le_iSup`) with `σ₀ = s₀`, `σ₁ = s₀ - n/p₀`, and the Nikolskii
inequality in supremum form (`Rd.iSup_dyadicWeight_enorm_blockFun_le`). -/
theorem tsum_dyadicWeight_enorm_blockFun_le [Nontrivial V] (hp₀ : p₀ ≠ ∞) (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≠ ∞) {s₀ s₁ : ℝ} (hs : s₀ - s₁ = nikolskiiExponent (finrank ℝ V) p₀ p₁)
    (f : Lp ℂ p₀ (volume : Measure V)) (x : V) :
    ∑' j, dyadicWeight s₁ j * ‖blockFun j f x‖ₑ ≤
      dyadicInterpConst ((finrank ℝ V : ℝ) / p₀.toReal) (p₀.toReal / p₁.toReal) *
        (lqNorm ∞ fun j => dyadicWeight s₀ j * ‖blockFun j f x‖ₑ) ^ (p₀.toReal / p₁.toReal) *
        (nikolskiiBlockConst V p₀ * littlewoodPaleyNorm hp₀ s₀ ∞ f) ^
          (1 - p₀.toReal / p₁.toReal) := by
  obtain ⟨hθ0, hθ1⟩ := ENNReal.toReal_div_toReal_mem_Ioo Fact.out hp₀₁ hp₁
  have hp₀0 : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hn : 0 < (finrank ℝ V : ℝ) / p₀.toReal :=
    div_pos (Nat.cast_pos.2 finrank_pos) (ENNReal.toReal_pos hp₀0 hp₀)
  have h := ENNReal.tsum_dyadicWeight_mul_le_iSup (σ₀ := s₀)
    (σ₁ := s₀ - (finrank ℝ V : ℝ) / p₀.toReal) (by linarith) hθ0 hθ1
    (fun j => ‖blockFun j f x‖ₑ)
  rw [nikolskiiExponent_interp_eq hp₀0 hp₀ hs, sub_sub_cancel] at h
  rw [ENNReal.lqNorm_top]
  exact h.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (iSup_dyadicWeight_enorm_blockFun_le hp₀ s₀ f x) (sub_nonneg.2 hθ1.le)))

/-! ### Integration -/

variable (V) in
/-- The **constant of the critical embedding**,
`K_{V,p₀,p₁} = c(n/p₀, θ) N_{p₀}^(1-θ)` with `θ = p₀/p₁`, the constant
`ENNReal.dyadicInterpConst` of the interpolation inequality for dyadic suprema and the Nikolskii
constant `Rd.nikolskiiBlockConst` of the blocks. -/
noncomputable def criticalEmbeddingConst (p₀ p₁ : ℝ≥0∞) : ℝ≥0∞ :=
  dyadicInterpConst ((finrank ℝ V : ℝ) / p₀.toReal) (p₀.toReal / p₁.toReal) *
    nikolskiiBlockConst V p₀ ^ (1 - p₀.toReal / p₁.toReal)

/-- The constant of the critical embedding is finite for `n ≥ 1` and `1 ≤ p₀ < p₁ < ∞`. -/
theorem criticalEmbeddingConst_ne_top [Nontrivial V] (hp₀₁ : p₀ < p₁) (hp₁ : p₁ ≠ ∞) :
    criticalEmbeddingConst V p₀ p₁ ≠ ∞ := by
  obtain ⟨hθ0, hθ1⟩ := ENNReal.toReal_div_toReal_mem_Ioo Fact.out hp₀₁ hp₁
  have hn : 0 < (finrank ℝ V : ℝ) / p₀.toReal := div_pos (Nat.cast_pos.2 finrank_pos)
    (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne' (hp₀₁.trans_le le_top).ne)
  exact ENNReal.mul_ne_top (ENNReal.dyadicInterpConst_ne_top hn hθ0 hθ1)
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hθ1.le) nikolskiiBlockConst_ne_top)

omit [Fact (1 ≤ p₀)] in
/-- **The `L_{p₁}` norm of `G^θ`** for `θ = p₀/p₁`: with
`G(x) = sup_j 2^(js) |(ψ_j ⋆ f)(x)|`, `‖G^θ‖_{p₁} = ‖G‖_{p₀}^θ = ‖f‖_{F^s_{p₀,∞}}^θ` for
`0 < p₀ < ∞` and `0 < p₁ < ∞` (`MeasureTheory.eLpNorm_fun_rpow`). -/
theorem eLpNorm_rpow_lqNorm_blockFun_eq (hp₀0 : p₀ ≠ 0) (hp₀ : p₀ ≠ ∞) (hp₁0 : p₁ ≠ 0)
    (hp₁ : p₁ ≠ ∞) (s : ℝ) (f : Lp ℂ p₀ (volume : Measure V)) :
    eLpNorm (fun x => (lqNorm ∞ fun j => dyadicWeight s j * ‖blockFun j f x‖ₑ) ^
      (p₀.toReal / p₁.toReal)) p₁ volume =
      triebelLizorkinNorm s ∞ f ^ (p₀.toReal / p₁.toReal) := by
  have hθ : 0 < p₀.toReal / p₁.toReal :=
    div_pos (ENNReal.toReal_pos hp₀0 hp₀) (ENNReal.toReal_pos hp₁0 hp₁)
  rw [eLpNorm_fun_rpow (aemeasurable_lqNorm_blockFun s ∞ f) hθ p₁,
    ENNReal.mul_ofReal_toReal_div_toReal hp₀ hp₁0 hp₁]
  rfl

/-- **The integrated bound** (Johnsen–Sickel 2007, (10)): let `n ≥ 1`, `1 ≤ p₀ < p₁ < ∞` and
`s₀ - s₁ = n(1/p₀ - 1/p₁)`. For every `f ∈ L_{p₀}(V)`,

`‖x ↦ ∑_j 2^(js₁) |(ψ_j ⋆ f)(x)|‖_{p₁} ≤ K_{V,p₀,p₁} ‖f‖_{F^{s₀}_{p₀,∞}}`.

The pointwise bound (`Rd.tsum_dyadicWeight_enorm_blockFun_le`) is
`c G(x)^θ (N_{p₀} A)^(1-θ)` with `A = ‖(2^(js₀) ‖ψ_j ⋆ f‖_{p₀})_j‖_{ℓ_∞}`; its `L_{p₁}` norm is
`c N_{p₀}^(1-θ) A^(1-θ) ‖f‖_{F^{s₀}_{p₀,∞}}^θ` (`Rd.eLpNorm_rpow_lqNorm_blockFun_eq`), and
`A ≤ ‖f‖_{F^{s₀}_{p₀,∞}}` (`Rd.littlewoodPaleyNorm_max_le_triebelLizorkinNorm`). -/
theorem eLpNorm_tsum_dyadicWeight_enorm_blockFun_le [Nontrivial V] (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≠ ∞) {s₀ s₁ : ℝ} (hs : s₀ - s₁ = nikolskiiExponent (finrank ℝ V) p₀ p₁)
    (f : Lp ℂ p₀ (volume : Measure V)) :
    eLpNorm (fun x => ∑' j, dyadicWeight s₁ j * ‖blockFun j f x‖ₑ) p₁ volume ≤
      criticalEmbeddingConst V p₀ p₁ * triebelLizorkinNorm s₀ ∞ f := by
  have hp₀ : p₀ ≠ ∞ := hp₀₁.ne_top
  obtain ⟨hθ0, hθ1⟩ := ENNReal.toReal_div_toReal_mem_Ioo Fact.out hp₀₁ hp₁
  have hp₀0 : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁0 : p₁ ≠ 0 := (zero_lt_one.trans_le ((Fact.out : 1 ≤ p₀).trans hp₀₁.le)).ne'
  set θ := p₀.toReal / p₁.toReal
  set K := dyadicInterpConst ((finrank ℝ V : ℝ) / p₀.toReal) θ
  set B := nikolskiiBlockConst V p₀ * littlewoodPaleyNorm hp₀ s₀ ∞ f
  set T := triebelLizorkinNorm s₀ ∞ f
  have hmeas : AEStronglyMeasurable (fun x => ∑' j, dyadicWeight s₁ j * ‖blockFun j f x‖ₑ)
      volume := (AEMeasurable.tsum fun j =>
        (aestronglyMeasurable_blockFun j f).eNorm.const_mul _).aestronglyMeasurable
  have hB : littlewoodPaleyNorm hp₀ s₀ ∞ f ≤ T := by
    simpa using littlewoodPaleyNorm_max_le_triebelLizorkinNorm hp₀ (s := s₀) le_top f
  calc eLpNorm (fun x => ∑' j, dyadicWeight s₁ j * ‖blockFun j f x‖ₑ) p₁ volume
      ≤ eLpNorm (fun x => K * B ^ (1 - θ) *
          (lqNorm ∞ fun j => dyadicWeight s₀ j * ‖blockFun j f x‖ₑ) ^ θ) p₁ volume :=
        eLpNorm_mono_eNorm hmeas fun x => by
          simp only [eNorm_eq_self]
          refine (tsum_dyadicWeight_enorm_blockFun_le hp₀ hp₀₁ hp₁ hs f x).trans_eq ?_
          ring
    _ = K * B ^ (1 - θ) * T ^ θ := by
        rw [eLpNorm_const_mul_ennreal
            ((aemeasurable_lqNorm_blockFun s₀ ∞ f).pow_const θ).aestronglyMeasurable,
          eLpNorm_rpow_lqNorm_blockFun_eq hp₀0 hp₀ hp₁0 hp₁]
    _ ≤ K * (nikolskiiBlockConst V p₀ ^ (1 - θ) * T ^ (1 - θ)) * T ^ θ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.2 hθ1.le)]
        exact mul_le_mul' (mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (ENNReal.rpow_le_rpow hB (sub_nonneg.2 hθ1.le)))) le_rfl
    _ = criticalEmbeddingConst V p₀ p₁ * T := by
        rw [criticalEmbeddingConst, mul_assoc, mul_assoc, mul_assoc, mul_comm (T ^ (1 - θ)),
          ENNReal.rpow_mul_rpow_one_sub _ hθ0.le hθ1.le]

/-! ### The embeddings -/

/-- **`F^α_{p₀,∞} ↪ L_{p₁}` with a named constant** (Jawerth 1977; the proof is Johnsen–Sickel's):
let `n ≥ 1`, `1 ≤ p₀ < p₁ < ∞` and `s = α = n(1/p₀ - 1/p₁)`. Every `f ∈ L_{p₀}(V)` with a finite
quasi-norm in `F^s_{p₀,∞}` has a representative `g ∈ L_{p₁}(V)` with
`‖g‖_{p₁} ≤ K_{V,p₀,p₁} ‖f‖_{F^s_{p₀,∞}}`. Since `s > 0`, the series of the blocks converges
almost everywhere to `f` (`Rd.ae_hasSum_blockFun`), so `|f| ≤ ∑_j |ψ_j ⋆ f|` almost everywhere,
and the integrated bound with `s₁ = 0` (`Rd.eLpNorm_tsum_dyadicWeight_enorm_blockFun_le`)
applies. This covers `p₀ = 1`. -/
theorem exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top [Nontrivial V] (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≠ ∞) {s : ℝ} (hs : nikolskiiExponent (finrank ℝ V) p₀ p₁ = s)
    {f : Lp ℂ p₀ (volume : Measure V)} (hf : triebelLizorkinNorm s ∞ f < ∞) :
    ∃ g : Lp ℂ p₁ (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f ∧
      ‖g‖ₑ ≤ criticalEmbeddingConst V p₀ p₁ * triebelLizorkinNorm s ∞ f := by
  have hp₀ : p₀ ≠ ∞ := hp₀₁.ne_top
  have : Fact (1 ≤ p₁) := ⟨(Fact.out : 1 ≤ p₀).trans hp₀₁.le⟩
  have hs0 : 0 < s := hs ▸ nikolskiiExponent_pos (Nat.cast_pos.2 finrank_pos) Fact.out hp₀₁
  have hLP : littlewoodPaleyNorm hp₀ s ∞ f < ∞ := by
    refine lt_of_le_of_lt ?_ hf
    simpa using littlewoodPaleyNorm_max_le_triebelLizorkinNorm hp₀ (s := s) le_top f
  have hae : ∀ᵐ x ∂volume, ‖f x‖ₑ ≤ ‖∑' j, dyadicWeight 0 j * ‖blockFun j f x‖ₑ‖ₑ := by
    filter_upwards [ae_hasSum_blockFun hp₀ hs0 le_top hLP] with x hx
    simp only [ENNReal.dyadicWeight_zero_left, one_mul, eNorm_eq_self]
    rw [← hx.tsum_eq]
    exact eNorm_tsum_le_tsum_eNorm
  have hbound : eLpNorm f p₁ volume ≤ criticalEmbeddingConst V p₀ p₁ * triebelLizorkinNorm s ∞ f :=
    (eLpNorm_mono_eNorm_ae (Lp.aestronglyMeasurable f) hae).trans
      (eLpNorm_tsum_dyadicWeight_enorm_blockFun_le hp₀₁ hp₁ (by rw [sub_zero, hs]) f)
  have hmem : MemLp f p₁ volume := memLp_iff.2 (hbound.trans_lt
    (ENNReal.mul_lt_top (criticalEmbeddingConst_ne_top hp₀₁ hp₁).lt_top hf))
  exact ⟨hmem.toLp f, hmem.coeFn_toLp, by rw [Lp.eNorm_toLp]; exact hbound⟩

/-- **`F^α_{p₀,q} ↪ L_{p₁}` for every `q`**: under the hypotheses of
`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`, every `f ∈ F^α_{p₀,q}`, `1 ≤ q ≤ ∞`, has a
representative `g ∈ L_{p₁}(V)` with `‖g‖_{p₁} ≤ K_{V,p₀,p₁} ‖f‖_{F^α_{p₀,q}}`, since
`‖f‖_{F^α_{p₀,∞}} ≤ ‖f‖_{F^α_{p₀,q}}` (`Rd.triebelLizorkinNorm_mono_exponent`). -/
theorem exists_memLp_ae_eq_of_memTriebelLizorkin [Nontrivial V] (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≠ ∞) {s : ℝ} (hs : nikolskiiExponent (finrank ℝ V) p₀ p₁ = s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p₀ (volume : Measure V)} (hf : MemTriebelLizorkin s q f) :
    ∃ g : Lp ℂ p₁ (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f ∧
      ‖g‖ₑ ≤ criticalEmbeddingConst V p₀ p₁ * triebelLizorkinNorm s q f := by
  have hle := triebelLizorkinNorm_mono_exponent (s := s) hq le_top f
  obtain ⟨g, hg, hn⟩ := exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top hp₀₁ hp₁ hs
    (hle.trans_lt hf)
  exact ⟨g, hg, hn.trans (mul_le_mul' le_rfl hle)⟩

/-- **`F^s_{p₀,q} ↪ L_{p₁}` for `p₀ ≤ p₁ < ∞`**: let `n ≥ 1`, `1 ≤ p₀ ≤ p₁ < ∞`, `1 ≤ q ≤ ∞` and
`n(1/p₀ - 1/p₁) ≤ s`. Every `f ∈ F^s_{p₀,q}(V)` has a representative in `L_{p₁}(V)`: for
`p₁ = p₀` this is `f` itself; for `p₀ < p₁`, `F^s_{p₀,q} ⊆ F^α_{p₀,∞}` with
`α = n(1/p₀ - 1/p₁)` (`Rd.triebelLizorkinNorm_mono_exponent`,
`Rd.MemTriebelLizorkin.mono_smoothness`) and `F^α_{p₀,∞} ↪ L_{p₁}`
(`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`). -/
theorem exists_memLp_ae_eq_of_memTriebelLizorkin_of_le [Nontrivial V] (hp₀₁ : p₀ ≤ p₁)
    (hp₁ : p₁ ≠ ∞) {s : ℝ} (hs : nikolskiiExponent (finrank ℝ V) p₀ p₁ ≤ s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : Lp ℂ p₀ (volume : Measure V)} (hf : MemTriebelLizorkin s q f) :
    ∃ g : Lp ℂ p₁ (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f := by
  rcases hp₀₁.eq_or_lt with rfl | hlt
  · exact ⟨f, ae_eq_refl _⟩
  obtain ⟨g, hg, -⟩ := exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top hlt hp₁ rfl
    ((triebelLizorkinNorm_mono_exponent hq le_top f).trans_lt (hf.mono_smoothness hs))
  exact ⟨g, hg⟩

/-- **Jawerth's embedding** `F^{s₀}_{p₀,∞} ↪ F^{s₁}_{p₁,q}` (Jawerth 1977; Triebel 1983, §2.7.1;
Vybíral 2008, Theorem 0.1 (ii); the proof is Johnsen–Sickel's, 2007, Proposition 1): let `n ≥ 1`,
`1 ≤ p₀ < p₁ < ∞`, `s₁ ≥ 0` and `s₀ - s₁ = n(1/p₀ - 1/p₁)`. Every `f ∈ L_{p₀}(V)` with a finite
quasi-norm in `F^{s₀}_{p₀,∞}` has a representative `g ∈ L_{p₁}(V)` with
`‖g‖_{F^{s₁}_{p₁,q}} ≤ K_{V,p₀,p₁} ‖f‖_{F^{s₀}_{p₀,∞}}` for every `1 ≤ q ≤ ∞`. The representative
comes from `F^{s₀}_{p₀,∞} ⊆ F^{s₀-s₁}_{p₀,∞} ↪ L_{p₁}`
(`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`), its blocks are those of `f`
(`Rd.blockFun_eq_of_ae_eq`), and `‖·‖_{ℓ_q} ≤ ‖·‖_{ℓ_1}` reduces the bound to the integrated
bound (`Rd.eLpNorm_tsum_dyadicWeight_enorm_blockFun_le`). -/
theorem exists_triebelLizorkinNorm_le_of_nikolskiiExponent [Nontrivial V] (hp₀₁ : p₀ < p₁)
    (hp₁ : p₁ ≠ ∞) {s₀ s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (hs : s₀ - s₁ = nikolskiiExponent (finrank ℝ V) p₀ p₁) {f : Lp ℂ p₀ (volume : Measure V)}
    (hf : triebelLizorkinNorm s₀ ∞ f < ∞) :
    ∃ g : Lp ℂ p₁ (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f ∧ ∀ q : ℝ≥0∞, 1 ≤ q →
      triebelLizorkinNorm s₁ q g ≤ criticalEmbeddingConst V p₀ p₁ * triebelLizorkinNorm s₀ ∞ f := by
  obtain ⟨g, hg, -⟩ := exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top hp₀₁ hp₁ hs.symm
    ((triebelLizorkinNorm_mono_smoothness (by linarith) ∞ f).trans_lt hf)
  refine ⟨g, hg, fun q hq => ?_⟩
  refine le_trans ?_ (eLpNorm_tsum_dyadicWeight_enorm_blockFun_le hp₀₁ hp₁ hs f)
  refine eLpNorm_mono_eNorm (aemeasurable_lqNorm_blockFun s₁ q g).aestronglyMeasurable
    fun x => ?_
  simp only [eNorm_eq_self, blockFun_eq_of_ae_eq hg]
  exact ENNReal.lqNorm_le_lqNorm_one hq _

/-! ### The critical Sobolev embedding -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {r : ℝ≥0∞}

omit [Fact (1 ≤ p)] in
/-- **The exponent `0`**: every `f ∈ L_p(V)` is a class `u` of `L_0(V)` with the same
representative, and `‖u‖_0 = 0`. With Lean's convention `0⁻¹ = 0`, the exponent `r = 0`
satisfies `n(1/p - 1/r) = n/p`, so the critical embeddings below treat it by this lemma. -/
theorem exists_lp_zero_ae_eq (f : Lp ℂ p (volume : Measure V)) :
    ∃ u : Lp ℂ 0 (volume : Measure V), (u : V → ℂ) =ᵐ[volume] f ∧ ‖u‖ₑ = 0 := by
  have hmem : MemLp (f : V → ℂ) 0 volume :=
    memLp_zero_iff_aestronglyMeasurable.2 (Lp.aestronglyMeasurable f)
  exact ⟨hmem.toLp f, hmem.coeFn_toLp,
    by rw [Lp.eNorm_toLp, eLpNorm_exponent_zero (Lp.aestronglyMeasurable f)]⟩

/-- **The critical Sobolev embedding with named constants**: let `n ≥ 1`, `1 < p < ∞`, `r < ∞`,
`m ≥ 1` and `m = n(1/p - 1/r)`, that is `1/r = 1/p - m/n`, and let `f ∈ L_p(V)` have weak
derivatives `g_α ∈ L_p(V)` of order `m` along the basis `e` of `Rd.gridBasis` for every
multi-index `α`. Then there is `u ∈ L_r(V)` with `u = f` almost everywhere and
`‖u‖_r ≤ K_{V,p,r} (‖Φ‖_1 ‖f‖_p + 2^m ∑_α K_α ‖g_α‖_p)` with `K_α = Rd.sobolevToTLConst V p α`.
Here `p < r`, and `‖f‖_{F^m_{p,∞}} ≤ ‖f‖_{F^m_{p,2}}` is bounded by the weak derivatives
(`Rd.triebelLizorkinNorm_le_of_hasWeakLineDeriv`), so `F^m_{p,∞} ↪ L_r`
(`Rd.exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top`) applies. -/
theorem exists_memLp_ae_eq_of_hasWeakLineDeriv_of_eq [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hr : r ≠ ∞) {m : ℕ} (hm : 1 ≤ m) (hs : nikolskiiExponent (finrank ℝ V) p r = m)
    {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    ∃ u : Lp ℂ r (volume : Measure V), (u : V → ℂ) =ᵐ[volume] f ∧
      ‖u‖ₑ ≤ criticalEmbeddingConst V p r * (eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
        2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · obtain ⟨u, hu, hn⟩ := exists_lp_zero_ae_eq f
    exact ⟨u, hu, hn.trans_le zero_le⟩
  have hpr : p < r := lt_of_nikolskiiExponent_pos (Nat.cast_nonneg _) hp
    (pos_iff_ne_zero.2 hr0) (by rw [hs]; exact Nat.cast_pos.2 hm)
  have hle : triebelLizorkinNorm (m : ℝ) ∞ f ≤ eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
      2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ :=
    (triebelLizorkinNorm_mono_exponent one_le_two le_top f).trans
      (triebelLizorkinNorm_le_of_hasWeakLineDeriv hp1 hp hg)
  obtain ⟨u, hu, hn⟩ := exists_memLp_ae_eq_of_triebelLizorkinNorm_lt_top hpr hr hs
    ((triebelLizorkinNorm_mono_exponent one_le_two le_top f).trans_lt
      (memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg))
  exact ⟨u, hu, hn.trans (mul_le_mul' le_rfl hle)⟩

/-- **The Sobolev embedding `W^m_p ↪ L_r` for `p ≤ r < ∞`**: let `n ≥ 1`, `1 < p < ∞`,
`p ≤ r < ∞` and `n(1/p - 1/r) ≤ m`. Every `f ∈ W^m_p(V)` has a representative in `L_r(V)`. For
`r = p` this is `f` itself; for `p < r`, `f ∈ F^m_{p,2}` (`Rd.memTriebelLizorkin_of_memSobolev`)
and `F^m_{p,2} ↪ L_r` (`Rd.exists_memLp_ae_eq_of_memTriebelLizorkin_of_le`). -/
theorem exists_memLp_ae_eq_of_memSobolev_of_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hpr : p ≤ r) (hr : r ≠ ∞) {m : ℕ} (hs : nikolskiiExponent (finrank ℝ V) p r ≤ m)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f :=
  exists_memLp_ae_eq_of_memTriebelLizorkin_of_le hpr hr hs one_le_two
    (memTriebelLizorkin_of_memSobolev hp1 hp hf)

/-- **The critical Sobolev embedding** (Sobolev's inequality for `1 < p < n/m`): let `n ≥ 1`,
`1 < p < ∞`, `r < ∞` and `m = n(1/p - 1/r)`, that is `1/r = 1/p - m/n`. Every `f ∈ W^m_p(V)` has
a representative in `L_r(V)`. Here `p ≤ r` (`le_of_nikolskiiExponent_nonneg`), so
`Rd.exists_memLp_ae_eq_of_memSobolev_of_le` applies;
`Rd.exists_memLp_ae_eq_of_hasWeakLineDeriv_of_eq` adds the norm bound. -/
theorem exists_memLp_ae_eq_of_memSobolev_of_eq [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hr : r ≠ ∞) {m : ℕ} (hs : nikolskiiExponent (finrank ℝ V) p r = m)
    {f : Lp ℂ p (volume : Measure V)} (hf : MemSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure V), (g : V → ℂ) =ᵐ[volume] f := by
  rcases eq_or_ne r 0 with rfl | hr0
  · obtain ⟨u, hu, -⟩ := exists_lp_zero_ae_eq f
    exact ⟨u, hu⟩
  have hpr : p ≤ r := le_of_nikolskiiExponent_nonneg (Nat.cast_pos.2 finrank_pos) hp
    (pos_iff_ne_zero.2 hr0) (by rw [hs]; exact Nat.cast_nonneg m)
  exact exists_memLp_ae_eq_of_memSobolev_of_le hp1 hp hpr hr hs.le hf

end Rd
