/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Assembly.ProductInductionEnergy
public import LeanPool.FastDynamo.Dynamics.Assembly.ProductResolvent

/-!
# The resolvent of the induction operator is bounded from `H⁻²`

The induction operator `A = productInductionOperator u ε` of the paper (`eq:induction`, §1.1) on
the product torus `T² × T` has, for a divergence-free transverse velocity `u` and `ε > 0`, the
resolvent `R(r) = (r − A)⁻¹ : L² → L²` at every real `r > M_u = ‖∇u‖_∞`
(`productInductionHalfPlaneResolvent`).  This module proves that `R(r)` is bounded with respect to
the `H⁻²` norm of the Fourier model `productL2ToHMinus2`:

`‖R(r) f‖₂ ≤ C ‖f‖_{H⁻²}` for every `f ∈ L²`

(`exists_norm_stateResolvent_le_productL2ToHMinus2`), and that consequently `R(r)` carries
derivatives taken in `H⁻²` to derivatives in `L²` (`hasDerivWithinAt_comp_of_norm_le`).  These
are the two analytic inputs of the uniqueness of `H⁻²`-valued strong solutions of the curl-form
induction equation in `FastDynamo/Dynamics/Assembly/PhysicalInductionUniqueness.lean`.

The proof writes `f = (1 − Δ) g` with `g ∈ H²` and `‖g‖₂ ≤ C ‖f‖_{H⁻²}` (Fourier synthesis of
`f̂/(1 + 4π²|ξ|²)`, `exists_productH2_sub_laplacian_eq`), and expresses `ε Δ g` through the pencil
`r − A`, the transport term `(u·∇)g` and the stretching term `(g·∇)u`.  The only term that is not
bounded by `‖g‖₂` is the transport term; its resolvent is controlled by the energy inequality
with the gradient term retained and the skewness of transport
(`exists_norm_stateResolvent_productInductionTransport_le`), i.e. the resolvent gains one
derivative.  The paper does not state these estimates.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

/-! ## Fourier synthesis from `H⁻²` -/

/-- Fourier synthesis on the `H⁻²` model: the `L²` field whose Fourier coefficients are the
entries of an `H⁻²` coefficient array.  On `productL2ToHMinus2 f` it is `(1 − Δ)⁻¹ f`. -/
def productHMinus2Synthesis : ProductC3HMinus2 →L[ℂ] ProductC3L2 :=
  productC3FourierSynthesis

/-- **`(1 − Δ)⁻¹` from `L²` into `H²`.**  Every `f ∈ L²` is `g − Δg` for an `H²` field `g` whose
`L²` part is the Fourier synthesis of the `H⁻²` coefficients `f̂/(1 + 4π²|ξ|²)` of `f`. -/
theorem exists_productH2_sub_laplacian_eq (f : ProductC3L2) :
    ∃ g : ProductC3H2, productH2Embedding g - productLaplacianFromH2 g = f ∧
      productH2Embedding g = productHMinus2Synthesis (productL2ToHMinus2 f) := by
  have hcoeff : ∀ n k i, productCoeffCLM n k i
      (productHMinus2Synthesis (productL2ToHMinus2 f)) =
        productCoeffCLM n k i f / (productH2Weight n k : ℂ) := by
    intro n k i
    rw [productHMinus2Synthesis, productCoeffCLM_productC3FourierSynthesis,
      productL2ToHMinus2_apply]
  have hw : ∀ n k, (productH2Weight n k : ℂ) ≠ 0 := fun n k ↦ by
    exact_mod_cast (productH2Weight_pos n k).ne'
  have hmem : (productHMinus2Synthesis (productL2ToHMinus2 f), productC3FourierAnalysis f) ∈
      productH2Submodule := by
    rw [mem_productH2Submodule_iff]
    intro n k i
    rw [productC3FourierAnalysis_apply, hcoeff, mul_div_cancel₀ _ (hw n k)]
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  apply productC3L2_ext_coeff
  intro n k i
  rw [map_sub, productCoeffCLM_productLaplacianFromH2, productH2Embedding_apply]
  change productCoeffCLM n k i (productHMinus2Synthesis (productL2ToHMinus2 f)) -
    -(productFrequencyEnergy n k : ℂ) *
      productCoeffCLM n k i (productHMinus2Synthesis (productL2ToHMinus2 f)) = _
  have hE : (productH2Weight n k : ℂ) = 1 + (productFrequencyEnergy n k : ℂ) := by
    rw [productH2Weight_eq_one_add_energy]; push_cast; rfl
  rw [hcoeff]
  calc productCoeffCLM n k i f / (productH2Weight n k : ℂ) -
        -(productFrequencyEnergy n k : ℂ) * (productCoeffCLM n k i f / (productH2Weight n k : ℂ))
      = (1 + (productFrequencyEnergy n k : ℂ)) *
          (productCoeffCLM n k i f / (productH2Weight n k : ℂ)) := by ring
    _ = productCoeffCLM n k i f := by rw [← hE, mul_div_cancel₀ _ (hw n k)]

/-! ## The resolvent gains one derivative on transport -/

/-- The arithmetic of the resolvent estimate for the transport term: from
`T = r Y² − a`, `T ≤ c s X` and `a ≤ M Y² − ε s²` (with `ε > 0`, `r > M`) follows
`Y ≤ √(c²/(4ε(r − M))) X`, by Young's inequality `c s X ≤ ε s² + c²/(4ε) X²`. -/
private theorem resolvent_transport_arith {r M ε c X Y s a T : ℝ} (hε : 0 < ε)
    (hrM : 0 < r - M) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hre : T = r * Y ^ 2 - a)
    (hskew : T ≤ c * s * X) (hen : a ≤ M * Y ^ 2 - ε * s ^ 2) :
    Y ≤ Real.sqrt (c ^ 2 / (4 * ε * (r - M))) * X := by
  have hyoung : c * s * X ≤ ε * s ^ 2 + c ^ 2 / (4 * ε) * X ^ 2 := by
    have e : ε * s ^ 2 + c ^ 2 / (4 * ε) * X ^ 2 - c * s * X =
        (2 * ε * s - c * X) ^ 2 / (4 * ε) := by
      field_simp
      ring
    have : 0 ≤ (2 * ε * s - c * X) ^ 2 / (4 * ε) := by positivity
    linarith
  have hY2 : (r - M) * Y ^ 2 ≤ c ^ 2 / (4 * ε) * X ^ 2 := by
    have e : (r - M) * Y ^ 2 = r * Y ^ 2 - M * Y ^ 2 := by ring
    rw [e]
    linarith
  have hK0 : 0 ≤ c ^ 2 / (4 * ε * (r - M)) := by positivity
  have hY2' : Y ^ 2 ≤ (Real.sqrt (c ^ 2 / (4 * ε * (r - M))) * X) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK0]
    have e : c ^ 2 / (4 * ε * (r - M)) * X ^ 2 = c ^ 2 / (4 * ε) * X ^ 2 / (r - M) := by
      field_simp
    rw [e, le_div_iff₀ hrM, mul_comm]
    exact hY2
  exact (pow_le_pow_iff_left₀ hY (by positivity) two_ne_zero).1 hY2'

/-- **The resolvent of the transport term.**  At a real parameter `r > M_u`, the resolvent of
the induction operator applied to the transport term `(u·∇)g` is bounded by `‖g‖₂`.  Pairing
`(r − A) y = (u·∇) g` with `y`, the energy inequality `Re ⟨y, A y⟩ ≤ M_u ‖y‖² − ε ‖∇y‖²` and the
skewness of transport give `(r − M_u) ‖y‖² + ε ‖∇y‖² ≤ c ‖∇y‖ ‖g‖`, and Young's inequality
removes `‖∇y‖`. -/
theorem exists_norm_stateResolvent_productInductionTransport_le (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) {r : ℝ}
    (hr : ‖transverseStretchingCoefficient u‖ < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ProductC3H2,
      ‖(productInductionHalfPlaneResolvent u hu hε).stateResolvent (r : ℂ)
          (productInductionTransport u g)‖ ≤ C * ‖productH2Embedding g‖ := by
  obtain ⟨c, -, hc⟩ := exists_norm_productInductionTransport_le u
  refine ⟨Real.sqrt (c ^ 2 / (4 * ε * (r - ‖transverseStretchingCoefficient u‖))),
    Real.sqrt_nonneg _, fun g ↦ ?_⟩
  have hz : (r : ℂ) ∈ {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re} := by
    simpa using hr
  have hpen := DFunLike.congr_fun ((productInductionHalfPlaneResolvent u hu hε).right_inv _ hz)
    (productInductionTransport u g)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    DomainOperator.pencil, sub_apply,
    smul_apply] at hpen
  change ‖productH2Embedding ((productInductionHalfPlaneResolvent u hu hε).inv (r : ℂ)
    (productInductionTransport u g))‖ ≤ _
  generalize (productInductionHalfPlaneResolvent u hu hε).inv (r : ℂ)
    (productInductionTransport u g) = y at hpen ⊢
  change (r : ℂ) • productH2Embedding y - productInductionAction u ε y =
    productInductionTransport u g at hpen
  have hre : (inner ℂ (productH2Embedding y) (productInductionTransport u g)).re =
      r * ‖productH2Embedding y‖ ^ 2 -
        (inner ℂ (productH2Embedding y) (productInductionAction u ε y)).re := by
    rw [← hpen, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      Complex.sub_re, Complex.re_ofReal_mul]
    norm_cast
  have hskew : (inner ℂ (productH2Embedding y) (productInductionTransport u g)).re ≤
      c * Real.sqrt (productGradientEnergy y) * ‖productH2Embedding g‖ := by
    rw [re_inner_productInductionTransport_skew u hu]
    refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      ((norm_inner_le_norm _ _).trans ?_))
    exact mul_le_mul_of_nonneg_right (hc y) (norm_nonneg _)
  have hen := re_inner_productInductionAction_le_sub u hu ε y
  rw [← Real.sq_sqrt (productGradientEnergy_nonneg y)] at hen
  exact resolvent_transport_arith hε (sub_pos.mpr hr) (norm_nonneg _) (norm_nonneg _) hre
    hskew hen

/-! ## The resolvent is bounded from `H⁻²` -/

/-- The norm bookkeeping of the `H⁻²` resolvent estimate, for a bounded operator `P` on a normed
space: if `f = x − Δ`, `ε Δ = r x − q + T − S` and `P q = x`, with `‖P T‖ ≤ C₁ ‖x‖` and
`‖S‖ ≤ d ‖x‖`, then `‖P f‖` is bounded by an explicit multiple of `‖x‖`. -/
private theorem norm_resolvent_arith {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : E →L[ℂ] E) {x q Δ T S f : E} {ε r C₁ d : ℝ} (hε : 0 < ε) (hf : x - Δ = f)
    (hq : P q = x) (key : (ε : ℂ) • Δ = (r : ℂ) • x - q + T - S) (hT : ‖P T‖ ≤ C₁ * ‖x‖)
    (hS : ‖S‖ ≤ d * ‖x‖) :
    ‖P f‖ ≤ (‖P‖ + ε⁻¹ * (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d)) * ‖x‖ := by
  have hΔ : (ε : ℂ) • P Δ = (r : ℂ) • P x - x + P T - P S := by
    rw [← P.map_smul, key, P.map_sub, P.map_add, P.map_sub, P.map_smul, hq]
  have hPx : ‖P x‖ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
  have hPS : ‖P S‖ ≤ ‖P‖ * (d * ‖x‖) :=
    (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hS (norm_nonneg _))
  have hrx : ‖(r : ℂ) • P x‖ ≤ |r| * (‖P‖ * ‖x‖) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hPx (abs_nonneg _)
  have hn : ε * ‖P Δ‖ ≤ (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d) * ‖x‖ := by
    have h1 : ‖(ε : ℂ) • P Δ‖ = ε * ‖P Δ‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    rw [← h1, hΔ]
    have h2 : ‖(r : ℂ) • P x - x + P T - P S‖ ≤
        ‖(r : ℂ) • P x‖ + ‖x‖ + ‖P T‖ + ‖P S‖ :=
      (norm_sub_le _ _).trans (add_le_add_left
        ((norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)) _)
    have h3 : (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d) * ‖x‖ =
        |r| * (‖P‖ * ‖x‖) + ‖x‖ + C₁ * ‖x‖ + ‖P‖ * (d * ‖x‖) := by ring
    linarith
  have hnΔ : ‖P Δ‖ ≤ ε⁻¹ * ((|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d) * ‖x‖) := by
    rw [← div_eq_inv_mul, le_div_iff₀' hε]
    exact hn
  rw [← hf, map_sub]
  have h4 : (‖P‖ + ε⁻¹ * (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d)) * ‖x‖ =
      ‖P‖ * ‖x‖ + ε⁻¹ * ((|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d) * ‖x‖) := by ring
  rw [h4]
  exact (norm_sub_le _ _).trans (add_le_add hPx hnΔ)

/-- **The resolvent is bounded from the `H⁻²` norm.**  For a divergence-free transverse
velocity, `ε > 0` and a real parameter `r > M_u`, there is `C` with
`‖(r − A)⁻¹ f‖₂ ≤ C ‖f‖_{H⁻²}` for every `f ∈ L²`.  With `f = g − Δg`,
`ε Δg = r g − (r − A) g + (u·∇)g − (g·∇)u`, so `(r − A)⁻¹ f` is a combination of `g`,
`(r − A)⁻¹ g`, `(r − A)⁻¹ (u·∇)g` and `(r − A)⁻¹ (g·∇)u`, each bounded by `‖g‖₂ ≤ C ‖f‖_{H⁻²}`. -/
theorem exists_norm_stateResolvent_le_productL2ToHMinus2 (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε) {r : ℝ}
    (hr : ‖transverseStretchingCoefficient u‖ < r) :
    ∃ C : ℝ, ∀ f : ProductC3L2,
      ‖(productInductionHalfPlaneResolvent u hu hε).stateResolvent (r : ℂ) f‖ ≤
        C * ‖productL2ToHMinus2 f‖ := by
  have hz : (r : ℂ) ∈ {z : ℂ | ‖transverseStretchingCoefficient u‖ < z.re} := by
    simpa using hr
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_stateResolvent_productInductionTransport_le u hu hε hr
  obtain ⟨d, hd0, hd⟩ := exists_norm_productInductionStretching_le u
  have hleft := (productInductionHalfPlaneResolvent u hu hε).left_inv _ hz
  obtain ⟨P, hP⟩ : ∃ P, P = (productInductionHalfPlaneResolvent u hu hε).stateResolvent (r : ℂ) :=
    ⟨_, rfl⟩
  rw [← hP]
  have hK0 : 0 ≤ ‖P‖ + ε⁻¹ * (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d) := by positivity
  refine ⟨(‖P‖ + ε⁻¹ * (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d)) * ‖productHMinus2Synthesis‖,
    fun f ↦ ?_⟩
  obtain ⟨g, hfg, hgsyn⟩ := exists_productH2_sub_laplacian_eq f
  have hPpen : P ((r : ℂ) • productH2Embedding g - productInductionAction u ε g) =
      productH2Embedding g := by
    have := DFunLike.congr_fun hleft g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      DomainOperator.pencil, sub_apply,
      smul_apply] at this
    rw [hP]
    exact congrArg productH2Embedding this
  have key : (ε : ℂ) • productLaplacianFromH2 g = (r : ℂ) • productH2Embedding g -
      ((r : ℂ) • productH2Embedding g - productInductionAction u ε g) +
        productInductionTransport u g - productInductionStretching u g := by
    rw [productInductionAction_eq_transport]
    abel
  have hPf := norm_resolvent_arith P hε hfg hPpen key (hP ▸ hC₁ g) (hd g)
  have hx : ‖productH2Embedding g‖ ≤ ‖productHMinus2Synthesis‖ * ‖productL2ToHMinus2 f‖ := by
    rw [hgsyn]
    exact productHMinus2Synthesis.le_opNorm _
  calc ‖P f‖ ≤ (‖P‖ + ε⁻¹ * (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d)) * ‖productH2Embedding g‖ := hPf
    _ ≤ (‖P‖ + ε⁻¹ * (|r| * ‖P‖ + 1 + C₁ + ‖P‖ * d)) *
          (‖productHMinus2Synthesis‖ * ‖productL2ToHMinus2 f‖) :=
        mul_le_mul_of_nonneg_left hx hK0
    _ = _ := by ring

/-! ## Transfer of derivatives -/

/-- **Transfer of a derivative through a dominated map.**  If `‖R x‖ ≤ C ‖J x‖` for continuous
linear maps `R` and `J`, then a derivative of `J ∘ c` of the form `J d` gives the derivative
`R d` of `R ∘ c`, within any set.  With `J = productL2ToHMinus2` and `R` the resolvent of the
induction operator, a time derivative in `H⁻²` becomes one in `L²`. -/
theorem hasDerivWithinAt_comp_of_norm_le {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G]
    [NormedSpace ℂ G] (R : E →L[ℂ] F) (J : E →L[ℂ] G) {C : ℝ}
    (hC : ∀ x, ‖R x‖ ≤ C * ‖J x‖) {c : ℝ → E} {d : E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt (fun τ ↦ J (c τ)) (J d) s t) :
    HasDerivWithinAt (fun τ ↦ R (c τ)) (R d) s t := by
  rw [hasDerivWithinAt_iff_isLittleO] at h ⊢
  refine Asymptotics.IsBigO.trans_isLittleO
    (Asymptotics.IsBigO.of_bound C (Eventually.of_forall fun τ ↦ ?_)) h
  have hR : R (c τ) - R (c t) - (τ - t) • R d = R (c τ - c t - (τ - t) • d) := by
    rw [map_sub, map_sub, R.map_smul_of_tower]
  have hJ : J (c τ) - J (c t) - (τ - t) • J d = J (c τ - c t - (τ - t) • d) := by
    rw [map_sub, map_sub, J.map_smul_of_tower]
  rw [hR, hJ]
  exact hC _

end

end FastDynamo
