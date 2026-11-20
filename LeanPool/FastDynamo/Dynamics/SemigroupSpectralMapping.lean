/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.AnalyticSemigroupGenerator
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Spectral mapping and growth bound of an analytic semigroup with compact resolvent

Let `S` be an analytic `C₀`-semigroup on a complex Banach space whose generator `G` has a
compact resolvent.  This module proves the two abstract statements behind the paper's
Lemma A.1 (`lem:semigroup-spectral-growth`):

* `IsAnalyticSemigroup.spectrum_diff_zero`: the spectral mapping theorem
  `σ(S(t)) \ {0} = exp(t σ(G))` for every `t > 0`;
* `IsAnalyticSemigroup.growthBound_eq_iSup`: if `σ(G)` is nonempty, the growth bound of `S` is
  `sup Re σ(G)`, the supremum is attained, and it is attained at an eigenvalue of `G`.

The argument uses point spectra only.  An eigenvector of `G` with eigenvalue `λ` is an
eigenvector of `S(t)` with eigenvalue `e^{tλ}`.  Conversely, `S(t)` is compact for `t > 0`, so by
the Fredholm alternative a nonzero `μ ∈ σ(S(t))` is an eigenvalue; its eigenspace `E` is
finite-dimensional (the identity of `E` is the compact operator `μ⁻¹ S(t)`), lies in the domain of
`G`, and is invariant under the bounded operator `G S(t)`, which therefore has an eigenvector in
`E`; this is an eigenvector of `G` with an eigenvalue `λ` such that `μ = e^{tλ}`.  For the growth
bound, an eigenvector gives `‖S(t)‖ ≥ e^{t Re λ}`, so the growth bound `ω₀` is finite and is the
limit of `t⁻¹ log ‖S(t)‖`; Gelfand's formula for `S(1)` identifies `e^{ω₀}` with the spectral
radius of `S(1)`, which is attained at a point `e^{λ}` of the spectrum with `λ ∈ σ(G)`.  The
paper cites Engel–Nagel (Corollaries IV.3.11 and IV.3.12) for spectral mapping and for the
equality of growth bound and spectral bound; the proof here is the direct one above, which uses
the compactness of the resolvent and of `S(t)` instead of the general theory of eventually
norm-continuous semigroups.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Topology

open scoped ENNReal

universe u

namespace StronglyContinuousSemigroup

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- An eigenvector of the generator with eigenvalue `λ` gives the lower bound
`e^{t Re λ} ≤ ‖S(t)‖`. -/
theorem exp_re_mul_le_norm [CompleteSpace X] (S : StronglyContinuousSemigroup X)
    (x : S.generator.domain) (hx : (x : X) ≠ 0) (lam : ℂ)
    (h : S.generator x = lam • (x : X)) (t : NNReal) :
    Real.exp (lam.re * t) ≤ ‖S t‖ := by
  have hpos : 0 < ‖(x : X)‖ := norm_pos_iff.mpr hx
  have h1 := (S t).le_opNorm (x : X)
  rw [S.apply_eq_cexp_smul_of_generator_eq_smul x lam h t, norm_smul, Complex.norm_exp,
    Complex.re_ofReal_mul, mul_comm (t : ℝ)] at h1
  exact le_of_mul_le_mul_right h1 hpos

/-- At integer times the semigroup is a power of its value at time `1`. -/
theorem operator_natCast (S : StronglyContinuousSemigroup X) (n : ℕ) :
    S (n : NNReal) = S 1 ^ n := by
  induction n with
  | zero => simp [ContinuousLinearMap.one_def]
  | succ n ih => rw [Nat.cast_succ, S.operator_add, ih, pow_succ, ContinuousLinearMap.mul_def]

/-- If the generator has a compact resolvent, every `λ` in its spectrum gives the point `e^{tλ}`
of the spectrum of `S(t)`, through an eigenvector. -/
theorem cexp_mem_spectrum [CompleteSpace X] {S : StronglyContinuousSemigroup X} {r : ℂ}
    {R : X →L[ℂ] X} (hR : LinearPMap.IsResolvent S.generator r R) (hc : IsCompactOperator R)
    {lam : ℂ} (hlam : lam ∈ LinearPMap.spectrum S.generator) (t : NNReal) :
    Complex.exp (((t : ℝ) : ℂ) * lam) ∈ spectrum ℂ (S t) := by
  obtain ⟨x, hx, hGx⟩ := LinearPMap.exists_eigenvector_of_mem_spectrum hR hc hlam
  rw [ContinuousLinearMap.spectrum_eq]
  refine Module.End.HasEigenvalue.mem_spectrum
    (Module.End.hasEigenvalue_of_hasEigenvector (x := (x : X))
      (Module.End.hasEigenvector_iff.mpr ⟨?_, hx⟩))
  rw [Module.End.mem_eigenspace_iff]
  exact S.apply_eq_cexp_smul_of_generator_eq_smul x lam hGx t

end StronglyContinuousSemigroup

/-- For an analytic semigroup whose generator has a compact resolvent and `t > 0`, every nonzero
point `μ` of the spectrum of `S(t)` is `e^{tλ}` for some `λ` in the spectrum of the generator.
The eigenspace of the compact operator `S(t)` at `μ` is finite-dimensional and invariant under
the bounded operator `G S(t)`, whose eigenvector there is an eigenvector of `G`. -/
theorem IsAnalyticSemigroup.exists_cexp_eq_of_mem_spectrum {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (hS : IsAnalyticSemigroup S δ)
    {r : ℂ} {R : X →L[ℂ] X} (hR : LinearPMap.IsResolvent S.generator r R)
    (hc : IsCompactOperator R) {t : NNReal} (ht : 0 < t) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (S t)) (hμ0 : μ ≠ 0) :
    ∃ lam ∈ LinearPMap.spectrum S.generator, Complex.exp (((t : ℝ) : ℂ) * lam) = μ := by
  have hcpt := hS.isCompactOperator hR hc ht
  have hev : Module.End.HasEigenvalue ((S t : X →L[ℂ] X) : Module.End ℂ X) μ :=
    (hcpt.hasEigenvalue_iff_mem_spectrum hμ0).2 hμ
  obtain ⟨G', hG'⟩ := hS.exists_generator_comp ht
  set E := Module.End.eigenspace ((S t : X →L[ℂ] X) : Module.End ℂ X) μ
  have hmemE : ∀ x, x ∈ E ↔ S t x = μ • x := fun _ ↦ Module.End.mem_eigenspace_iff
  have hcomm : ∀ x, S t (G' x) = G' (S t x) := by
    intro x
    obtain ⟨h1, e1⟩ := hG' x
    obtain ⟨h2, e2⟩ := S.apply_mem_generator_domain t ⟨S t x, h1⟩
    obtain ⟨h3, e3⟩ := hG' (S t x)
    calc S t (G' x) = S t (S.generator ⟨S t x, h1⟩) := by rw [e1]
      _ = S.generator ⟨S t (S t x), h3⟩ := e2.symm
      _ = G' (S t x) := e3
  have hmaps : ∀ x ∈ E, (G' : X →ₗ[ℂ] X) x ∈ E := by
    intro x hx
    rw [hmemE] at hx ⊢
    simp only [ContinuousLinearMap.coe_coe]
    rw [hcomm, hx, map_smul]
  have hSE : ∀ x ∈ E, ((S t : X →L[ℂ] X) : X →ₗ[ℂ] X) x ∈ E := by
    intro x hx
    rw [hmemE] at hx ⊢
    simp only [ContinuousLinearMap.coe_coe]
    rw [hx, map_smul, hx]
  have hclosed : IsClosed (E : Set X) := by
    have : (E : Set X) = {x | S t x = μ • x} := by
      ext x
      exact hmemE x
    rw [this]
    exact isClosed_eq (S t).continuous (continuous_const_smul μ)
  have hcE : IsCompactOperator (((S t : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict hSE) :=
    hcpt.restrict hSE hclosed
  have hid : (id : E → E) = μ⁻¹ • ⇑(((S t : X →L[ℂ] X) : X →ₗ[ℂ] X).restrict hSE) := by
    funext x
    apply Subtype.ext
    simp [LinearMap.restrict_apply, (hmemE x).1 x.2, smul_smul, inv_mul_cancel₀ hμ0]
  have : FiniteDimensional ℂ E :=
    FiniteDimensional.of_isCompactOperator_id (hid ▸ hcE.smul μ⁻¹)
  have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hev
  obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue ((G' : X →ₗ[ℂ] X).restrict hmaps)
  obtain ⟨v, hv⟩ := hν.exists_hasEigenvector
  have hv1 : G' (v : X) = ν • (v : X) := by
    have := congrArg Subtype.val hv.apply_eq_smul
    simpa using this
  have hv2 : S t (v : X) = μ • (v : X) := (hmemE _).1 v.2
  have hv0 : (v : X) ≠ 0 := by
    have := (Module.End.hasEigenvector_iff.mp hv).2
    simpa using this
  obtain ⟨h1, e1⟩ := hG' (v : X)
  set w : S.generator.domain := μ⁻¹ • ⟨S t v, h1⟩ with hw_def
  have hw : (w : X) = v := by
    simp [w, hv2, smul_smul, inv_mul_cancel₀ hμ0]
  have hGw : S.generator w = (μ⁻¹ * ν) • (w : X) := by
    rw [hw_def, _root_.LinearPMap.map_smul, e1, hv1, ← hw_def, hw, smul_smul]
  refine ⟨μ⁻¹ * ν, LinearPMap.mem_spectrum_of_eigenvector w (hw ▸ hv0) hGw, ?_⟩
  have := S.apply_eq_cexp_smul_of_generator_eq_smul w _ hGw t
  rw [hw, hv2] at this
  exact (smul_left_injective ℂ hv0 this).symm

/-- **Spectral mapping theorem**: equation (A.1) (`eq:compact-semigroup-spectral-mapping`) of
the paper's Lemma A.1 (`lem:semigroup-spectral-growth`), for an abstract analytic semigroup whose
generator `G` has a compact resolvent: `σ(S(t)) \ {0} = exp(t σ(G))` for every `t > 0`. -/
theorem IsAnalyticSemigroup.spectrum_diff_zero {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (hS : IsAnalyticSemigroup S δ)
    {r : ℂ} {R : X →L[ℂ] X} (hR : LinearPMap.IsResolvent S.generator r R)
    (hc : IsCompactOperator R) {t : NNReal} (ht : 0 < t) :
    spectrum ℂ (S t) \ {0} =
      (fun lam : ℂ ↦ Complex.exp (((t : ℝ) : ℂ) * lam)) '' LinearPMap.spectrum S.generator := by
  ext μ
  constructor
  · rintro ⟨hμ, hμ0⟩
    obtain ⟨lam, hlam, rfl⟩ := hS.exists_cexp_eq_of_mem_spectrum hR hc ht hμ hμ0
    exact ⟨lam, hlam, rfl⟩
  · rintro ⟨lam, hlam, rfl⟩
    exact ⟨StronglyContinuousSemigroup.cexp_mem_spectrum hR hc hlam t, Complex.exp_ne_zero _⟩

/-- **Growth bound equals spectral bound**: equation (A.2) (`eq:growth-rate-spectral-bound`) of
the paper's Lemma A.1 (`lem:semigroup-spectral-growth`), with attainment, for an abstract
analytic semigroup.  For an analytic semigroup whose generator `G` has a compact
resolvent and a nonempty spectrum, the growth bound is `sup {Re λ : λ ∈ σ(G)}`, and the supremum
is attained at an eigenvalue of `G`.  The growth bound is finite here (it is the real number
`Re λ` of that eigenvalue). -/
theorem IsAnalyticSemigroup.growthBound_eq_iSup {X : Type u}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {S : StronglyContinuousSemigroup X} {δ : ℝ} (hS : IsAnalyticSemigroup S δ)
    {r : ℂ} {R : X →L[ℂ] X} (hR : LinearPMap.IsResolvent S.generator r R)
    (hc : IsCompactOperator R)
    (hne : (LinearPMap.spectrum S.generator).Nonempty) :
    S.growthBound = ⨆ lam ∈ LinearPMap.spectrum S.generator, ((lam.re : ℝ) : EReal) ∧
      ∃ lam ∈ LinearPMap.spectrum S.generator, ((lam.re : ℝ) : EReal) = S.growthBound ∧
        ∃ x : S.generator.domain, (x : X) ≠ 0 ∧ S.generator x = lam • (x : X) := by
  obtain ⟨lam₀, hlam₀⟩ := hne
  obtain ⟨x₀, hx₀, hGx₀⟩ := LinearPMap.exists_eigenvector_of_mem_spectrum hR hc hlam₀
  have hbot : S.growthBound ≠ ⊥ := S.growthBound_ne_bot_iff.2
    ⟨lam₀.re, fun t _ ↦ S.exp_re_mul_le_norm x₀ hx₀ lam₀ hGx₀ t⟩
  obtain ⟨L, hL, hlim⟩ := S.exists_growthBound_eq_and_tendsto hbot
  have hup : ∀ lam ∈ LinearPMap.spectrum S.generator, lam.re ≤ L := by
    intro lam hlam
    obtain ⟨x, hx, hGx⟩ := LinearPMap.exists_eigenvector_of_mem_spectrum hR hc hlam
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have h := S.exp_re_mul_le_norm x hx lam hGx (Real.toNNReal t)
    rw [Real.coe_toNNReal _ ht.le] at h
    rw [le_inv_mul_iff₀ ht, mul_comm]
    exact (Real.le_log_iff_exp_le ((Real.exp_pos _).trans_le h)).2 h
  have hpos : ∀ t : NNReal, 0 < ‖S t‖ := fun t ↦
    (Real.exp_pos _).trans_le (S.exp_re_mul_le_norm x₀ hx₀ lam₀ hGx₀ t)
  have : Nontrivial X := ⟨⟨(x₀ : X), 0, hx₀⟩⟩
  have hrad : spectralRadius ℂ (S 1) = ENNReal.ofReal (Real.exp L) := by
    refine tendsto_nhds_unique
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (S 1)) ?_
    have h3 := (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto L).comp
      (hlim.comp tendsto_natCast_atTop_atTop))
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply, Real.toNNReal_natCast, ← S.operator_natCast]
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      (by positivity), Real.rpow_def_of_pos (hpos _), mul_comm, one_div]
  obtain ⟨μ₀, hμ₀, hnorm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (S 1))
  rw [hrad] at hnorm
  have hnorm' : ‖μ₀‖ = Real.exp L := by
    have := congrArg ENNReal.toReal hnorm
    rwa [ENNReal.coe_toReal, coe_nnnorm, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have hμ0 : μ₀ ≠ 0 := norm_pos_iff.mp (hnorm' ▸ Real.exp_pos _)
  obtain ⟨lam, hlam, hlam_eq⟩ :=
    hS.exists_cexp_eq_of_mem_spectrum hR hc one_pos hμ₀ hμ0
  have hre : lam.re = L := by
    rw [← hlam_eq, Complex.norm_exp] at hnorm'
    simpa using hnorm'
  refine ⟨?_, lam, hlam, by rw [hL, hre],
    LinearPMap.exists_eigenvector_of_mem_spectrum hR hc hlam⟩
  rw [hL]
  exact le_antisymm (le_iSup₂_of_le lam hlam (by rw [hre]))
    (iSup₂_le fun l hl ↦ EReal.coe_le_coe_iff.2 (hup l hl))

end

end FastDynamo
