/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSpectralEigenspaces
public import LeanPool.CutoffRigidity.GibbsSobolevConstants
public import LeanPool.CutoffRigidity.GibbsResolventBounds
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! # Constants and the genuine Gibbs spectral gap

The fixed space of the actual variational resolvent is identified from its
energy equation and the distributional closed-gradient kernel theorem.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The genuine resolvent has no fixed vectors other than constants. -/
theorem gibbsL2Resolvent_eq_self_iff_constant {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : E →₂[gibbsMeasure volume V] ℝ) :
    gibbsL2Resolvent hV hprob u = u ↔ ∃ c : ℝ, u = gibbsConstantLp hprob c := by
  constructor
  · intro hu
    let v := gibbsWeakResolvent hV hprob u
    have hJ : gibbsSobolevInclusion hV hprob v = u := hu
    have henergy := gibbsWeakResolvent_equation hV hprob u v
    rw [hJ] at henergy
    have hG : gibbsSobolevDerivative hV hprob v = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).mp
      change gibbsDirichletEnergy hV hprob v v = 0
      linarith
    obtain ⟨c, hc⟩ := gibbsSobolev_eq_constant_of_derivative_eq_zero hV hprob v hG
    exact ⟨c, hJ.symm.trans hc⟩
  · rintro ⟨c, rfl⟩
    exact gibbsL2Resolvent_constant hV hprob c

/-- Zero eigenvectors of the actual closed form operator are exactly
constant L² classes; no smooth representative is required. -/
theorem mem_gibbsOperatorEigenspace_zero_iff_constant {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : E →₂[gibbsMeasure volume V] ℝ) :
    u ∈ gibbsOperatorEigenspace hV hprob 0 ↔ ∃ c : ℝ, u = gibbsConstantLp hprob c := by
  rw [mem_gibbsOperatorEigenspace_iff_resolvent]
  simpa using gibbsL2Resolvent_eq_self_iff_constant hV hprob u

/-- The norm of a nonzero compact positive symmetric real Hilbert
operator is a genuine attained eigenvalue. -/
theorem compact_positive_hasEigenvalue_norm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ x (T x)) (hT : T ≠ 0) :
    Module.End.HasEigenvalue T.toLinearMap ‖T‖ := by
  have : Nontrivial H := by
    by_contra hn
    have := not_nontrivial_iff_subsingleton.mp hn
    exact hT (Subsingleton.elim _ _)
  have hnorm : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT
  have hspec : ‖T‖ ∈ spectrum ℝ T ∨ -‖T‖ ∈ spectrum ℝ T := by
    simp_rw [spectrum, Set.mem_compl_iff]
    by_contra! h
    obtain ⟨c, hc0, hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet
      (by simpa using h.1) (by simpa using h.2)
    have hle := ciSup_le hc
    rw [← ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hs] at hle
    linarith
  rcases hspec with hpos | hneg
  · exact (hc.hasEigenvalue_iff_mem_spectrum hnorm).mpr hpos
  · have hnegE := (hc.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hnorm)).mpr hneg
    have hh := eigenvalue_nonneg_of_nonneg hnegE hp
    change 0 ≤ -‖T‖ at hh
    exact False.elim (hnorm (le_antisymm (by linarith) (norm_nonneg _)))

/-- A compact positive symmetric contraction with no nonzero fixed vector
has norm strictly below one. This is the norm-attainment step of the
compact spectral argument, using the actual compact spectral theorem. -/
theorem compact_positive_contraction_norm_lt_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x, 0 ≤ inner ℝ x (T x)) (hn : ‖T‖ ≤ 1)
    (hfixed : ∀ x, T x = x → x = 0) : ‖T‖ < 1 := by
  apply lt_of_le_of_ne hn
  intro heq
  have hT : T ≠ 0 := by
    intro hz
    simp [hz] at heq
  have heigen := compact_positive_hasEigenvalue_norm T hc hs hp hT
  obtain ⟨x, hx, hx0⟩ := heigen.exists_hasEigenvector
  have hTx : T x = x := by
    have hh := hx
    rw [Module.End.mem_eigenspace_iff, heq, one_smul] at hh
    exact hh
  exact hx0 (hfixed x hTx)

/-- The actual mean-zero Hilbert subspace. -/
@[expose] noncomputable def gibbsMeanZeroSpace {V : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    Submodule ℝ (E →₂[gibbsMeasure volume V] ℝ) :=
  (ℝ ∙ gibbsConstantLp hprob 1)ᗮ

instance gibbsMeanZeroSpace_completeSpace {V : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    CompleteSpace (gibbsMeanZeroSpace hprob) := by
  unfold gibbsMeanZeroSpace
  infer_instance

theorem gibbsL2Resolvent_mem_meanZero {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : E →₂[gibbsMeasure volume V] ℝ) (hu : u ∈ gibbsMeanZeroSpace hprob) :
    gibbsL2Resolvent hV hprob u ∈ gibbsMeanZeroSpace hprob := by
  rw [gibbsMeanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_left] at hu ⊢
  rw [gibbsL2Resolvent_symmetric, gibbsL2Resolvent_constant]
  exact hu

/-- The genuine compact resolvent restricted to mean-zero classes. -/
@[expose] noncomputable def gibbsMeanZeroResolvent {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) :
    gibbsMeanZeroSpace hprob →L[ℝ] gibbsMeanZeroSpace hprob :=
  (gibbsL2Resolvent hV hprob).restrict (gibbsL2Resolvent_mem_meanZero hV hprob)

theorem gibbsConstantLp_eq_smul_one {V : E → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (c : ℝ) :
    gibbsConstantLp hprob c = c • gibbsConstantLp hprob 1 := by
  let := hprob
  apply Lp.ext
  filter_upwards [(memLp_const c).coeFn_toLp, Lp.coeFn_smul c (gibbsConstantLp hprob 1),
    (memLp_const (1 : ℝ)).coeFn_toLp] with x hx hs h1
  change (gibbsConstantLp hprob c : E → ℝ) x = c at hx
  change (gibbsConstantLp hprob 1 : E → ℝ) x = 1 at h1
  rw [hx, hs, Pi.smul_apply, smul_eq_mul, h1, mul_one]

/-- The actual restricted resolvent has no nonzero fixed vector. -/
theorem gibbsMeanZeroResolvent_fixed_eq_zero {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsMeanZeroSpace hprob) (hu : gibbsMeanZeroResolvent hV hprob u = u) : u = 0 := by
  have hfix : gibbsL2Resolvent hV hprob u = u := congrArg Subtype.val hu
  obtain ⟨c, hc⟩ := (gibbsL2Resolvent_eq_self_iff_constant hV hprob u).mp hfix
  have hspan : (u : E →₂[gibbsMeasure volume V] ℝ) ∈ ℝ ∙ gibbsConstantLp hprob 1 := by
    rw [hc]
    exact (gibbsConstantLp_eq_smul_one hprob c).symm ▸
      (ℝ ∙ gibbsConstantLp hprob 1).smul_mem c
        (Submodule.mem_span_singleton_self (gibbsConstantLp hprob 1))
  have hzero := Submodule.inner_right_of_mem_orthogonal hspan u.property
  apply Subtype.ext
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hzero

/-- Compactness and connectedness force a strict contraction on the
actual mean-zero subspace. The constant is obtained from the operator norm,
not assumed as a Poincaré or spectral-gap premise. -/
theorem norm_gibbsMeanZeroResolvent_lt_one {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ‖gibbsMeanZeroResolvent hV hprob‖ < 1 := by
  apply compact_positive_contraction_norm_lt_one
  · exact (gibbsL2Resolvent_isCompactOperator hV hprob ρ hρ hHess).restrict'
      (gibbsL2Resolvent_mem_meanZero hV hprob)
  · intro x y
    exact gibbsL2Resolvent_symmetric hV hprob x y
  · intro x
    exact gibbsL2Resolvent_nonneg hV hprob x
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖gibbsL2Resolvent hV hprob x‖ ≤ 1 * ‖x‖
    calc
      _ ≤ ‖gibbsL2Resolvent hV hprob‖ * ‖(x : E →₂[gibbsMeasure volume V] ℝ)‖ :=
        (gibbsL2Resolvent hV hprob).le_opNorm _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (norm_gibbsL2Resolvent_le_one hV hprob) (norm_nonneg _)
  · exact gibbsMeanZeroResolvent_fixed_eq_zero hV hprob

/-- In positive Euclidean dimension the genuine mean-zero Hilbert space
is nontrivial. Curvature supplies the coordinate L² integrability and full
support prevents a nonzero linear coordinate from being a constant class. -/
theorem gibbsMeanZeroSpace_nontrivial {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    Nontrivial (gibbsMeanZeroSpace hprob) := by
  let := hprob
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro hbot
  have htop : (ℝ ∙ gibbsConstantLp hprob 1) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hbot
  let j : Fin d := ⟨0, hd⟩
  let v : E := PiLp.single 2 j 1
  let f : E → ℝ := fun x => inner ℝ v x
  have hf : MemLp f 2 (gibbsMeasure volume V) :=
    (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess).const_inner v
  have hmem : hf.toLp f ∈ ℝ ∙ gibbsConstantLp hprob 1 := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hceq : hf.toLp f = gibbsConstantLp hprob c := by
    rw [gibbsConstantLp_eq_smul_one hprob c]
    exact hc.symm
  have hae : f =ᵐ[gibbsMeasure volume V] fun _ => c := by
    filter_upwards [hf.coeFn_toLp, (memLp_const c).coeFn_toLp] with x hx hconst
    change (gibbsConstantLp hprob c : E → ℝ) x = c at hconst
    rw [hceq] at hx
    exact hx.symm.trans hconst
  have heq : f = fun _ => c := gibbsMeasure_eq_of_ae_eq volume
    hV.continuous.measurable (by fun_prop) continuous_const hae
  have hz := congrFun heq 0
  have hv := congrFun heq v
  have hvnorm : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  change inner ℝ v 0 = c at hz
  change inner ℝ v v = c at hv
  rw [inner_zero_right] at hz
  rw [real_inner_self_eq_norm_sq, hvnorm] at hv
  norm_num at hv
  linarith

/-- The strictly positive bottom eigenvalue is attained by the genuine
closed Gibbs operator, in positive Euclidean dimension. -/
theorem exists_positive_gibbsOperator_eigenvalue {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    0 < ‖gibbsMeanZeroResolvent hV hprob‖ ∧
      ∃ u : E →₂[gibbsMeasure volume V] ℝ, u ≠ 0 ∧
        u ∈ gibbsOperatorEigenspace hV hprob (‖gibbsMeanZeroResolvent hV hprob‖⁻¹ - 1) ∧
        0 < ‖gibbsMeanZeroResolvent hV hprob‖⁻¹ - 1 := by
  let := gibbsMeanZeroSpace_nontrivial hV hprob hd ρ hρ hHess
  let T := gibbsMeanZeroResolvent hV hprob
  have hT : T ≠ 0 := by
    intro hzero
    obtain ⟨u, hu⟩ := exists_ne (0 : gibbsMeanZeroSpace hprob)
    have hRu : gibbsL2Resolvent hV hprob u = 0 := by
      have hh := congrArg (fun S : gibbsMeanZeroSpace hprob →L[ℝ] gibbsMeanZeroSpace hprob =>
        ((S u : gibbsMeanZeroSpace hprob) : E →₂[gibbsMeasure volume V] ℝ)) hzero
      exact hh
    have hu0 : (u : E →₂[gibbsMeasure volume V] ℝ) = 0 :=
      gibbsL2Resolvent_injective hV hprob (by simpa only [map_zero] using hRu)
    exact hu (Subtype.ext hu0)
  have hr : 0 < ‖T‖ := by
    have hh : ‖T‖ ≠ 0 := by
      intro hz
      apply hT
      apply ContinuousLinearMap.ext
      intro x
      apply norm_eq_zero.mp
      have hn := T.le_opNorm x
      rw [hz, zero_mul] at hn
      exact le_antisymm hn (norm_nonneg _)
    exact lt_of_le_of_ne (norm_nonneg T) hh.symm
  have hr1 : ‖T‖ < 1 := norm_gibbsMeanZeroResolvent_lt_one hV hprob ρ hρ hHess
  have heig := compact_positive_hasEigenvalue_norm T
    ((gibbsL2Resolvent_isCompactOperator hV hprob ρ hρ hHess).restrict'
      (gibbsL2Resolvent_mem_meanZero hV hprob))
    (fun x y => gibbsL2Resolvent_symmetric hV hprob x y)
    (fun x => gibbsL2Resolvent_nonneg hV hprob x) hT
  obtain ⟨u, hu, hu0⟩ := heig.exists_hasEigenvector
  refine ⟨hr, u, ?_, ?_, ?_⟩
  · intro hh
    exact hu0 (Subtype.ext hh)
  · have hRu : gibbsL2Resolvent hV hprob u = ‖T‖ • (u : E →₂[gibbsMeasure volume V] ℝ) :=
      congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hu)
    rw [mem_gibbsOperatorEigenspace_iff_resolvent, map_smul, hRu, smul_smul]
    have hh : (1 + (‖T‖⁻¹ - 1)) * ‖T‖ = 1 := by
      field_simp
      ring
    rw [hh, one_smul]
  · have hi : 1 < ‖T‖⁻¹ := (one_lt_inv₀ hr).mpr hr1
    linarith

/-- The exact mean-zero inclusion bound read from the actual restricted
resolvent norm. The argument is the Hilbert form version of Poincaré. -/
theorem gibbsMeanZero_sobolev_norm_sq_le {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (u : gibbsSobolevGraph hV hprob)
    (hu : gibbsSobolevInclusion hV hprob u ∈ gibbsMeanZeroSpace hprob) :
    ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 ≤
      ‖gibbsMeanZeroResolvent hV hprob‖ * ‖u‖ ^ 2 := by
  let x := gibbsSobolevInclusion hV hprob u
  let y := gibbsWeakResolvent hV hprob x
  let r := ‖gibbsMeanZeroResolvent hV hprob‖
  have hpair : inner ℝ u y = ‖x‖ ^ 2 := by
    rw [real_inner_comm, gibbsSobolev_inner, gibbsWeakResolvent_equation,
      real_inner_self_eq_norm_sq]
  have hynorm : ‖y‖ ^ 2 = inner ℝ x (gibbsL2Resolvent hV hprob x) := by
    rw [← real_inner_self_eq_norm_sq, gibbsSobolev_inner,
      gibbsWeakResolvent_equation]
    rfl
  have hRx : ‖gibbsL2Resolvent hV hprob x‖ ≤ r * ‖x‖ :=
    (gibbsMeanZeroResolvent hV hprob).le_opNorm ⟨x, hu⟩
  have hybound : ‖y‖ ^ 2 ≤ r * ‖x‖ ^ 2 := by
    rw [hynorm]
    calc
      _ ≤ ‖x‖ * ‖gibbsL2Resolvent hV hprob x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (r * ‖x‖) := mul_le_mul_of_nonneg_left hRx (norm_nonneg _)
      _ = _ := by ring
  have hcs : (‖x‖ ^ 2) ^ 2 ≤ ‖u‖ ^ 2 * ‖y‖ ^ 2 := by
    rw [← hpair]
    simpa only [pow_two, real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le u y
  have hh : (‖x‖ ^ 2) ^ 2 ≤ ‖u‖ ^ 2 * (r * ‖x‖ ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hybound (sq_nonneg _))
  by_cases hx : ‖x‖ ^ 2 = 0
  · change ‖x‖ ^ 2 ≤ r * ‖u‖ ^ 2
    rw [hx]
    exact mul_nonneg (norm_nonneg (gibbsMeanZeroResolvent hV hprob)) (sq_nonneg _)
  · have hxpos : 0 < ‖x‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hx)
    change ‖x‖ ^ 2 ≤ r * ‖u‖ ^ 2
    nlinarith

/-- Sharp Poincaré inequality for the actual closed Gibbs Sobolev form,
with its attained positive spectral value, derived from compactness. -/
theorem gibbsSharpPoincare {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsSobolevGraph hV hprob)
    (hu : gibbsSobolevInclusion hV hprob u ∈ gibbsMeanZeroSpace hprob) :
    (‖gibbsMeanZeroResolvent hV hprob‖⁻¹ - 1) *
        ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 ≤ gibbsDirichletEnergy hV hprob u u := by
  have hr := (exists_positive_gibbsOperator_eigenvalue hV hprob hd ρ hρ hHess).1
  have h := gibbsMeanZero_sobolev_norm_sq_le hV hprob u hu
  rw [gibbsSobolev_norm_sq] at h
  have he : (1 - ‖gibbsMeanZeroResolvent hV hprob‖) *
      ‖gibbsSobolevInclusion hV hprob u‖ ^ 2 ≤
      ‖gibbsMeanZeroResolvent hV hprob‖ * gibbsDirichletEnergy hV hprob u u := by
    nlinarith
  calc
    _ = ((1 - ‖gibbsMeanZeroResolvent hV hprob‖) *
        ‖gibbsSobolevInclusion hV hprob u‖ ^ 2) / ‖gibbsMeanZeroResolvent hV hprob‖ := by
      field_simp
    _ ≤ _ := (div_le_iff₀ hr).mpr (he.trans_eq (mul_comm _ _))

/-- The attained compact-resolvent spectral value is below every
positive actual operator eigenvalue. -/
theorem gibbsSpectralGap_le_positive_eigenvalue {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (rate : ℝ) (hrate : 0 < rate)
    (u : gibbsOperatorEigenspace hV hprob rate) (hu : u ≠ 0) :
    ‖gibbsMeanZeroResolvent hV hprob‖⁻¹ - 1 ≤ rate := by
  let x : E →₂[gibbsMeasure volume V] ℝ := u
  let v := gibbsWeakResolvent hV hprob ((1 + rate) • x)
  have hJ : gibbsSobolevInclusion hV hprob v = x :=
    (mem_gibbsOperatorEigenspace_iff_resolvent hV hprob rate x).mp u.property
  have hmean : x ∈ gibbsMeanZeroSpace hprob := by
    rw [gibbsMeanZeroSpace, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact gibbsOperatorEigen_inner_constant_eq_zero hV hprob rate (ne_of_gt hrate) u 1
  have henergy : gibbsDirichletEnergy hV hprob v v = rate * ‖x‖ ^ 2 := by
    have hh := gibbsWeakResolvent_equation hV hprob ((1 + rate) • x) v
    rw [hJ, real_inner_smul_left, real_inner_self_eq_norm_sq] at hh
    nlinarith
  have hp := gibbsSharpPoincare hV hprob hd ρ hρ hHess v (hJ.symm ▸ hmean)
  rw [hJ, henergy] at hp
  have hx : x ≠ 0 := by
    intro hz
    exact hu (Subtype.ext hz)
  have hxpos : 0 < ‖x‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  nlinarith

/-- Actual positive spectral-gap attainment and its bottom-of-positive-
spectrum characterization, with no gap or compactness assumption added. -/
theorem gibbsSpectralGap_attained {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ∃ rate : ℝ, 0 < rate ∧
      (∃ u : gibbsOperatorEigenspace hV hprob rate, u ≠ 0) ∧
      ∀ s : ℝ, 0 < s → ∀ u : gibbsOperatorEigenspace hV hprob s, u ≠ 0 → rate ≤ s := by
  obtain ⟨_, u, hu, he, hpos⟩ := exists_positive_gibbsOperator_eigenvalue hV hprob hd ρ hρ hHess
  refine ⟨_, hpos, ⟨⟨u, he⟩, ?_⟩, ?_⟩
  · intro hz
    exact hu (congrArg Subtype.val hz)
  · exact gibbsSpectralGap_le_positive_eigenvalue hV hprob hd ρ hρ hHess

end CutoffRigidity
