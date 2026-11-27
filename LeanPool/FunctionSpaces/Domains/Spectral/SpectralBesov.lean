/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Spectral.NeumannEigenbasis
public import LeanPool.FunctionSpaces.Domains.Lipschitz.BoundedLipschitz
public import LeanPool.FunctionSpaces.Rd.Interpolation.BesselPotentialInterpolation
public import LeanPool.FunctionSpaces.Rd.Differences.BesovDifferences

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on domains by eigenfunction expansions

Let `V` be a finite-dimensional real inner product space of dimension `n`, such as `ℝ^n`, with
Lebesgue measure, `0 < θ < 1` and `1 ≤ q ≤ ∞`. On a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1`, the Besov space `B^θ_{2,q}(Ω)` of intrinsic moduli of smoothness is the approximation
space `A^θ_q` of the Neumann eigenbasis; on every bounded open set the Dirichlet eigenbasis gives
one inclusion.

* **The modulus on `Ω` by the K-functional** of `(L_2(Ω), W^1_2(Ω))`:
  `ω_r(f, 2^(-k), Ω)_2 ≤ C K(2^(-k), f|_Ω)`, since every element of `W^1_2(Ω)` extends to
  `H^1(V)` with a bound and `ω_r(ι U, 2^(-k))_2 ≤ 2^(r-1) 2π 2^(-k) ‖U‖` for `U ∈ H^1(V)`
  (`Rd.lpModulus_toL2_le`, `Rd.BoundedLipschitzDomain.exists_lpModulusOn_le_kFunctional`); so the
  intrinsic quasi-norm is at most `C` times the interpolation norm
  (`Rd.BoundedLipschitzDomain.exists_modNormOn_le_interpNorm`).
* **The restriction** maps `(L_2(V), H^1(V))_{θ,q} = B^θ_{2,q}(V)` into
  `(L_2(Ω), W^1_2(Ω))_{θ,q}` (`Rd.memKMethod_neumann_restrict_of_memKMethod`), and the Besov
  extension theorem extends `f|_Ω` to `V`.
* **The main theorem** (`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`): for every order
  `r ≥ 1`, `f|_Ω` lies in the approximation space `A^θ_q` of the Neumann scheme iff
  `‖f‖_{L_2(Ω)} + ‖(2^(kθ) ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_q} < ∞`; equivalently the dyadic blocks of
  the Neumann expansion of `f|_Ω` have finite `B^θ_{2,q}` norm
  (`Rd.BoundedLipschitzDomain.modNormOn_lt_top_iff_blockNorm_lt_top`), and for `q = 2`,
  `∑_i (1 + λ_i)^θ |⟨e_i, f|_Ω⟩|² < ∞` with the Neumann eigenvalues `λ_i`
  (`Rd.BoundedLipschitzDomain.modNormOn_two_lt_top_iff`).
* **The Dirichlet inclusion**: elements of `H^1_0(Ω)` are the zero extensions of their values on
  `Ω` (`Rd.indicatorExtendLp_dirichletEmbedding`), so the zero extension maps the approximation
  space `A^θ_q` of the Dirichlet scheme into `B^θ_{2,q}(V)`
  (`Rd.memApprox_bandScheme_extendByZero_of_memApprox_dirichletScheme`), and these functions
  have finite intrinsic quasi-norm on `Ω` (`Rd.modNormOn_lt_top_of_memApprox_dirichletScheme`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace Module Metric
open scoped ENNReal Real InnerProductSpace BesselPotentialSpace SchwartzMap LineDeriv

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The modulus on a domain and the K-functional of the Neumann couple -/

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V) [Nontrivial V]

/-- **The intrinsic modulus by the K-functional of the Neumann couple**: for a bounded Lipschitz
domain `Ω` in dimension `n ≥ 1` and every order `r ≥ 1` there is a finite `C` such that
`ω_r(f, 2^(-k), Ω)_2 ≤ C K(2^(-k), f|_Ω)` for every `f ∈ L_2(V)` and every `k`, with the
K-functional of `(L_2(Ω), W^1_2(Ω))` for the Neumann embedding `J`. For `w` in the Neumann space
take `u ∈ H^1(Ω)` with `u|_Ω = J w` and `‖u‖ ≤ C₀ ‖w‖`
(`Rd.BoundedLipschitzDomain.exists_restrictionSpace_of_neumannSpace`); as an element of `H^1(V)`
it extends `J w`, so `Rd.lpModulusOn_le_add_lpModulus` and `Rd.lpModulus_toL2_le` give
`ω_r(f, 2^(-k), Ω)_2 ≤ 2^r ‖f|_Ω - J w‖ + 2^(r-1) 2π C₀ 2^(-k) ‖w‖`. -/
theorem exists_lpModulusOn_le_kFunctional {r : ℕ} (hr : 1 ≤ r) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (f : Lp ℂ 2 (volume : Measure V)) (k : ℕ),
      lpModulusOn 2 Ω.carrier r f k ≤
        C * ApproximationScheme.kFunctional ((neumannEmbedding Ω.toOpens).restrictScalars ℝ)
          (dyadicWeight (-1) k) (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f) := by
  obtain ⟨C₀, hC₀, hN⟩ := Ω.exists_restrictionSpace_of_neumannSpace
  have hM : max (2 ^ r) (2 ^ (r - 1) * ENNReal.ofReal (2 * π) * ENNReal.ofReal C₀) ≠ ∞ :=
    max_ne_top (by simp) (by finiteness)
  have hM0 : max (2 ^ r) (2 ^ (r - 1) * ENNReal.ofReal (2 * π) * ENNReal.ofReal C₀) ≠ 0 :=
    (lt_max_of_lt_left (by positivity)).ne'
  refine ⟨_, hM, fun f k => ?_⟩
  rw [ApproximationScheme.kFunctional, ENNReal.mul_iInf_of_ne hM0 hM]
  refine le_iInf fun w => ?_
  obtain ⟨u, hu, hnorm⟩ := hN w
  have h1 := lpModulusOn_le_add_lpModulus Ω.measurableSet r f (toL2 (u : H^{1}(V))) k
  have h2 : ‖indicatorLp Ω.measurableSet (f - toL2 (u : H^{1}(V)))‖ₑ =
      ‖LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f -
        (neumannEmbedding Ω.toOpens).restrictScalars ℝ w‖ₑ := by
    rw [enorm_indicatorLp_eq, map_sub]
    change ‖LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f - restrictL2 Ω.toOpens u‖ₑ = _
    rw [hu]
    rfl
  have h3 : ‖(u : H^{1}(V))‖ₑ ≤ ENNReal.ofReal C₀ * ‖w‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC₀]
    exact ENNReal.ofReal_le_ofReal hnorm
  have h4 := (lpModulus_toL2_le hr (u : H^{1}(V)) k).trans (mul_le_mul' le_rfl h3)
  rw [h2] at h1
  refine (h1.trans (add_le_add le_rfl h4)).trans ?_
  rw [mul_add]
  refine add_le_add (mul_le_mul' (le_max_left _ _) le_rfl) ?_
  calc 2 ^ (r - 1) * ENNReal.ofReal (2 * π) * dyadicWeight (-1) k * (ENNReal.ofReal C₀ * ‖w‖ₑ)
      = 2 ^ (r - 1) * ENNReal.ofReal (2 * π) * ENNReal.ofReal C₀ *
          (dyadicWeight (-1) k * ‖w‖ₑ) := by ring
    _ ≤ _ := mul_le_mul' (le_max_right _ _) le_rfl

/-- **The intrinsic quasi-norm by the interpolation norm of the Neumann couple**: for a bounded
Lipschitz domain `Ω` in dimension `n ≥ 1`, every order `r ≥ 1` and all `θ`, `q`, there is a finite
`C` such that every `f ∈ L_2(V)` satisfies
`N_Ω(f) ≤ C (‖f|_Ω‖_2 + ‖(2^(kθ) K(2^(-k), f|_Ω))_k‖_{ℓ_q})`, where `N_Ω` is the intrinsic Besov
quasi-norm with moduli of order `r` (`Rd.modNormOn`) and `K` the K-functional of
`(L_2(Ω), W^1_2(Ω))` (`Rd.BoundedLipschitzDomain.exists_lpModulusOn_le_kFunctional`). -/
theorem exists_modNormOn_le_interpNorm {r : ℕ} (hr : 1 ≤ r) (θ : ℝ) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ 2 (volume : Measure V),
      modNormOn Ω.measurableSet r θ q f ≤
        C * ApproximationScheme.interpNorm ((neumannEmbedding Ω.toOpens).restrictScalars ℝ) θ 1 q
          (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f) := by
  obtain ⟨C, hC, h⟩ := Ω.exists_lpModulusOn_le_kFunctional hr
  refine ⟨max 1 C, max_ne_top ENNReal.one_ne_top hC, fun f => ?_⟩
  rw [modNormOn, ApproximationScheme.interpNorm, mul_add, enorm_indicatorLp_eq]
  refine add_le_add (le_mul_of_one_le_left' (le_max_left _ _)) ?_
  rw [← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun k => ?_
  rw [ApproximationScheme.interpSeq, one_mul, mul_left_comm]
  exact mul_le_mul' le_rfl ((h f k).trans (mul_le_mul' (le_max_right _ _) le_rfl))

/-- **The Neumann approximation spaces lie in the intrinsic Besov space**: for a bounded Lipschitz
domain `Ω` in dimension `n ≥ 1`, `0 < θ < 1`, `1 ≤ q ≤ ∞` and every order `r ≥ 1`, if `f|_Ω`
lies in the approximation space `A^θ_q` of the Neumann scheme, then the intrinsic quasi-norm
`N_Ω(f)` with moduli of order `r` is finite. `A^θ_q` is `(L_2(Ω), W^1_2(Ω))_{θ,q}`
(`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff`), whose discrete norm on the grid `2^(-k)`
is finite (`InterpCouple.memKMethod_iff_interpNorm_lt_top`) and bounds `N_Ω(f)`
(`Rd.BoundedLipschitzDomain.exists_modNormOn_le_interpNorm`). -/
theorem modNormOn_lt_top_of_memApprox_neumannScheme {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ)
    (hθ' : θ < 1) (hq : 1 ≤ q) {r : ℕ} (hr : 1 ≤ r) {f : Lp ℂ 2 (volume : Measure V)}
    (hf : Ω.neumannScheme.toScheme.MemApprox θ q
      (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f)) :
    modNormOn Ω.measurableSet r θ q f < ∞ := by
  have hK := (Ω.memKMethod_neumann_iff hθ hθ' hq).2 hf
  have hI := (InterpCouple.memKMethod_iff_interpNorm_lt_top InterpCouple.isQuasiNormed_ofMap
    (max_ne_top ENNReal.one_ne_top eNorm_ne_top) InterpCouple.norm0_ofMap_le hθ one_pos
    (zero_lt_one.trans_le hq).ne').1 hK
  rw [InterpCouple.interpNorm_ofMap] at hI
  obtain ⟨C, hC, h⟩ := Ω.exists_modNormOn_le_interpNorm hr θ q
  exact (h f).trans_lt (ENNReal.mul_lt_top hC.lt_top hI)

end BoundedLipschitzDomain

/-! ### Restriction of `(L_2(V), H^1(V))` to the Neumann couple -/

variable (O : Opens V)

/-- **`H^1(V)` in the Neumann space, with norm at most `2π`**: for `U ∈ H^1(V)` and open `O`,
`‖(ι U|_O, ((∂_{b_k} ι U)|_O)_k)‖ ≤ 2π ‖U‖`, since
`‖ι U|_O‖_2² + ∑_k ‖(∂_{b_k} ι U)|_O‖_2² ≤ ‖ι U‖_2² + ∑_k ‖∂_{b_k} ι U‖_2² ≤ (2π)² ‖U‖²`
(`Rd.ValueGradientL2.sq_norm_eq`, `Rd.sq_norm_eq_of_hasWeakLineDeriv`). -/
theorem norm_restrictNeumann_apply_le (U : H^{1}(V)) :
    ‖restrictNeumann O U‖ ≤ 2 * π * ‖U‖ := by
  have hU := sq_norm_eq_of_hasWeakLineDeriv (gridBasis V) U
    (fun i => hasWeakLineDeriv_weakDerivL2 (gridBasis V i) U)
  have hw : ‖restrictNeumann O U‖ ^ 2 =
      ‖LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V) (toL2 U)‖ ^ 2 +
        ∑ i, ‖LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V) (weakDerivL2 (gridBasis V i) U)‖ ^ 2 :=
    ValueGradientL2.sq_norm_eq (toValueGradientL2 O U)
  have h1 : ‖restrictNeumann O U‖ ^ 2 ≤
      ‖toL2 U‖ ^ 2 + ∑ i, ‖weakDerivL2 (gridBasis V i) U‖ ^ 2 := by
    rw [hw]
    gcongr with i
    · exact norm_Lp_toLp_restrict_le _ _
    · exact norm_Lp_toLp_restrict_le _ _
  have hπ : 1 ≤ (2 * π) ^ 2 := one_le_pow₀ (by linarith [Real.two_le_pi])
  have hs : 0 ≤ ∑ i, ‖weakDerivL2 (gridBasis V i) U‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : ‖toL2 U‖ ^ 2 + ∑ i, ‖weakDerivL2 (gridBasis V i) U‖ ^ 2 ≤ (2 * π * ‖U‖) ^ 2 := by
    rw [mul_pow, hU, inv_pow, mul_add, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    nlinarith [sq_nonneg ‖toL2 U‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h1.trans h2)

/-- **The restriction maps `(L_2(V), H^1(V))` into the Neumann couple**: for an open set `O`, if
`f ∈ L_2(V)` lies in the real interpolation space `(L_2(V), H^1(V))_{θ,q}` of the `L_2` norm and
the Bessel potential norm (`Rd.lpBesselPotentialCouple 1`), then `f|_O` lies in
`(L_2(O), W^1_2(O))_{θ,q}`. The couple is that of the embedding `H^1(V) → L_2(V)`
(`Rd.ofMap_toL2_eq_lpBesselPotentialCouple`), and the restriction maps `ι U` to the value of
`Rd.restrictNeumann O U`, so the interpolation property for compatible maps applies
(`ApproximationScheme.MemKMethod.map`). -/
theorem memKMethod_neumann_restrict_of_memKMethod {θ : ℝ} {q : ℝ≥0∞}
    {f : Lp ℂ 2 (volume : Measure V)} (hf : (lpBesselPotentialCouple (p := 2) 1).MemKMethod θ q f) :
    (InterpCouple.ofMap ((neumannEmbedding O).restrictScalars ℝ)).MemKMethod θ q
      (LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V) f) := by
  rw [← ofMap_toL2_eq_lpBesselPotentialCouple, InterpCouple.memKMethod_ofMap_iff] at hf
  refine InterpCouple.memKMethod_ofMap_iff.2 (ApproximationScheme.MemKMethod.map
    ((LpToLpRestrictCLM V ℂ ℂ volume 2 (O : Set V)).restrictScalars ℝ)
    ((restrictNeumann O).restrictScalars ℝ) ?_ hf)
  ext1 U
  exact (neumannEmbedding_restrictNeumann U).symm

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V) [Nontrivial V]

/-- **The intrinsic Besov space lies in the Neumann approximation spaces**: for a bounded
Lipschitz domain `Ω` in dimension `n ≥ 1`, `0 < θ < 1`, `1 ≤ q ≤ ∞` and every order `r > θ`
(for natural `r` and `θ > 0` this is `r ≥ 1`), if the intrinsic quasi-norm `N_Ω(f)` with moduli
of order `r` is finite, then `f|_Ω` lies in the approximation space `A^θ_q` of the Neumann
scheme. The Besov extension theorem gives `F` with `F = f` on `Ω` in `B^θ_{2,q}(V)`
(`Rd.BoundedLipschitzDomain.exists_memApprox_extension_iff`), that is in
`(L_2(V), H^1(V))_{θ,q}` (`Rd.memKMethod_lpBesselPotentialCouple_iff`); the restriction maps it
into `(L_2(Ω), W^1_2(Ω))_{θ,q}` (`Rd.memKMethod_neumann_restrict_of_memKMethod`), which is
`A^θ_q` (`Rd.BoundedLipschitzDomain.memKMethod_neumann_iff`). -/
theorem memApprox_neumannScheme_of_modNormOn_lt_top {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ)
    (hθ' : θ < 1) (hq : 1 ≤ q) {r : ℕ} (hθr : θ < r) {f : Lp ℂ 2 (volume : Measure V)}
    (hf : modNormOn Ω.measurableSet r θ q f < ∞) :
    Ω.neumannScheme.toScheme.MemApprox θ q
      (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f) := by
  obtain ⟨F, hFf, hF⟩ := (Ω.exists_memApprox_extension_iff two_ne_top hθ hθr hq f).2 hf
  have hK : (lpBesselPotentialCouple (p := 2) 1).MemKMethod θ q F := by
    refine (memKMethod_lpBesselPotentialCouple_iff ENNReal.one_lt_two two_ne_top one_pos hθ hθ'
      hq).2 ?_
    rwa [mul_one]
  have hae := (indicatorLp_eq_iff_ae_eq_restrict Ω.measurableSet).1 hFf
  have hR : LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) F =
      LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f :=
    Lp.ext ((LpToLpRestrictCLM_coeFn ℂ _ F).trans
      (hae.trans (LpToLpRestrictCLM_coeFn ℂ _ f).symm))
  have h := memKMethod_neumann_restrict_of_memKMethod Ω.toOpens hK
  rw [hR] at h
  exact (Ω.memKMethod_neumann_iff hθ hθ' hq).1 h

/-- **Besov spaces on Lipschitz domains by Neumann eigenfunction expansions**: for a bounded
Lipschitz domain `Ω` in dimension `n ≥ 1`, `0 < θ < 1`, `1 ≤ q ≤ ∞`, every order `r ≥ 1` and
every `f ∈ L_2(V)`, `f|_Ω` lies in the approximation space `A^θ_q` of the Neumann eigenbasis iff
`‖f‖_{L_2(Ω)} + ‖(2^(kθ) ω_r(f, 2^(-k), Ω)_2)_k‖_{ℓ_q} < ∞`, that is `f|_Ω ∈ B^θ_{2,q}(Ω)`
(`Rd.BoundedLipschitzDomain.modNormOn_lt_top_of_memApprox_neumannScheme`,
`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_of_modNormOn_lt_top`). -/
theorem memApprox_neumannScheme_iff {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    {r : ℕ} (hr : 1 ≤ r) (f : Lp ℂ 2 (volume : Measure V)) :
    Ω.neumannScheme.toScheme.MemApprox θ q
        (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f) ↔
      modNormOn Ω.measurableSet r θ q f < ∞ :=
  ⟨Ω.modNormOn_lt_top_of_memApprox_neumannScheme hθ hθ' hq hr,
    Ω.memApprox_neumannScheme_of_modNormOn_lt_top hθ hθ' hq
      (hθ'.trans_le (by exact_mod_cast hr))⟩

/-- **`B^θ_{2,q}(Ω)` by dyadic blocks of Neumann coefficients**: for a bounded Lipschitz domain
`Ω` in dimension `n ≥ 1`, `0 < θ < 1`, `1 ≤ q ≤ ∞`, every order `r ≥ 1` and every
`f ∈ L_2(V)`, the intrinsic quasi-norm `N_Ω(f)` is finite iff
`‖P_1 f‖ + ‖(2^(kθ) ‖Δ_k f‖)_k‖_{ℓ_q} < ∞` for the dyadic blocks `Δ_k f` of the expansion of
`f|_Ω` in the Neumann eigenbasis (`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`,
`SpectralScheme.memApprox_iff_blockNorm_lt_top`). -/
theorem modNormOn_lt_top_iff_blockNorm_lt_top {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1)
    (hq : 1 ≤ q) {r : ℕ} (hr : 1 ≤ r) (f : Lp ℂ 2 (volume : Measure V)) :
    modNormOn Ω.measurableSet r θ q f < ∞ ↔
      Ω.neumannScheme.projectionScheme.blockNorm θ q
        (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f) < ∞ := by
  rw [← Ω.memApprox_neumannScheme_iff hθ hθ' hq hr,
    Ω.neumannScheme.memApprox_iff_blockNorm_lt_top hθ hq]

/-- **`B^θ_{2,2}(Ω)` by Neumann eigenvalues**: for a bounded Lipschitz domain `Ω` in dimension
`n ≥ 1`, `0 < θ < 1`, every order `r ≥ 1` and every `f ∈ L_2(V)`, the intrinsic quasi-norm
`N_Ω(f)` with `q = 2` is finite iff `∑_i (1 + λ_i)^θ |⟨e_i, f|_Ω⟩|² < ∞`, that is, the sequence
`((1 + λ_i)^(θ/2) ⟨e_i, f|_Ω⟩)_i` lies in `ℓ_2`, with the Neumann eigenvalues `λ_i` and the
Neumann eigenbasis `(e_i)`
(`Rd.BoundedLipschitzDomain.memApprox_neumannScheme_iff`, `CompactDenseEmbedding.memApprox_two_iff`
and `1 + λ_i = σ_i⁻²`). -/
theorem modNormOn_two_lt_top_iff {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) {r : ℕ} (hr : 1 ≤ r)
    (f : Lp ℂ 2 (volume : Measure V)) :
    modNormOn Ω.measurableSet r θ 2 f < ∞ ↔
      Memℓp (fun i => (((1 + Ω.neumannEigenvalue i) ^ (θ / 2) : ℝ) : ℂ) *
        Ω.neumannScheme.basis.repr
          (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω.toOpens : Set V) f) i) 2 := by
  have h : ∀ i, (1 + Ω.neumannEigenvalue i) ^ (θ / 2) =
      (Ω.neumannCompactEmbedding.singularValue i)⁻¹ ^ θ := fun i => by
    rw [one_add_neumannEigenvalue, ← Real.rpow_natCast,
      ← Real.rpow_mul (inv_nonneg.2 (Ω.neumannCompactEmbedding.singularValue_pos i).le)]
    congr 1
    push_cast
    ring
  rw [← Ω.memApprox_neumannScheme_iff hθ hθ' one_le_two hr]
  simp only [h]
  exact Ω.neumannCompactEmbedding.memApprox_two_iff hθ _

end BoundedLipschitzDomain

/-! ### The Dirichlet eigenbasis and the zero extension -/

section Dirichlet

variable {Ω : Opens V}

/-- **Elements of `H^1_0(Ω)` are the zero extensions of their values on `Ω`**: for
`w ∈ H^1_0(Ω)`, the zero extension of `J w ∈ L_2(Ω)` is the `L_2` function of `w ∈ H^1(V)`,
which vanishes outside `Ω` (`Rd.toL2_ae_eq_zero_of_mem_zeroBoundarySpace`,
`Rd.indicatorExtendLp_restrict_of_ae_eq_zero`). -/
theorem indicatorExtendLp_dirichletEmbedding (w : zeroBoundarySpace 1 Ω) :
    indicatorExtendLp Ω.isOpen.measurableSet subset_rfl (dirichletEmbedding Ω w) =
      toL2 ((w : RestrictionSpace 1 Ω) : H^{1}(V)) := by
  rw [dirichletEmbedding_apply, restrictL2_apply]
  exact indicatorExtendLp_restrict_of_ae_eq_zero Ω.isOpen.measurableSet
    (toL2_ae_eq_zero_of_mem_zeroBoundarySpace w)

/-- **The zero extension maps the Dirichlet couple into `(L_2(V), H^1(V))`**: for an open set
`Ω`, if `g ∈ L_2(Ω)` lies in `(L_2(Ω), H^1_0(Ω))_{θ,q}`, then its zero extension lies in the real
interpolation space `(L_2(V), H^1(V))_{θ,q}` of the `L_2` norm and the Bessel potential norm
(`Rd.lpBesselPotentialCouple 1`). The couple is that of the embedding `H^1(V) → L_2(V)`
(`Rd.ofMap_toL2_eq_lpBesselPotentialCouple`), and the zero extension maps `J w` to `ι w` for
`w ∈ H^1_0(Ω)` (`Rd.indicatorExtendLp_dirichletEmbedding`), so the interpolation property for
compatible maps applies (`ApproximationScheme.MemKMethod.map`). -/
theorem memKMethod_indicatorExtendLp_of_memKMethod_dirichlet {θ : ℝ} {q : ℝ≥0∞}
    {g : Lp ℂ 2 (volume.restrict (Ω : Set V))}
    (hg : (InterpCouple.ofMap ((dirichletEmbedding Ω).restrictScalars ℝ)).MemKMethod θ q g) :
    (lpBesselPotentialCouple (p := 2) 1).MemKMethod θ q
      (indicatorExtendLp Ω.isOpen.measurableSet subset_rfl g) := by
  rw [← ofMap_toL2_eq_lpBesselPotentialCouple]
  refine InterpCouple.memKMethod_ofMap_iff.2 (ApproximationScheme.MemKMethod.map
    ((indicatorExtendLp (p := 2) (μ := volume) Ω.isOpen.measurableSet subset_rfl).restrictScalars ℝ)
    ((((vanishOn 1 Ω)ᗮ.subtypeL).comp (zeroBoundarySpace 1 Ω).subtypeL).restrictScalars ℝ)
    ?_ (InterpCouple.memKMethod_ofMap_iff.1 hg))
  ext1 w
  exact indicatorExtendLp_dirichletEmbedding w

variable [Nontrivial V]

/-- **Dirichlet approximation spaces in `B^θ_{2,q}(V)`**: for a bounded open set `Ω` in
dimension `n ≥ 1`, `0 < θ < 1` and `1 ≤ q ≤ ∞`, if `g ∈ L_2(Ω)` lies in the approximation space
`A^θ_q` of the Dirichlet scheme, then its zero extension lies in the approximation space `A^θ_q`
of the band-limited functions, the Besov space `B^θ_{2,q}(V)`. `A^θ_q` is
`(L_2(Ω), H^1_0(Ω))_{θ,q}` (`Rd.memKMethod_dirichlet_iff`), the zero extension maps it into
`(L_2(V), H^1(V))_{θ,q}` (`Rd.memKMethod_indicatorExtendLp_of_memKMethod_dirichlet`), and this
is `B^θ_{2,q}(V)` (`Rd.memKMethod_lpBesselPotentialCouple_iff`). -/
theorem memApprox_bandScheme_extendByZero_of_memApprox_dirichletScheme
    (hΩ : Bornology.IsBounded (Ω : Set V)) {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1)
    (hq : 1 ≤ q) {g : Lp ℂ 2 (volume.restrict (Ω : Set V))}
    (hg : (dirichletScheme hΩ).toScheme.MemApprox θ q g) :
    (bandScheme (V := V) two_ne_top).MemApprox θ q
      (indicatorExtendLp Ω.isOpen.measurableSet subset_rfl g) := by
  have h := (memKMethod_lpBesselPotentialCouple_iff ENNReal.one_lt_two two_ne_top one_pos hθ hθ'
    hq).1 (memKMethod_indicatorExtendLp_of_memKMethod_dirichlet
      ((memKMethod_dirichlet_iff hΩ hθ hθ' hq).2 hg))
  rwa [mul_one] at h

/-- **Dirichlet approximation spaces lie in the intrinsic Besov space**: for a bounded open set
`Ω` in dimension `n ≥ 1`, `0 < θ < 1`, `1 ≤ q ≤ ∞` and every order `r > θ` (for natural `r` and
`θ > 0` this is `r ≥ 1`), if `f|_Ω` lies in the approximation space `A^θ_q` of the Dirichlet
scheme, then the intrinsic quasi-norm `N_Ω(f)` with moduli of order `r` is finite: the zero
extension of `f|_Ω` lies in `B^θ_{2,q}(V)`
(`Rd.memApprox_bandScheme_extendByZero_of_memApprox_dirichletScheme`,
`Rd.memApprox_bandScheme_iff_modulus`) and agrees with `f` on `Ω`
(`Rd.modNormOn_le_modNorm_of_indicatorLp`). -/
theorem modNormOn_lt_top_of_memApprox_dirichletScheme (hΩ : Bornology.IsBounded (Ω : Set V))
    {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q) {r : ℕ} (hθr : θ < r)
    {f : Lp ℂ 2 (volume : Measure V)}
    (hf : (dirichletScheme hΩ).toScheme.MemApprox θ q
      (LpToLpRestrictCLM V ℂ ℂ volume 2 (Ω : Set V) f)) :
    modNormOn Ω.isOpen.measurableSet r θ q f < ∞ :=
  (modNormOn_le_modNorm_of_indicatorLp Ω.isOpen.measurableSet r θ q
    (indicatorLp_indicatorExtendLp_restrict Ω.isOpen.measurableSet f)).trans_lt
    ((memApprox_bandScheme_iff_modulus two_ne_top hθ.le hθr hq _).1
      (memApprox_bandScheme_extendByZero_of_memApprox_dirichletScheme hΩ hθ hθ' hq hf))

end Dirichlet

end Rd
