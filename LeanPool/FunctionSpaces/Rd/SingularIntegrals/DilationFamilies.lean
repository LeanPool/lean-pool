/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.LocalMeans.KernelMajorants
public import LeanPool.FunctionSpaces.Rd.Approximation.BandInverse
public import LeanPool.FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels
public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTwoLittlewoodPaley
public import LeanPool.FunctionSpaces.Analysis.Lp.MixedNorms
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Dyadic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Dilation families of Schwartz kernels and the Hörmander condition

On a finite-dimensional real inner product space `V` of dimension `n` with Lebesgue measure, the
kernels of the vector-valued singular integrals of this project are families
`θ_j = (G_j)_{2^j}`, `j ∈ ℕ`, of dilated Schwartz functions `G_j` whose Schwartz seminorms are
bounded uniformly in `j` (`Rd.IsUniformSchwartz`). Two numbers control such a family
(`Rd.IsCZFamily`): the **Fourier overlap** `B` with `∑_j |𝓕θ_j(ξ)|² ≤ B` for every `ξ`, and the
**Hörmander constant** `H` with
`∫_{‖x‖ > 2‖y‖} ‖(θ_j(x - y) - θ_j(x))_j‖_{ℓ_2} dx ≤ H` for every `y`. Here
`δ_c F = F_c`, `F_c(x) = c^n F(c x)`, is the dilation by `c` (`Rd.dilate`), so that the
Littlewood–Paley kernels are `Φ_k = δ_{2^k} Φ`.

* **Schwartz forms of dilation, reflection and conjugation** (`Rd.schwartzDilate`,
  `Rd.schwartzReflect`, `Rd.schwartzConj`), with `𝓕(G_c)(ξ) = 𝓕G(c⁻¹ ξ)`
  (`Rd.fourier_schwartzDilate_apply`) and the chain rule
  `∂_{w_0} ⋯ ∂_{w_{k-1}} (G_c) = c^k (∂_{w_0} ⋯ ∂_{w_{k-1}} G)_c` for dilations
  (`Rd.iteratedLineDerivOp_schwartzDilate`).
* **One dilate** (`Rd.setLIntegral_enorm_dilate_sub_le_min`): the Hörmander integral of
  `G_{2^j}` is at most `H_G min(2^j ‖y‖, (2^j ‖y‖)⁻¹)` with the explicit `H_G`
  (`Rd.hormanderConst`): for short steps the `L_1` norm of the difference is at most the step
  times the `L_1` norm of the gradient (`Rd.lintegral_enorm_dilate_sub_le_mul`, constant
  `Rd.gradMassConst`), for long steps both terms are tails
  (`Rd.setLIntegral_enorm_dilate_sub_le_inv`).
* **Uniform families**: with the dyadic sum `∑_j min(2^j a, (2^j a)⁻¹) ≤ 4`
  (`ENNReal.tsum_min_two_pow_le`), the Hörmander condition holds for every uniform
  family with `H = 4 H_A` (`Rd.lintegral_lqNorm_sub_le`, `Rd.familyHormanderConst`), and
  `Rd.IsCZFamily.of_dilation`; finitely many members of a uniform family may be changed
  (`Rd.IsUniformSchwartz.of_forall_ge_eq`), also in a Calderón–Zygmund family of dilates
  (`Rd.IsCZFamily.of_dilation_of_forall_ge_eq`, with `ENNReal.tsum_le_tsum_add_sum_of_forall_ge_eq`
  for the overlap).
* **Adjoints**: `θ_j^*(x) = conj θ_j(-x)` has the same overlap and Hörmander constants
  (`Rd.IsCZFamily.adjoint`).
* **The Littlewood–Paley families**: the blocks `ψ_j = (psiBase j)_{2^j}`, Schwartz functions
  (`Rd.psiS`), with overlap `2` (`Rd.isCZFamily_psi`), and the synthesis kernels `Rd.psiDual`
  with `psiDual_j ⋆ ψ_j = ψ_j` (`Rd.conv_psiDual_psi`, `Rd.isCZFamily_psiDual`, overlap `4`).
-/

@[expose] public section

open MeasureTheory Module Metric Filter Set ComplexConjugate
open scoped ENNReal SchwartzMap FourierTransform LineDeriv

namespace Rd

open ENNReal (lqNorm)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Dilation, reflection and conjugation of Schwartz functions -/

/-- The **dilation of a Schwartz function**: for `c ≠ 0`, the function
`G_c(x) = c^n G(c x)` is a Schwartz function, the composition of `G` with the linear
equivalence `x ↦ c x` (Mathlib's `SchwartzMap.compCLMOfContinuousLinearEquiv`) times `c^n`. -/
noncomputable def schwartzDilate (c : ℝ) (hc : c ≠ 0) (G : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  (((c ^ finrank ℝ V : ℝ)) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc)) G

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Schwartz dilation is the dilation `Rd.dilate`. -/
theorem coe_schwartzDilate (c : ℝ) (hc : c ≠ 0) (G : 𝓢(V, ℂ)) :
    (schwartzDilate c hc G : V → ℂ) = dilate c G := by
  funext x
  simp [schwartzDilate, dilate, Units.smul_def]

/-- The Fourier transform of a dilate: `𝓕(G_c)(ξ) = 𝓕G(c⁻¹ ξ)` for a Schwartz function `G` and
`c > 0` (`Rd.fourier_dilate`). -/
theorem fourier_schwartzDilate_apply {c : ℝ} (hc : 0 < c) (G : 𝓢(V, ℂ)) (ξ : V) :
    (𝓕 (schwartzDilate c hc.ne' G) : 𝓢(V, ℂ)) ξ = (𝓕 G : 𝓢(V, ℂ)) (c⁻¹ • ξ) := by
  rw [SchwartzMap.fourier_coe, coe_schwartzDilate, fourier_dilate _ hc, SchwartzMap.fourier_coe]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The dilation of Schwartz functions is additive: `(∑_i G_i)_c = ∑_i (G_i)_c`. -/
theorem schwartzDilate_sum {ι : Type*} (s : Finset ι) (c : ℝ) (hc : c ≠ 0) (G : ι → 𝓢(V, ℂ)) :
    schwartzDilate c hc (∑ i ∈ s, G i) = ∑ i ∈ s, schwartzDilate c hc (G i) := by
  simp only [schwartzDilate, map_sum, Finset.smul_sum]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The chain rule for dilations**: `∂_v (G_c) = c (∂_v G)_c` for every Schwartz function `G`
and every `c ≠ 0`, from Mathlib's `SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv` and
`∂_{c v} = c ∂_v`. -/
theorem lineDerivOp_schwartzDilate (c : ℝ) (hc : c ≠ 0) (G : 𝓢(V, ℂ)) (v : V) :
    ∂_{v} (schwartzDilate c hc G) = (c : ℂ) • schwartzDilate c hc (∂_{v} G) := by
  unfold schwartzDilate
  rw [LineDeriv.lineDerivOp_smul, SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    show (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc)) v = c • v from rfl,
    LineDeriv.lineDerivOp_left_smul, smul_comm]
  congr 1

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Iterated derivatives of dilations**: for directions `w ∈ V^k`,
`∂_{w_0} ⋯ ∂_{w_{k-1}} (G_c) = c^k (∂_{w_0} ⋯ ∂_{w_{k-1}} G)_c`. -/
theorem iteratedLineDerivOp_schwartzDilate (c : ℝ) (hc : c ≠ 0) (G : 𝓢(V, ℂ)) {k : ℕ}
    (w : Fin k → V) :
    ∂^{w} (schwartzDilate c hc G) = ((c : ℂ) ^ k) • schwartzDilate c hc (∂^{w} G) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ih, LineDeriv.lineDerivOp_smul,
      lineDerivOp_schwartzDilate, smul_smul, ← pow_succ, ← LineDeriv.iteratedLineDerivOp_succ_left]

/-- The **reflection of a Schwartz function**, `x ↦ G(-x)`. -/
noncomputable def schwartzReflect (G : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) G

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Schwartz reflection is `x ↦ G(-x)`. -/
theorem coe_schwartzReflect (G : 𝓢(V, ℂ)) :
    (schwartzReflect G : V → ℂ) = fun x => G (-x) := by
  funext x
  simp [schwartzReflect]

/-- The **complex conjugate of a Schwartz function**, `x ↦ conj G(x)` (Mathlib's
`SchwartzMap.postcompCLM` with the real-linear conjugation). -/
noncomputable def schwartzConj (G : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap G

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Schwartz conjugate is `x ↦ conj G(x)`. -/
theorem coe_schwartzConj (G : 𝓢(V, ℂ)) :
    (schwartzConj G : V → ℂ) = fun x => conj (G x) := by
  funext x
  simp [schwartzConj]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Dilations are linear: `(F - G)_c = F_c - G_c`. -/
theorem dilate_sub (c : ℝ) (F G : V → ℂ) : dilate c (F - G) = dilate c F - dilate c G := by
  funext x
  simp only [dilate, Pi.sub_apply, mul_sub]

/-! ### Uniform Schwartz families -/

/-- A family `(G_j)_{j ∈ ℕ}` of Schwartz functions is **uniformly Schwartz with bounds `A`** if
every Schwartz seminorm `sup_x ‖x‖^k ‖D^l G_j(x)‖` is at most `A k l`, for every `j`. -/
def IsUniformSchwartz (G : ℕ → 𝓢(V, ℂ)) (A : ℕ → ℕ → ℝ) : Prop :=
  ∀ j k l, SchwartzMap.seminorm ℝ k l (G j) ≤ A k l

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A family taking only the two values `G₀` and `G₁` is uniformly Schwartz, with the larger of
the two seminorms as bounds. -/
theorem IsUniformSchwartz.of_forall_eq_or_eq {G : ℕ → 𝓢(V, ℂ)} {G₀ G₁ : 𝓢(V, ℂ)}
    (h : ∀ j, G j = G₀ ∨ G j = G₁) :
    IsUniformSchwartz G fun k l =>
      max (SchwartzMap.seminorm ℝ k l G₀) (SchwartzMap.seminorm ℝ k l G₁) := by
  intro j k l
  rcases h j with hj | hj <;> rw [hj]
  · exact le_max_left _ _
  · exact le_max_right _ _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A constant family `j ↦ G` is uniformly Schwartz, with the seminorms of `G` as bounds. -/
theorem IsUniformSchwartz.const (G : 𝓢(V, ℂ)) :
    IsUniformSchwartz (fun _ => G) fun k l => SchwartzMap.seminorm ℝ k l G :=
  fun _ _ _ => le_rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A family taking its values in a finite nonempty set `s` of Schwartz functions is uniformly
Schwartz, with the largest seminorm over `s` as bounds. -/
theorem IsUniformSchwartz.of_forall_mem {G : ℕ → 𝓢(V, ℂ)} {s : Finset 𝓢(V, ℂ)}
    (hs : s.Nonempty) (h : ∀ j, G j ∈ s) :
    IsUniformSchwartz G fun k l => s.sup' hs fun g => SchwartzMap.seminorm ℝ k l g :=
  fun j k l => Finset.le_sup' (fun g => SchwartzMap.seminorm ℝ k l g) (h j)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The seminorm bounds `A k l` of a uniform family are nonnegative, since they dominate a
seminorm. -/
theorem IsUniformSchwartz.nonneg {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ} (h : IsUniformSchwartz G A)
    (k l : ℕ) : 0 ≤ A k l :=
  (apply_nonneg _ _).trans (h 0 k l)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Finitely many exceptions**: a family `(G'_j)` that agrees with a uniform family `(G_j)` for
`j ≥ N` is uniformly Schwartz, with the bounds `max(A_{k,l}, ∑_{i < N} ‖G'_i‖_{k,l})`. -/
theorem IsUniformSchwartz.of_forall_ge_eq {G G' : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) {N : ℕ} (hG : ∀ j, N ≤ j → G' j = G j) :
    IsUniformSchwartz G' fun k l =>
      max (A k l) (∑ i ∈ Finset.range N, SchwartzMap.seminorm ℝ k l (G' i)) := by
  intro j k l
  by_cases hj : N ≤ j
  · rw [hG j hj]
    exact (h j k l).trans (le_max_left _ _)
  · exact le_max_of_le_right (Finset.single_le_sum (f := fun i => SchwartzMap.seminorm ℝ k l (G' i))
      (fun _ _ => apply_nonneg _ _) (Finset.mem_range.2 (not_le.1 hj)))

/-- The decay constant `2^N (A_{0,r} + A_{N,r})` of a uniform family, the analogue of
`Rd.schwartzDecayConst` with the seminorms replaced by their bounds. -/
noncomputable def familyDecayConst (A : ℕ → ℕ → ℝ) (r N : ℕ) : ℝ≥0∞ :=
  2 ^ N * ENNReal.ofReal (A 0 r + A N r)

/-- The decay constant of a uniform family is finite. -/
theorem familyDecayConst_ne_top (A : ℕ → ℕ → ℝ) (r N : ℕ) : familyDecayConst A r N ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Every member of a uniform family has decay constant at most that of the family. -/
theorem schwartzDecayConst_le_familyDecayConst {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) (j r N : ℕ) :
    schwartzDecayConst (G j) r N ≤ familyDecayConst A r N := by
  unfold schwartzDecayConst familyDecayConst
  gcongr
  · exact h j 0 r
  · exact h j N r

variable (V) in
/-- The tail constant `C_{A,0,N+r+n+1} I_{n+1}` of a uniform family, the analogue of
`Rd.tailConst`. -/
noncomputable def familyTailConst (A : ℕ → ℕ → ℝ) (r N : ℕ) : ℝ≥0∞ :=
  familyDecayConst A 0 (N + r + finrank ℝ V + 1) * peetreIntegral V (finrank ℝ V + 1)

/-- The tail constant of a uniform family is finite. -/
theorem familyTailConst_ne_top (A : ℕ → ℕ → ℝ) (r N : ℕ) : familyTailConst V A r N ≠ ∞ :=
  ENNReal.mul_ne_top (familyDecayConst_ne_top _ _ _) (peetreIntegral_ne_top (Nat.lt_succ_self _))

/-- Every member of a uniform family has tail constant at most that of the family. -/
theorem tailConst_le_familyTailConst {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) (j r N : ℕ) : tailConst (G j) r N ≤ familyTailConst V A r N := by
  unfold tailConst familyTailConst
  gcongr
  exact schwartzDecayConst_le_familyDecayConst h j 0 _

/-! ### The gradient mass -/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Decay of the derivatives of a Schwartz function**:
`‖D^r G(x)‖ ≤ C_{G,r,N} (1 + ‖x‖)^(-N)` with `C_{G,r,N} = Rd.schwartzDecayConst G r N`. -/
theorem enorm_iteratedFDeriv_schwartz_le (G : 𝓢(V, ℂ)) (r N : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ₑ ≤ schwartzDecayConst G r N * ((1 + ‖x‖ₑ) ^ N)⁻¹ := by
  have h := one_add_norm_pow_mul_le_schwartz G r N x
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ N := by positivity
  have h' : ‖iteratedFDeriv ℝ r (G : V → ℂ) x‖ ≤
      2 ^ N * (SchwartzMap.seminorm ℝ 0 r G + SchwartzMap.seminorm ℝ N r G) *
        ((1 + ‖x‖) ^ N)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact h
  have e3 : ENNReal.ofReal (((1 + ‖x‖) ^ N)⁻¹) = ((1 + ‖x‖ₑ) ^ N)⁻¹ := by
    have h3 := ofReal_inv_one_add_mul_norm_pow zero_le_one x N
    rwa [one_mul, ENNReal.ofReal_one, one_mul] at h3
  rw [← ofReal_norm]
  refine (ENNReal.ofReal_le_ofReal h').trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, e3, schwartzDecayConst]

/-- The **gradient mass** `C_{G,1,n+1} I_{n+1}` of a Schwartz function `G`, a bound for
`∫ ‖DG‖`. -/
noncomputable def gradMassConst (G : 𝓢(V, ℂ)) : ℝ≥0∞ :=
  schwartzDecayConst G 1 (finrank ℝ V + 1) * peetreIntegral V (finrank ℝ V + 1)

/-- The gradient mass of a Schwartz function is finite. -/
theorem gradMassConst_ne_top (G : 𝓢(V, ℂ)) : gradMassConst G ≠ ∞ :=
  ENNReal.mul_ne_top (schwartzDecayConst_ne_top _ _ _) (peetreIntegral_ne_top (Nat.lt_succ_self _))

/-- **`L_1` norms of directional derivatives**: `∫ |∂_v G| ≤ ‖v‖ M_G` with the gradient mass
`M_G = Rd.gradMassConst G`. -/
theorem lintegral_enorm_lineDerivOp_le (v : V) (G : 𝓢(V, ℂ)) :
    ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ ≤ ‖v‖ₑ * gradMassConst G := by
  have hpt : ∀ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ ≤ ‖v‖ₑ * schwartzDecayConst G 1 (finrank ℝ V + 1) *
      ((1 + ‖x‖ₑ) ^ (finrank ℝ V + 1))⁻¹ := fun x => by
    have h1 := enorm_iteratedLineDerivOp_le v 1 G x
    rw [LineDeriv.iteratedLineDerivOp_one, pow_one] at h1
    calc ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ ≤ ‖v‖ₑ * ‖iteratedFDeriv ℝ 1 (G : V → ℂ) x‖ₑ := h1
      _ ≤ ‖v‖ₑ * (schwartzDecayConst G 1 (finrank ℝ V + 1) *
            ((1 + ‖x‖ₑ) ^ (finrank ℝ V + 1))⁻¹) := by
          gcongr
          exact enorm_iteratedFDeriv_schwartz_le G 1 _ x
      _ = _ := by ring
  calc ∫⁻ x, ‖(∂_{v} G : 𝓢(V, ℂ)) x‖ₑ
      ≤ ∫⁻ x, ‖v‖ₑ * schwartzDecayConst G 1 (finrank ℝ V + 1) *
          ((1 + ‖x‖ₑ) ^ (finrank ℝ V + 1))⁻¹ := lintegral_mono hpt
    _ = ‖v‖ₑ * schwartzDecayConst G 1 (finrank ℝ V + 1) * peetreIntegral V (finrank ℝ V + 1) :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top eNorm_ne_top (schwartzDecayConst_ne_top _ _ _))
    _ = ‖v‖ₑ * gradMassConst G := by rw [gradMassConst, mul_assoc]

variable (V) in
/-- The gradient mass `C_{A,1,n+1} I_{n+1}` of a uniform family. -/
noncomputable def familyGradMass (A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  familyDecayConst A 1 (finrank ℝ V + 1) * peetreIntegral V (finrank ℝ V + 1)

/-- The gradient mass of a uniform family is finite. -/
theorem familyGradMass_ne_top (A : ℕ → ℕ → ℝ) : familyGradMass V A ≠ ∞ :=
  ENNReal.mul_ne_top (familyDecayConst_ne_top _ _ _) (peetreIntegral_ne_top (Nat.lt_succ_self _))

/-- Every member of a uniform family has gradient mass at most that of the family. -/
theorem gradMassConst_le_familyGradMass {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) (j : ℕ) : gradMassConst (G j) ≤ familyGradMass V A := by
  unfold gradMassConst familyGradMass
  gcongr
  exact schwartzDecayConst_le_familyDecayConst h j 1 _

/-! ### The Hörmander bound for one dilate -/

/-- **Short steps**: `∫ |G_{2^j}(x - y) - G_{2^j}(x)| dx ≤ M_G 2^j ‖y‖` with the gradient mass
`M_G = Rd.gradMassConst G`: the difference is the dilate of the difference of `G` with step
`-2^j y` (`Rd.higherDiff_dilate`), dilations keep `L_1` norms, and a difference is at most the
directional derivative in `L_1` (`Rd.lintegral_enorm_fwdDiff_le`). -/
theorem lintegral_enorm_dilate_sub_le_mul (G : 𝓢(V, ℂ)) (j : ℕ) (y : V) :
    ∫⁻ x, ‖dilate (2 ^ j) G (x - y) - dilate (2 ^ j) G x‖ₑ ≤
      gradMassConst G * (2 ^ j * ‖y‖ₑ) := by
  have hdiff : ∀ x, dilate (2 ^ j) (G : V → ℂ) (x - y) - dilate (2 ^ j) G x =
      dilate (2 ^ j) (fwdDiff (((2 : ℝ) ^ j) • -y) (G : V → ℂ)) x := fun x => by
    have h := higherDiff_dilate 1 ((2 : ℝ) ^ j) (-y) (G : V → ℂ)
    simp only [Function.iterate_one] at h
    rw [← h]
    simp [fwdDiff, sub_eq_add_neg]
  calc ∫⁻ x, ‖dilate (2 ^ j) (G : V → ℂ) (x - y) - dilate (2 ^ j) G x‖ₑ
      = ∫⁻ x, ‖dilate (2 ^ j) (fwdDiff (((2 : ℝ) ^ j) • -y) (G : V → ℂ)) x‖ₑ :=
        lintegral_congr fun x => by rw [hdiff x]
    _ = ∫⁻ x, ‖fwdDiff (((2 : ℝ) ^ j) • -y) (G : V → ℂ) x‖ₑ :=
        lintegral_enorm_dilate _ (by positivity)
    _ ≤ ∫⁻ x, ‖(∂_{((2 : ℝ) ^ j) • -y} G : 𝓢(V, ℂ)) x‖ₑ := lintegral_enorm_fwdDiff_le _ G
    _ ≤ ‖((2 : ℝ) ^ j) • -y‖ₑ * gradMassConst G := lintegral_enorm_lineDerivOp_le _ G
    _ = _ := by rw [enorm_two_pow_smul, eNorm_neg, mul_comm]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `(1 + 2^j ‖y‖)^(-1) ≤ (2^j ‖y‖)^(-1)` in `[0, ∞]`. -/
theorem inv_one_add_ofReal_two_pow_mul_le (j : ℕ) (y : V) :
    (1 + ENNReal.ofReal (2 ^ j * ‖y‖))⁻¹ ≤ (2 ^ j * ‖y‖ₑ)⁻¹ := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat, ofReal_norm]
  exact ENNReal.inv_le_inv.2 le_add_self

/-- `(1 + 2^j)^(-1) ≤ 2^(-j)` in `[0, ∞]`, written in the form `((1 + ofReal (2^j · 1))^1)^(-1)`
of the tail bound `Rd.setLIntegral_enorm_dilate_schwartz_le` at radius `1` and order `1`. -/
theorem inv_one_add_ofReal_two_pow_le (j : ℕ) :
    ((1 + ENNReal.ofReal (2 ^ j * 1)) ^ 1)⁻¹ ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
  rw [mul_one, pow_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, ← ENNReal.inv_pow]
  exact ENNReal.inv_le_inv.2 le_add_self

/-- **Long steps**: `∫_{‖x‖ > 2‖y‖} |G_{2^j}(x - y) - G_{2^j}(x)| dx ≤ 2 T_G (2^j ‖y‖)^(-1)` with
`T_G = Rd.tailConst G 0 1`: both `x` and `x - y` lie outside the ball of radius `‖y‖`, where the
mass of `G_{2^j}` is at most `T_G (1 + 2^j ‖y‖)^(-1)`
(`Rd.setLIntegral_enorm_dilate_schwartz_le`). -/
theorem setLIntegral_enorm_dilate_sub_le_inv (G : 𝓢(V, ℂ)) (j : ℕ) (y : V) :
    ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) G (x - y) - dilate (2 ^ j) G x‖ₑ ≤
      2 * tailConst G 0 1 * (2 ^ j * ‖y‖ₑ)⁻¹ := by
  have hS : MeasurableSet {x : V | 2 * ‖y‖ < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hT : MeasurableSet {z : V | ‖y‖ ≤ ‖z‖} := measurableSet_le measurable_const measurable_norm
  have hc : Continuous (dilate (2 ^ j) (G : V → ℂ)) := continuous_dilate G.continuous _
  have htail : ∫⁻ z in {z : V | ‖y‖ ≤ ‖z‖}, ‖dilate (2 ^ j) (G : V → ℂ) z‖ₑ ≤
      tailConst G 0 1 * (2 ^ j * ‖y‖ₑ)⁻¹ := by
    have h := setLIntegral_enorm_dilate_schwartz_le G 1 j ‖y‖
    rw [pow_one] at h
    exact h.trans (mul_le_mul_right (inv_one_add_ofReal_two_pow_mul_le j y) _)
  have h1 : ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) (G : V → ℂ) x‖ₑ ≤
      ∫⁻ z in {z : V | ‖y‖ ≤ ‖z‖}, ‖dilate (2 ^ j) (G : V → ℂ) z‖ₑ :=
    lintegral_mono_set fun x (hx : 2 * ‖y‖ < ‖x‖) => by
      change ‖y‖ ≤ ‖x‖
      linarith [norm_nonneg y]
  have h2 : ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) (G : V → ℂ) (x - y)‖ₑ ≤
      ∫⁻ z in {z : V | ‖y‖ ≤ ‖z‖}, ‖dilate (2 ^ j) (G : V → ℂ) z‖ₑ := by
    rw [← lintegral_indicator hS, ← lintegral_indicator hT]
    calc ∫⁻ x, {x : V | 2 * ‖y‖ < ‖x‖}.indicator
          (fun x => ‖dilate (2 ^ j) (G : V → ℂ) (x - y)‖ₑ) x
        ≤ ∫⁻ x, {z : V | ‖y‖ ≤ ‖z‖}.indicator
          (fun z => ‖dilate (2 ^ j) (G : V → ℂ) z‖ₑ) (x - y) := lintegral_mono fun x => by
          by_cases hx : x ∈ {x : V | 2 * ‖y‖ < ‖x‖}
          · have hxy : x - y ∈ {z : V | ‖y‖ ≤ ‖z‖} := by
              have hx' : 2 * ‖y‖ < ‖x‖ := hx
              change ‖y‖ ≤ ‖x - y‖
              linarith [norm_sub_norm_le x y]
            rw [indicator_of_mem hx, indicator_of_mem hxy]
          · rw [indicator_of_notMem hx]
            exact zero_le
      _ = _ := lintegral_sub_right_eq_self _ y
  calc ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) G (x - y) - dilate (2 ^ j) G x‖ₑ
      ≤ ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖},
          (‖dilate (2 ^ j) (G : V → ℂ) (x - y)‖ₑ + ‖dilate (2 ^ j) (G : V → ℂ) x‖ₑ) :=
        lintegral_mono fun x => eNorm_sub_le
    _ = (∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) (G : V → ℂ) (x - y)‖ₑ) +
          ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) (G : V → ℂ) x‖ₑ :=
        lintegral_add_right _ hc.eNorm.measurable
    _ ≤ tailConst G 0 1 * (2 ^ j * ‖y‖ₑ)⁻¹ + tailConst G 0 1 * (2 ^ j * ‖y‖ₑ)⁻¹ :=
        add_le_add (h2.trans htail) (h1.trans htail)
    _ = _ := by ring

/-- The **Hörmander constant** `M_G + 2 T_G` of a Schwartz function `G`, with the gradient mass
`M_G = Rd.gradMassConst G` and the tail constant `T_G = Rd.tailConst G 0 1`. -/
noncomputable def hormanderConst (G : 𝓢(V, ℂ)) : ℝ≥0∞ := gradMassConst G + 2 * tailConst G 0 1

/-- The Hörmander constant of a Schwartz function is finite. -/
theorem hormanderConst_ne_top (G : 𝓢(V, ℂ)) : hormanderConst G ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨gradMassConst_ne_top G,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (tailConst_ne_top G 0 1)⟩

/-- **The Hörmander bound for one dilate**: for every Schwartz function `G`, `j ∈ ℕ` and
`y ∈ V`,
`∫_{‖x‖ > 2‖y‖} |G_{2^j}(x - y) - G_{2^j}(x)| dx ≤ H_G min(2^j ‖y‖, (2^j ‖y‖)⁻¹)` with
`H_G = Rd.hormanderConst G`; at `y = 0` both sides vanish, since `0⁻¹ = ∞` in `[0, ∞]`. -/
theorem setLIntegral_enorm_dilate_sub_le_min (G : 𝓢(V, ℂ)) (j : ℕ) (y : V) :
    ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖}, ‖dilate (2 ^ j) G (x - y) - dilate (2 ^ j) G x‖ₑ ≤
      hormanderConst G * min (2 ^ j * ‖y‖ₑ) (2 ^ j * ‖y‖ₑ)⁻¹ := by
  rcases le_or_gt (2 ^ j * ‖y‖ₑ) 1 with h | h
  · rw [min_eq_left (h.trans (ENNReal.one_le_inv.2 h))]
    calc _ ≤ ∫⁻ x, ‖dilate (2 ^ j) (G : V → ℂ) (x - y) - dilate (2 ^ j) G x‖ₑ :=
          setLIntegral_le_lintegral _ _
      _ ≤ gradMassConst G * (2 ^ j * ‖y‖ₑ) := lintegral_enorm_dilate_sub_le_mul G j y
      _ ≤ hormanderConst G * (2 ^ j * ‖y‖ₑ) := by
          gcongr
          exact le_self_add
  · rw [min_eq_right ((ENNReal.inv_lt_one.2 h).le.trans h.le)]
    calc _ ≤ 2 * tailConst G 0 1 * (2 ^ j * ‖y‖ₑ)⁻¹ := setLIntegral_enorm_dilate_sub_le_inv G j y
      _ ≤ hormanderConst G * (2 ^ j * ‖y‖ₑ)⁻¹ := by
          gcongr
          exact le_add_self

/-! ### The Hörmander condition for uniform families -/

variable (V) in
/-- The **Hörmander constant of a uniform family**, `M_A + 2 T_A` with the gradient mass
`M_A = Rd.familyGradMass V A` and the tail constant `T_A = Rd.familyTailConst V A 0 1`. -/
noncomputable def familyHormanderConst (A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  familyGradMass V A + 2 * familyTailConst V A 0 1

/-- The Hörmander constant of a uniform family is finite. -/
theorem familyHormanderConst_ne_top (A : ℕ → ℕ → ℝ) : familyHormanderConst V A ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨familyGradMass_ne_top A,
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyTailConst_ne_top A 0 1)⟩

/-- Every member of a uniform family has Hörmander constant at most that of the family. -/
theorem hormanderConst_le_familyHormanderConst {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    (h : IsUniformSchwartz G A) (j : ℕ) : hormanderConst (G j) ≤ familyHormanderConst V A := by
  unfold hormanderConst familyHormanderConst
  gcongr
  · exact gradMassConst_le_familyGradMass h j
  · exact tailConst_le_familyTailConst h j 0 1

/-- **The Hörmander condition for dilation families**: for a uniform family `(G_j)` with bounds
`A` and every `y ∈ V`,
`∫_{‖x‖ > 2‖y‖} ‖((G_j)_{2^j}(x - y) - (G_j)_{2^j}(x))_j‖_{ℓ_2} dx ≤ 4 H_A` with
`H_A = Rd.familyHormanderConst V A`. The `ℓ_2` norm is at most the `ℓ_1` norm
(`ENNReal.lqNorm_le_lqNorm_one`), each term is bounded by
`Rd.setLIntegral_enorm_dilate_sub_le_min`, and the dyadic sum by `ENNReal.tsum_min_two_pow_le`. -/
theorem lintegral_lqNorm_sub_le {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ} (h : IsUniformSchwartz G A)
    (y : V) :
    ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖},
        lqNorm 2 (fun j => ‖dilate (2 ^ j) (G j) (x - y) - dilate (2 ^ j) (G j) x‖ₑ) ≤
      4 * familyHormanderConst V A := by
  have hmeas : ∀ j, AEMeasurable (fun x => ‖dilate (2 ^ j) (G j : V → ℂ) (x - y) -
      dilate (2 ^ j) (G j : V → ℂ) x‖ₑ) (volume.restrict {x : V | 2 * ‖y‖ < ‖x‖}) := fun j =>
    (((continuous_dilate (G j).continuous _).comp (continuous_id.sub continuous_const)).sub
      (continuous_dilate (G j).continuous _)).eNorm.measurable.aemeasurable
  calc ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖},
        lqNorm 2 (fun j => ‖dilate (2 ^ j) (G j) (x - y) - dilate (2 ^ j) (G j) x‖ₑ)
      ≤ ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖},
          ∑' j, ‖dilate (2 ^ j) (G j : V → ℂ) (x - y) - dilate (2 ^ j) (G j : V → ℂ) x‖ₑ :=
        lintegral_mono fun x => ENNReal.lqNorm_le_lqNorm_one one_le_two _
    _ = ∑' j, ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖},
          ‖dilate (2 ^ j) (G j : V → ℂ) (x - y) - dilate (2 ^ j) (G j : V → ℂ) x‖ₑ :=
        lintegral_tsum hmeas
    _ ≤ ∑' j : ℕ, familyHormanderConst V A * min (2 ^ j * ‖y‖ₑ) (2 ^ j * ‖y‖ₑ)⁻¹ :=
        tsum_le_tsum fun j => (setLIntegral_enorm_dilate_sub_le_min (G j) j y).trans
          (by gcongr; exact hormanderConst_le_familyHormanderConst h j)
    _ = familyHormanderConst V A * ∑' j : ℕ, min (2 ^ j * ‖y‖ₑ) (2 ^ j * ‖y‖ₑ)⁻¹ :=
        ENNReal.tsum_mul_left
    _ ≤ familyHormanderConst V A * 4 := by gcongr; exact ENNReal.tsum_min_two_pow_le _
    _ = 4 * familyHormanderConst V A := mul_comm _ _

/-! ### Calderón–Zygmund families -/

/-- A **Calderón–Zygmund family** `(θ_j)_{j ∈ ℕ}` of kernels on `V` with **Fourier overlap** `B`
and **Hörmander constant** `H`: the kernels are integrable, continuous and bounded with
integrable Fourier transforms, `∑_j |𝓕θ_j(ξ)|² ≤ B` for every `ξ`, and
`∫_{‖x‖ > 2‖y‖} ‖(θ_j(x - y) - θ_j(x))_j‖_{ℓ_2} dx ≤ H` for every `y`. -/
structure IsCZFamily (θ : ℕ → V → ℂ) (B H : ℝ≥0∞) : Prop where
  /-- Every kernel is integrable. -/
  integrable : ∀ j, Integrable (θ j)
  /-- Every kernel is continuous. -/
  continuous : ∀ j, Continuous (θ j)
  /-- Every kernel is bounded. -/
  bddAbove : ∀ j, BddAbove (Set.range fun x => ‖θ j x‖)
  /-- Every kernel has an integrable Fourier transform. -/
  integrable_fourier : ∀ j, Integrable (𝓕 (θ j))
  /-- The Fourier overlap: `∑_j |𝓕θ_j(ξ)|² ≤ B` for every `ξ`. -/
  overlap : ∀ ξ, ∑' j, ‖𝓕 (θ j) ξ‖ₑ ^ 2 ≤ B
  /-- The Hörmander condition with constant `H`. -/
  hormander : ∀ y, ∫⁻ x in {x : V | 2 * ‖y‖ < ‖x‖},
    lqNorm 2 (fun j => ‖θ j (x - y) - θ j x‖ₑ) ≤ H

/-- **Larger constants**: a Calderón–Zygmund family with overlap `B` and Hörmander constant `H`
is one with every larger overlap `B' ≥ B` and Hörmander constant `H' ≥ H`. -/
theorem IsCZFamily.mono {θ : ℕ → V → ℂ} {B H B' H' : ℝ≥0∞} (h : IsCZFamily θ B H)
    (hB : B ≤ B') (hH : H ≤ H') : IsCZFamily θ B' H' where
  integrable := h.integrable
  continuous := h.continuous
  bddAbove := h.bddAbove
  integrable_fourier := h.integrable_fourier
  overlap ξ := (h.overlap ξ).trans hB
  hormander y := (h.hormander y).trans hH

/-- **Fourier transform of the adjoint kernel**: `𝓕(conj θ(-·))(ξ) = conj 𝓕θ(ξ)`, from
`conj 𝓕θ = 𝓕⁻(conj θ)` (`Rd.conj_fourier_apply`) and `𝓕⁻ f = 𝓕(f(-·))` (Mathlib's
`Real.fourierInv_eq_fourier_comp_neg`). -/
theorem fourier_conj_comp_neg (θ : V → ℂ) (ξ : V) :
    𝓕 (fun x => conj (θ (-x))) ξ = conj (𝓕 θ ξ) := by
  rw [conj_fourier_apply, Real.fourierInv_eq_fourier_comp_neg]

/-- **Adjoint families**: if `(θ_j)` is a Calderón–Zygmund family with overlap `B` and Hörmander
constant `H`, so is `(θ_j^*)` with `θ_j^*(x) = conj θ_j(-x)`: the Fourier transforms are
conjugated, and the Hörmander integral is invariant under `x ↦ -x`, `y ↦ -y`. -/
theorem IsCZFamily.adjoint {θ : ℕ → V → ℂ} {B H : ℝ≥0∞} (h : IsCZFamily θ B H) :
    IsCZFamily (fun j x => conj (θ j (-x))) B H where
  integrable j := Complex.conjCLE.toContinuousLinearMap.integrable_comp (h.integrable j).comp_neg
  continuous j := Complex.continuous_conj.comp ((h.continuous j).comp continuous_neg)
  bddAbove j := by
    obtain ⟨M, hM⟩ := h.bddAbove j
    refine ⟨M, Set.forall_mem_range.2 fun x => ?_⟩
    rw [Complex.norm_conj]
    exact hM (Set.mem_range_self _)
  integrable_fourier j := by
    rw [show 𝓕 (fun x => conj (θ j (-x))) = fun ξ => conj (𝓕 (θ j) ξ) from
      funext (fourier_conj_comp_neg (θ j))]
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp (h.integrable_fourier j)
  overlap ξ := by
    simp_rw [fourier_conj_comp_neg, RCLike.eNorm_conj]
    exact h.overlap ξ
  hormander y := by
    have hS : ∀ z : V, MeasurableSet {x : V | 2 * ‖z‖ < ‖x‖} := fun z =>
      measurableSet_lt measurable_const measurable_norm
    have hF : ∀ x, (fun j => ‖conj (θ j (-(x - y))) - conj (θ j (-x))‖ₑ) =
        fun j => ‖θ j (-x - -y) - θ j (-x)‖ₑ := fun x => by
      funext j
      rw [← map_sub, RCLike.eNorm_conj, neg_sub, sub_neg_eq_add, neg_add_eq_sub]
    simp_rw [hF]
    rw [← lintegral_indicator (hS y)]
    calc ∫⁻ x, {x : V | 2 * ‖y‖ < ‖x‖}.indicator
          (fun x => lqNorm 2 fun j => ‖θ j (-x - -y) - θ j (-x)‖ₑ) x
        = ∫⁻ x, {x : V | 2 * ‖-y‖ < ‖x‖}.indicator
          (fun z => lqNorm 2 fun j => ‖θ j (z - -y) - θ j z‖ₑ) (-x) := lintegral_congr fun x => by
          by_cases hx : 2 * ‖y‖ < ‖x‖
          · have hx' : -x ∈ {x : V | 2 * ‖-y‖ < ‖x‖} := by
              change 2 * ‖-y‖ < ‖-x‖
              rwa [norm_neg, norm_neg]
            rw [indicator_of_mem (show x ∈ {x : V | 2 * ‖y‖ < ‖x‖} from hx),
              indicator_of_mem hx']
          · have hx' : -x ∉ {x : V | 2 * ‖-y‖ < ‖x‖} := by
              change ¬ 2 * ‖-y‖ < ‖-x‖
              rwa [norm_neg, norm_neg]
            rw [indicator_of_notMem (show x ∉ {x : V | 2 * ‖y‖ < ‖x‖} from hx),
              indicator_of_notMem hx']
      _ = ∫⁻ x, {x : V | 2 * ‖-y‖ < ‖x‖}.indicator
          (fun z => lqNorm 2 fun j => ‖θ j (z - -y) - θ j z‖ₑ) x := lintegral_neg_eq_self _
      _ ≤ H := by
          rw [lintegral_indicator (hS (-y))]
          exact h.hormander (-y)

/-- **Dilation families are Calderón–Zygmund families**: for a uniform family `(G_j)` with bounds
`A` whose dilates `θ_j = (G_j)_{2^j}` satisfy `∑_j |𝓕θ_j(ξ)|² ≤ B` for every `ξ`, `(θ_j)` is a
Calderón–Zygmund family with overlap `B` and Hörmander constant `4 H_A`,
`H_A = Rd.familyHormanderConst V A`. -/
theorem IsCZFamily.of_dilation {G : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ} {B : ℝ≥0∞}
    (h : IsUniformSchwartz G A)
    (hB : ∀ ξ, ∑' j, ‖𝓕 (dilate (2 ^ j) (G j : V → ℂ)) ξ‖ₑ ^ 2 ≤ B) :
    IsCZFamily (fun j => dilate (2 ^ j) (G j : V → ℂ)) B (4 * familyHormanderConst V A) where
  integrable j := integrable_dilate (G j).integrable (by positivity)
  continuous j := continuous_dilate (G j).continuous _
  bddAbove j := bddAbove_dilate (bddAbove_schwartz _) _
  integrable_fourier j := integrable_fourier_dilate
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 (G j)).integrable) (by positivity)
  overlap := hB
  hormander := lintegral_lqNorm_sub_le h

/-- The Fourier transform of a dilate of a Schwartz function `G` is bounded by the supremum of
`𝓕G`: `|𝓕(G_c)(ξ)| ≤ ‖𝓕G‖_{0,0}` for `c > 0` (`Rd.fourier_dilate`). -/
theorem enorm_fourier_dilate_le (G : 𝓢(V, ℂ)) {c : ℝ} (hc : 0 < c) (ξ : V) :
    ‖𝓕 (dilate c (G : V → ℂ)) ξ‖ₑ ≤ ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 (𝓕 G)) := by
  rw [fourier_dilate _ hc, ← SchwartzMap.fourier_coe, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (SchwartzMap.norm_le_seminorm ℝ _ _)

/-- **Dilation families with finitely many exceptional members**: let `(G_j)` be uniformly
Schwartz with bounds `A` and let its dilates `(G_j)_{2^j}` have the Fourier overlap `B`. If
`G'_j = G_j` for every `j ≥ N`, then the dilates `(G'_j)_{2^j}` form a Calderón–Zygmund family
with overlap `B + ∑_{i < N} ‖𝓕G'_i‖_{0,0}²` and Hörmander constant `4 H_{A'}`, where
`A'_{k,l} = max(A_{k,l}, ∑_{i < N} ‖G'_i‖_{k,l})` (`Rd.IsUniformSchwartz.of_forall_ge_eq`,
`ENNReal.tsum_le_tsum_add_sum_of_forall_ge_eq`, `Rd.IsCZFamily.of_dilation`). -/
theorem IsCZFamily.of_dilation_of_forall_ge_eq {G G' : ℕ → 𝓢(V, ℂ)} {A : ℕ → ℕ → ℝ}
    {B : ℝ≥0∞} (h : IsUniformSchwartz G A)
    (hB : ∀ ξ, ∑' j, ‖𝓕 (dilate (2 ^ j) (G j : V → ℂ)) ξ‖ₑ ^ 2 ≤ B) {N : ℕ}
    (hG : ∀ j, N ≤ j → G' j = G j) :
    IsCZFamily (fun j => dilate (2 ^ j) (G' j : V → ℂ))
      (B + ∑ i ∈ Finset.range N, ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 (𝓕 (G' i))) ^ 2)
      (4 * familyHormanderConst V fun k l =>
        max (A k l) (∑ i ∈ Finset.range N, SchwartzMap.seminorm ℝ k l (G' i))) :=
  IsCZFamily.of_dilation (h.of_forall_ge_eq hG) fun ξ =>
    (ENNReal.tsum_le_tsum_add_sum_of_forall_ge_eq
      (v := fun j => ‖𝓕 (dilate (2 ^ j) (G j : V → ℂ)) ξ‖ₑ ^ 2) fun j hj => by
        rw [hG j hj]).trans
      (add_le_add (hB ξ) (Finset.sum_le_sum fun i _ => by
        gcongr
        exact enorm_fourier_dilate_le _ (by positivity) ξ))

/-! ### The Littlewood–Paley kernels as dilation families -/

/-- `𝓕Φ_k = 1` on the closed ball of radius `2^k`. -/
theorem fourier_Phi_eq_one {k : ℕ} {ξ : V} (h : ‖ξ‖ ≤ 2 ^ k) : 𝓕 (Phi (V := V) k) ξ = 1 := by
  rw [fourier_Phi]
  refine cutoff_eq_one _ _ ?_
  rw [norm_two_pow_inv_smul, div_le_one (by positivity)]
  exact h

/-- `𝓕Φ_k = 0` outside the ball of radius `2^(k+1)`. -/
theorem fourier_Phi_eq_zero {k : ℕ} {ξ : V} (h : 2 ^ (k + 1) ≤ ‖ξ‖) :
    𝓕 (Phi (V := V) k) ξ = 0 := by
  rw [fourier_Phi]
  refine cutoff_eq_zero _ _ ?_
  rw [norm_two_pow_inv_smul, le_div_iff₀ (by positivity)]
  rw [pow_succ] at h
  linarith

/-- `𝓕Φ_k(ξ)` is a real number in `[0, 1]`: it is a value of the cut-off `χ_{1,2}`
(`Rd.fourier_Phi`), a smooth bump with values in `[0, 1]` (Mathlib's `ContDiffBump`). -/
theorem exists_fourier_Phi_eq_ofReal (k : ℕ) (ξ : V) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 𝓕 (Phi (V := V) k) ξ = t := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b (((2 : ℝ) ^ k)⁻¹ • ξ), b.nonneg, b.le_one, fourier_Phi k ξ⟩

/-- `|𝓕Φ_k(ξ)| ≤ 1`. -/
theorem norm_fourier_Phi_le_one (k : ℕ) (ξ : V) : ‖𝓕 (Phi (V := V) k) ξ‖ ≤ 1 := by
  obtain ⟨t, ht0, ht1, ht⟩ := exists_fourier_Phi_eq_ofReal (V := V) k ξ
  rw [ht, Complex.norm_real, Real.norm_of_nonneg ht0]
  exact ht1

/-- `|𝓕Φ_k(ξ) - 𝓕Φ_l(ξ)| ≤ 1`, since both values lie in `[0, 1]`. -/
theorem norm_fourier_Phi_sub_le_one (k l : ℕ) (ξ : V) :
    ‖𝓕 (Phi (V := V) k) ξ - 𝓕 (Phi (V := V) l) ξ‖ ≤ 1 := by
  obtain ⟨t, ht0, ht1, ht⟩ := exists_fourier_Phi_eq_ofReal (V := V) k ξ
  obtain ⟨u, hu0, hu1, hu⟩ := exists_fourier_Phi_eq_ofReal (V := V) l ξ
  rw [ht, hu, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_le_iff]
  constructor <;> linarith

/-- The Schwartz functions behind the blocks: `psiBase 0 = Φ` and
`psiBase (j+1) = Φ - δ_{1/2} Φ`, with the dilation `δ_c F(x) = c^n F(c x)`, so that
`ψ_j = δ_{2^j} (psiBase j)` (`Rd.dilate_psiBase`). -/
noncomputable def psiBase : ℕ → 𝓢(V, ℂ)
  | 0 => lpKernelS
  | _ + 1 => lpKernelS - schwartzDilate (1 / 2) (by norm_num) lpKernelS

/-- **The blocks are dilates**: `ψ_j = (psiBase j)_{2^j}`. -/
theorem dilate_psiBase (j : ℕ) : dilate (2 ^ j) (psiBase (V := V) j : V → ℂ) = psi j := by
  cases j with
  | zero => rfl
  | succ j =>
    have hcoe : ∀ F H : 𝓢(V, ℂ), ((F - H : 𝓢(V, ℂ)) : V → ℂ) = F - H := fun _ _ => rfl
    rw [psiBase, hcoe, coe_schwartzDilate, dilate_sub, dilate_dilate]
    change dilate (2 ^ (j + 1)) lpKernel - dilate (2 ^ (j + 1) * (1 / 2)) lpKernel = psi (j + 1)
    rw [show (2 : ℝ) ^ (j + 1) * (1 / 2) = 2 ^ j by ring]
    rfl

/-- The Littlewood–Paley block `ψ_j = (psiBase j)_{2^j}` as a Schwartz function. -/
noncomputable def psiS (j : ℕ) : 𝓢(V, ℂ) :=
  schwartzDilate (2 ^ j) (pow_ne_zero j two_ne_zero) (psiBase j)

/-- The Schwartz function `Rd.psiS j` is the block `ψ_j` (`Rd.dilate_psiBase`). -/
theorem coe_psiS (j : ℕ) : (psiS j : V → ℂ) = psi j := by
  rw [psiS, coe_schwartzDilate, dilate_psiBase]

variable (V) in
/-- The seminorm bounds of the family `psiBase`, the larger of the seminorms of `Φ` and of
`Φ - δ_{1/2} Φ`. -/
noncomputable def psiBaseBound (k l : ℕ) : ℝ :=
  max (SchwartzMap.seminorm ℝ k l (lpKernelS (V := V)))
    (SchwartzMap.seminorm ℝ k l (lpKernelS (V := V) - schwartzDilate (1 / 2) (by norm_num)
      lpKernelS))

/-- The seminorm bounds of the family `psiBase` are nonnegative. -/
theorem psiBaseBound_nonneg (k l : ℕ) : 0 ≤ psiBaseBound V k l :=
  le_max_of_le_left (apply_nonneg _ _)

/-- The family `psiBase` is uniformly Schwartz with bounds `Rd.psiBaseBound V`. -/
theorem isUniformSchwartz_psiBase : IsUniformSchwartz (psiBase (V := V)) (psiBaseBound V) :=
  IsUniformSchwartz.of_forall_eq_or_eq fun j => by
    cases j with
    | zero => exact Or.inl rfl
    | succ j => exact Or.inr rfl

/-- **Overlap of the blocks**: `∑_j |𝓕ψ_j(ξ)|² ≤ 2` for every `ξ`, the case `s = 0` of
`Rd.tsum_dyadicWeight_fourier_psi_sq_le`. -/
theorem tsum_fourier_psi_sq_le (ξ : V) : ∑' j, ‖𝓕 (psi (V := V) j) ξ‖ₑ ^ 2 ≤ 2 := by
  simpa [besselWeight] using tsum_dyadicWeight_fourier_psi_sq_le (V := V) le_rfl ξ

/-- **The blocks form a Calderón–Zygmund family** with overlap `2` and Hörmander constant
`4 H_{A^ψ}`, `H_{A^ψ} = Rd.familyHormanderConst V (Rd.psiBaseBound V)`. -/
theorem isCZFamily_psi :
    IsCZFamily (psi (V := V)) 2 (4 * familyHormanderConst V (psiBaseBound V)) := by
  have h := IsCZFamily.of_dilation (G := psiBase (V := V)) (A := psiBaseBound V) (B := 2)
    isUniformSchwartz_psiBase fun ξ => by
    simp_rw [dilate_psiBase]
    exact tsum_fourier_psi_sq_le ξ
  rwa [show (fun j => dilate (2 ^ j) (psiBase (V := V) j : V → ℂ)) = psi from
    funext dilate_psiBase] at h

/-- The **synthesis kernels** `psiDual 0 = Φ_1`, `psiDual 1 = Φ_2`,
`psiDual (j+2) = Φ_{j+3} - Φ_j`, with `psiDual_j ⋆ ψ_j = ψ_j` (`Rd.conv_psiDual_psi`). -/
noncomputable def psiDual : ℕ → V → ℂ
  | 0 => Phi 1
  | 1 => Phi 2
  | j + 2 => Phi (j + 3) - Phi j

/-- The Schwartz functions behind the synthesis kernels: `psiDualBase 0 = psiDualBase 1 = δ_2 Φ`
and `psiDualBase (j+2) = δ_2 Φ - δ_{1/4} Φ`, with the dilation `δ_c F(x) = c^n F(c x)`, so that
`psiDual_j = δ_{2^j} (psiDualBase j)` (`Rd.dilate_psiDualBase`). -/
noncomputable def psiDualBase : ℕ → 𝓢(V, ℂ)
  | 0 => schwartzDilate 2 two_ne_zero lpKernelS
  | 1 => schwartzDilate 2 two_ne_zero lpKernelS
  | _ + 2 => schwartzDilate 2 two_ne_zero lpKernelS - schwartzDilate (1 / 4) (by norm_num)
      lpKernelS

/-- **The synthesis kernels are dilates**: `psiDual_j = (psiDualBase j)_{2^j}`. -/
theorem dilate_psiDualBase (j : ℕ) :
    dilate (2 ^ j) (psiDualBase (V := V) j : V → ℂ) = psiDual j := by
  match j with
  | 0 =>
    rw [psiDualBase, coe_schwartzDilate, dilate_dilate]
    change dilate (2 ^ 0 * 2) lpKernel = dilate (2 ^ 1) lpKernel
    norm_num
  | 1 =>
    rw [psiDualBase, coe_schwartzDilate, dilate_dilate]
    change dilate (2 ^ 1 * 2) lpKernel = dilate (2 ^ 2) lpKernel
    norm_num
  | j + 2 =>
    have hcoe : ∀ F H : 𝓢(V, ℂ), ((F - H : 𝓢(V, ℂ)) : V → ℂ) = F - H := fun _ _ => rfl
    rw [psiDualBase, hcoe, coe_schwartzDilate, coe_schwartzDilate, dilate_sub,
      dilate_dilate, dilate_dilate]
    change dilate (2 ^ (j + 2) * 2) lpKernel - dilate (2 ^ (j + 2) * (1 / 4)) lpKernel =
      dilate (2 ^ (j + 3)) lpKernel - dilate (2 ^ j) lpKernel
    rw [show (2 : ℝ) ^ (j + 2) * 2 = 2 ^ (j + 3) by ring,
      show (2 : ℝ) ^ (j + 2) * (1 / 4) = 2 ^ j by ring]

variable (V) in
/-- The seminorm bounds of the family `psiDualBase`, the larger of the seminorms of `δ_2 Φ` and
of `δ_2 Φ - δ_{1/4} Φ`. -/
noncomputable def psiDualBaseBound (k l : ℕ) : ℝ :=
  max (SchwartzMap.seminorm ℝ k l (schwartzDilate 2 two_ne_zero (lpKernelS (V := V))))
    (SchwartzMap.seminorm ℝ k l (schwartzDilate 2 two_ne_zero (lpKernelS (V := V)) -
      schwartzDilate (1 / 4) (by norm_num) lpKernelS))

/-- The seminorm bounds of the family `psiDualBase` are nonnegative. -/
theorem psiDualBaseBound_nonneg (k l : ℕ) : 0 ≤ psiDualBaseBound V k l :=
  le_max_of_le_left (apply_nonneg _ _)

/-- The family `psiDualBase` is uniformly Schwartz with bounds `Rd.psiDualBaseBound V`. -/
theorem isUniformSchwartz_psiDualBase :
    IsUniformSchwartz (psiDualBase (V := V)) (psiDualBaseBound V) :=
  IsUniformSchwartz.of_forall_eq_or_eq fun j => by
    match j with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inl rfl
    | _ + 2 => exact Or.inr rfl

/-- The synthesis kernels are integrable. -/
theorem integrable_psiDual (j : ℕ) : Integrable (psiDual (V := V) j) := by
  rw [← dilate_psiDualBase]
  exact integrable_dilate (psiDualBase j).integrable (by positivity)

/-- The synthesis kernels are continuous. -/
theorem continuous_psiDual (j : ℕ) : Continuous (psiDual (V := V) j) := by
  rw [← dilate_psiDualBase]
  exact continuous_dilate (psiDualBase j).continuous _

/-- The synthesis kernels are bounded. -/
theorem bddAbove_psiDual (j : ℕ) : BddAbove (Set.range fun x => ‖psiDual (V := V) j x‖) := by
  rw [← dilate_psiDualBase]
  exact bddAbove_dilate (bddAbove_schwartz _) _

/-- The Fourier transforms of the synthesis kernels are integrable. -/
theorem integrable_fourier_psiDual (j : ℕ) : Integrable (𝓕 (psiDual (V := V) j)) := by
  rw [← dilate_psiDualBase]
  exact integrable_fourier_dilate
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 (psiDualBase (V := V) j)).integrable)
    (by positivity)

/-- `‖psiDual_j‖_1 ≤ 2 ‖Φ‖_1`. -/
theorem eLpNorm_psiDual_one_le (j : ℕ) :
    eLpNorm (psiDual (V := V) j) 1 volume ≤ 2 * eLpNorm (lpKernel (V := V)) 1 volume := by
  match j with
  | 0 =>
    change eLpNorm (Phi (V := V) 1) 1 volume ≤ _
    rw [eLpNorm_Phi_one, two_mul]
    exact le_self_add
  | 1 =>
    change eLpNorm (Phi (V := V) 2) 1 volume ≤ _
    rw [eLpNorm_Phi_one, two_mul]
    exact le_self_add
  | j + 2 =>
    change eLpNorm (Phi (V := V) (j + 3) - Phi j) 1 volume ≤ _
    calc eLpNorm (Phi (V := V) (j + 3) - Phi j) 1 volume
        ≤ eLpNorm (Phi (V := V) (j + 3)) 1 volume + eLpNorm (Phi (V := V) j) 1 volume :=
          eLpNorm_sub_le le_rfl
      _ = 2 * eLpNorm (lpKernel (V := V)) 1 volume := by
          rw [eLpNorm_Phi_one, eLpNorm_Phi_one, two_mul]

/-- `𝓕 psiDual_{j+2} = 𝓕Φ_{j+3} - 𝓕Φ_j`. -/
theorem fourier_psiDual_add_two (j : ℕ) (ξ : V) :
    𝓕 (psiDual (V := V) (j + 2)) ξ = 𝓕 (Phi (V := V) (j + 3)) ξ - 𝓕 (Phi (V := V) j) ξ :=
  fourier_sub_apply (integrable_Phi _) (integrable_Phi _) ξ

/-- `𝓕 psiDual_j · 𝓕ψ_j = 𝓕ψ_j`: wherever `𝓕ψ_j(ξ) ≠ 0`, `‖ξ‖ < 2^(j+1)`, so
`𝓕Φ_{j+1}(ξ) = 1`, and for `j ≥ 2` also `‖ξ‖ > 2^(j-1)`, so `𝓕Φ_{j-2}(ξ) = 0`; hence
`𝓕 psiDual_j(ξ) = 1` there. -/
theorem fourier_psiDual_mul_psi (j : ℕ) (ξ : V) :
    𝓕 (psiDual (V := V) j) ξ * 𝓕 (psi (V := V) j) ξ = 𝓕 (psi (V := V) j) ξ := by
  by_cases h : 𝓕 (psi (V := V) j) ξ = 0
  · rw [h, mul_zero]
  have hlt := norm_lt_of_fourier_psi_ne_zero h
  suffices 𝓕 (psiDual (V := V) j) ξ = 1 by rw [this, one_mul]
  match j with
  | 0 => exact fourier_Phi_eq_one hlt.le
  | 1 => exact fourier_Phi_eq_one (hlt.le.trans (pow_le_pow_right₀ one_le_two (by omega)))
  | m + 2 =>
    have hgt : 2 ^ (m + 1) < ‖ξ‖ := not_le.1 fun h' => h (fourier_psi_succ_eq_zero h')
    rw [fourier_psiDual_add_two, fourier_Phi_eq_one hlt.le, fourier_Phi_eq_zero hgt.le, sub_zero]

/-- **The synthesis kernels reproduce the blocks**: `psiDual_j ⋆ ψ_j = ψ_j`, by comparing
Fourier transforms (`Rd.conv_eq_of_fourier`). -/
theorem conv_psiDual_psi (j : ℕ) : conv (psiDual (V := V) j) (psi j) volume = psi j :=
  conv_eq_of_fourier (integrable_psiDual _) (integrable_psi _) (continuous_psi _)
    (bddAbove_psi _) (integrable_psi _) (continuous_psi _) (integrable_fourier_psi _)
    (fourier_psiDual_mul_psi j)

/-- `|𝓕 psiDual_j(ξ)| ≤ 1`. -/
theorem enorm_fourier_psiDual_le_one (j : ℕ) (ξ : V) : ‖𝓕 (psiDual (V := V) j) ξ‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  match j with
  | 0 => exact norm_fourier_Phi_le_one 1 ξ
  | 1 => exact norm_fourier_Phi_le_one 2 ξ
  | m + 2 =>
    rw [fourier_psiDual_add_two]
    exact norm_fourier_Phi_sub_le_one (m + 3) m ξ

/-- `𝓕 psiDual_j` vanishes outside the ball of radius `2^(j+2)`. -/
theorem norm_lt_of_fourier_psiDual_ne_zero {j : ℕ} {ξ : V}
    (h : 𝓕 (psiDual (V := V) j) ξ ≠ 0) : ‖ξ‖ < 2 ^ (j + 2) := by
  match j with
  | 0 => exact norm_lt_of_fourier_Phi_ne_zero h
  | 1 => exact norm_lt_of_fourier_Phi_ne_zero h
  | m + 2 =>
    rw [fourier_psiDual_add_two] at h
    by_cases h3 : 𝓕 (Phi (V := V) (m + 3)) ξ = 0
    · rw [h3, zero_sub, neg_ne_zero] at h
      exact (norm_lt_of_fourier_Phi_ne_zero h).trans
        (pow_lt_pow_right₀ one_lt_two (by omega))
    · exact norm_lt_of_fourier_Phi_ne_zero h3

/-- `𝓕 psiDual_{m+2}` vanishes on the closed ball of radius `2^m`. -/
theorem lt_norm_of_fourier_psiDual_ne_zero {m : ℕ} {ξ : V}
    (h : 𝓕 (psiDual (V := V) (m + 2)) ξ ≠ 0) : 2 ^ m < ‖ξ‖ := by
  by_contra hle
  push Not at hle
  apply h
  rw [fourier_psiDual_add_two, fourier_Phi_eq_one hle,
    fourier_Phi_eq_one (hle.trans (pow_le_pow_right₀ one_le_two (by omega))), sub_self]

/-- **At most four synthesis kernels see a frequency**: with `a` the least index such that
`‖ξ‖ < 2^(a+1)`, `𝓕 psiDual_j(ξ) ≠ 0` forces `a - 1 ≤ j ≤ a + 2`. -/
theorem mem_Icc_of_fourier_psiDual_ne_zero {a j : ℕ} {ξ : V} (ha : ‖ξ‖ < 2 ^ (a + 1))
    (hmin : ∀ i < a, ¬ ‖ξ‖ < 2 ^ (i + 1)) (h : 𝓕 (psiDual (V := V) j) ξ ≠ 0) :
    j ∈ Finset.Icc (a - 1) (a + 2) := by
  have hlo : a ≤ j + 1 := by
    by_contra hlt
    exact hmin (j + 1) (by omega) (norm_lt_of_fourier_psiDual_ne_zero h)
  have hhi : j ≤ a + 2 := by
    match j, h with
    | 0, _ => omega
    | 1, _ => omega
    | m + 2, h =>
      have h1 := (lt_norm_of_fourier_psiDual_ne_zero h).trans ha
      have h2 : m < a + 1 := (pow_lt_pow_iff_right₀ one_lt_two).1 h1
      omega
  exact Finset.mem_Icc.2 ⟨by omega, hhi⟩

/-- **Overlap of the synthesis kernels**: `∑_j |𝓕 psiDual_j(ξ)|² ≤ 4` for every `ξ`: at most four
kernels are nonzero at `ξ` (`Rd.mem_Icc_of_fourier_psiDual_ne_zero`), each of modulus at most
`1`. -/
theorem tsum_fourier_psiDual_sq_le (ξ : V) : ∑' j, ‖𝓕 (psiDual (V := V) j) ξ‖ₑ ^ 2 ≤ 4 := by
  classical
  have hex : ∃ a : ℕ, ‖ξ‖ < 2 ^ (a + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖ξ‖ (one_lt_two : (1 : ℝ) < 2)
    exact ⟨n, hn.trans (pow_lt_pow_right₀ one_lt_two n.lt_succ_self)⟩
  have hsupp := fun j => mem_Icc_of_fourier_psiDual_ne_zero (j := j) (Nat.find_spec hex)
    (fun i hi => Nat.find_min hex hi)
  rw [tsum_eq_sum (s := Finset.Icc (Nat.find hex - 1) (Nat.find hex + 2)) (fun j hj => ?_)]
  · calc ∑ j ∈ Finset.Icc (Nat.find hex - 1) (Nat.find hex + 2), ‖𝓕 (psiDual (V := V) j) ξ‖ₑ ^ 2
        ≤ ∑ _j ∈ Finset.Icc (Nat.find hex - 1) (Nat.find hex + 2), (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun j _ => pow_le_one₀ zero_le (enorm_fourier_psiDual_le_one j ξ)
      _ = ((Finset.Icc (Nat.find hex - 1) (Nat.find hex + 2)).card : ℝ≥0∞) := by simp
      _ ≤ 4 := by
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : Nat.find hex + 2 + 1 - (Nat.find hex - 1) ≤ 4)
  · have : 𝓕 (psiDual (V := V) j) ξ = 0 := by
      by_contra h
      exact hj (hsupp j h)
    simp [this]

/-- **The synthesis kernels form a Calderón–Zygmund family** with overlap `4` and Hörmander
constant `4 H_Ã`, `H_Ã = Rd.familyHormanderConst V (Rd.psiDualBaseBound V)`. -/
theorem isCZFamily_psiDual :
    IsCZFamily (psiDual (V := V)) 4 (4 * familyHormanderConst V (psiDualBaseBound V)) := by
  have h := IsCZFamily.of_dilation (G := psiDualBase (V := V)) (A := psiDualBaseBound V) (B := 4)
    isUniformSchwartz_psiDualBase fun ξ => by
    simp_rw [dilate_psiDualBase]
    exact tsum_fourier_psiDual_sq_le ξ
  rwa [show (fun j => dilate (2 ^ j) (psiDualBase (V := V) j : V → ℂ)) = psiDual from
    funext dilate_psiDualBase] at h

end Rd
