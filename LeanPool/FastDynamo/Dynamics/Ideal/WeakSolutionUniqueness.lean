/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Ideal.WeakSolution
public import LeanPool.FastDynamo.Dynamics.Ideal.LipschitzTestFields

/-!
# Uniqueness of weak solutions of the ideal induction equation

The proof of `cor:ideal-growth` (Corollary 4.2) identifies the ideal Cauchy group `𝒯₀` as *the*
solution group of the ideal induction equation `∂ₜB + (u·∇)B − (B·∇)u = 0`: distributional
solutions in `C([−T, T]; L²)` are unique (the paper invokes Ambrosio–Crippa, Proposition 2.3
there).  This module proves the uniqueness for the velocity of the paper, in the weak form
`IsIdealWeakSolution` of `FastDynamo/Dynamics/IdealWeakForm.lean`, by pulling back along the
flow.

## The argument

Let `W` be a weak solution with `W 0 = 0` and `ψ` a smooth test field, `χ = (u·∇)ψ`.  For every
`σ` the field `ψ ∘ Φ_{-σ}` has a Lipschitz, everywhere differentiable lift, and its advection is
`χ ∘ Φ_{-σ}` at every point (`DΦ_σ(a) u(a) = u(Φ_σ a)`), so the weak identity holds with the
test pair `(P σ, Q σ) = (ψ ∘ Φ_{-σ}, χ ∘ Φ_{-σ})` (`FastDynamo/Dynamics/Ideal/LipschitzTestFields`).
Moreover `d/dσ ⟪P σ, Y⟫ = −⟪Q σ, Y⟫` for every `Y ∈ L²` (differentiation under the integral sign).
For `f(t) = ⟪P t, W t⟫` the two advection terms cancel (`hasDerivAt_diag_of_eq_intervalIntegral`
isolates the two-parameter limit), so `f(t) = ∫₀ᵗ ⟪P τ, (W τ·∇)u⟫ dτ`.  Since composition with
the flow is an isometry of `L²` and the test fields are dense, `‖W t‖ ≤ ‖∇u‖ |∫₀ᵗ ‖W τ‖ dτ|`,
and Grönwall's argument (`eq_zero_of_le_mul_abs_intervalIntegral`) gives `W = 0`.  Applied to
the difference of two orbits, this identifies every solution group with `idealGroup`.

## Contents

* `IsIdealWeakSolution.eq_zero` — a weak solution vanishing at time `0` vanishes on `[−T, T]`.
* `IsIdealSolutionGroup.eq_idealGroup` — every solution group is `idealGroup`.
* `existsUnique_isIdealSolutionGroup` — the solution group exists and is unique.

The paper obtains the characteristic identity `W(t, Φ_t a) = ∫₀ᵗ ∇u(Φ_s a) W(s, Φ_s a) ds` for
almost every `a` from Ambrosio–Crippa (Proposition 2.3 there) and concludes with Grönwall's
inequality.  Here the identity is proved in tested form, `⟪ψ, W t ∘ Φ_t⟫ = ∫₀ᵗ ⟪ψ, (W τ·∇)u ∘ Φ_τ⟫`
for smooth `ψ` (`inner_flowCompL2_eq_intervalIntegral`, read through `inner_flowCompL2`),
directly from the weak form, and Grönwall's argument is applied to `‖W t‖`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal Interval

/-! ## Two lemmas on functions of a real variable -/

/-- **The derivative along the diagonal.**  If `G σ σ − G σ t = ∫ₜ^σ A σ τ dτ` near `t`, `A` is
continuous at `(t, t)` and `σ ↦ G σ t` has derivative `B` at `t`, then `σ ↦ G σ σ` has
derivative `A t t + B` at `t`. -/
theorem hasDerivAt_diag_of_eq_intervalIntegral {G A : ℝ → ℝ → ℂ} {B : ℂ} {t : ℝ}
    (hG : ∀ᶠ σ in 𝓝 t, G σ σ - G σ t = ∫ τ in t..σ, A σ τ)
    (hint : ∀ᶠ σ in 𝓝 t, IntervalIntegrable (A σ) volume t σ)
    (hA : ContinuousAt (Function.uncurry A) (t, t))
    (hB : HasDerivAt (fun σ ↦ G σ t) B t) :
    HasDerivAt (fun σ ↦ G σ σ) (A t t + B) t := by
  have h1 : HasDerivAt (fun σ ↦ G σ σ - G σ t) (A t t) t := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.1 hA c hc
    filter_upwards [hG, hint, Metric.ball_mem_nhds t hη] with σ hσ hi hση
    have hconst : (σ - t) • A t t = ∫ _ in t..σ, A t t := (intervalIntegral.integral_const _).symm
    rw [hσ, sub_self, sub_zero, hconst, ← intervalIntegral.integral_sub hi intervalIntegrable_const,
      Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ hτ ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq] at hση
    have hτt : dist τ t < η := by
      rw [Real.dist_eq]
      rcases Set.mem_uIoc.1 hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_lt] at hση ⊢
        constructor <;> linarith
      · rw [abs_lt] at hση ⊢
        constructor <;> linarith
    have hd : dist ((σ, τ) : ℝ × ℝ) (t, t) < η := by
      rw [Prod.dist_eq]
      exact max_lt (by rwa [Real.dist_eq]) hτt
    have := hball hd
    rw [dist_eq_norm] at this
    exact this.le
  have e : (fun σ ↦ G σ σ) = (fun σ ↦ G σ σ - G σ t) + fun σ ↦ G σ t := by
    funext σ
    simp
  rw [e]
  exact h1.add hB

/-- **Grönwall's argument.**  A nonnegative function, continuous on `[0, T]`, with
`w t ≤ M |∫₀ᵗ w|` on `[0, T]`, vanishes on `[0, T]`: `e^{−Mt} ∫₀ᵗ w` is antitone and starts at
`0`. -/
theorem eq_zero_of_le_mul_abs_intervalIntegral {w : ℝ → ℝ} {M T : ℝ}
    (hw : ContinuousOn w (Icc 0 T)) (hw0 : ∀ t ∈ Icc 0 T, 0 ≤ w t)
    (hle : ∀ t ∈ Icc 0 T, w t ≤ M * |∫ s in 0..t, w s|) : ∀ t ∈ Icc 0 T, w t = 0 := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hw' : ContinuousOn w (uIcc 0 T) := by rwa [uIcc_of_le hT]
  have hint : IntervalIntegrable w volume 0 T := hw'.intervalIntegrable
  set F : ℝ → ℝ := fun t ↦ ∫ s in 0..t, w s with hF
  have hFnn : ∀ x ∈ Icc 0 T, 0 ≤ F x := fun x hx ↦
    intervalIntegral.integral_nonneg hx.1 fun s hs ↦ hw0 s ⟨hs.1, hs.2.trans hx.2⟩
  have hFc : ContinuousOn F (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    rwa [uIcc_of_le hT] at this
  have hFd : ∀ x ∈ Ioo 0 T, HasDerivAt F (w x) x := fun x hx ↦
    intervalIntegral.integral_hasDerivAt_right
      (hint.mono_set (by
        rw [uIcc_of_le hx.1.le, uIcc_of_le hT]
        exact Icc_subset_Icc le_rfl hx.2.le))
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hw.mono Ioo_subset_Icc_self) x hx)
      (hw.continuousAt (Icc_mem_nhds hx.1 hx.2))
  set g : ℝ → ℝ := fun x ↦ Real.exp (-M * x) * F x with hg
  have hgd : ∀ x ∈ Ioo 0 T, HasDerivAt g
      (Real.exp (-M * x) * (-M) * F x + Real.exp (-M * x) * w x) x := by
    intro x hx
    have he : HasDerivAt (fun x ↦ Real.exp (-M * x)) (Real.exp (-M * x) * (-M)) x := by
      simpa using ((hasDerivAt_id x).const_mul (-M)).exp
    exact he.mul (hFd x hx)
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun x ↦ Real.exp (-M * x) * (-M) * F x + Real.exp (-M * x) * w x)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hFc)
      (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · rw [interior_Icc] at hx
      exact (hgd x hx).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have h1 := hle x (Ioo_subset_Icc_self hx)
      rw [abs_of_nonneg (hFnn x (Ioo_subset_Icc_self hx))] at h1
      have e : Real.exp (-M * x) * (-M) * F x + Real.exp (-M * x) * w x =
          Real.exp (-M * x) * (w x - M * F x) := by ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hgt : g t ≤ g 0 := hanti ⟨le_rfl, hT⟩ ht ht.1
  have hg0 : g 0 = 0 := by simp [hg, hF]
  have hFt : F t = 0 := by
    rw [hg0, hg] at hgt
    exact le_antisymm (nonpos_of_mul_nonpos_right hgt (Real.exp_pos _)) (hFnn t ht)
  have : w t ≤ M * |F t| := hle t ht
  rw [hFt, abs_zero, mul_zero] at this
  exact le_antisymm this (hw0 t ht)

/-- The weak identity is linear in the solution: it passes to the difference of two solutions
continuous on the time interval. -/
theorem IdealWeakIdentity.sub {v : Torus 3 → R3} {W₁ W₂ : ℝ → LiteralC3L2} {s t : ℝ}
    {φ ψ : LiteralC3L2} (hW₁ : ContinuousOn W₁ (uIcc s t)) (hW₂ : ContinuousOn W₂ (uIcc s t))
    (h₁ : IdealWeakIdentity v W₁ s t φ ψ) (h₂ : IdealWeakIdentity v W₂ s t φ ψ) :
    IdealWeakIdentity v (fun τ ↦ W₁ τ - W₂ τ) s t φ ψ := by
  have hi : ∀ {W : ℝ → LiteralC3L2}, ContinuousOn W (uIcc s t) →
      IntervalIntegrable (fun τ ↦ inner ℂ φ (literalStretchL2 v (W τ)) + inner ℂ ψ (W τ))
        volume s t := fun hW ↦
    ((continuousOn_const.inner ((literalStretchL2 v).continuous.comp_continuousOn hW)).add
      (continuousOn_const.inner hW)).intervalIntegrable
  have e : (∫ τ in s..t, (inner ℂ φ (literalStretchL2 v (W₁ τ - W₂ τ)) +
      inner ℂ ψ (W₁ τ - W₂ τ))) =
      (∫ τ in s..t, (inner ℂ φ (literalStretchL2 v (W₁ τ)) + inner ℂ ψ (W₁ τ))) -
        ∫ τ in s..t, (inner ℂ φ (literalStretchL2 v (W₂ τ)) + inner ℂ ψ (W₂ τ)) := by
    rw [← intervalIntegral.integral_sub (hi hW₁) (hi hW₂)]
    congr 1
    funext τ
    rw [map_sub, inner_sub_right, inner_sub_right]
    ring
  rw [IdealWeakIdentity] at h₁ h₂ ⊢
  rw [e, ← h₁, ← h₂, inner_sub_right, inner_sub_right]
  ring

namespace ScaleFamily.TorusCellPlacement

open FullVelocityConcrete

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- The velocity of the paper on the literal torus. -/
local notation "𝐮" => literalVelocity
  (parameterizedFullGlobalRealTorusSource h P angularSpeed axialSpeed tau)

/-! ## Transport of test fields by the flow -/

/-- The almost everywhere representative of `flowCompL2 … σ` applied to the class of a field. -/
theorem flowCompL2_toLp_coe_ae (σ : ℝ) {g : Torus 3 → C3} (hg : MemLp g 2 volume) :
    (flowCompL2 h P angularSpeed axialSpeed tau σ (hg.toLp g) : Torus 3 → C3) =ᵐ[volume]
      fun x ↦ g (literalFlow h P angularSpeed axialSpeed tau (-σ) x) := by
  filter_upwards [flowCompL2_coe_ae h P angularSpeed axialSpeed tau σ (hg.toLp g),
    (quasiMeasurePreserving_literalFlow h P angularSpeed axialSpeed tau (-σ)).ae
      hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- The adjoint of composition with `Φ_{-t}` is composition with `Φ_t`. -/
theorem inner_flowCompL2 (t : ℝ) (a b : LiteralC3L2) :
    inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau t a) b =
      inner ℂ a (flowCompL2 h P angularSpeed axialSpeed tau (-t) b) := by
  have hinv : flowCompL2 h P angularSpeed axialSpeed tau t
      (flowCompL2 h P angularSpeed axialSpeed tau (-t) b) = b := by
    refine Lp.ext ?_
    filter_upwards [flowCompL2_coe_ae h P angularSpeed axialSpeed tau t _,
      (quasiMeasurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t)).ae
        (flowCompL2_coe_ae h P angularSpeed axialSpeed tau (-t) b)] with x h1 h2
    rw [h1, h2, literalFlow_neg_literalFlow]
  conv_lhs => rw [← hinv]
  exact (Lp.compMeasurePreservingₗᵢ ℂ (E := C3) (p := 2)
    (literalFlow h P angularSpeed axialSpeed tau (-t))
    (measurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t))).inner_map_map _ _

/-- **The derivative of a transported test field**: `d/dσ ⟪ψ ∘ Φ_{-σ}, Y⟫ = −⟪χ ∘ Φ_{-σ}, Y⟫`
with `χ = (u·∇)ψ`, for every `Y ∈ L²`, by differentiation under the integral sign. -/
theorem hasDerivAt_inner_flowCompL2 (htau : 0 ≤ tau) {ψ : Torus 3 → C3}
    (hψ : IsIdealTestField ψ) (hψL : MemLp ψ 2 volume)
    (hχL : MemLp (literalAdvection 𝐮 ψ) 2 volume) (Y : LiteralC3L2) (s : ℝ) :
    HasDerivAt (fun σ ↦ inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ)) Y)
      (-inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau s (hχL.toLp _)) Y) s := by
  have hmp := measurePreserving_literalFlow h P angularSpeed axialSpeed tau
  set F : ℝ → Torus 3 → ℂ := fun σ x ↦
    inner ℂ (ψ (literalFlow h P angularSpeed axialSpeed tau (-σ) x)) ((Y : Torus 3 → C3) x)
    with hF
  set F' : ℝ → Torus 3 → ℂ := fun σ x ↦
    -inner ℂ (literalAdvection 𝐮 ψ (literalFlow h P angularSpeed axialSpeed tau (-σ) x))
      ((Y : Torus 3 → C3) x) with hF'
  -- the pointwise derivative
  have hpt : ∀ (x : Torus 3) (σ : ℝ),
      HasDerivAt (fun σ ↦ ψ (literalFlow h P angularSpeed axialSpeed tau (-σ) x))
        (-literalAdvection 𝐮 ψ (literalFlow h P angularSpeed axialSpeed tau (-σ) x)) σ := by
    intro x σ
    set b := literalIocRepresentative x
    have hb : ∀ σ : ℝ, literalFlow h P angularSpeed axialSpeed tau (-σ) x =
        literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau (-σ) b) := fun σ ↦ by
      rw [literalTorusPoint_literalFlowLift, literalTorusPoint_literalIocRepresentative]
    have hcurve : HasDerivAt (fun σ ↦ literalFlowLift h P angularSpeed axialSpeed tau (-σ) b)
        (-𝐮 (literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau (-σ) b))) σ := by
      have := (hasDerivAt_literalFlowLift h P angularSpeed axialSpeed tau (-σ) b).scomp σ
        (hasDerivAt_neg σ)
      exact this.congr_deriv (by simp)
    simp_rw [hb]
    rw [literalAdvection_literalTorusPoint, ← map_neg]
    exact ((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt σ hcurve
  -- bounds and measurability
  have hψm : Measurable ψ := measurable_of_continuous_lift hψ.continuous
  obtain ⟨Cψ, hCψ⟩ := exists_norm_le_of_continuous_lift hψ.continuous
  obtain ⟨Cχ, hCχ⟩ := exists_norm_literalAdvection_le h P angularSpeed axialSpeed tau htau hψ
  have hYint : Integrable (fun x ↦ ‖(Y : Torus 3 → C3) x‖) volume :=
    ((Lp.memLp Y).integrable one_le_two).norm
  have hFm : ∀ σ, AEStronglyMeasurable (F σ) volume := fun σ ↦
    (hψm.comp (hmp (-σ)).measurable).aestronglyMeasurable.inner (Lp.aestronglyMeasurable Y)
  have hF'm : AEStronglyMeasurable (F' s) volume :=
    (((aestronglyMeasurable_literalAdvection h P angularSpeed axialSpeed tau htau
      hψ).comp_measurePreserving (hmp (-s))).inner (Lp.aestronglyMeasurable Y)).neg
  have hFint : Integrable (F s) volume :=
    (hYint.const_mul Cψ).mono' (hFm s) (ae_of_all _ fun x ↦ (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hCψ _) (norm_nonneg _)))
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (bound := fun x ↦ Cχ * ‖(Y : Torus 3 → C3) x‖) Filter.univ_mem
    (Eventually.of_forall hFm) hFint hF'm
    (ae_of_all _ fun x σ _ ↦ by
      rw [hF', norm_neg]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hCχ _) (norm_nonneg _)))
    (hYint.const_mul Cχ)
    (ae_of_all _ fun x σ _ ↦ by
      have := (hpt x σ).inner ℂ (hasDerivAt_const σ ((Y : Torus 3 → C3) x))
      simpa [hF, hF', inner_neg_left] using this)
  have e1 : (fun σ ↦ inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ)) Y) =
      fun σ ↦ ∫ x, F σ x := by
    funext σ
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [flowCompL2_toLp_coe_ae h P angularSpeed axialSpeed tau σ hψL] with x hx
    rw [hx]
  have e2 : -inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau s (hχL.toLp _)) Y =
      ∫ x, F' s x := by
    rw [L2.inner_def, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [flowCompL2_toLp_coe_ae h P angularSpeed axialSpeed tau s hχL] with x hx
    rw [hx]
  rw [e1, e2]
  exact hD

/-- **The weak identity with transported test fields.**  For a weak solution `W`, a test field
`ψ` and every `σ`, `W` satisfies the weak identity with the test pair
`(ψ ∘ Φ_{-σ}, ((u·∇)ψ) ∘ Φ_{-σ})`: the lift of `ψ ∘ Φ_{-σ}` is Lipschitz and differentiable
everywhere, and its advection is `((u·∇)ψ) ∘ Φ_{-σ}` because `DΦ_{-σ}(a) u(a) = u(Φ_{-σ} a)`. -/
theorem idealWeakIdentity_flowCompL2_of_isIdealWeakSolution (htau : 0 ≤ tau) {T : ℝ}
    {W : ℝ → LiteralC3L2} (hW : IsIdealWeakSolution 𝐮 T W) {ψ : Torus 3 → C3}
    (hψ : IsIdealTestField ψ) (hψL : MemLp ψ 2 volume)
    (hχL : MemLp (literalAdvection 𝐮 ψ) 2 volume) (σ : ℝ) {s t : ℝ}
    (hs : s ∈ Icc (-T) T) (ht : t ∈ Icc (-T) T) :
    IdealWeakIdentity 𝐮 W s t (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ))
      (flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _)) := by
  set φ : Torus 3 → C3 := fun x ↦ ψ (literalFlow h P angularSpeed axialSpeed tau (-σ) x)
    with hφdef
  have hlift : (fun a : R3 ↦ φ (literalTorusPoint a)) =
      fun a ↦ ψ (literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau (-σ) a)) := by
    funext a
    rw [hφdef, literalTorusPoint_literalFlowLift]
  have hfd : ∀ a : R3, HasFDerivAt (fun a : R3 ↦ φ (literalTorusPoint a))
      ((fderiv ℝ (fun c : R3 ↦ ψ (literalTorusPoint c))
        (literalFlowLift h P angularSpeed axialSpeed tau (-σ) a)).comp
          (flowFDeriv h P angularSpeed axialSpeed tau (-σ) (literalTorusPoint a))) a := by
    intro a
    rw [hlift]
    exact ((hψ.differentiable (by simp)) _).hasFDerivAt.comp a
      (hasFDerivAt_literalFlowLift h P angularSpeed axialSpeed tau (-σ) a)
  have hdiff : Differentiable ℝ fun a : R3 ↦ φ (literalTorusPoint a) := fun a ↦
    (hfd a).differentiableAt
  -- the lift is Lipschitz
  obtain ⟨C, hC⟩ := exists_bound_comp_literalIocRepresentative (hψ.continuous_fderiv (by simp))
  have hC' : ∀ c : R3, ‖fderiv ℝ (fun c : R3 ↦ ψ (literalTorusPoint c)) c‖ ≤ C := fun c ↦ by
    rw [fderiv_literalLift_congr ψ
      (literalTorusPoint_literalIocRepresentative (literalTorusPoint c)).symm]
    exact hC _
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC' 0)
  have hD0 := flowDerivativeBound_nonneg h P angularSpeed axialSpeed tau htau (-σ)
  have hlip : LipschitzWith (Real.toNNReal
      (C * flowDerivativeBound h P angularSpeed axialSpeed tau (-σ)))
      fun a : R3 ↦ φ (literalTorusPoint a) := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun a ↦ ?_
    refine NNReal.coe_le_coe.1 ?_
    rw [coe_nnnorm, (hfd a).fderiv, Real.coe_toNNReal _ (mul_nonneg hC0 hD0)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hC' _)
      (norm_flowFDeriv_le_of_mem_uIcc h P angularSpeed axialSpeed tau htau right_mem_uIcc _)
      (norm_nonneg _) hC0)
  -- the classes of the transported field and of its advection
  have hφae : (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ) : Torus 3 → C3)
      =ᵐ[volume] φ := flowCompL2_toLp_coe_ae h P angularSpeed axialSpeed tau σ hψL
  have hφL : MemLp φ 2 volume := (Lp.memLp _).ae_eq hφae
  have hadv : ∀ x, literalAdvection 𝐮 φ x =
      literalAdvection 𝐮 ψ (literalFlow h P angularSpeed axialSpeed tau (-σ) x) := by
    intro x
    obtain ⟨a, rfl⟩ := literalTorusPoint_surjective x
    rw [literalAdvection_literalTorusPoint, (hfd a).fderiv, ContinuousLinearMap.comp_apply,
      flowFDeriv_apply_literalVelocity, ← literalTorusPoint_literalFlowLift,
      literalAdvection_literalTorusPoint]
  have hχae : (flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _) : Torus 3 → C3)
      =ᵐ[volume] literalAdvection 𝐮 φ := by
    filter_upwards [flowCompL2_toLp_coe_ae h P angularSpeed axialSpeed tau σ hχL] with x hx
    rw [hx, hadv]
  have hadvL : MemLp (literalAdvection 𝐮 φ) 2 volume := (Lp.memLp _).ae_eq hχae
  have key := IsIdealWeakSolution.weakIdentity_of_lipschitz h P angularSpeed axialSpeed tau htau
    hW hdiff hlip hφL hadvL hs ht
  have e1 : hφL.toLp φ = flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ) :=
    Lp.ext (hφL.coeFn_toLp.trans hφae.symm)
  have e2 : hadvL.toLp _ = flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _) :=
    Lp.ext (hadvL.coeFn_toLp.trans hχae.symm)
  rwa [e1, e2] at key

/-! ## The pulled-back pairing and the energy bound -/

/-- **The pulled-back pairing.**  If `W` is continuous on `[−T, T]`, vanishes at `0` and
satisfies the weak identity with the transported test pairs of `ψ`, then
`⟪ψ ∘ Φ_{-t}, W t⟫ = ∫₀ᵗ ⟪ψ ∘ Φ_{-τ}, (W τ·∇)u⟫ dτ` on `[−T, T]`: in the derivative of
`t ↦ ⟪ψ ∘ Φ_{-t}, W t⟫` the two advection terms cancel. -/
theorem inner_flowCompL2_eq_intervalIntegral (htau : 0 ≤ tau) {T : ℝ} {W : ℝ → LiteralC3L2}
    (hc : ContinuousOn W (Icc (-T) T)) {ψ : Torus 3 → C3} (hψ : IsIdealTestField ψ)
    (hψL : MemLp ψ 2 volume) (hχL : MemLp (literalAdvection 𝐮 ψ) 2 volume)
    (hweak : ∀ σ : ℝ, ∀ s ∈ Icc (-T) T, ∀ t ∈ Icc (-T) T,
      IdealWeakIdentity 𝐮 W s t (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ))
        (flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _)))
    (h0 : W 0 = 0) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau t (hψL.toLp ψ)) (W t) =
      ∫ τ in 0..t, inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau τ (hψL.toLp ψ))
        (literalStretchL2 𝐮 (W τ)) := by
  set S := literalStretchL2 𝐮
  set Pf : ℝ → LiteralC3L2 := fun σ ↦ flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ)
    with hPf
  set Qf : ℝ → LiteralC3L2 := fun σ ↦ flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _)
    with hQf
  have hPc : Continuous Pf := continuous_flowCompL2_apply h P angularSpeed axialSpeed tau _
  have hQc : Continuous Qf := continuous_flowCompL2_apply h P angularSpeed axialSpeed tau _
  have h0T : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hfc : ContinuousOn (fun σ ↦ inner ℂ (Pf σ) (W σ)) (Icc (-T) T) :=
    hPc.continuousOn.inner hc
  have hf'c : ContinuousOn (fun σ ↦ inner ℂ (Pf σ) (S (W σ))) (Icc (-T) T) :=
    hPc.continuousOn.inner (S.continuous.comp_continuousOn hc)
  have hderiv : ∀ τ ∈ Ioo (-T) T,
      HasDerivAt (fun σ ↦ inner ℂ (Pf σ) (W σ)) (inner ℂ (Pf τ) (S (W τ))) τ := by
    intro τ hτ
    have hnhds : Icc (-T) T ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    have hWτ : ContinuousAt W τ := hc.continuousAt hnhds
    have hW2 : ContinuousAt (fun q : ℝ × ℝ ↦ W q.2) (τ, τ) :=
      ContinuousAt.comp (x := (τ, τ)) hWτ continuousAt_snd
    have key := hasDerivAt_diag_of_eq_intervalIntegral (G := fun σ ρ ↦ inner ℂ (Pf σ) (W ρ))
      (A := fun σ ρ ↦ inner ℂ (Pf σ) (S (W ρ)) + inner ℂ (Qf σ) (W ρ))
      (B := -inner ℂ (Qf τ) (W τ)) (t := τ) ?_ ?_ ?_ ?_
    · simpa using key
    · filter_upwards [hnhds] with σ hσ
      exact hweak σ τ (Ioo_subset_Icc_self hτ) σ hσ
    · filter_upwards [hnhds] with σ hσ
      exact (((continuousOn_const.inner (S.continuous.comp_continuousOn hc)).add
        (continuousOn_const.inner hc)).mono
          (uIcc_subset_Icc (Ioo_subset_Icc_self hτ) hσ)).intervalIntegrable
    · exact ((hPc.continuousAt.comp continuousAt_fst).inner
        (S.continuous.continuousAt.comp hW2)).add
          ((hQc.continuousAt.comp continuousAt_fst).inner hW2)
    · exact hasDerivAt_inner_flowCompL2 h P angularSpeed axialSpeed tau htau hψ hψL hχL (W τ) τ
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (f := fun σ ↦ inner ℂ (Pf σ) (W σ)) (hfc.mono (uIcc_subset_Icc h0T ht))
    (fun x hx ↦ (hderiv x ⟨lt_of_le_of_lt (le_min (by linarith [ht.1, ht.2]) ht.1) hx.1,
      lt_of_lt_of_le hx.2 (max_le (by linarith [ht.1, ht.2]) ht.2)⟩).hasDerivWithinAt)
    (hf'c.mono (uIcc_subset_Icc h0T ht)).intervalIntegrable
  rw [hFTC, h0, inner_zero_right, sub_zero]

/-- **The energy bound** `‖W t‖ ≤ ‖∇u‖ |∫₀ᵗ ‖W τ‖ dτ|` on `[−T, T]`, for `W` continuous on
`[−T, T]`, vanishing at `0` and satisfying the weak identity with all transported test pairs.
The pulled-back pairing bounds `⟪ψ, W t ∘ Φ_t⟫` by `‖ψ‖` times the right-hand side; the test
fields are dense and composition with the flow is an isometry. -/
theorem norm_le_mul_abs_intervalIntegral (htau : 0 ≤ tau) {T : ℝ} {W : ℝ → LiteralC3L2}
    (hc : ContinuousOn W (Icc (-T) T))
    (hweak : ∀ ψ : Torus 3 → C3, IsIdealTestField ψ → ∀ (hψL : MemLp ψ 2 volume)
      (hχL : MemLp (literalAdvection 𝐮 ψ) 2 volume) (σ : ℝ), ∀ s ∈ Icc (-T) T,
      ∀ t ∈ Icc (-T) T,
      IdealWeakIdentity 𝐮 W s t (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ))
        (flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _)))
    (h0 : W 0 = 0) {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖W t‖ ≤ ‖literalStretchL2 𝐮‖ * |∫ τ in 0..t, ‖W τ‖| := by
  set S := literalStretchL2 𝐮
  set X := flowCompL2 h P angularSpeed axialSpeed tau (-t) (W t)
  set R := ‖S‖ * |∫ τ in 0..t, ‖W τ‖|
  have hR : 0 ≤ R := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have h0T : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  have hintW : IntervalIntegrable (fun τ ↦ ‖W τ‖) volume 0 t :=
    (hc.norm.mono (uIcc_subset_Icc h0T ht)).intervalIntegrable
  have htest : ∀ θ ∈ {f : LiteralC3L2 | ∃ φ : Torus 3 → C3, IsIdealTestField φ ∧
      ∃ hφ : MemLp φ 2 (volume : Measure (Torus 3)), f = hφ.toLp φ},
      ‖inner ℂ θ X‖ ≤ ‖θ‖ * R := by
    rintro θ ⟨ψ, hψ, hψL, rfl⟩
    have hχL : MemLp (literalAdvection 𝐮 ψ) 2 volume := by
      obtain ⟨C, hC⟩ := exists_norm_literalAdvection_le h P angularSpeed axialSpeed tau htau hψ
      exact MemLp.of_bound (aestronglyMeasurable_literalAdvection h P angularSpeed axialSpeed tau
        htau hψ) C (ae_of_all _ hC)
    have hid := inner_flowCompL2_eq_intervalIntegral h P angularSpeed axialSpeed tau htau hc hψ
      hψL hχL (hweak ψ hψ hψL hχL) h0 ht
    rw [← inner_flowCompL2, hid]
    have hpt : ∀ τ, ‖inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau τ (hψL.toLp ψ))
        (S (W τ))‖ ≤ ‖hψL.toLp ψ‖ * ‖S‖ * ‖W τ‖ := fun τ ↦ by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [norm_flowCompL2_apply, mul_assoc]
      exact mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
    have hle : ‖∫ τ in 0..t, inner ℂ (flowCompL2 h P angularSpeed axialSpeed tau τ
        (hψL.toLp ψ)) (S (W τ))‖ ≤ |∫ τ in 0..t, ‖hψL.toLp ψ‖ * ‖S‖ * ‖W τ‖| := by
      rcases le_total 0 t with hle | hle
      · exact (intervalIntegral.norm_integral_le_of_norm_le hle (ae_of_all _ fun τ _ ↦ hpt τ)
          (hintW.const_mul _)).trans (le_abs_self _)
      · have h' := intervalIntegral.norm_integral_le_of_norm_le hle
          (ae_of_all _ fun τ _ ↦ hpt τ) (hintW.symm.const_mul _)
        rw [intervalIntegral.integral_symm 0 t, intervalIntegral.integral_symm 0 t,
          norm_neg] at h'
        exact h'.trans (neg_le_abs _)
    rw [intervalIntegral.integral_const_mul, abs_mul,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at hle
    calc _ ≤ _ := hle
      _ = ‖hψL.toLp ψ‖ * R := by ring
  have hclosed : IsClosed {θ : LiteralC3L2 | ‖inner ℂ θ X‖ ≤ ‖θ‖ * R} :=
    isClosed_le (continuous_id.inner continuous_const).norm (continuous_norm.mul continuous_const)
  have hX : ‖inner ℂ X X‖ ≤ ‖X‖ * R :=
    hclosed.closure_subset_iff.2 htest (dense_idealTestFieldL2.closure_eq ▸ mem_univ X)
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hX
  have hXW : ‖X‖ = ‖W t‖ := norm_flowCompL2_apply h P angularSpeed axialSpeed tau _ _
  rw [← hXW]
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [norm_nonneg X]

/-- **Uniqueness for the weak identity with transported test pairs**: a field continuous on
`[−T, T]`, vanishing at `0` and satisfying the weak identity with all transported test pairs
vanishes on `[−T, T]` (the energy bound and Grönwall's argument, forward and backward in time). -/
theorem eq_zero_of_forall_idealWeakIdentity_flowCompL2 (htau : 0 ≤ tau) {T : ℝ}
    {W : ℝ → LiteralC3L2} (hc : ContinuousOn W (Icc (-T) T))
    (hweak : ∀ ψ : Torus 3 → C3, IsIdealTestField ψ → ∀ (hψL : MemLp ψ 2 volume)
      (hχL : MemLp (literalAdvection 𝐮 ψ) 2 volume) (σ : ℝ), ∀ s ∈ Icc (-T) T,
      ∀ t ∈ Icc (-T) T,
      IdealWeakIdentity 𝐮 W s t (flowCompL2 h P angularSpeed axialSpeed tau σ (hψL.toLp ψ))
        (flowCompL2 h P angularSpeed axialSpeed tau σ (hχL.toLp _)))
    (h0 : W 0 = 0) : ∀ t ∈ Icc (-T) T, W t = 0 := by
  intro t ht
  have hb := fun s (hs : s ∈ Icc (-T) T) ↦
    norm_le_mul_abs_intervalIntegral h P angularSpeed axialSpeed tau htau hc hweak h0 hs
  have hpos : ∀ s ∈ Icc 0 T, ‖W s‖ = 0 :=
    eq_zero_of_le_mul_abs_intervalIntegral (w := fun s ↦ ‖W s‖)
      (hc.norm.mono (Icc_subset_Icc (by linarith [ht.1, ht.2]) le_rfl))
      (fun s _ ↦ norm_nonneg _) (fun s hs ↦ hb s ⟨by linarith [hs.1, ht.1, ht.2], hs.2⟩)
  have hneg : ∀ s ∈ Icc 0 T, ‖W (-s)‖ = 0 := by
    refine eq_zero_of_le_mul_abs_intervalIntegral (w := fun s ↦ ‖W (-s)‖)
      (M := ‖literalStretchL2 𝐮‖)
      (hc.norm.comp continuousOn_neg fun s hs ↦ ⟨by linarith [hs.2], by linarith [hs.1, hs.2]⟩)
      (fun s _ ↦ norm_nonneg _) fun s hs ↦ ?_
    have := hb (-s) ⟨by linarith [hs.2], by linarith [hs.1, hs.2]⟩
    have e : ∫ τ in 0..s, ‖W (-τ)‖ = -∫ τ in 0..-s, ‖W τ‖ := by
      rw [intervalIntegral.integral_comp_neg (fun τ ↦ ‖W τ‖), neg_zero,
        intervalIntegral.integral_symm]
    rw [e, abs_neg]
    exact this
  rcases le_total 0 t with hle | hle
  · exact norm_eq_zero.1 (hpos t ⟨hle, ht.2⟩)
  · have := hneg (-t) ⟨by linarith, by linarith [ht.1]⟩
    rw [neg_neg] at this
    exact norm_eq_zero.1 this

/-! ## Uniqueness of weak solutions and of the solution group -/

/-- **Uniqueness of weak solutions** of the ideal induction equation (proof of
`cor:ideal-growth`): a weak solution on `[−T, T]` vanishing at time `0` vanishes on `[−T, T]`.
The paper obtains it from Ambrosio–Crippa (Proposition 2.3 there); here it is proved by testing
against test fields transported by the flow. -/
theorem IsIdealWeakSolution.eq_zero (htau : 0 ≤ tau) {T : ℝ} {W : ℝ → LiteralC3L2}
    (hW : IsIdealWeakSolution 𝐮 T W) (h0 : W 0 = 0) :
    ∀ t ∈ Set.Icc (-T) T, W t = 0 :=
  eq_zero_of_forall_idealWeakIdentity_flowCompL2 h P angularSpeed axialSpeed tau htau
    hW.continuousOn (fun _ hψ hψL hχL σ _ hs _ ht ↦
      idealWeakIdentity_flowCompL2_of_isIdealWeakSolution h P angularSpeed axialSpeed tau htau
        hW hψ hψL hχL σ hs ht) h0

/-- **Uniqueness of the solution group** (proof of `cor:ideal-growth`): every solution group of
the ideal induction equation on `L²_σ` is the ideal Cauchy group `idealGroup`.  The difference
of the two orbits of a datum satisfies the weak identity with all transported test pairs and
vanishes at time `0`. -/
theorem IsIdealSolutionGroup.eq_idealGroup (htau : 0 ≤ tau)
    {G : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace}
    (hG : IsIdealSolutionGroup 𝐮 G) : G = idealGroup h P angularSpeed axialSpeed tau := by
  have hI := isIdealSolutionGroup_idealGroup h P angularSpeed axialSpeed tau htau
  funext t
  refine ContinuousLinearMap.ext fun B ↦ Subtype.ext ?_
  have h1 := hG.weakSolution B |t|
  have h2 := hI.weakSolution B |t|
  have hz := eq_zero_of_forall_idealWeakIdentity_flowCompL2 h P angularSpeed axialSpeed tau htau
    (W := fun s ↦ ((G s B : literalSolenoidalSubspace) : LiteralC3L2) -
      ((idealGroup h P angularSpeed axialSpeed tau s B : literalSolenoidalSubspace) :
        LiteralC3L2))
    (h1.continuousOn.sub h2.continuousOn)
    (fun _ hψ hψL hχL σ _ hs _ hu ↦ IdealWeakIdentity.sub
      (h1.continuousOn.mono (uIcc_subset_Icc hs hu)) (h2.continuousOn.mono (uIcc_subset_Icc hs hu))
      (idealWeakIdentity_flowCompL2_of_isIdealWeakSolution h P angularSpeed axialSpeed tau htau
        h1 hψ hψL hχL σ hs hu)
      (idealWeakIdentity_flowCompL2_of_isIdealWeakSolution h P angularSpeed axialSpeed tau htau
        h2 hψ hψL hχL σ hs hu))
    (by simp [hG.group_zero, hI.group_zero]) t ⟨neg_abs_le t, le_abs_self t⟩
  exact sub_eq_zero.1 hz

/-- **The solution group exists and is unique** (proof of `cor:ideal-growth`): `idealGroup` is a
solution group of the ideal induction equation on `L²_σ`, and the only one. -/
theorem existsUnique_isIdealSolutionGroup (htau : 0 ≤ tau) :
    ∃! G : ℝ → literalSolenoidalSubspace →L[ℂ] literalSolenoidalSubspace,
      IsIdealSolutionGroup 𝐮 G :=
  ⟨idealGroup h P angularSpeed axialSpeed tau,
    isIdealSolutionGroup_idealGroup h P angularSpeed axialSpeed tau htau,
    fun _ hG ↦ IsIdealSolutionGroup.eq_idealGroup h P angularSpeed axialSpeed tau htau hG⟩

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
