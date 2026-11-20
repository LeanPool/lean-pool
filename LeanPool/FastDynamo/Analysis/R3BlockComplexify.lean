/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.R3Assembly

/-!
# Block matrices on `ℝ³` and their coordinatewise complexification

Two pieces of linear algebra on `R3 = EuclideanSpace ℝ (Fin 3)` and `C3 = EuclideanSpace ℂ
(Fin 3)`, used by the derivative flow of `FastDynamo/Dynamics/Flow/FlowDerivative.lean` and by
its truncated twin in `FastDynamo/Dynamics/Ideal/TruncatedFlow.lean`, but containing no flow, no
velocity and no parameter.

* **The block matrix.**  `flowBlockCLM A phi` is the endomorphism `[[A, 0], [phi, 1]]` of `ℝ³`
  built from an endomorphism `A` of the chart plane `ℝ × ℝ` and a functional `phi` on it: `A`
  acts on the first two coordinates, `phi` shears them into the third, and the third coordinate
  is otherwise untouched.  Delivered with its coordinates, the identity case, the operator-norm
  bound `norm_flowBlockCLM_le`, the Lipschitz and continuity statements in `(A, phi)` and the
  measurability of a composite.  `norm_fin3_le_two_mul_of_forall_norm_le` is the elementary
  inequality `‖w‖ ≤ 2 · max‖wᵢ‖` behind those bounds — the cost of assembling three sup-normed
  coordinates into one Euclidean vector.
* **The complexification.**  `r3Complexify M` is the endomorphism of `ℂ³` with the same matrix
  entries `(M eⱼ)ᵢ` as `M`, with `r3Complexify_id`, `r3Complexify_comp`, the bound
  `‖r3Complexify M‖ ≤ 6 ‖M‖` and the Lipschitz and continuity statements.  Those matrix entries
  are exactly what the `cauchy` clause of `IsIdealInductionGroup`
  (`FastDynamo/Dynamics/ParticleFlow.lean`) pairs with the amplitude.

The metric convention matters: `ℝ × ℝ` carries the **sup** metric while `R3` is Euclidean, which
is where the factors `2` and `6` come from.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open scoped NNReal

/-! ## Coordinates of a three-dimensional Euclidean space -/

/-- **A three-dimensional Euclidean vector whose coordinates are all bounded by `C` has norm at
most `2 C`.**  The sharp factor is `√3`; `2` is what every estimate below uses. -/
theorem norm_fin3_le_two_mul_of_forall_norm_le {𝕜 : Type*} [RCLike 𝕜]
    {v : EuclideanSpace 𝕜 (Fin 3)} {C : ℝ} (hv : ∀ j : Fin 3, ‖v j‖ ≤ C) : ‖v‖ ≤ 2 * C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  have hsq : ∀ j : Fin 3, ‖v j‖ ^ 2 ≤ C ^ 2 := by
    intro j
    have hj := hv j
    have hn := norm_nonneg (v j)
    nlinarith
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ j : Fin 3, ‖v j‖ ^ 2 ≤ (2 * C) ^ 2 := by
    have h0 := hsq 0
    have h1 := hsq 1
    have h2 := hsq 2
    rw [Fin.sum_univ_three]
    nlinarith
  calc Real.sqrt (∑ j : Fin 3, ‖v j‖ ^ 2) ≤ Real.sqrt ((2 * C) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 2 * C := Real.sqrt_sq (by linarith)

/-! ## The block matrix of the derivative flow -/

/-- The transverse coordinate pair of a vector of `ℝ³`, as a continuous linear map to the
sup-normed chart plane `ℝ × ℝ`. -/
def flowPairProjection : R3 →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj 0).prod (EuclideanSpace.proj 1)

/-- The transverse projection reads the first two coordinates. -/
@[simp] theorem flowPairProjection_apply (w : R3) : flowPairProjection w = (w 0, w 1) := rfl

/-- The transverse projection is norm non-increasing: the sup norm of two coordinates is at most
the Euclidean norm of the whole vector. -/
theorem norm_flowPairProjection_le (w : R3) : ‖flowPairProjection w‖ ≤ ‖w‖ := by
  rw [flowPairProjection_apply, Prod.norm_mk]
  exact max_le (PiLp.norm_apply_le w 0) (PiLp.norm_apply_le w 1)

/-- **The block matrix `[[A, 0], [φ, 1]]`** of the module docstring, as a continuous linear
endomorphism of `ℝ³`: the transverse block `A` acts on the first two coordinates, the functional
`φ` shears them into the third, and the third coordinate is otherwise untouched. -/
def flowBlockCLM (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (phi : (ℝ × ℝ) →L[ℝ] ℝ) : R3 →L[ℝ] R3 :=
  ((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] R3).comp
    (ContinuousLinearMap.pi
      ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp (A.comp flowPairProjection),
        (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (A.comp flowPairProjection),
        (EuclideanSpace.proj 2 : R3 →L[ℝ] ℝ) + phi.comp flowPairProjection])

/-- First coordinate of the block matrix. -/
@[simp] theorem flowBlockCLM_apply_zero (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (phi : (ℝ × ℝ) →L[ℝ] ℝ)
    (w : R3) : flowBlockCLM A phi w 0 = (A (w 0, w 1)).1 := rfl

/-- Second coordinate of the block matrix. -/
@[simp] theorem flowBlockCLM_apply_one (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (phi : (ℝ × ℝ) →L[ℝ] ℝ)
    (w : R3) : flowBlockCLM A phi w 1 = (A (w 0, w 1)).2 := rfl

/-- Third coordinate of the block matrix: the shear plus the identity. -/
@[simp] theorem flowBlockCLM_apply_two (A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (phi : (ℝ × ℝ) →L[ℝ] ℝ)
    (w : R3) : flowBlockCLM A phi w 2 = w 2 + phi (w 0, w 1) := rfl

/-- The block matrix of the identity and the zero functional is the identity of `ℝ³`. -/
theorem flowBlockCLM_id : flowBlockCLM (ContinuousLinearMap.id ℝ (ℝ × ℝ)) 0 =
    ContinuousLinearMap.id ℝ R3 := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  refine r3_ext ?_ ?_ ?_
  · rw [flowBlockCLM_apply_zero]; rfl
  · rw [flowBlockCLM_apply_one]; rfl
  · rw [flowBlockCLM_apply_two]; simp

/-- **The uniform bound for the block matrix**, pointwise form: if the transverse block has norm
at most `C` and the shear functional has norm at most `C - 1`, then the block matrix moves a
vector by at most `2 C` times its norm, the factor `2` being the cost of assembling three
sup-normed coordinates into a Euclidean vector. -/
theorem norm_flowBlockCLM_apply_le {A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ} {phi : (ℝ × ℝ) →L[ℝ] ℝ} {C : ℝ}
    (hA : ‖A‖ ≤ C) (hphi : ‖phi‖ + 1 ≤ C) (w : R3) :
    ‖flowBlockCLM A phi w‖ ≤ 2 * C * ‖w‖ := by
  have hpair : ‖(w 0, w 1)‖ ≤ ‖w‖ := norm_flowPairProjection_le w
  have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hAw : ‖A (w 0, w 1)‖ ≤ C * ‖w‖ :=
    le_trans (A.le_opNorm _) (mul_le_mul hA hpair (norm_nonneg _) (le_trans (norm_nonneg _) hA))
  have h0 : ‖flowBlockCLM A phi w 0‖ ≤ C * ‖w‖ :=
    le_trans (le_trans (le_of_eq (by rw [flowBlockCLM_apply_zero])) (norm_fst_le _)) hAw
  have h1 : ‖flowBlockCLM A phi w 1‖ ≤ C * ‖w‖ :=
    le_trans (le_trans (le_of_eq (by rw [flowBlockCLM_apply_one])) (norm_snd_le _)) hAw
  have h2 : ‖flowBlockCLM A phi w 2‖ ≤ C * ‖w‖ := by
    rw [flowBlockCLM_apply_two]
    have hphiw : ‖phi (w 0, w 1)‖ ≤ ‖phi‖ * ‖w‖ :=
      le_trans (phi.le_opNorm _) (mul_le_mul_of_nonneg_left hpair (norm_nonneg _))
    have hw2 : ‖w 2‖ ≤ ‖w‖ := PiLp.norm_apply_le w 2
    have hcomb : ‖w 2 + phi (w 0, w 1)‖ ≤ ‖w‖ + ‖phi‖ * ‖w‖ :=
      le_trans (norm_add_le _ _) (add_le_add hw2 hphiw)
    nlinarith
  have hcoord : ∀ j : Fin 3, ‖flowBlockCLM A phi w j‖ ≤ C * ‖w‖ := by
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have := norm_fin3_le_two_mul_of_forall_norm_le hcoord
  linarith

/-- **The uniform bound for the block matrix**, operator-norm form. -/
theorem norm_flowBlockCLM_le {A : (ℝ × ℝ) →L[ℝ] ℝ × ℝ} {phi : (ℝ × ℝ) →L[ℝ] ℝ} {C : ℝ}
    (hA : ‖A‖ ≤ C) (hphi : ‖phi‖ + 1 ≤ C) : ‖flowBlockCLM A phi‖ ≤ 2 * C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) hA
  exact ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    (norm_flowBlockCLM_apply_le hA hphi)

/-- The block matrix depends Lipschitz-continuously on its two blocks: the constant term of the
third row cancels in a difference. -/
theorem norm_flowBlockCLM_sub_le (A A' : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (phi phi' : (ℝ × ℝ) →L[ℝ] ℝ) :
    ‖flowBlockCLM A phi - flowBlockCLM A' phi'‖ ≤ 2 * (‖A - A'‖ + ‖phi - phi'‖) := by
  have hA : (0 : ℝ) ≤ ‖A - A'‖ := norm_nonneg _
  have hphi : (0 : ℝ) ≤ ‖phi - phi'‖ := norm_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun w ↦ ?_
  have hpair : ‖(w 0, w 1)‖ ≤ ‖w‖ := norm_flowPairProjection_le w
  have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hAw : ‖(A - A') (w 0, w 1)‖ ≤ ‖A - A'‖ * ‖w‖ :=
    le_trans ((A - A').le_opNorm _) (mul_le_mul_of_nonneg_left hpair (norm_nonneg _))
  have hphiw : ‖(phi - phi') (w 0, w 1)‖ ≤ ‖phi - phi'‖ * ‖w‖ :=
    le_trans ((phi - phi').le_opNorm _) (mul_le_mul_of_nonneg_left hpair (norm_nonneg _))
  have hsubA : (A - A') (w 0, w 1) = A (w 0, w 1) - A' (w 0, w 1) := rfl
  have hsubphi : (phi - phi') (w 0, w 1) = phi (w 0, w 1) - phi' (w 0, w 1) := rfl
  have hcoord : ∀ j : Fin 3,
      ‖(flowBlockCLM A phi - flowBlockCLM A' phi') w j‖ ≤ (‖A - A'‖ + ‖phi - phi'‖) * ‖w‖ := by
    have h0 : ‖(flowBlockCLM A phi - flowBlockCLM A' phi') w 0‖ ≤
        (‖A - A'‖ + ‖phi - phi'‖) * ‖w‖ := by
      have hval : (flowBlockCLM A phi - flowBlockCLM A' phi') w 0 =
          ((A - A') (w 0, w 1)).1 := by rw [hsubA]; rfl
      rw [hval]
      have := le_trans (norm_fst_le ((A - A') (w 0, w 1))) hAw
      nlinarith
    have h1 : ‖(flowBlockCLM A phi - flowBlockCLM A' phi') w 1‖ ≤
        (‖A - A'‖ + ‖phi - phi'‖) * ‖w‖ := by
      have hval : (flowBlockCLM A phi - flowBlockCLM A' phi') w 1 =
          ((A - A') (w 0, w 1)).2 := by rw [hsubA]; rfl
      rw [hval]
      have := le_trans (norm_snd_le ((A - A') (w 0, w 1))) hAw
      nlinarith
    have h2 : ‖(flowBlockCLM A phi - flowBlockCLM A' phi') w 2‖ ≤
        (‖A - A'‖ + ‖phi - phi'‖) * ‖w‖ := by
      have hval : (flowBlockCLM A phi - flowBlockCLM A' phi') w 2 =
          (phi - phi') (w 0, w 1) := by
        have hlhs : (flowBlockCLM A phi - flowBlockCLM A' phi') w 2 =
            w 2 + phi (w 0, w 1) - (w 2 + phi' (w 0, w 1)) := rfl
        rw [hlhs, hsubphi]
        ring
      rw [hval]
      nlinarith
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have := norm_fin3_le_two_mul_of_forall_norm_le hcoord
  nlinarith

/-- The block matrix is a Lipschitz function of its two blocks, hence continuous. -/
theorem lipschitzWith_flowBlockCLM :
    LipschitzWith 4
      (fun q : ((ℝ × ℝ) →L[ℝ] ℝ × ℝ) × ((ℝ × ℝ) →L[ℝ] ℝ) ↦ flowBlockCLM q.1 q.2) := by
  refine LipschitzWith.of_dist_le_mul fun q q' ↦ ?_
  have h1 : ‖q.1 - q'.1‖ ≤ ‖q - q'‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, Prod.dist_eq]
    exact le_max_left _ _
  have h2 : ‖q.2 - q'.2‖ ≤ ‖q - q'‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, Prod.dist_eq]
    exact le_max_right _ _
  have hmain := norm_flowBlockCLM_sub_le q.1 q'.1 q.2 q'.2
  have hcoe : ((4 : ℝ≥0) : ℝ) = 4 := by norm_num
  rw [dist_eq_norm, dist_eq_norm, hcoe]
  linarith

/-- The block matrix is a continuous function of its two blocks. -/
theorem continuous_flowBlockCLM :
    Continuous (fun q : ((ℝ × ℝ) →L[ℝ] ℝ × ℝ) × ((ℝ × ℝ) →L[ℝ] ℝ) ↦ flowBlockCLM q.1 q.2) :=
  lipschitzWith_flowBlockCLM.continuous

/-- A block matrix whose two blocks depend continuously on a parameter is continuous in that
parameter. -/
theorem continuous_flowBlockCLM_comp {alpha : Type*} [TopologicalSpace alpha]
    {A : alpha → ((ℝ × ℝ) →L[ℝ] ℝ × ℝ)} {phi : alpha → ((ℝ × ℝ) →L[ℝ] ℝ)}
    (hA : Continuous A) (hphi : Continuous phi) :
    Continuous fun x ↦ flowBlockCLM (A x) (phi x) := by
  have hcomp := continuous_flowBlockCLM.comp (hA.prodMk hphi)
  exact hcomp

/-- A block matrix whose two blocks depend measurably on a parameter is measurable in that
parameter. -/
theorem measurable_flowBlockCLM_comp {alpha : Type*} [MeasurableSpace alpha]
    {A : alpha → ((ℝ × ℝ) →L[ℝ] ℝ × ℝ)} {phi : alpha → ((ℝ × ℝ) →L[ℝ] ℝ)}
    (hA : Measurable A) (hphi : Measurable phi) :
    Measurable fun x ↦ flowBlockCLM (A x) (phi x) := by
  have hcomp := continuous_flowBlockCLM.measurable.comp (hA.prodMk hphi)
  exact hcomp

/-! ## The complexification of a real endomorphism of `ℝ³` -/

/-- **Expansion of a real endomorphism of `ℝ³` in the standard basis**: the `i`-th coordinate of
`M u` is the `i`-th row of the matrix of `M` paired with `u`. -/
theorem r3_apply_eq_sum (M : R3 →L[ℝ] R3) (u : R3) (i : Fin 3) :
    M u i = ∑ k : Fin 3, u k * M (EuclideanSpace.single k (1 : ℝ)) i := by
  have hu : u = ∑ k : Fin 3, u k • EuclideanSpace.single k (1 : ℝ) := by
    refine PiLp.ext fun j ↦ ?_
    simp [Pi.single_apply, Finset.sum_ite_eq]
  conv_lhs => rw [hu]
  rw [map_sum]
  simp

/-- **The coordinatewise complexification** of a real endomorphism of `ℝ³`: the `ℂ`-linear
endomorphism of `ℂ³` with the same matrix entries `(M e_j)_i`.  These are exactly the entries the
`cauchy` clause of `IsIdealInductionGroup` (`FastDynamo/Dynamics/ParticleFlow.lean`) pairs with
the complex amplitude, `eq:ideal-cauchy-formula`. -/
def r3Complexify (M : R3 →L[ℝ] R3) : C3 →L[ℂ] C3 :=
  ((EuclideanSpace.equiv (Fin 3) ℂ).symm : (Fin 3 → ℂ) →L[ℂ] C3).comp
    (ContinuousLinearMap.pi fun i : Fin 3 ↦
      ∑ j : Fin 3, ((M (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) •
        (EuclideanSpace.proj j : C3 →L[ℂ] ℂ))

/-- The complexification acts by the real matrix entries of `M`. -/
theorem r3Complexify_apply (M : R3 →L[ℝ] R3) (v : C3) (i : Fin 3) :
    r3Complexify M v i =
      ∑ j : Fin 3, ((M (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * v j := by
  change (∑ j : Fin 3, ((M (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) •
      (EuclideanSpace.proj j : C3 →L[ℂ] ℂ)) v = _
  simp

/-- The complexification is additive in the matrix, in the form the Lipschitz estimate needs. -/
theorem r3Complexify_sub (M N : R3 →L[ℝ] R3) :
    r3Complexify (M - N) = r3Complexify M - r3Complexify N := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  refine PiLp.ext fun i ↦ ?_
  have hR : (r3Complexify M - r3Complexify N) v i = r3Complexify M v i - r3Complexify N v i := rfl
  rw [hR, r3Complexify_apply, r3Complexify_apply, r3Complexify_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hentry : (M - N) (EuclideanSpace.single j (1 : ℝ)) i =
      M (EuclideanSpace.single j (1 : ℝ)) i - N (EuclideanSpace.single j (1 : ℝ)) i := rfl
  rw [hentry]
  push_cast
  ring

/-- **The uniform bound for the complexification**, pointwise form.  The factor `6` is the product
of the coordinate count `3` of the matrix row and the Euclidean assembly factor `2`. -/
theorem norm_r3Complexify_apply_le (M : R3 →L[ℝ] R3) (v : C3) :
    ‖r3Complexify M v‖ ≤ 6 * ‖M‖ * ‖v‖ := by
  have hcoord : ∀ i : Fin 3, ‖r3Complexify M v i‖ ≤ 3 * (‖M‖ * ‖v‖) := by
    intro i
    rw [r3Complexify_apply]
    have hterm : ∀ j : Fin 3,
        ‖((M (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * v j‖ ≤ ‖M‖ * ‖v‖ := by
      intro j
      have hsingle : ‖(EuclideanSpace.single j (1 : ℝ) : R3)‖ = 1 := by
        rw [EuclideanSpace.single, PiLp.norm_single]
        simp
      have hMe : ‖M (EuclideanSpace.single j (1 : ℝ))‖ ≤ ‖M‖ := by
        have := M.le_opNorm (EuclideanSpace.single j (1 : ℝ))
        rw [hsingle, mul_one] at this
        exact this
      have hentry : ‖M (EuclideanSpace.single j (1 : ℝ)) i‖ ≤ ‖M‖ :=
        le_trans (PiLp.norm_apply_le _ i) hMe
      have hv : ‖v j‖ ≤ ‖v‖ := PiLp.norm_apply_le v j
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul hentry hv (norm_nonneg _) (norm_nonneg _)
    calc ‖∑ j : Fin 3, ((M (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * v j‖
        ≤ ∑ j : Fin 3, ‖((M (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * v j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin 3, ‖M‖ * ‖v‖ := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = 3 * (‖M‖ * ‖v‖) := by rw [Finset.sum_const]; simp
  have := norm_fin3_le_two_mul_of_forall_norm_le hcoord
  linarith

/-- **The uniform bound for the complexification**, operator-norm form. -/
theorem norm_r3Complexify_le (M : R3 →L[ℝ] R3) : ‖r3Complexify M‖ ≤ 6 * ‖M‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_r3Complexify_apply_le M)

/-- The complexification is Lipschitz, hence continuous and measurable. -/
theorem lipschitzWith_r3Complexify : LipschitzWith 6 r3Complexify := by
  refine LipschitzWith.of_dist_le_mul fun M N ↦ ?_
  have hcoe : ((6 : ℝ≥0) : ℝ) = 6 := by norm_num
  rw [dist_eq_norm, dist_eq_norm, hcoe, ← r3Complexify_sub]
  exact norm_r3Complexify_le (M - N)

/-- The complexification is continuous. -/
theorem continuous_r3Complexify : Continuous r3Complexify :=
  lipschitzWith_r3Complexify.continuous

/-- The complexification of the identity is the identity. -/
theorem r3Complexify_id :
    r3Complexify (ContinuousLinearMap.id ℝ R3) = ContinuousLinearMap.id ℂ C3 := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  refine PiLp.ext fun i ↦ ?_
  have hentry : ∀ j : Fin 3,
      ((ContinuousLinearMap.id ℝ R3 (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : ℂ) * v j =
        if j = i then v j else 0 := by
    intro j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji, Ne.symm hji]
  change r3Complexify (ContinuousLinearMap.id ℝ R3) v i = v i
  rw [r3Complexify_apply]
  simp only [hentry]
  rw [Finset.sum_ite_eq' Finset.univ i fun j : Fin 3 ↦ v j]
  simp

/-- **The complexification is multiplicative**: complexifying a composite is composing the
complexifications.  This is what turns the chain rule for `DΦ_t` into the group law for the
complexified symbol. -/
theorem r3Complexify_comp (M N : R3 →L[ℝ] R3) :
    r3Complexify (M.comp N) = (r3Complexify M).comp (r3Complexify N) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  refine PiLp.ext fun i ↦ ?_
  have hR : ((r3Complexify M).comp (r3Complexify N)) v i =
      r3Complexify M (r3Complexify N v) i := rfl
  rw [hR, r3Complexify_apply, r3Complexify_apply]
  have hstep : ∀ k : Fin 3,
      ((M (EuclideanSpace.single k (1 : ℝ)) i : ℝ) : ℂ) * r3Complexify N v k =
        ∑ j : Fin 3, ((M (EuclideanSpace.single k (1 : ℝ)) i : ℝ) : ℂ) *
          (((N (EuclideanSpace.single j (1 : ℝ)) k : ℝ) : ℂ) * v j) := by
    intro k
    rw [r3Complexify_apply, Finset.mul_sum]
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hentry : (M.comp N) (EuclideanSpace.single j (1 : ℝ)) i =
      ∑ k : Fin 3, N (EuclideanSpace.single j (1 : ℝ)) k *
        M (EuclideanSpace.single k (1 : ℝ)) i :=
    r3_apply_eq_sum M (N (EuclideanSpace.single j (1 : ℝ))) i
  rw [hentry]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end

end FastDynamo
