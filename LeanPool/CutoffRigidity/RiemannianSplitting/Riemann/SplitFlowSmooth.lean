/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.JointDifferentiableCoordinateLocalFlow

/-! # Smooth dependence of Euclidean local flows on the initial point

`exists_contDiff_localFlow`: if `F : E → E` is `C^∞` on a finite-dimensional space, the local flow
is `C^n` jointly in the initial point and the time, for every `n`.  The proof is by induction on
`n`, applying the induction hypothesis to the variational field
`(y, J) ↦ (F y, DF(y) ∘ J)` on `E × (E →L E)`, whose flow is `(flow, D flow)`.  The `C¹` flow
theory of the project (`exists_jointContDiff_lipschitz_coordinate_localFlow`,
`hasFDerivAt_coordinateFlow_of_variation`) is the base of the induction.
-/

@[expose] public section
open Set Filter Metric Function
open scoped Topology NNReal ContDiff

namespace CutoffRigidity.Riemann

universe u

section Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The variational vector field `(y, J) ↦ (F y, DF(y) ∘ J)`. -/
noncomputable def variationalField (F : E → E) (p : E × (E →L[ℝ] E)) : E × (E →L[ℝ] E) :=
  (F p.1, (fderiv ℝ F p.1).comp p.2)

theorem contDiff_variationalField {n : WithTop ℕ∞} {F : E → E} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (variationalField F) := by
  unfold variationalField
  refine ((hF.of_le (le_self_add)).comp contDiff_fst).prodMk ?_
  have h1 : ContDiff ℝ n (fun p : E × (E →L[ℝ] E) => fderiv ℝ F p.1) :=
    (hF.fderiv_right (m := n) le_rfl).comp contDiff_fst
  exact h1.clm_comp contDiff_snd

/-- Initial-point derivative of a flow from the variational equation, in both time directions. -/
theorem hasFDerivAt_flow_of_variation_symm [FiniteDimensional ℝ E]
    {F : E → E} (hF : ContDiff ℝ 1 F) {α : E → ℝ → E}
    (x : E) {r θ : ℝ} (hr : 0 < r)
    (hαzero : ∀ y ∈ ball x r, α y 0 = y)
    (hαD : ∀ y ∈ ball x r, ∀ s ∈ Ioo (-θ) θ, HasDerivAt (α y) (F (α y s)) s)
    {L : ℝ≥0} (hαLip : ∀ s ∈ Ioo (-θ) θ, LipschitzOnWith L (fun y ↦ α y s) (ball x r))
    {J : ℝ → E →L[ℝ] E} (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ s ∈ Ioo (-θ) θ, HasDerivAt J ((fderiv ℝ F (α x s)).comp (J s)) s)
    {t : ℝ} (ht : t ∈ Ioo (-θ) θ) :
    HasFDerivAt (fun y ↦ α y t) (J t) x := by
  have hx : x ∈ ball x r := mem_ball_self hr
  have hθ : 0 < θ := by linarith [ht.1, ht.2]
  rcases le_or_gt 0 t with h0 | h0
  · refine hasFDerivAt_coordinateFlow_of_variation hF x hr h0 hαzero
      (fun y hy s hs => hαD y hy s ⟨by linarith [hs.1, ht.1, hs.2], by linarith [hs.2, ht.2, hs.1]⟩)
      (fun s hs => hαLip s ⟨by linarith [hs.1, ht.1, hs.2], by linarith [hs.2, ht.2, hs.1]⟩) hJzero
      (fun s hs => hJD s ⟨by linarith [hs.1, ht.1, hs.2], by linarith [hs.2, ht.2, hs.1]⟩)
  · have hneg : ∀ s ∈ Ioo (-θ) θ, -s ∈ Ioo (-θ) θ := fun s hs =>
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hmem : ∀ s ∈ Icc 0 (-t), -s ∈ Ioo (-θ) θ := fun s hs =>
      ⟨by linarith [hs.2, ht.1], by linarith [hs.1, hθ]⟩
    have := hasFDerivAt_coordinateFlow_of_variation (F := fun z => -F z) hF.neg x hr
      (T := -t) (by linarith) (α := fun y s => α y (-s))
      (by simpa using hαzero)
      (fun y hy s hs => by
        simpa only [Function.comp_def, neg_one_smul] using
          (hαD y hy (-s) (hmem s hs)).scomp s (hasDerivAt_neg s))
      (L := L) (fun s hs => hαLip (-s) (hmem s hs))
      (J := fun s => J (-s)) (by simpa using hJzero)
      (fun s hs => by
        have := (hJD (-s) (hmem s hs)).scomp s (hasDerivAt_neg s)
        refine HasDerivAt.congr_deriv this ?_
        ext v
        simp [fderiv_fun_neg])
    simpa using this

end Variational

section Flow

/-- The continuous linear map `(J, w) ↦ ((v, s) ↦ J v + s • w)`. -/
noncomputable def jointDerivMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ((E →L[ℝ] E) × E) →L[ℝ] (E × ℝ →L[ℝ] E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => p.1.coprod (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) p.2)
      map_add' := fun p q => by ext <;> simp
      map_smul' := fun c p => by ext <;> simp }

theorem jointDerivMap_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E →L[ℝ] E) (w : E) (v : E) (s : ℝ) :
    jointDerivMap E (J, w) (v, s) = J v + s • w := by
  simp [jointDerivMap]

/-- Smooth dependence of the local flow on the initial point, by induction on the order. -/
theorem exists_contDiff_localFlow (m : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (F : E → E), ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F → ∀ x₀ : E,
      ∃ r > (0 : ℝ), ∃ θ > (0 : ℝ), ∃ α : E → ℝ → E,
        ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (uncurry α) (ball x₀ r ×ˢ Ioo (-θ) θ) ∧
        ∀ x ∈ ball x₀ r, α x 0 = x ∧ ∀ t ∈ Ioo (-θ) θ, HasDerivAt (α x) (F (α x t)) t := by
  induction m with
  | zero =>
    intro E _ _ _ F hF x₀
    obtain ⟨r, hr, θ, hθ, α, L', h1, h2, h3⟩ :=
      exists_jointContDiff_lipschitz_coordinate_localFlow (by simpa using hF) x₀
    exact ⟨r, hr, θ, hθ, α, by simpa using h1, h2⟩
  | succ m ih =>
    intro E _ _ _ F hF x₀
    obtain ⟨ρ, hρ, θ, hθ, β, hβC, hβ⟩ := ih (E × (E →L[ℝ] E)) (variationalField F)
      (contDiff_variationalField (n := ((m + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast hF))
      (x₀, ContinuousLinearMap.id ℝ E)
    set p₀ : E × (E →L[ℝ] E) := (x₀, ContinuousLinearMap.id ℝ E) with hp₀
    set ι : E × ℝ → (E × (E →L[ℝ] E)) × ℝ := fun q => ((q.1, ContinuousLinearMap.id ℝ E), q.2)
      with hι
    have hι_smooth : ContDiff ℝ ∞ ι :=
      ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    have hβC1 : ContDiffOn ℝ 1 (uncurry β) (ball p₀ ρ ×ˢ Ioo (-θ) θ) :=
      hβC.of_le (by exact_mod_cast Nat.le_add_left 1 m)
    -- Lipschitz neighbourhood of `(p₀, 0)`.
    have hat : ContDiffAt ℝ 1 (uncurry β) (p₀, 0) :=
      hβC1.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
        ⟨mem_ball_self hρ, ⟨by linarith, hθ⟩⟩)
    obtain ⟨K, N, hN, hKN⟩ := hat.exists_lipschitzOnWith
    obtain ⟨ε₀, hε₀, hε₀N⟩ := Metric.mem_nhds_iff.mp hN
    set ε : ℝ := min ε₀ (min ρ θ) with hε
    have hεpos : 0 < ε := lt_min hε₀ (lt_min hρ hθ)
    have hερ : ε ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
    have hεθ : ε ≤ θ := (min_le_right _ _).trans (min_le_right _ _)
    have hεN : ball p₀ ε ×ˢ ball (0 : ℝ) ε ⊆ N := by
      have h := ball_prod_same p₀ (0 : ℝ) ε
      rw [h]
      exact (ball_subset_ball (min_le_left _ _)).trans hε₀N
    set α : E → ℝ → E := fun x t => (β (x, ContinuousLinearMap.id ℝ E) t).1 with hα
    set J : E → ℝ → (E →L[ℝ] E) := fun x t => (β (x, ContinuousLinearMap.id ℝ E) t).2 with hJ
    have hmemball : ∀ x ∈ ball x₀ ε, (x, ContinuousLinearMap.id ℝ E) ∈ ball p₀ ε := by
      intro x hx
      rw [mem_ball, Prod.dist_eq]
      simpa [hp₀, dist_self] using hx
    have hmemD : ∀ x ∈ ball x₀ ε, ∀ t ∈ Ioo (-ε) ε,
        ((x, ContinuousLinearMap.id ℝ E), t) ∈ ball p₀ ρ ×ˢ Ioo (-θ) θ := by
      intro x hx t ht
      refine ⟨ball_subset_ball hερ (hmemball x hx), ?_, ?_⟩ <;> linarith [ht.1, ht.2]
    have hα0 : ∀ x ∈ ball x₀ ε, α x 0 = x := by
      intro x hx
      have := (hβ _ (ball_subset_ball hερ (hmemball x hx))).1
      simp [hα, this]
    have hJ0 : ∀ x ∈ ball x₀ ε, J x 0 = ContinuousLinearMap.id ℝ E := by
      intro x hx
      have := (hβ _ (ball_subset_ball hερ (hmemball x hx))).1
      simp [hJ, this]
    have hβD : ∀ x ∈ ball x₀ ε, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun s => β (x, ContinuousLinearMap.id ℝ E) s)
          (variationalField F (β (x, ContinuousLinearMap.id ℝ E) t)) t := by
      intro x hx t ht
      exact (hβ _ (ball_subset_ball hερ (hmemball x hx))).2 t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hαD : ∀ x ∈ ball x₀ ε, ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α x) (F (α x t)) t := fun x hx t ht =>
      (hβD x hx t ht).fst
    have hJD : ∀ x ∈ ball x₀ ε, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (J x) ((fderiv ℝ F (α x t)).comp (J x t)) t := fun x hx t ht =>
      (hβD x hx t ht).snd
    have hLip : ∀ t ∈ Ioo (-ε) ε, LipschitzOnWith K (fun y => α y t) (ball x₀ ε) := by
      intro t ht
      have h1 : LipschitzOnWith K (uncurry β) (ball p₀ ε ×ˢ ball (0 : ℝ) ε) := hKN.mono hεN
      have h2 : LipschitzWith 1 (fun y : E => ((y, ContinuousLinearMap.id ℝ E), t)) :=
        LipschitzWith.of_dist_le_mul fun y y' => by
          simp [Prod.dist_eq, dist_self]
      have h3 : LipschitzOnWith (K * 1) (uncurry β ∘ fun y : E =>
          ((y, ContinuousLinearMap.id ℝ E), t)) (ball x₀ ε) :=
        h1.comp h2.lipschitzOnWith (fun y hy => ⟨hmemball y hy, by simpa [Real.dist_eq, abs_lt]
            using ht⟩)
      have h4 := (LipschitzWith.prod_fst).comp_lipschitzOnWith h3
      simpa [hα, Function.comp_def] using h4
    have hε2 : 0 < ε / 2 := half_pos hεpos
    have hsub : ∀ x ∈ ball x₀ (ε / 2), ball x (ε / 2) ⊆ ball x₀ ε := by
      intro x hx y hy
      rw [mem_ball] at hx hy ⊢
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add hy hx
        _ = ε := by ring
    have htsub : Ioo (-(ε / 2)) (ε / 2) ⊆ Ioo (-ε) ε := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hderiv : ∀ x ∈ ball x₀ (ε / 2), ∀ t ∈ Ioo (-(ε / 2)) (ε / 2),
        HasFDerivAt (fun y => α y t) (J x t) x := by
      intro x hx t ht
      refine hasFDerivAt_flow_of_variation_symm (hF.of_le (by exact_mod_cast Nat.le_add_left 1 (m
          + 1))) x hε2
        (θ := ε / 2) (α := α) (L := K)
        (fun y hy => hα0 y (hsub x hx hy))
        (fun y hy s hs => hαD y (hsub x hx hy) s (htsub hs))
        (fun s hs => (hLip s (htsub hs)).mono (hsub x hx))
        (J := J x) (hJ0 x (ball_subset_ball (by linarith) hx))
        (fun s hs => hJD x (ball_subset_ball (by linarith) hx) s (htsub hs)) ht
    set U : Set (E × ℝ) := ball x₀ (ε / 2) ×ˢ Ioo (-(ε / 2)) (ε / 2) with hU
    have hUopen : IsOpen U := isOpen_ball.prod isOpen_Ioo
    have hιU : MapsTo ι U (ball p₀ ρ ×ˢ Ioo (-θ) θ) := by
      intro q hq
      exact hmemD q.1 (ball_subset_ball (by linarith) hq.1) q.2 (htsub hq.2)
    have hβι : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (uncurry β ∘ ι) U :=
      hβC.comp (hι_smooth.of_le (by exact_mod_cast le_top)).contDiffOn hιU
    have hαC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (uncurry α) U := by
      have := (contDiff_fst (E := E) (F := E →L[ℝ] E)).comp_contDiffOn hβι
      exact this
    have hJC : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun q : E × ℝ => J q.1 q.2) U :=
      (contDiff_snd (E := E) (F := E →L[ℝ] E)).comp_contDiffOn hβι
    have hFα : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun q : E × ℝ => F (α q.1 q.2)) U :=
      (hF.of_le (by exact_mod_cast Nat.le_succ (m + 1))).comp_contDiffOn hαC
    have hfderiv : ∀ q ∈ U, fderiv ℝ (uncurry α) q =
        jointDerivMap E (J q.1 q.2, F (α q.1 q.2)) := by
      rintro ⟨x, t⟩ hq
      have hdiff : DifferentiableAt ℝ (uncurry α) (x, t) :=
        (hαC.differentiableOn (by simp)).differentiableAt
          (hUopen.mem_nhds hq)
      have hl : HasFDerivAt (fun y => uncurry α (y, t))
          ((fderiv ℝ (uncurry α) (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x :=
        HasFDerivAt.comp (g := uncurry α) (f := fun e : E => (e, t)) x hdiff.hasFDerivAt
          (hasFDerivAt_prodMk_left x t)
      have hr : HasFDerivAt (fun s => uncurry α (x, s))
          ((fderiv ℝ (uncurry α) (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)) t :=
        HasFDerivAt.comp (g := uncurry α) (f := fun s : ℝ => (x, s)) t hdiff.hasFDerivAt
          (hasFDerivAt_prodMk_right x t)
      have hl' : (fderiv ℝ (uncurry α) (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) = J x t :=
        hl.unique (hderiv x hq.1 t hq.2)
      have hr' : (fderiv ℝ (uncurry α) (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
          ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (F (α x t)) :=
        hr.unique (hαD x (ball_subset_ball (by linarith) hq.1) t (htsub hq.2)).hasFDerivAt
      refine ContinuousLinearMap.ext fun ⟨v, s⟩ => ?_
      have hvs : ((v, s) : E × ℝ) = ContinuousLinearMap.inl ℝ E ℝ v + ContinuousLinearMap.inr ℝ E
          ℝ s := by
        simp
      have e1 := congrArg (fun L => L v) hl'
      have e2 := congrArg (fun L => L s) hr'
      simp only [ContinuousLinearMap.comp_apply] at e1 e2
      change _ = jointDerivMap E (J x t, F (α x t)) (v, s)
      rw [jointDerivMap_apply, hvs, map_add, e1, e2]
      simp
    rw [show ((m + 1 + 1 : ℕ) : WithTop ℕ∞) = ((m + 1 : ℕ) : WithTop ℕ∞) + 1 by push_cast; rfl]
    refine ⟨ε / 2, hε2, ε / 2, hε2, α, ?_, fun x hx => ⟨hα0 x (ball_subset_ball (by linarith) hx),
      fun t ht => hαD x (ball_subset_ball (by linarith) hx) t (htsub ht)⟩⟩
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hUopen]
    refine ⟨hαC.differentiableOn (by simp), fun h => by simp at h, ?_⟩
    have : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun q : E × ℝ => jointDerivMap E (J q.1 q.2, F (α q.1 q.2))) U :=
      (jointDerivMap E).contDiff.comp_contDiffOn (hJC.prodMk hFα)
    exact this.congr hfderiv

end Flow

end CutoffRigidity.Riemann
