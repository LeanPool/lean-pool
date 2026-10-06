/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeChainSpace
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductFamilyTwo
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingHilbertChain

/-!
# The projected Navier–Stokes nonlinearity on the Sobolev tower

`prop:lps-smoothing`: on the spaces of slot vectors, the product `H^M × H^M → H^M` (`M ≥ 2`) is
a bounded bilinear map and the Leray projection acts slotwise. Consequently the right-hand side
`N(v)_i = Σ_k ∂_k ∂_k v_i - P(Σ_j v_j ∂_j v)_i` of the projected Navier–Stokes equation is a smooth
map `H^(n+3) → H^(n+1)` of divergence-free fields.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The Leibniz family is almost everywhere linear in its first family (`prop:lps-smoothing`). -/
theorem lps_leibniz_ae_linear_left (α : List (Fin 3)) (c : ℝ)
    {D D₁ D₂ E : List (Fin 3) → Vec3 → ℝ}
    (h : ∀ β : List (Fin 3), β.length ≤ α.length →
      D β =ᵐ[volume] fun x => c * D₁ β x + D₂ β x) :
    sobolevLeibnizFamily α D E =ᵐ[volume]
      fun x => c * sobolevLeibnizFamily α D₁ E x + sobolevLeibnizFamily α D₂ E x := by
  induction α generalizing D D₁ D₂ E with
  | nil =>
      filter_upwards [h [] le_rfl] with x hx
      simp only [sobolevLeibnizFamily, hx]
      ring
  | cons j α ih =>
      have h1 := ih (D := fun β => D (j :: β)) (D₁ := fun β => D₁ (j :: β))
        (D₂ := fun β => D₂ (j :: β)) (E := E)
        (fun β hβ => h (j :: β) (by simp only [List.length_cons]; omega))
      have h2 := ih (D := D) (D₁ := D₁) (D₂ := D₂) (E := fun β => E (j :: β))
        (fun β hβ => h β (by simp only [List.length_cons]; omega))
      filter_upwards [h1, h2] with x hx1 hx2
      simp only [sobolevLeibnizFamily]
      rw [hx1, hx2]
      ring

/-- The Leibniz family is almost everywhere linear in its second family (`prop:lps-smoothing`). -/
theorem lps_leibniz_ae_linear_right (α : List (Fin 3)) (c : ℝ)
    {D E E₁ E₂ : List (Fin 3) → Vec3 → ℝ}
    (h : ∀ β : List (Fin 3), β.length ≤ α.length →
      E β =ᵐ[volume] fun x => c * E₁ β x + E₂ β x) :
    sobolevLeibnizFamily α D E =ᵐ[volume]
      fun x => c * sobolevLeibnizFamily α D E₁ x + sobolevLeibnizFamily α D E₂ x := by
  induction α generalizing D E E₁ E₂ with
  | nil =>
      filter_upwards [h [] le_rfl] with x hx
      simp only [sobolevLeibnizFamily, hx]
      ring
  | cons j α ih =>
      have h1 := ih (D := fun β => D (j :: β)) (E := E) (E₁ := E₁) (E₂ := E₂)
        (fun β hβ => h β (by simp only [List.length_cons]; omega))
      have h2 := ih (D := D) (E := fun β => E (j :: β)) (E₁ := fun β => E₁ (j :: β))
        (E₂ := fun β => E₂ (j :: β))
        (fun β hβ => h (j :: β) (by simp only [List.length_cons]; omega))
      filter_upwards [h1, h2] with x hx1 hx2
      simp only [sobolevLeibnizFamily]
      rw [hx1, hx2]
      ring

/-- Linear relations between square-integrable functions hold for their `L²` classes
(`prop:lps-smoothing`). -/
theorem lps_toLp_linear {f g h : Vec3 → ℝ} (c : ℝ) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hfgh : f =ᵐ[volume] fun x => c * g x + h x) :
    hf.toLp f = c • hg.toLp g + hh.toLp h := by
  apply Lp.ext
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, hh.coeFn_toLp, hfgh,
    Lp.coeFn_add (c • hg.toLp g) (hh.toLp h), Lp.coeFn_smul c (hg.toLp g)]
    with x h1 h2 h3 h4 h5 h6
  rw [h5, Pi.add_apply, h6, Pi.smul_apply, h1, h2, h3, h4, smul_eq_mul]

/-- The slots of a linear combination are almost everywhere the linear combination of the
slots (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_ae_linear {M : ℕ} (c : ℝ) (v w : lpsSobolevSpace M) (α : List (Fin 3)) :
    ⇑(lpsSlotCLM M α (c • v + w)) =ᵐ[volume]
      fun x => c * lpsSlotCLM M α v x + lpsSlotCLM M α w x := by
  rw [map_add, map_smul]
  filter_upwards [Lp.coeFn_add (c • lpsSlotCLM M α v) (lpsSlotCLM M α w),
    Lp.coeFn_smul c (lpsSlotCLM M α v)] with x h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]

/-- The Leibniz family of the slots of two elements of `H^M(ℝ³)`, `M ≥ 2`, is a Sobolev family
of their product (`prop:lps-smoothing`). -/
theorem lps_mul_family {M : ℕ} (hM : 2 ≤ M) (v w : lpsSobolevSpace M) :
    IsSobolevFamilyOn M univ
      (sobolevLeibnizFamily [] (fun β => ⇑(lpsSlotCLM M β v)) (fun β => ⇑(lpsSlotCLM M β w)))
      (fun α => sobolevLeibnizFamily α (fun β => ⇑(lpsSlotCLM M β v))
        (fun β => ⇑(lpsSlotCLM M β w))) :=
  ((lps_sobolevFamily_mul_of_two_le hM).choose_spec.2 _ _ _ _ (lps_isSobolevFamilyOn_slot v)
    (lps_isSobolevFamilyOn_slot w)).1

/-- The product of two elements of `H^M(ℝ³)`, `M ≥ 2`: its slots are the Leibniz family of the
slots (`prop:lps-smoothing`). -/
@[expose] def lpsMulFun (M : ℕ) (hM : 2 ≤ M) (v w : lpsSobolevSpace M) : lpsSobolevSpace M :=
  lpsSobolevOf M
    (fun α => sobolevLeibnizFamily α (fun β => ⇑(lpsSlotCLM M β v)) (fun β => ⇑(lpsSlotCLM M β w)))
    (lps_mul_family hM v w)

/-- The Leibniz family of the slots of two elements of `H^M(ℝ³)`, `M ≥ 2`, is a Sobolev family
of their product (`prop:lps-smoothing`). -/
theorem lps_mul_family_memLp {M : ℕ} (hM : 2 ≤ M) (v w : lpsSobolevSpace M) {α : List (Fin 3)}
    (hα : α.length ≤ M) :
    MemLp (sobolevLeibnizFamily α (fun β => ⇑(lpsSlotCLM M β v))
      (fun β => ⇑(lpsSlotCLM M β w))) 2 volume := by
  simpa only [Measure.restrict_univ] using (lps_mul_family hM v w).memL2 α hα

/-- The slots of a product are the `L²` classes of the Leibniz family (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_mulFun {M : ℕ} (hM : 2 ≤ M) (v w : lpsSobolevSpace M) {α : List (Fin 3)}
    (hα : α.length ≤ M) :
    lpsSlotCLM M α (lpsMulFun M hM v w) = (lps_mul_family_memLp hM v w hα).toLp
      (sobolevLeibnizFamily α (fun β => ⇑(lpsSlotCLM M β v)) (fun β => ⇑(lpsSlotCLM M β w))) :=
  lpsSlotCLM_sobolevOf (lps_mul_family hM v w) hα

/-- The product is linear in its first factor (`prop:lps-smoothing`). -/
theorem lpsMulFun_linear_left {M : ℕ} (hM : 2 ≤ M) (c : ℝ) (v v' w : lpsSobolevSpace M) :
    lpsMulFun M hM (c • v + v') w = c • lpsMulFun M hM v w + lpsMulFun M hM v' w := by
  refine lps_sobolevSpace_ext fun α hα => ?_
  rw [map_add, map_smul, lpsSlotCLM_mulFun hM _ _ hα, lpsSlotCLM_mulFun hM _ _ hα,
    lpsSlotCLM_mulFun hM _ _ hα]
  exact lps_toLp_linear c (lps_mul_family_memLp hM _ _ hα) (lps_mul_family_memLp hM _ _ hα)
    (lps_mul_family_memLp hM _ _ hα)
    (lps_leibniz_ae_linear_left α c fun β _ => lpsSlotCLM_ae_linear c v v' β)

/-- The product is linear in its second factor (`prop:lps-smoothing`). -/
theorem lpsMulFun_linear_right {M : ℕ} (hM : 2 ≤ M) (c : ℝ) (v w w' : lpsSobolevSpace M) :
    lpsMulFun M hM v (c • w + w') = c • lpsMulFun M hM v w + lpsMulFun M hM v w' := by
  refine lps_sobolevSpace_ext fun α hα => ?_
  rw [map_add, map_smul, lpsSlotCLM_mulFun hM _ _ hα, lpsSlotCLM_mulFun hM _ _ hα,
    lpsSlotCLM_mulFun hM _ _ hα]
  exact lps_toLp_linear c (lps_mul_family_memLp hM _ _ hα) (lps_mul_family_memLp hM _ _ hα)
    (lps_mul_family_memLp hM _ _ hα)
    (lps_leibniz_ae_linear_right α c fun β _ => lpsSlotCLM_ae_linear c w w' β)

/-- The product with a zero first factor vanishes (`prop:lps-smoothing`). -/
theorem lpsMulFun_zero_left {M : ℕ} (hM : 2 ≤ M) (w : lpsSobolevSpace M) :
    lpsMulFun M hM 0 w = 0 := by
  have h := lpsMulFun_linear_left hM 1 0 0 w
  rw [one_smul, add_zero, one_smul] at h
  simpa using (congrArg (· - lpsMulFun M hM 0 w) h).symm

/-- The product with a zero second factor vanishes (`prop:lps-smoothing`). -/
theorem lpsMulFun_zero_right {M : ℕ} (hM : 2 ≤ M) (v : lpsSobolevSpace M) :
    lpsMulFun M hM v 0 = 0 := by
  have h := lpsMulFun_linear_right hM 1 v 0 0
  rw [one_smul, add_zero, one_smul] at h
  simpa using (congrArg (· - lpsMulFun M hM v 0) h).symm

/-- The product as a bilinear map (`prop:lps-smoothing`). -/
@[expose] def lpsMulLin (M : ℕ) (hM : 2 ≤ M) :
    lpsSobolevSpace M →ₗ[ℝ] lpsSobolevSpace M →ₗ[ℝ] lpsSobolevSpace M :=
  LinearMap.mk₂ ℝ (lpsMulFun M hM)
    (fun v v' w => by simpa only [one_smul] using lpsMulFun_linear_left hM 1 v v' w)
    (fun c v w => by
      simpa only [add_zero, lpsMulFun_zero_left hM] using lpsMulFun_linear_left hM c v 0 w)
    (fun v w w' => by simpa only [one_smul] using lpsMulFun_linear_right hM 1 v w w')
    (fun c v w => by
      simpa only [add_zero, lpsMulFun_zero_right hM] using lpsMulFun_linear_right hM c v w 0)

/-- The squared Sobolev norm of the slots is bounded by the number of words times the squared
norm of the slot vector (`prop:lps-smoothing`). -/
theorem lps_sobolevNormSq_slot_le {M : ℕ} (v : lpsSobolevSpace M) :
    sobolevNormSqOn M univ (fun α => ⇑(lpsSlotCLM M α v)) ≤
      ((sobolevWords M).card : ℝ) * ‖v‖ ^ 2 := by
  unfold sobolevNormSqOn
  calc (∑ α ∈ sobolevWords M, ∫ x in univ, (lpsSlotCLM M α v x) ^ 2)
      = ∑ α ∈ sobolevWords M, ‖lpsSlotCLM M α v‖ ^ 2 := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Measure.restrict_univ, lps_scalar_l2_norm_sq_integral]
    _ ≤ ∑ _α ∈ sobolevWords M, ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun α _ =>
          pow_le_pow_left₀ (norm_nonneg _) (lpsSlotCLM_norm_le α v) 2
    _ = ((sobolevWords M).card : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The product `H^M(ℝ³) × H^M(ℝ³) → H^M(ℝ³)`, `M ≥ 2`, is bounded (`prop:lps-smoothing`). -/
theorem lps_mulFun_bound {M : ℕ} (hM : 2 ≤ M) :
    ∃ K : ℝ, ∀ v w : lpsSobolevSpace M, ‖lpsMulFun M hM v w‖ ≤ K * ‖v‖ * ‖w‖ := by
  obtain ⟨C, hC, hmul⟩ := lps_sobolevFamily_mul_of_two_le hM
  refine ⟨Real.sqrt (C * ((sobolevWords M).card : ℝ) ^ 2), fun v w => ?_⟩
  have hbound : 0 ≤ Real.sqrt (C * ((sobolevWords M).card : ℝ) ^ 2) * ‖v‖ * ‖w‖ := by
    positivity
  change ‖(lpsMulFun M hM v w : LpsSlots M)‖ ≤ _
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro α
  rw [← lpsSlotCLM_of_mem α.2]
  have hα : α.1.length ≤ M := mem_sobolevWords.1 α.2
  rw [lpsSlotCLM_mulFun hM v w hα]
  have hfam := (hmul _ _ _ _ (lps_isSobolevFamilyOn_slot v) (lps_isSobolevFamilyOn_slot w)).2
  have hterm : (∫ x, sobolevLeibnizFamily α.1 (fun β => ⇑(lpsSlotCLM M β v))
      (fun β => ⇑(lpsSlotCLM M β w)) x ^ 2) ≤
      sobolevNormSqOn M univ (fun α => sobolevLeibnizFamily α (fun β => ⇑(lpsSlotCLM M β v))
        (fun β => ⇑(lpsSlotCLM M β w))) := by
    unfold sobolevNormSqOn
    rw [Measure.restrict_univ]
    exact Finset.single_le_sum (f := fun α => ∫ x, sobolevLeibnizFamily α
      (fun β => ⇑(lpsSlotCLM M β v)) (fun β => ⇑(lpsSlotCLM M β w)) x ^ 2)
      (fun γ _ => integral_nonneg fun x => sq_nonneg _) α.2
  have hv := lps_sobolevNormSq_slot_le v
  have hw := lps_sobolevNormSq_slot_le w
  have hNv : 0 ≤ sobolevNormSqOn M univ (fun α => ⇑(lpsSlotCLM M α v)) :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNw : 0 ≤ sobolevNormSqOn M univ (fun α => ⇑(lpsSlotCLM M α w)) :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hprod : C * sobolevNormSqOn M univ (fun α => ⇑(lpsSlotCLM M α v)) *
      sobolevNormSqOn M univ (fun α => ⇑(lpsSlotCLM M α w)) ≤
      C * (((sobolevWords M).card : ℝ) * ‖v‖ ^ 2) * (((sobolevWords M).card : ℝ) * ‖w‖ ^ 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hv hC) hw hNw (by positivity)
  have hsqrt : (Real.sqrt (C * ((sobolevWords M).card : ℝ) ^ 2) * ‖v‖ * ‖w‖) ^ 2 =
      C * (((sobolevWords M).card : ℝ) * ‖v‖ ^ 2) * (((sobolevWords M).card : ℝ) * ‖w‖ ^ 2) := by
    have h0 : 0 ≤ C * ((sobolevWords M).card : ℝ) ^ 2 := by positivity
    rw [mul_pow, mul_pow, Real.sq_sqrt h0]
    ring
  have hsq : ‖(lps_mul_family_memLp hM v w hα).toLp _‖ ^ 2 ≤
      (Real.sqrt (C * ((sobolevWords M).card : ℝ) ^ 2) * ‖v‖ * ‖w‖) ^ 2 := by
    rw [lps_scalar_l2_toLp_norm_sq_integral, hsqrt]
    exact (hterm.trans hfam).trans hprod
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hbound (by norm_num)).1 hsq

/-- The product `H^M(ℝ³) × H^M(ℝ³) → H^M(ℝ³)`, `M ≥ 2`, as a bounded bilinear map
(`prop:lps-smoothing`). -/
@[expose] def lpsMulCLM (M : ℕ) (hM : 2 ≤ M) :
    lpsSobolevSpace M →L[ℝ] lpsSobolevSpace M →L[ℝ] lpsSobolevSpace M :=
  LinearMap.mkContinuous₂ (lpsMulLin M hM) (lps_mulFun_bound hM).choose
    (lps_mulFun_bound hM).choose_spec

/-- The bounded bilinear product evaluates to the product of slot vectors (`prop:lps-smoothing`). -/
theorem lpsMulCLM_apply {M : ℕ} (hM : 2 ≤ M) (v w : lpsSobolevSpace M) :
    lpsMulCLM M hM v w = lpsMulFun M hM v w := rfl

/-- The product of the order-zero slots of two elements of `H^M(ℝ³)`, `M ≥ 2`, is square
integrable (`prop:lps-smoothing`). -/
theorem lps_memLp_mul_nil {M : ℕ} (hM : 2 ≤ M) (v w : lpsSobolevSpace M) :
    MemLp (fun x => lpsSlotCLM M [] v x * lpsSlotCLM M [] w x) 2 volume :=
  lps_mul_family_memLp hM v w (α := []) (Nat.zero_le _)

/-- The order-zero slot of a product is the product of the order-zero slots
(`prop:lps-smoothing`). -/
theorem lpsSlotCLM_mul_nil {M : ℕ} (hM : 2 ≤ M) (v w : lpsSobolevSpace M) :
    lpsSlotCLM M [] (lpsMulCLM M hM v w) =
      (lps_memLp_mul_nil hM v w).toLp
        (fun x => lpsSlotCLM M [] v x * lpsSlotCLM M [] w x) :=
  lpsSlotCLM_mulFun hM v w (Nat.zero_le _)

/-- The slot `α` of the Leray projection of a field of slot vectors (`prop:lps-smoothing`). -/
@[expose] def lpsLeraySlotCLM (M : ℕ) (α : List (Fin 3)) (i : Fin 3) :
    (Fin 3 → lpsSobolevSpace M) →L[ℝ] Lp ℝ 2 (volume : Measure Vec3) :=
  (PiLp.proj 2 (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3)) i).comp
    (lpsLerayP.comp
      ((PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin 3 => Lp ℝ 2 (volume : Measure Vec3))).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i' => (lpsSlotCLM M α).comp (ContinuousLinearMap.proj i'))))

/-- The slot of the Leray projection is the projection of the slots (`prop:lps-smoothing`). -/
theorem lpsLeraySlotCLM_apply (M : ℕ) (α : List (Fin 3)) (i : Fin 3)
    (F : Fin 3 → lpsSobolevSpace M) :
    lpsLeraySlotCLM M α i F = lpsLerayP (WithLp.toLp 2 fun i' => lpsSlotCLM M α (F i')) i := rfl

/-- The Leray projection acting slotwise on fields of `H^M(ℝ³)` slot vectors
(`prop:lps-smoothing`). -/
@[expose] def lpsLerayCLM (M : ℕ) : (Fin 3 → lpsSobolevSpace M) →L[ℝ] (Fin 3 → lpsSobolevSpace M) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.pi fun α : {α : List (Fin 3) // α ∈ sobolevWords M} =>
      lpsLeraySlotCLM M α.1 i).codRestrict (lpsSobolevSpace M) fun F =>
    mem_lpsSobolevSpace.2 fun α j h => by
      have hα : α.length < M := by
        have := mem_sobolevWords.1 h
        simp only [List.length_append, List.length_singleton] at this
        omega
      refine lpsLerayP_weakPartial j (fun i' => ?_) i
      exact (lps_isSobolevFamilyOn_slot (F i')).weak α j hα

/-- The slots of the slotwise Leray projection (`prop:lps-smoothing`). -/
theorem lpsSlotCLM_leray {M : ℕ} (F : Fin 3 → lpsSobolevSpace M) (i : Fin 3)
    {α : List (Fin 3)} (hα : α.length ≤ M) :
    lpsSlotCLM M α (lpsLerayCLM M F i) =
      lpsLerayP (WithLp.toLp 2 fun i' => lpsSlotCLM M α (F i')) i := by
  rw [lpsSlotCLM_of_mem (mem_sobolevWords.2 hα)]
  rfl

/-- The right-hand side of the projected Navier–Stokes equation, from `H^(n+3)` fields to
`H^(n+1)` fields: `N(v)_i = Σ_k ∂_k ∂_k v_i - P(Σ_j v_j ∂_j v)_i` (`prop:lps-smoothing`). -/
@[expose] def lpsNSMap (n : ℕ) (v : Fin 3 → lpsSobolevSpace (n + 2 + 1)) : Fin 3 → lpsSobolevSpace (n + 1) :=
  fun i => (∑ k, lpsDerivCLM (n + 1) k (lpsDerivCLM (n + 2) k (v i))) -
    lpsLerayCLM (n + 1) (fun i' => lpsInclCLM (n + 1)
      (∑ j, lpsMulCLM (n + 2) (by omega) (lpsInclCLM (n + 2) (v j))
        (lpsDerivCLM (n + 2) j (v i')))) i

/-- The projected Navier–Stokes right-hand side is a smooth map `H^(n+3) → H^(n+1)`
(`prop:lps-smoothing`). -/
theorem lpsNSMap_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (lpsNSMap n) := by
  have hlin : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) fun v : Fin 3 → lpsSobolevSpace (n + 2 + 1) =>
      ∑ k, lpsDerivCLM (n + 1) k (lpsDerivCLM (n + 2) k (v i)) := fun i =>
    ContDiff.sum fun k _ =>
      ((lpsDerivCLM (n + 1) k).comp (lpsDerivCLM (n + 2) k)).contDiff.comp
        (contDiff_apply ℝ _ i)
  have hquad : ContDiff ℝ (⊤ : ℕ∞) fun v : Fin 3 → lpsSobolevSpace (n + 2 + 1) =>
      fun i' => lpsInclCLM (n + 1) (∑ j, lpsMulCLM (n + 2) (by omega) (lpsInclCLM (n + 2) (v j))
        (lpsDerivCLM (n + 2) j (v i'))) := by
    refine contDiff_pi.2 fun i' => (lpsInclCLM (n + 1)).contDiff.comp ?_
    refine ContDiff.sum fun j _ => ContDiff.clm_apply ?_ ?_
    · have hB : ContDiff ℝ (⊤ : ℕ∞) fun x : lpsSobolevSpace (n + 2) =>
          lpsMulCLM (n + 2) (by omega) x :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := lpsSobolevSpace (n + 2))
          (F := lpsSobolevSpace (n + 2) →L[ℝ] lpsSobolevSpace (n + 2))
          (lpsMulCLM (n + 2) (by omega))
      exact hB.comp ((lpsInclCLM (n + 2)).contDiff.comp (contDiff_apply ℝ _ j))
    · exact (lpsDerivCLM (n + 2) j).contDiff.comp (contDiff_apply ℝ _ i')
  refine contDiff_pi.2 fun i => (hlin i).sub ?_
  exact (contDiff_apply ℝ _ i).comp ((lpsLerayCLM (n + 1)).contDiff.comp hquad)

/-- The product of the order-zero slot of one component with the first-order slot of another
is square integrable (`prop:lps-smoothing`). -/
theorem lps_memLp_slot_mul (n : ℕ) (v : Fin 3 → lpsSobolevSpace (n + 2 + 1)) (j i' : Fin 3) :
    MemLp (fun x => lpsSlotCLM (n + 2 + 1) [] (v j) x * lpsSlotCLM (n + 2 + 1) [j] (v i') x)
      2 volume := by
  have h := lps_mul_family_memLp (M := n + 2) (by omega) (lpsInclCLM (n + 2) (v j))
    (lpsDerivCLM (n + 2) j (v i')) (α := []) (Nat.zero_le _)
  have e1 : lpsSlotCLM (n + 2) [] (lpsInclCLM (n + 2) (v j)) = lpsSlotCLM (n + 2 + 1) [] (v j) :=
    lpsSlotCLM_incl _ (Nat.zero_le _)
  have e2 : lpsSlotCLM (n + 2) [] (lpsDerivCLM (n + 2) j (v i')) =
      lpsSlotCLM (n + 2 + 1) [j] (v i') :=
    lpsSlotCLM_deriv j _ (Nat.zero_le _)
  have h' : MemLp (fun x => lpsSlotCLM (n + 2) [] (lpsInclCLM (n + 2) (v j)) x *
      lpsSlotCLM (n + 2) [] (lpsDerivCLM (n + 2) j (v i')) x) 2 volume := h
  rw [e1, e2] at h'
  exact h'

/-- The order-zero slot of the projected Navier–Stokes right-hand side
(`prop:lps-smoothing`). -/
theorem lpsSlotCLM_NSMap_nil (n : ℕ) (v : Fin 3 → lpsSobolevSpace (n + 2 + 1)) (i : Fin 3) :
    lpsSlotCLM (n + 1) [] (lpsNSMap n v i) =
      (∑ k, lpsSlotCLM (n + 2 + 1) [k, k] (v i)) -
        lpsLerayP (WithLp.toLp 2 fun i' => ∑ j,
          (lps_memLp_slot_mul n v j i').toLp (fun x => lpsSlotCLM (n + 2 + 1) [] (v j) x *
            lpsSlotCLM (n + 2 + 1) [j] (v i') x)) i := by
  have e1 : lpsNSMap n v i = (∑ k, lpsDerivCLM (n + 1) k (lpsDerivCLM (n + 2) k (v i))) -
      lpsLerayCLM (n + 1) (fun i' => lpsInclCLM (n + 1)
        (∑ j, lpsMulCLM (n + 2) (by omega) (lpsInclCLM (n + 2) (v j))
          (lpsDerivCLM (n + 2) j (v i')))) i := rfl
  have h1 : (∑ k, lpsSlotCLM (n + 1) [] (lpsDerivCLM (n + 1) k (lpsDerivCLM (n + 2) k (v i)))) =
      ∑ k, lpsSlotCLM (n + 2 + 1) [k, k] (v i) := Finset.sum_congr rfl fun k _ => by
    rw [lpsSlotCLM_deriv k _ (Nat.zero_le _), lpsSlotCLM_deriv k _ (by simp)]
  have h3 : (fun i' => lpsSlotCLM (n + 1) [] (lpsInclCLM (n + 1)
      (∑ j, lpsMulCLM (n + 2) (by omega) (lpsInclCLM (n + 2) (v j))
        (lpsDerivCLM (n + 2) j (v i'))))) = fun i' => ∑ j,
          (lps_memLp_slot_mul n v j i').toLp (fun x => lpsSlotCLM (n + 2 + 1) [] (v j) x *
            lpsSlotCLM (n + 2 + 1) [j] (v i') x) := by
    funext i'
    rw [lpsSlotCLM_incl _ (Nat.zero_le _), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1' : lpsSlotCLM (n + 1 + 1) [] (lpsInclCLM (n + 2) (v j)) =
        lpsSlotCLM (n + 2 + 1) [] (v j) := lpsSlotCLM_incl _ (Nat.zero_le _)
    have e2' : lpsSlotCLM (n + 1 + 1) [] (lpsDerivCLM (n + 2) j (v i')) =
        lpsSlotCLM (n + 2 + 1) [j] (v i') := lpsSlotCLM_deriv j _ (Nat.zero_le _)
    rw [lpsSlotCLM_mul_nil]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [e1', e2'])
  rw [e1, map_sub, map_sum, h1, lpsSlotCLM_leray _ i (Nat.zero_le _), h3]

end ESS
