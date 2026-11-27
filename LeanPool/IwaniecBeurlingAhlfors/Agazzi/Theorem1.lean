/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Proof.RowRepresentation
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Proof.ScalarProjection.Main

/-!
# Theorem 1: the quasiconvexity of `L`

**Theorem 1** (`thm:L-quasiconvexity`): for all `A ∈ ℝ^{2×2}` and all `φ ∈ C^∞_per (Q; ℝ²)`,
`∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`.

The paper's proof (TeX lines 376–396) uses only that `φ` is Lipschitz and periodic: Lemma 4 is
stated for `W^{1,∞}_per (Q)`. `theorem1_lipschitz` states the theorem for Lipschitz periodic `φ`
(`φ ∈ W^{1,∞}_per (Q; ℝ²)`), proved by the paper's argument, and `theorem1` is the paper's
statement, for `C^∞` periodic `φ`, which are Lipschitz
(`exists_lipschitzWith_of_contDiff_of_isPeriodic`).
-/

@[expose] public section

noncomputable section

open MeasureTheory CalculusOfVariations
open scoped ContDiff

namespace Agazzi

/-! ### Helpers: `L`, `F`, `G_z`, the unit disk, gradients and integrals -/

/-- The entries of a matrix are continuous functions of it. -/
private theorem thm1_continuous_entry (i j : Fin 2) :
    Continuous fun B : Matrix (Fin 2) (Fin 2) ℝ => B i j :=
  continuous_id.matrix_elem i j

private theorem thm1_continuous_conformalPart : Continuous conformalPart := by
  have h : conformalPart = fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (((A 0 0 + A 1 1) / 2 : ℝ) : ℂ) + (((A 1 0 - A 0 1) / 2 : ℝ) : ℂ) * Complex.I := by
    funext A; exact Complex.mk_eq_add_mul_I _ _
  rw [h]
  have := thm1_continuous_entry
  fun_prop

private theorem thm1_continuous_anticonformalPart : Continuous anticonformalPart := by
  have h : anticonformalPart = fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (((A 0 0 - A 1 1) / 2 : ℝ) : ℂ) + (((A 1 0 + A 0 1) / 2 : ℝ) : ℂ) * Complex.I := by
    funext A; exact Complex.mk_eq_add_mul_I _ _
  rw [h]
  have := thm1_continuous_entry
  fun_prop

/-- `L` is continuous: the two formulas agree where `|a₊| + |a₋| = 1`. -/
private theorem thm1_continuous_integrandL : Continuous integrandL := by
  have hp := thm1_continuous_conformalPart
  have hm := thm1_continuous_anticonformalPart
  refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const ?_
  intro A hA
  have : ‖anticonformalPart A‖ = 1 - ‖conformalPart A‖ := by linarith
  rw [this]; ring

/-- `det A = |a₊|² − |a₋|²` (TeX line 268). -/
private theorem thm1_det_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.det = ‖conformalPart A‖ ^ 2 - ‖anticonformalPart A‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    Matrix.det_fin_two]
  simp only [conformalPart, anticonformalPart]
  ring

private theorem thm1_continuous_euclidNorm : Continuous euclidNorm := by
  have : euclidNorm = fun a : Fin 2 → ℝ => √(a 0 ^ 2 + a 1 ^ 2) := funext euclidNorm_eq
  rw [this]; fun_prop

private theorem thm1_abs_le_euclidNorm (a : Fin 2 → ℝ) (i : Fin 2) : |a i| ≤ euclidNorm a := by
  rw [euclidNorm_eq]
  apply Real.abs_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]

/-- `|A¹| ≤ |a₊| + |a₋|`: `A¹ = (Re (a₊ + ā₋), −Im (a₊ + ā₋))`. -/
private theorem thm1_euclidNorm_row_le (A : Matrix (Fin 2) (Fin 2) ℝ) :
    euclidNorm (A 0) ≤ ‖conformalPart A‖ + ‖anticonformalPart A‖ := by
  have hw : (⟨A 0 0, -A 0 1⟩ : ℂ) = conformalPart A + (starRingEnd ℂ) (anticonformalPart A) := by
    apply Complex.ext <;> simp [conformalPart, anticonformalPart] <;> ring
  have hn : euclidNorm (A 0) = ‖(⟨A 0 0, -A 0 1⟩ : ℂ)‖ := by
    rw [euclidNorm_eq, Complex.norm_def, Complex.normSq_mk]
    congr 1; ring
  rw [hn, hw]
  exact (norm_add_le _ _).trans (by rw [Complex.norm_conj])

/-- The closed unit disk is compact. -/
private theorem thm1_disk_isCompact : IsCompact {z : Fin 2 → ℝ | euclidNorm z ≤ 1} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le thm1_continuous_euclidNorm continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := 1)).subset fun z hz => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  exact (thm1_abs_le_euclidNorm z i).trans hz

/-- The closed unit disk is convex. -/
private theorem thm1_disk_convex : Convex ℝ {z : Fin 2 → ℝ | euclidNorm z ≤ 1} := by
  intro x hx y hy a b ha hb hab
  change euclidNorm (a • x + b • y) ≤ 1
  change euclidNorm x ≤ 1 at hx
  change euclidNorm y ≤ 1 at hy
  simp only [euclidNorm] at hx hy ⊢
  rw [WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_smul]
  calc ‖a • WithLp.toLp 2 x + b • WithLp.toLp 2 y‖
      ≤ ‖a • WithLp.toLp 2 x‖ + ‖b • WithLp.toLp 2 y‖ := norm_add_le _ _
    _ = a * ‖WithLp.toLp 2 x‖ + b * ‖WithLp.toLp 2 y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hab]

/-- A point of the boundary of the closed unit disk is on the unit circle. -/
private theorem thm1_mem_unitCircle_of_mem_frontier {z : Fin 2 → ℝ}
    (hz : z ∈ frontier {z : Fin 2 → ℝ | euclidNorm z ≤ 1}) : z ∈ unitCircle := by
  have hcl : IsClosed {z : Fin 2 → ℝ | euclidNorm z ≤ 1} :=
    isClosed_le thm1_continuous_euclidNorm continuous_const
  have h1 : euclidNorm z ≤ 1 := by
    have := frontier_subset_closure hz
    rwa [hcl.closure_eq] at this
  have hsub : {w : Fin 2 → ℝ | euclidNorm w < 1} ⊆ {w | euclidNorm w ≤ 1} := fun w hw =>
    show euclidNorm w ≤ 1 from le_of_lt hw
  refine le_antisymm h1 (not_lt.1 fun h2 => hz.2 ?_)
  exact interior_maximal hsub (isOpen_lt thm1_continuous_euclidNorm continuous_const) h2

/-- `z ↦ G_z (a, b)` is bounded above on `𝕊¹`: `|z_i| ≤ 1` there. -/
private theorem thm1_bddAbove_rowG_unitCircle (a b : Fin 2 → ℝ) :
    BddAbove ((fun z => rowG z a b) '' unitCircle) := by
  refine ⟨|a 0| + |a 1| + |b 0| + |b 1|, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h0 : |z 0| ≤ 1 := (thm1_abs_le_euclidNorm z 0).trans hz.le
  have h1 : |z 1| ≤ 1 := (thm1_abs_le_euclidNorm z 1).trans hz.le
  have k : ∀ s t : ℝ, |s| ≤ 1 → s * t ≤ |t| := fun s t hs =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs)
  have := k (z 0) (b 1) h0
  have := k (-z 1) (b 0) (by rwa [abs_neg])
  have := k (z 0) (a 0) h0
  have := k (z 1) (a 1) h1
  simp only [rowG, det2, dotProduct, Fin.sum_univ_two, Pi.sub_apply]
  nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]

/-- `G_z (A¹, A²) ≤ F (A)` for `|z| = 1`. -/
private theorem thm1_rowG_le_rowF {z : Fin 2 → ℝ} (hz : z ∈ unitCircle)
    (B : Matrix (Fin 2) (Fin 2) ℝ) : rowG z (B 0) (B 1) ≤ rowF B :=
  le_csSup (thm1_bddAbove_rowG_unitCircle _ _) ⟨z, hz, rfl⟩

/-- `D (p · x + ζ) = p + Dζ` where `ζ` is differentiable. -/
private theorem thm1_sgrad_dotProduct_add (p : Fin 2 → ℝ) {ζ : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ}
    (hζ : DifferentiableAt ℝ ζ x) : sgrad (fun y => p ⬝ᵥ y + ζ y) x = p + sgrad ζ x := by
  let ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun y => p ⬝ᵥ y
      map_add' := dotProduct_add p
      map_smul' := fun c y => dotProduct_smul c p y }
  have h : HasFDerivAt (fun y => p ⬝ᵥ y + ζ y) (ℓ + fderiv ℝ ζ x) x :=
    ℓ.hasFDerivAt.add hζ.hasFDerivAt
  funext j
  change fderiv ℝ (fun y => p ⬝ᵥ y + ζ y) x (Pi.single j 1) = p j + fderiv ℝ ζ x (Pi.single j 1)
  rw [h.fderiv]
  change ℓ (Pi.single j 1) + fderiv ℝ ζ x (Pi.single j 1) = _
  congr 1
  change p ⬝ᵥ Pi.single j 1 = p j
  rw [dotProduct_single, mul_one]

/-- `y ↦ (f y, g y)` is Lipschitz if `f`, `g` are. -/
private theorem thm1_lipschitzWith_vec2 {f g : (Fin 2 → ℝ) → ℝ} {K₁ K₂ : NNReal}
    (hf : LipschitzWith K₁ f) (hg : LipschitzWith K₂ g) :
    LipschitzWith (max K₁ K₂) fun y => ![f y, g y] := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_pi_le_iff (by positivity)]
  intro i
  fin_cases i
  · exact (hf.dist_le_mul x y).trans (by gcongr; exact_mod_cast le_max_left K₁ K₂)
  · exact (hg.dist_le_mul x y).trans (by gcongr; exact_mod_cast le_max_right K₁ K₂)

/-- `|Q| = 1`. -/
private theorem thm1_volume_unitSquare : volume unitSquare = 1 :=
  CalculusOfVariations.rd_volume_unitCube 2

/-- Integrability on `Q` of `f (B + ∇ψ)` for a continuous `f` and a Lipschitz `ψ`. -/
private theorem thm1_integrableOn {d : ℕ} {f : Matrix (Fin d) (Fin 2) ℝ → ℝ} (hf : Continuous f)
    (B : Matrix (Fin d) (Fin 2) ℝ) {ψ : (Fin 2 → ℝ) → Fin d → ℝ} {K : NNReal}
    (hψ : LipschitzWith K ψ) :
    IntegrableOn (fun x => f (B + CalculusOfVariations.grad ψ x)) unitSquare :=
  CalculusOfVariations.rd_integrableOn hf.measurable
    (CalculusOfVariations.isLocallyBounded_of_continuous hf) B hψ
    (by rw [thm1_volume_unitSquare]; exact ENNReal.one_lt_top)

/-- `∫_Q G_z (A¹ + Dφ¹, A² + Dφ²) = G_z (A¹, A²)`: `G_z` is affine and `∫_Q Dφ = 0`. -/
private theorem thm1_integral_rowG (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {C : NNReal} (hφ : LipschitzWith C φ) (hper : IsPeriodic φ) (z : Fin 2 → ℝ) :
    ∫ x in unitSquare, rowG z ((A + jacobian φ x) 0) ((A + jacobian φ x) 1) =
      rowG z (A 0) (A 1) := by
  have hI : ∀ i j, Integrable (fun x => jacobian φ x i j) (volume.restrict unitSquare) :=
    fun i j => by
      have := thm1_integrableOn (f := fun B => B i j) (continuous_id.matrix_elem i j) 0 hφ
      simp only [zero_add] at this
      exact this
  have h0 : ∀ i j, ∫ x in unitSquare, jacobian φ x i j = 0 := fun i j =>
    setIntegral_unitCube_grad_eq_zero hφ hper i j
  have : IsFiniteMeasure (volume.restrict unitSquare) :=
    ⟨by rw [Measure.restrict_apply_univ, thm1_volume_unitSquare]; exact ENNReal.one_lt_top⟩
  set c : Fin 2 → Fin 2 → ℝ := ![![z 0, z 1], ![-z 1, z 0]]
  have hpt : ∀ x, rowG z ((A + jacobian φ x) 0) ((A + jacobian φ x) 1) =
      rowG z (A 0) (A 1) + ∑ i, ∑ j, c i j * jacobian φ x i j := fun x => by
    simp only [c, rowG, det2, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Matrix.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hinner : ∀ i, ∫ x in unitSquare, ∑ j, c i j * jacobian φ x i j = 0 := fun i => by
    rw [integral_finsetSum _ fun j _ => (hI i j).const_mul _]
    simp [integral_const_mul, h0]
  calc ∫ x in unitSquare, rowG z ((A + jacobian φ x) 0) ((A + jacobian φ x) 1)
      = ∫ x in unitSquare, (rowG z (A 0) (A 1) + ∑ i, ∑ j, c i j * jacobian φ x i j) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ _ in unitSquare, rowG z (A 0) (A 1)) +
          ∫ x in unitSquare, ∑ i, ∑ j, c i j * jacobian φ x i j :=
        integral_add (integrable_const _)
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
            (hI i j).const_mul _)
    _ = rowG z (A 0) (A 1) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hI i j).const_mul _, Finset.sum_eq_zero fun i _ => hinner i, setIntegral_const,
          measureReal_def, thm1_volume_unitSquare, ENNReal.toReal_one, one_smul, add_zero]

/-- **Theorem 1** (`thm:L-quasiconvexity`) for Lipschitz periodic test maps
(`φ ∈ W^{1,∞}_per (Q; ℝ²)`), by the paper's proof: for all `A ∈ ℝ^{2×2}`,
`∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`.

The proof of the paper (TeX lines 376–396), with `u = A x + φ`, `Du = A + Dφ` (`|Q| = 1`, so the
claim is `∫_Q L (Du) ≥ L (A)`):

* if `|A| > 1`: `L ≥ F` everywhere, and `F = sup_{|z| = 1} G_z` with each `G_z` affine, so that
  `∫_Q G_z (Du) = G_z (A)` (`∫_Q Dφ = 0`, `setIntegral_unitCube_grad_eq_zero`); this is the
  convexity step `∫_Q F (Du) ≥ F (A)`, and `F (A) = L (A)`;
* if `|A| ≤ 1`, then `|A¹| ≤ 1`: Lemma 4 (`lemma4_exists`, `lemma4`) with `K` the closed unit disk,
  `p = A¹` and `η = φ¹` gives `w = A¹ · x + ζ` with `|Dw| ≤ 1` and `Dw = Du¹` or `|Dw| = 1` almost
  everywhere, so `Dw ∈ 𝒵 (Du¹)`, and Lemma 3 (`lemma3`) gives
  `L (Du) ≥ det (Dw, Du²) + Dw · (Du¹ − Dw)` almost everywhere. The determinant is a null Lagrangian
  (`setIntegral_unitCube_det_add_grad` for the periodic map `(ζ, φ²)`): `∫_Q det (Dw, Du²) = det A`;
  and `∫_Q Dw · (Du¹ − Dw) ≥ 0` (`(eq:projection-integral-sign)`). So `∫_Q L (Du) ≥ det A = L (A)`.

Here `Dw = A¹ + Dζ` and `Du¹ = A¹ + Dφ¹` hold where `ζ` and `φ¹` are differentiable, almost
everywhere (Rademacher). -/
theorem theorem1_lipschitz (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {C : NNReal} (hφ : LipschitzWith C φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (integrandL (A + jacobian φ x) - integrandL A) := by
  have hIL : IntegrableOn (fun x => integrandL (A + jacobian φ x)) unitSquare :=
    thm1_integrableOn thm1_continuous_integrandL A hφ
  have hQ : volume unitSquare ≠ ⊤ := by rw [thm1_volume_unitSquare]; exact ENNReal.one_ne_top
  rw [integral_sub hIL (integrableOn_const hQ), setIntegral_const, measureReal_def,
    thm1_volume_unitSquare, ENNReal.toReal_one, one_smul, sub_nonneg]
  -- `u = A x + φ`, `Du = A + Dφ`
  by_cases hA : ‖conformalPart A‖ + ‖anticonformalPart A‖ ≤ 1
  · -- `|A| ≤ 1`, so `|A¹| ≤ 1`: `L (A) = det A`
    have hLA : integrandL A = A.det := by rw [integrandL, ite_eq_left hA, thm1_det_eq]
    rw [hLA]
    set K : Set (Fin 2 → ℝ) := {z | euclidNorm z ≤ 1}
    have hp : A 0 ∈ K := (thm1_euclidNorm_row_le A).trans hA
    have hφi : ∀ i, LipschitzWith C fun y => φ y i := fun i => by
      have := (LipschitzWith.eval (α := fun _ : Fin 2 => ℝ) i).comp hφ
      rwa [one_mul] at this
    -- Lemma 4 with `K` the closed unit disk, `p = A¹`, `η = φ¹`
    set η : (Fin 2 → ℝ) → ℝ := fun y => φ y 0 with hηdef
    have hη : LipPer η := ⟨⟨C, hφi 0⟩, fun x k => by simp only [hηdef]; rw [hper x k]⟩
    obtain ⟨ζ, hζ⟩ := lemma4_exists ⟨A 0, hp⟩ thm1_disk_isCompact thm1_disk_convex hp hη
    obtain ⟨hae, hsign⟩ := lemma4 ⟨A 0, hp⟩ thm1_disk_isCompact thm1_disk_convex hp hη hζ
    obtain ⟨⟨⟨Cζ, hζL⟩, hζper⟩, hζK⟩ := hζ.1
    -- `w = A¹ · x + ζ`: `Dw = A¹ + Dζ` and `Du¹ = A¹ + Dφ¹` almost everywhere
    have hdζ : ∀ᵐ x ∂(volume.restrict unitSquare), DifferentiableAt ℝ ζ x :=
      ae_restrict_of_ae hζL.ae_differentiableAt
    have hdη : ∀ᵐ x ∂(volume.restrict unitSquare), DifferentiableAt ℝ η x :=
      ae_restrict_of_ae (hφi 0).ae_differentiableAt
    have hrow0 : ∀ x, (A + jacobian φ x) 0 = A 0 + sgrad η x := fun x => rfl
    -- `Dw ∈ 𝒵 (Du¹)`, so Lemma 3 gives `L (Du) ≥ det (Dw, Du²) + Dw · (Du¹ − Dw)`
    have hpt : ∀ᵐ x ∂(volume.restrict unitSquare),
        rowG (A 0 + sgrad ζ x) ((A + jacobian φ x) 0) ((A + jacobian φ x) 1) ≤
          integrandL (A + jacobian φ x) := by
      filter_upwards [hae, hdζ, hdη, hζK] with x hx hxζ hxη hxK
      rw [thm1_sgrad_dotProduct_add _ hxζ, thm1_sgrad_dotProduct_add _ hxη] at hx
      apply rowG_le_integrandL
      rcases hx with h | h
      · -- `Dw = Du¹`, and `|Dw| ≤ 1`
        rw [hrow0, ← h, rowZ, ite_eq_left (show euclidNorm (A 0 + sgrad ζ x) ≤ 1 from hxK)]
        exact Set.mem_union_right _ (Set.mem_singleton _)
      · -- `Dw ∈ ∂K`, so `|Dw| = 1`
        exact Set.mem_union_left _ (thm1_mem_unitCircle_of_mem_frontier h)
    -- the determinant is a null Lagrangian: `∫_Q det (Dw, Du²) = det A`, with `ψ = (ζ, φ²)`
    set ψ : (Fin 2 → ℝ) → Fin 2 → ℝ := fun y => ![ζ y, φ y 1] with hψdef
    have hψL : LipschitzWith (max Cζ C) ψ := thm1_lipschitzWith_vec2 hζL (hφi 1)
    have hψper : ∀ (x : Fin 2 → ℝ) (k : Fin 2 → ℤ), ψ (x + fun i => (k i : ℝ)) = ψ x :=
      fun x k => by simp only [hψdef]; rw [hζper x k, hper x k]
    have hψrow : ∀ x, (A + CalculusOfVariations.grad ψ x).det =
        det2 (A 0 + sgrad ζ x) ((A + jacobian φ x) 1) := fun x => by
      rw [det_eq_det2]
      rfl
    have hdet : ∫ x in unitSquare, det2 (A 0 + sgrad ζ x) ((A + jacobian φ x) 1) = A.det :=
      calc ∫ x in unitSquare, det2 (A 0 + sgrad ζ x) ((A + jacobian φ x) 1)
          = ∫ x in CalculusOfVariations.unitCube 2, (A + CalculusOfVariations.grad ψ x).det :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => (hψrow x).symm)
        _ = A.det := setIntegral_unitCube_det_add_grad hψL hψper A
    have hI1 : Integrable (fun x => det2 (A 0 + sgrad ζ x) ((A + jacobian φ x) 1))
        (volume.restrict unitSquare) :=
      (thm1_integrableOn (f := Matrix.det) (continuous_id.matrix_det) A hψL).congr
        (Filter.Eventually.of_forall hψrow)
    -- `Dw · (Du¹ − Dw)` is a continuous function of `A' + Dψ'`, `ψ' = (ζ, φ¹)`, `A' = (A¹, A¹)`
    set ψ' : (Fin 2 → ℝ) → Fin 2 → ℝ := fun y => ![ζ y, φ y 0] with hψ'def
    set A' : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![A 0, A 0] with hA'def
    have hψ'row : ∀ x, (A' + CalculusOfVariations.grad ψ' x) 0 ⬝ᵥ
        ((A' + CalculusOfVariations.grad ψ' x) 1 - (A' + CalculusOfVariations.grad ψ' x) 0) =
          (A 0 + sgrad ζ x) ⬝ᵥ ((A + jacobian φ x) 0 - (A 0 + sgrad ζ x)) := fun x => by
      have r0 : (A' + CalculusOfVariations.grad ψ' x) 0 = A 0 + sgrad ζ x := by
        ext j; simp [hψ'def, hA'def, CalculusOfVariations.grad, sgrad]
      have r1 : (A' + CalculusOfVariations.grad ψ' x) 1 = (A + jacobian φ x) 0 := by
        ext j; simp [hψ'def, hA'def, CalculusOfVariations.grad, jacobian]
      rw [r0, r1]
    have hI2 : Integrable (fun x => (A 0 + sgrad ζ x) ⬝ᵥ ((A + jacobian φ x) 0 - (A 0 + sgrad ζ x)))
        (volume.restrict unitSquare) := by
      have hc : Continuous fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 ⬝ᵥ (B 1 - B 0) := by
        have := thm1_continuous_entry
        simp only [dotProduct, Fin.sum_univ_two, Pi.sub_apply]
        fun_prop
      exact (thm1_integrableOn hc A' (thm1_lipschitzWith_vec2 hζL (hφi 0))).congr
        (Filter.Eventually.of_forall hψ'row)
    -- Lemma 4: `∫_Q Dw · (Du¹ − Dw) ≥ 0`
    have hsign' : 0 ≤ ∫ x in unitSquare,
        (A 0 + sgrad ζ x) ⬝ᵥ ((A + jacobian φ x) 0 - (A 0 + sgrad ζ x)) := by
      refine hsign.trans_eq (integral_congr_ae ?_)
      filter_upwards [hdζ, hdη] with x hxζ hxη
      rw [thm1_sgrad_dotProduct_add _ hxζ, thm1_sgrad_dotProduct_add _ hxη]
      rfl
    calc A.det = A.det + 0 := (add_zero _).symm
      _ ≤ (∫ x in unitSquare, det2 (A 0 + sgrad ζ x) ((A + jacobian φ x) 1)) +
            ∫ x in unitSquare, (A 0 + sgrad ζ x) ⬝ᵥ ((A + jacobian φ x) 0 - (A 0 + sgrad ζ x)) := by
          rw [hdet]; exact add_le_add le_rfl hsign'
      _ = ∫ x in unitSquare,
            rowG (A 0 + sgrad ζ x) ((A + jacobian φ x) 0) ((A + jacobian φ x) 1) :=
          (integral_add hI1 hI2).symm
      _ ≤ ∫ x in unitSquare, integrandL (A + jacobian φ x) :=
          integral_mono_ae (hI1.add hI2) hIL hpt
  · -- `|A| > 1`: `L ≥ F` and `F` is convex: `∫_Q L (Du) ≥ ∫_Q F (Du) ≥ F (A) = L (A)`
    have hLA : integrandL A = rowF A := by rw [integrandL, ite_eq_right hA, rowF_eq]
    have hIF : IntegrableOn (fun x => rowF (A + jacobian φ x)) unitSquare := by
      have hc : Continuous rowF := by
        rw [show rowF = fun B => 2 * ‖conformalPart B‖ - 1 from funext rowF_eq]
        have := thm1_continuous_conformalPart
        fun_prop
      exact thm1_integrableOn hc A hφ
    rw [hLA]
    calc rowF A ≤ ∫ x in unitSquare, rowF (A + jacobian φ x) := by
          -- `F = sup_{|z| = 1} G_z`, the `G_z` affine: `G_z (A) = ∫_Q G_z (Du) ≤ ∫_Q F (Du)`
          refine csSup_le ⟨_, ![1, 0], by simp [unitCircle, euclidNorm_eq], rfl⟩ ?_
          rintro _ ⟨z, hz, rfl⟩
          calc rowG z (A 0) (A 1)
              = ∫ x in unitSquare, rowG z ((A + jacobian φ x) 0) ((A + jacobian φ x) 1) :=
                (thm1_integral_rowG A hφ hper z).symm
            _ ≤ ∫ x in unitSquare, rowF (A + jacobian φ x) := by
                refine integral_mono ?_ hIF fun x => thm1_rowG_le_rowF hz _
                have hc : Continuous fun B : Matrix (Fin 2) (Fin 2) ℝ => rowG z (B 0) (B 1) := by
                  have := thm1_continuous_entry
                  simp only [rowG, det2, dotProduct, Fin.sum_univ_two, Pi.sub_apply]
                  fun_prop
                exact thm1_integrableOn hc A hφ
      _ ≤ ∫ x in unitSquare, integrandL (A + jacobian φ x) :=
          integral_mono hIF hIL fun x => rowF_le_integrandL _

/-- A `C^∞` `ℤ²`-periodic map `ℝ² → ℝ²` is Lipschitz: its derivative is continuous and periodic,
hence bounded (by its bound on the compact `[0, 1]²`), and `ℝ²` is convex. -/
theorem exists_lipschitzWith_of_contDiff_of_isPeriodic {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) : ∃ C : NNReal, LipschitzWith C φ := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  -- the derivative is periodic
  have hpf : ∀ (x : Fin 2 → ℝ) (k : Fin 2 → ℤ),
      fderiv ℝ φ (x + fun i => (k i : ℝ)) = fderiv ℝ φ x := by
    intro x k
    rw [← fderiv_comp_add_right]
    congr 1
    funext y
    exact hper y k
  -- and bounded on the compact `[0, 1]²`, hence everywhere
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun _ =>
    isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M.toNNReal, lipschitzWith_of_nnNorm_fderiv_le hd fun x => ?_⟩
  have hx : (x + fun i => ((-⌊x i⌋ : ℤ) : ℝ)) ∈ Set.pi Set.univ fun _ => Set.Icc (0:ℝ) 1 := by
    intro i _
    simp only [Pi.add_apply, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  rw [← hpf x (fun i => -⌊x i⌋), ← NNReal.coe_le_coe, coe_nnNorm]
  exact (hM _ hx).trans (Real.le_coe_toNNReal M)

/-- **Theorem 1** (`thm:L-quasiconvexity`). Let `Q = ℝ² / ℤ²`, with `|Q| = 1`. For all
`A ∈ ℝ^{2×2}` and all `φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [L (A + Dφ) − L (A)] dx ≥ 0`. -/
theorem theorem1 (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (integrandL (A + jacobian φ x) - integrandL A) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_contDiff_of_isPeriodic hφ hper
  exact theorem1_lipschitz A hC hper

end Agazzi
