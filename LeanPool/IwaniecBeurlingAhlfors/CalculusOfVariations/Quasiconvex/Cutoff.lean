/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Cutoff

/-!
# Cut-offs near the boundary of the cube

`le_of_quasiconvexAtOn_of_tendsto`: let `f` be Borel and locally bounded, and quasiconvex at `F` on
the unit cube `Q`. If the maps `u_k` are Lipschitz with the same constant, `u_k → 0` uniformly and
`∫_Q f (F + ∇u_k) → E`, then `f (F) ≤ E`, although the `u_k` need not vanish on `∂Q`.

This is the cut-off argument of F. Rindler, *Calculus of Variations*, 2nd ed., Graduate Texts in
Mathematics 310, Springer, 2026 ([R2]), proof of Proposition 5.6, Step 2 (p. 112–113), and of
B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Springer, 2008, proof of
Proposition 5.13 (p. 173–174). In [R2]: take cut-off functions `ρ_j` with `0 ≤ ρ_j ≤ 1`, `ρ_j = 0`
off `Q` and `|Q ∖ G_j| → 0` for `G_j = {ρ_j = 1}`, and `v_{j,k} = ρ_j u_k`, so that
`∇v_{j,k} = ρ_j ∇u_k + u_k ⊗ ∇ρ_j` ([R2] writes `F x + u_k` for `u_k` and `F x + v_{j,k}` for
`v_{j,k}`). Since `u_k → 0` uniformly, one can choose, for every `j`, an index `k (j)` such that the
gradients `∇v_j`, `v_j = v_{j,k (j)}`, are bounded independently of `j`. As `f` is locally bounded,
`∫_Q |f (F + ∇v_j) − f (F + ∇u_{k (j)})| ≤ C |Q ∖ G_j| → 0`, and
`f (F) ≤ ∫_Q f (F + ∇v_j)` by quasiconvexity.

Here `ρ_j = cubeCutoff (1/j)` (Lipschitz cut-offs, equal to `1` on `[1/j, 1 − 1/j]^m`, with
`|∇ρ_j| ≤ m j`), and `k (j)` is chosen with `|u_{k (j)}| ≤ 1/j`, so that `v_j` is Lipschitz with a
constant independent of `j`, and with `k (j) ≥ j`, so that `∫_Q f (F + ∇u_{k (j)}) → E` (for the
laminates of [R2] this integral does not depend on `k`, so `k (j) → ∞` is not needed there).
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-- The cut-off `ρ u` of a `K`-Lipschitz map `u` with `|u| ≤ M δ`, `ρ = cubeCutoff δ`, is
`(K + m M)`-Lipschitz: `|∇ρ| ≤ m / δ`. -/
lemma rd_eta_smul_lipschitz {u : (Fin m → ℝ) → Fin d → ℝ} {K M : NNReal} (hu : LipschitzWith K u)
    {δ : ℝ} (hδ : 0 < δ) (hb : ∀ x, ‖u x‖ ≤ M * δ) :
    LipschitzWith (K + m * M) fun x => cubeCutoff δ x • u x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm]
  have e : cubeCutoff δ x • u x - cubeCutoff δ y • u y =
      cubeCutoff δ x • (u x - u y) + (cubeCutoff δ x - cubeCutoff δ y) • u y := by
    rw [smul_sub, sub_smul]; abel
  have h1 := hu.dist_le_mul x y
  rw [dist_eq_norm] at h1
  have h2 := rd_eta_lip hδ x y
  have h3 := rd_eta_mem δ x
  rw [e]
  calc ‖cubeCutoff δ x • (u x - u y) + (cubeCutoff δ x - cubeCutoff δ y) • u y‖
      ≤ |cubeCutoff δ x| * ‖u x - u y‖ + |cubeCutoff δ x - cubeCutoff δ y| * ‖u y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 1 * (K * dist x y) + m * dist x y / δ * (M * δ) := by
        gcongr
        · rw [abs_of_nonneg h3.1]; exact h3.2
        · exact hb y
    _ = (K + m * M : NNReal) * dist x y := by
        push_cast
        field_simp

/-- The inner cube `(δ, 1 − δ)^m` lies in the unit cube. -/
lemma rd_inner_subset {δ : ℝ} (hδ : 0 ≤ δ) : innerCube (m := m) δ ⊆ unitCube m := fun x hx i _ =>
  ⟨by linarith [(hx i (mem_univ i)).1], by linarith [(hx i (mem_univ i)).2]⟩

lemma rd_inner_measurableSet (δ : ℝ) : MeasurableSet (innerCube (m := m) δ) :=
  (rd_inner_isOpen δ).measurableSet

/-- The boundary layer `Q ∖ (δ, 1 − δ)^m` of the unit cube has measure `1 − (1 − 2δ)^m`. -/
lemma rd_volume_real_layer {δ : ℝ} (hδ : 0 ≤ δ) (hδ2 : 2 * δ ≤ 1) :
    volume.real (unitCube m \ innerCube δ) = 1 - (1 - 2 * δ) ^ m := by
  have hQ : volume.real (unitCube m) = 1 := by
    rw [measureReal_def, rd_volume_unitCube, ENNReal.toReal_one]
  rw [measureReal_sdiff (rd_inner_subset hδ) (rd_inner_measurableSet δ)
    (by rw [rd_volume_unitCube]; exact ENNReal.one_ne_top), hQ, measureReal_def]
  simp only [innerCube, Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- **Cut-off near the boundary** ([R2], proof of Proposition 5.6, Step 2; see the module docstring
for the proof). Let `f` be Borel, locally bounded and quasiconvex at `F` on the unit cube `Q`. If
the `u_k` are `K`-Lipschitz, `u_k → 0` uniformly and `∫_Q f (F + ∇u_k) → E`, then `f (F) ≤ E`. -/
theorem le_of_quasiconvexAtOn_of_tendsto {f : Matrix (Fin d) (Fin m) ℝ → ℝ}
    (hf : Measurable f) (hbdd : IsLocallyBounded f) {F : Matrix (Fin d) (Fin m) ℝ}
    (hq : QuasiconvexAtOn (unitCube m) f F) {u : ℕ → (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hu : ∀ k, LipschitzWith K (u k)) (hu0 : TendstoUniformly u 0 atTop) {E : ℝ}
    (hE : Tendsto (fun k => ∫ x in unitCube m, f (F + grad (u k) x)) atTop (𝓝 E)) : f F ≤ E := by
  have hQm : MeasurableSet (unitCube m) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQfin : volume (unitCube m) < ⊤ := by rw [rd_volume_unitCube]; exact ENNReal.one_lt_top
  -- the bound of `f` on the gradients
  obtain ⟨C, hC0, hC⟩ := rd_bound_near hbdd F (K + m)
  -- the choice of `k (j)`
  have hk : ∀ j : ℕ, ∃ k, j ≤ k ∧ (0 < j → ∀ x, ‖u k x‖ ≤ 1 / (j : ℝ)) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨0, le_rfl, fun h => absurd h (lt_irrefl _)⟩
    · have hj' : (0 : ℝ) < 1 / j := one_div_pos.2 (Nat.cast_pos.2 hj)
      obtain ⟨k, hk⟩ := ((Metric.tendstoUniformly_iff.1 hu0 _ hj').and
        (eventually_ge_atTop j)).exists
      exact ⟨k, hk.2, fun _ x => by simpa using (hk.1 x).le⟩
  choose k hkj hkb using hk
  -- the energies of `v_j = ρ_j u_{k (j)}` and of `u_{k (j)}`
  have key : ∀ j : ℕ, 2 ≤ j → f F ≤ (∫ x in unitCube m, f (F + grad (u (k j)) x)) +
      2 * C * (1 - (1 - 2 * (1 / (j : ℝ))) ^ m) := by
    intro j hj
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    set δ : ℝ := 1 / j with hδdef
    have hδ : 0 < δ := by positivity
    have hδ2 : 2 * δ ≤ 1 := by rw [hδdef, mul_one_div, div_le_one (by linarith)]; exact hj'
    set v : (Fin m → ℝ) → Fin d → ℝ := fun x => cubeCutoff δ x • u (k j) x with hvdef
    have hv : LipschitzWith (K + m * 1) v := rd_eta_smul_lipschitz (hu _) hδ
      fun x => by rw [NNReal.coe_one, one_mul]; exact hkb j (by omega) x
    have hv0 : ∀ x ∉ unitCube m, v x = 0 := fun x hx => by
      simp only [hvdef, rd_eta_zero hδ hx, zero_smul]
    have hq' := hq v _ hv hv0 (rd_integrableOn hf hbdd F hv hQfin)
    rw [rd_volume_unitCube, ENNReal.toReal_one, one_mul] at hq'
    -- the two integrands agree on `G_j`
    have hagree : ∀ x ∈ innerCube δ, grad v x = grad (u (k j)) x := fun x hx => by
      refine cv_grad_congr ?_
      filter_upwards [(rd_inner_isOpen δ).mem_nhds hx] with y hy
      simp only [hvdef, rd_eta_one hδ hy, one_smul]
    have hb1 : ∀ x, ‖f (F + grad v x)‖ ≤ C := fun x => by
      rw [Real.norm_eq_abs]
      exact hC _ fun i l => by simpa using rd_grad_abs_le hv x i l
    have hb2 : ∀ x, ‖f (F + grad (u (k j)) x)‖ ≤ C := fun x => by
      rw [Real.norm_eq_abs]
      refine hC _ fun i l => (rd_grad_abs_le (hu _) x i l).trans ?_
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hint1 := rd_integrableOn hf hbdd F hv hQfin
    have hint2 := rd_integrableOn hf hbdd F (hu (k j)) hQfin
    have hsub := rd_inner_subset (m := m) hδ.le
    have hdiff : ∫ x in unitCube m, (f (F + grad v x) - f (F + grad (u (k j)) x)) =
        ∫ x in unitCube m \ innerCube δ, (f (F + grad v x) - f (F + grad (u (k j)) x)) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQm sdiff_subset fun x hx => ?_
      have hx' : x ∈ innerCube δ := by_contra fun h => hx.2 ⟨hx.1, h⟩
      rw [hagree x hx', sub_self]
    have hbd := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := unitCube m \ innerCube (m := m) δ) ((measure_mono sdiff_subset).trans_lt hQfin)
      (f := fun x => f (F + grad v x) - f (F + grad (u (k j)) x)) (C := 2 * C)
      fun x _ => (norm_sub_le _ _).trans (by linarith [hb1 x, hb2 x])
    rw [← hdiff, integral_sub hint1 hint2, Real.norm_eq_abs, rd_volume_real_layer hδ.le hδ2] at hbd
    linarith [(abs_le.1 hbd).2]
  -- the limit `j → ∞`
  have h1 : Tendsto (fun j : ℕ => ∫ x in unitCube m, f (F + grad (u (k j)) x)) atTop (𝓝 E) :=
    hE.comp (tendsto_atTop_mono hkj tendsto_id)
  have h2 : Tendsto (fun j : ℕ => 2 * C * (1 - (1 - 2 * (1 / (j : ℝ))) ^ m)) atTop
      (𝓝 (2 * C * (1 - (1 - 2 * 0) ^ m))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub
      ((tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat)).pow m))
  have h3 := h1.add h2
  simp only [mul_zero, sub_zero, one_pow, sub_self, add_zero] at h3
  exact ge_of_tendsto h3 ((eventually_ge_atTop 2).mono key)

end CalculusOfVariations
