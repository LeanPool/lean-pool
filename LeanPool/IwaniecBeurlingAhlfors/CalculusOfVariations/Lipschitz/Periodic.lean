/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Lipschitz.Gradient

/-!
# Periodic extension and periodic averages

* `periodicExtension φ = φ ∘ fract` extends maps on the unit cube. If `φ` is `K`-Lipschitz and
  vanishes off the open cube, the extension is `m K`-Lipschitz and `ℤ^m`-periodic. It has the
  same gradient on the open cube.
* the periodic average identity `∫_{(0,1)^m} G (N x) dx = ∫_{(0,1)^m} G` for bounded measurable
  `ℤ^m`-periodic `G` and integers `N ≥ 1`;
* a Lipschitz periodic map is bounded, and its gradient is periodic.
-/

@[expose] public section

open Metric Set MeasureTheory Filter Topology
open scoped Pointwise

namespace CalculusOfVariations

variable {d m : ℕ}

/-! ### Periodic extension of a test map -/

/-- The periodic extension `x ↦ φ (fract x)` of a map on the unit cube. -/
noncomputable def periodicExtension (φ : (Fin m → ℝ) → Fin d → ℝ) : (Fin m → ℝ) → Fin d → ℝ :=
  fun x => φ (fun i => Int.fract (x i))

/-- On a closed integer cell `z + [0, 1]^m`, the periodic extension of a map vanishing off the open
cube is its translate. -/
private lemma rd_perExt_cell {φ : (Fin m → ℝ) → Fin d → ℝ} (h0 : ∀ x ∉ unitCube m, φ x = 0)
    (z : Fin m → ℤ) {x : Fin m → ℝ} (hx : ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) :
    periodicExtension φ x = φ (x - fun i => (z i : ℝ)) := by
  by_cases h : ∀ i, (z i : ℝ) < x i ∧ x i < z i + 1
  · have : (fun i => Int.fract (x i)) = x - fun i => (z i : ℝ) := by
      funext i
      rw [← Int.self_sub_floor, Int.floor_eq_iff.2 ⟨(h i).1.le, (h i).2⟩]
      rfl
    simp only [periodicExtension, this]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hint : x i = z i ∨ x i = z i + 1 := by
      rcases eq_or_lt_of_le (hx i).1 with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr (le_antisymm (hx i).2 (hi h1))
    have h1 : (fun i => Int.fract (x i)) ∉ unitCube m := by
      intro hmem
      have := (hmem i (Set.mem_univ _)).1
      dsimp only at this
      rcases hint with h2 | h2
      · rw [h2, Int.fract_intCast] at this; exact lt_irrefl _ this
      · rw [h2, show (z i : ℝ) + 1 = ((z i + 1 : ℤ) : ℝ) by push_cast; ring,
          Int.fract_intCast] at this
        exact lt_irrefl _ this
    have h2 : (x - fun i => (z i : ℝ)) ∉ unitCube m := by
      intro hmem
      have := hmem i (Set.mem_univ _)
      simp only [Pi.sub_apply] at this
      rcases hint with h3 | h3 <;> rw [h3] at this <;> linarith [this.1, this.2]
    simp only [periodicExtension, h0 _ h1, h0 _ h2]

private lemma rd_perExt_eq_zero_of_int {φ : (Fin m → ℝ) → Fin d → ℝ}
    (h0 : ∀ x ∉ unitCube m, φ x = 0) {x : Fin m → ℝ} {c : Fin m} {n : ℤ} (hc : x c = n) :
    periodicExtension φ x = 0 := by
  apply h0
  intro hmem
  have := (hmem c (Set.mem_univ _)).1
  dsimp only at this
  rw [hc, Int.fract_intCast] at this
  exact lt_irrefl _ this

private lemma rd_dist_update (w : Fin m → ℝ) (c : Fin m) (a b : ℝ) :
    dist (Function.update w c a) (Function.update w c b) ≤ |a - b| := by
  rw [dist_pi_le_iff (abs_nonneg _)]
  intro i
  rcases eq_or_ne i c with rfl | hi
  · simp [Real.dist_eq]
  · simp [Function.update_of_ne hi]

/-- The one-dimensional step: along a coordinate line the periodic extension is `K`-Lipschitz
(it is the translate of `φ` on each closed cell, and vanishes at the integer points). -/
private lemma rd_perExt_line {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal} (hφ : LipschitzWith K φ)
    (h0 : ∀ x ∉ unitCube m, φ x = 0) (w : Fin m → ℝ) (c : Fin m) (s s' : ℝ) :
    dist (periodicExtension φ (Function.update w c s))
      (periodicExtension φ (Function.update w c s')) ≤ K * |s - s'| := by
  wlog hss : s ≤ s' generalizing s s'
  · rw [dist_comm, abs_sub_comm]; exact this s' s (le_of_not_ge hss)
  -- the cell of a point of the line
  have hcell : ∀ t : ℝ, ∀ i, ((fun j => ⌊Function.update w c t j⌋) i : ℝ) ≤
      Function.update w c t i ∧ Function.update w c t i ≤
        ((fun j => ⌊Function.update w c t j⌋) i : ℝ) + 1 := fun t i =>
    ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  -- moving coordinate `c` inside the cell of `t`
  have hmove : ∀ t u : ℝ, (⌊t⌋ : ℝ) ≤ u → u ≤ ⌊t⌋ + 1 →
      dist (periodicExtension φ (Function.update w c t))
        (periodicExtension φ (Function.update w c u)) ≤ K * |t - u| := by
    intro t u hu1 hu2
    set z := fun j => ⌊Function.update w c t j⌋
    have hzu : ∀ i, (z i : ℝ) ≤ Function.update w c u i ∧ Function.update w c u i ≤ z i + 1 := by
      intro i
      rcases eq_or_ne i c with rfl | hi
      · simp only [z, Function.update_self]; exact ⟨hu1, hu2⟩
      · simp only [z, Function.update_of_ne hi]
        exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    rw [rd_perExt_cell h0 z (hcell t), rd_perExt_cell h0 z hzu]
    calc dist (φ (Function.update w c t - fun i => (z i : ℝ)))
          (φ (Function.update w c u - fun i => (z i : ℝ)))
        ≤ K * dist (Function.update w c t - fun i => (z i : ℝ))
          (Function.update w c u - fun i => (z i : ℝ)) := hφ.dist_le_mul _ _
      _ = K * dist (Function.update w c t) (Function.update w c u) := by rw [dist_sub_right]
      _ ≤ K * |t - u| := by gcongr; exact rd_dist_update w c t u
  rcases eq_or_lt_of_le (Int.floor_le_floor hss) with heq | hlt
  · -- the same cell
    exact hmove s s' (by rw [heq]; exact Int.floor_le s')
      (by rw [heq]; exact (Int.lt_floor_add_one s').le)
  · -- through the integer points `⌊s⌋ + 1 ≤ ⌊s'⌋`
    have hle : (⌊s⌋ : ℝ) + 1 ≤ ⌊s'⌋ := by exact_mod_cast hlt
    have hp : periodicExtension φ (Function.update w c ((⌊s⌋ : ℝ) + 1)) = 0 :=
      rd_perExt_eq_zero_of_int h0 (c := c) (n := ⌊s⌋ + 1) (by simp)
    have hq : periodicExtension φ (Function.update w c (⌊s'⌋ : ℝ)) = 0 :=
      rd_perExt_eq_zero_of_int h0 (c := c) (n := ⌊s'⌋) (by simp)
    have h1 := hmove s ((⌊s⌋ : ℝ) + 1) (by linarith) le_rfl
    have h2 := hmove s' (⌊s'⌋ : ℝ) le_rfl (by linarith)
    rw [hp] at h1
    rw [hq] at h2
    have e1 : |s - ((⌊s⌋ : ℝ) + 1)| = (⌊s⌋ : ℝ) + 1 - s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [Int.lt_floor_add_one s])]
    have e2 : |s' - (⌊s'⌋ : ℝ)| = s' - ⌊s'⌋ := abs_of_nonneg (by linarith [Int.floor_le s'])
    rw [e1] at h1
    rw [e2] at h2
    calc dist (periodicExtension φ (Function.update w c s))
          (periodicExtension φ (Function.update w c s'))
        ≤ dist (periodicExtension φ (Function.update w c s)) 0 +
          dist 0 (periodicExtension φ (Function.update w c s')) := dist_triangle _ _ _
      _ ≤ K * ((⌊s⌋ : ℝ) + 1 - s) + K * (s' - ⌊s'⌋) := by
          rw [dist_comm 0]; exact add_le_add h1 h2
      _ ≤ K * |s - s'| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          have : (0 : ℝ) ≤ K := K.2
          nlinarith

/-- The periodic extension of a Lipschitz map vanishing off the open cube is Lipschitz (a path
that changes one coordinate at a time). -/
lemma rd_perExt_lipschitz {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (h0 : ∀ x ∉ unitCube m, φ x = 0) :
    LipschitzWith (m * K) (periodicExtension φ) := by
  suffices h : ∀ S : Finset (Fin m), ∀ x y : Fin m → ℝ, (∀ i ∉ S, x i = y i) →
      dist (periodicExtension φ x) (periodicExtension φ y) ≤ S.card * K * dist x y by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have := h Finset.univ x y (by simp)
    simpa [Finset.card_univ] using this
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x y h
    have : x = y := funext fun i => h i (Finset.notMem_empty _)
    simp [this]
  | insert c S hc ih =>
    intro x y hxy
    set w := Function.update x c (y c)
    have hwy : ∀ i ∉ S, w i = y i := by
      intro i hi
      rcases eq_or_ne i c with rfl | hic
      · simp [w]
      · simp only [w, Function.update_of_ne hic]
        exact hxy i (by simp [hic, hi])
    have hdwy : dist w y ≤ dist x y := by
      rw [dist_pi_le_iff dist_nonneg]
      intro i
      rcases eq_or_ne i c with rfl | hic
      · simp [w]
      · simp only [w, Function.update_of_ne hic]; exact dist_le_pi_dist x y i
    have h1 : dist (periodicExtension φ x) (periodicExtension φ w) ≤ K * dist x y := by
      have := rd_perExt_line hφ h0 x c (x c) (y c)
      rw [Function.update_eq_self] at this
      refine this.trans ?_
      gcongr
      rw [← Real.dist_eq]; exact dist_le_pi_dist x y c
    have h2 := ih w y hwy
    rw [Finset.card_insert_of_notMem hc]
    push_cast
    have hK : (0 : ℝ) ≤ K := K.2
    calc dist (periodicExtension φ x) (periodicExtension φ y)
        ≤ dist (periodicExtension φ x) (periodicExtension φ w) +
          dist (periodicExtension φ w) (periodicExtension φ y) :=
          dist_triangle _ _ _
      _ ≤ K * dist x y + S.card * K * dist w y := add_le_add h1 h2
      _ ≤ K * dist x y + S.card * K * dist x y := by gcongr
      _ = (S.card + 1) * K * dist x y := by ring

lemma rd_perExt_periodic (φ : (Fin m → ℝ) → Fin d → ℝ) (x : Fin m → ℝ) (z : Fin m → ℤ) :
    periodicExtension φ (x + fun i => (z i : ℝ)) = periodicExtension φ x := by
  simp only [periodicExtension, Pi.add_apply, Int.fract_add_intCast]

/-- On the open cube, the periodic extension is `φ`, so their gradients agree there. -/
lemma rd_grad_perExt {φ : (Fin m → ℝ) → Fin d → ℝ} {x : Fin m → ℝ} (hx : x ∈ unitCube m) :
    grad (periodicExtension φ) x = grad φ x := by
  have hopen : IsOpen (unitCube m) := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have heq : periodicExtension φ =ᶠ[𝓝 x] φ := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    simp only [periodicExtension]
    congr 1
    funext i
    have := hy i (Set.mem_univ _)
    rw [← Int.self_sub_floor, Int.floor_eq_zero_iff.2 ⟨this.1.le, this.2⟩, Int.cast_zero, sub_zero]
  ext i k
  simp only [grad, Matrix.of_apply]
  have hi : (fun y => periodicExtension φ y i) =ᶠ[𝓝 x] fun y => φ y i :=
    heq.mono fun y hy => by change periodicExtension φ y i = φ y i; rw [hy]
  rw [Filter.EventuallyEq.fderiv_eq hi]

/-! ### The periodic average identity -/

/-- The open unit cube and `[0, 1)^m` differ by a null set. -/
private lemma rd_setIntegral_unitCube_eq_Ico (g : (Fin m → ℝ) → ℝ) :
    ∫ x in unitCube m, g x = ∫ x in Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1), g x := by
  apply setIntegral_congr_set
  have h1 := Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => 1)
  have h2 := Measure.univ_pi_Ico_ae_eq_Icc (μ := fun _ : Fin m => (volume : Measure ℝ))
    (f := fun _ => (0:ℝ)) (g := fun _ => 1)
  exact h1.trans h2.symm

/-- The unit cell `z + [0, 1)^m`. -/
private def rd_cell (z : Fin m → ℝ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun i => Set.Ico (z i) (z i + 1)

private lemma rd_setIntegral_cell {G : (Fin m → ℝ) → ℝ}
    (hper : ∀ x (z : Fin m → ℤ), G (x + fun i => (z i : ℝ)) = G x) (z : Fin m → ℤ) :
    ∫ x in rd_cell (fun i => (z i : ℝ)), G x = ∫ x in rd_cell 0, G x := by
  have h := (measurePreserving_add_right (volume : Measure (Fin m → ℝ))
    (fun i => (z i : ℝ))).setIntegral_preimage_emb (measurableEmbedding_addRight _) G
    (rd_cell (fun i => (z i : ℝ)))
  have hpre : (fun x => x + fun i => (z i : ℝ)) ⁻¹' rd_cell (fun i => (z i : ℝ)) = rd_cell 0 := by
    ext x
    simp only [rd_cell, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico,
      Pi.add_apply, Pi.zero_apply, zero_add]
    refine forall_congr' fun i => ?_
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [← h, hpre]
  exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    fun x _ => hper x z

/-- The periodic average identity for bounded measurable `G`: for a `ℤ^m`-periodic `G` and an
integer `N ≥ 1`, `∫_{(0,1)^m} G (N x) dx = ∫_{(0,1)^m} G`. -/
lemma rd_setIntegral_comp_nsmul {G : (Fin m → ℝ) → ℝ} (hGm : Measurable G) {C : ℝ}
    (hGb : ∀ x, |G x| ≤ C) (hper : ∀ x (z : Fin m → ℤ), G (x + fun i => (z i : ℝ)) = G x)
    {N : ℕ} (hN : 0 < N) :
    ∫ x in unitCube m, G ((N : ℝ) • x) = ∫ x in unitCube m, G x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [rd_setIntegral_unitCube_eq_Ico, rd_setIntegral_unitCube_eq_Ico,
    Measure.setIntegral_comp_smul_of_pos volume G _ hN']
  have hQ : Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1) = rd_cell (0 : Fin m → ℝ) := by
    simp [rd_cell]
  have hcells : (N : ℝ) • Set.pi Set.univ (fun _ => Set.Ico (0:ℝ) 1) =
      ⋃ z : Fin m → Fin N, rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ)) := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hN'.ne', Set.mem_iUnion]
    simp only [rd_cell, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico, Pi.smul_apply,
      smul_eq_mul, Int.cast_natCast]
    constructor
    · intro h
      have h0 : ∀ i, 0 ≤ y i := fun i => by
        have := mul_nonneg hN'.le (h i).1
        rwa [mul_inv_cancel_left₀ hN'.ne'] at this
      have h1 : ∀ i, y i < N := fun i => by
        simpa using (inv_mul_lt_iff₀ hN').1 (h i).2
      refine ⟨fun i => ⟨⌊y i⌋₊, (Nat.floor_lt (h0 i)).2 (h1 i)⟩, fun i => ?_⟩
      exact ⟨Nat.floor_le (h0 i), Nat.lt_floor_add_one (y i)⟩
    · rintro ⟨z, hz⟩ i
      have hzN : ((z i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast (z i).isLt
      have h0 : 0 ≤ y i := le_trans (Nat.cast_nonneg _) (hz i).1
      refine ⟨mul_nonneg (inv_nonneg.2 hN'.le) h0, ?_⟩
      rw [inv_mul_lt_iff₀ hN', mul_one]
      linarith [(hz i).2]
  have hint : ∀ z : Fin m → Fin N, IntegrableOn G (rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) := by
    intro z
    refine IntegrableOn.of_bound ?_ hGm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x)
    simp only [rd_cell, Real.volume_pi_Ico]
    exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
  have hdisj : Pairwise (Function.onFun Disjoint fun z : Fin m → Fin N =>
      rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) := by
    intro z z' hzz'
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hzz'
    refine Set.disjoint_left.2 fun y hy hy' => hi ?_
    have a := hy i (Set.mem_univ _)
    have b := hy' i (Set.mem_univ _)
    simp only [Set.mem_Ico, Int.cast_natCast] at a b
    have c1 : ((z i : ℕ) : ℝ) < (z' i : ℕ) + 1 := by linarith [a.1, b.2]
    have c2 : ((z' i : ℕ) : ℝ) < (z i : ℕ) + 1 := by linarith [a.2, b.1]
    have d1 : (z i : ℕ) < (z' i : ℕ) + 1 := by exact_mod_cast c1
    have d2 : (z' i : ℕ) < (z i : ℕ) + 1 := by exact_mod_cast c2
    exact Fin.ext (by omega)
  have hmeas : ∀ z : Fin m → Fin N, MeasurableSet (rd_cell (fun i => (((z i : ℕ) : ℤ) : ℝ))) :=
    fun z => MeasurableSet.univ_pi fun _ => measurableSet_Ico
  rw [hcells, integral_iUnion_fintype hmeas hdisj hint]
  simp_rw [rd_setIntegral_cell hper, hQ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, ← mul_assoc]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_mul]

/-- A Lipschitz `ℤ^m`-periodic map is bounded: it takes all its values on `[0, 1]^m`. -/
lemma rd_periodic_bounded {φ : (Fin m → ℝ) → Fin d → ℝ} {K : NNReal}
    (hφ : LipschitzWith K φ) (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ),
      φ (x + fun i => (z i : ℝ)) = φ x) :
    ∃ M, 0 ≤ M ∧ ∀ x, ‖φ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ =>
    isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hφ.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hx : (x + fun i => ((-⌊x i⌋ : ℤ) : ℝ)) ∈ Set.pi Set.univ fun _ => Set.Icc (0:ℝ) 1 := by
    intro i _
    simp only [Pi.add_apply, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  rw [← hper x (fun i => -⌊x i⌋)]
  exact (hC _ hx).trans (le_max_left _ _)

/-- The gradient of a periodic map is periodic. -/
lemma rd_grad_periodic {φ : (Fin m → ℝ) → Fin d → ℝ}
    (hper : ∀ (x : Fin m → ℝ) (z : Fin m → ℤ), φ (x + fun i => (z i : ℝ)) = φ x)
    (x : Fin m → ℝ) (z : Fin m → ℤ) : grad φ (x + fun i => (z i : ℝ)) = grad φ x := by
  ext i k
  simp only [grad, Matrix.of_apply]
  rw [← fderiv_comp_add_right (f := fun y => φ y i)]
  congr 2
  funext y
  rw [hper]

end CalculusOfVariations
