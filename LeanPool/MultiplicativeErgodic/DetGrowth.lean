/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Analysis.Normed.Group.Quotient

public import LeanPool.MultiplicativeErgodic.GrowthFunction

/-!
# The determinant growth `E_k`, and the comparison of `D_k` with `∏ ρ_i`

`proof_met.tex` l.209-211 asserts `c_k D_k ≤ ∏_{i≤k} ρ_i ≤ C_k D_k` and cites
`gonzalez2015concise` for it. This file carries out that argument. It goes through a third
quantity, the supremum of `|det (θᵢ (T xⱼ))|` over functionals and vectors in the closed unit
balls, which unlike `volForm` is multilinear and alternating and so can be manipulated by row and
column operations.

The constants here are not the paper's and no attempt is made to match them: the statement only
claims agreement up to constants depending on `k`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open Module _root_.Submodule MultiplicativeErgodic.Submodule Metric

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_dual_vanishing (W : Submodule ℝ X) (x : X) :
    ∃ θ : X →L[ℝ] ℝ, ‖θ‖ ≤ 1 ∧ (∀ w ∈ W, θ w = 0) ∧
      θ x = Metric.infDist x (W : Set X) := by
  set q : X →L[ℝ] (X ⧸ W) :=
    (W.mkQ).mkContinuous 1 (fun z => by
      simpa using (Submodule.Quotient.norm_mk_le W z)) with hq
  obtain ⟨ψ, hψ1, hψ⟩ := exists_dual_vector'' ℝ (q x)
  refine ⟨ψ.comp q, ?_, ?_, ?_⟩
  · refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have hqn : ‖q‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
    nlinarith [norm_nonneg ψ, norm_nonneg q]
  · intro w hw
    have : q w = 0 := by
      change W.mkQ w = 0
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp [this]
  · have hnorm : ‖q x‖ = Metric.infDist x (W : Set X) := by
      change ‖(W.mkQ x : X ⧸ W)‖ = _
      rw [Submodule.mkQ_apply]
      exact QuotientAddGroup.norm_mk x
    simpa [hnorm] using hψ

open Classical in
/-- `E_k(T)`: the supremum of `|det (θᵢ (T xⱼ))|` over functionals and vectors in the closed unit
balls. Multilinearity makes this the mediating quantity between `D_k` and `∏ ρ_i`. -/
noncomputable def detGrowth (T : X →L[ℝ] X) (k : ℕ) : ℝ :=
  sSup (Set.range fun p : (Fin k → (X →L[ℝ] ℝ)) × (Fin k → X) =>
    if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
    then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0)

open Classical in
theorem detGrowth_bddAbove (T : X →L[ℝ] X) (k : ℕ) :
    BddAbove (Set.range fun p : (Fin k → (X →L[ℝ] ℝ)) × (Fin k → X) =>
      if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
      then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0) := by
  refine ⟨(Nat.factorial k) * ‖T‖ ^ k, ?_⟩
  rintro _ ⟨p, rfl⟩
  change (if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
    then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0)
      ≤ (Nat.factorial k) * ‖T‖ ^ k
  by_cases h : (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
  · rw [ite_eq_left h]
    have hent : ∀ i j, |p.1 i (T (p.2 j))| ≤ ‖T‖ := by
      intro i j
      have h1 : ‖p.1 i (T (p.2 j))‖ ≤ ‖p.1 i‖ * ‖T (p.2 j)‖ := (p.1 i).le_opNorm _
      have h2 : ‖T (p.2 j)‖ ≤ ‖T‖ * ‖p.2 j‖ := T.le_opNorm _
      rw [Real.norm_eq_abs] at h1
      nlinarith [h.1 i, h.2 j, norm_nonneg (p.1 i), norm_nonneg (T (p.2 j)),
        norm_nonneg T, norm_nonneg (p.2 j)]
    set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => p.1 i (T (p.2 j)) with hM
    rw [Matrix.det_apply']
    have hterm : ∀ σ : Equiv.Perm (Fin k),
        |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i| ≤ ‖T‖ ^ k := by
      intro σ
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
      calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin k, ‖T‖ :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hent _ _)
        _ = ‖T‖ ^ k := by simp
    calc |∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin k), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin k), ‖T‖ ^ k := Finset.sum_le_sum fun σ _ => hterm σ
      _ = (Nat.factorial k) * ‖T‖ ^ k := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm,
            Fintype.card_fin]
  · rw [ite_eq_right h]
    positivity

open Classical in
theorem detGrowth_nonneg (T : X →L[ℝ] X) (k : ℕ) : 0 ≤ detGrowth T k := by
  classical
  refine le_csSup_of_le (detGrowth_bddAbove T k)
    (Set.mem_range_self (f := fun p : (Fin k → (X →L[ℝ] ℝ)) × (Fin k → X) =>
      if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
      then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0) (0, 0)) ?_
  change (0:ℝ) ≤ if (∀ i : Fin k, ‖(0 : Fin k → (X →L[ℝ] ℝ)) i‖ ≤ 1) ∧
      (∀ j : Fin k, ‖(0 : Fin k → X) j‖ ≤ 1)
    then |Matrix.det (Matrix.of fun i j => (0 : Fin k → (X →L[ℝ] ℝ)) i (T ((0 : Fin k → X) j)))|
    else 0
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

open Classical in
/-- **`D_k ≤ E_k`** (`gonzalez2015concise`, first half of (2)). Hahn-Banach produces functionals
that make the matrix triangular with the volume factors on the diagonal. -/
theorem volumeGrowth_le_detGrowth (T : X →L[ℝ] X) (k : ℕ) :
    volumeGrowth T k ≤ detGrowth T k := by
  classical
  refine Real.sSup_le ?_ (detGrowth_nonneg T k)
  rintro _ ⟨u, rfl⟩
  change (if ∀ i, u i ∈ Metric.sphere (0 : X) 1 then volForm T u else 0) ≤ detGrowth T k
  by_cases h : ∀ i, u i ∈ Metric.sphere (0 : X) 1
  · rw [ite_eq_left h]
    choose θ hθnorm hθzero hθval using fun i : Fin k =>
      exists_dual_vanishing (Submodule.span ℝ ((fun j : Fin k => T (u j)) '' {j | j < i}))
        (T (u i))
    set M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => θ i (T (u j)) with hM
    have htri : M.BlockTriangular id := by
      intro i j hji
      exact hθzero i _ (Submodule.subset_span ⟨j, hji, rfl⟩)
    have hdet : M.det = volForm T u := by
      rw [Matrix.det_of_isUpperTriangular htri, volForm]
      exact Finset.prod_congr rfl fun i _ => hθval i
    have hmem : volForm T u ≤ detGrowth T k := by
      refine le_csSup_of_le (detGrowth_bddAbove T k)
        (Set.mem_range_self (f := fun p : (Fin k → (X →L[ℝ] ℝ)) × (Fin k → X) =>
          if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
          then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0) (θ, u)) ?_
      change volForm T u ≤ if (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ j, ‖u j‖ ≤ 1)
        then |Matrix.det (Matrix.of fun i j => θ i (T (u j)))| else 0
      rw [ite_eq_left ⟨hθnorm, fun j => le_of_eq (mem_sphere_zero_iff_norm.mp (h j))⟩]
      rw [← hM, hdet, abs_of_nonneg (volForm_nonneg T u)]
    exact hmem
  · rw [ite_eq_right h]
    exact detGrowth_nonneg T k

/-- Rescaling each vector by a nonzero scalar leaves the spans of initial segments alone. -/
theorem span_image_smul {k : ℕ} (v : Fin k → X) (c : Fin k → ℝ) (hc : ∀ i, c i ≠ 0)
    (s : Set (Fin k)) :
    Submodule.span ℝ ((fun j => c j • v j) '' s) = Submodule.span ℝ (v '' s) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rintro _ ⟨j, hj, rfl⟩
    have : v j = (c j)⁻¹ • (c j • v j) := by
      rw [smul_smul, inv_mul_cancel₀ (hc j), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)

/-- `volForm` is homogeneous in each slot. -/
theorem volForm_smul (T : X →L[ℝ] X) {k : ℕ} (v : Fin k → X) (c : Fin k → ℝ)
    (hc : ∀ i, c i ≠ 0) :
    volForm T (fun j => c j • v j) = (∏ j, |c j|) * volForm T v := by
  rw [volForm, volForm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hspan : Submodule.span ℝ ((fun j => T ((fun l => c l • v l) j)) '' {j | j < i})
      = Submodule.span ℝ ((fun j => T (v j)) '' {j | j < i}) := by
    have : (fun j => T ((fun l => c l • v l) j)) = fun j => c j • T (v j) := by
      funext j; simp
    rw [this]
    exact span_image_smul (fun j => T (v j)) c hc _
  rw [hspan]
  have : T ((fun l => c l • v l) i) = c i • T (v i) := by simp
  rw [this, infDist_smul_submodule]

/-- An element of the span of an initial segment is a combination of that segment, written with
coefficients indexed by all of `Fin k` and supported below `j`. -/
theorem exists_coeff_of_mem_span_lt {k : ℕ} (v : Fin k → X) (j : Fin k) {y : X}
    (hy : y ∈ Submodule.span ℝ (v '' {l | l < j})) :
    ∃ c : Fin k → ℝ, (∀ l, ¬ (l < j) → c l = 0) ∧ ∑ l, c l • v l = y := by
  classical
  have hrange : v '' {l : Fin k | l < j} =
      Set.range (fun l : {l : Fin k // l < j} => v (l : Fin k)) := by
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l, rfl⟩; exact ⟨(l : Fin k), l.2, rfl⟩
  rw [hrange] at hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
  set c : Fin k → ℝ := fun l => if h : l < j then a ⟨l, h⟩ else 0 with hc
  refine ⟨c, fun l hl => by simp [hc, hl], ?_⟩
  have h1 : ∑ i : {l : Fin k // l < j}, a i • v (i : Fin k)
      = ∑ i : {l : Fin k // l < j}, c (i : Fin k) • v (i : Fin k) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    simp only [dite_eq_left i.2]
  rw [← ha, h1, ← Finset.sum_subtype (s := Finset.univ.filter (fun l : Fin k => l < j))
    (p := fun l : Fin k => l < j) (by simp) (fun l => c l • v l)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro l _ hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  simp [hc, hl]

open Classical in
/-- **`E_k ≤ k! · D_k`** (`gonzalez2015concise`, second half of (2)). Column operations, packaged
as right multiplication by a unit upper-triangular matrix, replace each `xⱼ` by a representative
of its class modulo the earlier ones; the entries of the new matrix are then bounded by the volume
factors, and the Leibniz formula contributes the `k!`. -/
theorem detGrowth_le_factorial_mul_volumeGrowth (T : X →L[ℝ] X) (k : ℕ) :
    detGrowth T k ≤ (Nat.factorial k) * volumeGrowth T k := by
  classical
  have hDnn := volumeGrowth_nonneg T k
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨p, rfl⟩
  obtain ⟨θ, x⟩ := p
  change (if (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ j, ‖x j‖ ≤ 1)
    then |Matrix.det (Matrix.of fun i j => θ i (T (x j)))| else 0)
      ≤ (Nat.factorial k) * volumeGrowth T k
  by_cases h : (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ j, ‖x j‖ ≤ 1)
  swap
  · rw [ite_eq_right h]; positivity
  rw [ite_eq_left h]
  set U : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => θ i (T (x j)) with hU
  set α : Fin k → ℝ := fun j =>
    Metric.infDist (T (x j)) ((Submodule.span ℝ ((fun l => T (x l)) '' {l | l < j})) : Set X)
    with hα
  have hαnn : ∀ j, 0 ≤ α j := fun j => Metric.infDist_nonneg
  -- (A) the product of the volume factors is at most `D_k`
  have hA : ∏ j, α j ≤ volumeGrowth T k := by
    by_cases hz : ∃ j, x j = 0
    · obtain ⟨j, hj⟩ := hz
      have : α j = 0 := by
        rw [hα]
        simp only [hj, map_zero]
        exact Metric.infDist_zero_of_mem (Submodule.zero_mem _)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) this]
      exact hDnn
    · push Not at hz
      set c : Fin k → ℝ := fun j => ‖x j‖⁻¹ with hc
      have hcne : ∀ j, c j ≠ 0 := fun j => by
        rw [hc]
        exact inv_ne_zero (norm_ne_zero_iff.mpr (hz j))
      have hxnorm : ∀ j, ‖c j • x j‖ = 1 := by
        intro j
        rw [hc, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hz j))]
      have hone : (1:ℝ) ≤ ∏ j, |c j| := by
        have hstep : ∀ j : Fin k, (1:ℝ) ≤ |c j| := by
          intro j
          rw [hc]
          simp only [abs_inv, abs_of_nonneg (norm_nonneg (x j))]
          rw [one_le_inv_iff₀]
          exact ⟨norm_pos_iff.mpr (hz j), h.2 j⟩
        have hprod : (∏ _j : Fin k, (1:ℝ)) ≤ ∏ j, |c j| :=
          Finset.prod_le_prod₀ (fun j _ => zero_le_one) (fun j _ => hstep j)
        simpa using hprod
      have hscale := volForm_smul T x c hcne
      have hle : volForm T x ≤ volForm T (fun j => c j • x j) := by
        rw [hscale]
        nlinarith [volForm_nonneg T x]
      exact le_trans hle (volForm_le_volumeGrowth T hxnorm)
  -- (B) the determinant bound at scale `ε`
  have hB : ∀ ε : ℝ, 0 < ε → |U.det| ≤ (Nat.factorial k) * ∏ j, (α j + ε) := by
    intro ε hε
    have hex : ∀ j : Fin k, ∃ c : Fin k → ℝ, (∀ l, ¬ (l < j) → c l = 0) ∧
        ‖T (x j) - ∑ l, c l • T (x l)‖ < α j + ε := by
      intro j
      obtain ⟨y, hy, hylt⟩ := (Metric.infDist_lt_iff ⟨0, Submodule.zero_mem _⟩).mp
        (show α j < α j + ε by linarith)
      obtain ⟨c, hc0, hcy⟩ := exists_coeff_of_mem_span_lt (fun l => T (x l)) j hy
      exact ⟨c, hc0, by rw [hcy, ← dist_eq_norm]; exact hylt⟩
    choose cc hcc0 hcclt using hex
    set A : Matrix (Fin k) (Fin k) ℝ :=
      Matrix.of fun l j => if l = j then 1 else -(cc j l) with hA'
    have hAtri : A.BlockTriangular id := by
      intro l j hjl
      have hne : l ≠ j := fun hlj => by rw [hlj] at hjl; exact lt_irrefl _ hjl
      have : ¬ (l < j) := not_lt.mpr (le_of_lt hjl)
      rw [hA']
      simp only [Matrix.of_apply, ite_eq_right hne, hcc0 j l this, neg_zero]
    have hAdet : A.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular hAtri]
      simp [hA']
    have hentry : ∀ i j, (U * A) i j = θ i (T (x j)) - ∑ l, cc j l * θ i (T (x l)) := by
      intro i j
      have hccjj : cc j j = 0 := hcc0 j j (lt_irrefl j)
      rw [Matrix.mul_apply]
      have hsplit : ∀ l, U i l * A l j
          = (if l = j then θ i (T (x j)) else 0) - cc j l * θ i (T (x l)) := by
        intro l
        rcases eq_or_ne l j with rfl | hlj
        · simp [hU, hA', hccjj]
        · simp only [hU, hA', Matrix.of_apply, ite_eq_right hlj]
          ring
      rw [Finset.sum_congr rfl (fun l _ => hsplit l), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ j]
      simp
    have hentry' : ∀ i j, (U * A) i j = θ i (T (x j) - ∑ l, cc j l • T (x l)) := by
      intro i j
      rw [hentry i j, map_sub, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul]
    have hbd : ∀ i j, |(U * A) i j| ≤ α j + ε := by
      intro i j
      rw [hentry' i j]
      calc |θ i (T (x j) - ∑ l, cc j l • T (x l))|
          = ‖θ i (T (x j) - ∑ l, cc j l • T (x l))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖θ i‖ * ‖T (x j) - ∑ l, cc j l • T (x l)‖ := (θ i).le_opNorm _
        _ ≤ 1 * (α j + ε) := by
            refine mul_le_mul (h.1 i) (le_of_lt (hcclt j)) (norm_nonneg _) zero_le_one
        _ = α j + ε := one_mul _
    have hdeteq : U.det = (U * A).det := by rw [Matrix.det_mul, hAdet, mul_one]
    rw [hdeteq, Matrix.det_apply']
    have hterm : ∀ σ : Equiv.Perm (Fin k),
        |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (U * A) (σ i) i| ≤ ∏ j, (α j + ε) := by
      intro σ
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hbd _ _)
    calc |∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (U * A) (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin k), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (U * A) (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin k), ∏ j, (α j + ε) := Finset.sum_le_sum fun σ _ => hterm σ
      _ = (Nat.factorial k) * ∏ j, (α j + ε) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm,
            Fintype.card_fin]
  -- (C) let `ε → 0`
  have hcont : Filter.Tendsto (fun ε : ℝ => (Nat.factorial k : ℝ) * ∏ j, (α j + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Nat.factorial k : ℝ) * ∏ j, α j)) := by
    have h1 : Continuous fun ε : ℝ => (Nat.factorial k : ℝ) * ∏ j, (α j + ε) :=
      continuous_const.mul (continuous_finsetProd _ fun i _ => continuous_const.add continuous_id)
    have h2 : Filter.Tendsto (fun ε : ℝ => (Nat.factorial k : ℝ) * ∏ j, (α j + ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Nat.factorial k : ℝ) * ∏ j, (α j + 0))) :=
      (h1.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h2
  have hfinal : |U.det| ≤ (Nat.factorial k : ℝ) * ∏ j, α j := by
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hB ε hε
  calc |U.det| ≤ (Nat.factorial k : ℝ) * ∏ j, α j := hfinal
    _ ≤ (Nat.factorial k : ℝ) * volumeGrowth T k := by
        refine mul_le_mul_of_nonneg_left hA (by positivity)

open Classical in
/-- The key step of the lower half of `gonzalez2015concise` Lemma 5, for a single admissible
`(n)`-tuple and a single `(n+1)`-dimensional subspace. -/
theorem detGrowth_succ_ge_aux (T : X →L[ℝ] X) (n : ℕ) (V : GrassmannianFin X (n + 1))
    (θ' : Fin n → (X →L[ℝ] ℝ)) (x' : Fin n → X)
    (hθ' : ∀ i, ‖θ' i‖ ≤ 1) (hx' : ∀ j, ‖x' j‖ ≤ 1) :
    |Matrix.det (Matrix.of fun i j => θ' i (T (x' j)))| * growth T (V.1 : Submodule ℝ X)
      ≤ (n + 1) * detGrowth T (n + 1) := by
  classical
  set Δ : ℝ := Matrix.det (Matrix.of fun i j => θ' i (T (x' j))) with hΔ
  set g : ℝ := growth T (V.1 : Submodule ℝ X) with hg
  rcases le_or_gt g 0 with hg0 | hgpos
  · have : |Δ| * g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hg0
    refine this.trans ?_
    have := detGrowth_nonneg T (n + 1)
    positivity
  -- `T` is injective on `V`
  have : FiniteDimensional ℝ (V.1 : Submodule ℝ X) := V.2.1
  have hinj : Function.Injective (T.toLinearMap.domRestrict (V.1 : Submodule ℝ X)) :=
    injective_domRestrict_of_growth_pos hgpos
  set A : Submodule ℝ X := Submodule.map (T : X →ₗ[ℝ] X) (V.1 : Submodule ℝ X) with hA
  have : FiniteDimensional ℝ A := by
    rw [hA]; exact Module.Finite.map _ _
  have hAdim : Module.finrank ℝ A = n + 1 := by
    have he : (V.1 : Submodule ℝ X) ≃ₗ[ℝ] A :=
      (LinearEquiv.ofInjective _ hinj).trans
        (LinearEquiv.ofEq _ _ (LinearMap.range_domRestrict _ _))
    rw [hA, ← he.finrank_eq, V.2.2]
  set W : Submodule ℝ X := Submodule.span ℝ (Set.range fun j => T (x' j)) with hW
  have : FiniteDimensional ℝ W := by
    rw [hW]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hWdim : Module.finrank ℝ W ≤ n := by
    simpa [hW, Set.finrank, Fintype.card_fin] using finrank_range_le_card (R := ℝ)
      (fun j => T (x' j))
  -- a unit vector of `TV` far from `W`
  obtain ⟨z, hzA, hznorm, hzfar⟩ :=
    exists_unit_far_of_finrank_lt (A := A) (W := W) (by omega)
  obtain ⟨w, hwV, hwz⟩ : ∃ w ∈ (V.1 : Submodule ℝ X), T w = z := by
    rw [hA] at hzA; exact hzA
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, map_zero] at hwz; rw [← hwz, norm_zero] at hznorm; norm_num at hznorm
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set v : X := ‖w‖⁻¹ • w with hv
  have hvnorm : ‖v‖ = 1 := by
    rw [hv, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hwpos)]
  have hvV : v ∈ (V.1 : Submodule ℝ X) := Submodule.smul_mem _ _ hwV
  have hTv : T v = ‖w‖⁻¹ • z := by rw [hv, map_smul, hwz]
  -- the extra functional
  obtain ⟨θl, hθlnorm, hθlzero, hθlval⟩ := exists_dual_vanishing W z
  have hθlTv : θl (T v) = ‖w‖⁻¹ * Metric.infDist z (W : Set X) := by
    rw [hTv, map_smul, smul_eq_mul, hθlval]
  -- the `(n+1)`-tuple
  set Θ : Fin (n + 1) → (X →L[ℝ] ℝ) := Fin.cons θl θ' with hΘ
  set Y : Fin (n + 1) → X := Fin.cons v x' with hY
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => Θ i (T (Y j)) with hM
  have hrow0 : ∀ j : Fin n, M 0 j.succ = 0 := by
    intro j
    simp only [hM, hΘ, hY, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
    exact hθlzero _ (Submodule.subset_span ⟨j, rfl⟩)
  have hdetM : M.det = M 0 0 * Δ := by
    rw [Matrix.det_succ_row_zero]
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · have hsub : (M.submatrix Fin.succ (Fin.succAbove 0)) =
        Matrix.of fun i j => θ' i (T (x' j)) := by
        funext i j
        simp [hM, hΘ, hY, Fin.succAbove_zero]
      rw [hsub, Fin.val_zero, pow_zero, one_mul, ← hΔ]
    · intro j _ hj
      obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero hj
      rw [hrow0 j']
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  have hM00 : M 0 0 = θl (T v) := by simp [hM, hΘ, hY]
  -- the determinant is admissible for `E_{n+1}`
  have hadm : |M.det| ≤ detGrowth T (n + 1) := by
    refine le_csSup_of_le (detGrowth_bddAbove T (n + 1))
      (Set.mem_range_self (f := fun p : (Fin (n+1) → (X →L[ℝ] ℝ)) × (Fin (n+1) → X) =>
        if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
        then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0) (Θ, Y)) ?_
    change |M.det| ≤ if (∀ i, ‖Θ i‖ ≤ 1) ∧ (∀ j, ‖Y j‖ ≤ 1)
      then |Matrix.det (Matrix.of fun i j => Θ i (T (Y j)))| else 0
    rw [ite_eq_left ⟨fun i => by
        refine Fin.cases ?_ ?_ i
        · simpa [hΘ] using hθlnorm
        · intro i'; simpa [hΘ] using hθ' i',
      fun j => by
        refine Fin.cases ?_ ?_ j
        · simp [hY, hvnorm]
        · intro j'; simpa [hY] using hx' j'⟩]
  -- and it is at least `|Δ| g / (n+1)`
  have hlow : |Δ| * g / (n + 1) ≤ |M.det| := by
    rw [hdetM, hM00, abs_mul, hθlTv]
    have hTvnorm : ‖T v‖ = ‖w‖⁻¹ := by
      rw [hTv, norm_smul, norm_inv, norm_norm, hznorm, mul_one]
    have hgle : g ≤ ‖w‖⁻¹ := by
      rw [← hTvnorm]
      have := growth_mul_norm_le T hvV
      rw [hvnorm, mul_one] at this
      exact this
    have hfar : (1:ℝ) / (n + 1) ≤ Metric.infDist z (W : Set X) := by
      refine le_trans ?_ hzfar
      have : (Module.finrank ℝ W : ℝ) ≤ n := by exact_mod_cast hWdim
      apply div_le_div_of_nonneg_left one_pos.le (by positivity)
      linarith
    have h1 : 0 ≤ |Δ| := abs_nonneg _
    have h2 : (0:ℝ) < ‖w‖⁻¹ := inv_pos.mpr hwpos
    have hdnn : (0:ℝ) ≤ Metric.infDist z (W : Set X) := Metric.infDist_nonneg
    rw [abs_of_nonneg (mul_nonneg h2.le hdnn)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)]
    have h3 : g * (1 / ((n:ℝ) + 1)) ≤ ‖w‖⁻¹ * Metric.infDist z (W : Set X) :=
      mul_le_mul hgle hfar (by positivity) h2.le
    have hkey : g ≤ (‖w‖⁻¹ * Metric.infDist z (W : Set X)) * ((n:ℝ) + 1) := by
      have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)
      rw [mul_assoc, one_div, inv_mul_cancel₀ (by positivity : ((n:ℝ) + 1) ≠ 0), mul_one] at h4
      exact h4
    nlinarith [hkey, h1, mul_nonneg h2.le hdnn]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) + 1)] at hlow
  calc |Δ| * g ≤ |M.det| * ((n:ℝ) + 1) := hlow
    _ ≤ detGrowth T (n + 1) * ((n:ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hadm (by positivity)
    _ = ((n:ℝ) + 1) * detGrowth T (n + 1) := mul_comm _ _

open Classical in
/-- **Lower half of `gonzalez2015concise` Lemma 5**, with the constant `n+1` that
`exists_unit_far_of_finrank_lt` costs in place of their appeal to Gohberg-Krein. -/
theorem detGrowth_succ_ge (T : X →L[ℝ] X) (n : ℕ) :
    detGrowth T n * bernsteinNumber T (n + 1) ≤ ((n : ℝ) + 1) * detGrowth T (n + 1) := by
  classical
  have hEnn := detGrowth_nonneg T (n + 1)
  have hM : (0:ℝ) ≤ ((n:ℝ) + 1) * detGrowth T (n + 1) := by positivity
  have step1 : ∀ V : GrassmannianFin X (n + 1),
      detGrowth T n * growth T (V.1 : Submodule ℝ X)
        ≤ ((n:ℝ) + 1) * detGrowth T (n + 1) := by
    intro V
    rcases eq_or_lt_of_le (growth_nonneg T (V.1 : Submodule ℝ X)) with h0 | hpos
    · rw [← h0, mul_zero]; exact hM
    · rw [← le_div_iff₀ hpos]
      refine Real.sSup_le ?_ (by positivity)
      rintro _ ⟨p, rfl⟩
      obtain ⟨θ', x'⟩ := p
      change (if (∀ i, ‖θ' i‖ ≤ 1) ∧ (∀ j, ‖x' j‖ ≤ 1)
        then |Matrix.det (Matrix.of fun i j => θ' i (T (x' j)))| else 0)
          ≤ ((n:ℝ) + 1) * detGrowth T (n + 1) / growth T (V.1 : Submodule ℝ X)
      by_cases hadm : (∀ i, ‖θ' i‖ ≤ 1) ∧ (∀ j, ‖x' j‖ ≤ 1)
      · rw [ite_eq_left hadm, le_div_iff₀ hpos]
        exact detGrowth_succ_ge_aux T n V θ' x' hadm.1 hadm.2
      · rw [ite_eq_right hadm]; positivity
  rcases eq_or_lt_of_le (detGrowth_nonneg T n) with h0 | hpos
  · rw [← h0, zero_mul]; exact hM
  · rw [mul_comm, ← le_div_iff₀ hpos]
    change sSup (Set.range fun V : GrassmannianFin X (n + 1) =>
      growth T (V.1 : Submodule ℝ X)) ≤ _
    refine Real.sSup_le ?_ (by positivity)
    rintro _ ⟨V, rfl⟩
    rw [le_div_iff₀ hpos, mul_comm]
    exact step1 V

open Classical in
theorem detGrowth_zero (T : X →L[ℝ] X) : detGrowth T 0 = 1 := by
  classical
  have hfun : (fun p : (Fin 0 → (X →L[ℝ] ℝ)) × (Fin 0 → X) =>
      if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
      then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0) = fun _ => (1:ℝ) := by
    funext p
    rw [ite_eq_left ⟨fun i => i.elim0, fun j => j.elim0⟩]
    simp
  change sSup (Set.range _) = 1
  rw [hfun, Set.range_const, csSup_singleton]

/-- Iterating the lower half of Lemma 5: `∏_{i≤k} ρ_i ≤ k! · E_k`. -/
theorem prod_bernstein_le_detGrowth (T : X →L[ℝ] X) (k : ℕ) :
    ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1)
      ≤ (Nat.factorial k) * detGrowth T k := by
  induction k with
  | zero => simp [detGrowth_zero]
  | succ n ih =>
      rw [Finset.prod_range_succ]
      have hρ : 0 ≤ bernsteinNumber T (n + 1) := bernsteinNumber_nonneg T (n + 1)
      have hfac : (0:ℝ) ≤ (Nat.factorial n : ℝ) := by positivity
      calc (∏ i ∈ Finset.range n, bernsteinNumber T (i + 1)) * bernsteinNumber T (n + 1)
          ≤ ((Nat.factorial n : ℝ) * detGrowth T n) * bernsteinNumber T (n + 1) :=
            mul_le_mul_of_nonneg_right ih hρ
        _ = (Nat.factorial n : ℝ) * (detGrowth T n * bernsteinNumber T (n + 1)) := by ring
        _ ≤ (Nat.factorial n : ℝ) * (((n:ℝ) + 1) * detGrowth T (n + 1)) :=
            mul_le_mul_of_nonneg_left (detGrowth_succ_ge T n) hfac
        _ = (Nat.factorial (n + 1) : ℝ) * detGrowth T (n + 1) := by
            rw [Nat.factorial_succ]
            push_cast
            ring

open Classical in
/-- **Upper half of `gonzalez2015concise` Lemma 5.** The paper first row-reduces the functionals
against the one maximising `|θᵢ(Tv)|`, which buys the sharper constant `k2^{k-1}`; since only the
existence of constants is claimed, we expand along the column directly and settle for `(n+1)²`. -/
theorem detGrowth_succ_le (T : X →L[ℝ] X) (n : ℕ) :
    detGrowth T (n + 1) ≤ ((n:ℝ) + 1)^2 * (detGrowth T n * bernsteinNumber T (n + 1)) := by
  classical
  have hEn := detGrowth_nonneg T n
  have hρ := bernsteinNumber_nonneg T (n + 1)
  refine Real.sSup_le ?_ (by positivity)
  rintro _ ⟨p, rfl⟩
  obtain ⟨θ, x⟩ := p
  change (if (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ j, ‖x j‖ ≤ 1)
    then |Matrix.det (Matrix.of fun i j => θ i (T (x j)))| else 0)
      ≤ ((n:ℝ) + 1)^2 * (detGrowth T n * bernsteinNumber T (n + 1))
  by_cases hadm : (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ j, ‖x j‖ ≤ 1)
  swap
  · rw [ite_eq_right hadm]; positivity
  rw [ite_eq_left hadm]
  set U : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j => θ i (T (x j)) with hU
  -- if the `x j` are dependent the determinant vanishes
  by_cases hdep : ∃ c : Fin (n+1) → ℝ, c ≠ 0 ∧ ∑ j, c j • x j = 0
  · obtain ⟨c, hc0, hcsum⟩ := hdep
    have hdet : U.det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨c, hc0, ?_⟩
      funext i
      change ∑ j, U i j * c j = 0
      have : ∑ j, U i j * c j = θ i (T (∑ j, c j • x j)) := by
        rw [map_sum, map_sum]
        exact Finset.sum_congr rfl fun j _ => by
          rw [map_smul, map_smul, smul_eq_mul, hU]; simp [mul_comm]
      rw [this, hcsum, map_zero, map_zero]
    rw [hdet, abs_zero]; positivity
  push Not at hdep
  have hindep : LinearIndependent ℝ x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    have : c ≠ 0 := fun h0 => hne (fun i => by rw [h0]; rfl)
    exact absurd hc (hdep c this)
  -- the span is an honest `(n+1)`-dimensional subspace
  set V : Submodule ℝ X := Submodule.span ℝ (Set.range x) with hV
  have : FiniteDimensional ℝ V := by
    rw [hV]; exact FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  have hVdim : Module.finrank ℝ V = n + 1 := by
    rw [hV, finrank_span_eq_card hindep]; simp
  set Vg : GrassmannianFin X (n + 1) := ⟨V, inferInstance, hVdim⟩ with hVg
  have hgV : growth T V ≤ bernsteinNumber T (n + 1) := by
    refine le_csSup ⟨‖T‖, ?_⟩ ⟨Vg, rfl⟩
    rintro _ ⟨Z, rfl⟩
    exact growth_le_opNorm T _
  -- for each `ε`, a nearly-slowest unit vector of `V`
  have key : ∀ ε : ℝ, 0 < ε →
      |U.det| ≤ ((n:ℝ) + 1)^2 * (detGrowth T n * (bernsteinNumber T (n + 1) + ε)) := by
    intro ε hε
    have hne : (Metric.sphere (0 : X) 1 ∩ (V : Set X)).Nonempty := by
      have : Vg.sphere.Nonempty := Vg.nonempty_sphere
      exact this
    obtain ⟨_, ⟨v, hvmem, rfl⟩, hvlt⟩ := exists_lt_of_csInf_lt (hne.image _)
      (show growth T V < growth T V + ε by linarith)
    have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hvmem.1
    have hvlt' : ‖T v‖ < growth T V + ε := hvlt
    have hTvlt : ‖T v‖ < bernsteinNumber T (n + 1) + ε := by linarith [hgV]
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvmem.2
    -- some coefficient is at least `1/(n+1)`
    have hbig : ∃ j0, (1:ℝ) / ((n:ℝ) + 1) ≤ |a j0| := by
      by_contra hcon
      push Not at hcon
      have h1 : (1:ℝ) ≤ ∑ j, |a j| := by
        calc (1:ℝ) = ‖v‖ := hvnorm.symm
          _ = ‖∑ j, a j • x j‖ := by rw [ha]
          _ ≤ ∑ j, ‖a j • x j‖ := norm_sum_le _ _
          _ ≤ ∑ j, |a j| := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_smul, Real.norm_eq_abs]
              nlinarith [abs_nonneg (a j), hadm.2 j, norm_nonneg (x j)]
      have h2 : ∑ j, |a j| < 1 := by
        calc ∑ j, |a j| < ∑ _j : Fin (n+1), ((1:ℝ)/((n:ℝ)+1)) := by
              refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun j _ => hcon j
          _ = ((n:ℝ) + 1) * (1/((n:ℝ)+1)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              push_cast; ring
          _ = 1 := by field_simp
      linarith
    obtain ⟨j0, hj0⟩ := hbig
    have haj0 : a j0 ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hj0
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    -- replace column `j0` by `v`
    set Utl : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
      U.updateCol j0 (fun i => ∑ l, a l • U i l) with hUtl
    have hdetUtl : Utl.det = a j0 * U.det := by
      rw [hUtl, Matrix.det_updateCol_sum, smul_eq_mul]
    have hcol : ∀ i, Utl i j0 = θ i (T v) := by
      intro i
      rw [hUtl, Matrix.updateCol_self, ← ha, map_sum, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, map_smul, smul_eq_mul, hU]; simp
    have hoff : ∀ (i : Fin (n+1)) (j : Fin (n+1)), j ≠ j0 → Utl i j = U i j := fun i j hj => by
      rw [hUtl, Matrix.updateCol_ne hj]
    -- expand along column `j0`
    have hminor : ∀ i : Fin (n+1),
        |(Utl.submatrix i.succAbove j0.succAbove).det| ≤ detGrowth T n := by
      intro i
      have hsub : Utl.submatrix i.succAbove j0.succAbove
          = Matrix.of fun i' j' => (fun i' => θ (i.succAbove i')) i'
              (T ((fun j' => x (j0.succAbove j')) j')) := by
        funext i' j'
        rw [Matrix.submatrix_apply, hoff _ _ (Fin.succAbove_ne j0 j')]
        rfl
      rw [hsub]
      refine le_csSup_of_le (detGrowth_bddAbove T n)
        (Set.mem_range_self (f := fun p : (Fin n → (X →L[ℝ] ℝ)) × (Fin n → X) =>
          if (∀ i, ‖p.1 i‖ ≤ 1) ∧ (∀ j, ‖p.2 j‖ ≤ 1)
          then |Matrix.det (Matrix.of fun i j => p.1 i (T (p.2 j)))| else 0)
          ((fun i' => θ (i.succAbove i')), (fun j' => x (j0.succAbove j')))) ?_
      rw [ite_eq_left ⟨fun i' => hadm.1 _, fun j' => hadm.2 _⟩]
    have hexp : |Utl.det| ≤ ((n:ℝ) + 1) * (‖T v‖ * detGrowth T n) := by
      rw [Matrix.det_succ_column Utl j0]
      calc |∑ i : Fin (n+1), (-1:ℝ)^((i:ℕ) + (j0:ℕ)) * Utl i j0 *
              (Utl.submatrix i.succAbove j0.succAbove).det|
          ≤ ∑ i : Fin (n+1), |(-1:ℝ)^((i:ℕ) + (j0:ℕ)) * Utl i j0 *
              (Utl.submatrix i.succAbove j0.succAbove).det| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (n+1), ‖T v‖ * detGrowth T n := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
            have hb1 : |Utl i j0| ≤ ‖T v‖ := by
              rw [hcol i]
              calc |θ i (T v)| = ‖θ i (T v)‖ := (Real.norm_eq_abs _).symm
                _ ≤ ‖θ i‖ * ‖T v‖ := (θ i).le_opNorm _
                _ ≤ 1 * ‖T v‖ := by
                    exact mul_le_mul_of_nonneg_right (hadm.1 i) (norm_nonneg _)
                _ = ‖T v‖ := one_mul _
            exact mul_le_mul hb1 (hminor i) (abs_nonneg _) (norm_nonneg _)
        _ = ((n:ℝ) + 1) * (‖T v‖ * detGrowth T n) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
    -- combine
    have habs : |a j0| * |U.det| ≤ ((n:ℝ) + 1) * (‖T v‖ * detGrowth T n) := by
      rw [← abs_mul, ← hdetUtl]; exact hexp
    have hUd : |U.det| ≤ ((n:ℝ) + 1) * (((n:ℝ) + 1) * (‖T v‖ * detGrowth T n)) := by
      have hnp : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have h1 : (1/((n:ℝ)+1)) * |U.det| ≤ |a j0| * |U.det| :=
        mul_le_mul_of_nonneg_right hj0 (abs_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left (le_trans h1 habs) hnp.le
      rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hnp), one_mul] at h3
      exact h3
    calc |U.det| ≤ ((n:ℝ) + 1) * (((n:ℝ) + 1) * (‖T v‖ * detGrowth T n)) := hUd
      _ ≤ ((n:ℝ) + 1) * (((n:ℝ) + 1) * ((bernsteinNumber T (n+1) + ε) * detGrowth T n)) := by
          gcongr
      _ = ((n:ℝ) + 1)^2 * (detGrowth T n * (bernsteinNumber T (n + 1) + ε)) := by ring
  -- let `ε → 0`
  have hcont : Filter.Tendsto
      (fun ε : ℝ => ((n:ℝ) + 1)^2 * (detGrowth T n * (bernsteinNumber T (n + 1) + ε)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((n:ℝ) + 1)^2 * (detGrowth T n * bernsteinNumber T (n + 1)))) := by
    have h1 : Continuous fun ε : ℝ =>
        ((n:ℝ) + 1)^2 * (detGrowth T n * (bernsteinNumber T (n + 1) + ε)) := by continuity
    have h2 := (h1.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h2
  refine ge_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

/-- Iterating the upper half of Lemma 5: `E_k ≤ (k!)² ∏_{i≤k} ρ_i`. -/
theorem detGrowth_le_prod_bernstein (T : X →L[ℝ] X) (k : ℕ) :
    detGrowth T k
      ≤ ((Nat.factorial k : ℝ))^2 * ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) := by
  induction k with
  | zero => simp [detGrowth_zero]
  | succ n ih =>
      have hρ : 0 ≤ bernsteinNumber T (n + 1) := bernsteinNumber_nonneg T (n + 1)
      have hP : 0 ≤ ∏ i ∈ Finset.range n, bernsteinNumber T (i + 1) :=
        Finset.prod_nonneg fun i _ => bernsteinNumber_nonneg T (i + 1)
      calc detGrowth T (n + 1)
          ≤ ((n:ℝ) + 1)^2 * (detGrowth T n * bernsteinNumber T (n + 1)) :=
            detGrowth_succ_le T n
        _ ≤ ((n:ℝ) + 1)^2 * ((((Nat.factorial n : ℝ))^2 *
              ∏ i ∈ Finset.range n, bernsteinNumber T (i + 1)) * bernsteinNumber T (n + 1)) := by
            gcongr
        _ = ((Nat.factorial (n+1) : ℝ))^2 *
              ∏ i ∈ Finset.range (n + 1), bernsteinNumber T (i + 1) := by
            rw [Finset.prod_range_succ, Nat.factorial_succ]
            push_cast
            ring

/-- **`D_k` is comparable to `∏_{i≤k} ρ_i`** (`proof_met.tex` l.209-211), following
`gonzalez2015concise`. The constants are `c = (k!)⁻²` and `C = (k!)²`; they are not the paper's
and no attempt is made to match them, since only their existence is claimed. -/
theorem volumeGrowth_comparable (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ T : X →L[ℝ] X,
      c * volumeGrowth T k ≤ ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) ∧
      ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) ≤ C * volumeGrowth T k := by
  have hfac : (1:ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hfacpos : (0:ℝ) < (Nat.factorial k : ℝ) := by linarith
  refine ⟨((Nat.factorial k : ℝ))⁻¹^2, ((Nat.factorial k : ℝ))^2, by positivity, ?_, fun T => ?_⟩
  · rw [inv_pow]
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have h2 : (1:ℝ) ≤ ((Nat.factorial k : ℝ))^2 := by nlinarith [hfac]
    nlinarith [h2]
  refine ⟨?_, ?_⟩
  · -- `D_k ≤ E_k ≤ (k!)² ∏ ρ`
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    calc volumeGrowth T k ≤ detGrowth T k := volumeGrowth_le_detGrowth T k
      _ ≤ ((Nat.factorial k : ℝ))^2 * ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) :=
          detGrowth_le_prod_bernstein T k
  · -- `∏ ρ ≤ k! E_k ≤ (k!)² D_k`
    calc ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1)
        ≤ (Nat.factorial k : ℝ) * detGrowth T k := prod_bernstein_le_detGrowth T k
      _ ≤ (Nat.factorial k : ℝ) * ((Nat.factorial k : ℝ) * volumeGrowth T k) := by
          gcongr
          exact detGrowth_le_factorial_mul_volumeGrowth T k
      _ = ((Nat.factorial k : ℝ))^2 * volumeGrowth T k := by ring

/-- **The Bernstein products are submultiplicative up to a constant.** This is the inequality
`proof_met.tex` l.206--208 quotes from `gonzalez2015concise` (where `ρ_k` is written `F_k`); here
it is a consequence of `volumeGrowth_comparable` and `volumeGrowth_submultiplicative` rather than
a citation. It is what makes `log ∏_{i≤k} ρ_i(𝓛^{(n)}_ω)` a weakly subadditive family, and hence
what puts `χ_k` within reach of Kingman. -/
theorem exists_prod_bernstein_submultiplicative (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : X →L[ℝ] X,
      ∏ i ∈ Finset.range k, bernsteinNumber (S.comp T) (i + 1)
        ≤ K * ((∏ i ∈ Finset.range k, bernsteinNumber S (i + 1)) *
              (∏ i ∈ Finset.range k, bernsteinNumber T (i + 1))) := by
  obtain ⟨c, C, hcpos, hcC, hbound⟩ := volumeGrowth_comparable (X := X) k
  have hCpos : 0 < C := lt_of_lt_of_le hcpos hcC
  refine ⟨C / c ^ 2, div_pos hCpos (by positivity), fun S T => ?_⟩
  have h1 : ∏ i ∈ Finset.range k, bernsteinNumber (S.comp T) (i + 1)
      ≤ C * volumeGrowth (S.comp T) k := (hbound _).2
  have h2 : volumeGrowth (S.comp T) k ≤ volumeGrowth S k * volumeGrowth T k :=
    volumeGrowth_submultiplicative k T S
  have h3 : c * volumeGrowth S k ≤ ∏ i ∈ Finset.range k, bernsteinNumber S (i + 1) :=
    (hbound S).1
  have h4 : c * volumeGrowth T k ≤ ∏ i ∈ Finset.range k, bernsteinNumber T (i + 1) :=
    (hbound T).1
  have hSnn : 0 ≤ volumeGrowth S k := volumeGrowth_nonneg S k
  have hTnn : 0 ≤ volumeGrowth T k := volumeGrowth_nonneg T k
  have hKnn : (0 : ℝ) ≤ C / c ^ 2 := div_nonneg hCpos.le (by positivity)
  have heq : (C / c ^ 2) * ((c * volumeGrowth S k) * (c * volumeGrowth T k))
      = C * (volumeGrowth S k * volumeGrowth T k) := by
    field_simp
  calc ∏ i ∈ Finset.range k, bernsteinNumber (S.comp T) (i + 1)
      ≤ C * volumeGrowth (S.comp T) k := h1
    _ ≤ C * (volumeGrowth S k * volumeGrowth T k) := mul_le_mul_of_nonneg_left h2 hCpos.le
    _ = (C / c ^ 2) * ((c * volumeGrowth S k) * (c * volumeGrowth T k)) := heq.symm
    _ ≤ (C / c ^ 2) * ((∏ i ∈ Finset.range k, bernsteinNumber S (i + 1)) *
            (∏ i ∈ Finset.range k, bernsteinNumber T (i + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hKnn
        exact mul_le_mul h3 h4 (mul_nonneg hcpos.le hTnn)
          (le_trans (mul_nonneg hcpos.le hSnn) h3)

end MultiplicativeErgodic
