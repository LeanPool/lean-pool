/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AnalyticOfBounds
public import LeanPool.CIVAxisymmetric.Reduction.AxisDeriv
public import LeanPool.CIVAxisymmetric.Reduction.IteratedFDerivTuples
public import LeanPool.CIVAxisymmetric.Reduction.AxisDerivSymm
public import LeanPool.CIVAxisymmetric.Statements.LocallyUniformlyAnalyticOn

/-! ### From multilinear map norm to sum over basis evaluations -/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV



/-- The operator norm of a continuous multilinear map on `Vec3` is bounded by the sum of the
absolute values of its evaluations on the coordinate-basis tuples. This is the elementary
estimate that turns the factorial bound on `multiPartial`, `eq:analytic:interior:velocity`, into
a factorial bound on the operator norm of `iteratedFDeriv`, as used in `thm:analytic:interior`. -/
theorem norm_le_sum_abs_apply_basis {n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec3) ℝ) :
    ‖A‖ ≤ ∑ v : Fin n → Fin 3, |A (fun i => basisVec (v i))| := by
  classical
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun m => ?_
  have hm : m = fun i => ∑ j : Fin 3, m i j • basisVec j :=
    funext fun i => (sum_smul_basisVec (m i)).symm
  have hsum : A m = ∑ v : Fin n → Fin 3, A (fun i => m i (v i) • basisVec (v i)) := by
    conv_lhs => rw [hm]
    have hmap := A.toMultilinearMap.map_sum (g := fun i (j : Fin 3) => m i j • basisVec j)
    simpa only [ContinuousMultilinearMap.coe_coe] using hmap
  have hstep : ∀ v : Fin n → Fin 3,
      A (fun i => m i (v i) • basisVec (v i))
        = (∏ i : Fin n, m i (v i)) • A (fun i => basisVec (v i)) := by
    intro v
    have hmap := A.toMultilinearMap.map_smul_univ (fun i => m i (v i)) (fun i => basisVec (v i))
    simpa only [ContinuousMultilinearMap.coe_coe] using hmap
  rw [hsum, Real.norm_eq_abs]
  calc
    |∑ v : Fin n → Fin 3, A (fun i => m i (v i) • basisVec (v i))|
        ≤ ∑ v : Fin n → Fin 3, |A (fun i => m i (v i) • basisVec (v i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v : Fin n → Fin 3, |∏ i : Fin n, m i (v i)| * |A (fun i => basisVec (v i))| := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hstep v, smul_eq_mul, abs_mul]
    _ ≤ ∑ v : Fin n → Fin 3, (∏ i : Fin n, ‖m i‖) * |A (fun i => basisVec (v i))| := by
        refine Finset.sum_le_sum fun v _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        rw [Finset.abs_prod]
        gcongr with i hi
        exact norm_le_pi_norm (m i) (v i)
    _ = (∏ i : Fin n, ‖m i‖) * ∑ v : Fin n → Fin 3, |A (fun i => basisVec (v i))| := by
        rw [← Finset.mul_sum]
    _ = (∑ v : Fin n → Fin 3, |A (fun i => basisVec (v i))|) * ∏ i : Fin n, ‖m i‖ :=
        mul_comm _ _

/-! ### Factorial bounds on iterated derivatives from the multi-index bound -/

/-- Folding `axisDeriv j` over a list of `k` copies of the same direction `j` agrees with
iterating `axisDeriv j` itself `k` times. -/
theorem foldr_axisDeriv_replicate (j : Fin 3) (k : ℕ) (G : Vec3 → ℝ) :
    List.foldr axisDeriv G (List.replicate k j) = (axisDeriv j)^[k] G := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

/-- **Factorial bound on the iterated Fréchet derivative of a slice component.** The
multi-index bound `AnalyticBoundOn`, `eq:analytic:interior:force`, controls every iterated
`axisDeriv` composition; summing over the `3^n` coordinate-basis tuples of
`norm_le_sum_abs_apply_basis` turns this into the factorial bound on `iteratedFDeriv` that
`analyticOnNhd_vec3Ball_of_iteratedFDeriv_bound` consumes for `thm:analytic:interior`. -/
theorem norm_iteratedFDeriv_le_of_analyticBoundOn {g : ParabolicPoint → Vec3} {R' M a t : ℝ}
    {J : Set ℝ} (ht : t ∈ J) (ha : 0 < a) (i : Fin 3)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t) i) (vec3Ball 0 R'))
    (hb : AnalyticBoundOn g R' J M a) :
    ∀ n : ℕ, ∀ x ∈ vec3Ball 0 R',
      ‖iteratedFDeriv ℝ n (fun y : Vec3 => g (y, t) i) x‖ ≤ M * (3 / a) ^ n * (Nat.factorial n)
        := by
  classical
  intro n x hx
  set G : Vec3 → ℝ := fun y : Vec3 => g (y, t) i with hGdef
  have hterm : ∀ v : Fin n → Fin 3,
      |iteratedFDeriv ℝ n G x (fun j => basisVec (v j))|
        ≤ M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n) := by
    intro v
    set α : Fin 3 → ℕ := fun j => (List.ofFn v).count j with hαdef
    have hperm : (List.ofFn v).Perm
        (List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
          ++ List.replicate (α 2) (2 : Fin 3)) := by
      rw [List.perm_iff_count]
      intro c
      fin_cases c <;> simp [hαdef, List.count_append, List.count_replicate]
    have hlen : α 0 + α 1 + α 2 = n := by
      have h1 : (List.ofFn v).length =
          (List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
            ++ List.replicate (α 2) (2 : Fin 3)).length := hperm.length_eq
      simp only [List.length_append, List.length_replicate, List.length_ofFn] at h1
      omega
    have heq1 : iteratedFDeriv ℝ n G x (fun j => basisVec (v j))
        = List.foldr axisDeriv G (List.ofFn v) x :=
      eqOn_iteratedFDeriv_basis (vec3Ball 0 R') (isOpen_vec3Ball 0 R') G hsmooth n v hx
    have heq2 : List.foldr axisDeriv G (List.ofFn v) x
        = List.foldr axisDeriv G
            (List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
              ++ List.replicate (α 2) (2 : Fin 3)) x :=
      eqOn_foldr_axisDeriv_of_perm (vec3Ball 0 R') (isOpen_vec3Ball 0 R') G hsmooth hperm hx
    have heq3 : List.foldr axisDeriv G
          (List.replicate (α 0) (0 : Fin 3) ++ List.replicate (α 1) (1 : Fin 3)
            ++ List.replicate (α 2) (2 : Fin 3)) x
        = (axisDeriv 0)^[α 0] ((axisDeriv 1)^[α 1] ((axisDeriv 2)^[α 2] G)) x := by
      simp only [List.foldr_append, foldr_axisDeriv_replicate]
    have heq4 : (axisDeriv 0)^[α 0] ((axisDeriv 1)^[α 1] ((axisDeriv 2)^[α 2] G)) x
        = multiPartial (fun w => g w i) α (x, t) :=
      congrFun (multiPartial_slice (fun w => g w i) α t).symm x
    have heq0 : iteratedFDeriv ℝ n G x (fun j => basisVec (v j))
        = multiPartial (fun w => g w i) α (x, t) :=
      heq1.trans (heq2.trans (heq3.trans heq4))
    have hbound := hb α t ht x hx i
    have hconv : M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * (Nat.factorial (α 0 + α 1 + α 2))
        = M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n) := by
      rw [hlen]
    calc
      |iteratedFDeriv ℝ n G x (fun j => basisVec (v j))|
          = |multiPartial (fun w => g w i) α (x, t)| := congrArg abs heq0
      _ ≤ M * a ^ (-((α 0 + α 1 + α 2 : ℕ) : ℝ)) * (Nat.factorial (α 0 + α 1 + α 2)) := hbound
      _ = M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n) := hconv
  have hop : ‖iteratedFDeriv ℝ n G x‖ ≤ ∑ v : Fin n → Fin 3,
      |iteratedFDeriv ℝ n G x (fun j => basisVec (v j))| :=
    norm_le_sum_abs_apply_basis (iteratedFDeriv ℝ n G x)
  have hcard : (Finset.univ : Finset (Fin n → Fin 3)).card = 3 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp
  have hsum : (∑ v : Fin n → Fin 3, M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n))
      = (3 : ℝ) ^ n * (M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n)) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    norm_cast
  have hpow : (3 : ℝ) ^ n * a ^ (-((n : ℕ) : ℝ)) = (3 / a) ^ n := by
    rw [Real.rpow_neg ha.le, Real.rpow_natCast, ← div_eq_mul_inv, div_pow]
  calc
    ‖iteratedFDeriv ℝ n G x‖
        ≤ ∑ v : Fin n → Fin 3, |iteratedFDeriv ℝ n G x (fun j => basisVec (v j))| := hop
    _ ≤ ∑ v : Fin n → Fin 3, M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n) :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = (3 : ℝ) ^ n * (M * a ^ (-((n : ℕ) : ℝ)) * (Nat.factorial n)) := hsum
    _ = M * ((3 : ℝ) ^ n * a ^ (-((n : ℕ) : ℝ))) * (Nat.factorial n) := by ring
    _ = M * (3 / a) ^ n * (Nat.factorial n) := by rw [hpow]

/-! ### Analyticity of a time slice from locally uniform bounds -/

/-- **Spatial analyticity of a time slice from local uniform bounds.** This combines the
factorial bound `norm_iteratedFDeriv_le_of_analyticBoundOn` with the analyticity criterion
`analyticOnNhd_vec3Ball_of_iteratedFDeriv_bound` to conclude `thm:analytic:interior`: every
Cartesian component of a locally uniformly analytic field, at a fixed time in `(t₁, t₂)`, is
real analytic on the spatial ball `B(R)`. -/
theorem analyticOnNhd_slice_of_locallyUniformlyAnalyticOn {g : ParabolicPoint → Vec3}
    {R t₁ t₂ : ℝ}
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z)
      (spaceTimeSet (vec3Ball 0 R) (Ioo t₁ t₂)))
    (hg : LocallyUniformlyAnalyticOn g R t₁ t₂) :
    ∀ t ∈ Ioo t₁ t₂, ∀ i : Fin 3, AnalyticOnNhd ℝ (fun x : Vec3 => g (x, t) i) (vec3Ball 0 R) := by
  intro t ht i
  have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t) i) (vec3Ball 0 R) :=
    contDiffOn_slice_component ht hsmooth i
  refine analyticOnNhd_vec3Ball_of_iteratedFDeriv_bound hslice fun R' hR' => ?_
  have hs1 : t₁ < (t₁ + t) / 2 := by linarith only [ht.1]
  have hs2 : (t + t₂) / 2 < t₂ := by linarith only [ht.2]
  obtain ⟨M, a, ha, hb⟩ := hg R' hR' ((t₁ + t) / 2) ((t + t₂) / 2) hs1 hs2
  refine ⟨M, 3 / a, div_pos (by norm_num) ha, fun n x hx => ?_⟩
  have htJ : t ∈ Icc ((t₁ + t) / 2) ((t + t₂) / 2) :=
    ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
  have hslice' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t) i) (vec3Ball 0 R') :=
    hslice.mono (vec3Ball_mono hR'.le)
  exact norm_iteratedFDeriv_le_of_analyticBoundOn htJ ha i hslice' hb n x hx

end CIV
