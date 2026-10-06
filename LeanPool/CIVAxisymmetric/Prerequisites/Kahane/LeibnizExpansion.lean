/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialOrderShift
public import LeanPool.CIVAxisymmetric.Reduction.MultiPartialFinsetSumLinearity
public import LeanPool.CIVAxisymmetric.Prerequisites.Kahane.Vandermonde
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The multi-index Leibniz rule for `multiPartial`

The single-axis Leibniz rule for iterated `axisDeriv`, its three-axis expansion of
`∂^α (g h)` on a time slice, and the resulting bound
`|∂^α (g h)| ≤ ∑ₘ C(|α|, m) G m H (|α| - m)`. This product estimate carries the factorial
bookkeeping of the nonlinear and pressure terms in the proof of `thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Iterated axis derivatives of a smooth function are smooth. -/
theorem contDiffOn_axisDeriv_iterate {G : Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (j : Fin 3) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((axisDeriv j)^[k] G) s := by
  have h := contDiffOn_foldr_axisDeriv s hs G hG (List.replicate k j)
  rwa [foldr_axisDeriv_replicate] at h

/-- Single-axis Leibniz rule on an open set, indexed by the antidiagonal. -/
theorem axisDeriv_iterate_mul_eqOn_antidiagonal {G H : Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H s) (j : Fin 3) (n : ℕ) :
    Set.EqOn ((axisDeriv j)^[n] (fun y => G y * H y))
      (fun y => ∑ ij ∈ Finset.antidiagonal n,
        (n.choose ij.1 : ℝ) * ((axisDeriv j)^[ij.1] G y * (axisDeriv j)^[ij.2] H y)) s := by
  have hd : ∀ (F : Vec3 → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F s → ∀ k, ∀ y ∈ s,
      HasFDerivAt ((axisDeriv j)^[k] F) (fderiv ℝ ((axisDeriv j)^[k] F) y) y := by
    intro F hF k y hy
    exact (((contDiffOn_axisDeriv_iterate hs hF j k).differentiableOn (by simp)) y hy
      |>.differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  induction n with
  | zero =>
    intro y _
    simp
  | succ n ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    rw [axisDeriv_congr_on s hs _ _ j ih hy]
    have hsum : HasFDerivAt (fun y => ∑ ij ∈ Finset.antidiagonal n,
        (n.choose ij.1 : ℝ) * ((axisDeriv j)^[ij.1] G y * (axisDeriv j)^[ij.2] H y))
        (∑ ij ∈ Finset.antidiagonal n, (n.choose ij.1 : ℝ) •
          ((axisDeriv j)^[ij.1] G y • fderiv ℝ ((axisDeriv j)^[ij.2] H) y +
            (axisDeriv j)^[ij.2] H y • fderiv ℝ ((axisDeriv j)^[ij.1] G) y)) y := by
      apply HasFDerivAt.fun_sum
      intro ij _
      exact ((hd G hG ij.1 y hy).mul (hd H hH ij.2 y hy)).const_mul _
    show fderiv ℝ _ y (basisVec j) = _
    rw [hsum.fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, _root_.add_apply, smul_eq_mul]
    have hG1 : ∀ k, fderiv ℝ ((axisDeriv j)^[k] G) y (basisVec j) = (axisDeriv j)^[k + 1] G y := by
      intro k; rw [Function.iterate_succ_apply']; rfl
    have hH1 : ∀ k, fderiv ℝ ((axisDeriv j)^[k] H) y (basisVec j) = (axisDeriv j)^[k + 1] H y := by
      intro k; rw [Function.iterate_succ_apply']; rfl
    simp only [hG1, hH1]
    rw [Finset.sum_antidiagonal_choose_succ_mul
      (fun a b => (axisDeriv j)^[a] G y * (axisDeriv j)^[b] H y) n]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have hsymm : (n.choose ij.2 : ℝ) = n.choose ij.1 := by
      rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm]
    rw [hsymm]
    ring

/-- Single-axis Leibniz rule on an open set. -/
theorem axisDeriv_iterate_mul_eqOn {G H : Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G s) (hH : ContDiffOn ℝ (⊤ : ℕ∞) H s) (j : Fin 3) (n : ℕ) :
    Set.EqOn ((axisDeriv j)^[n] (fun y => G y * H y))
      (fun y => ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ((axisDeriv j)^[i] G y * (axisDeriv j)^[n - i] H y)) s := by
  intro y hy
  rw [axisDeriv_iterate_mul_eqOn_antidiagonal hs hG hH j n hy]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
    (fun ij => (n.choose ij.1 : ℝ) * ((axisDeriv j)^[ij.1] G y * (axisDeriv j)^[ij.2] H y)) n

/-- Iterated `axisDeriv` respects agreement on an open set. -/
theorem axisDeriv_iterate_congr_on {F F' : Vec3 → ℝ} {s : Set Vec3} (hs : IsOpen s)
    (h : Set.EqOn F F' s) (j : Fin 3) (n : ℕ) :
    Set.EqOn ((axisDeriv j)^[n] F) ((axisDeriv j)^[n] F') s := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ']
    exact axisDeriv_congr_on s hs _ _ j ih

/-- Iterated `axisDeriv` is linear over finite sums of smooth functions on an open set. -/
theorem axisDeriv_iterate_finset_sum_eqOn {ι : Type*} (u : Finset ι) {F : ι → Vec3 → ℝ}
    (c : ι → ℝ) {s : Set Vec3} (hs : IsOpen s) (hF : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (F k) s)
    (j : Fin 3) (n : ℕ) :
    Set.EqOn ((axisDeriv j)^[n] (fun y => ∑ k ∈ u, c k * F k y))
      (fun y => ∑ k ∈ u, c k * (axisDeriv j)^[n] (F k) y) s := by
  induction n with
  | zero => intro y _; rfl
  | succ n ih =>
    intro y hy
    rw [Function.iterate_succ_apply', axisDeriv_congr_on s hs _ _ j ih hy]
    have hsum : HasFDerivAt (fun y => ∑ k ∈ u, c k * (axisDeriv j)^[n] (F k) y)
        (∑ k ∈ u, c k • fderiv ℝ ((axisDeriv j)^[n] (F k)) y) y := by
      apply HasFDerivAt.fun_sum
      intro k _
      exact ((((contDiffOn_axisDeriv_iterate hs (hF k) j n).differentiableOn (by simp)) y hy
        |>.differentiableAt (hs.mem_nhds hy)).hasFDerivAt).const_mul _
    show fderiv ℝ _ y (basisVec j) = _
    rw [hsum.fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Function.iterate_succ_apply']
    rfl

/-- Three-axis Leibniz expansion of `∂^α (g h)` on a time slice. -/
theorem multiPartial_mul_expand {g h : ParabolicPoint → ℝ} {Ω : Set Vec3} (hΩ : IsOpen Ω) (t : ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) Ω) {x : Vec3} (hx : x ∈ Ω)
    (α : Fin 3 → ℕ) :
    multiPartial (fun w => g w * h w) α (x, t) =
      ∑ a ∈ Finset.range (α 0 + 1), ∑ b ∈ Finset.range (α 1 + 1), ∑ c ∈ Finset.range (α 2 + 1),
        ((α 0).choose a * (α 1).choose b * (α 2).choose c : ℝ) *
          (multiPartial g ![a, b, c] (x, t) *
            multiPartial h ![α 0 - a, α 1 - b, α 2 - c] (x, t)) := by
  set G : Vec3 → ℝ := fun y => g (y, t) with hGdef
  set H : Vec3 → ℝ := fun y => h (y, t) with hHdef
  have sm : ∀ (F : Vec3 → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) F Ω → ∀ (j : Fin 3) (k : ℕ),
      ContDiffOn ℝ (⊤ : ℕ∞) ((axisDeriv j)^[k] F) Ω :=
    fun F hF j k => contDiffOn_axisDeriv_iterate hΩ hF j k
  -- the slices of the target terms
  have hmg : ∀ a b c : ℕ, multiPartial g ![a, b, c] (x, t) =
      (axisDeriv 0)^[a] ((axisDeriv 1)^[b] ((axisDeriv 2)^[c] G)) x := by
    intro a b c
    have := congrFun (multiPartial_slice g ![a, b, c] t) x
    simpa using this
  have hmh : ∀ a b c : ℕ, multiPartial h ![a, b, c] (x, t) =
      (axisDeriv 0)^[a] ((axisDeriv 1)^[b] ((axisDeriv 2)^[c] H)) x := by
    intro a b c
    have := congrFun (multiPartial_slice h ![a, b, c] t) x
    simpa using this
  have hlhs : multiPartial (fun w => g w * h w) α (x, t) =
      (axisDeriv 0)^[α 0] ((axisDeriv 1)^[α 1] ((axisDeriv 2)^[α 2] (fun y => G y * H y))) x :=
    congrFun (multiPartial_slice (fun w => g w * h w) α t) x
  set a := α 0
  set b := α 1
  set c := α 2
  -- axis 2
  have e2 := axisDeriv_iterate_mul_eqOn hΩ hg hh 2 c
  -- axis 1
  have e1 : Set.EqOn ((axisDeriv 1)^[b] ((axisDeriv 2)^[c] (fun y => G y * H y)))
      (fun y => ∑ k2 ∈ Finset.range (c + 1), (c.choose k2 : ℝ) *
        ∑ k1 ∈ Finset.range (b + 1), (b.choose k1 : ℝ) *
          ((axisDeriv 1)^[k1] ((axisDeriv 2)^[k2] G) y *
            (axisDeriv 1)^[b - k1] ((axisDeriv 2)^[c - k2] H) y)) Ω := by
    intro y hy
    rw [axisDeriv_iterate_congr_on hΩ e2 1 b hy]
    rw [axisDeriv_iterate_finset_sum_eqOn (Finset.range (c + 1)) (fun k2 => (c.choose k2 : ℝ))
      hΩ (fun k2 => (sm G hg 2 k2).mul (sm H hh 2 (c - k2))) 1 b hy]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    rw [axisDeriv_iterate_mul_eqOn hΩ (sm G hg 2 k2) (sm H hh 2 (c - k2)) 1 b hy]
  -- flatten the double sum
  set u : Finset (ℕ × ℕ) := Finset.range (c + 1) ×ˢ Finset.range (b + 1) with hu
  have e1' : Set.EqOn ((axisDeriv 1)^[b] ((axisDeriv 2)^[c] (fun y => G y * H y)))
      (fun y => ∑ q ∈ u, ((c.choose q.1 : ℝ) * (b.choose q.2 : ℝ)) *
        ((axisDeriv 1)^[q.2] ((axisDeriv 2)^[q.1] G) y *
          (axisDeriv 1)^[b - q.2] ((axisDeriv 2)^[c - q.1] H) y)) Ω := by
    intro y hy
    rw [e1 hy, hu]
    dsimp only
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    ring
  -- axis 0
  have e0 : (axisDeriv 0)^[a] ((axisDeriv 1)^[b] ((axisDeriv 2)^[c] (fun y => G y * H y))) x =
      ∑ q ∈ u, ((c.choose q.1 : ℝ) * (b.choose q.2 : ℝ)) *
        ∑ k0 ∈ Finset.range (a + 1), (a.choose k0 : ℝ) *
          ((axisDeriv 0)^[k0] ((axisDeriv 1)^[q.2] ((axisDeriv 2)^[q.1] G)) x *
            (axisDeriv 0)^[a - k0] ((axisDeriv 1)^[b - q.2] ((axisDeriv 2)^[c - q.1] H)) x) := by
    rw [axisDeriv_iterate_congr_on hΩ e1' 0 a hx]
    rw [axisDeriv_iterate_finset_sum_eqOn u _ hΩ
      (fun q => (sm _ (sm G hg 2 q.1) 1 q.2).mul (sm _ (sm H hh 2 (c - q.1)) 1 (b - q.2))) 0 a hx]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [axisDeriv_iterate_mul_eqOn hΩ (sm _ (sm G hg 2 q.1) 1 q.2)
      (sm _ (sm H hh 2 (c - q.1)) 1 (b - q.2)) 0 a hx]
  rw [hlhs, e0, hu, Finset.sum_product]
  simp_rw [hmg, hmh, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k2 _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k0 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => ?_
  ring

/-- The multi-index Leibniz bound: with bounds `G m`, `H m` on the derivatives of order `m ≤ |α|`,
`|∂^α (g h)| ≤ ∑ₘ C(|α|, m) G m H (|α| - m)`. -/
theorem abs_multiPartial_mul_le {g h : ParabolicPoint → ℝ} {Ω : Set Vec3} (hΩ : IsOpen Ω)
    (t : ℝ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) Ω)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => h (x, t)) Ω) {x : Vec3} (hx : x ∈ Ω)
    (α : Fin 3 → ℕ) (G H : ℕ → ℝ)
    (hG : ∀ γ : Fin 3 → ℕ, (∀ i, γ i ≤ α i) → |multiPartial g γ (x, t)| ≤ G (γ 0 + γ 1 + γ 2))
    (hH : ∀ γ : Fin 3 → ℕ, (∀ i, γ i ≤ α i) → |multiPartial h γ (x, t)| ≤ H (γ 0 + γ 1 + γ 2)) :
    |multiPartial (fun w => g w * h w) α (x, t)| ≤
      ∑ m ∈ Finset.range (α 0 + α 1 + α 2 + 1),
        ((α 0 + α 1 + α 2).choose m : ℝ) * (G m * H (α 0 + α 1 + α 2 - m)) := by
  rw [multiPartial_mul_expand hΩ t hg hh hx α]
  have hcol := sum_choose_mul_choose_mul_choose_collapse (α 0) (α 1) (α 2)
    (fun m => G m * H (α 0 + α 1 + α 2 - m))
  push_cast at hcol
  rw [← hcol]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c hc => ?_)
  rw [Finset.mem_range] at ha hb hc
  have hγ := hG ![a, b, c] (fun i => by fin_cases i <;> simp <;> omega)
  have hη := hH ![α 0 - a, α 1 - b, α 2 - c] (fun i => by fin_cases i <;> simp)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hγ hη
  have hsum : α 0 - a + (α 1 - b) + (α 2 - c) = α 0 + α 1 + α 2 - (a + b + c) := by omega
  rw [hsum] at hη
  have hG0 : 0 ≤ G (a + b + c) := (abs_nonneg _).trans hγ
  rw [abs_mul (((α 0).choose a * (α 1).choose b * (α 2).choose c : ℝ)),
    abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((α 0).choose a * (α 1).choose b * (α 2).choose c : ℝ)), abs_mul]
  gcongr

end CIV
