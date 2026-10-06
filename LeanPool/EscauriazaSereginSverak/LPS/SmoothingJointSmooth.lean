/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Joint smoothness from continuous partial derivatives

`lem:lps-Bochner-joint-smooth`: a family of functions on `ℝ³ × [a,b]` closed under
the spatial derivatives and the time derivative, all jointly continuous, is
`C^∞` on the closed slab, with one-sided time derivatives at the endpoints.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The candidate Fréchet derivative of `w j α` on the slab: coordinate
derivatives in space and the time derivative. -/
@[expose] def lpsSlabDeriv (w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ) (j : ℕ) (α : List (Fin 3))
    (z : Vec3 × ℝ) : Vec3 × ℝ →L[ℝ] ℝ :=
  (∑ i : Fin 3, w j (α ++ [i]) z •
      ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ Vec3 ℝ))) +
    w (j + 1) α z • ContinuousLinearMap.snd ℝ Vec3 ℝ

theorem lpsSlabDeriv_continuousOn {w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hc : ∀ j α, ContinuousOn (w j α) S) (j : ℕ) (α : List (Fin 3)) :
    ContinuousOn (lpsSlabDeriv w j α) S := by
  unfold lpsSlabDeriv
  refine ContinuousOn.add (continuousOn_finsetSum _ fun i _ => ?_) ?_
  · exact (hc _ _).smul continuousOn_const
  · exact (hc _ _).smul continuousOn_const

theorem lpsSlabDeriv_contDiffOn {w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    {n : ℕ} (hc : ∀ j α, ContDiffOn ℝ n (w j α) S) (j : ℕ) (α : List (Fin 3)) :
    ContDiffOn ℝ n (lpsSlabDeriv w j α) S := by
  unfold lpsSlabDeriv
  refine ContDiffOn.add (ContDiffOn.sum fun i _ => ?_) ?_
  · exact (hc _ _).smul contDiffOn_const
  · exact (hc _ _).smul contDiffOn_const

/-- Fréchet differentiability at interior points of the slab from the continuous
partial derivatives. -/
theorem lps_slab_hasFDerivAt {a b : ℝ} {w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ}
    (hc : ∀ j α, ContinuousOn (w j α) ((univ : Set Vec3) ×ˢ Icc a b))
    (hx : ∀ j α, ∀ t ∈ Icc a b, ∀ x : Vec3,
      HasFDerivAt (fun y => w j α (y, t))
        (∑ i : Fin 3, w j (α ++ [i]) (x, t) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) x)
    (ht : ∀ j α, ∀ x : Vec3, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => w j α (x, s)) (w (j + 1) α (x, t)) (Icc a b) t)
    (j : ℕ) (α : List (Fin 3)) {z : Vec3 × ℝ} (hz : z ∈ (univ : Set Vec3) ×ˢ Ioo a b) :
    HasFDerivAt (w j α) (lpsSlabDeriv w j α z) z := by
  have hU : IsOpen ((univ : Set Vec3) ×ˢ Ioo a b) := isOpen_univ.prod isOpen_Ioo
  have hUS : (univ : Set Vec3) ×ˢ Ioo a b ⊆ (univ : Set Vec3) ×ˢ Icc a b :=
    prod_mono subset_rfl Ioo_subset_Icc_self
  have hnhds : (univ : Set Vec3) ×ˢ Ioo a b ∈ 𝓝 z := hU.mem_nhds hz
  let f : Vec3 → ℝ → ℝ := fun x t => w j α (x, t)
  let f₁ : Vec3 → ℝ → Vec3 →L[ℝ] ℝ := fun x t =>
    ∑ i : Fin 3, w j (α ++ [i]) (x, t) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  let f₂ : Vec3 → ℝ → ℝ →L[ℝ] ℝ := fun x t =>
    w (j + 1) α (x, t) • (1 : ℝ →L[ℝ] ℝ)
  have df₁ : ∀ᶠ v in 𝓝 z, HasFDerivAt (f · v.2) (↿f₁ v) v.1 := by
    filter_upwards [hnhds] with v hv
    exact hx j α v.2 (Ioo_subset_Icc_self hv.2) v.1
  have df₂ : ∀ᶠ v in 𝓝 z, HasFDerivAt (f v.1 ·) (↿f₂ v) v.2 := by
    filter_upwards [hnhds] with v hv
    have hd := (ht j α v.1 v.2 (Ioo_subset_Icc_self hv.2))
    have hd' : HasDerivAt (fun s => w j α (v.1, s)) (w (j + 1) α (v.1, v.2)) v.2 :=
      hd.hasDerivAt (Icc_mem_nhds hv.2.1 hv.2.2)
    refine hd'.hasFDerivAt.congr_fderiv ?_
    have hu : (↿f₂ v) = w (j + 1) α v • (1 : ℝ →L[ℝ] ℝ) := rfl
    rw [hu]
    exact ContinuousLinearMap.ext fun r => by simp [mul_comm]
  have cont : ∀ (k : ℕ) (β : List (Fin 3)), ContinuousAt (w k β) z := fun k β =>
    (hc k β).continuousAt (mem_of_superset hnhds hUS)
  have cf₁ : ContinuousAt ↿f₁ z := by
    have : ContinuousOn (fun v : Vec3 × ℝ => ∑ i : Fin 3, w j (α ++ [i]) v •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) ((univ : Set Vec3) ×ˢ Icc a b) :=
      continuousOn_finsetSum _ fun i _ => (hc j (α ++ [i])).smul continuousOn_const
    exact this.continuousAt (mem_of_superset hnhds hUS)
  have cf₂ : ContinuousAt ↿f₂ z :=
    (cont (j + 1) α).smul continuousAt_const
  have hs := hasStrictFDerivAt_uncurry_coprod (f := f) (f₁ := f₁) (f₂ := f₂) df₁ df₂ cf₁ cf₂
  have hEq : (↿f₁ z).coprod (↿f₂ z) = lpsSlabDeriv w j α z := by
    have hu₁ : (↿f₁ z) = ∑ i : Fin 3, w j (α ++ [i]) z •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ) := rfl
    have hu₂ : (↿f₂ z) = w (j + 1) α z • (1 : ℝ →L[ℝ] ℝ) := rfl
    rw [hu₁, hu₂]
    ext v
    · simp [lpsSlabDeriv, sum_apply]
    · simp [lpsSlabDeriv]
  rw [hEq] at hs
  exact hs.hasFDerivAt

/-- Fréchet differentiability within the closed slab, including the endpoints. -/
theorem lps_slab_hasFDerivWithinAt {a b : ℝ} (hab : a < b)
    {w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ}
    (hc : ∀ j α, ContinuousOn (w j α) ((univ : Set Vec3) ×ˢ Icc a b))
    (hx : ∀ j α, ∀ t ∈ Icc a b, ∀ x : Vec3,
      HasFDerivAt (fun y => w j α (y, t))
        (∑ i : Fin 3, w j (α ++ [i]) (x, t) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) x)
    (ht : ∀ j α, ∀ x : Vec3, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => w j α (x, s)) (w (j + 1) α (x, t)) (Icc a b) t)
    (j : ℕ) (α : List (Fin 3)) {z : Vec3 × ℝ} (hz : z ∈ (univ : Set Vec3) ×ˢ Icc a b) :
    HasFDerivWithinAt (w j α) (lpsSlabDeriv w j α z) ((univ : Set Vec3) ×ˢ Icc a b) z := by
  set U : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioo a b with hU
  have hUo : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hUc : Convex ℝ U := (convex_univ).prod (convex_Ioo a b)
  have hcl : closure U = (univ : Set Vec3) ×ˢ Icc a b := by
    rw [hU, closure_prod_eq, closure_univ, closure_Ioo hab.ne]
  have hUS : U ⊆ (univ : Set Vec3) ×ˢ Icc a b := prod_mono subset_rfl Ioo_subset_Icc_self
  have hint : ∀ y ∈ U, HasFDerivAt (w j α) (lpsSlabDeriv w j α y) y := fun y hy =>
    lps_slab_hasFDerivAt hc hx ht j α hy
  have hdiff : DifferentiableOn ℝ (w j α) U := fun y hy => (hint y
    hy).differentiableAt.differentiableWithinAt
  have hcont : ∀ y ∈ closure U, ContinuousWithinAt (w j α) U y := by
    intro y hy
    rw [hcl] at hy
    exact (hc j α y hy).mono hUS
  have hlim : Tendsto (fun y => fderiv ℝ (w j α) y) (𝓝[U] z) (𝓝 (lpsSlabDeriv w j α z)) := by
    have h1 : Tendsto (lpsSlabDeriv w j α) (𝓝[U] z) (𝓝 (lpsSlabDeriv w j α z)) :=
      ((lpsSlabDeriv_continuousOn hc j α) z hz).mono hUS
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hint y hy).fderiv.symm
  have := hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hUc hUo hcont hlim
  rwa [hcl] at this

/-- Joint smoothness on the closed slab from continuous partial derivatives of all
orders (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_slab_contDiffOn {a b : ℝ} (hab : a < b)
    {w : ℕ → List (Fin 3) → Vec3 × ℝ → ℝ}
    (hc : ∀ j α, ContinuousOn (w j α) ((univ : Set Vec3) ×ˢ Icc a b))
    (hx : ∀ j α, ∀ t ∈ Icc a b, ∀ x : Vec3,
      HasFDerivAt (fun y => w j α (y, t))
        (∑ i : Fin 3, w j (α ++ [i]) (x, t) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) x)
    (ht : ∀ j α, ∀ x : Vec3, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s => w j α (x, s)) (w (j + 1) α (x, t)) (Icc a b) t)
    (j : ℕ) (α : List (Fin 3)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (w j α) ((univ : Set Vec3) ×ˢ Icc a b) := by
  have huniq : UniqueDiffOn ℝ ((univ : Set Vec3) ×ˢ Icc a b) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Icc hab)
  have hn : ∀ n : ℕ, ∀ j α, ContDiffOn ℝ n (w j α) ((univ : Set Vec3) ×ˢ Icc a b) := by
    intro n
    induction n with
    | zero => exact fun j α => contDiffOn_zero.mpr (hc j α)
    | succ n ih =>
        intro j α
        rw [Nat.cast_succ]
        refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn huniq).mpr
          ⟨fun h => absurd h (by simp), lpsSlabDeriv w j α, lpsSlabDeriv_contDiffOn ih j α, ?_⟩
        intro z hz
        exact lps_slab_hasFDerivWithinAt hab hc hx ht j α hz
  exact contDiffOn_infty.mpr fun n => hn n j α

end ESS
