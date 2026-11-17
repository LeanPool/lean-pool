/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Data.Fintype.Perm

/-!
# Rank-one bounds and symmetrization of real multilinear maps

The symmetrization `S_q` of a real `q`-linear map on a real inner product space (the average over
all permutations of its arguments, Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2) and the
pairing `appendInner` of a vector-valued `d`-linear map with a last vector argument, which places
the original index after the `d` Taylor indices as in BKL Lemma 3.6. The counting identity
`sum_perm_inner_init_last` evaluates `S_{d+1}` of such a pairing when the `d`-linear map is
symmetric.
-/

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one moment product is bounded by the product of the argument norms. -/
theorem norm_prod_inner_le (d : ℕ) (h : Fin d → E) (x : E) :
    ‖∏ j, ⟪x, h j⟫‖ ≤ ‖x‖ ^ d * ∏ j, ‖h j‖ := by
  rw [norm_prod]
  calc
    ∏ j, ‖⟪x, h j⟫‖ ≤ ∏ j, ‖x‖ * ‖h j‖ := by
      apply Finset.prod_le_prod₀
      · intro j _; exact norm_nonneg _
      · intro j _; exact norm_inner_le_norm _ _
    _ = ‖x‖ ^ d * ∏ j, ‖h j‖ := by rw [Finset.prod_mul_distrib]; simp


/-- The symmetrization `S_q` of a `q`-linear map with values in a real normed space: the average of
`Φ (h ∘ σ)` over all permutations `σ` of the `q` arguments (BKL Section 2; for a tensor-valued map
the values carry the trailing indices, which are not permuted). -/
def symmetrizeML {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ}
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F :=
  ((q.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin q), Φ.domDomCongr σ

/-- For a tensor `Ψ` with `d` Taylor indices and one original vector index (BKL places the Taylor
indices first), the real `(d+1)`-linear map `h ↦ ⟪Ψ (h₀, …, h_{d-1}), h_d⟫`. -/
def appendInner {d : ℕ} (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (d + 1) => E) ℝ :=
  ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).compContinuousMultilinearMap Ψ).uncurryRight


private lemma card_perm_fiber_eq_card_subtype {d : ℕ} (j : Fin (d + 1)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) =>
      σ (Fin.last d) = j).card =
      Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} := by
  classical
  let s : Finset (Equiv.Perm (Fin (d + 1))) :=
    Finset.univ.filter fun σ => σ (Fin.last d) = j
  let e : (↥s) ≃ {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} :=
    { toFun := fun σ =>
        ⟨σ.1, (Finset.mem_filter.mp σ.2).2⟩
      invFun := fun σ =>
        ⟨σ.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.2⟩⟩
      left_inv := by
        intro σ
        rfl
      right_inv := by
        intro σ
        rfl }
  change s.card = _
  calc
    s.card = Fintype.card ↥s := (Fintype.card_coe s).symm
    _ = Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} :=
      Fintype.card_congr e

private lemma card_perm_fiber_eq_card_perm_fiber {d : ℕ}
    (j j' : Fin (d + 1)) :
    Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} =
      Fintype.card {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j'} := by
  let e :
      {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j} ≃
        {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j'} :=
    { toFun := fun σ =>
        ⟨Equiv.swap j j' * σ.1, by
          simp [Equiv.Perm.mul_apply, σ.2]⟩
      invFun := fun σ =>
        ⟨Equiv.swap j j' * σ.1, by
          simp [Equiv.Perm.mul_apply, σ.2]⟩
      left_inv := by
        intro σ
        simp [Equiv.swap_mul_self_mul]
      right_inv := by
        intro σ
        simp [Equiv.swap_mul_self_mul] }
  exact Fintype.card_congr e

/-- Each value of `σ (last d)` is taken by exactly `d!` permutations of `Fin (d + 1)`. -/
theorem card_filter_perm_apply_last_eq {d : ℕ} (k : Fin (d + 1)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d) = k).card =
      d.factorial := by
    classical
    let β : Fin (d + 1) → Type :=
      fun j => {σ : Equiv.Perm (Fin (d + 1)) // σ (Fin.last d) = j}
    let e :
        Equiv.Perm (Fin (d + 1)) ≃ Σ j : Fin (d + 1), β j :=
      { toFun := fun σ => ⟨σ (Fin.last d), ⟨σ, rfl⟩⟩
        invFun := fun σ => σ.2.1
        left_inv := by
          intro σ
          rfl
        right_inv := by
          rintro ⟨j, ⟨σ, hσ⟩⟩
          cases hσ
          rfl }
    have hsum :
        ∑ j : Fin (d + 1), Fintype.card (β j) =
          (d + 1).factorial := by
      calc
        ∑ j : Fin (d + 1), Fintype.card (β j) =
            Fintype.card (Σ j : Fin (d + 1), β j) := by
              rw [Fintype.card_sigma]
        _ = Fintype.card (Equiv.Perm (Fin (d + 1))) :=
          Fintype.card_congr e.symm
        _ = (d + 1).factorial := by
          simp [Fintype.card_perm, Fintype.card_fin]
    have hconst :
        ∀ j : Fin (d + 1), Fintype.card (β j) =
          Fintype.card (β (Fin.last d)) := by
      intro j
      exact card_perm_fiber_eq_card_perm_fiber j (Fin.last d)
    have hmul :
        (d + 1) * Fintype.card (β (Fin.last d)) =
          (d + 1).factorial := by
      simpa [hconst] using hsum
    rw [Nat.factorial_succ] at hmul
    have hmulK :
        (d + 1) * Fintype.card (β k) =
          (d + 1) * d.factorial := by
      rw [hconst k]
      exact hmul
    rw [show
        (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) =>
          σ (Fin.last d) = k).card =
          Fintype.card (β k) from card_perm_fiber_eq_card_subtype k]
    exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ d) hmulK

/-- If `σ (last d) = k`, the first `d` entries of `h ∘ σ` are a permutation of `h` without `h k`. -/
theorem exists_perm_init_comp_eq {α : Type*} {d : ℕ} (h : Fin (d + 1) → α)
    (σ : Equiv.Perm (Fin (d + 1))) {k : Fin (d + 1)} (hk : σ (Fin.last d) = k) :
    ∃ τ : Equiv.Perm (Fin d), Fin.init (h ∘ σ) = k.removeNth h ∘ τ := by
    have hne : ∀ i : Fin d, σ (Fin.castSucc i) ≠ k := by
      intro i hi
      have heq : σ (Fin.castSucc i) = σ (Fin.last d) := hi.trans hk.symm
      exact (Fin.castSucc_ne_last i) (σ.injective heq)
    let f : Fin d → Fin d := fun i =>
      Classical.choose (Fin.exists_succAbove_eq (hne i))
    have hf : ∀ i : Fin d, k.succAbove (f i) = σ (Fin.castSucc i) := by
      intro i
      dsimp [f]
      exact Classical.choose_spec (Fin.exists_succAbove_eq (hne i))
    have hinj : Function.Injective f := by
      intro i j hij
      apply Fin.castSucc_injective
      apply σ.injective
      calc
        σ (Fin.castSucc i) = k.succAbove (f i) := (hf i).symm
        _ = k.succAbove (f j) := congrArg (k.succAbove) hij
        _ = σ (Fin.castSucc j) := hf j
    have hbij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp⟩
    let τ : Equiv.Perm (Fin d) := Equiv.ofBijective f hbij
    refine ⟨τ, ?_⟩
    funext i
    change h (σ (Fin.castSucc i)) = h (k.succAbove (f i))
    exact (congrArg h (hf i)).symm

/-- Symmetrizing `⟪Φ (h₀, …, h_{d-1}), h_d⟫` for a symmetric `Φ`: the sum over permutations is
`d!` times the sum over the position of the last argument. -/
theorem sum_perm_inner_init_last {d : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E)
    (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (v : Fin d → E), Φ (v ∘ τ) = Φ v) (h : Fin (d + 1) → E) :
    ∑ σ : Equiv.Perm (Fin (d + 1)), ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫ =
      (d.factorial : ℝ) * ∑ k : Fin (d + 1), ⟪Φ (k.removeNth h), h k⟫ := by
    let F : Equiv.Perm (Fin (d + 1)) → ℝ :=
      fun σ => ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫
    change Finset.sum Finset.univ F =
      (d.factorial : ℝ) *
        Finset.sum Finset.univ (fun k : Fin (d + 1) =>
          ⟪Φ (k.removeNth h), h k⟫)
    calc
      Finset.sum Finset.univ F =
          Finset.sum Finset.univ (fun k : Fin (d + 1) =>
            Finset.sum
              (Finset.univ.filter
                (fun σ : Equiv.Perm (Fin (d + 1)) =>
                  σ (Fin.last d) = k))
              F) := by
        simpa using
          (Finset.sum_fiberwise Finset.univ
            (fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d)) F).symm
      _ = Finset.sum Finset.univ (fun k : Fin (d + 1) =>
            (d.factorial : ℝ) * ⟪Φ (k.removeNth h), h k⟫) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          Finset.sum
              (Finset.univ.filter
                (fun σ : Equiv.Perm (Fin (d + 1)) =>
                  σ (Fin.last d) = k))
              F =
              Finset.sum
                (Finset.univ.filter
                  (fun σ : Equiv.Perm (Fin (d + 1)) =>
                    σ (Fin.last d) = k))
                (fun _ => ⟪Φ (k.removeNth h), h k⟫) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            have hkσ : σ (Fin.last d) = k :=
              (Finset.mem_filter.mp hσ).2
            obtain ⟨τ, hτ⟩ :=
              exists_perm_init_comp_eq h σ hkσ
            have hΦσ :
                Φ (Fin.init (h ∘ σ)) = Φ (k.removeNth h) := by
              calc
                Φ (Fin.init (h ∘ σ)) =
                    Φ (k.removeNth h ∘ τ) := by rw [hτ]
                _ = Φ (k.removeNth h) := hΦ τ _
            dsimp [F]
            rw [hΦσ, hkσ]
          _ =
              ((Finset.univ.filter
                  (fun σ : Equiv.Perm (Fin (d + 1)) =>
                    σ (Fin.last d) = k)).card : ℝ) *
                ⟪Φ (k.removeNth h), h k⟫ := by
            simp [nsmul_eq_mul]
          _ = (d.factorial : ℝ) * ⟪Φ (k.removeNth h), h k⟫ := by
            rw [card_filter_perm_apply_last_eq]
      _ = (d.factorial : ℝ) *
          Finset.sum Finset.univ (fun k : Fin (d + 1) =>
            ⟪Φ (k.removeNth h), h k⟫) := by
        rw [Finset.mul_sum]

/-- Continuous linear maps commute with the symmetrization. -/
theorem clm_comp_symmetrizeML {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {q : ℕ}
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) G) (L : G →L[ℝ] H) :
    L.compContinuousMultilinearMap (symmetrizeML Φ) =
      symmetrizeML (L.compContinuousMultilinearMap Φ) := by
  ext h
  simp [symmetrizeML, map_smul, map_sum, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    ContinuousMultilinearMap.domDomCongr_apply]

end FunctionalInequalities.Analysis.Tensor
