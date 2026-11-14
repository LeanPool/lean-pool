/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import LeanPool.RoyStrongSix.Roy.BaseChange

/-!
# Realizing a rational subquotient in coordinates

Given `F`-subspaces `A_S ≤ A_T` of `F`-points of `ℂⁿ`, we construct `k` and a `ℂ`-linear map
`ψ : ℂⁿ → ℂᵏ` such that
* `ψ` sends `F`-points to `F`-points;
* `ψ (A_T) = Fpts F k`, hence `ψ (span_ℂ A_T) = ℂᵏ`;
* `ker ψ ⊓ span_ℂ A_T = span_ℂ A_S`;
* `k + dim_F A_S = dim_F A_T`.

So `ψ` realizes the subquotient `span A_T / span A_S` as `ℂᵏ`, compatibly with the `F`-structures.
The construction uses an `F`-basis adapted to the flag `A_S ≤ A_T ≤ Fpts`, which by base change
is a `ℂ`-basis of `ℂⁿ`; `ψ` takes the coordinates along the middle block.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

namespace StrongSix.Roy

variable {F : Type*} [Field F] [Algebra F ℂ]

omit [Algebra F ℂ] in
/-- A complement of `A` inside `B` (for `A ≤ B`). -/
theorem exists_compl_in {V : Type*} [AddCommGroup V] [Module F V] {A B : Submodule F V}
    (hAB : A ≤ B) : ∃ C : Submodule F V, C ≤ B ∧ A ⊓ C = ⊥ ∧ A ⊔ C = B := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (A.comap B.subtype)
  refine ⟨q.map B.subtype, map_subtype_le _ _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, ⟨y, hy, rfl⟩⟩
    have : y ∈ A.comap B.subtype ⊓ q := ⟨hxA, hy⟩
    rw [hq.inf_eq_bot, mem_bot] at this
    rw [this]; rfl
  · apply le_antisymm
    · exact sup_le hAB (map_subtype_le _ _)
    · intro x hx
      have : (⟨x, hx⟩ : B) ∈ A.comap B.subtype ⊔ q := by rw [hq.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup.mp this
      have hx' : x = (y : V) + (z : V) := by rw [← Submodule.coe_add, hyz]
      rw [hx']
      exact add_mem (mem_sup_left hy) (mem_sup_right ⟨z, hz, rfl⟩)

variable {n : ℕ}

omit [Algebra F ℂ] in
theorem span_basis_coe {V : Type*} [AddCommGroup V] [Module F V] (A : Submodule F V)
    {ι : Type*} (b : Basis ι F A) : span F (Set.range fun i => (b i : V)) = A := by
  have h := congrArg (Submodule.map A.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
  exact h

/-- **Realization of a rational subquotient.** -/
theorem realize (AS AT : Submodule F (Fin n → ℂ)) (hST : AS ≤ AT) (hT : AT ≤ Fpts F (Fin n)) :
    ∃ (k : ℕ) (ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)),
      PresF F ψ ∧
      AT.map (ψ.restrictScalars F) = Fpts F (Fin k) ∧
      LinearMap.ker ψ ⊓ span ℂ (AT : Set (Fin n → ℂ)) = span ℂ (AS : Set (Fin n → ℂ)) ∧
      k + finrank F AS = finrank F AT := by
  classical
  have hS : AS ≤ Fpts F (Fin n) := hST.trans hT
  have : FiniteDimensional F AS := Submodule.finiteDimensional_of_le hS
  have : FiniteDimensional F AT := Submodule.finiteDimensional_of_le hT
  obtain ⟨C1, hC1T, hC1i, hC1s⟩ := exists_compl_in hST
  obtain ⟨C2, hC2P, hC2i, hC2s⟩ := exists_compl_in hT
  have : FiniteDimensional F C1 := Submodule.finiteDimensional_of_le (hC1T.trans hT)
  have : FiniteDimensional F C2 := Submodule.finiteDimensional_of_le hC2P
  let bS := Module.finBasis F AS
  let b1 := Module.finBasis F C1
  let b2 := Module.finBasis F C2
  set a := finrank F AS
  set k := finrank F C1
  set m := finrank F C2
  let vS : Fin a → (Fin n → ℂ) := fun i => (bS i : Fin n → ℂ)
  let v1 : Fin k → (Fin n → ℂ) := fun i => (b1 i : Fin n → ℂ)
  let v2 : Fin m → (Fin n → ℂ) := fun i => (b2 i : Fin n → ℂ)
  let v : Fin a ⊕ (Fin k ⊕ Fin m) → (Fin n → ℂ) := Sum.elim vS (Sum.elim v1 v2)
  have hspS : span F (Set.range vS) = AS := span_basis_coe AS bS
  have hsp1 : span F (Set.range v1) = C1 := span_basis_coe C1 b1
  have hsp2 : span F (Set.range v2) = C2 := span_basis_coe C2 b2
  have hsp12 : span F (Set.range (Sum.elim v1 v2)) = C1 ⊔ C2 := by
    rw [Set.Sum.elim_range, span_union, hsp1, hsp2]
  have hspv : span F (Set.range v) = Fpts F (Fin n) := by
    rw [Set.Sum.elim_range, span_union, hspS, hsp12, ← sup_assoc, hC1s, hC2s]
  -- `F`-linear independence
  have hliS : LinearIndependent F vS := bS.linearIndependent.map' AS.subtype (by simp)
  have hli1 : LinearIndependent F v1 := b1.linearIndependent.map' C1.subtype (by simp)
  have hli2 : LinearIndependent F v2 := b2.linearIndependent.map' C2.subtype (by simp)
  have hli12 : LinearIndependent F (Sum.elim v1 v2) := by
    refine hli1.sum_type hli2 ?_
    rw [hsp1, hsp2, disjoint_iff, eq_bot_iff]
    intro x ⟨h1, h2⟩
    have : x ∈ AT ⊓ C2 := ⟨hC1T h1, h2⟩
    rwa [hC2i] at this
  have hliv : LinearIndependent F v := by
    refine hliS.sum_type hli12 ?_
    rw [hspS, hsp12, disjoint_iff, eq_bot_iff]
    intro x ⟨hxS, hx12⟩
    obtain ⟨c1, hc1, c2, hc2, rfl⟩ := mem_sup.mp hx12
    have hc2AT : c2 ∈ AT := by
      have : c2 = (c1 + c2) - c1 := by abel
      rw [this]; exact sub_mem (hST hxS) (hC1T hc1)
    have hc2z : c2 = 0 := by
      have : c2 ∈ AT ⊓ C2 := ⟨hc2AT, hc2⟩
      rwa [hC2i, mem_bot] at this
    subst hc2z
    rw [add_zero] at hxS ⊢
    have : c1 ∈ AS ⊓ C1 := ⟨hxS, hc1⟩
    rwa [hC1i, mem_bot] at this
  have hv_mem : ∀ i, v i ∈ Fpts F (Fin n) := fun i => hspv ▸ subset_span ⟨i, rfl⟩
  -- the `ℂ`-basis
  have hliC : LinearIndependent ℂ v := linearIndependent_of_Fpts hv_mem hliv
  have hspC : ⊤ ≤ span ℂ (Set.range v) := by
    rw [← span_Fpts_eq_top (F := F) (ι := Fin n), ← hspv, Submodule.span_span_of_tower]
  let B : Basis (Fin a ⊕ (Fin k ⊕ Fin m)) ℂ (Fin n → ℂ) := Basis.mk hliC hspC
  have hB : ∀ i, B i = v i := fun i => Basis.mk_apply hliC hspC i
  let ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi fun j => B.coord (Sum.inr (Sum.inl j))
  have hψ : ∀ x j, ψ x j = B.repr x (Sum.inr (Sum.inl j)) := fun _ _ => rfl
  have hψB : ∀ i, ψ (B i) = fun j => if i = Sum.inr (Sum.inl j) then 1 else 0 := by
    intro i; funext j
    rw [hψ, Basis.repr_self, Finsupp.single_apply]
  -- `F`-points have `F`-coordinates
  have hcoord : ∀ x ∈ Fpts F (Fin n), ∃ f : Fin a ⊕ (Fin k ⊕ Fin m) → F,
      ∀ i, B.repr x i = algebraMap F ℂ (f i) := by
    intro x hx
    rw [← hspv] at hx
    obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
    refine ⟨f, fun i => ?_⟩
    have hx' : x = B.equivFun.symm (fun i => algebraMap F ℂ (f i)) := by
      rw [Basis.equivFun_symm_apply, ← hf]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hB, algebraMap_smul]
    rw [← Basis.equivFun_apply, hx', LinearEquiv.apply_symm_apply]
  have hpres : PresF F ψ := by
    intro x hx j
    obtain ⟨f, hf⟩ := hcoord x hx
    exact ⟨f _, by rw [hψ, hf]⟩
  -- `ψ` kills `AS`
  have hψS : ∀ i, ψ (vS i) = 0 := by
    intro i
    have := hψB (Sum.inl i)
    rw [hB] at this
    change ψ (v (Sum.inl i)) = 0
    rw [this]; funext j; simp
  have hS_ker : AS ≤ (LinearMap.ker ψ).restrictScalars F := by
    rw [← hspS, span_le]
    rintro _ ⟨i, rfl⟩
    exact hψS i
  -- image of `AT`
  have hψ1 : ∀ j, ψ (v1 j) = Pi.single j 1 := by
    intro j
    have := hψB (Sum.inr (Sum.inl j))
    rw [hB] at this
    rw [show v1 j = v (Sum.inr (Sum.inl j)) from rfl, this]
    funext j'
    by_cases h : j' = j
    · subst h; simp
    · rw [Pi.single_eq_of_ne h]
      simp [Ne.symm h]
  have hmap : AT.map (ψ.restrictScalars F) = Fpts F (Fin k) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hpres x (hT hx)
    · rw [Fpts_eq_span, span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨v1 j, hC1T (b1 j).2, hψ1 j⟩
  -- the kernel on `span AT`
  set P : Submodule ℂ (Fin n → ℂ) := span ℂ (AT : Set (Fin n → ℂ)) with hP
  have hle : span ℂ (AS : Set (Fin n → ℂ)) ≤ LinearMap.ker ψ ⊓ P := by
    refine le_inf ?_ (span_mono hST)
    rw [span_le]; intro x hx; exact hS_ker hx
  have hdimAT : k + a = finrank F AT := by
    have := Submodule.finrank_sup_add_finrank_inf_eq AS C1
    rw [hC1s, hC1i, finrank_bot] at this
    omega
  have hker : LinearMap.ker ψ ⊓ P = span ℂ (AS : Set (Fin n → ℂ)) := by
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    let ψP := ψ.comp P.subtype
    have hrange : LinearMap.range ψP = ⊤ := by
      rw [LinearMap.range_comp, Submodule.range_subtype, hP, Submodule.map_span, eq_top_iff,
        ← span_Fpts_eq_top (F := F) (ι := Fin k), ← hmap]
      apply span_mono
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    have hkermap : (LinearMap.ker ψP).map P.subtype = LinearMap.ker ψ ⊓ P := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
      · rintro ⟨hx1, hx2⟩; exact ⟨⟨x, hx2⟩, hx1, rfl⟩
    have rn := LinearMap.finrank_range_add_finrank_ker ψP
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      ← Submodule.finrank_map_subtype_eq P (LinearMap.ker ψP), hkermap] at rn
    have hPdim : finrank ℂ P = finrank F AT := finrank_span_of_le_Fpts AT hT
    rw [finrank_span_of_le_Fpts AS hS]
    omega
  exact ⟨k, ψ, hpres, hmap, hker, hdimAT⟩

end StrongSix.Roy

end LeanPool
