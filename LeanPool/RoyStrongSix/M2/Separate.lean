/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import LeanPool.RoyStrongSix.M2.Classify
public import LeanPool.RoyStrongSix.M2.Transl

/-!
# Restriction spaces and separation of cosets (Roy Ex. 8.5, Lemma 8.15)

* `restrE E`: polynomials ↦ their values on `E` (extended by `0`).
* `hfun_vanish_eq`: `hfun (vanish E) t = dim (restrictions of FLE(tD) to E)`.
* `hfun_union2`: if `B` has block degree `≤ c • D`, `B ≡ 0` on `E₁` and `B ≡ 1` on `E₂`, then
  `hfun I(E₁) t + hfun I(E₂) t ≤ hfun I(E₁ ∪ E₂) (t + c)`.
* `exists_sep`: for `γ ∉ V × T_Λ` there is `A ∈ I(V × T_Λ)` with `A ≡ 1` on `γ·(V × T_Λ)`.
* **`hfun_cosets_ge`**: for finitely many distinct cosets `gᵢ·G₀` of `G₀ = V × T_Λ`,
  `#cosets · hfun I(G₀) t ≤ hfun I(⋃ gᵢ·G₀) (t + c)` for some `c`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

local notation "B" => MvPolynomial (V3 d0 d1) K

/-- The restriction of a polynomial to `E`, as a function on `G` vanishing off `E`. -/
noncomputable def restrE (E : Set (GPt K d0 d1)) : B →ₗ[K] (GPt K d0 d1 → K) where
  toFun P := E.indicator fun g => eval (pt g) P
  map_add' P Q := by
    funext g; by_cases hg : g ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hg]
  map_smul' c P := by
    funext g; by_cases hg : g ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hg]

open Classical in
omit [CharZero K] in
theorem restrE_apply (E : Set (GPt K d0 d1)) (P : B) (g : GPt K d0 d1) :
    restrE E P g = if g ∈ E then eval (pt g) P else 0 := by
  simp only [restrE, LinearMap.coe_mk, AddHom.coe_mk, Set.indicator_apply]

/-- The indicator projection on functions. -/
noncomputable def indE (E : Set (GPt K d0 d1)) : (GPt K d0 d1 → K) →ₗ[K] (GPt K d0 d1 → K) where
  toFun f := E.indicator f
  map_add' f f' := by
    funext g; by_cases hg : g ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hg]
  map_smul' c f := by
    funext g; by_cases hg : g ∈ E <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hg]

open Classical in
omit [CharZero K] in
theorem indE_apply (E : Set (GPt K d0 d1)) (f : GPt K d0 d1 → K) (g : GPt K d0 d1) :
    indE E f g = if g ∈ E then f g else 0 := by
  simp only [indE, LinearMap.coe_mk, AddHom.coe_mk, Set.indicator_apply]

variable (D : Fin 2 → ℕ)

omit [CharZero K] in
/-- `hfun` as the dimension of a restriction space. -/
theorem hfun_vanish_eq (E : Set (GPt K d0 d1)) (t : ℕ) :
    hfun blk D K (vanish E) t = finrank K ((FLE K blk (t • D)).map (restrE E)) := by
  classical
  set F := FLE K blk (t • D)
  let ρ := (restrE E).domRestrict F
  have h1 := LinearMap.finrank_range_add_finrank_ker ρ
  have hrange : LinearMap.range ρ = F.map (restrE E) := LinearMap.range_domRestrict _ _
  have hker : LinearMap.ker ρ = ((vanish E).restrictScalars K).comap F.subtype := by
    ext ⟨P, hP⟩
    simp only [LinearMap.mem_ker, ρ, LinearMap.domRestrict_apply, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.restrictScalars_mem]
    constructor
    · intro h g hg
      have := congrFun h g
      rwa [restrE_apply, ite_eq_left hg] at this
    · intro h
      funext g
      rw [restrE_apply]
      split_ifs with hg
      · exact h g hg
      · rfl
  rw [hrange, hker, finrank_comap_subtype, inf_comm] at h1
  have e : hfun blk D K (vanish E) t = finrank K F - finrank K ↥((vanish E).restrictScalars K ⊓
    F) :=
    rfl
  rw [e]
  omega

omit [CharZero K] in
/-- **Two separated sets.** -/
theorem hfun_union2 {E1 E2 : Set (GPt K d0 d1)} {Bp : B} {c : ℕ}
    (hB : Bp ∈ FLE K blk (c • D)) (hB1 : ∀ g ∈ E1, eval (pt g) Bp = 0)
    (hB2 : ∀ g ∈ E2, eval (pt g) Bp = 1) (t : ℕ) :
    hfun blk D K (vanish E1) t + hfun blk D K (vanish E2) t ≤
      hfun blk D K (vanish (E1 ∪ E2)) (t + c) := by
  classical
  rw [hfun_vanish_eq, hfun_vanish_eq, hfun_vanish_eq]
  set F0 := FLE K blk (t • D)
  set F1 := FLE K blk ((t + c) • D)
  set R := F1.map (restrE (E1 ∪ E2))
  have hdeg : ∀ {P Q : B}, P ∈ FLE K blk (c • D) → Q ∈ F0 → P * Q ∈ F1 := fun hP hQ => by
    have := mul_mem_FLE K hP hQ
    rwa [show c • D + t • D = (t + c) • D by rw [add_nsmul, add_comm]] at this
  have h1mem : (1 : B) - Bp ∈ FLE K blk (c • D) :=
    Submodule.sub_mem _ (one_mem_FLE (K := K) (d0 := d0) (d1 := d1) (c • D)) hB
  -- `R` surjects onto the restrictions to `E₁`
  have hR1 : F0.map (restrE E1) ≤ R.map (indE E1) := by
    rintro _ ⟨P, hP, rfl⟩
    refine ⟨restrE (E1 ∪ E2) ((1 - Bp) * P), ⟨(1 - Bp) * P, hdeg h1mem hP, rfl⟩, ?_⟩
    funext g
    rw [indE_apply, restrE_apply, restrE_apply]
    by_cases hg : g ∈ E1
    · simp only [hg, Set.mem_union, true_or, ite_true, map_mul, map_sub, map_one, hB1 g hg,
      sub_zero,
        one_mul]
    · rw [ite_eq_right hg, ite_eq_right hg]
  -- the kernel of `indE E₁` on `R` contains `B · F₀`
  let K2 := F0.map ((restrE (E1 ∪ E2)).comp (LinearMap.mulLeft K Bp))
  have hK2 : K2 ≤ R ⊓ LinearMap.ker (indE E1) := by
    rintro _ ⟨P, hP, rfl⟩
    refine ⟨⟨Bp * P, hdeg hB hP, rfl⟩, LinearMap.mem_ker.mpr ?_⟩
    funext g
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, indE_apply, restrE_apply,
      Pi.zero_apply]
    split_ifs with hg hg'
    · rw [map_mul, hB1 g hg, zero_mul]
    · exact absurd (Set.mem_union_left _ hg) hg'
    · rfl
  have hK2E2 : F0.map (restrE E2) ≤ K2.map (indE E2) := by
    rintro _ ⟨P, hP, rfl⟩
    refine ⟨_, ⟨P, hP, rfl⟩, ?_⟩
    funext g
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, indE_apply, restrE_apply]
    by_cases hg : g ∈ E2
    · rw [ite_eq_left hg, ite_eq_left (Set.mem_union_right _ hg), ite_eq_left hg, map_mul, hB2 g
      hg, one_mul]
    · rw [ite_eq_right hg, ite_eq_right hg]
  -- dimension count
  have : FiniteDimensional K F1 := inferInstance
  have : FiniteDimensional K R := Module.Finite.map _ _
  let π := (indE E1).domRestrict R
  have hrn := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_domRestrict] at hrn
  have hkerπ : finrank K (LinearMap.ker π) = finrank K ↥(R ⊓ LinearMap.ker (indE E1)) := by
    have : LinearMap.ker π = (LinearMap.ker (indE E1)).comap R.subtype := by
      ext x; simp [π]
    rw [this, finrank_comap_subtype]
  have e1 := Submodule.finrank_mono hR1
  have e2 := Submodule.finrank_mono hK2
  have e3 := Submodule.finrank_mono hK2E2
  have : FiniteDimensional K K2 := Submodule.finiteDimensional_of_le (hK2.trans inf_le_left)
  have e4 := Submodule.finrank_map_le (indE E2) K2
  omega

/-! ### Monotonicity and an upper bound for unions -/

omit [CharZero K] in
theorem hfun_vanish_mono (E : Set (GPt K d0 d1)) {t t' : ℕ} (h : t ≤ t') :
    hfun blk D K (vanish E) t ≤ hfun blk D K (vanish E) t' := by
  rw [hfun_vanish_eq, hfun_vanish_eq]
  apply Submodule.finrank_mono
  apply Submodule.map_mono
  apply FLE_mono
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Nat.mul_le_mul_right _ h

omit [CharZero K] in
/-- **Unions**: `hfun I(E₁ ∪ E₂) ≤ hfun I(E₁) + hfun I(E₂)`. -/
theorem hfun_union_le (E1 E2 : Set (GPt K d0 d1)) (t : ℕ) :
    hfun blk D K (vanish (E1 ∪ E2)) t ≤ hfun blk D K (vanish E1) t + hfun blk D K (vanish E2) t
      := by
  classical
  rw [hfun_vanish_eq, hfun_vanish_eq, hfun_vanish_eq]
  set F := FLE K blk (t • D)
  have hsplit : F.map (restrE (E1 ∪ E2)) ≤
      F.map (restrE E1) ⊔ (F.map (restrE E2)).map (indE (E2 \ E1)) := by
    rintro _ ⟨P, hP, rfl⟩
    refine Submodule.mem_sup.mpr ⟨restrE E1 P, ⟨P, hP, rfl⟩, indE (E2 \ E1) (restrE E2 P),
      ⟨restrE E2 P, ⟨P, hP, rfl⟩, rfl⟩, ?_⟩
    funext g
    simp only [Pi.add_apply, restrE_apply, indE_apply, Set.mem_union, Set.mem_sdiff]
    by_cases h1 : g ∈ E1 <;> by_cases h2 : g ∈ E2 <;> simp [h1, h2]
  calc finrank K (F.map (restrE (E1 ∪ E2)))
      ≤ finrank K ↥(F.map (restrE E1) ⊔ (F.map (restrE E2)).map (indE (E2 \ E1))) :=
        Submodule.finrank_mono hsplit
    _ ≤ finrank K (F.map (restrE E1)) + finrank K ((F.map (restrE E2)).map (indE (E2 \ E1))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ finrank K (F.map (restrE E1)) + finrank K (F.map (restrE E2)) := by
        gcongr; exact Submodule.finrank_map_le _ _

/-! ### Separating polynomials -/

/-- The monomial `Y^{λ⁺} Z^{λ⁻}`, which is `y^λ` on `G`. -/
noncomputable def monoChr (l : Fin d1 → ℤ) : B :=
  ∏ j, if 0 ≤ l j then X (Sum.inr (Sum.inl j)) ^ (l j).toNat else X (Sum.inr (Sum.inr j)) ^ (-l
    j).toNat

omit [CharZero K] in
theorem eval_monoChr (g : GPt K d0 d1) (l : Fin d1 → ℤ) :
    eval (pt g) (monoChr l) = chr g.2 l := by
  simp only [monoChr, map_prod, chr]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [map_pow, eval_X]
    simp only [pt, Sum.elim_inr, Sum.elim_inl]
    rw [← zpow_natCast, Int.toNat_of_nonneg h]
  · rw [map_pow, eval_X]
    simp only [pt, Sum.elim_inr]
    rw [Units.val_inv_eq_inv_val, ← zpow_natCast, Int.toNat_of_nonneg (by omega), inv_zpow',
      neg_neg]

omit [CharZero K] in
/-- A polynomial vanishing on `V × T_Λ` and equal to `1` on `γ·(V × T_Λ)`, when `γ ∉ V × T_Λ`. -/
theorem exists_sep (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) (γ : GPt K d0 d1)
    (hγ : γ ∉ prodSet V Λ) : ∃ A : B, A ∈ vanish (prodSet V Λ) ∧
      ∀ g ∈ prodSet V Λ, eval (pt (gmul γ g)) A = 1 := by
  by_cases hx : γ.1 ∈ V
  · have : ∃ l ∈ Λ, chr γ.2 l ≠ 1 := by
      by_contra h; push Not at h; exact hγ ⟨hx, h⟩
    obtain ⟨l, hl, hne⟩ := this
    have hne' : chr γ.2 l - 1 ≠ 0 := sub_ne_zero.mpr hne
    refine ⟨C ((chr γ.2 l - 1)⁻¹) * (monoChr l - 1), fun g hg => ?_, fun g hg => ?_⟩
    · simp [eval_monoChr, hg.2 l hl]
    · simp only [map_mul, eval_C, map_sub, eval_monoChr, map_one, gmul, chr_mul, hg.2 l hl,
        mul_one]
      exact inv_mul_cancel₀ hne'
  · obtain ⟨μ, hμγ, hVμ⟩ := Submodule.exists_le_ker_of_notMem hx
    let lin : B := ∑ k, C (μ (Pi.single k 1)) * X (Sum.inl k)
    have hlin : ∀ h : GPt K d0 d1, eval (pt h) lin = μ h.1 := by
      intro h
      simp only [lin, map_sum, map_mul, eval_C, eval_X, pt, Sum.elim_inl]
      rw [LinearMap.pi_apply_eq_sum_univ μ h.1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      funext i; simp [Pi.single_apply, eq_comm]
    refine ⟨C ((μ γ.1)⁻¹) * lin, fun g hg => ?_, fun g hg => ?_⟩
    · simp only [map_mul, eval_C, hlin]
      rw [hVμ hg.1, mul_zero]
    · simp only [map_mul, eval_C, hlin, gmul, map_add]
      rw [hVμ hg.1, add_zero]
      exact inv_mul_cancel₀ hμγ

/-- **Separation of cosets.** -/
theorem hfun_cosets_ge (hD : ∀ i, 1 ≤ D i) (V : Submodule K (Fin d0 → K))
    (Λ : AddSubgroup (Fin d1 → ℤ)) (s : Finset (GPt K d0 d1))
    (hdist : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → gmul (ginv b) a ∉ prodSet V Λ) :
    ∃ c : ℕ, ∀ t, s.card * hfun blk D K (vanish (prodSet V Λ)) t ≤
      hfun blk D K (vanish (⋃ a ∈ s, gtransl a (prodSet V Λ))) (t + c) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun t => by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih fun x hx y hy hxy =>
      hdist x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    -- the separating polynomial
    have hsep : ∀ b ∈ s, ∃ A : B, A ∈ vanish (prodSet V Λ) ∧
        ∀ g ∈ prodSet V Λ, eval (pt (gmul (gmul (ginv b) a) g)) A = 1 := fun b hb =>
      exists_sep V Λ _ (hdist a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
        (fun h => ha (h ▸ hb)))
    choose! Asep hAvan hAone using hsep
    let Bp : B := ∏ b ∈ s, transl (ginv b) (Asep b)
    have hB1 : ∀ h ∈ ⋃ b ∈ s, gtransl b (prodSet V Λ), eval (pt h) Bp = 0 := by
      intro h hh
      simp only [Set.mem_iUnion] at hh
      obtain ⟨b, hb, g, hg, rfl⟩ := hh
      simp only [Bp, map_prod]
      apply Finset.prod_eq_zero hb
      rw [eval_transl, ← gmul_assoc, gmul_ginv, gzero_gmul]
      exact hAvan b hb g hg
    have hB2 : ∀ h ∈ gtransl a (prodSet V Λ), eval (pt h) Bp = 1 := by
      rintro _ ⟨g, hg, rfl⟩
      simp only [Bp, map_prod]
      apply Finset.prod_eq_one
      intro b hb
      rw [eval_transl, ← gmul_assoc]
      exact hAone b hb g hg
    set cB := Bp.totalDegree
    have hBp : Bp ∈ FLE K blk (cB • D) := mem_FLE_totalDegree blk D K hD Bp
    refine ⟨c + cB, fun t => ?_⟩
    have h2 := hfun_union2 D hBp hB1 hB2 (t + c)
    have h3 := hfun_vanish_transl D a (prodSet V Λ) (t + c)
    have h4 := hfun_vanish_mono D (prodSet V Λ) (show t ≤ t + c by omega)
    have h5 := hc t
    have hU : (⋃ x ∈ insert a s, gtransl x (prodSet V Λ)) =
        (⋃ b ∈ s, gtransl b (prodSet V Λ)) ∪ gtransl a (prodSet V Λ) := by
      rw [Finset.set_biUnion_insert, Set.union_comm]
    rw [hU, Finset.card_insert_of_notMem ha, ← add_assoc]
    nlinarith

end StrongSix.M2

end LeanPool
