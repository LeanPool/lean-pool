/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Kochen–Specker valuations

A *Kochen–Specker valuation* on an inner product space `E` of dimension `d` is a map `v : E → Bool`
that is `true` on exactly one vector of every orthonormal basis (indexed by `Fin d`). Nothing is
assumed about `v` off unit vectors, or about its behaviour under phases.

* `IsValuation.existsUnique_of_orthonormal`: exactly one `true` on any `d` orthonormal vectors.
* `IsValuation.not_both`: never `true` on two orthonormal vectors (when `d ≥ 2`).
* `IsValuation.map`: valuations transfer along linear isometric equivalences.
* `IsValuation.exists_subspace`: a valuation in dimension `d + 1` (`d ≥ 1`) restricts to one on
  the orthogonal complement of a unit vector where it is `false`, a space of dimension `d`.
* `NoValuation.succ`, `NoValuation.of_le`: so the absence of valuations in dimension `d`
  propagates to every larger dimension.
-/

@[expose] public section

open Module

namespace KochenSpecker

variable {𝕜 : Type*} [RCLike 𝕜]

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- `v` is a **Kochen–Specker valuation** in dimension `d`: every orthonormal basis indexed by
`Fin d` has exactly one vector on which `v` is `true`. -/
def IsValuation (d : ℕ) (v : E → Bool) : Prop :=
  ∀ b : OrthonormalBasis (Fin d) 𝕜 E, ∃! i, v (b i) = true

/-- `d` orthonormal vectors in a space of dimension `d` carry exactly one `true`. -/
theorem IsValuation.existsUnique_of_orthonormal {d : ℕ} [NeZero d] {v : E → Bool}
    (hv : IsValuation 𝕜 d v) (hE : finrank 𝕜 E = d) {f : Fin d → E} (hf : Orthonormal 𝕜 f) :
    ∃! i, v (f i) = true := by
  have hcard : Fintype.card (Fin d) = finrank 𝕜 E := by simp [hE]
  set B := basisOfOrthonormalOfCardEqFinrank hf hcard
  have hB : (B : Fin d → E) = f := coe_basisOfOrthonormalOfCardEqFinrank hf hcard
  have hon : Orthonormal 𝕜 B := by rw [hB]; exact hf
  have := hv (B.toOrthonormalBasis hon)
  simpa [Module.Basis.coe_toOrthonormalBasis, hB] using this

/-- A valuation is never `true` on two orthonormal vectors. -/
theorem IsValuation.not_both {n : ℕ} {v : E → Bool} (hv : IsValuation 𝕜 (n + 2) v)
    (hE : finrank 𝕜 E = n + 2) {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner 𝕜 x y = 0) :
    ¬ (v x = true ∧ v y = true) := by
  rintro ⟨hvx, hvy⟩
  have : FiniteDimensional 𝕜 E := Module.finite_of_finrank_pos (by omega)
  set w : Fin (n + 2) → E := fun i => if i = 0 then x else if i = 1 then y else 0
  have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
  have hw : Orthonormal 𝕜 (({0, 1} : Set (Fin (n + 2))).domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    have hyx : inner 𝕜 y x = 0 := inner_eq_zero_symm.1 hxy
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.domRestrict_apply, w, h01, h01.symm, hxy, hyx, inner_self_eq_norm_sq_to_K, hx, hy]
  obtain ⟨b, hb⟩ := hw.exists_orthonormalBasis_extension_of_card_eq (by simp [hE])
  have hb0 : b 0 = x := by rw [hb 0 (by simp)]; simp [w]
  have hb1 : b 1 = y := by rw [hb 1 (by simp)]; simp [w, h01.symm]
  obtain ⟨i, -, hu⟩ := hv b
  exact h01 ((hu 0 (show v (b 0) = true by rw [hb0]; exact hvx)).trans
    (hu 1 (show v (b 1) = true by rw [hb1]; exact hvy)).symm)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Valuations transfer along linear isometric equivalences. -/
theorem IsValuation.map {d : ℕ} {v : E → Bool} (hv : IsValuation 𝕜 d v) (φ : E ≃ₗᵢ[𝕜] F) :
    IsValuation 𝕜 d (fun y => v (φ.symm y)) := by
  intro b
  simpa using hv (b.map φ.symm)

/-- A valuation in dimension `d + 1` restricts to the orthogonal complement of a unit vector on
which it is `false`, a subspace of dimension `d`. -/
theorem IsValuation.exists_subspace {d : ℕ} [NeZero d] {v : E → Bool}
    (hv : IsValuation 𝕜 (d + 1) v) (hE : finrank 𝕜 E = d + 1) :
    ∃ K : Submodule 𝕜 E, finrank 𝕜 K = d ∧ IsValuation 𝕜 d (fun x : K => v x) := by
  have : Fact (finrank 𝕜 E = d + 1) := ⟨hE⟩
  have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ d
  -- A unit vector `u` where `v` is `false`.
  set b₀ := (stdOrthonormalBasis 𝕜 E).reindex (finCongr hE)
  obtain ⟨i₀, -, huniq⟩ := hv b₀
  obtain ⟨j, hj⟩ : ∃ j : Fin (d + 1), j ≠ i₀ := by
    by_cases h : i₀ = 0
    · refine ⟨Fin.last d, fun e => NeZero.ne d ?_⟩
      have := congrArg Fin.val (e.trans h)
      simpa using this
    · exact ⟨0, fun e => h e.symm⟩
  have hfalse : v (b₀ j) = false := by
    cases h : v (b₀ j)
    · rfl
    · exact absurd (huniq j h) hj
  set u := b₀ j
  have hu1 : ‖u‖ = 1 := b₀.orthonormal.1 j
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu1
    exact zero_ne_one hu1
  refine ⟨(𝕜 ∙ u)ᗮ, Submodule.finrank_orthogonal_span_singleton hu0, fun b => ?_⟩
  -- `u` together with an orthonormal basis of its complement.
  set f : Fin (d + 1) → E := Fin.cons u (fun i => (b i : E))
  have hperp : ∀ i, inner 𝕜 u (b i : E) = 0 := fun i =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (b i).2
  have hb : ∀ i j, inner 𝕜 (b i : E) (b j : E) = if i = j then 1 else 0 := fun i j => by
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.1 b.orthonormal i j
  have hf : Orthonormal 𝕜 f := by
    rw [orthonormal_iff_ite]
    intro i k
    induction i using Fin.cases <;> induction k using Fin.cases
    · simp [f, inner_self_eq_norm_sq_to_K, hu1]
    · simp [f, hperp, (Fin.succ_ne_zero _).symm]
    · simp [f, inner_eq_zero_symm.1 (hperp _), Fin.succ_ne_zero]
    · simp [f, hb]
  obtain ⟨k, hk, hku⟩ := hv.existsUnique_of_orthonormal hE hf
  induction k using Fin.cases with
  | zero => simp [f, u, hfalse] at hk
  | succ k =>
    refine ⟨k, by simpa [f] using hk, fun m hm => Fin.succ_injective _ ?_⟩
    exact hku m.succ (by simpa [f] using hm)

end General

universe u

variable (𝕜) in
/-- No inner product space of dimension `d` (in universe `u`) carries a Kochen–Specker
valuation. -/
def NoValuation (d : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E], finrank 𝕜 E = d →
    ∀ v : E → Bool, ¬ IsValuation 𝕜 d v

/-- The absence of valuations passes from dimension `d ≥ 1` to dimension `d + 1`. -/
theorem NoValuation.succ {d : ℕ} [NeZero d] (h : NoValuation.{u} 𝕜 d) :
    NoValuation.{u} 𝕜 (d + 1) := by
  intro E _ _ hE v hv
  obtain ⟨K, hK, hvK⟩ := hv.exists_subspace hE
  exact h K hK _ hvK

/-- The absence of valuations passes from dimension `d ≥ 1` to every larger dimension. -/
theorem NoValuation.of_le {d d' : ℕ} (hd : 1 ≤ d) (h : NoValuation.{u} 𝕜 d) (hdd' : d ≤ d') :
    NoValuation.{u} 𝕜 d' := by
  induction d', hdd' using Nat.le_induction with
  | base => exact h
  | succ n hn ih =>
    have : NeZero n := ⟨by omega⟩
    exact ih.succ

end KochenSpecker
