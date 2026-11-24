/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermRing
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RegularDirection
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LastVariableTaylorDivision
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.WeierstrassDivisionAbstract
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Holomorphic germs form a Noetherian ring, given Weierstrass division

`GermWeierstrassDivision E` is the Weierstrass division theorem for germs at `0` of
`E × ℂ`: if `G (0, t) = t^d u(t)` with `u(0) ≠ 0`, every holomorphic germ `h` is
`q G + ∑_{k<d} r_k(z) t^k` with `q` and the `r_k` holomorphic.

`isNoetherianRing_prod_of_division` proves the classical induction step (Rückert's basis
theorem): if `𝒪_{E,0}` is Noetherian and division holds on `E × ℂ`, then `𝒪_{E×ℂ,0}` is
Noetherian.  Let `I ≠ 0` be an ideal.  After a linear change of coordinates
(`exists_regular_continuousLinearEquiv`) it contains some `G` with `G (0, t) = t^d u(t)`.
Division shows `I = (G) + (I ∩ M)`, where `M = ∑_{k<d} 𝒪_{E,0} t^k` is a finitely generated
`𝒪_{E,0}`-module, so `I ∩ M` is finitely generated over `𝒪_{E,0}`.

`isNoetherianRing_holGerm_euclidean` runs the induction over `ℂⁿ`.
-/

@[expose] public section

open Filter Topology

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

/-- Weierstrass division for germs at `0` of `E × ℂ`, with respect to the last variable. -/
def GermWeierstrassDivision (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ (G : E × ℂ → ℂ), (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ G x) →
    ∀ (d : ℕ) (u : ℂ → ℂ), AnalyticAt ℂ u 0 → u 0 ≠ 0 →
    (∀ᶠ t in 𝓝 (0 : ℂ), G (0, t) = t ^ d * u t) →
    ∀ (h : E × ℂ → ℂ), (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) →
    ∃ q : E × ℂ → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ q x) ∧
      ∃ r : ℕ → E → ℂ, (∀ k, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (r k) z) ∧
        h =ᶠ[𝓝 0] fun x => q x * G x + ∑ k ∈ Finset.range d, r k x.1 * x.2 ^ k

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If every nonzero germ is a unit, the ring of germs is Noetherian. -/
theorem isNoetherianRing_holGerm_of_subsingleton [Subsingleton E] :
    IsNoetherianRing (HolGerm E) := by
  rw [isNoetherianRing_iff, isNoetherian_def]
  intro I
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  · obtain ⟨g, hgI, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hunit : IsUnit g := by
      rw [HolGerm.isUnit_iff_eval_ne_zero]
      intro hev
      apply hg0
      obtain ⟨f, hf, rfl⟩ := HolGerm.exists_eq_mk g
      rw [HolGerm.eval_mk] at hev
      rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
      exact Eventually.of_forall fun z => by
        simp [Subsingleton.elim z 0, hev]
    rw [Ideal.eq_top_of_isUnit_mem I hgI hunit]
    exact ⟨{1}, by simp⟩

/-- The germ of the last coordinate `t` on `E × ℂ`. -/
def HolGerm.lastCoord : HolGerm (E × ℂ) :=
  HolGerm.mk (fun x : E × ℂ => x.2)
    (Eventually.of_forall fun _ => differentiableAt_snd)

/-- Pullback of germs along the projection `E × ℂ → E`. -/
def HolGerm.ofFst : HolGerm E →+* HolGerm (E × ℂ) :=
  HolGerm.comap (ContinuousLinearMap.fst ℂ E ℂ)

/-- **Rückert's basis theorem, for an ideal containing a regular germ.** -/
theorem ideal_fg_of_regular [IsNoetherianRing (HolGerm E)] (hdiv : GermWeierstrassDivision E)
    (I : Ideal (HolGerm (E × ℂ))) {G : E × ℂ → ℂ} (hG : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ G x)
    (hGI : HolGerm.mk G hG ∈ I) {d : ℕ} {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hGu : ∀ᶠ t in 𝓝 (0 : ℂ), G (0, t) = t ^ d * u t) : I.FG := by
  classical
  let _ : Algebra (HolGerm E) (HolGerm (E × ℂ)) := (HolGerm.ofFst (E := E)).toAlgebra
  set R := HolGerm E
  set S := HolGerm (E × ℂ)
  set M : Submodule R S :=
    Submodule.span R ((fun k => HolGerm.lastCoord ^ k) '' (Finset.range d : Set ℕ))
  have : IsNoetherian R M :=
    isNoetherian_span_of_finite R ((Finset.range d).finite_toSet.image _)
  obtain ⟨T, hT⟩ := isNoetherian_submodule.mp this (I.restrictScalars R ⊓ M) inf_le_right
  refine ⟨insert (HolGerm.mk G hG) T, le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxT
    · exact hGI
    · have : x ∈ I.restrictScalars R ⊓ M := hT ▸ Submodule.subset_span hxT
      exact this.1
  · intro h hhI
    obtain ⟨hf, hhf, rfl⟩ := HolGerm.exists_eq_mk h
    obtain ⟨q, hq, r, hr, heq⟩ := hdiv G hG d u hu hu0 hGu hf hhf
    set rem : S := ∑ k ∈ Finset.range d,
      HolGerm.ofFst (HolGerm.mk (r k) (hr k)) * HolGerm.lastCoord ^ k with hrem
    have hsnd : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ (fun x : E × ℂ => x.2) x :=
      Eventually.of_forall fun _ => differentiableAt_snd
    have hterm : ∀ k, ∀ᶠ x in 𝓝 (0 : E × ℂ),
        DifferentiableAt ℂ (fun x : E × ℂ => r k x.1 * x.2 ^ k) x := fun k =>
      eventually_differentiableAt_mul
        (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) (hr k))
        (eventually_differentiableAt_pow hsnd k)
    have hremmk : rem = HolGerm.mk (fun x : E × ℂ => ∑ k ∈ Finset.range d, r k x.1 * x.2 ^ k)
        (eventually_differentiableAt_sum _ hterm) := by
      rw [HolGerm.mk_sum (Finset.range d) (fun k (x : E × ℂ) => r k x.1 * x.2 ^ k) hterm]
      rfl
    have hdecomp : HolGerm.mk hf hhf = HolGerm.mk q hq * HolGerm.mk G hG + rem := by
      rw [hremmk, ← HolGerm.mk_mul, ← HolGerm.mk_add, HolGerm.mk_eq_mk_iff]
      exact heq
    have hremM : rem ∈ M := by
      refine Submodule.sum_mem _ fun k hk => ?_
      have : HolGerm.ofFst (HolGerm.mk (r k) (hr k)) * HolGerm.lastCoord ^ k =
          HolGerm.mk (r k) (hr k) • (HolGerm.lastCoord ^ k : S) := by
        rw [Algebra.smul_def]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, by simpa using hk, rfl⟩)
    have hremI : rem ∈ I := by
      have : rem = HolGerm.mk hf hhf - HolGerm.mk q hq * HolGerm.mk G hG := by
        rw [hdecomp]; ring
      rw [this]
      exact I.sub_mem hhI (I.mul_mem_left _ hGI)
    have hremT : rem ∈ Submodule.span R (T : Set S) := hT ▸ ⟨hremI, hremM⟩
    have hremT' : rem ∈ Ideal.span (insert (HolGerm.mk G hG) (T : Set S)) :=
      (Ideal.span_mono (Set.subset_insert _ _))
        (Submodule.span_le_restrictScalars R S (T : Set S) hremT)
    rw [Finset.coe_insert, hdecomp]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      hremT'

/-- **Rückert's basis theorem, induction step.**  If `𝒪_{E,0}` is Noetherian and Weierstrass
division holds on `E × ℂ`, then `𝒪_{E×ℂ,0}` is Noetherian. -/
theorem isNoetherianRing_prod_of_division [IsNoetherianRing (HolGerm E)]
    (hdiv : GermWeierstrassDivision E) : IsNoetherianRing (HolGerm (E × ℂ)) := by
  rw [isNoetherianRing_iff, isNoetherian_def]
  intro I
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  obtain ⟨g, hgI, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨G, hG, rfl⟩ := HolGerm.exists_eq_mk g
  have hne : ¬ G =ᶠ[𝓝 0] 0 := fun h =>
    hg0 (by rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]; exact h)
  obtain ⟨A, d, u, hu, hu0, hAu⟩ :=
    exists_regular_continuousLinearEquiv hG hne (e := ((0 : E), (1 : ℂ))) (by simp)
  set φ := HolGerm.comapEquiv A
  have hGA := eventually_differentiableAt_comp_clm (A : E × ℂ →L[ℂ] E × ℂ) hG
  have hmem : HolGerm.mk (G ∘ A) hGA ∈
      Ideal.map (φ : HolGerm (E × ℂ) →+* HolGerm (E × ℂ)) I := by
    rw [← HolGerm.comapEquiv_mk A G hG]
    exact Ideal.mem_map_of_mem _ hgI
  have hreg : ∀ᶠ t in 𝓝 (0 : ℂ), (G ∘ A) (0, t) = t ^ d * u t := by
    filter_upwards [hAu] with t ht
    have e : t • ((0 : E), (1 : ℂ)) = ((0 : E), t) := by
      ext <;> simp
    rw [e] at ht
    exact ht
  have hfg := ideal_fg_of_regular hdiv _ hGA hmem hu hu0 hreg
  have := Ideal.FG.map hfg (φ.symm : HolGerm (E × ℂ) →+* HolGerm (E × ℂ))
  rwa [Ideal.map_of_equiv] at this

end

/-- **Weierstrass division for holomorphic germs** on `E × ℂ`, from the parametric Taylor
division (`Pending.LastVariableTaylorDivision`) and the Neumann series
(`Pending.WeierstrassDivisionAbstract`). -/
theorem germWeierstrassDivision (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    GermWeierstrassDivision E := by
  intro G hG d u hu hu0 hGu h hh
  exact exists_weierstrass_division_of_taylorDivision lastQuot lastCoeff
    (fun _ _ _ _ hρ hρR hh k => differentiableOn_lastCoeff hρ hρR hh k)
    (fun _ _ _ _ hρ hρR hh d => differentiableOn_lastQuot hρ hρR hh d)
    (fun _ _ _ _ hρ hρR hh d => eq_lastQuot_mul_add hρ hρR hh d)
    (fun _ _ _ _ _ hρ hρR hh hM k => norm_lastCoeff_le hρ hρR hh hM k)
    (fun d _ _ hρ hρR => exists_norm_lastQuot_le d hρ hρR) hG hu hu0 hGu hh

/-- The splitting `ℂ^{n+1} ≅ ℂⁿ × ℂ` off the last coordinate. -/
noncomputable def euclideanSnocCLE (n : ℕ) :
    EuclideanSpace ℂ (Fin (n + 1)) ≃L[ℂ] EuclideanSpace ℂ (Fin n) × ℂ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => (WithLp.toLp 2 fun i => x i.castSucc, x (Fin.last n))
      invFun := fun q => WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (fun i => q.1 i) q.2)
      map_add' := fun x y => by ext i <;> simp
      map_smul' := fun a x => by ext i <;> simp
      left_inv := fun x => by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      right_inv := fun q => by ext i <;> simp }

/-- **The ring of holomorphic germs at a point of `ℂⁿ` is Noetherian.** -/
theorem isNoetherianRing_holGerm_euclidean (n : ℕ) :
    IsNoetherianRing (HolGerm (EuclideanSpace ℂ (Fin n))) := by
  induction n with
  | zero => exact isNoetherianRing_holGerm_of_subsingleton
  | succ n ih =>
      have := isNoetherianRing_prod_of_division
        (germWeierstrassDivision (EuclideanSpace ℂ (Fin n)))
      exact isNoetherianRing_of_ringEquiv _ (HolGerm.comapEquiv (euclideanSnocCLE n))

end SGPT.Foundations.Analysis.Pending
