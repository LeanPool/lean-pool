/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import LeanPool.CutoffRigidity.SymmetricOperatorDenseRange
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Friedrichs construction on an abstract real Hilbert space

`FormData H`: a densely defined, symmetric, nonnegative operator `A : D → H`.  The energy
inner product `⟪f,g⟫₁ = ⟪f,g⟫ + ⟪A f,g⟫` makes `D` a pre-Hilbert space; its completion `K` maps
to `H` by the continuous extension `ι` of the inclusion.  Closability is automatic from
symmetry: `ι` is injective (`FormData.ι_injective`).  The form domain is `Q = range ι`, the
energy is `E(u,v) = ⟪ι⁻¹u, ι⁻¹v⟫_K - ⟪u,v⟫`, and the Friedrichs resolvent is `R = ι ι†`.
-/

@[expose] public section

open scoped InnerProductSpace
open Filter Topology

namespace CutoffRigidity.Riemann.Diff

/-- Densely defined symmetric nonnegative operator on a real Hilbert space. -/
structure FormData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Domain. -/
  D : Submodule ℝ H
  dense : Dense (D : Set H)
  /-- The operator. -/
  A : D →ₗ[ℝ] H
  symm : ∀ f g : D, inner ℝ (A f) (g : H) = inner ℝ (f : H) (A g)
  nonneg : ∀ f : D, 0 ≤ inner ℝ (A f) (f : H)

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : FormData H)

/-- The domain `D` with the energy inner product. -/
def Dom : Type _ := S.D

instance : AddCommGroup S.Dom := inferInstanceAs (AddCommGroup S.D)
instance : Module ℝ S.Dom := inferInstanceAs (Module ℝ S.D)

/-- The inclusion `D → H` as a linear map. -/
def emb : S.Dom →ₗ[ℝ] H := S.D.subtype

/-- `A` on `Dom`. -/
def opA : S.Dom →ₗ[ℝ] H := S.A

lemma emb_apply (f : S.Dom) : S.emb f = ((show S.D from f) : H) := rfl
lemma opA_apply (f : S.Dom) : S.opA f = S.A (show S.D from f) := rfl

lemma symm' (f g : S.Dom) : inner ℝ (S.opA f) (S.emb g) = inner ℝ (S.emb f) (S.opA g) :=
  S.symm f g

lemma nonneg' (f : S.Dom) : 0 ≤ inner ℝ (S.opA f) (S.emb f) := S.nonneg f

/-- The energy inner product. -/
@[instance_reducible]
noncomputable def innerCore : InnerProductSpace.Core ℝ S.Dom where
  inner f g := inner ℝ (S.emb f) (S.emb g) + inner ℝ (S.opA f) (S.emb g)
  conj_inner_symm f g := by
    change (starRingEnd ℝ) (inner ℝ (S.emb g) (S.emb f) + inner ℝ (S.opA g) (S.emb f)) =
      inner ℝ (S.emb f) (S.emb g) + inner ℝ (S.opA f) (S.emb g)
    simp only [RCLike.conj_to_real]
    rw [real_inner_comm (S.emb g) (S.emb f), S.symm' g f, real_inner_comm (S.opA f) (S.emb g)]
  re_inner_nonneg f := by
    change 0 ≤ inner ℝ (S.emb f) (S.emb f) + inner ℝ (S.opA f) (S.emb f)
    exact add_nonneg real_inner_self_nonneg (S.nonneg' f)
  add_left f g h := by
    change inner ℝ (S.emb (f + g)) (S.emb h) + inner ℝ (S.opA (f + g)) (S.emb h) =
      (inner ℝ (S.emb f) (S.emb h) + inner ℝ (S.opA f) (S.emb h)) +
      (inner ℝ (S.emb g) (S.emb h) + inner ℝ (S.opA g) (S.emb h))
    rw [map_add, map_add, inner_add_left, inner_add_left]; ring
  smul_left f g c := by
    change inner ℝ (S.emb (c • f)) (S.emb g) + inner ℝ (S.opA (c • f)) (S.emb g) =
      (starRingEnd ℝ) c * (inner ℝ (S.emb f) (S.emb g) + inner ℝ (S.opA f) (S.emb g))
    rw [map_smul, map_smul, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]; ring
  definite f hf := by
    have h1 : inner ℝ (S.emb f) (S.emb f) + inner ℝ (S.opA f) (S.emb f) = 0 := hf
    have h2 : inner ℝ (S.emb f) (S.emb f) = 0 := by
      have := real_inner_self_nonneg (x := S.emb f)
      have := S.nonneg' f
      linarith
    have h3 : S.emb f = 0 := inner_self_eq_zero.mp h2
    have : (show S.D from f) = 0 := Subtype.ext h3
    exact this

noncomputable instance : NormedAddCommGroup S.Dom := S.innerCore.toNormedAddCommGroup
noncomputable instance : InnerProductSpace ℝ S.Dom := InnerProductSpace.ofCore S.innerCore.toCore

lemma inner_dom (f g : S.Dom) :
    inner ℝ f g = inner ℝ (S.emb f) (S.emb g) + inner ℝ (S.opA f) (S.emb g) := rfl

section Completion

variable [CompleteSpace H]

/-- The energy Hilbert space: completion of `D` for the energy norm. -/
abbrev K : Type _ := UniformSpace.Completion S.Dom

omit [CompleteSpace H] in
lemma norm_emb_le (f : S.Dom) : ‖S.emb f‖ ≤ ‖f‖ := by
  have h : ‖f‖ ^ 2 = ‖S.emb f‖ ^ 2 + inner ℝ (S.opA f) (S.emb f) := by
    rw [← real_inner_self_eq_norm_sq, inner_dom, real_inner_self_eq_norm_sq]
  have := S.nonneg' f
  apply le_of_sq_le_sq _ (norm_nonneg _)
  linarith

/-- The extension `ι : K → H` of the inclusion `D → H` (a contraction). -/
noncomputable def ι : S.K →L[ℝ] H :=
  S.emb.extendOfNorm (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := S.Dom)).toLinearMap

lemma ι_coe (f : S.Dom) : S.ι (f : S.K) = S.emb f := by
  have h := LinearMap.extendOfNorm_eq (f := S.emb)
    (e := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := S.Dom)).toLinearMap)
    (UniformSpace.Completion.denseRange_coe) ⟨1, fun x => by
      simpa using S.norm_emb_le x⟩ f
  exact h

lemma norm_ι_le (x : S.K) : ‖S.ι x‖ ≤ ‖x‖ := by
  have := LinearMap.norm_extendOfNorm_apply_le (f := S.emb)
    (e := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := S.Dom)).toLinearMap)
    (UniformSpace.Completion.denseRange_coe) 1 (fun f => by
      simpa using S.norm_emb_le f) x
  unfold ι
  simpa using this

lemma opNorm_ι_le : ‖S.ι‖ ≤ 1 := S.ι.opNorm_le_bound zero_le_one (fun x => by
  simpa using S.norm_ι_le x)

/-- Key identity: `⟪g, x⟫_K = ⟪g + A g, ι x⟫_H` for `g ∈ D`, `x ∈ K`. -/
lemma inner_coe_left (g : S.Dom) (x : S.K) :
    inner ℝ (g : S.K) x = inner ℝ (S.emb g + S.opA g) (S.ι x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [UniformSpace.Completion.inner_coe, S.ι_coe, inner_dom, inner_add_left]

lemma ι_injective : Function.Injective S.ι := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h : ∀ g : S.Dom, inner ℝ (g : S.K) x = 0 := fun g => by
    rw [S.inner_coe_left, hx, inner_zero_right]
  have : inner ℝ x x = 0 := by
    have hc : Continuous fun y : S.K => inner ℝ y x := by fun_prop
    have hz : ∀ y : S.K, inner ℝ y x = 0 := by
      intro y
      exact UniformSpace.Completion.induction_on y (isClosed_eq hc continuous_const) h
    exact hz x
  exact inner_self_eq_zero.mp this

/-- Form domain `Q = ran ι ⊆ H`. -/
noncomputable def Q : Submodule ℝ H := LinearMap.range S.ι.toLinearMap

lemma mem_Q_iff (u : H) : u ∈ S.Q ↔ ∃ x : S.K, S.ι x = u := Iff.rfl

lemma emb_mem_Q (f : S.Dom) : S.emb f ∈ S.Q := ⟨(f : S.K), S.ι_coe f⟩

lemma D_subset_Q (f : H) (hf : f ∈ S.D) : f ∈ S.Q := S.emb_mem_Q ⟨f, hf⟩

/-- `K ≃ Q`. -/
noncomputable def qEquiv : S.K ≃ₗ[ℝ] S.Q :=
  LinearEquiv.ofInjective S.ι.toLinearMap S.ι_injective

lemma qEquiv_apply (x : S.K) : ((S.qEquiv x : S.Q) : H) = S.ι x := rfl

/-- Energy plus `L²` inner product: `E₁(u,v) = E(u,v) + ⟪u,v⟫`. -/
noncomputable def E1 (u v : S.Q) : ℝ := inner ℝ (S.qEquiv.symm u) (S.qEquiv.symm v)

/-- The closed energy form `E(u,v) = ⟪ι⁻¹u, ι⁻¹v⟫_K - ⟪u,v⟫`. -/
noncomputable def E (u v : S.Q) : ℝ := S.E1 u v - inner ℝ (u : H) (v : H)

lemma E1_eq (x y : S.K) : S.E1 (S.qEquiv x) (S.qEquiv y) = inner ℝ x y := by
  simp [E1]

lemma E_eq (x y : S.K) :
    S.E (S.qEquiv x) (S.qEquiv y) = inner ℝ x y - inner ℝ (S.ι x) (S.ι y) := by
  simp [E, E1_eq, qEquiv_apply]

/-- The energy on `D` is the quadratic form of `A`. -/
lemma E_emb (f g : S.Dom) :
    S.E ⟨S.emb f, S.emb_mem_Q f⟩ ⟨S.emb g, S.emb_mem_Q g⟩ = inner ℝ (S.opA f) (S.emb g) := by
  have h1 : S.qEquiv (f : S.K) = ⟨S.emb f, S.emb_mem_Q f⟩ := Subtype.ext (by
    rw [qEquiv_apply, ι_coe])
  have h2 : S.qEquiv (g : S.K) = ⟨S.emb g, S.emb_mem_Q g⟩ := Subtype.ext (by
    rw [qEquiv_apply, ι_coe])
  rw [← h1, ← h2, E_eq, UniformSpace.Completion.inner_coe, ι_coe, ι_coe, inner_dom]
  ring

lemma E_nonneg (u : S.Q) : 0 ≤ S.E u u := by
  obtain ⟨x, rfl⟩ := S.qEquiv.surjective u
  rw [E_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have := S.norm_ι_le x
  have h0 := norm_nonneg (S.ι x)
  nlinarith

/-- The Friedrichs resolvent `R = ι ι†` (at spectral parameter `1`). -/
noncomputable def R : H →L[ℝ] H := S.ι.comp (ContinuousLinearMap.adjoint S.ι)

lemma R_apply (g : H) : S.R g = S.ι (ContinuousLinearMap.adjoint S.ι g) := rfl

lemma R_mem_Q (g : H) : S.R g ∈ S.Q := ⟨_, rfl⟩

lemma inner_R (u v : H) : inner ℝ (S.R u) v = inner ℝ (ContinuousLinearMap.adjoint S.ι u)
    (ContinuousLinearMap.adjoint S.ι v) := by
  rw [R_apply, ← ContinuousLinearMap.adjoint_inner_right]

lemma R_isSelfAdjoint : IsSelfAdjoint S.R := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, R, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

lemma R_nonneg (u : H) : 0 ≤ inner ℝ (S.R u) u := by
  rw [inner_R]; exact real_inner_self_nonneg

lemma norm_adjoint_ι_le (u : H) : ‖ContinuousLinearMap.adjoint S.ι u‖ ≤ ‖u‖ := by
  have h := (ContinuousLinearMap.adjoint S.ι).le_opNorm u
  have h2 : ‖ContinuousLinearMap.adjoint S.ι‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]; exact S.opNorm_ι_le
  nlinarith [norm_nonneg u, norm_nonneg (ContinuousLinearMap.adjoint S.ι u)]

/-- A vector of zero closed energy is fixed by the unit-parameter resolvent. -/
theorem R_apply_of_energy_eq_zero (u : S.Q) (hu : S.E u u = 0) : S.R (u : H) = u := by
  obtain ⟨v, rfl⟩ := S.qEquiv.surjective u
  rw [E_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, sub_eq_zero] at hu
  have hadj : ContinuousLinearMap.adjoint S.ι (S.ι v) = v := by
    have hnorm := S.norm_adjoint_ι_le (S.ι v)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hdiff : ‖v - ContinuousLinearMap.adjoint S.ι (S.ι v)‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
        hu]
      linarith only [hsq]
    exact (sub_eq_zero.mp (norm_eq_zero.mp ((sq_nonpos_iff _).mp hdiff))).symm
  rw [qEquiv_apply, R_apply, hadj]

lemma R_le_one (u : H) : inner ℝ (S.R u) u ≤ inner ℝ u u := by
  rw [inner_R, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have := S.norm_adjoint_ι_le u
  nlinarith [norm_nonneg u, norm_nonneg (ContinuousLinearMap.adjoint S.ι u)]

lemma norm_R_le : ‖S.R‖ ≤ 1 := by
  calc ‖S.R‖ ≤ ‖S.ι‖ * ‖ContinuousLinearMap.adjoint S.ι‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul S.opNorm_ι_le S.opNorm_ι_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma R_injective : Function.Injective S.R := by
  apply CutoffRigidity.self_comp_adjoint_injective_of_denseRange
  apply S.dense.mono
  intro u hu
  let f : S.Dom := ⟨u, hu⟩
  exact ⟨(f : S.K), S.ι_coe f⟩

/-- `R (f + A f) = f` on the domain. -/
lemma R_resolvent (f : S.Dom) : S.R (S.emb f + S.opA f) = S.emb f := by
  have h : ContinuousLinearMap.adjoint S.ι (S.emb f + S.opA f) = (f : S.K) := by
    apply ext_inner_right ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, S.inner_coe_left]
  rw [R_apply, h, ι_coe]

/-- Weak form of the resolvent equation: `E₁(R g, φ) = ⟪g, φ⟫` for `φ ∈ Q`. -/
lemma E1_R (g : H) (φ : S.Q) : S.E1 ⟨S.R g, S.R_mem_Q g⟩ φ = inner ℝ g (φ : H) := by
  obtain ⟨x, rfl⟩ := S.qEquiv.surjective φ
  have : (⟨S.R g, S.R_mem_Q g⟩ : S.Q) = S.qEquiv (ContinuousLinearMap.adjoint S.ι g) :=
    Subtype.ext (by rw [qEquiv_apply]; rfl)
  rw [this, E1_eq, qEquiv_apply, ContinuousLinearMap.adjoint_inner_left]

lemma E_R (g : H) (φ : S.Q) :
    S.E ⟨S.R g, S.R_mem_Q g⟩ φ + inner ℝ (S.R g) (φ : H) = inner ℝ g (φ : H) := by
  rw [E]; simp only [sub_add_cancel]; exact S.E1_R g φ

/-- Closedness of the form domain in the energy norm: an `E₁`-Cauchy sequence in `Q` converging
in `H` has its limit in `Q` and converges in energy. -/
lemma limit_mem_Q (u : ℕ → S.Q) (v : H)
    (hc : CauchySeq fun n => S.qEquiv.symm (u n)) (hv : Tendsto (fun n => (u n : H)) atTop (𝓝 v)) :
    ∃ w : S.Q, (w : H) = v ∧
      Tendsto (fun n => S.qEquiv.symm (u n)) atTop (𝓝 (S.qEquiv.symm w)) := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have h1 : Tendsto (fun n => S.ι (S.qEquiv.symm (u n))) atTop (𝓝 (S.ι x)) :=
    (S.ι.continuous.tendsto x).comp hx
  have h2 : ∀ n, S.ι (S.qEquiv.symm (u n)) = (u n : H) := fun n => by
    rw [← qEquiv_apply, LinearEquiv.apply_symm_apply]
  simp only [h2] at h1
  have : S.ι x = v := tendsto_nhds_unique h1 hv
  refine ⟨S.qEquiv x, by rw [qEquiv_apply, this], ?_⟩
  simpa using hx

end Completion

end FormData

end CutoffRigidity.Riemann.Diff
