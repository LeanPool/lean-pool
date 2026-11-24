/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.EnergyForm
public import LeanPool.CutoffRigidity.Friedrichs.SemigroupDerivative
public import LeanPool.CutoffRigidity.Friedrichs.SemigroupPowers

/-! # Friedrichs resolvents `R_λ` for all `λ > 0` and the canonical semigroup of a `FormData`

`S.R` is the resolvent at `λ = 1`; `S.resolvent λ := resolventLam S.R λ` is the resolvent for
every `λ > 0` (obtained by the functional calculus, `r ↦ r / (1 + (λ-1) r)`).  We prove the
properties of the brief: self-adjoint, nonnegative, injective, range in the form domain `Q`,
`R_λ (λ f + A f) = f` on `D`, the weak equation `E(R_λ g, φ) + λ⟪R_λ g, φ⟫ = ⟪g, φ⟫` for `φ ∈ Q`,
and `‖R_λ‖ ≤ 1/λ`.  The semigroup `S.semigroup t := cfcSemigroup S.R t` is then available with
all the properties of `FunctionalCalculusSemigroup`/`SemigroupDerivative`.
-/

@[expose] public section

open Filter Topology Set
open scoped NNReal InnerProductSpace

namespace CutoffRigidity.Riemann.Diff


namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

lemma R_unitOp : UnitOp S.R :=
  ⟨S.R_isSelfAdjoint, S.R_nonneg, S.R_le_one⟩

/-- The Friedrichs resolvent `(λ + A_F)⁻¹`, `λ > 0`. -/
noncomputable def resolvent (lam : ℝ) : H →L[ℝ] H := resolventLam S.R lam

/-- The canonical semigroup `e^{-t A_F}`. -/
noncomputable def semigroup (t : ℝ≥0) : H →L[ℝ] H := cfcSemigroup S.R t

lemma resolvent_one : S.resolvent 1 = S.R := resolventLam_one S.R_unitOp

lemma one_div_den_continuousOn {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (fun r : ℝ => 1 / (1 + (lam - 1) * r)) (Icc 0 1) := by
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro r hr; exact (den_pos hlam hr).ne'

/-- `R_λ = R S_λ` with `S_λ = (1 + (λ - 1) R)⁻¹`. -/
lemma resolvent_eq_R_mul {lam : ℝ} (hlam : 0 < lam) :
    S.resolvent lam = S.R * cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R := by
  have hU := S.R_unitOp
  have h := hU.rcfc_mul (f := id) (g := fun r : ℝ => 1 / (1 + (lam - 1) * r)) continuousOn_id
    (one_div_den_continuousOn hlam)
  rw [hU.rcfc_id] at h
  rw [← h]
  unfold resolvent resolventLam
  apply hU.rcfc_congr
  intro r _
  simp [resFun, div_eq_mul_inv]

lemma resolvent_mem_Q {lam : ℝ} (hlam : 0 < lam) (g : H) : S.resolvent lam g ∈ S.Q := by
  rw [resolvent_eq_R_mul S hlam, mul_apply_eq_comp]
  exact S.R_mem_Q _

lemma M_mul_inv {lam : ℝ} (hlam : 0 < lam) :
    ((lam - 1) • S.R + 1) * cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R = 1 := by
  have hU := S.R_unitOp
  have hc : ContinuousOn (fun r : ℝ => (lam - 1) * r + 1) (Icc 0 1) := by fun_prop
  rw [resolvent_denominator_eq_cfc hU lam, ← hU.rcfc_mul hc (one_div_den_continuousOn hlam),
    ← hU.rcfc_one]
  apply hU.rcfc_congr
  intro r hr
  have h := (den_pos hlam hr).ne'
  have : (lam - 1) * r + 1 = 1 + (lam - 1) * r := by ring
  rw [this]
  field_simp

/-- The resolvent identity on the domain: `R_λ (λ f + A f) = f`. -/
theorem resolvent_apply_D {lam : ℝ} (hlam : 0 < lam) (f : S.D) :
    S.resolvent lam (lam • (f : H) + S.A f) = f := by
  have hU := S.R_unitOp
  have hf : S.R ((f : H) + S.A f) = f := S.R_resolvent ⟨f, f.2⟩
  have h1 : lam • (f : H) + S.A f = ((lam - 1) • S.R + 1) ((f : H) + S.A f) := by
    simp only [add_apply, smul_apply, one_apply_eq_self, hf]
    rw [sub_smul, one_smul]; abel
  have h2 := congrArg (fun T => T ((f : H) + S.A f)) (resolventLam_mul hU hlam)
  simp only [mul_apply_eq_comp, hf] at h2
  rw [h1]
  exact h2

/-- Weak equation: `E(R_λ g, φ) + λ ⟪R_λ g, φ⟫ = ⟪g, φ⟫` for `φ ∈ Q`. -/
theorem E_resolvent {lam : ℝ} (hlam : 0 < lam) (g : H) (φ : S.Q) :
    S.E ⟨S.resolvent lam g, S.resolvent_mem_Q hlam g⟩ φ +
      lam * inner ℝ (S.resolvent lam g) (φ : H) = inner ℝ g (φ : H) := by
  set Sl := cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R with hSl
  set h : H := Sl g with hh
  have hw : S.resolvent lam g = S.R h := by
    rw [resolvent_eq_R_mul S hlam]; rfl
  have hE := S.E_R h φ
  have e1 : (⟨S.resolvent lam g, S.resolvent_mem_Q hlam g⟩ : S.Q) = ⟨S.R h, S.R_mem_Q h⟩ :=
    Subtype.ext hw
  rw [e1, hw]
  have hMg : ((lam - 1) • S.R + 1) h = g := by
    have := congrArg (fun T => T g) (M_mul_inv S hlam)
    simp only [mul_apply_eq_comp, add_apply, smul_apply, one_apply_eq_self] at this
    simp only [add_apply, smul_apply, one_apply_eq_self]
    exact this
  have h3 : inner ℝ g (φ : H) = inner ℝ h (φ : H) + (lam - 1) * inner ℝ (S.R h) (φ : H) := by
    rw [← hMg]
    simp only [add_apply, smul_apply, one_apply_eq_self, inner_add_left, inner_smul_left]
    simp only [RCLike.conj_to_real]; ring
  rw [h3]
  linarith

lemma resolvent_isSelfAdjoint (lam : ℝ) : IsSelfAdjoint (S.resolvent lam) :=
  resolventLam_isSelfAdjoint lam

lemma resolvent_inner_nonneg {lam : ℝ} (hlam : 0 < lam) (u : H) :
    0 ≤ inner ℝ (S.resolvent lam u) u :=
  resolventLam_inner_nonneg S.R_unitOp hlam u

lemma norm_resolvent_le {lam : ℝ} (hlam : 0 < lam) : ‖S.resolvent lam‖ ≤ 1 / lam :=
  norm_resolventLam_le S.R_unitOp hlam

lemma resolvent_injective {lam : ℝ} (hlam : 0 < lam) : Function.Injective (S.resolvent lam) := by
  have hU := S.R_unitOp
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hcomm : Commute (S.resolvent lam) S.R := by
    have := cfc_commute_cfc (resFun lam) id S.R
    rwa [hU.rcfc_id] at this
  have hcomm2 : Commute (S.resolvent lam) ((lam - 1) • S.R + 1) :=
    (hcomm.smul_right _).add_right (Commute.one_right _)
  have h1 := resolventLam_mul hU hlam
  have h2 : S.R u = 0 := by
    calc S.R u = (S.resolvent lam * ((lam - 1) • S.R + 1)) u := by
          change _ = (resolventLam S.R lam * ((lam - 1) • S.R + 1)) u
          rw [h1]
      _ = (((lam - 1) • S.R + 1) * S.resolvent lam) u := by rw [hcomm2.eq]
      _ = 0 := by rw [mul_apply_eq_comp]; simp [hu]
  exact S.R_injective (by rw [h2, map_zero])

/-- The Friedrichs resolvent exists for each positive parameter. -/
theorem exists_resolvent {lam : ℝ} (hlam : 0 < lam) :
    ∃ (R : H →L[ℝ] H) (hQ : ∀ g, R g ∈ S.Q),
      IsSelfAdjoint R ∧ (∀ u, 0 ≤ inner ℝ (R u) u) ∧ Function.Injective R ∧
      (∀ f : S.D, R (lam • (f : H) + S.A f) = f) ∧
      (∀ (g : H) (φ : S.Q), S.E ⟨R g, hQ g⟩ φ + lam * inner ℝ (R g) (φ : H) =
        inner ℝ g (φ : H)) ∧ ‖R‖ ≤ 1 / lam :=
  ⟨S.resolvent lam, S.resolvent_mem_Q hlam, S.resolvent_isSelfAdjoint lam,
    S.resolvent_inner_nonneg hlam, S.resolvent_injective hlam, S.resolvent_apply_D hlam,
    S.E_resolvent hlam, S.norm_resolvent_le hlam⟩

/-- Resolvent identity. -/
lemma resolvent_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    S.resolvent a - S.resolvent b = (b - a) • (S.resolvent a * S.resolvent b) :=
  resolventLam_sub S.R_unitOp ha hb

/-! ### The semigroup -/

lemma semigroup_zero : S.semigroup 0 = 1 := cfcSemigroup_zero S.R_unitOp
lemma semigroup_add (s t : ℝ≥0) : S.semigroup (s + t) = S.semigroup s * S.semigroup t :=
  cfcSemigroup_add S.R_unitOp s t
lemma norm_semigroup_le (t : ℝ≥0) : ‖S.semigroup t‖ ≤ 1 := norm_cfcSemigroup_le_one S.R_unitOp t
lemma semigroup_isSelfAdjoint (t : ℝ≥0) : IsSelfAdjoint (S.semigroup t) :=
  cfcSemigroup_isSelfAdjoint t
lemma continuous_semigroup_apply (u : H) : Continuous fun t : ℝ≥0 => S.semigroup t u :=
  continuous_cfcSemigroup_apply S.R_unitOp S.R_injective u

/-- Euler limit. -/
theorem tendsto_euler {t : ℝ≥0} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => ((((n + 1 : ℝ) / t) • S.resolvent ((n + 1 : ℝ) / t)) ^ (n + 1)))
      atTop (𝓝 (S.semigroup t)) := by
  have := tendsto_eulerOp S.R_unitOp t ht
  exact this

/-- If `R u = (1 + c)⁻¹ u` (i.e. `u ∈ D(A_F)` with `A_F u = c u`), then `T_t u = e^{-ct} u`. -/
theorem semigroup_eigen {c : ℝ} (hc : 0 ≤ c) {u : H} (hu : S.R u = (1 + c)⁻¹ • u) (t : ℝ≥0) :
    S.semigroup t u = Real.exp (-c * t) • u :=
  cfcSemigroup_eigen S.R_unitOp hc hu t

/-- Closed convex cones/sets invariant under all `λ R_λ` are invariant under the semigroup. -/
theorem semigroup_mapsTo (C : Set H) (hC : IsClosed C)
    (hres : ∀ lam : ℝ, 0 < lam → ∀ x ∈ C, (lam • S.resolvent lam) x ∈ C)
    (t : ℝ≥0) {x : H} (hx : x ∈ C) : S.semigroup t x ∈ C :=
  cfcSemigroup_mapsTo S.R_unitOp C hC hres t hx

/-- Derivative on `D(A_F)`: `d/ds T_s (R g) = -T_s (g - R g)`, `s > 0`. -/
theorem hasDerivAt_semigroup {t : ℝ} (ht : 0 < t) (g : H) :
    HasDerivAt (fun s : ℝ => S.semigroup s.toNNReal (S.R g))
      (-(S.semigroup t.toNNReal (g - S.R g))) t :=
  hasDerivAt_cfcSemigroup_apply S.R_unitOp ht g

/-- Dynkin/Duhamel formula. -/
theorem semigroup_integral (g : H) (t : ℝ≥0) :
    S.semigroup t (S.R g) - S.R g = -∫ s in (0 : ℝ)..t, S.semigroup s.toNNReal (g - S.R g) :=
  cfcSemigroup_integral S.R_unitOp S.R_injective g t

/-- For `f ∈ D`, `f = R (f + A f)` and `T_t f - f = -∫₀ᵗ T_s (R-complement)`;  with
`g = f + A f`: `g - R g = A f`. -/
theorem semigroup_integral_D (f : S.D) (t : ℝ≥0) :
    S.semigroup t (f : H) - f = -∫ s in (0 : ℝ)..t, S.semigroup s.toNNReal (S.A f) := by
  have hf : S.R ((f : H) + S.A f) = f := S.R_resolvent ⟨f, f.2⟩
  have h := S.semigroup_integral ((f : H) + S.A f) t
  rw [hf] at h
  have e : (f : H) + S.A f - f = S.A f := by abel
  rw [e] at h
  exact h

/-! ### Weak characterization of the Friedrichs operator -/

lemma E1_sub_left (a b c : S.Q) : S.E1 (a - b) c = S.E1 a c - S.E1 b c := by
  simp [E1, map_sub, inner_sub_left]

lemma E1_self_eq_zero {v : S.Q} (h : S.E1 v v = 0) : v = 0 := by
  have : S.qEquiv.symm v = 0 := inner_self_eq_zero.mp h
  simpa using this

/-- Uniqueness in the weak formulation: if `u ∈ Q` and `E₁(u, φ) = ⟪g, φ⟫` for all `φ ∈ Q`
then `u = R g` (`u ∈ D(A_F)` and `u + A_F u = g`). -/
theorem eq_R_of_weak {u : H} (hu : u ∈ S.Q) (g : H)
    (h : ∀ φ : S.Q, S.E1 ⟨u, hu⟩ φ = inner ℝ g (φ : H)) : u = S.R g := by
  set v : S.Q := ⟨u, hu⟩ - ⟨S.R g, S.R_mem_Q g⟩ with hv
  have h0 : ∀ φ : S.Q, S.E1 v φ = 0 := fun φ => by
    rw [hv, E1_sub_left, h φ, S.E1_R g φ, sub_self]
  have : v = 0 := S.E1_self_eq_zero (h0 v)
  have h2 : (v : H) = 0 := by rw [this]; rfl
  have h3 : (v : H) = u - S.R g := rfl
  rw [h3] at h2
  exact sub_eq_zero.mp h2

/-- Weak formulation for all `λ > 0`: `E(u, φ) + λ⟪u, φ⟫ = ⟪g, φ⟫ ∀ φ ∈ Q` forces `u = R_λ g`. -/
theorem eq_resolvent_of_weak {lam : ℝ} (hlam : 0 < lam) {u : H} (hu : u ∈ S.Q) (g : H)
    (h : ∀ φ : S.Q, S.E ⟨u, hu⟩ φ + lam * inner ℝ u (φ : H) = inner ℝ g (φ : H)) :
    u = S.resolvent lam g := by
  have h1 : ∀ φ : S.Q, S.E1 ⟨u, hu⟩ φ = inner ℝ (g - (lam - 1) • u) (φ : H) := by
    intro φ
    have := h φ
    rw [inner_sub_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    unfold E at this
    simp only at this
    linarith
  have h2 := S.eq_R_of_weak hu _ h1
  -- `u = R h'`, `h' = g - (λ-1) u`, so `h' + (λ-1) R h' = g`
  set h' : H := g - (lam - 1) • u with hh'
  have hMh : ((lam - 1) • S.R + 1) h' = g := by
    simp only [add_apply, smul_apply, one_apply_eq_self]
    rw [← h2, hh']; abel
  have hinv : h' = cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R g := by
    have hU := S.R_unitOp
    have hc : Commute (cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R) S.R := by
      have := cfc_commute_cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) id S.R
      rwa [hU.rcfc_id] at this
    have hc2 : Commute (cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R)
        ((lam - 1) • S.R + 1) := (hc.smul_right _).add_right (Commute.one_right _)
    have h3 : cfc (fun r : ℝ => 1 / (1 + (lam - 1) * r)) S.R * ((lam - 1) • S.R + 1) = 1 := by
      rw [hc2.eq]; exact M_mul_inv S hlam
    have := congrArg (fun T => T h') h3
    simp only [mul_apply_eq_comp, one_apply_eq_self, hMh] at this
    exact this.symm
  rw [h2, hinv, resolvent_eq_R_mul S hlam]
  rfl

/-- Weak eigenfunctions of the form give eigenvectors of `R`: if `u ∈ Q` and
`E(u, φ) = c ⟪u, φ⟫` for all `φ ∈ Q` (`1 + c ≠ 0`), then `R u = (1 + c)⁻¹ u`. -/
theorem R_eigen_of_weak {c : ℝ} (hc : 1 + c ≠ 0) {u : H} (hu : u ∈ S.Q)
    (h : ∀ φ : S.Q, S.E ⟨u, hu⟩ φ = c * inner ℝ u (φ : H)) : S.R u = (1 + c)⁻¹ • u := by
  have h1 : ∀ φ : S.Q, S.E1 ⟨u, hu⟩ φ = inner ℝ ((1 + c) • u) (φ : H) := by
    intro φ
    rw [inner_smul_left]
    simp only [RCLike.conj_to_real]
    have := h φ
    unfold E at this
    simp only at this
    linarith
  have h2 := S.eq_R_of_weak hu _ h1
  rw [map_smul] at h2
  calc S.R u = (1 + c)⁻¹ • ((1 + c) • S.R u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = (1 + c)⁻¹ • u := by rw [← h2]

/-! ### Domain and action of the Friedrichs generator -/

/-- Domain of the Friedrichs generator `A_F = R⁻¹ - 1`. -/
noncomputable abbrev domAF : Submodule ℝ H := LinearMap.range S.R.toLinearMap

/-- `A_F` on its domain: `A_F (R g) = g - R g`. -/
noncomputable def AF : S.domAF →ₗ[ℝ] H :=
  (LinearMap.id - S.R.toLinearMap) ∘ₗ
    (LinearEquiv.ofInjective S.R.toLinearMap S.R_injective).symm.toLinearMap

lemma AF_R (g : H) : S.AF ⟨S.R g, ⟨g, rfl⟩⟩ = g - S.R g := by
  unfold AF
  have : (LinearEquiv.ofInjective S.R.toLinearMap S.R_injective).symm ⟨S.R g, ⟨g, rfl⟩⟩ = g := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

lemma D_subset_domAF (f : S.D) : (f : H) ∈ S.domAF :=
  ⟨(f : H) + S.A f, S.R_resolvent ⟨f, f.2⟩⟩

lemma AF_extends (f : S.D) : S.AF ⟨f, S.D_subset_domAF f⟩ = S.A f := by
  have h := S.R_resolvent ⟨f, f.2⟩
  have h' : S.R ((f : H) + S.A f) = f := h
  have e : (⟨(f : H), S.D_subset_domAF f⟩ : S.domAF) =
      ⟨S.R ((f : H) + S.A f), ⟨(f : H) + S.A f, rfl⟩⟩ := Subtype.ext h'.symm
  rw [e, AF_R, h']; abel

/-- Smoothing: for `t > 0`, `T_t = R^k B` (so `T_t H ⊆ D(A_F^{k-1})`). -/
theorem semigroup_eq_pow_mul {t : ℝ≥0} (ht : t ≠ 0) (k : ℕ) :
    ∃ B : H →L[ℝ] H, S.semigroup t = S.R ^ k * B :=
  ⟨_, cfcSemigroup_eq_pow_mul S.R_unitOp ht k⟩

/-- For `t > 0`, `T_t u` lies in the form domain `Q`. -/
theorem semigroup_apply_mem_Q {t : ℝ≥0} (ht : t ≠ 0) (u : H) : S.semigroup t u ∈ S.Q := by
  obtain ⟨B, hB⟩ := S.semigroup_eq_pow_mul ht 1
  rw [hB, pow_one, mul_apply_eq_comp]
  exact S.R_mem_Q _

end FormData

end CutoffRigidity.Riemann.Diff
