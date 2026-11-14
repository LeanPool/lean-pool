/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module
public import Mathlib.FieldTheory.AlgebraicClosure

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import LeanPool.RoyStrongSix.Roy.Abstract
public import LeanPool.RoyStrongSix.Roy.BaseChange
public import LeanPool.RoyStrongSix.Roy.Theorem1

/-!
# Roy's category, realized as subquotients of a fixed ambient space

Fix `E = ℂ^{d₀} × ℂ^{d₁}` with a finite-dimensional `ℚ`-subspace `Y` and `ℂ`-subspaces
`W ≤ V` with `Y ⊆ V`. A *rational product subspace* is `S = S₀ × S₁` with `S₀` rational over
`Qbar` and `S₁` rational over `ℚ`. The objects of Roy's category reachable from `(E, Y, W, V)` are,
up to isomorphism, the subquotients `T/S` with `S ≤ T` rational product subspaces, carrying the
induced `Y`, `W`, `V`. Kernels keep `S`, cokernels keep `T`, and exact triples are
`(S ≤ M) → (S ≤ T) → (M ≤ T)` (Roy, Proposition 1).

This file defines the admissible system, Roy's functions `a, b, c, d, r, d₁` on it, and proves
Roy's Propositions 2 and 3.
-/

@[expose] public section

namespace LeanPool

open Module Submodule

noncomputable section

namespace StrongSix.Roy

/-- The field `Qbar` of algebraic numbers inside `ℂ`. -/
abbrev Qb := algebraicClosure ℚ ℂ

/-- A rational product subspace `S₀ × S₁` of `ℂ^{d₀} × ℂ^{d₁}`. -/
structure RSub (d0 d1 : ℕ) where
  /-- The additive coordinate subspace, rational over the algebraic numbers. -/
  S0 : Submodule ℂ (Fin d0 → ℂ)
  /-- The multiplicative coordinate subspace, rational over the rationals. -/
  S1 : Submodule ℂ (Fin d1 → ℂ)
  h0 : IsRat Qb S0
  h1 : IsRat ℚ S1

namespace RSub

variable {d0 d1 : ℕ}

@[ext] theorem ext {S T : RSub d0 d1} (h0 : S.S0 = T.S0) (h1 : S.S1 = T.S1) : S = T := by
  cases S; cases T; simp only at h0 h1; subst h0; subst h1; rfl

/-- The underlying `ℂ`-subspace of `E`. -/
def sub (S : RSub d0 d1) : Submodule ℂ (E d0 d1) := S.S0.prod S.S1

instance : LE (RSub d0 d1) := ⟨fun S T => S.S0 ≤ T.S0 ∧ S.S1 ≤ T.S1⟩

theorem le_def {S T : RSub d0 d1} : S ≤ T ↔ S.S0 ≤ T.S0 ∧ S.S1 ≤ T.S1 := Iff.rfl

theorem sub_mono {S T : RSub d0 d1} (h : S ≤ T) : S.sub ≤ T.sub :=
  fun _ hx => ⟨h.1 hx.1, h.2 hx.2⟩

theorem le_refl' (S : RSub d0 d1) : S ≤ S := ⟨le_rfl, le_rfl⟩

theorem le_trans' {S T U : RSub d0 d1} (h1 : S ≤ T) (h2 : T ≤ U) : S ≤ U :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem eq_of_sub_eq {S T : RSub d0 d1} (h : S.sub = T.sub) : S = T := by
  ext x
  · constructor
    · intro hx
      have : ((x, 0) : E d0 d1) ∈ T.sub := h ▸ ⟨hx, S.S1.zero_mem⟩
      exact this.1
    · intro hx
      have : ((x, 0) : E d0 d1) ∈ S.sub := h.symm ▸ ⟨hx, T.S1.zero_mem⟩
      exact this.1
  · constructor
    · intro hx
      have : ((0, x) : E d0 d1) ∈ T.sub := h ▸ ⟨S.S0.zero_mem, hx⟩
      exact this.2
    · intro hx
      have : ((0, x) : E d0 d1) ∈ S.sub := h.symm ▸ ⟨T.S0.zero_mem, hx⟩
      exact this.2

end RSub

/-- The fixed ambient data `(E, Y, W, V)`. -/
structure Amb where
  /-- The number of additive coordinates. -/
  d0 : ℕ
  /-- The number of multiplicative coordinates. -/
  d1 : ℕ
  /-- The rational subspace of point data. -/
  Y : Submodule ℚ (E d0 d1)
  /-- The complex subspace of differentiation directions. -/
  W : Submodule ℂ (E d0 d1)
  /-- The complex subspace containing the point and direction data. -/
  V : Submodule ℂ (E d0 d1)
  hYfin : FiniteDimensional ℚ Y
  hYV : ∀ p ∈ Y, p ∈ V
  hWV : W ≤ V

namespace Amb

variable (M : Amb)

/-- Objects: pairs `S ≤ T` of rational product subspaces. -/
def Ob := {p : RSub M.d0 M.d1 × RSub M.d0 M.d1 // p.1 ≤ p.2}

/-- The admissible system of subquotients. -/
def sys : AdmSys M.Ob where
  Ker A B := A.1.1 = B.1.1 ∧ A.1.2 ≤ B.1.2
  Cok B C := B.1.2 = C.1.2 ∧ B.1.1 ≤ C.1.1
  Ex A B C := A.1.1 = B.1.1 ∧ A.1.2 = C.1.1 ∧ B.1.2 = C.1.2
  ker_refl X := ⟨rfl, RSub.le_refl' _⟩
  cok_refl X := ⟨rfl, RSub.le_refl' _⟩
  ker_trans h1 h2 := ⟨h1.1.trans h2.1, RSub.le_trans' h1.2 h2.2⟩
  cok_trans h1 h2 := ⟨h1.1.trans h2.1, RSub.le_trans' h1.2 h2.2⟩
  ex_ker {A B C} h := ⟨h.1, by rw [h.2.1, h.2.2]; exact C.2⟩
  ex_cok {A B C} h := ⟨h.2.2, by rw [← h.1, ← h.2.1]; exact A.2⟩
  ker_ex {A B} h := ⟨⟨(A.1.2, B.1.2), h.2⟩, h.1, rfl, rfl⟩
  cok_ex {B C} h := ⟨⟨(B.1.1, C.1.1), h.2⟩, rfl, rfl, h.1⟩

variable {M}

/-! ### Roy's functions -/

/-- `S` as a `ℚ`-subspace. -/
abbrev subQ (S : RSub M.d0 M.d1) : Submodule ℚ (E M.d0 M.d1) := S.sub.restrictScalars ℚ

/-- The complex dimension of the ambient subquotient `T / S`. -/
def r (X : M.Ob) : ℕ := finrank ℂ X.1.2.sub - finrank ℂ X.1.1.sub
/-- The dimension of the multiplicative coordinate subquotient. -/
def d1f (X : M.Ob) : ℕ := finrank ℂ X.1.2.S1 - finrank ℂ X.1.1.S1
/-- The dimension of the subquotient induced by `V`. -/
def vd (X : M.Ob) : ℕ := finrank ℂ ↥(M.V ⊓ X.1.2.sub) - finrank ℂ ↥(M.V ⊓ X.1.1.sub)
/-- The dimension of the subquotient induced by `W`. -/
def wd (X : M.Ob) : ℕ := finrank ℂ ↥(M.W ⊓ X.1.2.sub) - finrank ℂ ↥(M.W ⊓ X.1.1.sub)
/-- The codimension of the subspace induced by `V` in the ambient subquotient. -/
def b (X : M.Ob) : ℕ := r X - vd X
/-- The dimension remaining in the induced `V` subquotient after removing `W`. -/
def d (X : M.Ob) : ℕ := vd X - wd X
/-- The rational dimension of the subquotient induced by the point space `Y`. -/
def c (X : M.Ob) : ℕ := finrank ℚ ↥(M.Y ⊓ subQ X.1.2) - finrank ℚ ↥(M.Y ⊓ subQ X.1.1)

/-- `G(S, T) = Y ∩ T ∩ (Ω ∩ T + S)`. -/
def G (X : M.Ob) : Submodule ℚ (E M.d0 M.d1) :=
  M.Y ⊓ subQ X.1.2 ⊓ (Omega M.d0 M.d1 ⊓ subQ X.1.2 ⊔ subQ X.1.1)

/-- The rational dimension contributed by point data lying in periods modulo `S`. -/
def e (X : M.Ob) : ℕ := finrank ℚ (G X) - finrank ℚ ↥(M.Y ⊓ subQ X.1.1)
/-- The multiplicative dimension after subtracting the period contribution. -/
def a (X : M.Ob) : ℕ := d1f X - e X

/-! ### Monotonicity facts -/

instance (X : M.Ob) : FiniteDimensional ℚ ↥(M.Y ⊓ subQ X.1.2) := by
  have := M.hYfin
  exact Submodule.finiteDimensional_of_le inf_le_left

theorem finrank_sub_le (X : M.Ob) : finrank ℂ X.1.1.sub ≤ finrank ℂ X.1.2.sub :=
  Submodule.finrank_mono (RSub.sub_mono X.2)

theorem finrank_S1_le (X : M.Ob) : finrank ℂ X.1.1.S1 ≤ finrank ℂ X.1.2.S1 :=
  Submodule.finrank_mono X.2.2

theorem finrank_V_le (X : M.Ob) :
    finrank ℂ ↥(M.V ⊓ X.1.1.sub) ≤ finrank ℂ ↥(M.V ⊓ X.1.2.sub) :=
  Submodule.finrank_mono (inf_le_inf_left _ (RSub.sub_mono X.2))

theorem finrank_W_le (X : M.Ob) :
    finrank ℂ ↥(M.W ⊓ X.1.1.sub) ≤ finrank ℂ ↥(M.W ⊓ X.1.2.sub) :=
  Submodule.finrank_mono (inf_le_inf_left _ (RSub.sub_mono X.2))

theorem finrank_Y_le (X : M.Ob) :
    finrank ℚ ↥(M.Y ⊓ subQ X.1.1) ≤ finrank ℚ ↥(M.Y ⊓ subQ X.1.2) :=
  Submodule.finrank_mono (inf_le_inf_left _ (fun _ hx => RSub.sub_mono X.2 hx))

/-- `dim(V ∩ T) - dim(V ∩ S) ≤ dim T - dim S`. -/
theorem vd_le_aux (X : M.Ob) :
    finrank ℂ ↥(M.V ⊓ X.1.2.sub) + finrank ℂ X.1.1.sub ≤
      finrank ℂ X.1.2.sub + finrank ℂ ↥(M.V ⊓ X.1.1.sub) := by
  have hST := RSub.sub_mono X.2
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (M.V ⊓ X.1.2.sub) X.1.1.sub
  have h2 : (M.V ⊓ X.1.2.sub) ⊓ X.1.1.sub = M.V ⊓ X.1.1.sub := by
    rw [inf_assoc, inf_eq_right.mpr hST]
  have h3 : finrank ℂ ↥((M.V ⊓ X.1.2.sub) ⊔ X.1.1.sub) ≤ finrank ℂ X.1.2.sub :=
    Submodule.finrank_mono (sup_le inf_le_right hST)
  rw [h2] at h1
  omega

/-- `dim(W ∩ T) - dim(W ∩ S) ≤ dim(V ∩ T) - dim(V ∩ S)`. -/
theorem wd_le_aux (X : M.Ob) :
    finrank ℂ ↥(M.W ⊓ X.1.2.sub) + finrank ℂ ↥(M.V ⊓ X.1.1.sub) ≤
      finrank ℂ ↥(M.V ⊓ X.1.2.sub) + finrank ℂ ↥(M.W ⊓ X.1.1.sub) := by
  have hST := RSub.sub_mono X.2
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (M.W ⊓ X.1.2.sub) (M.V ⊓ X.1.1.sub)
  have h2 : (M.W ⊓ X.1.2.sub) ⊓ (M.V ⊓ X.1.1.sub) = M.W ⊓ X.1.1.sub := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · exact le_inf (inf_le_inf_left _ hST) (inf_le_inf_right _ M.hWV)
  have h3 : finrank ℂ ↥((M.W ⊓ X.1.2.sub) ⊔ (M.V ⊓ X.1.1.sub)) ≤ finrank ℂ ↥(M.V ⊓ X.1.2.sub) :=
    Submodule.finrank_mono (sup_le (inf_le_inf_right _ M.hWV) (inf_le_inf_left _ hST))
  rw [h2] at h1
  omega

theorem Y_le_G (X : M.Ob) : M.Y ⊓ subQ X.1.1 ≤ G X := by
  intro y hy
  refine ⟨⟨hy.1, RSub.sub_mono X.2 hy.2⟩, ?_⟩
  exact Submodule.mem_sup_right hy.2

theorem G_le (X : M.Ob) : G X ≤ M.Y ⊓ subQ X.1.2 := inf_le_left

instance (X : M.Ob) : FiniteDimensional ℚ (G X) :=
  Submodule.finiteDimensional_of_le (G_le X)

end Amb

/-! ### `Ω` as the image of the rational points -/

/-- `ω = 2πi`. -/
def ω : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem ω_ne_zero : ω ≠ 0 := by
  unfold ω
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

/-- `q ↦ (0, q)`, as a `ℚ`-linear map. -/
def ι₂ (d0 d1 : ℕ) : (Fin d1 → ℂ) →ₗ[ℚ] E d0 d1 :=
  (LinearMap.inr ℂ (Fin d0 → ℂ) (Fin d1 → ℂ)).restrictScalars ℚ

/-- `μ q = (0, ω q)`. -/
def μ (d0 d1 : ℕ) : (Fin d1 → ℂ) →ₗ[ℚ] E d0 d1 :=
  ((LinearMap.inr ℂ (Fin d0 → ℂ) (Fin d1 → ℂ)).comp (ω • LinearMap.id)).restrictScalars ℚ

theorem μ_apply {d0 d1 : ℕ} (q : Fin d1 → ℂ) : μ d0 d1 q = (0, ω • q) := rfl

theorem μ_injective (d0 d1 : ℕ) : Function.Injective (μ d0 d1) := by
  intro q q' h
  rw [μ_apply, μ_apply, Prod.mk.injEq] at h
  exact smul_right_injective _ ω_ne_zero h.2

theorem Omega_eq_map (d0 d1 : ℕ) : Omega d0 d1 = (Fpts ℚ (Fin d1)).map (μ d0 d1) := by
  rw [Fpts_eq_span, Submodule.map_span, Omega]
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ⟨j, rfl⟩, ?_⟩
    rw [μ_apply, ← Pi.single_smul, smul_eq_mul, mul_one]
    rfl
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    refine ⟨j, ?_⟩
    rw [μ_apply, ← Pi.single_smul, smul_eq_mul, mul_one]
    rfl

theorem span_coe_sup {n : ℕ} (A B : Submodule ℚ (Fin n → ℂ)) :
    span ℂ ((A ⊔ B : Submodule ℚ (Fin n → ℂ)) : Set (Fin n → ℂ)) =
      span ℂ (A : Set (Fin n → ℂ)) ⊔ span ℂ (B : Set (Fin n → ℂ)) := by
  apply le_antisymm
  · rw [span_le]
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hy
    exact add_mem (mem_sup_left (subset_span ha)) (mem_sup_right (subset_span hb))
  · exact sup_le (span_mono (le_sup_left : A ≤ A ⊔ B)) (span_mono (le_sup_right : B ≤ A ⊔ B))

namespace Amb

variable {M : Amb}

/-! ### Roy's Proposition 3 -/

/-- `R(S, T) = {q ∈ ℚ^{d₁} : (0, q) ∈ V ∩ T + S}`. -/
def R (X : M.Ob) : Submodule ℚ (Fin M.d1 → ℂ) :=
  Fpts ℚ (Fin M.d1) ⊓ ((M.V ⊓ X.1.2.sub ⊔ X.1.1.sub).restrictScalars ℚ).comap (ι₂ M.d0 M.d1)

theorem R_le_Fpts (X : M.Ob) : R X ≤ Fpts ℚ (Fin M.d1) := inf_le_left

instance (X : M.Ob) : FiniteDimensional ℚ (R X) :=
  Submodule.finiteDimensional_of_le (R_le_Fpts X)

theorem inr_mem_of_mem_R {X : M.Ob} {q : Fin M.d1 → ℂ} (hq : q ∈ R X) :
    ((0 : Fin M.d0 → ℂ), q) ∈ M.V ⊓ X.1.2.sub ⊔ X.1.1.sub := hq.2

theorem span_R_le (X : M.Ob) :
    (span ℂ ((R X : Submodule ℚ (Fin M.d1 → ℂ)) : Set (Fin M.d1 → ℂ))).map
        (LinearMap.inr ℂ (Fin M.d0 → ℂ) (Fin M.d1 → ℂ)) ≤ M.V ⊓ X.1.2.sub ⊔ X.1.1.sub := by
  rw [Submodule.map_span, span_le]
  rintro _ ⟨q, hq, rfl⟩
  exact inr_mem_of_mem_R hq

theorem span_R_le_T1 (X : M.Ob) :
    span ℂ ((R X : Submodule ℚ (Fin M.d1 → ℂ)) : Set (Fin M.d1 → ℂ)) ≤ X.1.2.S1 := by
  intro z hz
  have h := span_R_le X ⟨z, hz, rfl⟩
  have hT : M.V ⊓ X.1.2.sub ⊔ X.1.1.sub ≤ X.1.2.sub :=
    sup_le inf_le_right (RSub.sub_mono X.2)
  exact (hT h).2

/-- The new rational product subspace `S' = S₀ × (S₁ + span R)`. -/
def S' (X : M.Ob) : RSub M.d0 M.d1 where
  S0 := X.1.1.S0
  S1 := X.1.1.S1 ⊔ span ℂ ((R X : Submodule ℚ (Fin M.d1 → ℂ)) : Set (Fin M.d1 → ℂ))
  h0 := X.1.1.h0
  h1 := by
    obtain ⟨A1, hA1, hS1⟩ := X.1.1.h1
    refine ⟨A1 ⊔ R X, sup_le hA1 (R_le_Fpts X), ?_⟩
    rw [hS1, span_coe_sup]

/-- The cokernel object of Proposition 3. -/
def prop3Ob (X : M.Ob) : M.Ob :=
  ⟨(S' X, X.1.2), ⟨X.2.1, sup_le X.2.2 (span_R_le_T1 X)⟩⟩

theorem S_le_S' (X : M.Ob) : X.1.1 ≤ S' X := ⟨le_rfl, le_sup_left⟩

/-- `S' + V = S + V`. -/
theorem S'_sup_V (X : M.Ob) : (S' X).sub ⊔ M.V = X.1.1.sub ⊔ M.V := by
  apply le_antisymm
  · rw [sup_le_iff]
    refine ⟨?_, le_sup_right⟩
    rintro ⟨x0, x1⟩ ⟨hx0, hx1⟩
    obtain ⟨s1, hs1, z, hz, rfl⟩ := mem_sup.mp hx1
    have e : ((x0, s1 + z) : E M.d0 M.d1) = (x0, s1) + (0, z) := by simp
    rw [e]
    refine add_mem (mem_sup_left ⟨hx0, hs1⟩) ?_
    have h := span_R_le X ⟨z, hz, rfl⟩
    have hle : M.V ⊓ X.1.2.sub ⊔ X.1.1.sub ≤ X.1.1.sub ⊔ M.V :=
      sup_le (inf_le_left.trans le_sup_right) le_sup_left
    exact hle h
  · exact sup_le_sup_right (RSub.sub_mono (S_le_S' X)) _

/-- **The key estimate**: `e(S, T) ≤ dim R - dim (R ∩ A₁)`. -/
theorem e_le_R {X : M.Ob} {A1 : Submodule ℚ (Fin M.d1 → ℂ)} (hA1 : A1 ≤ Fpts ℚ (Fin M.d1))
    (hS1 : X.1.1.S1 = span ℂ (A1 : Set (Fin M.d1 → ℂ))) :
    e X + finrank ℚ ↥(R X ⊓ A1) ≤ finrank ℚ (R X) := by
  have hfY := M.hYfin
  set S := X.1.1
  set T := X.1.2
  set μR : Submodule ℚ (E M.d0 M.d1) := (R X).map (μ M.d0 M.d1) with hμR
  set Q : Submodule ℚ (E M.d0 M.d1) := μR ⊔ (M.Y ⊓ subQ T) with hQ
  have : FiniteDimensional ℚ μR := Module.Finite.map _ _
  have : FiniteDimensional ℚ Q := Submodule.finiteDimensional_sup _ _
  set QS : Submodule ℚ (E M.d0 M.d1) := Q ⊓ subQ S with hQS
  have : FiniteDimensional ℚ QS := Submodule.finiteDimensional_of_le inf_le_left
  -- (i) G ≤ μR ⊔ QS
  have hi : G X ≤ μR ⊔ QS := by
    intro y hy
    obtain ⟨⟨hyY, hyT⟩, hyΩ⟩ := hy
    obtain ⟨w, ⟨hwΩ, hwT⟩, s, hs, hws⟩ := mem_sup.mp hyΩ
    rw [Omega_eq_map] at hwΩ
    obtain ⟨q, hqF, rfl⟩ := hwΩ
    have hyV : y ∈ M.V := M.hYV y hyY
    have hμq : μ M.d0 M.d1 q ∈ M.V ⊓ T.sub ⊔ S.sub := by
      have h1 : y ∈ M.V ⊓ T.sub ⊔ S.sub := mem_sup_left ⟨hyV, hyT⟩
      have h2 : s ∈ M.V ⊓ T.sub ⊔ S.sub := mem_sup_right hs
      have : μ M.d0 M.d1 q = y - s := by rw [← hws]; abel
      rw [this]; exact sub_mem h1 h2
    have hqR : q ∈ R X := by
      refine ⟨hqF, ?_⟩
      change ((0 : Fin M.d0 → ℂ), q) ∈ M.V ⊓ T.sub ⊔ S.sub
      have : ((0 : Fin M.d0 → ℂ), q) = ω⁻¹ • μ M.d0 M.d1 q := by
        rw [μ_apply, Prod.smul_mk, smul_zero, smul_smul, inv_mul_cancel₀ ω_ne_zero, one_smul]
      rw [this]; exact Submodule.smul_mem _ _ hμq
    have hμR : μ M.d0 M.d1 q ∈ μR := Submodule.mem_map_of_mem hqR
    have hsQ : s ∈ Q := by
      have : s = y - μ M.d0 M.d1 q := by rw [← hws]; abel
      rw [this]
      exact sub_mem (mem_sup_right ⟨hyY, hyT⟩) (mem_sup_left hμR)
    rw [← hws]
    exact add_mem (mem_sup_left hμR) (mem_sup_right ⟨hsQ, hs⟩)
  -- (ii) G ∩ QS = Y ∩ S
  have hii : G X ⊓ QS = M.Y ⊓ subQ S := by
    apply le_antisymm
    · rintro y ⟨hyG, -, hyS⟩
      exact ⟨hyG.1.1, hyS⟩
    · intro y hy
      refine ⟨Y_le_G X hy, ?_, hy.2⟩
      exact mem_sup_right ⟨hy.1, RSub.sub_mono X.2 hy.2⟩
  -- (iii) μR ∩ QS = μ (R ∩ A₁)
  have hiii : μR ⊓ QS = (R X ⊓ A1).map (μ M.d0 M.d1) := by
    apply le_antisymm
    · rintro z ⟨⟨q, hqR, rfl⟩, -, hzS⟩
      refine ⟨q, ⟨hqR, ?_⟩, rfl⟩
      have h1 : ω • q ∈ S.S1 := hzS.2
      have h2 : q ∈ S.S1 := by
        have := S.S1.smul_mem ω⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ ω_ne_zero, one_smul] at this
      rw [hS1] at h2
      exact (mem_span_iff_of_le_Fpts A1 hA1 (R_le_Fpts X hqR)).mp h2
    · rintro _ ⟨q, ⟨hqR, hqA⟩, rfl⟩
      have hμR : μ M.d0 M.d1 q ∈ μR := Submodule.mem_map_of_mem hqR
      refine ⟨hμR, mem_sup_left hμR, ?_⟩
      refine ⟨S.S0.zero_mem, ?_⟩
      have : q ∈ S.S1 := by rw [hS1]; exact subset_span hqA
      exact S.S1.smul_mem ω this
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (G X) QS
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq μR QS
  rw [hii] at h1
  rw [hiii] at h2
  have h3 : finrank ℚ ↥(G X ⊔ QS) ≤ finrank ℚ ↥(μR ⊔ QS) :=
    Submodule.finrank_mono (sup_le hi le_sup_right)
  have h4 : finrank ℚ (R X) = finrank ℚ μR :=
    (Submodule.equivMapOfInjective _ (μ_injective M.d0 M.d1) (R X)).finrank_eq
  have h5 : finrank ℚ ↥(R X ⊓ A1) = finrank ℚ ↥((R X ⊓ A1).map (μ M.d0 M.d1)) :=
    (Submodule.equivMapOfInjective _ (μ_injective M.d0 M.d1) (R X ⊓ A1)).finrank_eq
  have h6 : finrank ℚ ↥(M.Y ⊓ subQ S) ≤ finrank ℚ (G X) := Submodule.finrank_mono (Y_le_G X)
  have he : e X = finrank ℚ (G X) - finrank ℚ ↥(M.Y ⊓ subQ S) := rfl
  omega

/-- Dimension of the new `S₁`. -/
theorem finrank_S'1 {X : M.Ob} {A1 : Submodule ℚ (Fin M.d1 → ℂ)} (hA1 : A1 ≤ Fpts ℚ (Fin M.d1))
    (hS1 : X.1.1.S1 = span ℂ (A1 : Set (Fin M.d1 → ℂ))) :
    finrank ℂ (S' X).S1 + finrank ℚ ↥(R X ⊓ A1) = finrank ℂ X.1.1.S1 + finrank ℚ (R X) := by
  have : FiniteDimensional ℚ A1 := Submodule.finiteDimensional_of_le hA1
  have e1 : (S' X).S1 = span ℂ ((A1 ⊔ R X : Submodule ℚ (Fin M.d1 → ℂ)) : Set (Fin M.d1 → ℂ)) := by
    change X.1.1.S1 ⊔ _ = _
    rw [hS1, span_coe_sup]
  rw [e1, finrank_span_of_le_Fpts _ (sup_le hA1 (R_le_Fpts X)), hS1,
    finrank_span_of_le_Fpts _ hA1]
  have := Submodule.finrank_sup_add_finrank_inf_eq A1 (R X)
  rw [inf_comm] at this
  omega

/-- `e ≤ d₁` and Roy's Proposition 3 (dimension part). -/
theorem d1f_prop3_add_e (X : M.Ob) : d1f (prop3Ob X) + e X ≤ d1f X := by
  obtain ⟨A1, hA1, hS1⟩ := X.1.1.h1
  have hk := e_le_R hA1 hS1
  have hf := finrank_S'1 hA1 hS1
  have hT : finrank ℂ (S' X).S1 ≤ finrank ℂ X.1.2.S1 := Submodule.finrank_mono (prop3Ob X).2.2
  have hd1 : d1f (prop3Ob X) = finrank ℂ X.1.2.S1 - finrank ℂ (S' X).S1 := rfl
  have hd2 : d1f X = finrank ℂ X.1.2.S1 - finrank ℂ X.1.1.S1 := rfl
  omega

theorem e_le_d1f (X : M.Ob) : e X ≤ d1f X := by
  have := d1f_prop3_add_e X; omega

theorem b_prop3 (X : M.Ob) : b (prop3Ob X) = b X := by
  have hS := S'_sup_V X
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (S' X).sub M.V
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq X.1.1.sub M.V
  rw [hS] at e1
  have v1 : finrank ℂ ↥(M.V ⊓ X.1.2.sub) + finrank ℂ (S' X).sub ≤
      finrank ℂ X.1.2.sub + finrank ℂ ↥(M.V ⊓ (S' X).sub) := vd_le_aux (prop3Ob X)
  have v2 := vd_le_aux X
  have f1 : finrank ℂ (S' X).sub ≤ finrank ℂ X.1.2.sub := finrank_sub_le (prop3Ob X)
  have f2 := finrank_sub_le X
  have g1 : finrank ℂ ↥(M.V ⊓ (S' X).sub) ≤ finrank ℂ ↥(M.V ⊓ X.1.2.sub) :=
    finrank_V_le (prop3Ob X)
  have g2 := finrank_V_le X
  have c1 : finrank ℂ ↥((S' X).sub ⊓ M.V) = finrank ℂ ↥(M.V ⊓ (S' X).sub) := by rw [inf_comm]
  have c2 : finrank ℂ ↥(X.1.1.sub ⊓ M.V) = finrank ℂ ↥(M.V ⊓ X.1.1.sub) := by rw [inf_comm]
  have hb1 : b (prop3Ob X) = (finrank ℂ X.1.2.sub - finrank ℂ (S' X).sub) -
      (finrank ℂ ↥(M.V ⊓ X.1.2.sub) - finrank ℂ ↥(M.V ⊓ (S' X).sub)) := rfl
  have hb2 : b X = (finrank ℂ X.1.2.sub - finrank ℂ X.1.1.sub) -
      (finrank ℂ ↥(M.V ⊓ X.1.2.sub) - finrank ℂ ↥(M.V ⊓ X.1.1.sub)) := rfl
  omega

/-- **Roy, Proposition 3.** -/
theorem prop3 (X : M.Ob) :
    ∃ X'', M.sys.Cok X X'' ∧ d1f X'' ≤ a X ∧ b X'' = b X := by
  refine ⟨prop3Ob X, ⟨rfl, S_le_S' X⟩, ?_, b_prop3 X⟩
  have := d1f_prop3_add_e X
  unfold a; omega

/-! ### Roy's Proposition 2: additivity -/

theorem ex_eqs {A B C : M.Ob} (h : M.sys.Ex A B C) :
    A.1.1 = B.1.1 ∧ A.1.2 = C.1.1 ∧ B.1.2 = C.1.2 := h

/-- Telescoping for functions of the form `φ T - φ S` with `φ` monotone. -/
theorem telescope (φ : RSub M.d0 M.d1 → ℕ) (hφ : ∀ S T : RSub M.d0 M.d1, S ≤ T → φ S ≤ φ T)
    {A B C : M.Ob} (h : M.sys.Ex A B C) :
    φ B.1.2 - φ B.1.1 = (φ A.1.2 - φ A.1.1) + (φ C.1.2 - φ C.1.1) := by
  obtain ⟨h1, h2, h3⟩ := ex_eqs h
  have hA := hφ _ _ A.2
  have hC := hφ _ _ C.2
  rw [h1, h2] at hA
  rw [← h3] at hC
  rw [h1, h2, ← h3]
  omega

theorem mono_sub : ∀ S T : RSub M.d0 M.d1, S ≤ T → finrank ℂ S.sub ≤ finrank ℂ T.sub :=
  fun _ _ h => Submodule.finrank_mono (RSub.sub_mono h)
theorem mono_S1 : ∀ S T : RSub M.d0 M.d1, S ≤ T → finrank ℂ S.S1 ≤ finrank ℂ T.S1 :=
  fun _ _ h => Submodule.finrank_mono h.2
theorem mono_V : ∀ S T : RSub M.d0 M.d1, S ≤ T →
    finrank ℂ ↥(M.V ⊓ S.sub) ≤ finrank ℂ ↥(M.V ⊓ T.sub) :=
  fun _ _ h => Submodule.finrank_mono (inf_le_inf_left _ (RSub.sub_mono h))
theorem mono_W : ∀ S T : RSub M.d0 M.d1, S ≤ T →
    finrank ℂ ↥(M.W ⊓ S.sub) ≤ finrank ℂ ↥(M.W ⊓ T.sub) :=
  fun _ _ h => Submodule.finrank_mono (inf_le_inf_left _ (RSub.sub_mono h))
theorem mono_Y : ∀ S T : RSub M.d0 M.d1, S ≤ T →
    finrank ℚ ↥(M.Y ⊓ subQ S) ≤ finrank ℚ ↥(M.Y ⊓ subQ T) := by
  intro S T h
  have := M.hYfin
  have : FiniteDimensional ℚ ↥(M.Y ⊓ subQ T) := Submodule.finiteDimensional_of_le inf_le_left
  exact Submodule.finrank_mono (inf_le_inf_left _ (fun x hx => RSub.sub_mono h hx))

theorem r_add : Additive M.sys r := fun _ _ _ h => telescope _ mono_sub h
theorem d1f_add : Additive M.sys d1f := fun _ _ _ h => telescope _ mono_S1 h
theorem vd_add : Additive M.sys vd := fun _ _ _ h => telescope _ mono_V h
theorem wd_add : Additive M.sys wd := fun _ _ _ h => telescope _ mono_W h
theorem c_add : Additive M.sys c := fun _ _ _ h => telescope _ mono_Y h

theorem vd_le_r (X : M.Ob) : vd X ≤ r X := by
  have := vd_le_aux X; have := finrank_sub_le X; have := finrank_V_le X
  unfold vd r; omega

theorem wd_le_vd (X : M.Ob) : wd X ≤ vd X := by
  have := wd_le_aux X; have := finrank_V_le X; have := finrank_W_le X
  unfold wd vd; omega

theorem b_add : Additive M.sys b := by
  intro A B C h
  have := r_add h; have := vd_add h
  have := vd_le_r A; have := vd_le_r B; have := vd_le_r C
  unfold b; omega

theorem d_add : Additive M.sys d := by
  intro A B C h
  have := vd_add h; have := wd_add h
  have := wd_le_vd A; have := wd_le_vd B; have := wd_le_vd C
  unfold d; omega

/-- `e` is lower additive. -/
theorem e_lower {A B C : M.Ob} (h : M.sys.Ex A B C) : e B ≤ e A + e C := by
  have hY := M.hYfin
  obtain ⟨h1, h2, h3⟩ := ex_eqs h
  have hSM : A.1.1 ≤ A.1.2 := A.2
  have hYM : FiniteDimensional ℚ ↥(M.Y ⊓ subQ A.1.2) :=
    Submodule.finiteDimensional_of_le inf_le_left
  -- `G(S,T) ∩ (Y ∩ M) ≤ G(S,M)`
  have ha : G B ⊓ (M.Y ⊓ subQ A.1.2) ≤ G A := by
    rintro y ⟨⟨⟨hyY, -⟩, hyΩ⟩, -, hyM⟩
    refine ⟨⟨hyY, hyM⟩, ?_⟩
    have hyΩ' : y ∈ Omega M.d0 M.d1 ⊓ subQ B.1.2 ⊔ subQ A.1.1 := by rw [h1]; exact hyΩ
    obtain ⟨w, ⟨hwΩ, -⟩, s, hs, rfl⟩ := mem_sup.mp hyΩ'
    have hsM : s ∈ subQ A.1.2 := RSub.sub_mono hSM hs
    have hwM : w ∈ subQ A.1.2 := by
      have : w = (w + s) - s := by abel
      rw [this]; exact sub_mem hyM hsM
    exact add_mem (mem_sup_left ⟨hwΩ, hwM⟩) (mem_sup_right hs)
  -- `G(S,T) ⊔ (Y ∩ M) ≤ G(M,T)`
  have hb : G B ⊔ (M.Y ⊓ subQ A.1.2) ≤ G C := by
    apply sup_le
    · rintro y ⟨⟨hyY, hyT⟩, hyΩ⟩
      change y ∈ M.Y ⊓ subQ C.1.2 ⊓ (Omega M.d0 M.d1 ⊓ subQ C.1.2 ⊔ subQ C.1.1)
      rw [← h2, ← h3]
      refine ⟨⟨hyY, hyT⟩, ?_⟩
      have hle : subQ B.1.1 ≤ subQ A.1.2 := by
        rw [← h1]; exact fun x hx => RSub.sub_mono hSM hx
      exact (sup_le_sup_left hle _) hyΩ
    · intro y hy
      have := Y_le_G C
      rw [← h2] at this
      exact this hy
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (G B) (M.Y ⊓ subQ A.1.2)
  have f1 : finrank ℚ ↥(G B ⊔ (M.Y ⊓ subQ A.1.2)) ≤ finrank ℚ (G C) := Submodule.finrank_mono hb
  have f2 : finrank ℚ ↥(G B ⊓ (M.Y ⊓ subQ A.1.2)) ≤ finrank ℚ (G A) := Submodule.finrank_mono ha
  have k1 : finrank ℚ ↥(M.Y ⊓ subQ A.1.1) ≤ finrank ℚ (G A) :=
    Submodule.finrank_mono (Y_le_G A)
  have eB : e B = finrank ℚ (G B) - finrank ℚ ↥(M.Y ⊓ subQ A.1.1) := by
    change finrank ℚ (G B) - finrank ℚ ↥(M.Y ⊓ subQ B.1.1) = _
    rw [h1]
  have eA : e A = finrank ℚ (G A) - finrank ℚ ↥(M.Y ⊓ subQ A.1.1) := rfl
  have eC : e C = finrank ℚ (G C) - finrank ℚ ↥(M.Y ⊓ subQ A.1.2) := by
    change finrank ℚ (G C) - finrank ℚ ↥(M.Y ⊓ subQ C.1.1) = _
    rw [h2]
  have k2 : finrank ℚ ↥(M.Y ⊓ subQ A.1.2) ≤ finrank ℚ (G C) := by
    have := Y_le_G C; rw [← h2] at this; exact Submodule.finrank_mono this
  omega

theorem a_upper : UpperAdd M.sys a := by
  intro A B C h
  have := e_lower h
  have := d1f_add h
  have := e_le_d1f A; have := e_le_d1f B; have := e_le_d1f C
  unfold a; omega

theorem eq_of_r_eq_zero {X : M.Ob} (h : r X = 0) : X.1.1 = X.1.2 := by
  have h1 := finrank_sub_le X
  have h2 : finrank ℂ X.1.2.sub ≤ finrank ℂ X.1.1.sub := by unfold r at h; omega
  exact RSub.eq_of_sub_eq (Submodule.eq_of_le_of_finrank_le (RSub.sub_mono X.2) h2)

theorem van (X : M.Ob) (h : r X = 0) : a X = 0 ∧ b X = 0 ∧ c X = 0 ∧ d X = 0 := by
  have hST := eq_of_r_eq_zero h
  have hd1 : d1f X = 0 := by unfold d1f; rw [hST]; simp
  have hc : c X = 0 := by unfold c; rw [hST]; simp
  have hvd : vd X = 0 := by unfold vd; rw [hST]; simp
  have := e_le_d1f X
  refine ⟨?_, ?_, hc, ?_⟩
  · unfold a; omega
  · unfold b; rw [hvd, h]
  · unfold d; rw [hvd]; simp

/-- **Roy's Proposition 2** (and the vanishing on objects with `r = 0`). -/
theorem hyp : Hyp M.sys a b c d r where
  ha := a_upper
  hd _ _ _ h := (d_add h).ge
  hb := b_add
  hc := c_add
  hr := r_add
  van := van

theorem a_le_d1f (X : M.Ob) : a X ≤ d1f X := by unfold a; omega

end Amb

end StrongSix.Roy

end

end LeanPool
