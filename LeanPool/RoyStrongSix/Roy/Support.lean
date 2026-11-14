/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Roy.Subquot

/-!
# Support lemmas for deducing Statement 1 from Theorem 1

* algebraic / rational coordinate vectors as `F`-points;
* `𝓛` is a `ℚ`-subspace of `ℂ`, preserved (coordinatewise) by `ℚ`-point-preserving maps;
* rationality over `Qbar` in `ℂ^{d₀} × ℂ^{d₁}` (Roy's sense) is stable under intersection and
  under images by maps preserving algebraic points;
* dimension of product subspaces and a rank–nullity helper.
-/

@[expose] public section

namespace LeanPool

open Module Submodule Complex

noncomputable section

namespace StrongSix.Roy

/-! ### Points -/

theorem mem_range_Qb {z : ℂ} : z ∈ (algebraMap Qb ℂ).range ↔ IsAlgebraic ℚ z := by
  constructor
  · rintro ⟨w, rfl⟩
    exact (mem_algebraicClosure_iff'.mp w.2).isAlgebraic
  · intro h
    exact ⟨⟨z, mem_algebraicClosure_iff'.mpr h.isIntegral⟩, rfl⟩

theorem algVec_iff {n : ℕ} {u : Fin n → ℂ} : AlgVec u ↔ u ∈ Fpts Qb (Fin n) :=
  forall_congr' fun _ => mem_range_Qb.symm

theorem mem_range_Q {z : ℂ} : z ∈ (algebraMap ℚ ℂ).range ↔ ∃ q : ℚ, z = q := by
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, by simp⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, by simp⟩

theorem ratVec_iff {n : ℕ} {v : Fin n → ℂ} : RatVec v ↔ v ∈ Fpts ℚ (Fin n) :=
  forall_congr' fun _ => mem_range_Q.symm

theorem Fpts_Q_le_Qb {n : ℕ} {v : Fin n → ℂ} (h : v ∈ Fpts ℚ (Fin n)) : v ∈ Fpts Qb (Fin n) := by
  intro i
  obtain ⟨q, hq⟩ := h i
  rw [mem_range_Qb, ← hq]
  exact isAlgebraic_algebraMap q

/-! ### `𝓛` is a `ℚ`-subspace -/

theorem logAlg_add {a b : ℂ} (ha : a ∈ logAlg) (hb : b ∈ logAlg) : a + b ∈ logAlg := by
  change IsAlgebraic ℚ (exp (a + b)); rw [exp_add]; exact ha.mul hb

theorem logAlg_zero : (0 : ℂ) ∈ logAlg := by
  change IsAlgebraic ℚ (exp 0); rw [exp_zero]; exact isAlgebraic_one

theorem logAlg_int_mul {a : ℂ} (ha : a ∈ logAlg) (m : ℤ) : (m : ℂ) * a ∈ logAlg := by
  change IsAlgebraic ℚ (exp (m * a))
  rw [exp_int_mul]
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · simpa using ha.pow k
  · rw [zpow_neg]; simpa using (ha.pow k).inv

theorem logAlg_rat_mul {a : ℂ} (ha : a ∈ logAlg) (q : ℚ) : (q : ℂ) * a ∈ logAlg := by
  change IsAlgebraic ℚ (exp (q * a))
  have hd : 0 < q.den := q.den_pos
  apply IsAlgebraic.of_pow hd
  rw [← exp_nat_mul]
  have : ((q.den : ℕ) : ℂ) * ((q : ℂ) * a) = ((q.num : ℤ) : ℂ) * a := by
    rw [← mul_assoc]
    congr 1
    have := Rat.mul_den_eq_num q
    have h' : ((q.den : ℕ) : ℂ) * (q : ℂ) = ((q * q.den : ℚ) : ℂ) := by push_cast; ring
    rw [h', this]; push_cast; rfl
  rw [this]
  exact logAlg_int_mul ha q.num

/-- `𝓛` as a `ℚ`-subspace of `ℂ`. -/
def logAlgSub : Submodule ℚ ℂ where
  carrier := logAlg
  add_mem' := logAlg_add
  zero_mem' := logAlg_zero
  smul_mem' q a ha := by rw [Rat.smul_def]; exact logAlg_rat_mul ha q

/-- The algebraic numbers as a `ℚ`-subspace of `ℂ`. -/
def algSub : Submodule ℚ ℂ where
  carrier := {z | IsAlgebraic ℚ z}
  add_mem' ha hb := ha.add hb
  zero_mem' := isAlgebraic_zero
  smul_mem' q a ha := by rw [Rat.smul_def]; exact (isAlgebraic_algebraMap q).mul ha

/-! ### `ℚ`-point-preserving maps preserve coordinatewise `ℚ`-subspaces -/

theorem linmap_apply_eq_sum {n k : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)) (x : Fin n → ℂ)
    (j : Fin k) : f x j = ∑ i, x i * f (Pi.single i 1) j := by
  conv_lhs => rw [pi_eq_sum_univ x]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (fun j => if i = j then (1 : ℂ) else 0) = (Pi.single i 1 : Fin n → ℂ) := by
    funext l; simp [Pi.single_apply, eq_comm]
  rw [hs, map_smul, Pi.smul_apply, smul_eq_mul]

theorem presQ_preserves {n k : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin k → ℂ)) (hf : PresF ℚ f)
    (P : Submodule ℚ ℂ) {x : Fin n → ℂ} (hx : ∀ i, x i ∈ P) (j : Fin k) : f x j ∈ P := by
  rw [linmap_apply_eq_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨q, hq⟩ := hf (Pi.single i 1) (single_mem_Fpts i) j
  rw [← hq, mul_comm, ← Algebra.smul_def]
  exact P.smul_mem q (hx i)

/-! ### Rank–nullity and dimensions of products -/

theorem finrank_map_add_inf_ker {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (σ : V →ₗ[K] V') (A : Submodule K V) [FiniteDimensional K A] :
    finrank K (A.map σ) + finrank K ↥(A ⊓ LinearMap.ker σ) = finrank K A := by
  let g := σ.comp A.subtype
  have hr : LinearMap.range g = A.map σ := by rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : (LinearMap.ker g).map A.subtype = A ⊓ LinearMap.ker σ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h1⟩, h2, rfl⟩
  have := LinearMap.finrank_range_add_finrank_ker g
  rw [hr, ← Submodule.finrank_map_subtype_eq A (LinearMap.ker g), hk] at this
  exact this

theorem finrank_prod_sub {d0 d1 : ℕ} (p : Submodule ℂ (Fin d0 → ℂ)) (q : Submodule ℂ (Fin d1 → ℂ)) :
    finrank ℂ ↥(p.prod q) = finrank ℂ p + finrank ℂ q := by
  rw [(Submodule.prodEquiv p q).finrank_eq, Module.finrank_prod]

/-! ### Rationality over `Qbar` in `ℂ^{d₀} × ℂ^{d₁}` -/

/-- The algebraic points of a `ℂ`-subspace of `E`, as a `Qbar`-subspace. -/
def algPts {d0 d1 : ℕ} (U : Submodule ℂ (E d0 d1)) : Submodule Qb (E d0 d1) where
  carrier := {u | u ∈ U ∧ AlgVec u.1 ∧ AlgVec u.2}
  add_mem' {_ _} hx hy :=
    ⟨U.add_mem hx.1 hy.1,
      algVec_iff.mpr ((Fpts Qb _).add_mem (algVec_iff.mp hx.2.1) (algVec_iff.mp hy.2.1)),
      algVec_iff.mpr ((Fpts Qb _).add_mem (algVec_iff.mp hx.2.2) (algVec_iff.mp hy.2.2))⟩
  zero_mem' := ⟨U.zero_mem, algVec_iff.mpr (Fpts Qb _).zero_mem,
    algVec_iff.mpr (Fpts Qb _).zero_mem⟩
  smul_mem' c _ hx :=
    ⟨U.smul_of_tower_mem c hx.1, algVec_iff.mpr ((Fpts Qb _).smul_mem c (algVec_iff.mp hx.2.1)),
      algVec_iff.mpr ((Fpts Qb _).smul_mem c (algVec_iff.mp hx.2.2))⟩

theorem rationalOverQbar_iff {d0 d1 : ℕ} (U : Submodule ℂ (E d0 d1)) :
    RationalOverQbar U ↔ U = span ℂ ((algPts U : Submodule Qb (E d0 d1)) : Set (E d0 d1)) :=
  Iff.rfl

/-- The coordinate equivalence `ℂ^{Fin d₀ ⊕ Fin d₁} ≃ ℂ^{d₀} × ℂ^{d₁}`. -/
def eqv (d0 d1 : ℕ) : ((Fin d0 ⊕ Fin d1) → ℂ) ≃ₗ[ℂ] E d0 d1 :=
  LinearEquiv.sumArrowLequivProdArrow (Fin d0) (Fin d1) ℂ ℂ

theorem eqv_fpts {d0 d1 : ℕ} (x : (Fin d0 ⊕ Fin d1) → ℂ) :
    x ∈ Fpts Qb (Fin d0 ⊕ Fin d1) ↔ AlgVec (eqv d0 d1 x).1 ∧ AlgVec (eqv d0 d1 x).2 := by
  change (∀ i, x i ∈ (algebraMap Qb ℂ).range) ↔
    (∀ i, IsAlgebraic ℚ (x (Sum.inl i))) ∧ ∀ i, IsAlgebraic ℚ (x (Sum.inr i))
  rw [← Sum.forall (p := fun i => IsAlgebraic ℚ (x i))]
  exact forall_congr' fun _ => mem_range_Qb

/-- The `Qbar`-points of `U`, transported to the sum-indexed coordinate space. -/
def algPtsT {d0 d1 : ℕ} (U : Submodule ℂ (E d0 d1)) : Submodule Qb ((Fin d0 ⊕ Fin d1) → ℂ) :=
  (algPts U).comap ((eqv d0 d1).toLinearMap.restrictScalars Qb)

theorem algPtsT_le {d0 d1 : ℕ} (U : Submodule ℂ (E d0 d1)) :
    algPtsT U ≤ Fpts Qb (Fin d0 ⊕ Fin d1) := fun x hx => (eqv_fpts x).mpr hx.2

theorem span_algPts_eq_map {d0 d1 : ℕ} (U : Submodule ℂ (E d0 d1)) :
    span ℂ ((algPts U : Submodule Qb (E d0 d1)) : Set (E d0 d1)) =
      (span ℂ ((algPtsT U : Submodule Qb _) : Set ((Fin d0 ⊕ Fin d1) → ℂ))).map
        (eqv d0 d1).toLinearMap := by
  rw [Submodule.map_span]
  congr 1
  ext p
  constructor
  · intro hp
    refine ⟨(eqv d0 d1).symm p, ?_, by simp⟩
    change (eqv d0 d1) ((eqv d0 d1).symm p) ∈ algPts U
    rw [LinearEquiv.apply_symm_apply]; exact hp
  · rintro ⟨x, hx, rfl⟩; exact hx

theorem algPts_inf {d0 d1 : ℕ} (W T : Submodule ℂ (E d0 d1)) :
    algPtsT (W ⊓ T) = algPtsT W ⊓ algPtsT T := by
  ext x
  simp only [algPtsT, algPts, Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  tauto

/-- **Intersections of `Qbar`-rational subspaces are `Qbar`-rational.** -/
theorem rationalOverQbar_inf {d0 d1 : ℕ} {W T : Submodule ℂ (E d0 d1)}
    (hW : RationalOverQbar W) (hT : RationalOverQbar T) : RationalOverQbar (W ⊓ T) := by
  rw [rationalOverQbar_iff] at *
  apply le_antisymm
  · conv_lhs => rw [hW, hT]
    rw [span_algPts_eq_map, span_algPts_eq_map, span_algPts_eq_map,
      ← Submodule.map_inf _ (eqv d0 d1).injective,
      span_inf_span_of_le_Fpts _ _ (algPtsT_le W) (algPtsT_le T), algPts_inf]
  · rw [span_le]; intro x hx; exact hx.1

/-- A rational product subspace is rational over `Qbar`. -/
theorem rationalOverQbar_prod {d0 d1 : ℕ} {T0 : Submodule ℂ (Fin d0 → ℂ)}
    {T1 : Submodule ℂ (Fin d1 → ℂ)} (h0 : IsRat Qb T0) (h1 : IsRat ℚ T1) :
    RationalOverQbar (T0.prod T1) := by
  obtain ⟨A0, hA0, rfl⟩ := h0
  obtain ⟨A1, hA1, rfl⟩ := h1
  rw [rationalOverQbar_iff]
  apply le_antisymm
  · rintro ⟨x0, x1⟩ ⟨hx0, hx1⟩
    have e : ((x0, x1) : E d0 d1) = (x0, 0) + (0, x1) := by simp
    rw [e]
    refine add_mem ?_ ?_
    · have := Submodule.apply_mem_span_image_of_mem_span (LinearMap.inl ℂ (Fin d0 → ℂ)
        (Fin d1 → ℂ)) hx0
      refine span_mono ?_ this
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨⟨subset_span ha, (span ℂ _).zero_mem⟩, ?_, ?_⟩
      · rw [algVec_iff]; exact hA0 ha
      · rw [algVec_iff]; exact (Fpts Qb _).zero_mem
    · have := Submodule.apply_mem_span_image_of_mem_span (LinearMap.inr ℂ (Fin d0 → ℂ)
        (Fin d1 → ℂ)) hx1
      refine span_mono ?_ this
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨⟨(span ℂ _).zero_mem, subset_span ha⟩, ?_, ?_⟩
      · rw [algVec_iff]; exact (Fpts Qb _).zero_mem
      · rw [algVec_iff]; exact Fpts_Q_le_Qb (hA1 ha)
  · rw [span_le]; intro x hx; exact hx.1

/-- Images of `Qbar`-rational subspaces under maps preserving algebraic points. -/
theorem rationalOverQbar_map {d0 d1 k0 k1 : ℕ} {W : Submodule ℂ (E d0 d1)}
    (ψ : E d0 d1 →ₗ[ℂ] E k0 k1)
    (hψ : ∀ u : E d0 d1, AlgVec u.1 → AlgVec u.2 → AlgVec (ψ u).1 ∧ AlgVec (ψ u).2)
    (hW : RationalOverQbar W) : RationalOverQbar (W.map ψ) := by
  rw [rationalOverQbar_iff] at *
  apply le_antisymm
  · conv_lhs => rw [hW]
    rw [Submodule.map_span]
    apply span_mono
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨Submodule.mem_map_of_mem hu.1, hψ u hu.2.1 hu.2.2⟩
  · rw [span_le]; intro x hx; exact hx.1

end StrongSix.Roy

end

end LeanPool
