/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.RangeProjection
public import LeanPool.VacuumBellSeparation.Bell.Cells
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Threshold projections of a self-adjoint element of a von Neumann algebra

For a self-adjoint `A` in a von Neumann algebra `M` and a real threshold `u`, the range
projection `E u` of the positive part of `A - u` belongs to `M`, commutes with `A`, and
satisfies `(A - u) E u ≥ 0`, `(u - A) (1 - E u) ≥ 0`.  The family is decreasing:
`E u * E v = E v` for `u ≤ v`.  The main result is `exists_threshold_projections`.
-/

@[expose] public section

open scoped ComplexOrder

namespace VacuumBellSeparation

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Range-projection identities -/

theorem rangeProjection_idem (T : H →L[ℂ] H) :
    rangeProjection T * rangeProjection T = rangeProjection T := by
  first
    | exact (rangeClosure T).isIdempotentElem_starProjection

theorem rangeProjection_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (rangeProjection T) := by
  first
    | exact isSelfAdjoint_starProjection (rangeClosure T)

/-- A self-adjoint idempotent is positive. -/
theorem isPositive_of_isSelfAdjoint_of_idem {Q : H →L[ℂ] H} (hsa : IsSelfAdjoint Q)
    (hQ : Q * Q = Q) : Q.IsPositive := by
  have h : star Q * Q = Q := by rw [hsa.star_eq, hQ]
  have h0 : (0 : H →L[ℂ] H) ≤ star Q * Q := star_mul_self_nonneg Q
  rw [h] at h0
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp h0

theorem rangeProjection_isPositive (T : H →L[ℂ] H) : (rangeProjection T).IsPositive :=
  isPositive_of_isSelfAdjoint_of_idem (rangeProjection_isSelfAdjoint T) (rangeProjection_idem T)

theorem rangeProjection_apply_mem (T : H →L[ℂ] H) (x : H) :
    rangeProjection T x ∈ rangeClosure T :=
  Submodule.starProjection_apply_mem (rangeClosure T) x

theorem rangeProjection_apply_of_mem {T : H →L[ℂ] H} {x : H} (hx : x ∈ rangeClosure T) :
    rangeProjection T x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

omit [CompleteSpace H] in
theorem apply_mem_rangeClosure (T : H →L[ℂ] H) (x : H) : T x ∈ rangeClosure T := by
  have hmem : T x ∈ LinearMap.range T.toLinearMap := LinearMap.mem_range.mpr ⟨x, rfl⟩
  exact Submodule.le_topologicalClosure _ hmem

omit [CompleteSpace H] in
/-- A closed subspace containing the range of `T` contains the closure of the range. -/
theorem rangeClosure_le_of_forall_mem {T : H →L[ℂ] H} {K : Submodule ℂ H}
    (hK : IsClosed (K : Set H)) (h : ∀ z : H, T z ∈ K) : rangeClosure T ≤ K := by
  have hle : (LinearMap.range T.toLinearMap).topologicalClosure ≤ K := by
    refine Submodule.topologicalClosure_minimal _ ?_ hK
    intro y hy
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy
    exact h z
  exact hle

theorem rangeProjection_mul_self (T : H →L[ℂ] H) : rangeProjection T * T = T := by
  refine ContinuousLinearMap.ext fun x => ?_
  change rangeProjection T (T x) = T x
  exact rangeProjection_apply_of_mem (apply_mem_rangeClosure T x)

theorem self_mul_rangeProjection {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    T * rangeProjection T = T := by
  have h := congrArg star (rangeProjection_mul_self T)
  rw [star_mul, hT.star_eq, (rangeProjection_isSelfAdjoint T).star_eq] at h
  exact h

/-- If `S` vanishes on the range of `T`, it vanishes on the closure of the range. -/
theorem mul_rangeProjection_eq_zero {T S : H →L[ℂ] H} (h : S * T = 0) :
    S * rangeProjection T = 0 := by
  have hST : ∀ z : H, S (T z) = 0 := fun z => by
    have hz := DFunLike.congr_fun h z
    first
      | exact hz
  have hsub : (LinearMap.range T.toLinearMap : Set H) ⊆ {y : H | S y = 0} := by
    intro y hy
    have hy' : y ∈ LinearMap.range T.toLinearMap := hy
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hy'
    exact hST z
  have hclosed : IsClosed {y : H | S y = 0} := isClosed_eq S.continuous continuous_const
  have hcl : closure (LinearMap.range T.toLinearMap : Set H) ⊆ {y : H | S y = 0} :=
    closure_minimal hsub hclosed
  have hall : ∀ x ∈ rangeClosure T, S x = 0 := by
    intro x hx
    first
      | exact hcl hx
  refine ContinuousLinearMap.ext fun x => ?_
  change S (rangeProjection T x) = 0
  exact hall _ (rangeProjection_apply_mem T x)

/-- An operator commuting with `T` and whose adjoint commutes with `T` commutes with the
range projection of `T`. -/
theorem rangeProjection_commute {T S : H →L[ℂ] H} (h : S * T = T * S)
    (h' : star S * T = T * star S) : rangeProjection T * S = S * rangeProjection T :=
  commute_projection_of_invariant (rangeClosure T) S
    (fun _ hx => map_mem_rangeClosure_of_commute h hx)
    (fun _ hx => map_mem_rangeClosure_of_commute h' hx)

/-- If the range projection of `T` fixes `S` from the left, it dominates the range projection
of `S`. -/
theorem rangeProjection_mul_rangeProjection_of_mul_eq {T S : H →L[ℂ] H}
    (h : rangeProjection T * S = S) :
    rangeProjection T * rangeProjection S = rangeProjection S := by
  have hmem : ∀ z : H, S z ∈ rangeClosure T := fun z => by
    have hz : rangeProjection T (S z) = S z := DFunLike.congr_fun h z
    have hm := rangeProjection_apply_mem T (S z)
    rwa [hz] at hm
  have hclosed : IsClosed ((rangeClosure T : Submodule ℂ H) : Set H) :=
    Submodule.isClosed_topologicalClosure (LinearMap.range T.toLinearMap)
  have hle : rangeClosure S ≤ rangeClosure T := rangeClosure_le_of_forall_mem hclosed hmem
  refine ContinuousLinearMap.ext fun x => ?_
  change rangeProjection T (rangeProjection S x) = rangeProjection S x
  exact rangeProjection_apply_of_mem (hle (rangeProjection_apply_mem S x))

/-! ### Positive and negative parts -/

/-- Anything commuting with `T` commutes with its positive part. -/
theorem commute_posPart {T S : H →L[ℂ] H} (h : S * T = T * S) : S * T⁺ = T⁺ * S := by
  have hc : Commute T S := h.symm
  have h2 : Commute (cfcₙ (fun x : ℝ => x⁺) T) S := hc.cfcₙ_real _
  have h3 : T⁺ = cfcₙ (fun x : ℝ => x⁺) T := CFC.posPart_def T
  rw [h3]
  first
    | exact h2.symm.eq

/-- Anything commuting with `T` commutes with its negative part. -/
theorem commute_negPart {T S : H →L[ℂ] H} (h : S * T = T * S) : S * T⁻ = T⁻ * S := by
  have hc : Commute T S := h.symm
  have h2 : Commute (cfcₙ (fun x : ℝ => x⁻) T) S := hc.cfcₙ_real _
  have h3 : T⁻ = cfcₙ (fun x : ℝ => x⁻) T := CFC.negPart_def T
  rw [h3]
  first
    | exact h2.symm.eq

/-- The positive part of an element of a von Neumann algebra belongs to the algebra. -/
theorem posPart_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M) : T⁺ ∈ M := by
  have key : T⁺ ∈ M.commutant.commutant := by
    refine VonNeumannAlgebra.mem_commutant_iff.mpr fun S hS => ?_
    have h1 : S * T = T * S := (VonNeumannAlgebra.mem_commutant_iff.mp hS T hT).symm
    exact commute_posPart h1
  first
    | (rw [VonNeumannAlgebra.commutant_commutant] at key; exact key)

/-- The negative part of an element of a von Neumann algebra belongs to the algebra. -/
theorem negPart_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M) : T⁻ ∈ M := by
  have key : T⁻ ∈ M.commutant.commutant := by
    refine VonNeumannAlgebra.mem_commutant_iff.mpr fun S hS => ?_
    have h1 : S * T = T * S := (VonNeumannAlgebra.mem_commutant_iff.mp hS T hT).symm
    exact commute_negPart h1
  first
    | (rw [VonNeumannAlgebra.commutant_commutant] at key; exact key)

theorem posPart_isPositive (T : H →L[ℂ] H) : (T⁺).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.posPart_nonneg T)

theorem negPart_isPositive (T : H →L[ℂ] H) : (T⁻).IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.negPart_nonneg T)

/-! ### The range projection of the positive part -/

theorem mul_rangeProjection_posPart {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    T * rangeProjection T⁺ = T⁺ := by
  have h1 : T⁺ * rangeProjection T⁺ = T⁺ :=
    self_mul_rangeProjection (posPart_isPositive T).isSelfAdjoint
  have h2 : T⁻ * rangeProjection T⁺ = 0 :=
    mul_rangeProjection_eq_zero (CFC.negPart_mul_posPart T)
  have h3 : T⁺ - T⁻ = T := CFC.posPart_sub_negPart T hT
  calc T * rangeProjection T⁺ = (T⁺ - T⁻) * rangeProjection T⁺ := by rw [h3]
    _ = T⁺ * rangeProjection T⁺ - T⁻ * rangeProjection T⁺ := sub_mul _ _ _
    _ = T⁺ := by rw [h1, h2, sub_zero]

theorem mul_rangeProjection_posPart_isPositive {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    (T * rangeProjection T⁺).IsPositive := by
  rw [mul_rangeProjection_posPart hT]
  exact posPart_isPositive T

theorem neg_mul_one_sub_rangeProjection_posPart {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    (-T) * (1 - rangeProjection T⁺) = T⁻ := by
  have h1 : T * rangeProjection T⁺ = T⁺ := mul_rangeProjection_posPart hT
  have h3 : T⁺ - T⁻ = T := CFC.posPart_sub_negPart T hT
  calc (-T) * (1 - rangeProjection T⁺) = T * rangeProjection T⁺ - T := by
        rw [mul_sub, mul_one, neg_mul]
        abel
    _ = T⁺ - (T⁺ - T⁻) := by rw [h1, h3]
    _ = T⁻ := by abel

theorem neg_mul_one_sub_rangeProjection_posPart_isPositive {T : H →L[ℂ] H}
    (hT : IsSelfAdjoint T) : ((-T) * (1 - rangeProjection T⁺)).IsPositive := by
  rw [neg_mul_one_sub_rangeProjection_posPart hT]
  exact negPart_isPositive T

/-- Anything commuting (together with its adjoint) with `T` commutes with the range projection
of the positive part of `T`. -/
theorem rangeProjection_posPart_commute {T S : H →L[ℂ] H} (h : S * T = T * S)
    (h' : star S * T = T * star S) :
    rangeProjection T⁺ * S = S * rangeProjection T⁺ :=
  rangeProjection_commute (commute_posPart h) (commute_posPart h')

/-! ### Nestedness -/

theorem ofReal_nonneg_complex {c : ℝ} (hc : 0 ≤ c) : (0 : ℂ) ≤ (c : ℂ) := by
  first
    | exact Complex.zero_le_real.mpr hc

omit [CompleteSpace H] in
/-- A positive operator whose negative is positive vanishes. -/
theorem eq_zero_of_isPositive_of_neg_isPositive {B : H →L[ℂ] H} (h1 : B.IsPositive)
    (h2 : (-B).IsPositive) : B = 0 := by
  have h1' : (0 : H →L[ℂ] H) ≤ B := ContinuousLinearMap.nonneg_iff_isPositive.mpr h1
  have h2' : B ≤ 0 := by
    first
      | exact ContinuousLinearMap.le_def.mpr (by rwa [zero_sub])
  exact le_antisymm h2' h1'

/-- `Z = 0` as soon as `Z⋆ Z = 0`. -/
theorem eq_zero_of_star_mul_self_eq_zero {Z : H →L[ℂ] H} (h : star Z * Z = 0) : Z = 0 := by
  have hn : ‖star Z * Z‖ = ‖Z‖ * ‖Z‖ := CStarRing.norm_star_mul_self
  rw [h, norm_zero] at hn
  exact norm_eq_zero.mp (mul_self_eq_zero.mp hn.symm)

/-- The algebraic core of nestedness: if `X, Y₁ ≥ 0`, `Q` is a projection commuting with `X`,
`X Y = 0`, `X` commutes with `Y₁`, and `(Y - X) Q = Y₁ + c Q` with `c ≥ 0`, then `X Q = 0`. -/
theorem mul_eq_zero_of_sub_mul_eq {X Y Y₁ Q : H →L[ℂ] H} (hX : X.IsPositive)
    (hY₁ : Y₁.IsPositive) (hQsa : IsSelfAdjoint Q) (hQ : Q * Q = Q) (hXY : X * Y = 0)
    (hQX : Q * X = X * Q) (hXY₁ : X * Y₁ = Y₁ * X) {c : ℝ} (hc : 0 ≤ c)
    (h : (Y - X) * Q = Y₁ + (c : ℂ) • Q) : X * Q = 0 := by
  have hQpos : Q.IsPositive := isPositive_of_isSelfAdjoint_of_idem hQsa hQ
  have hP : (Y₁ + (c : ℂ) • Q).IsPositive :=
    hY₁.add (hQpos.smul_of_nonneg (ofReal_nonneg_complex hc))
  have hcomm : X * (Y₁ + (c : ℂ) • Q) = (Y₁ + (c : ℂ) • Q) * X := by
    rw [mul_add, add_mul, hXY₁, mul_smul_comm, smul_mul_assoc, hQX]
  have hpos : (X * (Y₁ + (c : ℂ) • Q)).IsPositive := isPositive_mul_of_commute hX hP hcomm
  have hXsa : star X = X := hX.isSelfAdjoint.star_eq
  have hW : star (X * Q) * (X * Q) = X * X * Q := by
    rw [star_mul, hQsa.star_eq, hXsa]
    calc Q * X * (X * Q) = X * Q * (X * Q) := by rw [hQX]
      _ = X * (Q * X) * Q := by simp only [mul_assoc]
      _ = X * (X * Q) * Q := by rw [hQX]
      _ = X * X * (Q * Q) := by simp only [mul_assoc]
      _ = X * X * Q := by rw [hQ]
  have hWpos : (star (X * Q) * (X * Q)).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg (X * Q))
  have hneg : X * (Y₁ + (c : ℂ) • Q) = -(X * X * Q) := by
    rw [← h]
    calc X * ((Y - X) * Q) = (X * Y - X * X) * Q := by rw [← mul_assoc, mul_sub]
      _ = -(X * X * Q) := by rw [hXY, zero_sub, neg_mul]
  have hW0 : star (X * Q) * (X * Q) = 0 := by
    refine eq_zero_of_isPositive_of_neg_isPositive hWpos ?_
    rw [hW, ← hneg]
    exact hpos
  exact eq_zero_of_star_mul_self_eq_zero hW0

omit [CompleteSpace H] in
theorem commute_sub_smul_one {A S : H →L[ℂ] H} (h : S * A = A * S) (c : ℂ) :
    S * (A - c • (1 : H →L[ℂ] H)) = (A - c • (1 : H →L[ℂ] H)) * S := by
  rw [mul_sub, sub_mul, h, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- Lowering a self-adjoint operator by a nonnegative constant shrinks the range projection of
its positive part. -/
theorem rangeProjection_posPart_nested {T₁ T₂ : H →L[ℂ] H} (h₁ : IsSelfAdjoint T₁)
    (h₂ : IsSelfAdjoint T₂) {c : ℝ} (hc : 0 ≤ c)
    (h : T₂ = T₁ - (c : ℂ) • (1 : H →L[ℂ] H)) :
    rangeProjection T₁⁺ * rangeProjection T₂⁺ = rangeProjection T₂⁺ := by
  have h12 : T₁ * T₂ = T₂ * T₁ := by
    rw [h]
    exact commute_sub_smul_one (A := T₁) (S := T₁) rfl (c : ℂ)
  have hX : (T₂⁺).IsPositive := posPart_isPositive T₂
  have hY₁ : (T₁⁻).IsPositive := negPart_isPositive T₁
  have hEsa : IsSelfAdjoint (rangeProjection T₁⁺) := rangeProjection_isSelfAdjoint _
  have hEE : rangeProjection T₁⁺ * rangeProjection T₁⁺ = rangeProjection T₁⁺ :=
    rangeProjection_idem _
  have h1sa : IsSelfAdjoint (1 : H →L[ℂ] H) := by
    first | exact IsSelfAdjoint.one _
  have hQsa : IsSelfAdjoint (1 - rangeProjection T₁⁺) := h1sa.sub hEsa
  have hQ : (1 - rangeProjection T₁⁺) * (1 - rangeProjection T₁⁺) = 1 - rangeProjection T₁⁺ := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hEE, sub_self, sub_zero]
  have hXT : T₂⁺ * T₁ = T₁ * T₂⁺ := (commute_posPart h12).symm
  have hXT' : star T₂⁺ * T₁ = T₁ * star T₂⁺ := by
    rw [hX.isSelfAdjoint.star_eq]
    exact hXT
  have hEX : rangeProjection T₁⁺ * T₂⁺ = T₂⁺ * rangeProjection T₁⁺ :=
    rangeProjection_posPart_commute hXT hXT'
  have hQX : (1 - rangeProjection T₁⁺) * T₂⁺ = T₂⁺ * (1 - rangeProjection T₁⁺) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hEX]
  have hXY₁ : T₂⁺ * T₁⁻ = T₁⁻ * T₂⁺ := commute_negPart hXT
  have hkey : (T₂⁻ - T₂⁺) * (1 - rangeProjection T₁⁺)
      = T₁⁻ + (c : ℂ) • (1 - rangeProjection T₁⁺) := by
    have h3 : T₂⁺ - T₂⁻ = T₂ := CFC.posPart_sub_negPart T₂ h₂
    have h4 : T₂⁻ - T₂⁺ = -T₁ + (c : ℂ) • (1 : H →L[ℂ] H) := by
      rw [← neg_sub T₂⁺ T₂⁻, h3, h]
      first
        | abel
    rw [h4, add_mul, neg_mul_one_sub_rangeProjection_posPart h₁, smul_mul_assoc, one_mul]
  have hXQ : T₂⁺ * (1 - rangeProjection T₁⁺) = 0 :=
    mul_eq_zero_of_sub_mul_eq hX hY₁ hQsa hQ (CFC.posPart_mul_negPart T₂) hQX hXY₁ hc hkey
  have hfix : rangeProjection T₁⁺ * T₂⁺ = T₂⁺ := by
    rw [hEX]
    have hexp : T₂⁺ * (1 - rangeProjection T₁⁺) = T₂⁺ - T₂⁺ * rangeProjection T₁⁺ := by
      rw [mul_sub, mul_one]
    rw [hexp] at hXQ
    exact (sub_eq_zero.mp hXQ).symm
  exact rangeProjection_mul_rangeProjection_of_mul_eq hfix

/-! ### Threshold projections -/

theorem isSelfAdjoint_ofReal_smul_one (u : ℝ) :
    IsSelfAdjoint ((u : ℂ) • (1 : H →L[ℂ] H)) := by
  have h1sa : IsSelfAdjoint (1 : H →L[ℂ] H) := by
    first | exact IsSelfAdjoint.one _
  have hu : IsSelfAdjoint (u : ℂ) := by
    first
      | exact Complex.conj_ofReal u
  first
    | exact IsSelfAdjoint.smul hu h1sa

theorem isSelfAdjoint_sub_ofReal_smul_one {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (u : ℝ) :
    IsSelfAdjoint (A - (u : ℂ) • (1 : H →L[ℂ] H)) :=
  hsa.sub (isSelfAdjoint_ofReal_smul_one u)

/-- The threshold projection of `A` at level `u`: the range projection of the positive part
of `A - u`. -/
def thresholdProjection (A : H →L[ℂ] H) (u : ℝ) : H →L[ℂ] H :=
  rangeProjection (A - (u : ℂ) • (1 : H →L[ℂ] H))⁺

theorem thresholdProjection_mem (M : VonNeumannAlgebra H) {A : H →L[ℂ] H} (hA : A ∈ M)
    (u : ℝ) : thresholdProjection A u ∈ M := by
  unfold thresholdProjection
  exact rangeProjection_mem M
    (posPart_mem M (sub_mem hA (smul_mem_vonNeumann M _ (one_mem M))))

theorem thresholdProjection_isSelfAdjoint (A : H →L[ℂ] H) (u : ℝ) :
    IsSelfAdjoint (thresholdProjection A u) := by
  unfold thresholdProjection
  exact rangeProjection_isSelfAdjoint _

theorem thresholdProjection_idem (A : H →L[ℂ] H) (u : ℝ) :
    thresholdProjection A u * thresholdProjection A u = thresholdProjection A u := by
  unfold thresholdProjection
  exact rangeProjection_idem _

/-- Anything commuting (together with its adjoint) with `A` commutes with the threshold
projections of `A`. -/
theorem thresholdProjection_commute {A S : H →L[ℂ] H} (h : S * A = A * S)
    (h' : star S * A = A * star S) (u : ℝ) :
    thresholdProjection A u * S = S * thresholdProjection A u := by
  unfold thresholdProjection
  exact rangeProjection_posPart_commute (commute_sub_smul_one h _) (commute_sub_smul_one h' _)

theorem thresholdProjection_commute_self {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (u : ℝ) :
    thresholdProjection A u * A = A * thresholdProjection A u := by
  have h' : star A * A = A * star A := by rw [hsa.star_eq]
  exact thresholdProjection_commute rfl h' u

theorem sub_mul_thresholdProjection_isPositive {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A)
    (u : ℝ) :
    ((A - (u : ℂ) • (1 : H →L[ℂ] H)) * thresholdProjection A u).IsPositive := by
  unfold thresholdProjection
  exact mul_rangeProjection_posPart_isPositive (isSelfAdjoint_sub_ofReal_smul_one hsa u)

theorem sub_mul_one_sub_thresholdProjection_isPositive {A : H →L[ℂ] H}
    (hsa : IsSelfAdjoint A) (u : ℝ) :
    (((u : ℂ) • (1 : H →L[ℂ] H) - A) * (1 - thresholdProjection A u)).IsPositive := by
  have hneg : (u : ℂ) • (1 : H →L[ℂ] H) - A = -(A - (u : ℂ) • (1 : H →L[ℂ] H)) :=
    (neg_sub A ((u : ℂ) • (1 : H →L[ℂ] H))).symm
  rw [hneg]
  unfold thresholdProjection
  exact neg_mul_one_sub_rangeProjection_posPart_isPositive
    (isSelfAdjoint_sub_ofReal_smul_one hsa u)

theorem thresholdProjection_mul_of_le {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) {u v : ℝ}
    (huv : u ≤ v) :
    thresholdProjection A u * thresholdProjection A v = thresholdProjection A v := by
  have hrel : A - (v : ℂ) • (1 : H →L[ℂ] H)
      = (A - (u : ℂ) • (1 : H →L[ℂ] H)) - ((v - u : ℝ) : ℂ) • (1 : H →L[ℂ] H) := by
    rw [Complex.ofReal_sub, sub_smul]
    abel
  unfold thresholdProjection
  exact rangeProjection_posPart_nested (isSelfAdjoint_sub_ofReal_smul_one hsa u)
    (isSelfAdjoint_sub_ofReal_smul_one hsa v) (sub_nonneg.mpr huv) hrel

/-- **Threshold projections.**  A self-adjoint element `A` of a von Neumann algebra `M` has a
decreasing family of projections `E u ∈ M` commuting with `A` such that `A ≥ u` on the range
of `E u` and `A ≤ u` on the range of `1 - E u`. -/
theorem exists_threshold_projections (M : VonNeumannAlgebra H) {A : H →L[ℂ] H}
    (hA : A ∈ M) (hsa : IsSelfAdjoint A) :
    ∃ E : ℝ → (H →L[ℂ] H),
      (∀ u, E u ∈ M) ∧ (∀ u, IsSelfAdjoint (E u)) ∧ (∀ u, E u * E u = E u) ∧
      (∀ u, E u * A = A * E u) ∧
      (∀ u : ℝ, ((A - (u : ℂ) • (1 : H →L[ℂ] H)) * E u).IsPositive) ∧
      (∀ u : ℝ, (((u : ℂ) • (1 : H →L[ℂ] H) - A) * (1 - E u)).IsPositive) ∧
      (∀ u v, u ≤ v → E u * E v = E v) :=
  ⟨thresholdProjection A,
    fun u => thresholdProjection_mem M hA u,
    fun u => thresholdProjection_isSelfAdjoint A u,
    fun u => thresholdProjection_idem A u,
    fun u => thresholdProjection_commute_self hsa u,
    fun u => sub_mul_thresholdProjection_isPositive hsa u,
    fun u => sub_mul_one_sub_thresholdProjection_isPositive hsa u,
    fun _ _ huv => thresholdProjection_mul_of_le hsa huv⟩

end

end VacuumBellSeparation
