/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Ftau.GoodPosition
public import LeanPool.HyperellipticCurves.RedJ.RedIdealPrincipal

/-!
# Conditions on tuples of curve points: the avoidance principle (towards `lem:tau-generic`)

Polynomial conditions on `g`-tuples of points of the affine curve `y² = f(x)`, and the
**domain property** — "`C^g` is irreducible", at the evaluation level: a product of
conditions vanishing at every tuple of curve points has a factor that does
(`ChabautyColeman.curveVanishing_mul`). By induction on `g`: splitting off the last
point (`ChabautyColeman.lastSplit`) and reducing modulo its curve relation
(`ChabautyColeman.ySq`, `ChabautyColeman.redCoeff`), a condition becomes a function
`A₀(x) + A₁(x)·y` of the last point with coefficient conditions on the initial tuple
(`ChabautyColeman.eval_snoc_eq`); the one-point case is the norm argument
(`ChabautyColeman.curve_pair_mul_eq_zero`, via
`ChabautyColeman.sq_sub_mul_sq_ne_zero` and `ChabautyColeman.finite_curve_zeros`).

The consequence is the **avoidance principle**
(`ChabautyColeman.exists_curveTuple_ne_zero`): finitely many conditions, each
nonvanishing at *some* tuple of curve points, admit a *common* witness tuple. This is
the engine behind the all-genus centre-fold witness (`lem:tau-generic`): each fold
condition needs only its own convenient witness configuration, and a single
good-position tuple then satisfies all the conditions simultaneously.

A condition can be refuted by evaluating it at a **formal family** of curve points over
any commutative `K`-algebra (`ChabautyColeman.not_curveVanishing_of_aeval_ne_zero`);
this is the certificate form the fold witness uses —
`LeanPool.HyperellipticCurves.Log.Fold.FoldWitness`
refutes each fold-condition numerator at the all-at-infinity family of
`LeanPool.HyperellipticCurves.Log.Witness.InfinityFamily`, at the common rates of the cusp descent.
(The per-disk conditions go through the pencil instead,
`LeanPool.HyperellipticCurves.Log.Witness.DiskPencil`.)
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section CurveLevel

variable {κ : Type*} [Field κ] {f : κ[X]}

/-- A function `g₀ + g₁·y` vanishing at every point of the affine curve is zero. -/
theorem eq_zero_of_forall_curve_eval [IsAlgClosed κ] (hf : f.Monic)
    (hodd : Odd f.natDegree) {g₀ g₁ : κ[X]}
    (h : ∀ p : κ × κ, p.2 ^ 2 = f.eval p.1 → g₀.eval p.1 + g₁.eval p.1 * p.2 = 0) :
    g₀ = 0 ∧ g₁ = 0 := by
  by_contra hne
  have hg := not_and_or.mp hne
  have hfin := finite_curve_zeros hf hodd hg
  have hinf := residue_curve_points_infinite (f := f) hf.ne_zero
  exact hinf.not_finite (hfin.subset fun z ⟨hz, _⟩ ↦ ⟨hz, h z hz⟩)

/-- **The curve-function domain property**: if the product of two functions `g₀ + g₁·y`
vanishes identically on the affine curve, one of the factors does. -/
theorem curve_pair_mul_eq_zero [IsAlgClosed κ] (hf : f.Monic) (hodd : Odd f.natDegree)
    {a b c d : κ[X]}
    (h : ∀ p : κ × κ, p.2 ^ 2 = f.eval p.1 →
      (a.eval p.1 + b.eval p.1 * p.2) * (c.eval p.1 + d.eval p.1 * p.2) = 0) :
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by
  -- the product is the curve function of the product pair
  have hprod : ∀ p : κ × κ, p.2 ^ 2 = f.eval p.1 →
      (a * c + f * (b * d)).eval p.1 + (a * d + b * c).eval p.1 * p.2 = 0 := by
    intro p hp
    have h1 := h p hp
    simp only [eval_add, eval_mul]
    linear_combination h1 - eval p.1 b * eval p.1 d * hp
  obtain ⟨h₀, h₁⟩ := eq_zero_of_forall_curve_eval hf hodd hprod
  -- norms multiply
  have hnorm : (a ^ 2 - f * b ^ 2) * (c ^ 2 - f * d ^ 2) = 0 := by
    linear_combination (a * c + f * (b * d)) * h₀ - f * (a * d + b * c) * h₁
  exact (mul_eq_zero.mp hnorm).imp
    (fun h2 ↦ of_not_not fun hab ↦ sq_sub_mul_sq_ne_zero hodd hab h2)
    fun h2 ↦ of_not_not fun hcd ↦ sq_sub_mul_sq_ne_zero hodd hcd h2

end CurveLevel

section Tuples

/-- The coordinate assignment of a tuple of plane points (over any coordinate ring, so
that formal families of curve points — e.g. over `K⟦ε⟧` — can be evaluated as well). -/
def tupleCoords {R : Type*} {g : ℕ} (P : Fin g → R × R) : Fin g × Fin 2 → R :=
  fun s ↦ ![(P s.1).1, (P s.1).2] s.2

@[simp] theorem tupleCoords_zero {R : Type*} {g : ℕ} (P : Fin g → R × R) (i : Fin g) :
    tupleCoords P (i, 0) = (P i).1 := rfl

@[simp] theorem tupleCoords_one {R : Type*} {g : ℕ} (P : Fin g → R × R) (i : Fin g) :
    tupleCoords P (i, 1) = (P i).2 := rfl

variable {κ : Type*} [Field κ] (f : κ[X])

/-- A tuple of points on the affine curve `y² = f(x)`. -/
def IsCurveTuple {g : ℕ} (P : Fin g → κ × κ) : Prop :=
  ∀ i, (P i).2 ^ 2 = f.eval (P i).1

/-- A polynomial condition vanishing at every tuple of curve points. -/
def CurveVanishing (g : ℕ) (F : MvPolynomial (Fin g × Fin 2) κ) : Prop :=
  ∀ P : Fin g → κ × κ, IsCurveTuple f P → MvPolynomial.eval (tupleCoords P) F = 0

variable {f}

theorem isCurveTuple_snoc {g : ℕ} {P : Fin g → κ × κ} {p : κ × κ}
    (hP : IsCurveTuple f P) (hp : p.2 ^ 2 = f.eval p.1) :
    IsCurveTuple f (Fin.snoc P p) := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rwa [Fin.snoc_last]
  · rw [Fin.snoc_castSucc]
    exact hP j

variable (f)

/-- Split off the last point: the variables of the last point become the (inner) `x` and
(outer) `y` polynomial variables. -/
noncomputable def lastSplit (g : ℕ) :
    MvPolynomial (Fin (g + 1) × Fin 2) κ →ₐ[κ]
      Polynomial (Polynomial (MvPolynomial (Fin g × Fin 2) κ)) :=
  MvPolynomial.aeval fun s ↦ Fin.lastCases
    (motive := fun _ ↦ Polynomial (Polynomial (MvPolynomial (Fin g × Fin 2) κ)))
    (![Polynomial.C Polynomial.X, Polynomial.X] s.2)
    (fun i ↦ Polynomial.C (Polynomial.C (MvPolynomial.X (i, s.2)))) s.1

/-- The evaluation of a split condition at a tuple with an appended point. -/
noncomputable def sndEval {g : ℕ} (P : Fin g → κ × κ) (p : κ × κ) :
    Polynomial (Polynomial (MvPolynomial (Fin g × Fin 2) κ)) →+* κ :=
  (Polynomial.evalRingHom p.2).comp ((Polynomial.mapRingHom
    (Polynomial.evalRingHom p.1)).comp (Polynomial.mapRingHom (Polynomial.mapRingHom
      (MvPolynomial.eval (tupleCoords P)))))

theorem eval_snoc_eq_sndEval {g : ℕ} (P : Fin g → κ × κ) (p : κ × κ)
    (F : MvPolynomial (Fin (g + 1) × Fin 2) κ) :
    MvPolynomial.eval (tupleCoords (Fin.snoc P p)) F
      = sndEval P p ((lastSplit (κ := κ) g) F) := by
  have h : (MvPolynomial.eval (tupleCoords (Fin.snoc P p)) :
        MvPolynomial (Fin (g + 1) × Fin 2) κ →+* κ)
      = (sndEval P p).comp (lastSplit (κ := κ) g).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun s ↦ ?_)
    · simp [sndEval, lastSplit]
    · obtain ⟨i, e⟩ := s
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · fin_cases e <;>
          simp [sndEval, lastSplit, tupleCoords, Fin.snoc_last]
      · fin_cases e <;>
          simp [sndEval, lastSplit, tupleCoords, Fin.snoc_castSucc]
  exact RingHom.congr_fun h F

variable {g : ℕ}

/-- The curve relation for the split-off last point. -/
noncomputable def ySq (g : ℕ) :
    Polynomial (Polynomial (MvPolynomial (Fin g × Fin 2) κ)) :=
  Polynomial.X ^ 2
    - Polynomial.C (f.map (MvPolynomial.C : κ →+* MvPolynomial (Fin g × Fin 2) κ))

theorem ySq_monic (g : ℕ) : (ySq f g).Monic :=
  monic_X_pow_sub (lt_of_le_of_lt degree_C_le (by norm_num))

/-- The reduced coefficient conditions of a condition: the split condition modulo the
curve relation of the last point has degree `< 2` in `y`; its `y`-coefficients are
polynomials in `x` whose coefficients are conditions on the initial tuple. -/
noncomputable def redCoeff (F : MvPolynomial (Fin (g + 1) × Fin 2) κ) (e : Fin 2)
    (k : ℕ) : MvPolynomial (Fin g × Fin 2) κ :=
  ((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff (e : ℕ)).coeff k

theorem sndEval_X {P : Fin g → κ × κ} {p : κ × κ} :
    sndEval (κ := κ) (g := g) P p Polynomial.X = p.2 := by
  simp [sndEval]

theorem sndEval_C {P : Fin g → κ × κ} {p : κ × κ}
    (c : Polynomial (MvPolynomial (Fin g × Fin 2) κ)) :
    sndEval P p (Polynomial.C c)
      = Polynomial.eval p.1 (c.map (MvPolynomial.eval (tupleCoords P))) := by
  simp [sndEval]

theorem sndEval_ySq {P : Fin g → κ × κ} {p : κ × κ} (hp : p.2 ^ 2 = f.eval p.1) :
    sndEval P p (ySq f g) = 0 := by
  rw [ySq, map_sub (sndEval P p), map_pow (sndEval P p), sndEval_C, sndEval_X]
  have hf : (f.map (MvPolynomial.C : κ →+* MvPolynomial (Fin g × Fin 2) κ)).map
      (MvPolynomial.eval (tupleCoords P)) = f := by
    rw [Polynomial.map_map]
    have hcomp : (MvPolynomial.eval (tupleCoords P)).comp
        (MvPolynomial.C : κ →+* MvPolynomial (Fin g × Fin 2) κ) = RingHom.id κ :=
      RingHom.ext fun r ↦ by simp
    rw [hcomp, Polynomial.map_id]
  rw [hf]
  linear_combination hp

/-- **The on-curve evaluation identity**: at a tuple with an appended curve point, a
condition evaluates through the two reduced coefficient polynomials. -/
theorem eval_snoc_eq (P : Fin g → κ × κ) {p : κ × κ}
    (hp : p.2 ^ 2 = f.eval p.1) (F : MvPolynomial (Fin (g + 1) × Fin 2) κ) :
    MvPolynomial.eval (tupleCoords (Fin.snoc P p)) F
      = Polynomial.eval p.1 (((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 0).map
          (MvPolynomial.eval (tupleCoords P)))
        + Polynomial.eval p.1 (((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 1).map
            (MvPolynomial.eval (tupleCoords P))) * p.2 := by
  rw [eval_snoc_eq_sndEval]
  set H := (lastSplit (κ := κ) g) F
  rcases eq_or_ne (H %ₘ ySq f g) 0 with h0 | h0
  · have hHe : H = ySq f g * (H /ₘ ySq f g) := by
      nth_rw 1 [← modByMonic_add_div H (ySq f g)]
      rw [h0, zero_add]
    rw [h0]
    simp only [Polynomial.coeff_zero, Polynomial.map_zero, Polynomial.eval_zero,
      zero_mul, add_zero]
    rw [hHe, map_mul (sndEval P p), sndEval_ySq f hp, zero_mul]
  · have hdeg : (H %ₘ ySq f g).degree < (ySq f g).degree :=
      degree_modByMonic_lt H (ySq_monic f g)
    have hy : (ySq f g).degree = 2 := by
      rw [ySq, degree_sub_eq_left_of_degree_lt
        (by rw [degree_X_pow]; exact lt_of_le_of_lt degree_C_le (by norm_num))]
      exact degree_X_pow 2
    rw [hy] at hdeg
    have h1 : (H %ₘ ySq f g).degree ≤ 1 := by
      have h2 := (natDegree_lt_iff_degree_lt h0).mpr hdeg
      exact_mod_cast degree_le_of_natDegree_le
        (show (H %ₘ ySq f g).natDegree ≤ 1 by lia)
    have hrep := eq_X_add_C_of_degree_le_one h1
    nth_rw 1 [← modByMonic_add_div H (ySq f g)]
    rw [map_add (sndEval P p), map_mul (sndEval P p), sndEval_ySq f hp, zero_mul,
      add_zero]
    nth_rw 1 [hrep]
    rw [map_add (sndEval P p), map_mul (sndEval P p), sndEval_C, sndEval_C, sndEval_X]
    ring

/-- A condition all of whose reduced coefficient conditions vanish, vanishes. -/
theorem curveVanishing_of_forall_redCoeff {F : MvPolynomial (Fin (g + 1) × Fin 2) κ}
    (hall : ∀ (e : Fin 2) (k : ℕ), CurveVanishing f g (redCoeff f F e k)) :
    CurveVanishing f (g + 1) F := by
  intro Q hQ
  have hQi : IsCurveTuple f (Fin.init Q) := fun i ↦ hQ i.castSucc
  have hql : (Q (Fin.last g)).2 ^ 2 = f.eval (Q (Fin.last g)).1 := hQ _
  rw [show Q = Fin.snoc (Fin.init Q) (Q (Fin.last g)) from (Fin.snoc_init_self Q).symm,
    eval_snoc_eq f (Fin.init Q) hql F]
  have hc0 : ((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 0).map
      (MvPolynomial.eval (tupleCoords (Fin.init Q))) = 0 :=
    Polynomial.ext fun k ↦ by
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      exact hall 0 k (Fin.init Q) hQi
  have hc1 : ((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 1).map
      (MvPolynomial.eval (tupleCoords (Fin.init Q))) = 0 :=
    Polynomial.ext fun k ↦ by
      rw [Polynomial.coeff_map, Polynomial.coeff_zero]
      exact hall 1 k (Fin.init Q) hQi
  rw [hc0, hc1]
  simp

end Tuples

section Domain

variable {κ : Type*} [Field κ] [IsAlgClosed κ] {f : κ[X]}

/-- **The domain property of curve-tuple conditions** ("`C^g` is irreducible", at the
evaluation level): a product of conditions vanishing at every tuple of curve points has
a factor that does. -/
theorem curveVanishing_mul (hf : f.Monic) (hodd : Odd f.natDegree) :
    ∀ (g : ℕ) (F G : MvPolynomial (Fin g × Fin 2) κ),
      CurveVanishing f g (F * G) → CurveVanishing f g F ∨ CurveVanishing f g G := by
  intro g
  induction g with
  | zero =>
    intro F G h
    by_cases hF : CurveVanishing f 0 F
    · exact Or.inl hF
    right
    intro P hP
    have hFG := h P hP
    rw [map_mul] at hFG
    rcases mul_eq_zero.mp hFG with h1 | h1
    · exact absurd (fun Q hQ ↦ (Subsingleton.elim Q P : Q = P) ▸ h1) hF
    · exact h1
  | succ g ih =>
    intro F G h
    classical
    by_cases hF : ∀ (e : Fin 2) (k : ℕ), CurveVanishing f g (redCoeff f F e k)
    · exact Or.inl (curveVanishing_of_forall_redCoeff f hF)
    right
    push Not at hF
    obtain ⟨e₀, k₀, hφ⟩ := hF
    refine curveVanishing_of_forall_redCoeff f fun e k ↦ ?_
    have hprod : CurveVanishing f g (redCoeff f F e₀ k₀ * redCoeff f G e k) := by
      intro P hP
      -- the pair functions of `F` and `G` at `P` multiply to zero on the curve
      have hpair : ∀ p : κ × κ, p.2 ^ 2 = f.eval p.1 →
          (Polynomial.eval p.1 (((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 0).map
              (MvPolynomial.eval (tupleCoords P)))
            + Polynomial.eval p.1 (((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 1).map
                (MvPolynomial.eval (tupleCoords P))) * p.2)
          * (Polynomial.eval p.1 (((((lastSplit (κ := κ) g) G) %ₘ ySq f g).coeff 0).map
              (MvPolynomial.eval (tupleCoords P)))
            + Polynomial.eval p.1 (((((lastSplit (κ := κ) g) G) %ₘ ySq f g).coeff 1).map
                (MvPolynomial.eval (tupleCoords P))) * p.2) = 0 := by
        intro p hp
        rw [← eval_snoc_eq f P hp F, ← eval_snoc_eq f P hp G, ← map_mul]
        exact h (Fin.snoc P p) (isCurveTuple_snoc hP hp)
      rcases curve_pair_mul_eq_zero hf hodd hpair with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · rw [map_mul]
        refine mul_eq_zero_of_left ?_ _
        have hzero : ((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff ((e₀ : Fin 2) : ℕ)).map
            (MvPolynomial.eval (tupleCoords P)) = 0 := by
          fin_cases e₀
          · exact hA
          · exact hB
        have h2 := congrArg (fun q : κ[X] ↦ q.coeff k₀) hzero
        rwa [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
      · rw [map_mul]
        refine mul_eq_zero_of_right _ ?_
        have hzero : ((((lastSplit (κ := κ) g) G) %ₘ ySq f g).coeff ((e : Fin 2) : ℕ)).map
            (MvPolynomial.eval (tupleCoords P)) = 0 := by
          fin_cases e
          · exact hA
          · exact hB
        have h2 := congrArg (fun q : κ[X] ↦ q.coeff k) hzero
        rwa [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
    rcases ih _ _ hprod with h1 | h1
    · exact absurd h1 hφ
    · exact h1

/-- Some tuple of curve points exists. -/
theorem exists_isCurveTuple (hf : f.Monic) (g : ℕ) :
    ∃ P : Fin g → κ × κ, IsCurveTuple f P := by
  obtain ⟨p, hp⟩ := (residue_curve_points_infinite (f := f) hf.ne_zero).nonempty
  exact ⟨fun _ ↦ p, fun _ ↦ hp.1⟩

/-- **Common nonvanishing** (the avoidance principle): finitely many conditions, each
nonvanishing at some tuple of curve points, admit a common witness tuple. -/
theorem exists_curveTuple_ne_zero (hf : f.Monic) (hodd : Odd f.natDegree) {g : ℕ}
    (S : Finset (MvPolynomial (Fin g × Fin 2) κ))
    (hS : ∀ F ∈ S, ¬CurveVanishing f g F) :
    ∃ P : Fin g → κ × κ, IsCurveTuple f P
      ∧ ∀ F ∈ S, MvPolynomial.eval (tupleCoords P) F ≠ 0 := by
  classical
  have hprod : ¬CurveVanishing f g (∏ F ∈ S, F) := by
    induction S using Finset.induction with
    | empty =>
      intro hv
      obtain ⟨P, hP⟩ := exists_isCurveTuple hf g
      simpa using hv P hP
    | insert F T hFT ihT =>
      intro hv
      rw [Finset.prod_insert hFT] at hv
      rcases curveVanishing_mul hf hodd g _ _ hv with h1 | h1
      · exact hS F (Finset.mem_insert_self F T) h1
      · exact ihT (fun F' hF' ↦ hS F' (Finset.mem_insert_of_mem hF')) h1
  rw [CurveVanishing] at hprod
  push Not at hprod
  obtain ⟨P, hP, hne⟩ := hprod
  exact ⟨P, hP, fun F hF h0 ↦ hne (by rw [map_prod]; exact Finset.prod_eq_zero hF h0)⟩

end Domain

section CurveIdeal

variable {κ : Type*} [Field κ] (f : κ[X]) {g : ℕ}

/-- **The ideal of the curve-tuple relations** `yᵢ² = f(xᵢ)`: the algebraic counterpart of
`ChabautyColeman.CurveVanishing` — over an algebraically closed field, vanishing at every
tuple of curve points is membership in this ideal, which is what lets a condition be
refuted by evaluation at a *formal family* of curve points
(`ChabautyColeman.not_curveVanishing_of_aeval_ne_zero`). -/
noncomputable def curveIdeal (g : ℕ) : Ideal (MvPolynomial (Fin g × Fin 2) κ) :=
  Ideal.span (Set.range fun i : Fin g ↦
    MvPolynomial.X (i, 1) ^ 2 - Polynomial.aeval (MvPolynomial.X (i, 0)) f)

/-- Evaluation at a family of curve points over any commutative algebra kills the curve
ideal. The family may live in any `κ`-algebra — e.g. `K⟦ε⟧` for a degenerating family. -/
theorem aeval_eq_zero_of_mem_curveIdeal {A : Type*} [CommRing A] [Algebra κ A]
    {P : Fin g → A × A} (hP : ∀ i, (P i).2 ^ 2 = Polynomial.aeval (P i).1 f)
    {F : MvPolynomial (Fin g × Fin 2) κ} (hF : F ∈ curveIdeal f g) :
    MvPolynomial.aeval (tupleCoords P) F = 0 := by
  have hle : curveIdeal f g
      ≤ RingHom.ker (MvPolynomial.aeval (R := κ) (S₁ := A) (tupleCoords P)) := by
    rw [curveIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have hcomp : MvPolynomial.aeval (tupleCoords P)
        (Polynomial.aeval (MvPolynomial.X (i, 0) : MvPolynomial (Fin g × Fin 2) κ) f)
          = Polynomial.aeval (tupleCoords P (i, 0)) f := by
      rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
    simp only [map_sub, map_pow, MvPolynomial.aeval_X, hcomp]
    rw [tupleCoords_zero, tupleCoords_one, hP i, sub_self]
  exact hle hF

/-- Reassembling a split condition: the (ring-homomorphism) inverse of
`ChabautyColeman.lastSplit`, sending the outer variable to the last `y`, the inner
variable to the last `x`, and embedding the initial tuple's variables. -/
noncomputable def lastJoin (g : ℕ) :
    Polynomial (Polynomial (MvPolynomial (Fin g × Fin 2) κ))
      →+* MvPolynomial (Fin (g + 1) × Fin 2) κ :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom
      (MvPolynomial.rename (Prod.map (Fin.castSucc (n := g)) (id (α := Fin 2)))).toRingHom
      (MvPolynomial.X (Fin.last g, 0)))
    (MvPolynomial.X (Fin.last g, 1))

theorem lastJoin_comp_lastSplit :
    (lastJoin (κ := κ) g).comp (lastSplit (κ := κ) g).toRingHom
      = RingHom.id (MvPolynomial (Fin (g + 1) × Fin 2) κ) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun s ↦ ?_)
  · simp [lastSplit, lastJoin]
  · obtain ⟨i, e⟩ := s
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · fin_cases e <;> simp [lastSplit, lastJoin]
    · fin_cases e <;> simp [lastSplit, lastJoin, Prod.map]

theorem lastJoin_lastSplit (F : MvPolynomial (Fin (g + 1) × Fin 2) κ) :
    lastJoin (κ := κ) g ((lastSplit (κ := κ) g) F) = F :=
  RingHom.congr_fun lastJoin_comp_lastSplit F

/-- The variable embedding of an initial tuple maps the curve ideal into the curve ideal. -/
theorem rename_castSucc_mem_curveIdeal {F : MvPolynomial (Fin g × Fin 2) κ}
    (hF : F ∈ curveIdeal f g) :
    MvPolynomial.rename (Prod.map Fin.castSucc id) F ∈ curveIdeal f (g + 1) := by
  have hle : (curveIdeal f g).map
      (MvPolynomial.rename (Prod.map (Fin.castSucc (n := g)) (id (α := Fin 2)))).toRingHom
        ≤ curveIdeal f (g + 1) := by
    rw [curveIdeal, Ideal.map_span, Ideal.span_le]
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨i.castSucc, ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_sub, map_pow, MvPolynomial.rename_X, ← Polynomial.aeval_algHom_apply,
      MvPolynomial.rename_X]
    rfl
  exact hle (Ideal.mem_map_of_mem _ hF)

/-- A polynomial in the last `x` whose coefficient conditions on the initial tuple lie in
the curve ideal lands in the curve ideal. -/
theorem eval₂_rename_mem_curveIdeal {c : Polynomial (MvPolynomial (Fin g × Fin 2) κ)}
    (hc : ∀ k, c.coeff k ∈ curveIdeal f g) :
    Polynomial.eval₂
      (MvPolynomial.rename (Prod.map (Fin.castSucc (n := g)) (id (α := Fin 2)))).toRingHom
      (MvPolynomial.X (Fin.last g, 0)) c ∈ curveIdeal f (g + 1) := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum]
  exact Submodule.sum_mem _ fun k _ ↦
    Ideal.mul_mem_right _ _ (rename_castSucc_mem_curveIdeal f (hc k))

theorem lastJoin_C (c : Polynomial (MvPolynomial (Fin g × Fin 2) κ)) :
    lastJoin (κ := κ) g (Polynomial.C c) = Polynomial.eval₂
      (MvPolynomial.rename (Prod.map (Fin.castSucc (n := g)) (id (α := Fin 2)))).toRingHom
      (MvPolynomial.X (Fin.last g, 0)) c := by
  rw [lastJoin]
  simp

theorem lastJoin_ySq :
    lastJoin (κ := κ) g (ySq f g)
      = MvPolynomial.X (Fin.last g, 1) ^ 2
        - Polynomial.aeval (MvPolynomial.X (Fin.last g, 0)) f := by
  rw [ySq, lastJoin]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_map]
  have hCC : (MvPolynomial.rename (Prod.map (Fin.castSucc (n := g))
      (id (α := Fin 2)))).toRingHom.comp (MvPolynomial.C (R := κ) (σ := Fin g × Fin 2))
        = MvPolynomial.C (R := κ) (σ := Fin (g + 1) × Fin 2) :=
    RingHom.ext fun a ↦ MvPolynomial.rename_C _ a
  rw [hCC, Polynomial.aeval_def, MvPolynomial.algebraMap_eq]

/-- **Curve-vanishing conditions lie in the curve ideal**: over an algebraically closed
field, a condition vanishing at every tuple of curve points is an algebraic combination
of the curve relations. By induction on the tuple length: the pair function of the last
point vanishes on the curve, so both its coefficient polynomials vanish
(`ChabautyColeman.eq_zero_of_forall_curve_eval`), and the reassembly along
`ChabautyColeman.lastJoin` expresses the condition as (reduced coefficients, in the ideal
by induction) plus a multiple of the last curve relation. -/
theorem mem_curveIdeal_of_curveVanishing [IsAlgClosed κ] (hf : f.Monic)
    (hodd : Odd f.natDegree) {F : MvPolynomial (Fin g × Fin 2) κ}
    (hF : CurveVanishing f g F) : F ∈ curveIdeal f g := by
  induction g with
  | zero =>
    obtain ⟨a, rfl⟩ := MvPolynomial.C_surjective (σ := Fin 0 × Fin 2) F
    obtain ⟨P, hP⟩ := exists_isCurveTuple hf 0
    have h0 := hF P hP
    rw [MvPolynomial.eval_C] at h0
    rw [h0, map_zero]
    exact Ideal.zero_mem _
  | succ g ih =>
    have hred : ∀ (e : Fin 2) (k : ℕ), CurveVanishing f g (redCoeff f F e k) := by
      intro e k P hP
      have hpair : ∀ p : κ × κ, p.2 ^ 2 = f.eval p.1 →
          Polynomial.eval p.1 (((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 0).map
              (MvPolynomial.eval (tupleCoords P)))
            + Polynomial.eval p.1 (((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff 1).map
                (MvPolynomial.eval (tupleCoords P))) * p.2 = 0 := by
        intro p hp
        rw [← eval_snoc_eq f P hp F]
        exact hF _ (isCurveTuple_snoc hP hp)
      obtain ⟨h0, h1⟩ := eq_zero_of_forall_curve_eval hf hodd hpair
      have hcoeff : ∀ e' : Fin 2,
          ((((lastSplit (κ := κ) g) F) %ₘ ySq f g).coeff (e' : ℕ)).map
              (MvPolynomial.eval (tupleCoords P)) = 0 →
            MvPolynomial.eval (tupleCoords P) (redCoeff f F e' k) = 0 := by
        intro e' he'
        have h2 := congrArg (fun q : κ[X] ↦ q.coeff k) he'
        rwa [Polynomial.coeff_map, Polynomial.coeff_zero] at h2
      fin_cases e
      · exact hcoeff 0 h0
      · exact hcoeff 1 h1
    -- reassemble along the division by the last curve relation
    have hFeq : F = lastJoin (κ := κ) g ((lastSplit (κ := κ) g) F %ₘ ySq f g)
        + lastJoin (κ := κ) g (ySq f g)
          * lastJoin (κ := κ) g ((lastSplit (κ := κ) g) F /ₘ ySq f g) := by
      nth_rw 1 [← lastJoin_lastSplit F]
      rw [← map_mul, ← map_add, Polynomial.modByMonic_add_div _ (ySq f g)]
    rw [hFeq]
    refine Ideal.add_mem _ ?_ ?_
    · set r := (lastSplit (κ := κ) g) F %ₘ ySq f g with hr
      have hdeg : r.degree ≤ 1 := by
        rcases eq_or_ne r 0 with h0 | h0
        · rw [h0, Polynomial.degree_zero]
          exact bot_le
        · have hlt := Polynomial.degree_modByMonic_lt ((lastSplit (κ := κ) g) F)
            (ySq_monic f g)
          have hy : (ySq f g).degree = 2 := by
            rw [ySq, Polynomial.degree_sub_eq_left_of_degree_lt (by
              rw [Polynomial.degree_X_pow]
              exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num))]
            exact Polynomial.degree_X_pow 2
          rw [← hr, hy] at hlt
          have h2 := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hlt
          exact_mod_cast Polynomial.degree_le_of_natDegree_le
            (show r.natDegree ≤ 1 by lia)
      rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg, map_add, map_mul, lastJoin_C,
        lastJoin_C]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) ?_
      · exact eval₂_rename_mem_curveIdeal f fun k ↦ ih (hred 1 k)
      · exact eval₂_rename_mem_curveIdeal f fun k ↦ ih (hred 0 k)
    · rw [lastJoin_ySq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Fin.last g, rfl⟩)

/-- **The family-refutation form of the avoidance engine**: a condition that evaluates to
something nonzero at a formal family of curve points — over any commutative `κ`-algebra,
e.g. a family over `K⟦ε⟧` degenerating onto special points — does not vanish identically
on tuples of curve points, and hence admits an honest witness tuple through
`ChabautyColeman.exists_curveTuple_ne_zero`. -/
theorem not_curveVanishing_of_aeval_ne_zero [IsAlgClosed κ] (hf : f.Monic)
    (hodd : Odd f.natDegree) {A : Type*} [CommRing A] [Algebra κ A]
    {P : Fin g → A × A} (hP : ∀ i, (P i).2 ^ 2 = Polynomial.aeval (P i).1 f)
    {F : MvPolynomial (Fin g × Fin 2) κ}
    (hne : MvPolynomial.aeval (tupleCoords P) F ≠ 0) :
    ¬CurveVanishing f g F :=
  fun hF ↦ hne (aeval_eq_zero_of_mem_curveIdeal f hP
    (mem_curveIdeal_of_curveVanishing f hf hodd hF))

end CurveIdeal

end ChabautyColeman

end
