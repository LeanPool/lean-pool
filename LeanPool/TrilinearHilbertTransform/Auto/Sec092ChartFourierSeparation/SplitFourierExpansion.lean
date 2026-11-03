/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec092ChartFourierSeparation.Setup

/-!
# Trilinear Hilbert transform: splitFourierExpansion
-/

@[expose] public section

section
open scoped FourierTransform
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform

open scoped Classical in
private def SplitFourierExpansionConclusion8Statement : Prop :=
  ∀ (c₀ : ℕ)
    (_ : (1 : ℕ) ≤ c₀)
    (k : ℕ)
    (R : ℝ)
    (Kψ : ℕ)
    (_ : (1 : ℕ) ≤ Kψ),
  let L₀ : ℝ :=
    Real.log ((5 : ℝ) * ((↑k : ℝ) * R + (1 : ℝ)) + (↑Kψ : ℝ) + (18 : ℝ))
  ∀ (_ : (0 : ℝ) ≤ L₀),
  let ccard : ℝ :=
    Real.log ((2 : ℝ) * (↑k : ℝ) * R + (7 : ℝ)) + (16 : ℝ)
  ∀ (_ : (0 : ℝ) ≤ ccard),
  let cht : ℝ :=
    Real.log ((20 : ℝ) * ((↑k : ℝ) * R + (1 : ℝ))) + Real.log ((2 : ℝ) * (↑k : ℝ) * R +
      (9 : ℝ)) + (56 : ℝ)
  ∀ (_ : (0 : ℝ) ≤ cht),
  let c3 : ℝ :=
    ((8 : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + ((4 : ℝ) * (↑Kψ : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + (18 :
      ℝ)) * (3 : ℝ)) * (L₀ + (4 : ℝ) + (3 : ℝ))
  ∀ (_ : (0 : ℝ) ≤ c3),
  let ctot : ℝ :=
    ccard + (2 : ℝ) + c3 + c3 + (7 : ℝ)
  ∀ (_ : ctot = ccard + (2 : ℝ) + c3 + c3 + (7 : ℝ)),
  let cJ : ℕ → ℝ :=
    fun (J : ℕ) => ccard + ((8 : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + ((4 : ℝ) * (↑Kψ : ℝ) + (3 :
      ℝ) * (↑c₀ : ℝ) + (18 : ℝ)) * ((4 : ℝ) * (↑J : ℝ) + (4 : ℝ))) * (L₀ + (4 : ℝ) + ((4
      : ℝ) * (↑J : ℝ) + (4 : ℝ))) + (8 : ℝ) * (↑J : ℝ) + (8 : ℝ)
  ∀ (_ : cJ = fun (J : ℕ) => ccard + ((8 : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + ((4 : ℝ) * (↑Kψ : ℝ) +
      (3 : ℝ) * (↑c₀ : ℝ) + (18 : ℝ)) * ((4 : ℝ) * (↑J : ℝ) + (4 : ℝ))) * (L₀ + (4 : ℝ)
      + ((4 : ℝ) * (↑J : ℝ) + (4 : ℝ))) + (8 : ℝ) * (↑J : ℝ) + (8 : ℝ))
    (H : ℝ)
    (B : ℝ),
  let X : ℝ :=
    (1 : ℝ) + Real.log H + Real.log B
  ∀ (_ : (0 : ℝ) ≤ Real.log B)
    (_ : (2 : ℝ) ≤ Real.log H),
  let D : ℕ :=
    ⌈ccard + cht + ctot + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)
  ∀ (_ : ∀ c ≤ ccard + cht + ctot + (↑c₀ : ℝ), Real.exp (c * X ^ (6 : ℕ)) ≤ Real.exp ((↑D :
      ℝ) * X ^ D))
    (_ : ∀ (J : ℕ), ∀ c ≤ cJ J + (↑c₀ : ℝ), Real.exp (c * X ^ (6 : ℕ)) ≤ Real.exp ((↑(⌈cJ J +
      (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) : ℝ) * X ^ (⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ))))
    (C : Matrix (Fin (0 : ℕ)) (Fin (0 : ℕ)) ℚ)
    (Q : Matrix (Fin (0 : ℕ)) (Fin (0 : ℕ)) ℚ)
    (_ : ∀ (i j : Fin (0 : ℕ)), (↑(rationalHeight (C i j)) : ℝ) ≤ H)
    (_ : ((1 : Matrix (Fin (0 : ℕ)) (Fin (0 : ℕ)) ℝ) - Q.map fun (q : ℚ) => (↑q :
      ℝ)).transpose * ((C.map fun (q : ℚ) => (↑q : ℝ)) - (C.map fun (q : ℚ) => (↑q :
      ℝ)).transpose) * ((1 : Matrix (Fin (0 : ℕ)) (Fin (0 : ℕ)) ℝ) - Q.map fun (q : ℚ)
      => (↑q : ℝ)) = (0 : Matrix (Fin (0 : ℕ)) (Fin (0 : ℕ)) ℝ))
    (_ : ∀ (A : MultivariableQuadraticChartData k (0 : ℕ)),
      MultivariableQuadraticChartComplexity c₀ H A → ∀ (w : Fin (0 : ℕ) → ℝ),
      ‖A.amplitude w‖ ≤ Real.exp ((↑c₀ : ℝ) * X ^ (6 : ℕ))),
  ∃ (ι : Type) (_ : Fintype ι) (σ : ι × (Fin ((0 : ℕ) + (0 : ℕ)) → ℤ) → Fin (0 : ℕ) →
    ℚ), (↑(Fintype.card ι) : ℝ) ≤ Real.exp ((↑D : ℝ) * X ^ D) ∧ (∀ (p : ι × (Fin ((0 :
    ℕ) + (0 : ℕ)) → ℤ)) (i : Fin (0 : ℕ)), (↑(rationalHeight (σ p i)) : ℝ) ≤ Real.exp
    ((↑D : ℝ) * X ^ D) * ((1 : ℝ) + frequencyLength p.2)) ∧ ∀ (A :
    MultivariableQuadraticChartData k (0 : ℕ)), A.matrix = C →
    MultivariableQuadraticChartComplexity c₀ H A → ‖realMatrixOperator ((Q.map fun (q
    : ℚ) => (↑q : ℝ)) * A.horizontal)‖ ≤ B → ∃ (a : ι × (Fin ((0 : ℕ) + (0 : ℕ)) → ℤ)
    → ℂ), (∀ (z : Fin k → ℝ), (∀ (i : Fin k), |z i| ≤ R) → HasSum (fun (p : ι × (Fin
    ((0 : ℕ) + (0 : ℕ)) → ℤ)) => a p * (↑((𝐞 : ℝ → Circle) ((fun (i : Fin (0 : ℕ)) =>
    (↑(σ p i) : ℝ)) ⬝ᵥ A.horizontal.mulVec z)) : ℂ)) ((↑((𝐞 : ℝ → Circle) (-(z ⬝ᵥ
    (effectiveReturnQuadratic (C.map fun (q : ℚ) => (↑q : ℝ)) A.quadratic A.horizontal
    (((1 : Matrix (Fin (0 : ℕ)) (Fin (0 : ℕ)) ℝ) - Q.map fun (q : ℚ) => (↑q : ℝ)) *
    A.horizontal) ((Q.map fun (q : ℚ) => (↑q : ℝ)) * A.horizontal)).mulVec z +
    A.linear ⬝ᵥ z))) : ℂ) * multivariableQuadraticChartAtom A z)) ∧ (Summable fun (p :
    ι × (Fin ((0 : ℕ) + (0 : ℕ)) → ℤ)) => ‖a p‖) ∧ ∑' (p : ι × (Fin ((0 : ℕ) + (0 :
    ℕ)) → ℤ)), ‖a p‖ ≤ Real.exp ((↑D : ℝ) * X ^ D) ∧ ∀ (J : ℕ), (∀ (p : ι × (Fin ((0 :
    ℕ) + (0 : ℕ)) → ℤ)), ‖a p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (J * ((0 : ℕ) + (1
    : ℕ)) ^ (2 : ℕ)) ≤ Real.exp ((↑((fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) J)
    : ℝ) * X ^ (fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) J)) ∧ ∀ (T : ℝ), (1 : ℝ)
    ≤ T → (∑ f : ι, ∑ v ∈ frequencyShell ((0 : ℕ) + (0 : ℕ)) T, ‖a (f, v)‖) * T ^ (J *
    ((0 : ℕ) + (1 : ℕ)) ^ (2 : ℕ)) ≤ Real.exp ((↑((fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊
    + (6 : ℕ)) J) : ℝ) * X ^ (fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) J)


open scoped Classical in
private def SplitFourierExpansionStage1Statement : Prop :=
  ∀ (c₀ : ℕ)
    (_ : (1 : ℕ) ≤ c₀)
    (k : ℕ)
    (R : ℝ)
    (_ : (0 : ℝ) ≤ R)
    (ψ : ℝ → ℝ)
    (Kψ : ℕ)
    (_ : (1 : ℕ) ≤ Kψ)
    (_ : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (_ : ∀ (x : ℝ), |ψ x| ≤ (1 : ℝ))
    (_ : ∀ (x : ℝ), |x| ≤ (1 : ℝ) → ψ x = (1 : ℝ))
    (_ : ∀ (x : ℝ), (2 : ℝ) ≤ |x| → ψ x = (0 : ℝ))
    (_ : ∀ (i : ℕ) (x : ℝ), |iteratedDeriv i ψ x| ≤ ((↑Kψ : ℝ) * ((↑i : ℝ) + (1 : ℝ))) ^ (Kψ
      * (i + (1 : ℕ))))
    (_ : (0 : ℝ) ≤ (↑k : ℝ) * R),
  let L₀ : ℝ :=
    Real.log ((5 : ℝ) * ((↑k : ℝ) * R + (1 : ℝ)) + (↑Kψ : ℝ) + (18 : ℝ))
  ∀ (_ : (0 : ℝ) ≤ L₀),
  let ccard : ℝ :=
    Real.log ((2 : ℝ) * (↑k : ℝ) * R + (7 : ℝ)) + (16 : ℝ)
  ∀ (_ : (0 : ℝ) ≤ ccard),
  let cht : ℝ :=
    Real.log ((20 : ℝ) * ((↑k : ℝ) * R + (1 : ℝ))) + Real.log ((2 : ℝ) * (↑k : ℝ) * R +
      (9 : ℝ)) + (56 : ℝ)
  ∀ (_ : (0 : ℝ) ≤ cht),
  let c3 : ℝ :=
    ((8 : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + ((4 : ℝ) * (↑Kψ : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + (18 :
      ℝ)) * (3 : ℝ)) * (L₀ + (4 : ℝ) + (3 : ℝ))
  ∀ (_ : (0 : ℝ) ≤ c3),
  let ctot : ℝ :=
    ccard + (2 : ℝ) + c3 + c3 + (7 : ℝ)
  ∀ (_ : ctot = ccard + (2 : ℝ) + c3 + c3 + (7 : ℝ)),
  let cJ : ℕ → ℝ :=
    fun (J : ℕ) => ccard + ((8 : ℝ) + (3 : ℝ) * (↑c₀ : ℝ) + ((4 : ℝ) * (↑Kψ : ℝ) + (3 :
      ℝ) * (↑c₀ : ℝ) + (18 : ℝ)) * ((4 : ℝ) * (↑J : ℝ) + (4 : ℝ))) * (L₀ + (4 : ℝ) + ((4
      : ℝ) * (↑J : ℝ) + (4 : ℝ))) + (8 : ℝ) * (↑J : ℝ) + (8 : ℝ)
  ∀ (d : ℕ)
    (H : ℝ)
    (B : ℝ)
    (_ : Real.exp (2 : ℝ) ≤ H)
    (_ : (↑d : ℝ) ≤ Real.log H)
    (_ : (2 : ℝ) ≤ B)
    (C : Matrix (Fin d) (Fin d) ℚ)
    (Q : Matrix (Fin d) (Fin d) ℚ)
    (_ : ∀ (i j : Fin d), (↑(rationalHeight (C i j)) : ℝ) ≤ H)
    (_ : Q.IsSymm)
    (_ : ∀ (i j : Fin d), (↑(rationalHeight (Q i j)) : ℝ) ≤ B)
    (_ : ((1 : Matrix (Fin d) (Fin d) ℝ) - Q.map fun (q : ℚ) => (↑q : ℝ)).transpose * ((C.map
      fun (q : ℚ) => (↑q : ℝ)) - (C.map fun (q : ℚ) => (↑q : ℝ)).transpose) * ((1 :
      Matrix (Fin d) (Fin d) ℝ) - Q.map fun (q : ℚ) => (↑q : ℝ)) = (0 : Matrix (Fin d)
      (Fin d) ℝ)),
  let X : ℝ :=
    (1 : ℝ) + Real.log H + Real.log B
  ∀ (_ : (3 : ℝ) ≤ (1 : ℝ) + Real.log H + Real.log B)
    (_ : (↑d : ℝ) ≤ (1 : ℝ) + Real.log H + Real.log B),
  let D : ℕ :=
    ⌈ccard + cht + ctot + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)
  ∀ (_ : ∀ c ≤ ccard + cht + ctot + (↑c₀ : ℝ), Real.exp (c * X ^ (6 : ℕ)) ≤ Real.exp ((↑D :
      ℝ) * X ^ D))
    (_ : ∀ (J : ℕ), ∀ c ≤ cJ J + (↑c₀ : ℝ), Real.exp (c * X ^ (6 : ℕ)) ≤ Real.exp ((↑(⌈cJ J +
      (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) : ℝ) * X ^ (⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ))))
    (_ : d > (0 : ℕ)),
  ∃ (ι : Type) (_ : Fintype ι) (σ : ι × (Fin (d + d) → ℤ) → Fin d → ℚ),
    (↑(Fintype.card ι) : ℝ) ≤ Real.exp ((↑D : ℝ) * X ^ D) ∧ (∀ (p : ι × (Fin (d + d) →
    ℤ)) (i : Fin d), (↑(rationalHeight (σ p i)) : ℝ) ≤ Real.exp ((↑D : ℝ) * X ^ D) *
    ((1 : ℝ) + frequencyLength p.2)) ∧ ∀ (A : MultivariableQuadraticChartData k d),
    A.matrix = C → MultivariableQuadraticChartComplexity c₀ H A → ‖realMatrixOperator
    ((Q.map fun (q : ℚ) => (↑q : ℝ)) * A.horizontal)‖ ≤ B → ∃ (a : ι × (Fin (d + d) →
    ℤ) → ℂ), (∀ (z : Fin k → ℝ), (∀ (i : Fin k), |z i| ≤ R) → HasSum (fun (p : ι ×
    (Fin (d + d) → ℤ)) => a p * (↑((𝐞 : ℝ → Circle) ((fun (i : Fin d) => (↑(σ p i) :
    ℝ)) ⬝ᵥ A.horizontal.mulVec z)) : ℂ)) ((↑((𝐞 : ℝ → Circle) (-(z ⬝ᵥ
    (effectiveReturnQuadratic (C.map fun (q : ℚ) => (↑q : ℝ)) A.quadratic A.horizontal
    (((1 : Matrix (Fin d) (Fin d) ℝ) - Q.map fun (q : ℚ) => (↑q : ℝ)) * A.horizontal)
    ((Q.map fun (q : ℚ) => (↑q : ℝ)) * A.horizontal)).mulVec z + A.linear ⬝ᵥ z))) : ℂ)
    * multivariableQuadraticChartAtom A z)) ∧ (Summable fun (p : ι × (Fin (d + d) →
    ℤ)) => ‖a p‖) ∧ ∑' (p : ι × (Fin (d + d) → ℤ)), ‖a p‖ ≤ Real.exp ((↑D : ℝ) * X ^
    D) ∧ ∀ (J : ℕ), (∀ (p : ι × (Fin (d + d) → ℤ)), ‖a p‖ * ((1 : ℝ) + frequencyLength
    p.2) ^ (J * (d + (1 : ℕ)) ^ (2 : ℕ)) ≤ Real.exp ((↑((fun (J : ℕ) => ⌈cJ J + (↑c₀ :
    ℝ)⌉₊ + (6 : ℕ)) J) : ℝ) * X ^ (fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) J)) ∧
    ∀ (T : ℝ), (1 : ℝ) ≤ T → (∑ f : ι, ∑ v ∈ frequencyShell (d + d) T, ‖a (f, v)‖) * T
    ^ (J * (d + (1 : ℕ)) ^ (2 : ℕ)) ≤ Real.exp ((↑((fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊
    + (6 : ℕ)) J) : ℝ) * X ^ (fun (J : ℕ) => ⌈cJ J + (↑c₀ : ℝ)⌉₊ + (6 : ℕ)) J)




private theorem splitFourierExpansion_conclusion_8 : SplitFourierExpansionConclusion8Statement := by
  classical
  intro c₀ hc k R Kψ hK L₀ hL₀ ccard hccard0 cht hcht0 c3 hc30 ctot hctot cJ hcJ H B X hlB hlH D
    hDc hDJc C Q hC hiso hHc
  -- dimension zero: a single term
  refine ⟨Unit, inferInstance, fun _ i => Fin.elim0 i, ?_, fun p i => Fin.elim0 i, ?_⟩
  · simp only [Fintype.card_unit, Nat.cast_one]
    exact Real.one_le_exp (by positivity)
  intro A hAC hA hQV
  subst hAC
  have hc0D : (c₀ : ℝ) ≤ ccard + cht + ctot + c₀ := by
    have : 0 ≤ ctot := by rw [hctot]; positivity
    linarith
  have hc0J (J : ℕ) : (c₀ : ℝ) ≤ cJ J + c₀ := by
    have : 0 ≤ cJ J := by simp only [hcJ]; positivity
    linarith
  have hlen (v : Fin (0 + 0) → ℤ) : frequencyLength v = 0 := by
    simp [frequencyLength]
  have hE0 : IsEmpty (Fin (0 + 0)) := ⟨fun i => Fin.elim0 i⟩
  let hU : Unique (Fin (0 + 0) → ℤ) := Pi.uniqueOfIsEmpty _
  let : Unique (Unit × (Fin (0 + 0) → ℤ)) :=
    { default := ((), default), uniq := fun p => Prod.ext (Subsingleton.elim _ _)
        (Subsingleton.elim _ _) }
  let : Fintype (Unit × (Fin (0 + 0) → ℤ)) := Fintype.ofFinite _
  refine ⟨fun _ => A.amplitude 0, fun z _ => ?_, Summable.of_finite, ?_, fun J => ⟨?_, ?_⟩⟩
  · have h := hasSum_fintype (fun p : Unit × (Fin (0 + 0) → ℤ) => A.amplitude 0 *
      (Real.fourierChar (dotProduct (fun i => ((Fin.elim0 i : ℚ) : ℝ))
        (A.horizontal.mulVec z)) : ℂ))
    rw [Fintype.sum_unique] at h
    have hdot : dotProduct (fun i => ((Fin.elim0 i : ℚ) : ℝ)) (A.horizontal.mulVec z) = 0 := by
      simp [dotProduct]
    simp only [hdot, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at h ⊢
    rw [chart_split_fourier_dim_zero A Q z]
    exact h
  · rw [tsum_fintype, Fintype.sum_unique]
    exact (hHc A hA 0).trans (hDc _ hc0D)
  · intro p
    have h1 : (1 + frequencyLength p.2) ^ (J * (0 + 1) ^ 2) = 1 := by rw [hlen]; simp
    rw [h1, mul_one]
    exact (hHc A hA 0).trans (hDJc J _ (hc0J J))
  · intro T hT
    have hempty : frequencyShell (0 + 0) T = ∅ := by
      ext v
      simp only [mem_frequencyShell, Finset.notMem_empty, iff_false, not_and]
      intro hv
      exact absurd (Subsingleton.elim v 0) hv
    simp only [hempty, Finset.sum_empty, Finset.sum_const_zero, zero_mul]
    exact (Real.exp_pos _).le
-- dimension at least one



private theorem splitFourierExpansion_stage_1 : SplitFourierExpansionStage1Statement := by
  classical
  intro c₀ hc k R hR ψ Kψ hK hψ hψ1 hψe hψ0 hder hkR L₀ hL₀ ccard hccard0 cht hcht0 c3 hc30 ctot
    hctot cJ d H B hH hd hB C Q hC hQs hQB hiso X hX3 hdX D hDc hDJc hdpos
  have hH0 : 0 ≤ H := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hB0 : 0 ≤ B := by linarith
  have habs (q : ℚ) {M : ℝ} (hq : (rationalHeight q : ℝ) ≤ M) : |(q : ℝ)| ≤ M := by
    have h := rational_abs_le_height q
    have h' : |(q : ℝ)| ≤ (rationalHeight q : ℝ) := by exact_mod_cast h
    exact h'.trans hq
  obtain ⟨P, ZP, hP, hPH, hZP⟩ := chart_matrix_clear_denominators hH0 C hC
  have hPC : ∀ i j, ∃ z : ℤ, (P : ℚ) * C i j = z := fun i j =>
    ⟨ZP i j, by have h := hZP i j; exact_mod_cast h.symm⟩
  obtain ⟨q₀, ZQ, hq, hqB, hZQ⟩ := chart_matrix_clear_denominators hB0 Q hQB
  have hqQ : ∀ i j, ∃ z : ℤ, (q₀ : ℚ) * Q i j = z := fun i j =>
    ⟨ZQ i j, by have h := hZQ i j; exact_mod_cast h.symm⟩
  set! S := B * (k * R + 1) with hSdef
  have hS2 : 2 ≤ S := by rw [hSdef]; nlinarith only [hkR, hB]
  set! P₁ := ⌈4 * S⌉₊ with hP₁def
  have hP₁ : 4 * S ≤ P₁ := Nat.le_ceil _
  have hP₁' : (P₁ : ℝ) ≤ 4 * S + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hP₁1 : (1 : ℝ) ≤ P₁ := by linarith
  set! K := ⌈(q₀ : ℝ) * (S + d * B * H)⌉₊ with hKdef
  have hKb : (q₀ : ℝ) * (S + d * B * H) ≤ K := Nat.le_ceil _
  have hK' : (K : ℝ) ≤ q₀ * (S + d * B * H) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  obtain ⟨hcard, hheight⟩ := chartBudget_card_height (k := k) hH hd hB hR (P := P) (q₀ := q₀)
    (P₁ := P₁) (K := K) hPH hqB hP₁' hK'
  have hQBr : ∀ i j, |(Q i j : ℝ)| ≤ B := fun i j => habs _ (hQB i j)
  have hCH : ∀ i j, |(C i j : ℝ)| ≤ H := fun i j => habs _ (hC i j)
  have hskH : ∀ i j, |realSkewPart (C.map fun q => (q : ℝ)) i j| ≤ H := fun i j => by
    simp only [realSkewPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply,
      smul_eq_mul, Matrix.map_apply]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_sub (C i j : ℝ) (C j i)
    linarith [hCH i j, hCH j i]
  have hctot0 : 0 ≤ ctot := by rw [hctot]; positivity
  refine ⟨slowValueBox d K, inferInstance,
    fun p => chartSplitFrequencyQ Q C q₀ (2 * P) P₁ p.1 p.2, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe]
    exact hcard.trans (hDc _ (by linarith))
  · intro p i
    have hν : ∀ a, |((p.1 : Fin d → ℤ) a : ℝ)| ≤ K := fun a => by
      have := (mem_slowValueBox.mp p.1.2) a
      exact_mod_cast this
    have hP1pos : 0 < P₁ := by exact_mod_cast (lt_of_lt_of_le one_pos hP₁1)
    have h := chartSplitFrequencyQ_height (P₀ := 2 * P) Q C hB0 hQBr hskH hq hP (by omega)
      hP1pos hqQ hPC p.1 hν p.2 i
    have hL := frequencyLength_nonneg p.2
    set a := (d : ℝ) * (1 + B) * (d * H * K) + d * B + 1
    have ha : 0 ≤ a := by positivity
    have hDen0 : (0 : ℝ) ≤ ((2 * P * q₀ ^ 2 * (q₀ * P₁) * (2 * P) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (rationalHeight (chartSplitFrequencyQ Q C q₀ (2 * P) P₁ p.1 p.2 i) : ℝ) ≤
          ((2 * P * q₀ ^ 2 * (q₀ * P₁) * (2 * P) : ℕ) : ℝ) * (a * (1 + frequencyLength p.2) + 1) :=
          h
      _ ≤ ((2 * P * q₀ ^ 2 * (q₀ * P₁) * (2 * P) : ℕ) : ℝ) *
            ((a + 1) * (1 + frequencyLength p.2)) := by
          apply mul_le_mul_of_nonneg_left _ hDen0
          have e : (a + 1) * (1 + frequencyLength p.2) =
              a * (1 + frequencyLength p.2) + 1 + frequencyLength p.2 := by ring
          linarith
      _ = (((2 * P * q₀ ^ 2 * (q₀ * P₁) * (2 * P) : ℕ) : ℝ) *
            ((d : ℝ) * (1 + B) * (d * H * K) + d * B + 2)) * (1 + frequencyLength p.2) := by
          simp only [a]; ring
      _ ≤ Real.exp (cht * X ^ 6) * (1 + frequencyLength p.2) :=
          mul_le_mul_of_nonneg_right hheight (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hDc _ (by linarith)) (by linarith)
  · intro A hAC hA hQV
    subst hAC
    obtain ⟨a, hsum, hsumm, htot, hpt, hshell⟩ := chart_split_fourier_explicit hdpos hA hc hψ hψ1
      hψe hψ0 hK hder Q hQs hiso hq hqQ hB0 hQBr hCH hP hPC (by linarith : (0 : ℝ) < S) hP₁ hKb
    set E := fun m => chartUnitEnvelope d c₀ Kψ m H S (1 / (3 * q₀)) B H (2 * P : ℕ) P₁ with hEdef
    have hE0 : ∀ m, 0 ≤ E m := fun m => chartUnitEnvelope_nonneg hH0 (by linarith)
      (by positivity) hB0 (Nat.cast_nonneg _) (by linarith)
    have hE : ∀ m, E m ≤ Real.exp ((8 * d + 3 * c₀ + (4 * Kψ + 3 * c₀ + 18) * m : ℕ) *
        (L₀ + 4 * X ^ 3 + Real.log (m + 1))) := fun m =>
      chartBudget_env (c₀ := c₀) (Kψ := Kψ) (k := k) hH hd hB hR hq hPH hqB hP₁1 hP₁' m
    have hcard' : (((slowValueBox d K).card : ℕ) : ℝ) ≤ Real.exp (ccard * X ^ 6) := hcard
    have hcJ' (J : ℕ) : ccard + (8 + 3 * (c₀ : ℝ) + (4 * Kψ + 3 * c₀ + 18) * (4 * J + 4)) *
        (L₀ + 4 + (4 * J + 4)) + 8 * J + 8 ≤ cJ J + c₀ := by
      have : cJ J = ccard + (8 + 3 * (c₀ : ℝ) + (4 * Kψ + 3 * c₀ + 18) * (4 * J + 4)) *
          (L₀ + 4 + (4 * J + 4)) + 8 * J + 8 := rfl
      rw [this]; linarith [Nat.cast_nonneg (α := ℝ) c₀]
    refine ⟨a, fun z hz => ?_, hsumm, ?_, fun J => ⟨?_, ?_⟩⟩
    · apply hsum z
      intro i
      have h1 := mulVec_coord_le_opNorm (Q.map (fun q => (q : ℝ)) * A.horizontal) z hz i
      rw [← Matrix.mulVec_mulVec] at h1
      calc |(Q.map (fun q => (q : ℝ))).mulVec (A.horizontal.mulVec z) i| ≤
            ‖realMatrixOperator (Q.map (fun q => (q : ℝ)) * A.horizontal)‖ * (k * R) := h1
        _ ≤ B * (k * R) := mul_le_mul_of_nonneg_right hQV hkR
        _ ≤ S := by
            rw [hSdef]; exact mul_le_mul_of_nonneg_left (by linarith) hB0
    · refine htot.trans ((chartBudget_total hX3 hdX hL₀ E hE0 hE hcard').trans ?_)
      exact hDc _ (by rw [hctot]; linarith)
    · intro p
      exact (hpt J p).trans (((chartBudget_J hX3 hdX hL₀ E hE0 hE hcard' hccard0 J).1).trans
        (hDJc J _ (hcJ' J)))
    · intro T hT
      exact (hshell J T hT).trans (((chartBudget_J hX3 hdX hL₀ E hE0 hE hcard' hccard0 J).2).trans
        (hDJc J _ (hcJ' J)))


/-- A fixed polynomial exponential is bounded by a larger integer budget. -/
theorem exp_le_ceil_power_budget {x a b : ℝ} (p : ℕ) (hx : 1 ≤ x) (hab : a ≤ b) :
    Real.exp (a * x ^ p) ≤ Real.exp (((⌈b⌉₊ + p : ℕ) : ℝ) * x ^ (⌈b⌉₊ + p)) := by
  apply Real.exp_le_exp.mpr
  by_cases ha : a ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg ha (by positivity)).trans (by positivity)
  · have ha' : 0 ≤ a := (lt_of_not_ge ha).le
    have hb : a ≤ ((⌈b⌉₊ + p : ℕ) : ℝ) := by
      have := Nat.le_ceil b
      push_cast
      linarith only [hab, this, Nat.cast_nonneg (α := ℝ) p]
    exact mul_le_mul hb (pow_le_pow_right₀ hx (by omega)) (by positivity) (by positivity)

/-- A logarithmic bound controls every fixed power by an exponential budget. -/
theorem power_le_exp_budget {H x : ℝ} (c p : ℕ) (hH : 0 < H) (hx : 1 ≤ x)
    (hp : 1 ≤ p) (hlog : Real.log H ≤ x) :
    H ^ c ≤ Real.exp ((c : ℝ) * x ^ p) := by
  rw [← Real.exp_log hH, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg c)
  exact hlog.trans (le_self_pow₀ hx (by omega))

/-- **Blueprint lem:chartfourier (Fourier expansion with uniform envelopes),
lines 1338–1377.** Let `Q` be a chart of complexity `H` (fixed Gevrey order
`c₀`) with matrix `C`, and let a rational symmetric splitting matrix `Q_s` of
height at most `B` have fast part `P_f = 1 - Q_s` isotropic for `C - Cᵀ` and
bounded slow velocity `‖P_s V‖ ≤ B`. Then on the fixed box `[-R,R]^k`
`Q(z) = e(zᵀΛ_* z + bᵀz) Σ_ℓ a_ℓ e(σ_ℓᵀ V z)` exactly and absolutely, with
`Λ_*` the effective quadratic form of eq:effective. The families `ι` are at most
`exp(D X^D)` in number, each indexed by `2d` integers; the rational frequencies
`σ` (chosen before the amplitude and the slow velocity) have height at most
`exp(D X^D)(1+|ℓ|)`; `Σ|a_ℓ| ≤ exp(D X^D)`; and for every `J` the pooled envelope
satisfies `|a_ℓ|(1+|ℓ|)^{J(d+1)²} ≤ exp(D_J X^{D_J})`, while the absolute mass in
each dyadic shell `T ≤ 1+|ℓ| < 2T` is at most `exp(D_J X^{D_J}) T^{-J(d+1)²}`.
Here `X = 1 + log H + log B`, so all bounds are quasipolynomial in `H, B`. -/
theorem splitFourierExpansion (c₀ : ℕ) (hc : 1 ≤ c₀) (k : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ DJ : ℕ → ℕ, ∀ {d : ℕ} (H B : ℝ), Real.exp 2 ≤ H →
      (d : ℝ) ≤ Real.log H → 2 ≤ B →
      ∀ (C Q : Matrix (Fin d) (Fin d) ℚ), (∀ i j, (rationalHeight (C i j) : ℝ) ≤ H) →
      Q.IsSymm → (∀ i j, (rationalHeight (Q i j) : ℝ) ≤ B) →
      (1 - Q.map (fun q => (q : ℝ))).transpose * (C.map (fun q => (q : ℝ)) -
        (C.map (fun q => (q : ℝ))).transpose) * (1 - Q.map (fun q => (q : ℝ))) = 0 →
      let X := 1 + Real.log H + Real.log B
      ∃ (ι : Type) (_ : Fintype ι) (σ : ι × (Fin (d + d) → ℤ) → Fin d → ℚ),
        (Fintype.card ι : ℝ) ≤ Real.exp (D * X ^ D) ∧
        (∀ p i, (rationalHeight (σ p i) : ℝ) ≤
          Real.exp (D * X ^ D) * (1 + frequencyLength p.2)) ∧
        ∀ A : MultivariableQuadraticChartData k d, A.matrix = C →
          MultivariableQuadraticChartComplexity c₀ H A →
          ‖realMatrixOperator (Q.map (fun q => (q : ℝ)) * A.horizontal)‖ ≤ B →
          ∃ a : ι × (Fin (d + d) → ℤ) → ℂ,
            (∀ z : Fin k → ℝ, (∀ i, |z i| ≤ R) →
              HasSum (fun p => a p * (Real.fourierChar (dotProduct (fun i => (σ p i : ℝ))
                  (A.horizontal.mulVec z)) : ℂ))
                ((Real.fourierChar (-(dotProduct z ((effectiveReturnQuadratic
                    (C.map (fun q => (q : ℝ))) A.quadratic A.horizontal
                    ((1 - Q.map (fun q => (q : ℝ))) * A.horizontal)
                    (Q.map (fun q => (q : ℝ)) * A.horizontal)).mulVec z) +
                    dotProduct A.linear z)) : ℂ) * multivariableQuadraticChartAtom A z)) ∧
            Summable (fun p => ‖a p‖) ∧ (∑' p, ‖a p‖) ≤ Real.exp (D * X ^ D) ∧
            ∀ J : ℕ,
              (∀ p, ‖a p‖ * (1 + frequencyLength p.2) ^ (J * (d + 1) ^ 2) ≤
                Real.exp (DJ J * X ^ DJ J)) ∧
              ∀ T : ℝ, 1 ≤ T →
                (∑ f : ι, ∑ v ∈ frequencyShell (d + d) T, ‖a (f, v)‖) *
                    T ^ (J * (d + 1) ^ 2) ≤ Real.exp (DJ J * X ^ DJ J) := by
  obtain ⟨ψ, Kψ, hK, hψ, hψ1, hψe, hψ0, hder⟩ := exists_plateau_cutoff
  have hkR : 0 ≤ (k : ℝ) * R := mul_nonneg (Nat.cast_nonneg k) hR
  have hKψ0 : (0 : ℝ) ≤ Kψ := Nat.cast_nonneg Kψ
  set L₀ := Real.log (5 * (k * R + 1) + Kψ + 18) with hL₀def
  have hL₀ : 0 ≤ L₀ := Real.log_nonneg (by linarith)
  set ccard := Real.log (2 * k * R + 7) + 16 with hccard
  have hccard0 : 0 ≤ ccard := by
    have : 0 ≤ Real.log (2 * k * R + 7) := Real.log_nonneg (by linarith)
    linarith
  set cht := Real.log (20 * (k * R + 1)) + Real.log (2 * k * R + 9) + 56 with hcht
  have hcht0 : 0 ≤ cht := by
    have h1 : 0 ≤ Real.log (20 * (k * R + 1)) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (2 * k * R + 9) := Real.log_nonneg (by linarith)
    linarith
  set c3 := (8 + 3 * (c₀ : ℝ) + (4 * Kψ + 3 * c₀ + 18) * 3) * (L₀ + 4 + 3) with hc3
  have hc30 : 0 ≤ c3 := by positivity
  set! ctot := ccard + 2 + c3 + c3 + 7 with hctot
  set! cJ := fun J : ℕ => ccard + (8 + 3 * (c₀ : ℝ) + (4 * Kψ + 3 * c₀ + 18) * (4 * J + 4)) *
    (L₀ + 4 + (4 * J + 4)) + 8 * J + 8 with hcJ
  refine ⟨⌈ccard + cht + ctot + c₀⌉₊ + 6, by omega,
    fun J => ⌈cJ J + c₀⌉₊ + 6, ?_⟩
  intro d H B hH hd hB C Q hC hQs hQB hiso X
  obtain ⟨hX3, hHX, hBX, hdX, hlB, hlH, hd2⟩ := chartBudget_basic hH hd hB
  have hX1 : 1 ≤ X := by linarith
  set D := ⌈ccard + cht + ctot + c₀⌉₊ + 6 with hD
  have hDc (c : ℝ) (hc : c ≤ ccard + cht + ctot + c₀) :
      Real.exp (c * X ^ 6) ≤ Real.exp (D * X ^ D) :=
    exp_le_ceil_power_budget 6 hX1 hc
  have hDJc (J : ℕ) (c : ℝ) (hc : c ≤ cJ J + c₀) :
      Real.exp (c * X ^ 6) ≤
        Real.exp ((⌈cJ J + c₀⌉₊ + 6 : ℕ) * X ^ (⌈cJ J + c₀⌉₊ + 6)) :=
    exp_le_ceil_power_budget 6 hX1 hc
  have hHc (A : MultivariableQuadraticChartData k d)
      (hA : MultivariableQuadraticChartComplexity c₀ H A)
      (w : Fin d → ℝ) : ‖A.amplitude w‖ ≤ Real.exp ((c₀ : ℝ) * X ^ 6) := by
    have h1 := quadraticChartComplexity_amplitude_bound
      (multivariableChartAlongLine_complexity hA 0) w
    change ‖A.amplitude w‖ ≤ H ^ c₀ at h1
    refine h1.trans ?_
    have hH0 : 0 < H := lt_of_lt_of_le (Real.exp_pos 2) hH
    exact power_le_exp_budget c₀ 6 hH0 hX1 (by norm_num) hHX
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · expose_names
    exact @splitFourierExpansion_conclusion_8 c₀ hc k R Kψ hK hL₀ hccard0 hcht0 hc30 hctot hcJ H B
      hlB hlH hDc hDJc C Q hC hiso hHc
  expose_names
  exact @splitFourierExpansion_stage_1 c₀ hc k R hR ψ Kψ hK hψ hψ1 hψe hψ0 hder hkR hL₀ hccard0
    hcht0 hc30 hctot d H B hH hd hB C Q hC hQs hQB hiso hX3 hdX hDc hDJc hdpos

/-- Blueprint lem:chartfourier, line 1347: shell bounds with one power of decay
give a pooled tail bound, so a uniform tail `ε` requires truncation only at
frequency `2^K ≥ 2E/ε`. -/
theorem pooled_shell_tail_bound {ι : Type*} [Fintype ι] {n : ℕ}
    (a : ι × (Fin n → ℤ) → ℂ) {E : ℝ}
    (hshell : ∀ T : ℝ, 1 ≤ T → (∑ f : ι, ∑ v ∈ frequencyShell n T, ‖a (f, v)‖) * T ≤ E)
    (K : ℕ) :
    Summable (fun p : ι × (Fin n → ℤ) =>
        ‖if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0‖) ∧
      (∑' p : ι × (Fin n → ℤ),
        ‖if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0‖) ≤
        2 * E / 2 ^ K := by
  classical
  set c : ι × (Fin n → ℤ) → ℂ := fun p =>
    if p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 then a p else 0
  let s : ℕ → Finset (ι × (Fin n → ℤ)) := fun k =>
    Finset.univ ×ˢ frequencyShell n ((2 : ℝ) ^ (K + k))
  have hcover : ∀ p, c p ≠ 0 → ∃ k, p ∈ s k := by
    intro p hp
    have hcond : p.2 ≠ 0 ∧ (2 : ℝ) ^ K ≤ 1 + frequencyLength p.2 := by
      by_contra h; exact hp (by simp [c, h])
    obtain ⟨k, hk⟩ := exists_mem_late_frequencyShell hcond.1 K hcond.2
    exact ⟨k, Finset.mem_product.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hmass (k : ℕ) : ∑ p ∈ s k, ‖c p‖ ≤ E / 2 ^ K * (1 / 2) ^ k := by
    have hT : (1 : ℝ) ≤ 2 ^ (K + k) := one_le_pow₀ (by norm_num)
    have h1 : ∑ p ∈ s k, ‖c p‖ ≤ ∑ f : ι, ∑ v ∈ frequencyShell n ((2 : ℝ) ^ (K + k)),
        ‖a (f, v)‖ := by
      rw [Finset.sum_product]
      apply Finset.sum_le_sum; intro f _
      apply Finset.sum_le_sum; intro v _
      simp only [c]
      split_ifs <;> simp
    have h2 := hshell _ hT
    have hpos : (0 : ℝ) < 2 ^ (K + k) := by positivity
    calc ∑ p ∈ s k, ‖c p‖ ≤ E / 2 ^ (K + k) := by
          rw [le_div_iff₀ hpos]; exact (mul_le_mul_of_nonneg_right h1 hpos.le).trans h2
      _ = E / 2 ^ K * (1 / 2) ^ k := by
          rw [pow_add, one_div_pow]; field_simp
  have hgeom : Summable (fun k : ℕ => E / 2 ^ K * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_two).mul_left _
  have hm0 (k : ℕ) : 0 ≤ ∑ p ∈ s k, ‖c p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsumm : Summable (fun k => ∑ p ∈ s k, ‖c p‖) :=
    Summable.of_nonneg_of_le hm0 hmass hgeom
  obtain ⟨hs, ht⟩ := tsum_norm_le_shell_masses c s hcover hsumm
  refine ⟨hs, ht.trans ?_⟩
  calc ∑' k, ∑ p ∈ s k, ‖c p‖ ≤ ∑' k : ℕ, E / 2 ^ K * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_le_tsum hmass hsumm hgeom
    _ = 2 * E / 2 ^ K := by
        rw [tsum_mul_left, tsum_geometric_two]; ring

/-! ### Progression separation (lem:separation) -/

/-- The tensor Gevrey lattice partition used for the slot lifts. -/
noncomputable def sepPartition {d : ℕ} (w : Fin d → ℝ) : ℂ :=
  chartCoordinateProduct gevreyPartition w

theorem sepPartition_tsum {d : ℕ} (z : Fin d → ℝ) :
    (∑' k : Fin d → ℤ, sepPartition (z - fun l => (k l : ℝ))) = 1 :=
  chartCoordinateProduct_periodization gevreyPartition gevreyPartition_hasCompactSupport
    gevreyPartition_tsum z

theorem sepPartition_ne_zero {d : ℕ} {w : Fin d → ℝ} (hw : sepPartition w ≠ 0) (l : Fin d) :
    |w l| ≤ 3 / 4 := by
  have h : gevreyPartition (w l) ≠ 0 := by
    intro h0
    apply hw
    unfold sepPartition chartCoordinateProduct
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp [h0])
  have := gevreyPartition_tsupport_subset (subset_tsupport _ h)
  exact abs_le.mpr ⟨this.1, this.2⟩

/-- The coupled amplitude of lem:separation, lines 1403–1407: the original cutoff
at `w_a + (i-a)w - k_i`, the equality cutoff imposing `d_b = d_a + (b-a)d + k_b`,
and the three lattice partitions. -/
noncomputable def sepCoupledAmplitude {d : ℕ} (χ : (Fin d → ℝ) → ℂ) (ψ : ℝ → ℝ)
    (i a b : ℤ) (ki kb : Fin d → ℤ) (wa wb w : Fin d → ℝ) : ℂ :=
  χ (wa + ((i - a : ℤ) : ℝ) • w - fun l => (ki l : ℝ)) *
    tensorCutoff ψ (1 / 3) (wa - wb + ((b - a : ℤ) : ℝ) • w - fun l => (kb l : ℝ)) *
    sepPartition wa * sepPartition wb * sepPartition w

theorem tensorCutoff_int {d : ℕ} {ψ : ℝ → ℝ} (hψ1 : ∀ x, |x| ≤ 1 → ψ x = 1)
    (hψ0 : ∀ x, 2 ≤ |x| → ψ x = 0) (v : Fin d → ℤ) :
    tensorCutoff ψ (1 / 3) (fun l => (v l : ℝ)) = if v = 0 then 1 else 0 := by
  split_ifs with h
  · subst h
    exact tensorCutoff_eq_one hψ1 (by norm_num) (fun l => by simp)
  · obtain ⟨l, hl⟩ : ∃ l, v l ≠ 0 := by
      by_contra hc; push Not at hc; exact h (funext hc)
    apply tensorCutoff_eq_zero hψ0 (by norm_num) l
    have : (1 : ℝ) ≤ |(v l : ℝ)| := by exact_mod_cast Int.one_le_abs hl
    linarith



end TrilinearHT.Auto
end
