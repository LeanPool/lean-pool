/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.DatumPiece
public import LeanPool.EllipticPDE.Regularity.LocalWeakFormWkInfty


/-!
# Datum of the induction step

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 step 3 produces an equation
for the cut-off derivative whose datum is a fixed list of shapes. Each is the middle cutoff of
the tower, or one of its first two partial derivatives, against a coefficient of the operator or
one of its derivatives, against a derivative of the solution of order at most two.

This file builds that datum as a single `L²(Ω)` class, with its order-`k` family, its bound and
its pairing. Nothing here knows how the list arose: the expansion of the bilinear form and the
differentiated equation both live in `EllipticPdes.Regularity.HigherInterior`, and what they
need of the datum is exactly the three conclusions below.

The constant is quantified before the solution, the datum and the direction of differentiation.
The shapes that differentiate a coefficient in the direction the equation is differentiated
depend on that direction, so their constants are collected over it.

## Main declarations

* `exists_cutoffDatum`: the datum, its family, its bound and its pairing.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- Pairing of the twelve pieces in the differentiated, cut-off datum. -/
def cutoffDatumPairing (Op : FullEllipticOp (n + 1)) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {N : Set (EuclideanSpace ℝ (Fin (n + 1)))} (ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (ℓ : Fin (n + 1)) (uN Df : L2D N) (HuN : HasIteratedWeakDerivOn N (k + 2) uN)
    (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : ℝ :=
  (∫ x in N, ξ x * ((1 : ℝ) * (Df x : ℝ)) * v x)
- (∑ i, ∫ x in N, ξ x * ((hbc.bReg i).D [ℓ] x * (HuN.D [i] x : ℝ)) * v x)
- (∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [ℓ, i] x : ℝ)) * v x)
- (∫ x in N, ξ x * (hbc.cReg.D [ℓ] x * (uN x : ℝ)) * v x)
+ (∑ i, ∑ j, ∫ x in N,
    ξ x * (hA.D [j, ℓ] i j x * (HuN.D [i] x : ℝ)) * v x)
+ (∑ i, ∑ j, ∫ x in N,
    ξ x * (hA.D [ℓ] i j x * (HuN.D [j, i] x : ℝ)) * v x)
- (∑ i, ∑ j, ∫ x in N,
    partialD j ξ x * (Op.a x i j * (HuN.D [i, ℓ] x : ℝ)) * v x)
- (∑ i, ∑ j, ∫ x in N,
    partialD j (partialD i ξ) x * (Op.a x i j * (HuN.D [ℓ] x : ℝ)) * v x)
- (∑ i, ∑ j, ∫ x in N,
    partialD i ξ x * (hA.D [j] i j x * (HuN.D [ℓ] x : ℝ)) * v x)
- (∑ i, ∑ j, ∫ x in N,
    partialD i ξ x * (Op.a x i j * (HuN.D [j, ℓ] x : ℝ)) * v x)
+ (∑ i, ∫ x in N, partialD i ξ x * (Op.b x i * (HuN.D [ℓ] x : ℝ)) * v x)
+ ∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [i, ℓ] x : ℝ)) * v x

/-- **Datum of the induction step.** For a cutoff `ξ` supported in the collar `N ⊆ Ω`, there
is a constant such that every family of derivatives of the solution on `N` bounded by `B`, and
every derivative of the datum bounded by `B`, produce an `L²(Ω)` class with `k` weak derivatives
bounded by `K·B` and pairing against a test function as the twelve shapes.

The two shapes with the zeroth-order coefficient against the differentiated solution cancel
between the differentiated equation and the zeroth-order block, and are absent. The two with the
transport coefficient do not, because the equation names one order of differentiation and the
block the other, and only the symmetry of the mixed second derivatives identifies them. -/
theorem exists_cutoffDatum (Op : FullEllipticOp (n + 1))
    {Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ : IsTestFn N ξ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : Fin (n + 1)) (uN Df : L2D N)
      (HuN : HasIteratedWeakDerivOn N (k + 2) uN)
      (HDf : HasIteratedWeakDerivOn N k Df) (B : ℝ),
      IteratedL2Bound HuN B → IteratedL2Bound HDf B →
      ∃ (F : L2D Ω) (HF : HasIteratedWeakDerivOn Ω k F),
        IteratedL2Bound HF (K * B) ∧
        ∀ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
          HasCompactSupport v →
          (∫ x in Ω, (F x : ℝ) * v x)
            = cutoffDatumPairing Op hA hbc ξ ℓ uN Df HuN v := by
  classical
  -- The coefficients, each read off its bundle at order `k`.
  have haE : ∀ i j : Fin (n + 1), IsWkInfty (fun x => Op.a x i j) k :=
    fun i j => (hA.entry i j).mono (by omega)
  have haD : ∀ i j m : Fin (n + 1), IsWkInfty ((hA.entry i j).D [m]) k :=
    fun i j m => ((hA.entry i j).deriv m).mono (by omega)
  have haDD : ∀ i j m r : Fin (n + 1), IsWkInfty (((hA.entry i j).deriv m).D [r]) k :=
    fun i j m r => (((hA.entry i j).deriv m).deriv r).mono (by omega)
  have hbE : ∀ i : Fin (n + 1), IsWkInfty (fun x => Op.b x i) k :=
    fun i => (hbc.bReg i).mono (by omega)
  have hbD : ∀ i m : Fin (n + 1), IsWkInfty ((hbc.bReg i).D [m]) k :=
    fun i m => ((hbc.bReg i).deriv m).mono (by omega)
  have hcD : ∀ m : Fin (n + 1), IsWkInfty (hbc.cReg.D [m]) k :=
    fun m => (hbc.cReg.deriv m).mono (by omega)
  have hξD : ∀ i : Fin (n + 1), IsTestFn N (partialD i ξ) := fun i => isTestFn_partialD hξ i
  have hξDD : ∀ i j : Fin (n + 1), IsTestFn N (partialD j (partialD i ξ)) :=
    fun i j => isTestFn_partialD (hξD i) j
  -- The shapes whose coefficient does not depend on the direction of differentiation.
  obtain ⟨K1, hK1, hP1⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Unit)
    (χ := fun _ => ξ) (fun _ => hξ)
    (a := fun _ => fun _ => (1 : ℝ)) (fun _ => IsWkInfty.const 1 k)
  obtain ⟨K3, hK3, hP3⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Fin (n + 1))
    (χ := fun _ => ξ) (fun _ => hξ) (a := fun i => fun x => Op.b x i) hbE
  obtain ⟨K7, hK7, hP7⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.2 ξ) (fun t => hξD t.2)
    (a := fun t => fun x => Op.a x t.1 t.2) (fun t => haE t.1 t.2)
  obtain ⟨K8, hK8, hP8⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.2 (partialD t.1 ξ)) (fun t => hξDD t.1 t.2)
    (a := fun t => fun x => Op.a x t.1 t.2) (fun t => haE t.1 t.2)
  obtain ⟨K9, hK9, hP9⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.1 ξ) (fun t => hξD t.1)
    (a := fun t => hA.D [t.2] t.1 t.2) (fun t => haD t.1 t.2 t.2)
  obtain ⟨K10, hK10, hP10⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k
    (ι := Fin (n + 1) × Fin (n + 1))
    (χ := fun t => partialD t.1 ξ) (fun t => hξD t.1)
    (a := fun t => fun x => Op.a x t.1 t.2) (fun t => haE t.1 t.2)
  obtain ⟨K11, hK11, hP11⟩ := exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Fin (n + 1))
    (χ := fun i => partialD i ξ) hξD (a := fun i => fun x => Op.b x i) hbE
  -- The shapes that differentiate a coefficient in the direction the equation is
  -- differentiated, collected over that direction.
  choose K2 hK2 hP2 using fun m : Fin (n + 1) =>
    exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Fin (n + 1))
      (χ := fun _ => ξ) (fun _ => hξ)
      (a := fun i => (hbc.bReg i).D [m]) (fun i => hbD i m)
  choose K4 hK4 hP4 using fun m : Fin (n + 1) =>
    exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Unit)
      (χ := fun _ => ξ) (fun _ => hξ)
      (a := fun _ => hbc.cReg.D [m]) (fun _ => hcD m)
  choose K5 hK5 hP5 using fun m : Fin (n + 1) =>
    exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Fin (n + 1) × Fin (n + 1))
      (χ := fun _ => ξ) (fun _ => hξ)
      (a := fun t => hA.D [t.2, m] t.1 t.2) (fun t => haDD t.1 t.2 m t.2)
  choose K6 hK6 hP6 using fun m : Fin (n + 1) =>
    exists_datum_of_pieces (Ω := Ω) hNm hNΩ k (ι := Fin (n + 1) × Fin (n + 1))
      (χ := fun _ => ξ) (fun _ => hξ)
      (a := fun t => hA.D [m] t.1 t.2) (fun t => haD t.1 t.2 m)
  refine ⟨K1 + (∑ m, K2 m) + 2 * K3 + (∑ m, K4 m) + (∑ m, K5 m) + (∑ m, K6 m)
      + K7 + K8 + K9 + K10 + K11, ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ ∑ m, K2 m := Finset.sum_nonneg fun m _ => hK2 m
    have h4 : (0 : ℝ) ≤ ∑ m, K4 m := Finset.sum_nonneg fun m _ => hK4 m
    have h5 : (0 : ℝ) ≤ ∑ m, K5 m := Finset.sum_nonneg fun m _ => hK5 m
    have h6 : (0 : ℝ) ≤ ∑ m, K6 m := Finset.sum_nonneg fun m _ => hK6 m
    linarith [hK1, hK3, hK7, hK8, hK9, hK10, hK11]
  intro ℓ uN Df HuN HDf B hHuN hHDf
  -- The twelve pieces.
  obtain ⟨F1, HF1, hB1, hp1⟩ := hP1 (fun _ => Df) (fun _ => HDf) (fun _ => hHDf)
  obtain ⟨F2, HF2, hB2, hp2⟩ := hP2 ℓ (fun i => HuN.D [i]) (fun i => HuN.deriv₁ i)
    (fun i => hHuN.deriv₁ i)
  obtain ⟨F3, HF3, hB3, hp3⟩ := hP3 (fun i => HuN.D [ℓ, i]) (fun i => HuN.deriv₂ i ℓ)
    (fun i => hHuN.deriv₂ i ℓ)
  obtain ⟨F4, HF4, hB4, hp4⟩ := hP4 ℓ (fun _ => uN)
    (fun _ => HuN.mono (Nat.le_add_right k 2))
    (fun _ => hHuN.mono_order (Nat.le_add_right k 2))
  obtain ⟨F5, HF5, hB5, hp5⟩ := hP5 ℓ (fun t => HuN.D [t.1]) (fun t => HuN.deriv₁ t.1)
    (fun t => hHuN.deriv₁ t.1)
  obtain ⟨F6, HF6, hB6, hp6⟩ := hP6 ℓ (fun t => HuN.D [t.2, t.1])
    (fun t => HuN.deriv₂ t.1 t.2) (fun t => hHuN.deriv₂ t.1 t.2)
  obtain ⟨F7, HF7, hB7, hp7⟩ := hP7 (fun t => HuN.D [t.1, ℓ]) (fun t => HuN.deriv₂ ℓ t.1)
    (fun t => hHuN.deriv₂ ℓ t.1)
  obtain ⟨F8, HF8, hB8, hp8⟩ := hP8 (fun _ => HuN.D [ℓ]) (fun _ => HuN.deriv₁ ℓ)
    (fun _ => hHuN.deriv₁ ℓ)
  obtain ⟨F9, HF9, hB9, hp9⟩ := hP9 (fun _ => HuN.D [ℓ]) (fun _ => HuN.deriv₁ ℓ)
    (fun _ => hHuN.deriv₁ ℓ)
  obtain ⟨F10, HF10, hB10, hp10⟩ := hP10 (fun t => HuN.D [t.2, ℓ])
    (fun t => HuN.deriv₂ ℓ t.2) (fun t => hHuN.deriv₂ ℓ t.2)
  obtain ⟨F11, HF11, hB11, hp11⟩ := hP11 (fun _ => HuN.D [ℓ]) (fun _ => HuN.deriv₁ ℓ)
    (fun _ => hHuN.deriv₁ ℓ)
  obtain ⟨F12, HF12, hB12, hp12⟩ := hP3 (fun i => HuN.D [i, ℓ]) (fun i => HuN.deriv₂ ℓ i)
    (fun i => hHuN.deriv₂ ℓ i)
  refine ⟨F1 - F2 - F3 - F4 + F5 + F6 - F7 - F8 - F9 - F10 + F11 + F12,
    ((((((((((HF1.sub HF2).sub HF3).sub HF4).add HF5).add HF6).sub HF7).sub HF8).sub
      HF9).sub HF10).add HF11).add HF12, ?_, ?_⟩
  · have hB := ((((((((((hB1.sub hB2).sub hB3).sub hB4).add hB5).add hB6).sub hB7).sub
      hB8).sub hB9).sub hB10).add hB11).add hB12
    refine hB.mono_const ?_
    have h2 : K2 ℓ ≤ ∑ m, K2 m := Finset.single_le_sum (fun m _ => hK2 m) (Finset.mem_univ ℓ)
    have h4 : K4 ℓ ≤ ∑ m, K4 m := Finset.single_le_sum (fun m _ => hK4 m) (Finset.mem_univ ℓ)
    have h5 : K5 ℓ ≤ ∑ m, K5 m := Finset.single_le_sum (fun m _ => hK5 m) (Finset.mem_univ ℓ)
    have h6 : K6 ℓ ≤ ∑ m, K6 m := Finset.single_le_sum (fun m _ => hK6 m) (Finset.mem_univ ℓ)
    have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg uN) hHuN.norm_le
    have hK : K1 + K2 ℓ + K3 + K4 ℓ + K5 ℓ + K6 ℓ + K7 + K8 + K9 + K10 + K11 + K3
        ≤ K1 + (∑ m, K2 m) + 2 * K3 + (∑ m, K4 m) + (∑ m, K5 m) + (∑ m, K6 m)
          + K7 + K8 + K9 + K10 + K11 := by linarith only [h2, h4, h5, h6]
    linarith only [mul_le_mul_of_nonneg_right hK hB0]
  · intro v hvc hvcs
    dsimp only [cutoffDatumPairing]
    rw [setIntegral_add_mul_testFn _ _ hvc hvcs, setIntegral_add_mul_testFn _ _ hvc hvcs,
      setIntegral_sub_mul_testFn _ _ hvc hvcs, setIntegral_sub_mul_testFn _ _ hvc hvcs,
      setIntegral_sub_mul_testFn _ _ hvc hvcs, setIntegral_sub_mul_testFn _ _ hvc hvcs,
      setIntegral_add_mul_testFn _ _ hvc hvcs, setIntegral_add_mul_testFn _ _ hvc hvcs,
      setIntegral_sub_mul_testFn _ _ hvc hvcs, setIntegral_sub_mul_testFn _ _ hvc hvcs,
      setIntegral_sub_mul_testFn _ _ hvc hvcs,
      hp1 v hvc hvcs, hp2 v hvc hvcs, hp3 v hvc hvcs, hp4 v hvc hvcs, hp5 v hvc hvcs,
      hp6 v hvc hvcs, hp7 v hvc hvcs, hp8 v hvc hvcs, hp9 v hvc hvcs, hp10 v hvc hvcs,
      hp11 v hvc hvcs, hp12 v hvc hvcs]
    simp only [Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]

end EllipticPdes.Regularity
