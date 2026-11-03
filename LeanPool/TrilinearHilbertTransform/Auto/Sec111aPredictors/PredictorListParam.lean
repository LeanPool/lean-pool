/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec111aPredictors.ExpansionCatalogTail

/-!
# Trilinear Hilbert transform: predictor_list_param
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate

open scoped Classical in
private def PredictorListParamConclusion13Statement : Prop :=
  ∀
    (κ : LocalKernelClass)
    (Ds : ℕ)
    (Cr : ℕ)
    (Dc : ℕ)
    (DJ : ℕ → ℕ)
    (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (B : ℝ)
    (τ : Type)
    (size : τ → ℝ),
  let T₀ : ℝ :=
    pdT0 Ds Cr H B
  ∀ (_ : T₀ = pdT0 Ds Cr H B)
    (_ : (1 : ℝ) ≤ T₀)
    (Qs : Finset τ)
    (_ : (↑Qs.card : ℝ) ≤ Real.exp ((10 : ℝ) * ((1 : ℝ) + Real.log H) ^ (2 : ℕ)) * ((3 : ℝ) *
      T₀) ^ ((3 : ℕ) * (d + e))),
  let R : Finset τ :=
    {q ∈ Qs | size q ≤ T₀}
  ∀ (_ : R = {q ∈ Qs | size q ≤ T₀}),
  let E : ℝ :=
    pdE Dc Ds Cr H B
  ∀ (_ : E = pdE Dc Ds Cr H B),
  let K₀ : ℕ :=
    pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B
  ∀ (_ : K₀ = pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B),
  let Bσ : ℝ :=
    E * (2 : ℝ) ^ K₀
  ∀ (_ : Bσ = E * (2 : ℝ) ^ K₀),
  let Mset : Finset (Matrix (Fin (d + e)) (Fin (d + e)) ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d + e)) =>
      boundedRationalEnumeration ⌊E⌋₊
  ∀ (_ : Mset = Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d +
      e)) => boundedRationalEnumeration ⌊E⌋₊),
  let σset : Finset (Fin (d + e) → ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => boundedRationalEnumeration ⌊Bσ⌋₊
  ∀ (_ : σset = Fintype.piFinset fun (_ : Fin (d + e)) => boundedRationalEnumeration ⌊Bσ⌋₊),
  (↑(R ×ˢ Mset ×ˢ σset).card : ℝ) ≤ pdCard κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B

open scoped Classical in
private def PredictorListParamCatalogTailBoundStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (Ds : ℕ)
    (Cr : ℕ)
    (Dc : ℕ)
    (DJ : ℕ → ℕ)
    (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (B : ℝ)
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (_ : (1 : ℝ) ≤ H)
    (τ : Type)
    (cf : τ → ℂ)
    (φa : τ → QuadraticChartData (d + e))
    (φb : τ → QuadraticChartData (d + e))
    (φt : τ → QuadraticChartData (d + e))
    (size : τ → ℝ),
  let Es : ℝ :=
    pdEs Ds H
  let T₀ : ℝ :=
    pdT0 Ds Cr H B
  ∀ (Qs : Finset τ),
  let R : Finset τ :=
    {q ∈ Qs | size q ≤ T₀}
  let M₀ : ℕ :=
    pdM0 Ds Cr H B
  let δ : ℝ :=
    Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))
  let A4 : τ → QuadraticChartData (d + e) :=
    fun (q : τ) => scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q)
  let ret : τ → ℝ → Prop :=
    fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r
  let E : ℝ :=
    pdE Dc Ds Cr H B
  let E1 : ℝ :=
    pdE1 (DJ (1 : ℕ)) Ds Cr H B
  ∀ (lamf : τ → ℝ → ℝ)
    (Mf : τ → ℝ → Matrix (Fin (d + e)) (Fin (d + e)) ℚ)
    (σf : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → Fin (d + e) → ℚ)
    (coeff : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ)
    (_ : ∀ (q : τ) (r : ℝ), q ∈ R → (0 : ℝ) < r → ret q r → (∀ (i j : Fin (d + e)),
      (↑(rationalHeight (Mf q r i j)) : ℝ) ≤ E) ∧ lamf q r = (φt q).quadratic + ∑ i :
      Fin (d + e), ∑ j : Fin (d + e), (φt q).horizontal i * (↑(Mf q r i j) : ℝ) * (φt
      q).horizontal j ∧ |lamf q r| * r ^ (2 : ℕ) ≤ E ∧ (∀ (p : ℕ × (Fin (d + e + (d +
      e)) → ℤ)) (i : Fin (d + e)), (↑(rationalHeight (σf q r p i)) : ℝ) ≤ E * ((1 : ℝ) +
      frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) * r → HasSum (fun (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)) => coeff q r p * quadPhase (lamf q r) ((φt q).linear + ∑ i
      : Fin (d + e), (↑(σf q r p i) : ℝ) * (φt q).horizontal i) t) (quadraticChartAtom
      (A4 q) t)) ∧ (Summable fun (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => ‖coeff q r p‖)
      ∧ ∑' (p : ℕ × (Fin (d + e + (d + e)) → ℤ)), ‖coeff q r p‖ ≤ E ∧ (∀ (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)), ⌊E⌋₊ ≤ p.1 → coeff q r p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d
      + e + (d + e)) → ℤ)), ‖coeff q r p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + e +
      (1 : ℕ)) ^ (2 : ℕ) ≤ E1),
  let K₀ : ℕ :=
    pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B
  let P : Finset (ℕ × (Fin (d + e + (d + e)) → ℤ)) :=
    Finset.range ⌊E⌋₊ ×ˢ frequencyTruncationSet (d + e + (d + e)) K₀
  ∀ (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : IsAdmissibleOpponent G J Fa za Ka)
    (_ : IsAdmissibleOpponent G J Fb zb Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : (1 : ℕ) ≤ d + e),
  let len : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => dyadicGridLength G I.1
  ∀ (_ : ∀ (I : ℤ × ℤ), (0 : ℝ) < len I),
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) ≤ Ka * Kb * Na * Nb),
  let ψA : τ → ℝ → ℂ :=
    fun (q : τ) => quadraticChartAtom (φa q)
  let ψB : τ → ℝ → ℂ :=
    fun (q : τ) => quadraticChartAtom (φb q)
  ∀ (_ : ∀ (q : τ), Measurable (ψA q))
    (_ : ∀ (q : τ), Measurable (ψB q))
    (_ : ∀ (q : τ) (y : ℝ), ‖ψA q y‖ ≤ (1 : ℝ))
    (_ : ∀ (q : τ) (y : ℝ), ‖ψB q y‖ ≤ (1 : ℝ)),
  let gam : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℝ :=
    fun (q : τ) (r : ℝ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => (φt q).linear + ∑ j :
      Fin (d + e), (↑(σf q r p j) : ℝ) * (φt q).horizontal j
  let sepP : ℤ × ℤ → τ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ :=
    fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => separatedLocalForm
      (len I) (w I) (quadPhase (lamf q (len I)) (gam q (len I) p)) a b (fun (y : ℝ) =>
      ψA q y * za I y) fun (y : ℝ) => ψB q y * zb I y
  let coeffI : ℤ × ℤ → τ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ :=
    fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => if q ∈ R ∧ ret q
      (len I) then coeff q (len I) p else (0 : ℂ)
  ∀ (_ : coeffI = fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => if q ∈ R ∧
      ret q (len I) then coeff q (len I) p else (0 : ℂ))
    (_ : ∑ q ∈ R, ‖cf q‖ ≤ Es)
    (_ : (0 : ℝ) ≤ E1),
  (∑ q ∈ R, (4 : ℝ) * ‖cf q‖ * ∑ I ∈ S with ret q (len I), len I * ∑' (p : ℕ × (Fin (d
    + e + (d + e)) → ℤ)), if p ∈ P then (0 : ℝ) else ‖coeffI I q p‖ * ‖sepP I q p‖) ≤
    Real.exp (-B) / (3 : ℝ) * (Ka * Kb * Na * Nb)

open scoped Classical in
private def PredictorListParamCatalogRegroupingStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (Ds : ℕ)
    (Cr : ℕ)
    (Dc : ℕ)
    (DJ : ℕ → ℕ)
    (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (B : ℝ)
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (τ : Type)
    (cf : τ → ℂ)
    (φa : τ → QuadraticChartData (d + e))
    (φb : τ → QuadraticChartData (d + e))
    (φt : τ → QuadraticChartData (d + e))
    (size : τ → ℝ),
  let T₀ : ℝ :=
    pdT0 Ds Cr H B
  ∀ (Qs : Finset τ),
  let R : Finset τ :=
    {q ∈ Qs | size q ≤ T₀}
  let M₀ : ℕ :=
    pdM0 Ds Cr H B
  let δ : ℝ :=
    Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))
  let A4 : τ → QuadraticChartData (d + e) :=
    fun (q : τ) => scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q)
  let ret : τ → ℝ → Prop :=
    fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r
  let E : ℝ :=
    pdE Dc Ds Cr H B
  let E1 : ℝ :=
    pdE1 (DJ (1 : ℕ)) Ds Cr H B
  ∀ (lamf : τ → ℝ → ℝ)
    (Mf : τ → ℝ → Matrix (Fin (d + e)) (Fin (d + e)) ℚ)
    (σf : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → Fin (d + e) → ℚ)
    (coeff : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ)
    (_ : ∀ (q : τ) (r : ℝ), q ∈ R → (0 : ℝ) < r → ret q r → (∀ (i j : Fin (d + e)),
      (↑(rationalHeight (Mf q r i j)) : ℝ) ≤ E) ∧ lamf q r = (φt q).quadratic + ∑ i :
      Fin (d + e), ∑ j : Fin (d + e), (φt q).horizontal i * (↑(Mf q r i j) : ℝ) * (φt
      q).horizontal j ∧ |lamf q r| * r ^ (2 : ℕ) ≤ E ∧ (∀ (p : ℕ × (Fin (d + e + (d +
      e)) → ℤ)) (i : Fin (d + e)), (↑(rationalHeight (σf q r p i)) : ℝ) ≤ E * ((1 : ℝ) +
      frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) * r → HasSum (fun (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)) => coeff q r p * quadPhase (lamf q r) ((φt q).linear + ∑ i
      : Fin (d + e), (↑(σf q r p i) : ℝ) * (φt q).horizontal i) t) (quadraticChartAtom
      (A4 q) t)) ∧ (Summable fun (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => ‖coeff q r p‖)
      ∧ ∑' (p : ℕ × (Fin (d + e + (d + e)) → ℤ)), ‖coeff q r p‖ ≤ E ∧ (∀ (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)), ⌊E⌋₊ ≤ p.1 → coeff q r p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d
      + e + (d + e)) → ℤ)), ‖coeff q r p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + e +
      (1 : ℕ)) ^ (2 : ℕ) ≤ E1),
  let K₀ : ℕ :=
    pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B
  let P : Finset (ℕ × (Fin (d + e + (d + e)) → ℤ)) :=
    Finset.range ⌊E⌋₊ ×ˢ frequencyTruncationSet (d + e + (d + e)) K₀
  let Bσ : ℝ :=
    E * (2 : ℝ) ^ K₀
  let Mset : Finset (Matrix (Fin (d + e)) (Fin (d + e)) ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d + e)) =>
      boundedRationalEnumeration ⌊E⌋₊
  let σset : Finset (Fin (d + e) → ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => boundedRationalEnumeration ⌊Bσ⌋₊
  let lamℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) => (φt
      ℓ.1).quadratic + ∑ i : Fin (d + e), ∑ j : Fin (d + e), (φt ℓ.1).horizontal i *
      (↑(ℓ.2.1 i j) : ℝ) * (φt ℓ.1).horizontal j
  let νℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) => ((φt
      ℓ.1).linear + ∑ i : Fin (d + e), (↑(ℓ.2.2 i) : ℝ) * (φt ℓ.1).horizontal i) /
      ((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ))
  let coefℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ → ℂ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) (r : ℝ) => if
      ℓ.1 ∈ R ∧ (0 : ℝ) < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then (4 : ℂ) * cf ℓ.1 * ∑ p ∈
      P with σf ℓ.1 r p = ℓ.2.2, coeff ℓ.1 r p else (0 : ℂ)
  ∀ (_ : coefℓ = fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) (r :
      ℝ) => if ℓ.1 ∈ R ∧ (0 : ℝ) < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then (4 : ℂ) * cf
      ℓ.1 * ∑ p ∈ P with σf ℓ.1 r p = ℓ.2.2, coeff ℓ.1 r p else (0 : ℂ))
    (G : RealDyadicGrid)
    (S : Finset (ℤ × ℤ))
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (f : ℤ × ℤ → Fin (4 : ℕ) → ℝ → ℂ),
  let len : ℤ × ℤ → ℝ :=
    fun (I : ℤ × ℤ) => dyadicGridLength G I.1
  ∀ (_ : ∀ (I : ℤ × ℤ), (0 : ℝ) < len I),
  let ψA : τ → ℝ → ℂ :=
    fun (q : τ) => quadraticChartAtom (φa q)
  let ψB : τ → ℝ → ℂ :=
    fun (q : τ) => quadraticChartAtom (φb q)
  let gam : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℝ :=
    fun (q : τ) (r : ℝ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => (φt q).linear + ∑ j :
      Fin (d + e), (↑(σf q r p j) : ℝ) * (φt q).horizontal j
  let sepP : ℤ × ℤ → τ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ :=
    fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => separatedLocalForm
      (len I) (w I) (quadPhase (lamf q (len I)) (gam q (len I) p)) a b (fun (y : ℝ) =>
      ψA q y * za I y) fun (y : ℝ) => ψB q y * zb I y
  ∀ (_ : sepP = fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) =>
      separatedLocalForm (len I) (w I) (quadPhase (lamf q (len I)) (gam q (len I) p)) a
      b (fun (y : ℝ) => ψA q y * za I y) fun (y : ℝ) => ψB q y * zb I y),
  let coeffI : ℤ × ℤ → τ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ :=
    fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => if q ∈ R ∧ ret q
      (len I) then coeff q (len I) p else (0 : ℂ)
  ∀ (_ : coeffI = fun (I : ℤ × ℤ) (q : τ) (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => if q ∈ R ∧
      ret q (len I) then coeff q (len I) p else (0 : ℂ)),
  ∀ I ∈ S, len I * ‖localProgressionForm (len I) (w I) (f I) - ∑ ℓ ∈ R ×ˢ Mset ×ˢ
    σset, coefℓ ℓ (len I) * separatedLocalForm (len I) (w I) (fun (t : ℝ) => (↑((𝐞 : ℝ
    → Circle) (lamℓ ℓ * t ^ (2 : ℕ))) : ℂ)) a b (fun (y : ℝ) => za I y *
    quadraticChartAtom (modulateQuadraticChart (φa ℓ.1) (-νℓ ℓ)) y) fun (y : ℝ) => zb
    I y * quadraticChartAtom (modulateQuadraticChart (φb ℓ.1) (νℓ ℓ)) y‖ = len I *
    ‖localProgressionForm (len I) (w I) (f I) - ∑ q ∈ R, if ret q (len I) then (4 : ℂ)
    * cf q * ∑ p ∈ P, coeffI I q p * sepP I q p else (0 : ℂ)‖

open scoped Classical in
private def PredictorListParamConclusion15Statement : Prop :=
  ∀
    (κ : LocalKernelClass)
    (Ds : ℕ)
    (Cr : ℕ)
    (Dc : ℕ)
    (DJ : ℕ → ℕ)
    (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (B : ℝ)
    (τ : Type)
    (cf : τ → ℂ)
    (φt : τ → QuadraticChartData (d + e))
    (size : τ → ℝ)
    (_ : Summable fun (q : τ) => ‖cf q‖),
  let Es : ℝ :=
    pdEs Ds H
  ∀ (_ : ∑' (q : τ), ‖cf q‖ ≤ Es)
    (_ : Es = pdEs Ds H),
  let T₀ : ℝ :=
    pdT0 Ds Cr H B
  ∀ (Qs : Finset τ),
  let R : Finset τ :=
    {q ∈ Qs | size q ≤ T₀}
  let M₀ : ℕ :=
    pdM0 Ds Cr H B
  let δ : ℝ :=
    Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))
  let A4 : τ → QuadraticChartData (d + e) :=
    fun (q : τ) => scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q)
  let ret : τ → ℝ → Prop :=
    fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r
  let E : ℝ :=
    pdE Dc Ds Cr H B
  ∀ (_ : E = pdE Dc Ds Cr H B),
  let E1 : ℝ :=
    pdE1 (DJ (1 : ℕ)) Ds Cr H B
  ∀ (lamf : τ → ℝ → ℝ)
    (Mf : τ → ℝ → Matrix (Fin (d + e)) (Fin (d + e)) ℚ)
    (σf : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → Fin (d + e) → ℚ)
    (coeff : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ)
    (_ : ∀ (q : τ) (r : ℝ), q ∈ R → (0 : ℝ) < r → ret q r → (∀ (i j : Fin (d + e)),
      (↑(rationalHeight (Mf q r i j)) : ℝ) ≤ E) ∧ lamf q r = (φt q).quadratic + ∑ i :
      Fin (d + e), ∑ j : Fin (d + e), (φt q).horizontal i * (↑(Mf q r i j) : ℝ) * (φt
      q).horizontal j ∧ |lamf q r| * r ^ (2 : ℕ) ≤ E ∧ (∀ (p : ℕ × (Fin (d + e + (d +
      e)) → ℤ)) (i : Fin (d + e)), (↑(rationalHeight (σf q r p i)) : ℝ) ≤ E * ((1 : ℝ) +
      frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) * r → HasSum (fun (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)) => coeff q r p * quadPhase (lamf q r) ((φt q).linear + ∑ i
      : Fin (d + e), (↑(σf q r p i) : ℝ) * (φt q).horizontal i) t) (quadraticChartAtom
      (A4 q) t)) ∧ (Summable fun (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => ‖coeff q r p‖)
      ∧ ∑' (p : ℕ × (Fin (d + e + (d + e)) → ℤ)), ‖coeff q r p‖ ≤ E ∧ (∀ (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)), ⌊E⌋₊ ≤ p.1 → coeff q r p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d
      + e + (d + e)) → ℤ)), ‖coeff q r p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + e +
      (1 : ℕ)) ^ (2 : ℕ) ≤ E1),
  let K₀ : ℕ :=
    pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B
  let P : Finset (ℕ × (Fin (d + e + (d + e)) → ℤ)) :=
    Finset.range ⌊E⌋₊ ×ˢ frequencyTruncationSet (d + e + (d + e)) K₀
  let Bσ : ℝ :=
    E * (2 : ℝ) ^ K₀
  let Mset : Finset (Matrix (Fin (d + e)) (Fin (d + e)) ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d + e)) =>
      boundedRationalEnumeration ⌊E⌋₊
  let σset : Finset (Fin (d + e) → ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => boundedRationalEnumeration ⌊Bσ⌋₊
  let coefℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ → ℂ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) (r : ℝ) => if
      ℓ.1 ∈ R ∧ (0 : ℝ) < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then (4 : ℂ) * cf ℓ.1 * ∑ p ∈
      P with σf ℓ.1 r p = ℓ.2.2, coeff ℓ.1 r p else (0 : ℂ)
  ∀ (_ : coefℓ = fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) (r :
      ℝ) => if ℓ.1 ∈ R ∧ (0 : ℝ) < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then (4 : ℂ) * cf
      ℓ.1 * ∑ p ∈ P with σf ℓ.1 r p = ℓ.2.2, coeff ℓ.1 r p else (0 : ℂ)),
  ∀ (r : ℝ), ∑ ℓ ∈ R ×ˢ Mset ×ˢ σset, ‖coefℓ ℓ r‖ ≤ (4 : ℝ) * Es * E

open scoped Classical in
private def PredictorListParamConclusion17Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₁ : ℕ)
    (Ds : ℕ)
    (Cr : ℕ)
    (_ : ∀ {d : ℕ} (H : ℝ) (A : QuadraticChartData d), (1 : ℕ) ≤ d → QuadraticChartComplexity
      c₁ H A → IsBoundedQuadraticChart A → ∀ (M₀ : ℕ) (G : RealDyadicGrid) (J : ℤ × ℤ)
      (S : Finset (ℤ × ℤ)), (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1
      J.2) → ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) → ∀ {a b : Fin (4 :
      ℕ)}, a ≠ b → ∀ {ψa ψb : ℝ → ℂ}, Measurable ψa → Measurable ψb → (∀ (y : ℝ), ‖ψa y‖
      ≤ (1 : ℝ)) → (∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ)) → ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ
      → ℂ} {Ka Kb : ℝ}, (0 : ℝ) ≤ Ka → (0 : ℝ) ≤ Kb → IsAdmissibleOpponent G J Fa za Ka
      → IsAdmissibleOpponent G J Fb zb Kb → HasDepthEnergy G J Fa za Ka → HasDepthEnergy
      G J Fb zb Kb → (∀ (I : ℤ × ℤ), Measurable (za I)) → (∀ (I : ℤ × ℤ), Measurable (zb
      I)) → (∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell
      G I.1 I.2))) → (∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict
      (dyadicGridCell G I.1 I.2))) → (∀ I ∈ S, bandSup (quadraticChartAtom
      (scaleQuadraticChartAmplitude (1 / 4 : ℂ) A)) (dyadicGridLength G I.1) ≤ Real.exp
      (-(↑M₀ : ℝ))) → ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm
      (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b (fun (y : ℝ) => ψa y *
      za I y) fun (y : ℝ) => ψb y * zb I y‖ ≤ Real.exp (-(↑M₀ : ℝ) / (2 : ℝ)) * ((↑Cr :
      ℝ) * ((2 : ℝ) + Real.log H) ^ Cr) * Ka * Kb * √(∫ (y : ℝ) in dyadicGridCell G J.1
      J.2, ‖Fa y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 :
      ℕ)))
    (Dc : ℕ)
    (DJ : ℕ → ℕ)
    (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (B : ℝ)
    (A : QuadraticChartData d)
    (A' : QuadraticChartData e)
    (_ : (1 : ℕ) ≤ d)
    (_ : (1 : ℕ) ≤ e)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ i)
    (_ : a ≠ k)
    (_ : a ≠ b)
    (_ : i ≠ k)
    (_ : i ≠ b)
    (_ : k ≠ b)
    (_ : (1 : ℝ) ≤ H)
    (τ : Type)
    (_ : Countable τ)
    (cf : τ → ℂ)
    (φa : τ → QuadraticChartData (d + e))
    (φb : τ → QuadraticChartData (d + e))
    (φt : τ → QuadraticChartData (d + e))
    (size : τ → ℝ)
    (_ : ∀ (x t : ℝ), HasSum (fun (q : τ) => cf q * quadraticChartAtom (φa q) (x + (↑(↑(↑a :
      ℕ) : ℤ) : ℝ) * t) * quadraticChartAtom (φb q) (x + (↑(↑(↑b : ℕ) : ℤ) : ℝ) * t) *
      quadraticChartAtom (φt q) t) (quadraticChartAtom A (x + (↑(↑(↑i : ℕ) : ℤ) : ℝ) *
      t) * quadraticChartAtom A' (x + (↑(↑(↑k : ℕ) : ℤ) : ℝ) * t)))
    (_ : ∀ (q : τ), IsBoundedQuadraticChart (φa q) ∧ IsBoundedQuadraticChart (φb q) ∧
      IsBoundedQuadraticChart (φt q))
    (_ : ∀ (q : τ), (1 : ℝ) ≤ size q)
    (_ : Summable fun (q : τ) => ‖cf q‖),
  let Es : ℝ :=
    pdEs Ds H
  ∀ (_ : ∀ (q : τ), QuadraticChartComplexity c₁ ((Es * size q) ^ (6 : ℕ)) (φa q) ∧
      QuadraticChartComplexity c₁ ((Es * size q) ^ (6 : ℕ)) (φb q) ∧
      QuadraticChartComplexity c₁ ((Es * size q) ^ (6 : ℕ)) (φt q))
    (_ : ∀ (T : ℝ), (1 : ℝ) ≤ T → (∑' (q : τ), if T ≤ size q then ‖cf q‖ else (0 : ℝ)) ≤ Es /
      T ^ (100 : ℕ))
    (_ : ∑' (q : τ), ‖cf q‖ ≤ Es)
    (_ : Es = pdEs Ds H),
  let T₀ : ℝ :=
    pdT0 Ds Cr H B
  ∀ (_ : (1 : ℝ) ≤ T₀)
    (Qs : Finset τ),
  let R : Finset τ :=
    {q ∈ Qs | size q ≤ T₀}
  ∀ (_ : ∀ q ∉ R, T₀ < size q),
  let H₀ : ℝ :=
    pdH0 Ds Cr H B
  ∀ (_ : (1 : ℝ) ≤ H₀)
    (_ : ∀ q ∈ R, QuadraticChartComplexity c₁ H₀ (φt q) ∧ QuadraticChartComplexity c₁ H₀ (φa
      q) ∧ QuadraticChartComplexity c₁ H₀ (φb q)),
  let M₀ : ℕ :=
    pdM0 Ds Cr H B
  let δ : ℝ :=
    Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))
  ∀ (_ : δ = Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))),
  let A4 : τ → QuadraticChartData (d + e) :=
    fun (q : τ) => scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q)
  let ret : τ → ℝ → Prop :=
    fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r
  ∀ (_ : ret = fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r),
  let E : ℝ :=
    pdE Dc Ds Cr H B
  let E1 : ℝ :=
    pdE1 (DJ (1 : ℕ)) Ds Cr H B
  ∀ (_ : E1 = pdE1 (DJ (1 : ℕ)) Ds Cr H B)
    (lamf : τ → ℝ → ℝ)
    (Mf : τ → ℝ → Matrix (Fin (d + e)) (Fin (d + e)) ℚ)
    (σf : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → Fin (d + e) → ℚ)
    (coeff : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ)
    (_ : ∀ (q : τ) (r : ℝ), q ∈ R → (0 : ℝ) < r → ret q r → (∀ (i j : Fin (d + e)),
      (↑(rationalHeight (Mf q r i j)) : ℝ) ≤ E) ∧ lamf q r = (φt q).quadratic + ∑ i :
      Fin (d + e), ∑ j : Fin (d + e), (φt q).horizontal i * (↑(Mf q r i j) : ℝ) * (φt
      q).horizontal j ∧ |lamf q r| * r ^ (2 : ℕ) ≤ E ∧ (∀ (p : ℕ × (Fin (d + e + (d +
      e)) → ℤ)) (i : Fin (d + e)), (↑(rationalHeight (σf q r p i)) : ℝ) ≤ E * ((1 : ℝ) +
      frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) * r → HasSum (fun (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)) => coeff q r p * quadPhase (lamf q r) ((φt q).linear + ∑ i
      : Fin (d + e), (↑(σf q r p i) : ℝ) * (φt q).horizontal i) t) (quadraticChartAtom
      (A4 q) t)) ∧ (Summable fun (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => ‖coeff q r p‖)
      ∧ ∑' (p : ℕ × (Fin (d + e + (d + e)) → ℤ)), ‖coeff q r p‖ ≤ E ∧ (∀ (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)), ⌊E⌋₊ ≤ p.1 → coeff q r p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d
      + e + (d + e)) → ℤ)), ‖coeff q r p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + e +
      (1 : ℕ)) ^ (2 : ℕ) ≤ E1),
  let K₀ : ℕ :=
    pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B
  let P : Finset (ℕ × (Fin (d + e + (d + e)) → ℤ)) :=
    Finset.range ⌊E⌋₊ ×ˢ frequencyTruncationSet (d + e + (d + e)) K₀
  let Bσ : ℝ :=
    E * (2 : ℝ) ^ K₀
  let Mset : Finset (Matrix (Fin (d + e)) (Fin (d + e)) ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d + e)) =>
      boundedRationalEnumeration ⌊E⌋₊
  let σset : Finset (Fin (d + e) → ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => boundedRationalEnumeration ⌊Bσ⌋₊
  let lamℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) => (φt
      ℓ.1).quadratic + ∑ i : Fin (d + e), ∑ j : Fin (d + e), (φt ℓ.1).horizontal i *
      (↑(ℓ.2.1 i j) : ℝ) * (φt ℓ.1).horizontal j
  let νℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) => ((φt
      ℓ.1).linear + ∑ i : Fin (d + e), (↑(ℓ.2.2 i) : ℝ) * (φt ℓ.1).horizontal i) /
      ((↑(↑b : ℕ) : ℝ) - (↑(↑a : ℕ) : ℝ))
  let coefℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ) → ℝ → ℂ :=
    fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) (r : ℝ) => if
      ℓ.1 ∈ R ∧ (0 : ℝ) < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then (4 : ℂ) * cf ℓ.1 * ∑ p ∈
      P with σf ℓ.1 r p = ℓ.2.2, coeff ℓ.1 r p else (0 : ℂ)
  ∀ (_ : coefℓ = fun (ℓ : τ × Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) (r :
      ℝ) => if ℓ.1 ∈ R ∧ (0 : ℝ) < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then (4 : ℂ) * cf
      ℓ.1 * ∑ p ∈ P with σf ℓ.1 r p = ℓ.2.2, coeff ℓ.1 r p else (0 : ℂ)),
  ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)), (∀ I ∈ S, dyadicGridCell G
    I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) → ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S,
    IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w
    I)) → ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, (0 : ℝ) ≤ Ka → (0 :
    ℝ) ≤ Kb → IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
    HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb → (∀ (I : ℤ × ℤ),
    Measurable (za I)) → (∀ (I : ℤ × ℤ), Measurable (zb I)) → (∀ (I : ℤ × ℤ), MemLp
    (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1 I.2))) → (∀ (I : ℤ ×
    ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1 I.2))) → ∀
    (f : ℤ × ℤ → Fin (4 : ℕ) → ℝ → ℂ), (∀ (I : ℤ × ℤ), f I a = za I) → (∀ (I : ℤ × ℤ),
    f I i = quadraticChartAtom A) → (∀ (I : ℤ × ℤ), f I k = quadraticChartAtom A') →
    (∀ (I : ℤ × ℤ), f I b = zb I) → ∑ I ∈ S, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (f I) - ∑ ℓ ∈ R ×ˢ Mset ×ˢ
    σset, coefℓ ℓ (dyadicGridLength G I.1) * separatedLocalForm (dyadicGridLength G
    I.1) (w I) (fun (t : ℝ) => (↑((𝐞 : ℝ → Circle) (lamℓ ℓ * t ^ (2 : ℕ))) : ℂ)) a b
    (fun (y : ℝ) => za I y * quadraticChartAtom ((fun (ℓ : τ × Matrix (Fin (d + e))
    (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) => modulateQuadraticChart (φa ℓ.1) (-νℓ ℓ))
    ℓ) y) fun (y : ℝ) => zb I y * quadraticChartAtom ((fun (ℓ : τ × Matrix (Fin (d +
    e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) => modulateQuadraticChart (φb ℓ.1) (νℓ
    ℓ)) ℓ) y‖ ≤ Real.exp (-B) * Ka * Kb * √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa
    y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))

open scoped Classical in
private def PredictorListParamStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₁ : ℕ)
    (Ds : ℕ)
    (Cr : ℕ)
    (_ : ∀ {d : ℕ} (H : ℝ) (A : QuadraticChartData d), (1 : ℕ) ≤ d → QuadraticChartComplexity
      c₁ H A → IsBoundedQuadraticChart A → ∀ (M₀ : ℕ) (G : RealDyadicGrid) (J : ℤ × ℤ)
      (S : Finset (ℤ × ℤ)), (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1
      J.2) → ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) → ∀ {a b : Fin (4 :
      ℕ)}, a ≠ b → ∀ {ψa ψb : ℝ → ℂ}, Measurable ψa → Measurable ψb → (∀ (y : ℝ), ‖ψa y‖
      ≤ (1 : ℝ)) → (∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ)) → ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ
      → ℂ} {Ka Kb : ℝ}, (0 : ℝ) ≤ Ka → (0 : ℝ) ≤ Kb → IsAdmissibleOpponent G J Fa za Ka
      → IsAdmissibleOpponent G J Fb zb Kb → HasDepthEnergy G J Fa za Ka → HasDepthEnergy
      G J Fb zb Kb → (∀ (I : ℤ × ℤ), Measurable (za I)) → (∀ (I : ℤ × ℤ), Measurable (zb
      I)) → (∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell
      G I.1 I.2))) → (∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict
      (dyadicGridCell G I.1 I.2))) → (∀ I ∈ S, bandSup (quadraticChartAtom
      (scaleQuadraticChartAmplitude (1 / 4 : ℂ) A)) (dyadicGridLength G I.1) ≤ Real.exp
      (-(↑M₀ : ℝ))) → ∑ I ∈ S, dyadicGridLength G I.1 * ‖separatedLocalForm
      (dyadicGridLength G I.1) (w I) (quadraticChartAtom A) a b (fun (y : ℝ) => ψa y *
      za I y) fun (y : ℝ) => ψb y * zb I y‖ ≤ Real.exp (-(↑M₀ : ℝ) / (2 : ℝ)) * ((↑Cr :
      ℝ) * ((2 : ℝ) + Real.log H) ^ Cr) * Ka * Kb * √(∫ (y : ℝ) in dyadicGridCell G J.1
      J.2, ‖Fa y‖ ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 :
      ℕ)))
    (Dc : ℕ)
    (DJ : ℕ → ℕ)
    (d : ℕ)
    (e : ℕ)
    (H : ℝ)
    (B : ℝ)
    (A : QuadraticChartData d)
    (A' : QuadraticChartData e)
    (_ : (1 : ℕ) ≤ d)
    (_ : (1 : ℕ) ≤ e)
    (a : Fin (4 : ℕ))
    (i : Fin (4 : ℕ))
    (k : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ i)
    (_ : a ≠ k)
    (_ : a ≠ b)
    (_ : i ≠ k)
    (_ : i ≠ b)
    (_ : k ≠ b)
    (_ : (1 : ℝ) ≤ H)
    (τ : Type)
    (_ : Countable τ)
    (cf : τ → ℂ)
    (φa : τ → QuadraticChartData (d + e))
    (φb : τ → QuadraticChartData (d + e))
    (φt : τ → QuadraticChartData (d + e))
    (size : τ → ℝ)
    (_ : ∀ (x t : ℝ), HasSum (fun (q : τ) => cf q * quadraticChartAtom (φa q) (x + (↑(↑(↑a :
      ℕ) : ℤ) : ℝ) * t) * quadraticChartAtom (φb q) (x + (↑(↑(↑b : ℕ) : ℤ) : ℝ) * t) *
      quadraticChartAtom (φt q) t) (quadraticChartAtom A (x + (↑(↑(↑i : ℕ) : ℤ) : ℝ) *
      t) * quadraticChartAtom A' (x + (↑(↑(↑k : ℕ) : ℤ) : ℝ) * t)))
    (_ : ∀ (q : τ), IsBoundedQuadraticChart (φa q) ∧ IsBoundedQuadraticChart (φb q) ∧
      IsBoundedQuadraticChart (φt q))
    (_ : ∀ (q : τ), (1 : ℝ) ≤ size q)
    (_ : Summable fun (q : τ) => ‖cf q‖),
  let Es : ℝ :=
    pdEs Ds H
  ∀ (_ : ∀ (q : τ), QuadraticChartComplexity c₁ ((Es * size q) ^ (6 : ℕ)) (φa q) ∧
      QuadraticChartComplexity c₁ ((Es * size q) ^ (6 : ℕ)) (φb q) ∧
      QuadraticChartComplexity c₁ ((Es * size q) ^ (6 : ℕ)) (φt q))
    (_ : ∀ (T : ℝ), (1 : ℝ) ≤ T → (∑' (q : τ), if T ≤ size q then ‖cf q‖ else (0 : ℝ)) ≤ Es /
      T ^ (100 : ℕ))
    (_ : ∑' (q : τ), ‖cf q‖ ≤ Es)
    (_ : Es = pdEs Ds H),
  let T₀ : ℝ :=
    pdT0 Ds Cr H B
  ∀ (_ : T₀ = pdT0 Ds Cr H B)
    (_ : (1 : ℝ) ≤ T₀)
    (Qs : Finset τ)
    (_ : (↑Qs.card : ℝ) ≤ Real.exp ((10 : ℝ) * ((1 : ℝ) + Real.log H) ^ (2 : ℕ)) * ((3 : ℝ) *
      T₀) ^ ((3 : ℕ) * (d + e))),
  let R : Finset τ :=
    {q ∈ Qs | size q ≤ T₀}
  ∀ (_ : R = {q ∈ Qs | size q ≤ T₀})
    (_ : ∀ q ∉ R, T₀ < size q),
  let H₀ : ℝ :=
    pdH0 Ds Cr H B
  ∀ (_ : (1 : ℝ) ≤ H₀)
    (_ : ∀ q ∈ R, QuadraticChartComplexity c₁ H₀ (φt q) ∧ QuadraticChartComplexity c₁ H₀ (φa
      q) ∧ QuadraticChartComplexity c₁ H₀ (φb q)),
  let M₀ : ℕ :=
    pdM0 Ds Cr H B
  let δ : ℝ :=
    Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))
  ∀ (_ : δ = Real.exp (-((↑M₀ : ℝ) + (1 : ℝ)))),
  let A4 : τ → QuadraticChartData (d + e) :=
    fun (q : τ) => scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q)
  let ret : τ → ℝ → Prop :=
    fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r
  ∀ (_ : ret = fun (q : τ) (r : ℝ) => δ < bandSup (quadraticChartAtom (A4 q)) r),
  let E : ℝ :=
    pdE Dc Ds Cr H B
  ∀ (_ : E = pdE Dc Ds Cr H B),
  let E1 : ℝ :=
    pdE1 (DJ (1 : ℕ)) Ds Cr H B
  ∀ (_ : E1 = pdE1 (DJ (1 : ℕ)) Ds Cr H B)
    (lamf : τ → ℝ → ℝ)
    (Mf : τ → ℝ → Matrix (Fin (d + e)) (Fin (d + e)) ℚ)
    (σf : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → Fin (d + e) → ℚ)
    (coeff : τ → ℝ → ℕ × (Fin (d + e + (d + e)) → ℤ) → ℂ)
    (_ : ∀ (q : τ) (r : ℝ), q ∈ R → (0 : ℝ) < r → ret q r → (∀ (i j : Fin (d + e)),
      (↑(rationalHeight (Mf q r i j)) : ℝ) ≤ E) ∧ lamf q r = (φt q).quadratic + ∑ i :
      Fin (d + e), ∑ j : Fin (d + e), (φt q).horizontal i * (↑(Mf q r i j) : ℝ) * (φt
      q).horizontal j ∧ |lamf q r| * r ^ (2 : ℕ) ≤ E ∧ (∀ (p : ℕ × (Fin (d + e + (d +
      e)) → ℤ)) (i : Fin (d + e)), (↑(rationalHeight (σf q r p i)) : ℝ) ≤ E * ((1 : ℝ) +
      frequencyLength p.2)) ∧ (∀ (t : ℝ), |t| ≤ (2 : ℝ) * r → HasSum (fun (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)) => coeff q r p * quadPhase (lamf q r) ((φt q).linear + ∑ i
      : Fin (d + e), (↑(σf q r p i) : ℝ) * (φt q).horizontal i) t) (quadraticChartAtom
      (A4 q) t)) ∧ (Summable fun (p : ℕ × (Fin (d + e + (d + e)) → ℤ)) => ‖coeff q r p‖)
      ∧ ∑' (p : ℕ × (Fin (d + e + (d + e)) → ℤ)), ‖coeff q r p‖ ≤ E ∧ (∀ (p : ℕ × (Fin
      (d + e + (d + e)) → ℤ)), ⌊E⌋₊ ≤ p.1 → coeff q r p = (0 : ℂ)) ∧ ∀ (p : ℕ × (Fin (d
      + e + (d + e)) → ℤ)), ‖coeff q r p‖ * ((1 : ℝ) + frequencyLength p.2) ^ (d + e +
      (1 : ℕ)) ^ (2 : ℕ) ≤ E1),
  let K₀ : ℕ :=
    pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B
  ∀ (_ : K₀ = pdK0 κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B),
  let Bσ : ℝ :=
    E * (2 : ℝ) ^ K₀
  ∀ (_ : Bσ = E * (2 : ℝ) ^ K₀),
  let Mset : Finset (Matrix (Fin (d + e)) (Fin (d + e)) ℚ) :=
    Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d + e)) =>
      boundedRationalEnumeration ⌊E⌋₊
  ∀ (_ : Mset = Fintype.piFinset fun (_ : Fin (d + e)) => Fintype.piFinset fun (_ : Fin (d +
      e)) => boundedRationalEnumeration ⌊E⌋₊),
  ∃ (ι : Type) (L : Finset ι) (ψa : ι → QuadraticChartData (d + e)) (ψb : ι →
    QuadraticChartData (d + e)) (lam : ι → ℝ) (coef : ι → ℝ → ℂ), (↑L.card : ℝ) ≤
    pdCard κ (d + e) Dc (DJ (1 : ℕ)) Ds Cr H B ∧ (∀ ℓ ∈ L, IsBoundedQuadraticChart (ψa
    ℓ) ∧ IsBoundedQuadraticChart (ψb ℓ) ∧ QuadraticChartComplexity c₁ H₀ (ψa ℓ) ∧
    QuadraticChartComplexity c₁ H₀ (ψb ℓ)) ∧ (∀ (r : ℝ), ∑ ℓ ∈ L, ‖coef ℓ r‖ ≤ (4 : ℝ)
    * Es * E) ∧ (∀ (ℓ : ι) (r : ℝ), coef ℓ r ≠ (0 : ℂ) → |lam ℓ| * r ^ (2 : ℕ) ≤ E) ∧
    ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)), (∀ I ∈ S, dyadicGridCell
    G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) → ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S,
    IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w
    I)) → ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, (0 : ℝ) ≤ Ka → (0 :
    ℝ) ≤ Kb → IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
    HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb → (∀ (I : ℤ × ℤ),
    Measurable (za I)) → (∀ (I : ℤ × ℤ), Measurable (zb I)) → (∀ (I : ℤ × ℤ), MemLp
    (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1 I.2))) → (∀ (I : ℤ ×
    ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1 I.2))) → ∀
    (f : ℤ × ℤ → Fin (4 : ℕ) → ℝ → ℂ), (∀ (I : ℤ × ℤ), f I a = za I) → (∀ (I : ℤ × ℤ),
    f I i = quadraticChartAtom A) → (∀ (I : ℤ × ℤ), f I k = quadraticChartAtom A') →
    (∀ (I : ℤ × ℤ), f I b = zb I) → ∑ I ∈ S, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (f I) - ∑ ℓ ∈ L, coef ℓ
    (dyadicGridLength G I.1) * separatedLocalForm (dyadicGridLength G I.1) (w I) (fun
    (t : ℝ) => (↑((𝐞 : ℝ → Circle) (lam ℓ * t ^ (2 : ℕ))) : ℂ)) a b (fun (y : ℝ) => za
    I y * quadraticChartAtom (ψa ℓ) y) fun (y : ℝ) => zb I y * quadraticChartAtom (ψb
    ℓ) y‖ ≤ Real.exp (-B) * Ka * Kb * √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖
    ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))

private theorem predictor_list_param_conclusion_13 : PredictorListParamConclusion13Statement := by
  classical
  intro κ Ds Cr Dc DJ d e H B τ size T₀ hT₀ hT₀1 Qs hQscard R hR E hE K₀ hK₀ Bσ hBσ Mset hMset
    σset hσset
  -- the size of the list
  have hE1' : 1 ≤ E := one_le_pdE Dc Ds Cr H B
  have hfE : 1 ≤ ⌊E⌋₊ := Nat.le_floor (by exact_mod_cast hE1')
  have hBσ1 : 1 ≤ Bσ := by
    rw [hBσ]; exact one_le_mul_of_one_le_of_one_le hE1' (one_le_pow₀ (by norm_num))
  have hfB : 1 ≤ ⌊Bσ⌋₊ := Nat.le_floor (by exact_mod_cast hBσ1)
  have hR : (R.card : ℝ) ≤ Real.exp (10 * pdX H ^ 2) * (3 * T₀) ^ (3 * (d + e)) := by
    refine (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans ?_
    rw [pdX]; exact hQscard
  have hMs : (Mset.card : ℝ) ≤ (3 * (⌊E⌋₊ : ℝ) ^ 2) ^ ((d + e) * (d + e)) := by
    have hc : Mset.card = (boundedRationalEnumeration ⌊E⌋₊).card ^ ((d + e) * (d + e)) := by
      rw [hMset, pow_mul]
      erw [Fintype.card_piFinset]
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc]
    have h := boundedRationalEnumeration_card ⌊E⌋₊ hfE
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) _
  have hσs : (σset.card : ℝ) ≤ (3 * (⌊Bσ⌋₊ : ℝ) ^ 2) ^ (d + e) := by
    rw [hσset, Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h := boundedRationalEnumeration_card ⌊Bσ⌋₊ hfB
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast h) _
  rw [Finset.card_product, Finset.card_product]
  push_cast
  unfold pdCard
  rw [← hT₀, ← hE, ← hK₀, ← hBσ]
  calc (R.card : ℝ) * ((Mset.card : ℝ) * (σset.card : ℝ))
      ≤ (Real.exp (10 * pdX H ^ 2) * (3 * T₀) ^ (3 * (d + e))) *
        ((3 * (⌊E⌋₊ : ℝ) ^ 2) ^ ((d + e) * (d + e)) * (3 * (⌊Bσ⌋₊ : ℝ) ^ 2) ^ (d + e)) := by
        gcongr
    _ = _ := by ring

private theorem predictor_list_param_catalog_tail_bound :
  PredictorListParamCatalogTailBoundStatement := by
  classical
  intro κ Ds Cr Dc DJ d e H B a b h3 hH1 τ cf φa φb φt size Es T₀ Qs R M₀ δ A4 ret E E1 lamf Mf σf
    coeff hprops K₀ P G J S hSJ w hw Fa Fb za zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2
    hde len hlen0 Na Nb hK ψA ψB hψAm hψBm hψAb hψBb gam sepP coeffI hcoeffI hsumR hE10
  set! W := (⌊E⌋₊ : ℝ) * (E1 * tailCT κ (d + e) E *
    (2 * 7 ^ ((d + e) + (d + e)) * (2 * Real.pi) ^ (((d + e) + 1) ^ 2 - 1) / 2 ^ K₀))
    with hW
  have hW0 : 0 ≤ W := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hE10
    (tailCT_nonneg κ (d + e) (one_le_pdE Dc Ds Cr H B))) (by positivity))
  have hpt : ∀ q ∈ R, ∑ I ∈ S.filter (fun I => ret q (len I)), len I *
      ∑' p, (if p ∈ P then 0 else ‖coeffI I q p‖ * ‖sepP I q p‖) ≤
      W * (Ka * Kb * Na * Nb) := by
    intro q hq
    have h := expansion_catalog_tail κ hde (φt q) (one_le_pdE Dc Ds Cr H B) hE10 K₀ G J
      (S.filter (fun I => ret q (len I))) (fun I hI => hSJ I (Finset.mem_filter.mp hI).1)
      w (fun I hI => hw I (Finset.mem_filter.mp hI).1) h3 (hψAm q) (hψBm q) (hψAb q)
      (hψBb q) hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2
      (fun s => lamf q (dyadicGridLength G s)) (fun s => Mf q (dyadicGridLength G s))
      (fun s => σf q (dyadicGridLength G s)) (fun s => coeff q (dyadicGridLength G s))
      (fun s hs => by
        obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hs
        have h := hprops q (len I) hq (hlen0 I) (Finset.mem_filter.mp hI).2
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩)
    calc _ = ∑ I ∈ S.filter (fun I => ret q (len I)), len I *
          ∑' p, (if p ∈ P then 0 else ‖coeff q (len I) p‖ * ‖sepP I q p‖) := by
          refine Finset.sum_congr rfl fun I hI => ?_
          have hrt := (Finset.mem_filter.mp hI).2
          simp only [hcoeffI, hq, hrt, and_self, ite_true]
      _ ≤ W * (Ka * Kb * Na * Nb) := h.trans (le_of_eq (by rw [hW]; ring))
  calc _ ≤ ∑ q ∈ R, 4 * ‖cf q‖ * (W * (Ka * Kb * Na * Nb)) :=
        Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hpt q hq) (by positivity)
    _ = 4 * (∑ q ∈ R, ‖cf q‖) * (W * (Ka * Kb * Na * Nb)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ 4 * Es * (W * (Ka * Kb * Na * Nb)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hW0 hK)
    _ = (4 * Es * W) * (Ka * Kb * Na * Nb) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (pd_catalog_budget κ (d + e) Dc (DJ 1) Ds Cr (B := B) hH1) hK

private theorem predictor_list_param_catalog_regrouping :
  PredictorListParamCatalogRegroupingStatement := by
  classical
  intro κ Ds Cr Dc DJ d e H B a b h3 τ cf φa φb φt size T₀ Qs R M₀ δ A4 ret E E1 lamf Mf σf coeff
    hprops K₀ P Bσ Mset σset lamℓ νℓ coefℓ hcoefℓ G S w za zb f len hlen0 ψA ψB gam sepP hsepP
    coeffI hcoeffI I hI
  have hr0 : 0 < (len I) := hlen0 I
  have hG := predictor_grouping R Mset σset P (fun q => ret q (len I)) (fun q => Mf q (len I))
    (fun q p => σf q (len I) p) cf (fun q p => coeff q (len I) p)
    (fun q M σ => separatedLocalForm (len I) (w I)
      (fun t => (Real.fourierChar (lamℓ (q, (M, σ)) * t ^ 2) : ℂ)) a b
      (fun y => za I y *
        quadraticChartAtom (modulateQuadraticChart (φa q) (-νℓ (q, (M, σ)))) y)
      (fun y => zb I y *
        quadraticChartAtom (modulateQuadraticChart (φb q) (νℓ (q, (M, σ)))) y))
    (sepP I)
    (fun q hq hrt => Fintype.mem_piFinset.mpr fun i' => Fintype.mem_piFinset.mpr fun j =>
      mem_boundedRationalEnumeration
        (rationalHeight_le_floor ((hprops q (len I) hq hr0 hrt).1 i' j)))
    (fun q hq hrt p hp => Fintype.mem_piFinset.mpr fun j =>
      mem_boundedRationalEnumeration (rationalHeight_le_floor
        (((hprops q (len I) hq hr0 hrt).2.2.2.1 p j).trans (mul_le_mul_of_nonneg_left
          (frequencyTruncationSet_le (Finset.mem_product.mp hp).2)
          (by have := one_le_pdE Dc Ds Cr H B; positivity)))))
    (fun q hq hrt p hp => by
      have hpr := hprops q (len I) hq hr0 hrt
      have hl : lamℓ (q, (Mf q (len I), σf q (len I) p)) = lamf q (len I) := by
        rw [hpr.2.1]
      simp only [hsepP]
      rw [separatedLocalForm_phase_distribute _ _ _ _ h3, hl]
      have hν : νℓ (q, (Mf q (len I), σf q (len I) p)) = gam q (len I) p / ((b : ℝ) - (a :
          ℝ)) := rfl
      rw [hν]
      congr 1
      · funext y; rw [modulateQuadraticChart_atom, neg_mul]; ring
      · funext y; rw [modulateQuadraticChart_atom]; ring)
  have hR' : ∑ q ∈ R, (if ret q (len I) then 4 * cf q * ∑ p ∈ P, coeffI I q p * sepP I q p
      else 0) = ∑ q ∈ R, (if ret q (len I) then 4 * cf q *
        ∑ p ∈ P, coeff q (len I) p * sepP I q p else 0) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    split_ifs with hrt
    · congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hcoeffI, hq, hrt, and_self, ite_true]
    · rfl
  congr 2
  rw [hR', ← hG]
  congr 1
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hq : ℓ.1 ∈ R := (Finset.mem_product.mp hℓ).1
  simp only [hcoefℓ, hq, hr0, true_and]

private theorem predictor_list_param_conclusion_15 : PredictorListParamConclusion15Statement := by
  classical
  -- the coefficient norm
  intro κ Ds Cr Dc DJ d e H B τ cf φt size hcs Es hcsum hEs T₀ Qs R M₀ δ A4 ret E hE E1 lamf Mf σf
    coeff hprops K₀ P Bσ Mset σset coefℓ hcoefℓ r
  have hinner : ∀ q ∈ R, ∑ x ∈ Mset ×ˢ σset, ‖coefℓ (q, x) r‖ ≤ 4 * ‖cf q‖ * E := by
    intro q hq
    by_cases hc : 0 < r ∧ ret q r
    · have hMfix : ∑ x ∈ Mset ×ˢ σset, ‖coefℓ (q, x) r‖ ≤
          ∑ σ ∈ σset, ‖4 * cf q * ∑ p ∈ P.filter (fun p => σf q r p = σ), coeff q r p‖ := by
        rw [Finset.sum_product]
        by_cases hMm : Mf q r ∈ Mset
        · rw [Finset.sum_eq_single (Mf q r)]
          · refine Finset.sum_le_sum fun σ _ => le_of_eq ?_
            simp only [hcoefℓ, hq, hc.1, hc.2, and_self, ite_true]
          · intro M _ hne
            refine Finset.sum_eq_zero fun σ _ => ?_
            simp only [hcoefℓ]
            rw [ite_eq_right (show ¬(q ∈ R ∧ 0 < r ∧ ret q r ∧ Mf q r = M) from
              fun h => hne h.2.2.2.symm), norm_zero]
          · intro h; exact absurd hMm h
        · rw [Finset.sum_eq_zero (fun M hM => Finset.sum_eq_zero fun σ _ => by
              simp only [hcoefℓ]
              rw [ite_eq_right (show ¬(q ∈ R ∧ 0 < r ∧ ret q r ∧ Mf q r = M) from
                fun h => hMm (h.2.2.2 ▸ hM)), norm_zero])]
          exact Finset.sum_nonneg fun _ _ => norm_nonneg _
      refine hMfix.trans ?_
      have hpsum : ∑ p ∈ P, ‖coeff q r p‖ ≤ E :=
        ((hprops q r hq hc.1 hc.2).2.2.2.2.2.1.sum_le_tsum P
          (fun _ _ => norm_nonneg _)).trans (hprops q r hq hc.1 hc.2).2.2.2.2.2.2.1
      calc ∑ σ ∈ σset, ‖4 * cf q * ∑ p ∈ P.filter (fun p => σf q r p = σ), coeff q r p‖
          ≤ ∑ σ ∈ σset, 4 * ‖cf q‖ * ∑ p ∈ P.filter (fun p => σf q r p = σ),
              ‖coeff q r p‖ := by
            refine Finset.sum_le_sum fun σ _ => ?_
            rw [norm_mul, norm_mul]
            have : ‖(4 : ℂ)‖ = 4 := by norm_num
            rw [this]
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ = 4 * ‖cf q‖ * ∑ p ∈ P.filter (fun p => σf q r p ∈ σset), ‖coeff q r p‖ := by
            rw [← Finset.mul_sum]
            congr 1
            rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => σf q r p) (t := σset)
              (fun p hp => (Finset.mem_filter.mp hp).2)]
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [Finset.filter_filter]
            congr 1
            ext p
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hp, rfl⟩; exact ⟨hp, ⟨‹_›, rfl⟩⟩
            · rintro ⟨hp, -, h⟩; exact ⟨hp, h⟩
        _ ≤ 4 * ‖cf q‖ * ∑ p ∈ P, ‖coeff q r p‖ :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)) (by positivity)
        _ ≤ 4 * ‖cf q‖ * E := mul_le_mul_of_nonneg_left hpsum (by positivity)
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun x _ => ?_)) (by
        have := one_le_pdE Dc Ds Cr H B; positivity)
      simp only [hcoefℓ]
      rw [ite_eq_right (show ¬(q ∈ R ∧ 0 < r ∧ ret q r ∧ Mf q r = x.1) from
        fun h => hc ⟨h.2.1, h.2.2.1⟩), norm_zero]
  rw [Finset.sum_product]
  calc ∑ q ∈ R, ∑ x ∈ Mset ×ˢ σset, ‖coefℓ (q, x) r‖
      ≤ ∑ q ∈ R, 4 * ‖cf q‖ * E := Finset.sum_le_sum hinner
    _ = 4 * E * ∑ q ∈ R, ‖cf q‖ := by rw [Finset.mul_sum]; congr 1; funext q; ring
    _ ≤ 4 * E * Es := by
        refine mul_le_mul_of_nonneg_left ((hcs.sum_le_tsum R (fun _ _ => norm_nonneg _)).trans
          hcsum) (by have := one_le_pdE Dc Ds Cr H B; positivity)
    _ = 4 * pdEs Ds H * pdE Dc Ds Cr H B := by rw [hE, hEs]; ring

private theorem predictor_list_param_conclusion_17 : PredictorListParamConclusion17Statement := by
  classical
  -- the error bound
  intro κ c₁ Ds Cr hCr Dc DJ d e H B A A' hd he a i k b h1 h2 h3 h4 h5 h6 hH1 τ hτc cf φa φb φt
    size hexpS hbdd hsize1 hcs Es hcomp htail hcsum hEs T₀ hT₀1 Qs R hnotR H₀ hH₀1 hcompR M₀ δ hδ
    A4 ret hret E E1 hE1d lamf Mf σf coeff hprops K₀ P Bσ Mset σset lamℓ νℓ coefℓ hcoefℓ G J S hSJ
    w hw Fa Fb za zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 f hfa hfi hfk hfb
  have := hτc
  have hde : 1 ≤ d + e := by omega
  set! len : ℤ × ℤ → ℝ := fun I => dyadicGridLength G I.1 with hlen
  have hlen0 : ∀ I, 0 < len I := fun I => dyadicGridLength_pos G I.1
  set Na := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) with hNa
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) with hNb
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  set! ψA : τ → ℝ → ℂ := fun q => quadraticChartAtom (φa q) with hψA
  set! ψB : τ → ℝ → ℂ := fun q => quadraticChartAtom (φb q) with hψB
  set! Qt : τ → ℝ → ℂ := fun q => quadraticChartAtom (φt q) with hQt
  have hψAm : ∀ q, Measurable (ψA q) := fun q => quadraticChartAtom_measurable _
  have hψBm : ∀ q, Measurable (ψB q) := fun q => quadraticChartAtom_measurable _
  have hQtm : ∀ q, Measurable (Qt q) := fun q => quadraticChartAtom_measurable _
  have hψAb : ∀ q y, ‖ψA q y‖ ≤ 1 := fun q y => (hbdd q).1 y
  have hψBb : ∀ q y, ‖ψB q y‖ ≤ 1 := fun q y => (hbdd q).2.1 y
  have hQtb : ∀ q y, ‖Qt q y‖ ≤ 1 := fun q y => (hbdd q).2.2 y
  have hexpR : ∀ x t : ℝ, HasSum (fun q => cf q * ψA q (x + (a : ℝ) * t) *
      ψB q (x + (b : ℝ) * t) * Qt q t)
      (quadraticChartAtom A (x + (i : ℝ) * t) * quadraticChartAtom A' (x + (k : ℝ) * t)) := by
    intro x t
    have h := hexpS x t
    simpa only [Int.cast_natCast] using h
  -- the separated forms of the separation terms and of the catalog terms
  set! sepQ : ℤ × ℤ → τ → ℂ := fun I q => separatedLocalForm (len I) (w I) (Qt q) a b
    (fun y => ψA q y * za I y) (fun y => ψB q y * zb I y) with hsepQ
  set! gam : τ → ℝ → ℕ × (Fin ((d + e) + (d + e)) → ℤ) → ℝ := fun q r p =>
    (φt q).linear + ∑ j, (σf q r p j : ℝ) * (φt q).horizontal j with hgam
  set! sepP : ℤ × ℤ → τ → ℕ × (Fin ((d + e) + (d + e)) → ℤ) → ℂ := fun I q p =>
    separatedLocalForm (len I) (w I) (quadPhase (lamf q (len I)) (gam q (len I) p)) a b
      (fun y => ψA q y * za I y) (fun y => ψB q y * zb I y) with hsepP
  set! coeffI : ℤ × ℤ → τ → ℕ × (Fin ((d + e) + (d + e)) → ℤ) → ℂ := fun I q p =>
    if q ∈ R ∧ ret q (len I) then coeff q (len I) p else 0 with hcoeffI
  have hcell : ∀ I, ∃ M : ℝ, I ∈ S → HasSum (fun q => cf q * sepQ I q)
      (localProgressionForm (len I) (w I) (f I)) ∧ ∀ q, ‖sepQ I q‖ ≤ M := by
    intro I
    by_cases hI : I ∈ S
    · obtain ⟨M, hM1, hM2⟩ := pair_expansion_cell (hlen0 I) (hw I hI) h1 h2 h3 h4 h5 h6
        (hzam I) (hzbm I) (hza2 I) (hzb2 I) cf ψA ψB Qt hψAm hψBm hQtm hψAb hψBb hQtb hcs
        hexpR (f I) (hfa I) (hfi I) (hfk I) (hfb I)
      exact ⟨M, fun _ => ⟨hM1, hM2⟩⟩
    · exact ⟨0, fun h => absurd h hI⟩
  choose MQ hMQ using hcell
  set! MP : ℤ × ℤ → ℝ := fun I => localKernelSupBound κ *
    Real.sqrt ((len I)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
      (dyadicGridLeft G I.1 I.2 + len I), ‖za I y‖ ^ 2) *
    Real.sqrt ((len I)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
      (dyadicGridLeft G I.1 I.2 + len I), ‖zb I y‖ ^ 2) with hMP
  have hsepPb : ∀ I ∈ S, ∀ q p, ‖sepP I q p‖ ≤ MP I := fun I hI q p =>
    separatedLocalForm_bounded_le (hlen0 I) (hw I hI) h3
      (fun t => (norm_quadPhase _ _ t).le) (hψAm q) (hψBm q) (hψAb q) (hψBb q) (hzam I)
      (hzbm I) (hza2 I) (hzb2 I)
  have hcoeffs : ∀ I q, Summable (fun p => ‖coeffI I q p‖) := by
    intro I q
    simp only [hcoeffI]
    split_ifs with h
    · exact (hprops q (len I) h.1 (hlen0 I) h.2).2.2.2.2.2.1
    · simp
  have hexpI : ∀ I ∈ S, ∀ q ∈ R, ret q (len I) → HasSum (fun p => coeffI I q p * sepP I q p)
      (sepQ I q / 4) := by
    intro I hI q hq hrt
    have hpr := hprops q (len I) hq (hlen0 I) hrt
    have h := separatedLocalForm_hasSum (hlen0 I) (hw I hI) h3 (coeff q (len I))
      (fun p => quadPhase (lamf q (len I)) (gam q (len I) p))
      (fun p => measurable_quadPhase _ _) (fun p t => (norm_quadPhase _ _ t).le)
      hpr.2.2.2.2.2.1 (Q := quadraticChartAtom (A4 q))
      (fun t ht => hpr.2.2.2.2.1 t (by linarith [(hlen0 I).le]))
      ((hψAm q).mul (hzam I)) ((hψBm q).mul (hzbm I))
      (memLp_mul_bounded_restrict (hψAm q) (hψAb q) (hza2 I))
      (memLp_mul_bounded_restrict (hψBm q) (hψBb q) (hzb2 I))
    have hA4e : quadraticChartAtom (A4 q) = fun t => (1 / 4 : ℂ) * Qt q t :=
      funext fun t => scaleQuadraticChartAmplitude_atom _ _ _
    rw [hA4e, separatedLocalForm_const_mul] at h
    have hc : ∀ p, coeffI I q p = coeff q (len I) p := fun p => by
      simp only [hcoeffI, hq, hrt, and_self, ite_true]
    simp only [hc]
    convert h using 1
    rw [mul_comm, div_eq_mul_one_div]; rfl
  -- regroup the list into the retained catalog terms
  have hrw : ∀ I ∈ S, len I * ‖localProgressionForm (len I) (w I) (f I) -
      ∑ ℓ ∈ R ×ˢ (Mset ×ˢ σset), coefℓ ℓ (len I) *
        separatedLocalForm (len I) (w I)
          (fun t => (Real.fourierChar (lamℓ ℓ * t ^ 2) : ℂ)) a b
          (fun y => za I y * quadraticChartAtom (modulateQuadraticChart (φa ℓ.1) (-νℓ ℓ)) y)
          (fun y => zb I y * quadraticChartAtom (modulateQuadraticChart (φb ℓ.1) (νℓ ℓ)) y)‖ =
      len I * ‖localProgressionForm (len I) (w I) (f I) - ∑ q ∈ R,
        (if ret q (len I) then 4 * cf q * ∑ p ∈ P, coeffI I q p * sepP I q p else 0)‖ := by
    expose_names
    exact @predictor_list_param_catalog_regrouping κ Ds Cr Dc DJ d e H B a b h3 τ cf φa φb φt
      size Qs lamf Mf σf coeff hprops hcoefℓ G S w za zb f hlen0 hsepP hcoeffI
  refine le_trans (le_of_eq (Finset.sum_congr rfl hrw)) ?_
  refine (predictor_sum_bound S len (fun I => (hlen0 I).le) cf hcs
    (fun I => localProgressionForm (len I) (w I) (f I)) sepQ MQ
    (fun I hI => (hMQ I hI).2) (fun I hI => (hMQ I hI).1) R (fun q I => ret q (len I)) P
    coeffI sepP hcoeffs MP hsepPb hexpI).trans ?_
  -- the three error terms
  have hsumR : ∑ q ∈ R, ‖cf q‖ ≤ Es :=
    (hcs.sum_le_tsum R (fun _ _ => norm_nonneg _)).trans hcsum
  have hsep0 : ∀ q (S' : Finset (ℤ × ℤ)), 0 ≤ ∑ I ∈ S', len I * ‖sepQ I q‖ := fun q S' =>
    Finset.sum_nonneg fun I _ => mul_nonneg (hlen0 I).le (norm_nonneg _)
  -- the discarded separation shells
  set! c := (Cr : ℝ) * pdA0 Ds H ^ Cr * (1 + 6 * Cr) ^ Cr with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by
    linarith [one_le_pdA0 (Ds := Ds) hH1]) _)) (by positivity)
  obtain ⟨hgs, hgle⟩ := weighted_shell_tail cf size (by linarith [one_le_pdEs (Ds := Ds) hH1])
    htail hcs hT₀1
  have hT1pt : ∀ q, (if q ∈ R then 0 else ‖cf q‖ * ∑ I ∈ S, len I * ‖sepQ I q‖) ≤
      c * (Ka * Kb * Na * Nb) * (if T₀ < size q then ‖cf q‖ * size q else 0) := by
    intro q
    by_cases hq : q ∈ R
    · simp only [hq, ite_true]
      refine mul_nonneg (mul_nonneg hc0 hK) ?_
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (by linarith [hsize1 q])
      · exact le_rfl
    · have hT := hnotR q hq
      simp only [hq, ite_false, hT, ite_true]
      have hs1 := hsize1 q
      have hband : ∀ I ∈ S, bandSup (quadraticChartAtom
          (scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q))) (dyadicGridLength G I.1) ≤
          Real.exp (-((0 : ℕ) : ℝ)) := fun I _ =>
        (bandSup_le (quarterChart_norm_le (hbdd q).2.2) _).trans (by norm_num)
      have h := hCr ((Es * size q) ^ 6) (φt q) hde (hcomp q).2.2 (hbdd q).2.2 0 G J S hSJ w hw
        h3 (hψAm q) (hψBm q) (hψAb q) (hψBb q) hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2
        hband
      have hl := pd_shell_log Ds (H := H) hs1
      rw [← hEs] at hl
      rw [hl, Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, one_mul] at h
      have hlw := log_weight_le (one_le_pdA0 (Ds := Ds) hH1) hs1 Cr
      calc ‖cf q‖ * ∑ I ∈ S, len I * ‖sepQ I q‖
          ≤ ‖cf q‖ * ((Cr : ℝ) * (pdA0 Ds H + 6 * Real.log (size q)) ^ Cr *
              (Ka * Kb * Na * Nb)) :=
            mul_le_mul_of_nonneg_left (h.trans (le_of_eq (by ring))) (norm_nonneg _)
        _ ≤ ‖cf q‖ * ((Cr : ℝ) * (pdA0 Ds H ^ Cr * (1 + 6 * Cr) ^ Cr * size q) *
              (Ka * Kb * Na * Nb)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlw (Nat.cast_nonneg _)) hK) (norm_nonneg _)
        _ = c * (Ka * Kb * Na * Nb) * (‖cf q‖ * size q) := by rw [hc]; ring
  have hT1 : (∑' q, if q ∈ R then 0 else ‖cf q‖ * ∑ I ∈ S, len I * ‖sepQ I q‖) ≤
      Real.exp (-B) / 3 * (Ka * Kb * Na * Nb) := by
    have hsum2 := hgs.mul_left (c * (Ka * Kb * Na * Nb))
    have hsum1 : Summable (fun q => if q ∈ R then 0 else
        ‖cf q‖ * ∑ I ∈ S, len I * ‖sepQ I q‖) :=
      Summable.of_nonneg_of_le (fun q => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (norm_nonneg _) (hsep0 q S)) hT1pt hsum2
    calc _ ≤ ∑' q, c * (Ka * Kb * Na * Nb) *
          (if T₀ < size q then ‖cf q‖ * size q else 0) := hsum1.tsum_le_tsum hT1pt hsum2
      _ = c * (Ka * Kb * Na * Nb) *
          ∑' q, (if T₀ < size q then ‖cf q‖ * size q else 0) := tsum_mul_left
      _ ≤ c * (Ka * Kb * Na * Nb) * (4 * Es / T₀ ^ 99) :=
          mul_le_mul_of_nonneg_left hgle (mul_nonneg hc0 hK)
      _ = (c * (4 * Es / T₀ ^ 99)) * (Ka * Kb * Na * Nb) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (pd_shell_budget (Ds := Ds) (Cr := Cr) (B := B) hH1) hK
  -- the discarded bands
  have hT2 : ∑ q ∈ R, ‖cf q‖ * ∑ I ∈ S.filter (fun I => ¬ ret q (len I)),
      len I * ‖sepQ I q‖ ≤ Real.exp (-B) / 3 * (Ka * Kb * Na * Nb) := by
    set! Z := Real.exp (-(M₀ : ℝ) / 2) * (Cr * (2 + Real.log H₀) ^ Cr) with hZ
    have hZ0 : 0 ≤ Z := by have := Real.log_nonneg hH₀1; positivity
    have hpt : ∀ q ∈ R, ∑ I ∈ S.filter (fun I => ¬ ret q (len I)), len I * ‖sepQ I q‖ ≤
        Z * (Ka * Kb * Na * Nb) := by
      intro q hq
      have hband : ∀ I ∈ S.filter (fun I => ¬ ret q (len I)), bandSup (quadraticChartAtom
          (scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt q))) (dyadicGridLength G I.1) ≤
          Real.exp (-(M₀ : ℝ)) := by
        intro I hI
        have hn := (Finset.mem_filter.mp hI).2
        simp only [hret, not_lt] at hn
        refine hn.trans ?_
        rw [hδ]; exact Real.exp_le_exp.mpr (by linarith)
      have h := hCr H₀ (φt q) hde (hcompR q hq).1 (hbdd q).2.2 M₀ G J
        (S.filter (fun I => ¬ ret q (len I))) (fun I hI => hSJ I (Finset.mem_filter.mp hI).1)
        w (fun I hI => hw I (Finset.mem_filter.mp hI).1) h3 (hψAm q) (hψBm q) (hψAb q)
        (hψBb q) hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 hband
      exact h.trans (le_of_eq (by rw [hZ]; ring))
    calc _ ≤ ∑ q ∈ R, ‖cf q‖ * (Z * (Ka * Kb * Na * Nb)) :=
          Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hpt q hq) (norm_nonneg _)
      _ = (∑ q ∈ R, ‖cf q‖) * (Z * (Ka * Kb * Na * Nb)) := (Finset.sum_mul _ _ _).symm
      _ ≤ Es * (Z * (Ka * Kb * Na * Nb)) :=
          mul_le_mul_of_nonneg_right hsumR (mul_nonneg hZ0 hK)
      _ = (Es * Z) * (Ka * Kb * Na * Nb) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (pd_band_budget (Ds := Ds) (Cr := Cr) (B := B) hH1) hK
  -- the catalog tails
  have hE10 : 0 ≤ E1 := by rw [hE1d, pdE1]; positivity
  have hT3 : ∑ q ∈ R, 4 * ‖cf q‖ * ∑ I ∈ S.filter (fun I => ret q (len I)), len I *
      ∑' p, (if p ∈ P then 0 else ‖coeffI I q p‖ * ‖sepP I q p‖) ≤
      Real.exp (-B) / 3 * (Ka * Kb * Na * Nb) := by
    expose_names
    exact @predictor_list_param_catalog_tail_bound κ Ds Cr Dc DJ d e H B a b h3 hH1 τ cf φa φb
      φt size Qs lamf Mf σf coeff hprops G J S hSJ w hw Fa Fb za zb Ka Kb hKa hKb hza hzb hEa
      hEb hzam hzbm hza2 hzb2 hde hlen0 hK hψAm hψBm hψAb hψBb hcoeffI hsumR hE10
  refine (add_le_add (add_le_add hT1 hT2) hT3).trans (le_of_eq ?_)
  ring

private theorem predictor_list_param_stage_1 : PredictorListParamStage1Statement := by
  classical
  intro κ c₁ Ds Cr hCr Dc DJ d e H B A A' hd he a i k b h1 h2 h3 h4 h5 h6 hH1 τ hτc cf φa φb φt
    size hexpS hbdd hsize1 hcs Es hcomp htail hcsum hEs T₀ hT₀ hT₀1 Qs hQscard R hR hnotR H₀ hH₀1
    hcompR M₀ δ hδ A4 ret hret E hE E1 hE1d lamf Mf σf coeff hprops K₀ hK₀
  let P : Finset (ℕ × (Fin (d + e + (d + e)) → ℤ)) :=
    Finset.range ⌊E⌋₊ ×ˢ frequencyTruncationSet (d + e + (d + e)) K₀
  intro Bσ hBσ Mset hMset
  set! σset : Finset (Fin (d + e) → ℚ) :=
    Fintype.piFinset (fun _ => boundedRationalEnumeration ⌊Bσ⌋₊) with hσset
  set! lamℓ : τ × (Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) → ℝ := fun ℓ =>
    (φt ℓ.1).quadratic + ∑ i, ∑ j, (φt ℓ.1).horizontal i * (ℓ.2.1 i j : ℝ) *
      (φt ℓ.1).horizontal j with hlamℓ
  set! νℓ : τ × (Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) → ℝ := fun ℓ =>
    ((φt ℓ.1).linear + ∑ i, (ℓ.2.2 i : ℝ) * (φt ℓ.1).horizontal i) / ((b : ℝ) - (a : ℝ))
    with hνℓ
  set! coefℓ : τ × (Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)) → ℝ → ℂ :=
    fun ℓ r => if ℓ.1 ∈ R ∧ 0 < r ∧ ret ℓ.1 r ∧ Mf ℓ.1 r = ℓ.2.1 then
      4 * cf ℓ.1 * ∑ p ∈ P.filter (fun p => σf ℓ.1 r p = ℓ.2.2), coeff ℓ.1 r p else 0
    with hcoefℓ
  refine ⟨τ × (Matrix (Fin (d + e)) (Fin (d + e)) ℚ × (Fin (d + e) → ℚ)),
    R ×ˢ (Mset ×ˢ σset), fun ℓ => modulateQuadraticChart (φa ℓ.1) (-νℓ ℓ),
    fun ℓ => modulateQuadraticChart (φb ℓ.1) (νℓ ℓ), lamℓ, coefℓ, ?_, ?_, ?_, ?_, ?_⟩
  · expose_names
    exact @predictor_list_param_conclusion_13 κ Ds Cr Dc DJ d e H B τ size hT₀ hT₀1 Qs hQscard hR
      hE hK₀ hBσ hMset hσset
  · -- bounded atoms of controlled complexity
    intro ℓ hℓ
    have hq : ℓ.1 ∈ R := (Finset.mem_product.mp hℓ).1
    exact ⟨modulateQuadraticChart_bounded (hbdd ℓ.1).1 _,
      modulateQuadraticChart_bounded (hbdd ℓ.1).2.1 _,
      modulateQuadraticChart_complexity (hcompR ℓ.1 hq).2.1 _,
      modulateQuadraticChart_complexity (hcompR ℓ.1 hq).2.2 _⟩
  · expose_names
    exact @predictor_list_param_conclusion_15 κ Ds Cr Dc DJ d e H B τ cf φt size hcs hcsum hEs Qs
      hE lamf Mf σf coeff hprops hcoefℓ
  · -- quadratic size of the used terms
    intro ℓ r hne
    simp only [hcoefℓ] at hne
    split_ifs at hne with hcond
    · obtain ⟨hq, hr, hrt, hM⟩ := hcond
      have hl := (hprops ℓ.1 r hq hr hrt).2.1
      have hlamℓeq : lamℓ ℓ = lamf ℓ.1 r := by
        rw [hl]; simp only [hlamℓ, hM]
      rw [hlamℓeq]
      exact (hprops ℓ.1 r hq hr hrt).2.2.1
    · exact absurd rfl hne
  · expose_names
    exact @predictor_list_param_conclusion_17 κ c₁ Ds Cr hCr Dc DJ d e H B A A' hd he a i k b
      h1 h2 h3 h4 h5 h6 hH1 τ hτc cf φa φb φt size hexpS hbdd hsize1 hcs hcomp htail
      hcsum hEs hT₀1 Qs hnotR hH₀1 hcompR hδ hret hE1d lamf Mf σf coeff hprops hcoefℓ

/-- Blueprint lem:predictors, `eq:predictors` with explicit parameters: the product of two
fixed bounded atoms in slots `i, k` of the local form is replaced by a finite list of terms
`ψ_a(y_a) ψ_b(y_b) w_I(x,t) e(λ_* t²)` with scale-dependent coefficients, with absolute
length-weighted error at most `e^{-B} K_a K_b ‖1_J F_a‖ ‖1_J F_b‖`. -/
theorem predictor_list_param (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ c₁ Ds Cr Dc J1 : ℕ, 1 ≤ c₁ ∧ ∀ {d e : ℕ} (H B : ℝ) (A : QuadraticChartData d)
      (A' : QuadraticChartData e), 1 ≤ d → 1 ≤ e → QuadraticChartComplexity c₀ H A →
      QuadraticChartComplexity c₀ H A' → IsBoundedQuadraticChart A →
      IsBoundedQuadraticChart A' → 1 ≤ B →
      ∀ {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
      ∃ (ι : Type) (L : Finset ι) (ψa ψb : ι → QuadraticChartData (d + e)) (lam : ι → ℝ)
        (coef : ι → ℝ → ℂ),
        (L.card : ℝ) ≤ pdCard κ (d + e) Dc J1 Ds Cr H B ∧
        (∀ ℓ ∈ L, IsBoundedQuadraticChart (ψa ℓ) ∧ IsBoundedQuadraticChart (ψb ℓ) ∧
          QuadraticChartComplexity c₁ (pdH0 Ds Cr H B) (ψa ℓ) ∧
          QuadraticChartComplexity c₁ (pdH0 Ds Cr H B) (ψb ℓ)) ∧
        (∀ r, ∑ ℓ ∈ L, ‖coef ℓ r‖ ≤ 4 * pdEs Ds H * pdE Dc Ds Cr H B) ∧
        (∀ ℓ r, coef ℓ r ≠ 0 → |lam ℓ| * r ^ 2 ≤ pdE Dc Ds Cr H B) ∧
        ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
        (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) →
        ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
          (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
        ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, 0 ≤ Ka → 0 ≤ Kb →
        IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
        HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb →
        (∀ I, Measurable (za I)) → (∀ I, Measurable (zb I)) →
        (∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
        (∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
        ∀ (f : ℤ × ℤ → Fin 4 → ℝ → ℂ), (∀ I, f I a = za I) →
        (∀ I, f I i = quadraticChartAtom A) → (∀ I, f I k = quadraticChartAtom A') →
        (∀ I, f I b = zb I) →
        ∑ I ∈ S, dyadicGridLength G I.1 *
          ‖localProgressionForm (dyadicGridLength G I.1) (w I) (f I) -
            ∑ ℓ ∈ L, coef ℓ (dyadicGridLength G I.1) *
              separatedLocalForm (dyadicGridLength G I.1) (w I)
                (fun t => (Real.fourierChar (lam ℓ * t ^ 2) : ℂ)) a b
                (fun y => za I y * quadraticChartAtom (ψa ℓ) y)
                (fun y => zb I y * quadraticChartAtom (ψb ℓ) y)‖ ≤
          Real.exp (-B) * Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
            Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  obtain ⟨c₁, Ds, hc₁, hDs, hsep⟩ := progressionSeparation c₀ hc
  obtain ⟨Cr, hCr⟩ := chart_band_range_scale_sum c₁ hc₁ κ
  obtain ⟨Dc, hDc, DJ, hexpand⟩ := chart_depth_expansion c₁ hc₁
  refine ⟨c₁, Ds, Cr, Dc, DJ 1, hc₁, ?_⟩
  intro d e H B A A' hd he hA hA' hAb hA'b hB a i k b h1 h2 h3 h4 h5 h6
  classical
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hB0 : 0 ≤ B := by linarith
  -- the separation of the atom pair
  have hab : ((a : ℕ) : ℤ) ≠ ((b : ℕ) : ℤ) := by
    intro h; apply h3; exact Fin.ext (by exact_mod_cast h)
  obtain ⟨τ, hτc, cf, φa, φb, φt, size, hexpS, hbdd, hsize1, hcs, hcsum, htail, hcomp, hcount,
    -⟩ :=
    hsep H A A' hd he hA hA' ((i : ℕ) : ℤ) ((k : ℕ) : ℤ) ((a : ℕ) : ℤ) ((b : ℕ) : ℤ) hab
      (abs_fin_int_le i) (abs_fin_int_le k) (abs_fin_int_le a) (abs_fin_int_le b)
  set Es := pdEs Ds H with hEs
  have hEsdef : Real.exp (Ds * (1 + Real.log H) ^ Ds) = Es := by rw [hEs, pdEs, pdX]
  rw [hEsdef] at hcsum htail hcomp
  set! T₀ := pdT0 Ds Cr H B with hT₀
  have hT₀1 : 1 ≤ T₀ := one_le_pdT0 hH1
  obtain ⟨Qs, hQs, hQscard⟩ := hcount T₀ hT₀1
  set! R := Qs.filter (fun q => size q ≤ T₀) with hR
  have hnotR : ∀ q, q ∉ R → T₀ < size q := by
    intro q hq
    by_contra hle
    push Not at hle
    exact hq (Finset.mem_filter.mpr ⟨hQs q hle, hle⟩)
  set H₀ := pdH0 Ds Cr H B with hH₀
  have hH₀1 : 1 ≤ H₀ := one_le_pdH0
  have hcompR : ∀ q ∈ R, QuadraticChartComplexity c₁ H₀ (φt q) ∧
      QuadraticChartComplexity c₁ H₀ (φa q) ∧ QuadraticChartComplexity c₁ H₀ (φb q) := by
    intro q hq
    have hs := (Finset.mem_filter.mp hq).2
    have hle : (Es * size q) ^ 6 ≤ H₀ := by
      rw [hH₀, pdH0]
      refine le_trans ?_ (le_max_left _ _)
      have := hsize1 q
      have hE1 : 1 ≤ Es := one_le_pdEs hH1
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hs (by linarith)) 6
    exact ⟨quadraticChartComplexity_mono (hcomp q).2.2 hle,
      quadraticChartComplexity_mono (hcomp q).1 hle,
      quadraticChartComplexity_mono (hcomp q).2.1 hle⟩
  -- the band precision and the retained scales
  set! M₀ := pdM0 Ds Cr H B with hM₀
  set! δ := Real.exp (-((M₀ : ℝ) + 1)) with hδ
  have hδ0 : 0 < δ := Real.exp_pos _
  have hlogδ : Real.log (max 1 δ⁻¹) = (M₀ : ℝ) + 1 := by
    rw [hδ, ← Real.exp_neg, neg_neg, max_eq_right (Real.one_le_exp (by positivity)),
      Real.log_exp]
  have hLE : 1 + Real.log H₀ + Real.log (max 1 δ⁻¹) = pdLE Ds Cr H B := by
    rw [hlogδ, pdLE, hH₀]; ring
  set! A4 : τ → QuadraticChartData (d + e) := fun q => scaleQuadraticChartAmplitude (1 / 4 : ℂ) (φt
      q)
    with hA4
  have hA4c : ∀ q ∈ R, QuadraticChartComplexity c₁ H₀ (A4 q) := fun q hq =>
    scaleQuadraticChartAmplitude_complexity (hcompR q hq).1 (by norm_num)
  have hA4b : ∀ q t, ‖quadraticChartAtom (A4 q) t‖ ≤ 1 / 4 := fun q t =>
    quarterChart_norm_le (hbdd q).2.2 t
  set! ret : τ → ℝ → Prop := fun q r => δ < bandSup (quadraticChartAtom (A4 q)) r with hret
  have hζb : ∀ u, ‖(bandCutoff u : ℂ)‖ ≤ H₀ := fun u => by
    rw [Complex.norm_real, Real.norm_of_nonneg (bandCutoff_spec.2.1 u)]
    exact (bandCutoff_spec.2.2.1 u).trans hH₀1
  have hζL : ∀ u v, ‖(bandCutoff v : ℂ) - (bandCutoff u : ℂ)‖ ≤ H₀ * |v - u| := by
    intro u v
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (bandLip_spec.2 u v).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    rw [hH₀, pdH0]; exact (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  -- the per-(term, scale) chart expansions
  set E := pdE Dc Ds Cr H B with hE
  set! E1 := pdE1 (DJ 1) Ds Cr H B with hE1d
  have hEdef : Real.exp (Dc * (1 + Real.log H₀ + Real.log (max 1 δ⁻¹)) ^ Dc) = E := by
    rw [hLE, hE, pdE]
  have hE1def : Real.exp ((DJ 1 : ℕ) * (1 + Real.log H₀ + Real.log (max 1 δ⁻¹)) ^ (DJ 1)) =
      E1 := by rw [hLE, hE1d, pdE1]
  have hexpq : ∀ (q : τ) (r : ℝ), ∃ (lam : ℝ) (M : Matrix (Fin (d + e)) (Fin (d + e)) ℚ)
      (σ : ℕ × (Fin ((d + e) + (d + e)) → ℤ) → Fin (d + e) → ℚ)
      (coef : ℕ × (Fin ((d + e) + (d + e)) → ℤ) → ℂ),
      q ∈ R → 0 < r → ret q r →
        (∀ i j, (rationalHeight (M i j) : ℝ) ≤ E) ∧
        lam = (φt q).quadratic + ∑ i, ∑ j, (φt q).horizontal i * (M i j : ℝ) *
          (φt q).horizontal j ∧
        |lam| * r ^ 2 ≤ E ∧
        (∀ p i, (rationalHeight (σ p i) : ℝ) ≤ E * (1 + frequencyLength p.2)) ∧
        (∀ t, |t| ≤ 2 * r → HasSum (fun p => coef p *
          quadPhase lam ((φt q).linear + ∑ i, (σ p i : ℝ) * (φt q).horizontal i) t)
            (quadraticChartAtom (A4 q) t)) ∧
        Summable (fun p => ‖coef p‖) ∧ (∑' p, ‖coef p‖) ≤ E ∧
        (∀ p, ⌊E⌋₊ ≤ p.1 → coef p = 0) ∧
        ∀ p, ‖coef p‖ * (1 + frequencyLength p.2) ^ ((d + e + 1) ^ 2) ≤ E1 := by
    intro q r
    by_cases hall : q ∈ R ∧ 0 < r ∧ ret q r
    · obtain ⟨hqR, hr, hret'⟩ := hall
      have hlow : ∃ ξ, δ < bandAmplitude (quadraticChartAtom (A4 q)) r ξ := by
        obtain ⟨ξ, hξ⟩ := exists_lt_of_lt_ciSup hret'
        exact ⟨ξ, hξ⟩
      obtain ⟨lam, M, σ, coef, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
        hexpand H₀ δ r (A4 q) (hA4c q hqR) hr hδ0 hζb hζL hlow
      rw [hEdef] at g1 g3 g4 g7 g8
      rw [hE1def] at g9
      exact ⟨lam, M, σ, coef, fun _ _ _ => ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩⟩
    · exact ⟨0, 0, 0, 0, fun hq hr hrt => absurd ⟨hq, hr, hrt⟩ hall⟩
  choose lamf Mf σf coeff hprops using hexpq
  -- the catalog and the list
  set! K₀ := pdK0 κ (d + e) Dc (DJ 1) Ds Cr H B with hK₀
  set! P : Finset (ℕ × (Fin ((d + e) + (d + e)) → ℤ)) :=
    (Finset.range ⌊E⌋₊) ×ˢ frequencyTruncationSet ((d + e) + (d + e)) K₀ with hP
  set! Bσ := E * 2 ^ K₀ with hBσ
  set! Mset : Finset (Matrix (Fin (d + e)) (Fin (d + e)) ℚ) :=
    Fintype.piFinset (fun _ => Fintype.piFinset (fun _ => boundedRationalEnumeration ⌊E⌋₊))
    with hMset
  expose_names
  exact @predictor_list_param_stage_1 κ c₁ Ds Cr hCr Dc DJ d e H B A A' hd he a i k b h1 h2 h3
      h4 h5 h6 hH1 τ hτc cf φa φb φt size hexpS hbdd hsize1 hcs hcomp htail hcsum hEs hT₀
      hT₀1 Qs hQscard hR hnotR hH₀1 hcompR hδ hret hE hE1d lamf Mf σf coeff hprops hK₀ hBσ
      hMset

/-! ### The quasipolynomial size of the predictor budget -/

theorem qple_poly {Y a : ℝ} {K : ℕ} (h : a ≤ K * Y ^ K) : QPLe Y K a := by
  unfold QPLe; linarith [Real.add_one_le_exp ((K : ℝ) * Y ^ K)]

theorem qple_exp {Y x : ℝ} {K : ℕ} (h : x ≤ K * Y ^ K) : QPLe Y K (Real.exp x) :=
  Real.exp_le_exp.mpr h

theorem qple_add {Y a b : ℝ} {K : ℕ} (hY : 1 ≤ Y) (ha : QPLe Y K a) (hb : QPLe Y K b) :
    QPLe Y (K + 1) (a + b) := by
  unfold QPLe at *
  have hY0 : 0 ≤ Y := by linarith
  have hx : 1 ≤ Real.exp (K * Y ^ K) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hY0 _))
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h2 : a + b ≤ Real.exp 1 * Real.exp (K * Y ^ K) :=
    calc a + b ≤ 2 * Real.exp (K * Y ^ K) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right he (by linarith)
  refine h2.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : Y ^ K ≤ Y ^ (K + 1) := pow_le_pow_right₀ hY (by omega)
  have h3 : 1 ≤ Y ^ (K + 1) := one_le_pow₀ hY
  have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) K)
  push_cast
  linarith

theorem qple_add_one {Y a : ℝ} {K : ℕ} (hY : 1 ≤ Y) (ha : QPLe Y K a) :
    QPLe Y (K + 1) (a + 1) :=
  qple_add hY ha (QPLe.one_le hY)

/-- Variable powers `a^n` with `n ≤ m Y^j`. -/
theorem qple_pow_var {Y a : ℝ} {K m j n : ℕ} (hY : 1 ≤ Y) (ha0 : 0 ≤ a) (ha : QPLe Y K a)
    (hn : (n : ℝ) ≤ m * Y ^ j) : QPLe Y (m * K + K + j) (a ^ n) := by
  unfold QPLe at *
  refine (pow_le_pow_left₀ ha0 ha n).trans ?_
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hY0 : 0 ≤ Y := by linarith
  have hKY : 0 ≤ (K : ℝ) * Y ^ K := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hY0 _)
  have h1 : (n : ℝ) * (K * Y ^ K) ≤ m * Y ^ j * (K * Y ^ K) :=
    mul_le_mul_of_nonneg_right hn hKY
  have h2 : Y ^ j * Y ^ K ≤ Y ^ (m * K + K + j) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hY (by omega)
  have h3 : ((m * K : ℕ) : ℝ) ≤ ((m * K + K + j : ℕ) : ℝ) := by exact_mod_cast (by omega)
  calc (n : ℝ) * (K * Y ^ K) ≤ m * Y ^ j * (K * Y ^ K) := h1
    _ = ((m * K : ℕ) : ℝ) * (Y ^ j * Y ^ K) := by push_cast; ring
    _ ≤ ((m * K + K + j : ℕ) : ℝ) * Y ^ (m * K + K + j) :=
        mul_le_mul h3 h2 (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _)) (Nat.cast_nonneg _)

/-- A polynomial `c + x` with `x ≤ K Y^K` and `c ≤ n`. -/
theorem poly_add_le {Y x c : ℝ} {K n : ℕ} (hY : 1 ≤ Y) (hx : x ≤ K * Y ^ K) (hc : c ≤ n) :
    c + x ≤ ((K + n : ℕ) : ℝ) * Y ^ (K + n) := by
  have hY0 : 0 ≤ Y := by linarith
  have h1 : Y ^ K ≤ Y ^ (K + n) := pow_le_pow_right₀ hY (by omega)
  have h3 : 1 ≤ Y ^ (K + n) := one_le_pow₀ hY
  have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) K)
  have h5 : (n : ℝ) ≤ n * Y ^ (K + n) := le_mul_of_one_le_right (Nat.cast_nonneg _) h3
  push_cast
  linarith

section PredictorQP
variable {Y H B : ℝ}

theorem qp_pdX (hH : 1 ≤ H) (hHY : 1 + Real.log H ≤ Y) : 1 ≤ pdX H ∧ pdX H ≤ Y := by
  unfold pdX; exact ⟨by linarith [Real.log_nonneg hH], hHY⟩

theorem qp_pdEs (Ds : ℕ) (hH : 1 ≤ H) (hHY : 1 + Real.log H ≤ Y) :
    QPLe Y Ds (pdEs Ds H) := by
  obtain ⟨h1, h2⟩ := qp_pdX hH hHY
  unfold pdEs
  exact qple_exp (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h2 _)
    (Nat.cast_nonneg _))

theorem qp_pdA0 (Ds : ℕ) (hH : 1 ≤ H) (hHY : 1 + Real.log H ≤ Y) :
    QPLe Y (8 * Ds + 2) (pdA0 Ds H) := by
  obtain ⟨h1, h2⟩ := qp_pdX hH hHY
  have hY : 1 ≤ Y := by linarith
  apply qple_poly
  unfold pdA0
  have hp : pdX H ^ Ds ≤ Y ^ (8 * Ds + 2) :=
    (pow_le_pow_left₀ (by linarith) h2 _).trans (pow_le_pow_right₀ hY (by omega))
  have h1' : 1 ≤ Y ^ (8 * Ds + 2) := one_le_pow₀ hY
  have h3 := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) Ds)
  have h4 : 0 ≤ (Ds : ℝ) * Y ^ (8 * Ds + 2) := by positivity
  push_cast
  linarith

theorem qp_expB (hBY : B ≤ Y) : QPLe Y 1 (Real.exp B) :=
  qple_exp (by norm_num; exact hBY)

theorem pdA0_nonneg (Ds : ℕ) (hH : 1 ≤ H) : 0 ≤ pdA0 Ds H := by
  linarith [one_le_pdA0 (Ds := Ds) hH]

theorem qp_pdT0 (Ds Cr : ℕ) : ∃ K : ℕ, ∀ {Y H B : ℝ}, 1 ≤ H → B ≤ Y →
    1 + Real.log H ≤ Y → QPLe Y K (pdT0 Ds Cr H B) := by
  refine ⟨((((⌈12 * (Cr : ℝ)⌉₊ + (Cr * (8 * Ds + 2) + (8 * Ds + 2))) +
    ⌈(1 + 6 * (Cr : ℝ)) ^ Cr⌉₊) + Ds) + 1) + 1, fun {Y H B} hH hBY hHY => ?_⟩
  have hY : 1 ≤ Y := by linarith [Real.log_nonneg hH]
  have hA := (qp_pdA0 Ds hH hHY).pow hY (pdA0_nonneg Ds hH) Cr
  have hEs0 : 0 ≤ pdEs Ds H := (Real.exp_pos _).le
  have h := ((((QPLe.const hY (12 * (Cr : ℝ))).mul hY (pow_nonneg (pdA0_nonneg Ds hH) _)
    hA).mul hY (by positivity) (QPLe.const hY ((1 + 6 * (Cr : ℝ)) ^ Cr))).mul hY hEs0
    (qp_pdEs Ds hH hHY)).mul hY (Real.exp_pos _).le (qp_expB hBY)
  exact qple_add_one hY h

theorem qple_add' {Y a b : ℝ} {K L : ℕ} (hY : 1 ≤ Y) (ha : QPLe Y K a) (hb : QPLe Y L b) :
    QPLe Y (K + L + 1) (a + b) :=
  qple_add hY (ha.mono hY (Nat.le_add_right K L)) (hb.mono hY (Nat.le_add_left L K))

theorem qple_max' {Y a b : ℝ} {K L : ℕ} (hY : 1 ≤ Y) (ha : QPLe Y K a) (hb : QPLe Y L b) :
    QPLe Y (K + L) (max a b) :=
  qple_max (ha.mono hY (Nat.le_add_right K L)) (hb.mono hY (Nat.le_add_left L K))

theorem ceil_two_log_le {Y B z : ℝ} {K : ℕ} (hY : 1 ≤ Y) (hB0 : 0 ≤ B) (hBY : B ≤ Y)
    (hz : QPLe Y K z) (hz1 : 1 ≤ z) :
    (⌈2 * (B + Real.log z)⌉₊ : ℝ) ≤ ((2 * K + 3 : ℕ) : ℝ) * Y ^ (2 * K + 3) := by
  have hl := hz.log_le (by linarith)
  have hl0 := Real.log_nonneg hz1
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (B + Real.log z) by linarith)
  have h1 : Y ^ K ≤ Y ^ (2 * K + 3) := pow_le_pow_right₀ hY (by omega)
  have h2 : Y ≤ Y ^ (2 * K + 3) := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ _ := pow_le_pow_right₀ hY (by omega)
  have h3 : 1 ≤ Y ^ (2 * K + 3) := one_le_pow₀ hY
  have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) K)
  push_cast
  linarith

theorem qple_exp_LE {Y h M : ℝ} {K1 K2 : ℕ} (D : ℕ) (hY : 1 ≤ Y) (hh1 : 1 ≤ h)
    (hh : QPLe Y K1 h) (hM0 : 0 ≤ M) (hM : M ≤ K2 * Y ^ K2) :
    QPLe Y (D * (1 + (1 + K1 + K2)) ^ D + (1 + K1 + K2) * D)
      (Real.exp (D * (2 + Real.log h + M) ^ D)) := by
  have ha := ((qple_exp (K := 1) (x := 1) (Y := Y) (by norm_num; exact hY)).mul hY
    (by linarith) hh).mul hY (Real.exp_pos M).le (qple_exp hM)
  have ha1 : 1 ≤ Real.exp 1 * h * Real.exp M :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (Real.one_le_exp (by norm_num)) hh1) (Real.one_le_exp hM0)
  have hc := ha.compose hY (D := D) ha1
  have hlog : 1 + Real.log (Real.exp 1 * h * Real.exp M) = 2 + Real.log h + M := by
    rw [Real.log_mul (mul_pos (Real.exp_pos 1) (by linarith)).ne' (Real.exp_pos _).ne',
      Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp, Real.log_exp]
    ring
  rw [hlog] at hc
  exact hc

theorem two_pow_ceil_logb_le {z : ℝ} (hz : 0 ≤ z) :
    (2 : ℝ) ^ ⌈Real.logb 2 z⌉₊ ≤ 2 * z + 1 := by
  rcases hz.eq_or_lt with h | h
  · subst h; simp
  by_cases hl : 0 ≤ Real.logb 2 z
  · have hc : (⌈Real.logb 2 z⌉₊ : ℝ) < Real.logb 2 z + 1 := Nat.ceil_lt_add_one hl
    rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (⌈Real.logb 2 z⌉₊ : ℝ) ≤ 2 ^ (Real.logb 2 z + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hc.le
      _ = 2 * z := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) h,
            Real.rpow_one]; ring
      _ ≤ 2 * z + 1 := by linarith
  · push Not at hl
    rw [Nat.ceil_eq_zero.mpr hl.le]; simp; linarith

theorem qp_pdH0 (Ds Cr : ℕ) : ∃ K : ℕ, ∀ {Y H B : ℝ}, 1 ≤ H → B ≤ Y →
    1 + Real.log H ≤ Y → QPLe Y K (pdH0 Ds Cr H B) := by
  obtain ⟨KT, hKT⟩ := qp_pdT0 Ds Cr
  exact ⟨_, fun {Y H B} hH hBY hHY => by
    have hY : 1 ≤ Y := by linarith [Real.log_nonneg hH]
    have hT0 : 0 ≤ pdT0 Ds Cr H B := by
      linarith [one_le_pdT0 (Ds := Ds) (Cr := Cr) (B := B) hH]
    have hET := ((qp_pdEs Ds hH hHY).mul hY hT0 (hKT hH hBY hHY)).pow hY
      (mul_nonneg (Real.exp_pos _).le hT0) 6
    exact qple_max' hY hET (QPLe.const hY (bandLip + 1))⟩

theorem qp_pdM0 (Ds Cr : ℕ) : ∃ K : ℕ, ∀ {Y H B : ℝ}, 1 ≤ H → 0 ≤ B → B ≤ Y →
    1 + Real.log H ≤ Y → (pdM0 Ds Cr H B : ℝ) ≤ K * Y ^ K := by
  obtain ⟨KH, hKH⟩ := qp_pdH0 Ds Cr
  exact ⟨_, fun {Y H B} hH hB0 hBY hHY => by
    have hY : 1 ≤ Y := by linarith [Real.log_nonneg hH]
    have hH0 := one_le_pdH0 (Ds := Ds) (Cr := Cr) (H := H) (B := B)
    have hl := (hKH hH hBY hHY).log_le (by linarith)
    have hl0 := Real.log_nonneg hH0
    have hP : QPLe Y (KH + 2) (2 + Real.log (pdH0 Ds Cr H B)) :=
      qple_poly (poly_add_le hY hl (by norm_num))
    have hP0 : 0 ≤ 2 + Real.log (pdH0 Ds Cr H B) := by linarith
    have hZ := (((QPLe.const hY 3).mul hY (Real.exp_pos _).le (qp_pdEs Ds hH hHY)).mul hY
      (Nat.cast_nonneg Cr) (QPLe.const hY (Cr : ℝ))).mul hY (pow_nonneg hP0 Cr)
      (hP.pow hY hP0 Cr)
    have hZ1 := qple_add_one hY hZ
    have hZ0 : 0 ≤ 3 * pdEs Ds H * Cr * (2 + Real.log (pdH0 Ds Cr H B)) ^ Cr :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        (Nat.cast_nonneg _)) (pow_nonneg hP0 _)
    have h := ceil_two_log_le hY hB0 hBY hZ1 (le_add_of_nonneg_left hZ0)
    unfold pdM0
    exact h⟩

theorem qp_pdLE_exp (Ds Cr D : ℕ) : ∃ K : ℕ, ∀ {Y H B : ℝ}, 1 ≤ H → 0 ≤ B → B ≤ Y →
    1 + Real.log H ≤ Y → QPLe Y K (Real.exp (D * pdLE Ds Cr H B ^ D)) := by
  obtain ⟨KH, hKH⟩ := qp_pdH0 Ds Cr
  obtain ⟨KM, hKM⟩ := qp_pdM0 Ds Cr
  exact ⟨_, fun {Y H B} hH hB0 hBY hHY => by
    have hY : 1 ≤ Y := by linarith [Real.log_nonneg hH]
    have h := qple_exp_LE D hY (one_le_pdH0 (Ds := Ds) (Cr := Cr) (H := H) (B := B))
      (hKH hH hBY hHY) (Nat.cast_nonneg _) (hKM hH hB0 hBY hHY)
    unfold pdLE
    exact h⟩

theorem qp_tailCT (κ : LocalKernelClass) (KE : ℕ) : ∃ K : ℕ, ∀ {Y E : ℝ} {d : ℕ}, 1 ≤ Y →
    (d : ℝ) ≤ 2 * Y → 1 ≤ E → QPLe Y KE E → QPLe Y K (tailCT κ d E) := by
  exact ⟨_, fun {Y E d} hY hd hE hEK => by
    have hY0 : 0 ≤ Y := by linarith
    have hlE : 0 ≤ Real.log E := Real.log_nonneg hE
    have hlEK : Real.log E ≤ KE * Y ^ KE := hEK.log_le (by linarith)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    -- the factor `tailAlpha`
    have hX : QPLe Y 5 ((((d + 1 : ℕ) + 1 : ℝ) + 1)) := by
      apply qple_poly
      have : Y ≤ Y ^ 5 := le_self_pow₀ hY (by norm_num)
      push_cast; linarith
    have hX0 : 0 ≤ ((((d + 1 : ℕ) + 1 : ℝ) + 1)) := by positivity
    have hL : QPLe Y (KE * 2 + 28) (Real.log 24 + 2 * Real.log E + 2 + Real.log 4) := by
      apply qple_poly
      have h24 : Real.log 24 ≤ 23 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 24 by norm_num)]
      have h4 : Real.log 4 ≤ 3 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
      have h1 : Y ^ KE ≤ Y ^ (KE * 2 + 28) := pow_le_pow_right₀ hY (by omega)
      have h2 : 1 ≤ Y ^ (KE * 2 + 28) := one_le_pow₀ hY
      have h3 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) KE)
      push_cast; linarith
    have hL0 : 0 ≤ Real.log 24 + 2 * Real.log E + 2 + Real.log 4 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 24 by norm_num)
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      linarith
    have hXL0 : 0 ≤ 32 * ((((d + 1 : ℕ) + 1 : ℝ) + 1)) ^ 4 *
        (Real.log 24 + 2 * Real.log E + 2 + Real.log 4) := by positivity
    have hα := (QPLe.const hY (24 * (2 * Real.pi) ^ 2)).mul hY (by positivity)
      ((QPLe.const hY 4).mul hY hXL0 (((QPLe.const hY 32).mul hY (pow_nonneg hX0 4)
        (hX.pow hY hX0 4)).mul hY hL0 hL))
    -- the factor `tailLam`
    have hX2 : QPLe Y 6 (((d * d + 1 : ℕ) : ℝ) + 1) := by
      apply qple_poly
      have hdd : (d : ℝ) * d ≤ 4 * Y ^ 2 := by nlinarith only [hd]
      have h1 : Y ^ 2 ≤ Y ^ 6 := pow_le_pow_right₀ hY (by norm_num)
      have h2 : 1 ≤ Y ^ 6 := one_le_pow₀ hY
      push_cast; linarith
    have hX20 : 0 ≤ (((d * d + 1 : ℕ) : ℝ) + 1) := by positivity
    have hlog0 : 0 ≤ Real.log (2 * (E + 2)) := Real.log_nonneg (by linarith)
    have hlog : QPLe Y (⌈(5 : ℝ)⌉₊ + KE) (Real.log (2 * (E + 2))) := by
      refine QPLe.of_le ?_ ((QPLe.const hY 5).mul hY (by linarith) hEK)
      linarith [Real.log_le_sub_one_of_pos (show 0 < 2 * (E + 2) by linarith)]
    have hlam := (QPLe.const hY (2 * Real.pi)).mul hY (by positivity)
      ((((QPLe.const hY 128).mul hY (pow_nonneg hX20 4) (hX2.pow hY hX20 4)).mul hY hlog0
        hlog).mul hY (by linarith) hEK)
    have hCT := qple_add' hY ((QPLe.const hY (linearScaleConst κ)).mul hY
      (mul_nonneg (by positivity) (mul_nonneg (by norm_num) hXL0)) hα)
      ((QPLe.const hY (localKernelSupBound κ)).mul hY (mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (by positivity) hlog0) (by linarith))) hlam)
    unfold tailCT
    exact hCT⟩

theorem qp_pdK0 (κ : LocalKernelClass) (Dc J1 Ds Cr : ℕ) : ∃ K : ℕ, ∀ {Y H B : ℝ} {d' : ℕ},
    1 ≤ H → 0 ≤ B → B ≤ Y → 1 + Real.log H ≤ Y → (d' : ℝ) ≤ 2 * Y →
    QPLe Y K ((2 : ℝ) ^ pdK0 κ d' Dc J1 Ds Cr H B) := by
  obtain ⟨KE, hKE⟩ := qp_pdLE_exp Ds Cr Dc
  obtain ⟨KE1, hKE1⟩ := qp_pdLE_exp Ds Cr J1
  obtain ⟨KC, hKC⟩ := qp_tailCT κ KE
  exact ⟨_, fun {Y H B d'} hH hB0 hBY hHY hd => by
    have hY : 1 ≤ Y := by linarith [Real.log_nonneg hH]
    have hE := hKE hH hB0 hBY hHY
    have hE1 := hKE1 hH hB0 hBY hHY
    have hE1' : 1 ≤ pdE Dc Ds Cr H B := one_le_pdE Dc Ds Cr H B
    have hEq : QPLe Y KE (pdE Dc Ds Cr H B) := hE
    have hCT := hKC hY hd hE1' hEq
    have hCT0 := tailCT_nonneg κ d' hE1'
    have h7 := qple_pow_var (n := d' + d') (m := 4) (j := 1) hY (by norm_num)
      (QPLe.const hY 7) (by push_cast; linarith)
    have hpi := qple_pow_var (n := (d' + 1) ^ 2) (m := 9) (j := 2) hY (by positivity)
      (QPLe.const hY (2 * Real.pi)) (by
        have h1 : (d' : ℝ) + 1 ≤ 3 * Y := by linarith
        have h0 : (0 : ℝ) ≤ d' + 1 := by positivity
        push_cast; nlinarith only [hd, hY])
    have hZ := ((((((((QPLe.const hY 12).mul hY (Real.exp_pos _).le (qp_pdEs Ds hH hHY)).mul hY
      (by linarith) (qple_add_one hY hEq)).mul hY (Real.exp_pos _).le hE1).mul hY
      (by linarith) (qple_add_one hY hCT)).mul hY (by norm_num) (QPLe.const hY 2)).mul hY
      (by positivity) h7).mul hY (by positivity) hpi).mul hY (Real.exp_pos _).le (qp_expB hBY)
    have hZ0 : 0 ≤ 12 * pdEs Ds H * (pdE Dc Ds Cr H B + 1) * pdE1 J1 Ds Cr H B *
        (tailCT κ d' (pdE Dc Ds Cr H B) + 1) * 2 * 7 ^ (d' + d') *
        (2 * Real.pi) ^ ((d' + 1) ^ 2) * Real.exp B := by
      have : 0 ≤ pdE1 J1 Ds Cr H B := (Real.exp_pos _).le
      have : 0 ≤ pdEs Ds H := (Real.exp_pos _).le
      have : 0 ≤ tailCT κ d' (pdE Dc Ds Cr H B) + 1 := by linarith
      have : 0 ≤ pdE Dc Ds Cr H B + 1 := by linarith
      positivity
    have h2 := qple_add_one hY ((QPLe.const hY 2).mul hY hZ0 hZ)
    unfold pdK0
    exact QPLe.of_le (two_pow_ceil_logb_le hZ0) h2⟩

theorem qp_pdCard (κ : LocalKernelClass) (Dc J1 Ds Cr : ℕ) : ∃ K : ℕ,
    ∀ {Y H B : ℝ} {d' : ℕ}, 1 ≤ H → 0 ≤ B → B ≤ Y → 1 + Real.log H ≤ Y →
    (d' : ℝ) ≤ 2 * Y → QPLe Y K (pdCard κ d' Dc J1 Ds Cr H B) := by
  obtain ⟨KT, hKT⟩ := qp_pdT0 Ds Cr
  obtain ⟨KE, hKE⟩ := qp_pdLE_exp Ds Cr Dc
  obtain ⟨KK, hKK⟩ := qp_pdK0 κ Dc J1 Ds Cr
  exact ⟨_, fun {Y H B d'} hH hB0 hBY hHY hd => by
    have hY : 1 ≤ Y := by linarith [Real.log_nonneg hH]
    have hd0 : (0 : ℝ) ≤ d' := Nat.cast_nonneg _
    obtain ⟨hX1, hXY⟩ := qp_pdX hH hHY
    have hE : QPLe Y KE (pdE Dc Ds Cr H B) := hKE hH hB0 hBY hHY
    have hE1' : 1 ≤ pdE Dc Ds Cr H B := one_le_pdE Dc Ds Cr H B
    have hT0 : 0 ≤ pdT0 Ds Cr H B := by
      linarith [one_le_pdT0 (Ds := Ds) (Cr := Cr) (B := B) hH]
    -- the four factors
    have h1 : QPLe Y 10 (Real.exp (10 * pdX H ^ 2)) := by
      apply qple_exp
      have : pdX H ^ 2 ≤ Y ^ 10 := (pow_le_pow_left₀ (by linarith) hXY 2).trans
        (pow_le_pow_right₀ hY (by norm_num))
      push_cast; linarith
    have h3T := (QPLe.const hY 3).mul hY hT0 (hKT hH hBY hHY)
    have h2 := qple_pow_var (n := 3 * d') (m := 6) (j := 1) hY (by positivity) h3T
      (by push_cast; linarith)
    have hfE : (⌊pdE Dc Ds Cr H B⌋₊ : ℝ) ≤ pdE Dc Ds Cr H B :=
      Nat.floor_le (by linarith)
    have h3a : QPLe Y _ (3 * (⌊pdE Dc Ds Cr H B⌋₊ : ℝ) ^ 2) :=
      QPLe.of_le (by gcongr) ((QPLe.const hY 3).mul hY (by positivity)
        (hE.pow hY (by linarith) 2))
    have h3 := qple_pow_var (n := d' * d') (m := 4) (j := 2) hY (by positivity) h3a
      (by push_cast; nlinarith only [hd])
    have hK0 := hKK hH hB0 hBY hHY hd
    have hEK : QPLe Y _ (pdE Dc Ds Cr H B * 2 ^ pdK0 κ d' Dc J1 Ds Cr H B) :=
      hE.mul hY (by positivity) hK0
    have hfEK : (⌊pdE Dc Ds Cr H B * 2 ^ pdK0 κ d' Dc J1 Ds Cr H B⌋₊ : ℝ) ≤
        pdE Dc Ds Cr H B * 2 ^ pdK0 κ d' Dc J1 Ds Cr H B :=
      Nat.floor_le (by positivity)
    have h4a : QPLe Y _ (3 * (⌊pdE Dc Ds Cr H B * 2 ^ pdK0 κ d' Dc J1 Ds Cr H B⌋₊ : ℝ) ^ 2) :=
      QPLe.of_le (by gcongr) ((QPLe.const hY 3).mul hY (by positivity)
        (hEK.pow hY (by positivity) 2))
    have h4 := qple_pow_var (n := d') (m := 2) (j := 1) hY (by positivity) h4a
      (by push_cast; linarith)
    have h := ((h1.mul hY (by positivity) h2).mul hY (by positivity) h3).mul hY
      (by positivity) h4
    unfold pdCard
    exact h⟩

end PredictorQP

/-- Blueprint lem:predictors, `eq:predictors` (Declaration predictors, line 1536): for two
fixed bounded original atoms of complexity `H` in slots `i, k` and `B ≥ 1`, their product in
the local form is replaced by a finite list of terms
`ψ_a(y_a) ψ_b(y_b) w_I(x,t) e(λ_* t²)` with `|λ_*| |I|² ≤ D_pred`, scale-dependent scalar
coefficients, bounded atoms `ψ_a, ψ_b` fixed on `J`, and absolute length-weighted error at
most `e^{-B} K_a K_b ‖1_J F_a‖ ‖1_J F_b‖` against admissible opponents with depth energy (the
opponent constants `K_a, K_b` carry the polynomial in `log(2 D_h)` and `1 + L`). The list
size, the coefficient norm, the multiplier complexities and `D_pred` are at most
`D_pred = exp(C (1 + B + log H)^C)`, i.e. `log D_pred ≤ poly(1 + B, log H)`. -/
theorem finitePredictorList (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ c₁ C : ℕ, 1 ≤ c₁ ∧ ∀ {d e : ℕ} (H B : ℝ) (A : QuadraticChartData d)
      (A' : QuadraticChartData e), 1 ≤ d → 1 ≤ e → QuadraticChartComplexity c₀ H A →
      QuadraticChartComplexity c₀ H A' → IsBoundedQuadraticChart A →
      IsBoundedQuadraticChart A' → 1 ≤ B →
      ∀ {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
      ∃ (ι : Type) (L : Finset ι) (ψa ψb : ι → QuadraticChartData (d + e)) (lam : ι → ℝ)
        (coef : ι → ℝ → ℂ),
        (L.card : ℝ) ≤ Real.exp (C * (1 + B + Real.log H) ^ C) ∧
        (∀ ℓ ∈ L, IsBoundedQuadraticChart (ψa ℓ) ∧ IsBoundedQuadraticChart (ψb ℓ) ∧
          QuadraticChartComplexity c₁ (Real.exp (C * (1 + B + Real.log H) ^ C)) (ψa ℓ) ∧
          QuadraticChartComplexity c₁ (Real.exp (C * (1 + B + Real.log H) ^ C)) (ψb ℓ)) ∧
        (∀ r, ∑ ℓ ∈ L, ‖coef ℓ r‖ ≤ Real.exp (C * (1 + B + Real.log H) ^ C)) ∧
        (∀ ℓ r, coef ℓ r ≠ 0 → |lam ℓ| * r ^ 2 ≤ Real.exp (C * (1 + B + Real.log H) ^ C)) ∧
        ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
        (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) →
        ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
          (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
        ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, 0 ≤ Ka → 0 ≤ Kb →
        IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
        HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb →
        (∀ I, Measurable (za I)) → (∀ I, Measurable (zb I)) →
        (∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
        (∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
        ∀ (f : ℤ × ℤ → Fin 4 → ℝ → ℂ), (∀ I, f I a = za I) →
        (∀ I, f I i = quadraticChartAtom A) → (∀ I, f I k = quadraticChartAtom A') →
        (∀ I, f I b = zb I) →
        ∑ I ∈ S, dyadicGridLength G I.1 *
          ‖localProgressionForm (dyadicGridLength G I.1) (w I) (f I) -
            ∑ ℓ ∈ L, coef ℓ (dyadicGridLength G I.1) *
              separatedLocalForm (dyadicGridLength G I.1) (w I)
                (fun t => (Real.fourierChar (lam ℓ * t ^ 2) : ℂ)) a b
                (fun y => za I y * quadraticChartAtom (ψa ℓ) y)
                (fun y => zb I y * quadraticChartAtom (ψb ℓ) y)‖ ≤
          Real.exp (-B) * Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
            Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  obtain ⟨c₁, Ds, Cr, Dc, J1, hc₁, hP⟩ := predictor_list_param c₀ hc κ
  obtain ⟨K1, hK1⟩ := qp_pdCard κ Dc J1 Ds Cr
  obtain ⟨K2, hK2⟩ := qp_pdH0 Ds Cr
  obtain ⟨K3, hK3⟩ := qp_pdLE_exp Ds Cr Dc
  refine ⟨c₁, K1 + K2 + (⌈(4 : ℝ)⌉₊ + Ds + K3) + K3, hc₁, ?_⟩
  intro d e H B A A' hd he hA hA' hAb hA'b hB a i k b h1 h2 h3 h4 h5 h6
  obtain ⟨ι, L, ψa, ψb, lam, coef, hcard, hbd, hcoef, hlam, herr⟩ :=
    hP H B A A' hd he hA hA' hAb hA'b hB h1 h2 h3 h4 h5 h6
  have hH1 : 1 ≤ H := by linarith [hA.lower, Real.add_one_le_exp (2 : ℝ)]
  have hlogH := Real.log_nonneg hH1
  set Y := 1 + B + Real.log H with hYdef
  have hY1 : 1 ≤ Y := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hBY : B ≤ Y := by linarith
  have hHY : 1 + Real.log H ≤ Y := by linarith
  have hdY : ((d + e : ℕ) : ℝ) ≤ 2 * Y := by
    have := hA.dimension; have := hA'.dimension; push_cast; linarith
  set K := K1 + K2 + (⌈(4 : ℝ)⌉₊ + Ds + K3) + K3 with hK
  have hcardQ : QPLe Y K (pdCard κ (d + e) Dc J1 Ds Cr H B) :=
    (hK1 hH1 hB0 hBY hHY hdY).mono hY1 (by omega)
  have hH0Q : QPLe Y K (pdH0 Ds Cr H B) := (hK2 hH1 hBY hHY).mono hY1 (by omega)
  have hE : QPLe Y K3 (pdE Dc Ds Cr H B) := hK3 hH1 hB0 hBY hHY
  have hE0 : 0 ≤ pdE Dc Ds Cr H B := by linarith [one_le_pdE Dc Ds Cr H B]
  have hEQ : QPLe Y K (pdE Dc Ds Cr H B) := hE.mono hY1 (by omega)
  have hcoefQ : QPLe Y K (4 * pdEs Ds H * pdE Dc Ds Cr H B) :=
    (((QPLe.const hY1 4).mul hY1 (Real.exp_pos _).le (qp_pdEs Ds hH1 hHY)).mul hY1 hE0
      hE).mono hY1 (by omega)
  refine ⟨ι, L, ψa, ψb, lam, coef, hcard.trans hcardQ, fun ℓ hℓ => ?_,
    fun r => (hcoef r).trans hcoefQ, fun ℓ r h => (hlam ℓ r h).trans hEQ, herr⟩
  obtain ⟨b1, b2, c1, c2⟩ := hbd ℓ hℓ
  exact ⟨b1, b2, quadraticChartComplexity_mono c1 hH0Q, quadraticChartComplexity_mono c2 hH0Q⟩

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Dyadic conditional expectations -/

/-- The position of the depth-`h` cell containing `y`. -/
noncomputable def dyadicIndex (G : RealDyadicGrid) (h : ℤ) (y : ℝ) : ℤ :=
  Classical.choose (dyadicGridCell_covers G h y)

theorem mem_dyadicIndex (G : RealDyadicGrid) (h : ℤ) (y : ℝ) :
    y ∈ dyadicGridCell G h (dyadicIndex G h y) :=
  Classical.choose_spec (dyadicGridCell_covers G h y)

theorem dyadicIndex_eq {G : RealDyadicGrid} {h m : ℤ} {y : ℝ}
    (hy : y ∈ dyadicGridCell G h m) : dyadicIndex G h y = m :=
  dyadicGridCell_sameDepth_common_point G h _ _ (mem_dyadicIndex G h y) hy

/-- The normalized integral of `F` over the depth-`h` cell at position `m`. -/
noncomputable def cellAverage (G : RealDyadicGrid) (h m : ℤ) (F : ℝ → ℂ) : ℂ :=
  (((dyadicGridLength G h)⁻¹ : ℝ) : ℂ) * ∫ y in dyadicGridCell G h m, F y

/-- The dyadic conditional expectation `E_h` at depth `h`. -/
noncomputable def depthExpectation (G : RealDyadicGrid) (h : ℤ) (F : ℝ → ℂ) (y : ℝ) : ℂ :=
  cellAverage G h (dyadicIndex G h y) F

theorem depthExpectation_of_mem {G : RealDyadicGrid} {h m : ℤ} {y : ℝ}
    (hy : y ∈ dyadicGridCell G h m) (F : ℝ → ℂ) :
    depthExpectation G h F y = cellAverage G h m F := by
  rw [depthExpectation, dyadicIndex_eq hy]

/-- Functions that are constant on every depth-`h` cell. -/
def DepthConst (G : RealDyadicGrid) (h : ℤ) (g : ℝ → ℂ) : Prop :=
  ∀ m : ℤ, ∀ y ∈ dyadicGridCell G h m, ∀ z ∈ dyadicGridCell G h m, g y = g z

theorem depthConst_depthExpectation (G : RealDyadicGrid) (h : ℤ) (F : ℝ → ℂ) :
    DepthConst G h (depthExpectation G h F) := fun m y hy z hz => by
  rw [depthExpectation_of_mem hy, depthExpectation_of_mem hz]

/-- Constancy passes to deeper cells. -/
theorem DepthConst.mono {G : RealDyadicGrid} {h k : ℤ} (hhk : h ≤ k) {g : ℝ → ℂ}
    (hg : DepthConst G h g) : DepthConst G k g := by
  intro m y hy z hz
  obtain ⟨n, hn⟩ := dyadicGridCell_ancestor G hhk m
  exact hg n y (hn hy) z (hn hz)

/-- The integral over a cell splits over its depth-`(s+n)` generation. -/
theorem setIntegral_cell_eq_sum_generation (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ)
    {F : ℝ → ℂ} (hF : IntegrableOn F (dyadicGridCell G I.1 I.2)) :
    ∫ y in dyadicGridCell G I.1 I.2, F y =
      ∑ Q ∈ dyadicGeneration G I n, ∫ y in dyadicGridCell G Q.1 Q.2, F y := by
  have h := integral_biUnion_finset (dyadicGeneration G I n)
    (fun Q _ => dyadicGridCell_measurable G Q.1 Q.2) (dyadicGeneration_pairwiseDisjoint G I n)
    (μ := volume) (f := F)
    (fun Q hQ => hF.mono_set (dyadicGeneration_subset G I n hQ))
  rw [dyadicGeneration_union] at h
  exact h

theorem setIntegral_mul_const_cell {G : RealDyadicGrid} {Q : ℤ × ℤ} {g : ℝ → ℂ} {c : ℂ}
    (hg : ∀ y ∈ dyadicGridCell G Q.1 Q.2, g y = c) (F : ℝ → ℂ) :
    ∫ y in dyadicGridCell G Q.1 Q.2, F y * g y =
      (∫ y in dyadicGridCell G Q.1 Q.2, F y) * c := by
  rw [← integral_mul_const]
  exact setIntegral_congr_fun (dyadicGridCell_measurable G Q.1 Q.2)
    (fun y hy => by simp only [hg y hy])

/-- `∫_Q E_k F = ∫_Q F` on cells of depth at most `k`. -/
theorem setIntegral_depthExpectation (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ)
    {F : ℝ → ℂ} (hF : IntegrableOn F (dyadicGridCell G I.1 I.2)) :
    ∫ y in dyadicGridCell G I.1 I.2, depthExpectation G (I.1 + n) F y =
      ∫ y in dyadicGridCell G I.1 I.2, F y := by
  have hE : ∀ Q ∈ dyadicGeneration G I n, ∫ y in dyadicGridCell G Q.1 Q.2,
      depthExpectation G (I.1 + n) F y = ∫ y in dyadicGridCell G Q.1 Q.2, F y := by
    intro Q hQ
    have hd := dyadicGeneration_depth G I n hQ
    have hc : ∀ y ∈ dyadicGridCell G Q.1 Q.2,
        depthExpectation G (I.1 + n) F y = cellAverage G Q.1 Q.2 F := by
      intro y hy
      rw [← hd]; exact depthExpectation_of_mem hy F
    rw [setIntegral_congr_fun (dyadicGridCell_measurable G Q.1 Q.2) hc, setIntegral_const,
      cellAverage]
    have hvol : volume.real (dyadicGridCell G Q.1 Q.2) = dyadicGridLength G Q.1 := by
      rw [Measure.real, dyadicGridCell_volume, ENNReal.toReal_ofReal
        (dyadicGridLength_pos G Q.1).le]
    rw [hvol, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (dyadicGridLength_pos G Q.1).ne', Complex.ofReal_one, one_mul]
  have hEi : IntegrableOn (depthExpectation G (I.1 + n) F) (dyadicGridCell G I.1 I.2) := by
    rw [← dyadicGeneration_union G I n]
    refine (integrableOn_finset_iUnion).mpr fun Q hQ => ?_
    have hd := dyadicGeneration_depth G I n hQ
    refine (integrableOn_const (C := cellAverage G Q.1 Q.2 F)
      (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top)).congr_fun ?_
      (dyadicGridCell_measurable G Q.1 Q.2)
    intro y hy
    rw [← hd]; exact (depthExpectation_of_mem hy F).symm
  rw [setIntegral_cell_eq_sum_generation G I n hEi,
    setIntegral_cell_eq_sum_generation G I n hF]
  exact Finset.sum_congr rfl hE

theorem dyadicIndex_eq_floor (G : RealDyadicGrid) (h : ℤ) (y : ℝ) :
    dyadicIndex G h y = ⌊(y - G.origin h) / dyadicGridLength G h⌋ := by
  apply dyadicIndex_eq
  have hl := dyadicGridLength_pos G h
  have h1 := Int.floor_le ((y - G.origin h) / dyadicGridLength G h)
  have h2 := Int.lt_floor_add_one ((y - G.origin h) / dyadicGridLength G h)
  rw [le_div_iff₀ hl] at h1
  rw [div_lt_iff₀ hl] at h2
  unfold dyadicGridCell dyadicGridLeft
  constructor <;> nlinarith

theorem measurable_depthExpectation (G : RealDyadicGrid) (h : ℤ) (F : ℝ → ℂ) :
    Measurable (depthExpectation G h F) := by
  have e : depthExpectation G h F = (fun m : ℤ => cellAverage G h m F) ∘
      (fun y => ⌊(y - G.origin h) / dyadicGridLength G h⌋) := by
    funext y; simp only [depthExpectation, dyadicIndex_eq_floor, Function.comp]
  rw [e]
  exact (measurable_of_countable _).comp
    (Int.measurable_floor.comp ((measurable_id.sub_const _).div_const _))

theorem volume_real_cell (G : RealDyadicGrid) (s m : ℤ) :
    volume.real (dyadicGridCell G s m) = dyadicGridLength G s := by
  rw [Measure.real, dyadicGridCell_volume, ENNReal.toReal_ofReal (dyadicGridLength_pos G s).le]

theorem cell_isFiniteMeasure (G : RealDyadicGrid) (s m : ℤ) :
    IsFiniteMeasure (volume.restrict (dyadicGridCell G s m)) :=
  isFiniteMeasure_restrict.mpr (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top)

theorem dyadicGridLength_add_nat (G : RealDyadicGrid) (s : ℤ) (j : ℕ) :
    dyadicGridLength G (s + j) = dyadicGridLength G s * (2 : ℝ)⁻¹ ^ j := by
  unfold dyadicGridLength
  rw [neg_add, zpow_add₀ (by norm_num), zpow_neg, zpow_neg, zpow_natCast, inv_pow]; ring

theorem norm_cellAverage_sub_le {G : RealDyadicGrid} {h m : ℤ} {F : ℝ → ℂ} {c : ℂ} {B : ℝ}
    (hF : IntegrableOn F (dyadicGridCell G h m))
    (hB : ∀ z ∈ dyadicGridCell G h m, ‖F z - c‖ ≤ B) :
    ‖cellAverage G h m F - c‖ ≤ B := by
  have hl := dyadicGridLength_pos G h
  have hfin : volume (dyadicGridCell G h m) < ⊤ := by
    rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top
  have e : cellAverage G h m F - c =
      (((dyadicGridLength G h)⁻¹ : ℝ) : ℂ) * ∫ y in dyadicGridCell G h m, (F y - c) := by
    rw [integral_sub hF (integrableOn_const hfin.ne), setIntegral_const, volume_real_cell,
      cellAverage, mul_sub, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hl.ne', Complex.ofReal_one, one_mul]
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hI := norm_setIntegral_le_of_norm_le_const_ae' hfin
    (Filter.Eventually.of_forall fun z hz => hB z hz) (f := fun y => F y - c)
  rw [volume_real_cell] at hI
  calc (dyadicGridLength G h)⁻¹ * ‖∫ y in dyadicGridCell G h m, (F y - c)‖
      ≤ (dyadicGridLength G h)⁻¹ * (B * dyadicGridLength G h) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = B := by field_simp

theorem integrableOn_cell_of_continuous (G : RealDyadicGrid) (s m : ℤ) {θ : ℝ → ℂ}
    (hθ : Continuous θ) : IntegrableOn θ (dyadicGridCell G s m) :=
  (hθ.integrableOn_Icc (a := dyadicGridLeft G s m)
    (b := dyadicGridLeft G s m + dyadicGridLength G s)).mono_set Set.Ico_subset_Icc_self

theorem norm_depthExpectation_le (G : RealDyadicGrid) (h : ℤ) {θ : ℝ → ℂ} {L : ℝ}
    (hθc : Continuous θ) (hθb : ∀ y, ‖θ y‖ ≤ L) (y : ℝ) :
    ‖depthExpectation G h θ y‖ ≤ L := by
  have h := norm_cellAverage_sub_le (c := 0) (B := L)
    (integrableOn_cell_of_continuous G h (dyadicIndex G h y) hθc)
    (fun z _ => by rw [sub_zero]; exact hθb z)
  rw [sub_zero] at h
  exact h

theorem norm_sub_depthExpectation_le (G : RealDyadicGrid) (h : ℤ) {θ : ℝ → ℂ} {Lip : ℝ}
    (hLip0 : 0 ≤ Lip) (hθc : Continuous θ) (hLip : ∀ y z, ‖θ y - θ z‖ ≤ Lip * |y - z|)
    (y : ℝ) : ‖θ y - depthExpectation G h θ y‖ ≤ Lip * dyadicGridLength G h := by
  rw [norm_sub_rev]
  have hy := mem_dyadicIndex G h y
  refine norm_cellAverage_sub_le (integrableOn_cell_of_continuous G h _ hθc) fun z hz => ?_
  refine (hLip z y).trans (mul_le_mul_of_nonneg_left ?_ hLip0)
  unfold dyadicGridCell at hy hz
  obtain ⟨h1, h2⟩ := hy
  obtain ⟨h3, h4⟩ := hz
  rw [abs_le]; constructor <;> linarith

theorem norm_depthExpectation_succ_sub_le (G : RealDyadicGrid) (h : ℤ) {θ : ℝ → ℂ}
    {Lip : ℝ} (hLip0 : 0 ≤ Lip) (hθc : Continuous θ)
    (hLip : ∀ y z, ‖θ y - θ z‖ ≤ Lip * |y - z|) (y : ℝ) :
    ‖depthExpectation G (h + 1) θ y - depthExpectation G h θ y‖ ≤
      2 * Lip * dyadicGridLength G h := by
  have h1 := norm_sub_depthExpectation_le G (h + 1) hLip0 hθc hLip y
  have h2 := norm_sub_depthExpectation_le G h hLip0 hθc hLip y
  have hl := dyadicGridLength_half G h
  have hl0 := (dyadicGridLength_pos G (h + 1)).le
  calc ‖depthExpectation G (h + 1) θ y - depthExpectation G h θ y‖
      = ‖(θ y - depthExpectation G h θ y) - (θ y - depthExpectation G (h + 1) θ y)‖ := by
        congr 1; ring
    _ ≤ ‖θ y - depthExpectation G h θ y‖ + ‖θ y - depthExpectation G (h + 1) θ y‖ :=
        norm_sub_le _ _
    _ ≤ Lip * dyadicGridLength G h + Lip * dyadicGridLength G (h + 1) := add_le_add h2 h1
    _ ≤ 2 * Lip * dyadicGridLength G h := by nlinarith

theorem integrableOn_cell_mul_bdd {G : RealDyadicGrid} {I : ℤ × ℤ} {u v : ℝ → ℂ} {B : ℝ}
    (hu : MemLp u 2 (volume.restrict (dyadicGridCell G I.1 I.2))) (hv : Measurable v)
    (hvb : ∀ y, ‖v y‖ ≤ B) :
    IntegrableOn (fun y => u y * v y) (dyadicGridCell G I.1 I.2) := by
  have := cell_isFiniteMeasure G I.1 I.2
  exact (hu.integrable one_le_two).mul_bdd hv.aestronglyMeasurable
    (Filter.Eventually.of_forall hvb)

theorem norm_setIntegral_cell_mul_le {G : RealDyadicGrid} {I : ℤ × ℤ} {u v : ℝ → ℂ} {B : ℝ}
    (hu : MemLp u 2 (volume.restrict (dyadicGridCell G I.1 I.2))) (hB : 0 ≤ B)
    (hvb : ∀ y, ‖v y‖ ≤ B) :
    ‖∫ y in dyadicGridCell G I.1 I.2, u y * v y‖ ≤
      B * Real.sqrt (dyadicGridLength G I.1) *
        Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖u y‖ ^ 2) := by
  have := cell_isFiniteMeasure G I.1 I.2
  have hfin : volume (dyadicGridCell G I.1 I.2) < ⊤ := by
    rw [dyadicGridCell_volume]; exact ENNReal.ofReal_lt_top
  have hsq := setIntegral_norm_le_sqrt hfin hu
  rw [volume_real_cell] at hsq
  calc ‖∫ y in dyadicGridCell G I.1 I.2, u y * v y‖
      ≤ ∫ y in dyadicGridCell G I.1 I.2, ‖u y * v y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in dyadicGridCell G I.1 I.2, B * ‖u y‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((hu.integrable one_le_two).norm.const_mul B)
          (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hvb y) (norm_nonneg _)
    _ = B * ∫ y in dyadicGridCell G I.1 I.2, ‖u y‖ := integral_const_mul _ _
    _ ≤ B * (Real.sqrt (dyadicGridLength G I.1) *
          Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖u y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq hB
    _ = _ := by ring

/-- The swap principle with constancy only on the depth-`(s+n)` cells of `I`. -/
theorem setIntegral_mul_locConst (G : RealDyadicGrid) (I : ℤ × ℤ) (n : ℕ)
    {D μ g : ℝ → ℂ}
    (hg : ∀ Q ∈ dyadicGeneration G I n, ∀ y ∈ dyadicGridCell G Q.1 Q.2,
      ∀ z ∈ dyadicGridCell G Q.1 Q.2, g y = g z)
    (hD : IntegrableOn D (dyadicGridCell G I.1 I.2))
    (hμ : IntegrableOn μ (dyadicGridCell G I.1 I.2))
    (hDμ : ∀ Q ∈ dyadicGeneration G I n,
      ∫ y in dyadicGridCell G Q.1 Q.2, D y = ∫ y in dyadicGridCell G Q.1 Q.2, μ y) :
    ∫ y in dyadicGridCell G I.1 I.2, D y * g y =
      ∫ y in dyadicGridCell G I.1 I.2, μ y * g y := by
  have hconst : ∀ Q ∈ dyadicGeneration G I n, ∀ y ∈ dyadicGridCell G Q.1 Q.2,
      g y = g (dyadicGridLeft G Q.1 Q.2) := fun Q hQ y hy =>
    hg Q hQ y hy _ (dyadicGridCell_left_mem G Q.1 Q.2)
  have hsub : ∀ Q ∈ dyadicGeneration G I n,
      dyadicGridCell G Q.1 Q.2 ⊆ dyadicGridCell G I.1 I.2 :=
    fun Q hQ => dyadicGeneration_subset G I n hQ
  have hint : ∀ F : ℝ → ℂ, IntegrableOn F (dyadicGridCell G I.1 I.2) →
      IntegrableOn (fun y => F y * g y) (dyadicGridCell G I.1 I.2) := by
    intro F hF
    rw [← dyadicGeneration_union G I n]
    refine (integrableOn_finset_iUnion).mpr fun Q hQ => ?_
    have hFQ := hF.mono_set (hsub Q hQ)
    refine IntegrableOn.congr_fun (Integrable.mul_const hFQ (g (dyadicGridLeft G Q.1 Q.2)))
      ?_ (dyadicGridCell_measurable G Q.1 Q.2)
    intro y hy
    simp only [hconst Q hQ y hy]
  rw [setIntegral_cell_eq_sum_generation G I n (hint D hD),
    setIntegral_cell_eq_sum_generation G I n (hint μ hμ)]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [setIntegral_mul_const_cell (hconst Q hQ), setIntegral_mul_const_cell (hconst Q hQ),
    hDμ Q hQ]

theorem depthConst_locConst {G : RealDyadicGrid} {I : ℤ × ℤ} {n : ℕ} {k : ℤ}
    (hk : k ≤ I.1 + n) {g : ℝ → ℂ} (hg : DepthConst G k g) :
    ∀ Q ∈ dyadicGeneration G I n, ∀ y ∈ dyadicGridCell G Q.1 Q.2,
      ∀ z ∈ dyadicGridCell G Q.1 Q.2, g y = g z := by
  intro Q hQ y hy z hz
  have hd := dyadicGeneration_depth G I n hQ
  have hg' := hg.mono hk
  rw [← hd] at hg'
  exact hg' Q.2 y hy z hz

/-- `∫_Q E_k F = ∫_Q F` on cells `Q` of depth at most `k`. -/
theorem setIntegral_depthExpectation_of_le (G : RealDyadicGrid) (Q : ℤ × ℤ) {k : ℤ}
    (hk : Q.1 ≤ k) {F : ℝ → ℂ} (hF : IntegrableOn F (dyadicGridCell G Q.1 Q.2)) :
    ∫ y in dyadicGridCell G Q.1 Q.2, depthExpectation G k F y =
      ∫ y in dyadicGridCell G Q.1 Q.2, F y := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = Q.1 + n := ⟨(k - Q.1).toNat, by omega⟩
  rw [hn]
  exact setIntegral_depthExpectation G Q n hF

variable {V : Type*} [Fintype V]

/-- A bounded measurable cell-supported test as an `L²` class. -/
theorem cellRow_memLp {G : RealDyadicGrid} {ι : Type} (R : CellRowFamily G ι) (i : ι) :
    MemLp (R.test i) 2 volume := by
  obtain ⟨C, hC⟩ := R.bounded i
  have hs := dyadicGridCell_measurable G (R.cell i).1 (R.cell i).2
  have heq : (dyadicGridCell G (R.cell i).1 (R.cell i).2).indicator (R.test i) = R.test i := by
    funext y
    by_cases hy : y ∈ dyadicGridCell G (R.cell i).1 (R.cell i).2
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, R.local_support i y hy]
  rw [← heq]
  refine (memLp_indicator_iff_restrict hs).mpr ?_
  have := cell_isFiniteMeasure G (R.cell i).1 (R.cell i).2
  exact MemLp.of_bound (R.measurable i).aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem cellRow_inner_Lp {G : RealDyadicGrid} {ι : Type} (R : CellRowFamily G ι) (i : ι)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ ((cellRow_memLp R i).toLp (R.test i)) g = ∫ y, conj (R.test i y) * g y := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (cellRow_memLp R i)] with y h1
  rw [h1, RCLike.inner_apply, mul_comm]

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Path-uniform column systems -/

/-- A path-uniform column system on the complete finite tree of depth `N` below `J`: labels
reused across disjoint branches, inherited cellwise availability, cellwise bounded scalars that
agree along paths, and private weights in `(0, 1]` (blueprint sec:columns, lines 470-483, in the
form used by prop:base). -/
structure PathColumnSystem (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (V : Type) [Fintype V] where
  /-- Available column labels at each point of a dyadic path. -/
  avail : ℤ × ℤ → Finset V
  /-- Scalar column function at each cell and label. -/
  scalarAt : ℤ × ℤ → V → ℝ → ℂ
  /-- Normalization weight of a path column label. -/
  weight : V → ℝ
  weight_pos : ∀ v, 0 < weight v
  weight_le : ∀ v, weight v ≤ 1
  scalar_meas : ∀ c v, Measurable (scalarAt c v)
  scalar_bound : ∀ c v y, ‖scalarAt c v y‖ ≤ 1
  avail_mono : ∀ c d, c ∈ dyadicFiniteTree G J N → d ∈ dyadicFiniteTree G J N →
    dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G d.1 d.2 → avail d ⊆ avail c
  consistent : ∀ c d, c ∈ dyadicFiniteTree G J N → d ∈ dyadicFiniteTree G J N →
    dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G d.1 d.2 → ∀ v ∈ avail d,
      ∀ y ∈ dyadicGridCell G c.1 c.2, scalarAt c v y = scalarAt d v y

/-- The leaf of the tree of depth `N` below `J` containing `y`. -/
noncomputable def pathLeaf (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (y : ℝ) : ℤ × ℤ :=
  (J.1 + N, dyadicIndex G (J.1 + N) y)

/-- The part below `R` of the tree of depth `N` below `J`. -/
noncomputable def pathBelow (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (R : ℤ × ℤ) :
    Finset (ℤ × ℤ) :=
  dyadicFiniteTree G R (dyadicRemainingDepth J N R)

namespace PathColumnSystem
variable {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {V : Type} [Fintype V]
  (P : PathColumnSystem G J N V)

/-- The scalar of label `v`, read off at the leaf below `y` (and at `R` outside `R`). -/
noncomputable def scalar (R : ℤ × ℤ) (v : V) (y : ℝ) : ℂ :=
  by classical exact
    if y ∈ dyadicGridCell G R.1 R.2 then P.scalarAt (pathLeaf G J N y) v y else P.scalarAt R v y

theorem scalar_bound' (R : ℤ × ℤ) (v : V) (y : ℝ) : ‖P.scalar R v y‖ ≤ 1 := by
  classical
  unfold scalar
  split_ifs
  · exact P.scalar_bound _ _ _
  · exact P.scalar_bound _ _ _

theorem below_mem_iff {R : ℤ × ℤ} (hR : R ∈ dyadicFiniteTree G J N) (c : ℤ × ℤ) :
    c ∈ pathBelow G J N R ↔
      c ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G c.1 c.2 ⊆ dyadicGridCell G R.1 R.2 :=
  dyadicFiniteTree_below_iff G J N hR c

theorem leaf_mem (y : ℝ) : y ∈ dyadicGridCell G (pathLeaf G J N y).1
    (pathLeaf G J N y).2 := mem_dyadicIndex G _ y

/-- The budget of the system. -/
noncomputable def budget : ℝ := 2 + Fintype.card V + ∑ v, (Real.sqrt (P.weight v))⁻¹

theorem two_le_budget : 2 ≤ P.budget := by
  unfold budget
  have : 0 ≤ ∑ v, (Real.sqrt (P.weight v))⁻¹ := Finset.sum_nonneg fun v _ => by positivity
  have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  linarith

end PathColumnSystem

/-! ### Opponent algebra and delayed opponents -/

/-- Admissibility only sees each opponent on its own cell. -/
theorem IsAdmissibleOpponent.congr_cell {G : RealDyadicGrid} {J : ℤ × ℤ} {F : ℝ → ℂ}
    {z z' : ℤ × ℤ → ℝ → ℂ} {K : ℝ} (h : IsAdmissibleOpponent G J F z K)
    (hz : ∀ I : ℤ × ℤ, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2 →
      ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → z' I y = z I y) :
    IsAdmissibleOpponent G J F z' K := by
  intro ι R hR
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) (h ι R hR)
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [hz (R.cell i) (hR i hi)] with y hy
  by_cases hyc : y ∈ dyadicGridCell G (R.cell i).1 (R.cell i).2
  · rw [hy hyc]
  · rw [R.local_support i y hyc]; simp

theorem cellRow_integrable {G : RealDyadicGrid} {ι : Type} (R : CellRowFamily G ι) (i : ι)
    {z : ℝ → ℂ} (hz : MemLp z 2 (volume.restrict (dyadicGridCell G (R.cell i).1 (R.cell i).2))) :
    Integrable (fun y => conj (R.test i y) * z y) := by
  have hs := dyadicGridCell_measurable G (R.cell i).1 (R.cell i).2
  have := cell_isFiniteMeasure G (R.cell i).1 (R.cell i).2
  obtain ⟨C, hC⟩ := R.bounded i
  have heq : (fun y => conj (R.test i y) * z y) =
      (dyadicGridCell G (R.cell i).1 (R.cell i).2).indicator
        (fun y => conj (R.test i y) * z y) := by
    funext y
    by_cases hy : y ∈ dyadicGridCell G (R.cell i).1 (R.cell i).2
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, R.local_support i y hy]; simp
  rw [heq, integrable_indicator_iff hs]
  have hz1 : IntegrableOn z (dyadicGridCell G (R.cell i).1 (R.cell i).2) :=
    hz.integrable one_le_two
  refine (hz1.bdd_mul (c := C)
    ((Complex.continuous_conj.measurable.comp (R.measurable i)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_))
  simp only [Complex.norm_conj]; exact hC y

theorem norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  calc ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Sums of admissible opponents are admissible. -/
theorem IsAdmissibleOpponent.add {G : RealDyadicGrid} {J : ℤ × ℤ} {F : ℝ → ℂ}
    {z₁ z₂ : ℤ × ℤ → ℝ → ℂ} {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : IsAdmissibleOpponent G J F z₁ K₁) (h₂ : IsAdmissibleOpponent G J F z₂ K₂)
    (hm₁ : ∀ I, MemLp (z₁ I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hm₂ : ∀ I, MemLp (z₂ I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) :
    IsAdmissibleOpponent G J F (fun I y => z₁ I y + z₂ I y) (2 * (K₁ + K₂)) := by
  intro ι R hR
  set E := ∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2 with hEdef
  have hE : 0 ≤ E := integral_nonneg fun _ => by positivity
  set a₁ := fun i => ∫ y, conj (R.test i y) * z₁ (R.cell i) y
  set a₂ := fun i => ∫ y, conj (R.test i y) * z₂ (R.cell i) y
  have e1 : ∑ i ∈ R.index, ‖a₁ i‖ ^ 2 ≤ K₁ ^ 2 * R.bound ^ 2 * E := h₁ ι R hR
  have e2 : ∑ i ∈ R.index, ‖a₂ i‖ ^ 2 ≤ K₂ ^ 2 * R.bound ^ 2 * E := h₂ ι R hR
  have hsplit : ∀ i, ∫ y, conj (R.test i y) * (z₁ (R.cell i) y + z₂ (R.cell i) y) =
      a₁ i + a₂ i := by
    intro i
    rw [← integral_add (cellRow_integrable R i (hm₁ _)) (cellRow_integrable R i (hm₂ _))]
    simp only [mul_add]
  have hB : 0 ≤ R.bound ^ 2 * E := mul_nonneg (sq_nonneg _) hE
  have hK : 2 * K₁ ^ 2 + 2 * K₂ ^ 2 ≤ (2 * (K₁ + K₂)) ^ 2 := by
    nlinarith [mul_nonneg hK₁ hK₂]
  change ∑ i ∈ R.index, ‖∫ y, conj (R.test i y) * (z₁ (R.cell i) y + z₂ (R.cell i) y)‖ ^ 2 ≤
    (2 * (K₁ + K₂)) ^ 2 * R.bound ^ 2 * E
  simp only [hsplit]
  calc ∑ i ∈ R.index, ‖a₁ i + a₂ i‖ ^ 2
      ≤ ∑ i ∈ R.index, (2 * ‖a₁ i‖ ^ 2 + 2 * ‖a₂ i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => norm_add_sq_le_two _ _
    _ = 2 * ∑ i ∈ R.index, ‖a₁ i‖ ^ 2 + 2 * ∑ i ∈ R.index, ‖a₂ i‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (2 * K₁ ^ 2 + 2 * K₂ ^ 2) * (R.bound ^ 2 * E) := by nlinarith
    _ ≤ (2 * (K₁ + K₂)) ^ 2 * (R.bound ^ 2 * E) := mul_le_mul_of_nonneg_right hK hB
    _ = (2 * (K₁ + K₂)) ^ 2 * R.bound ^ 2 * E := by ring

/-- Sums of opponents with depth energy have depth energy. -/
theorem HasDepthEnergy.add {G : RealDyadicGrid} {J : ℤ × ℤ} {F : ℝ → ℂ}
    {z₁ z₂ : ℤ × ℤ → ℝ → ℂ} {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : HasDepthEnergy G J F z₁ K₁) (h₂ : HasDepthEnergy G J F z₂ K₂)
    (hm₁ : ∀ I, MemLp (z₁ I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hm₂ : ∀ I, MemLp (z₂ I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) :
    HasDepthEnergy G J F (fun I y => z₁ I y + z₂ I y) (2 * (K₁ + K₂)) := by
  intro s S hS
  have e1 := h₁ s S hS
  have e2 := h₂ s S hS
  have hE : 0 ≤ ∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  calc ∑ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, ‖z₁ I y + z₂ I y‖ ^ 2
      ≤ ∑ I ∈ S, (2 * (∫ y in dyadicGridCell G I.1 I.2, ‖z₁ I y‖ ^ 2) +
          2 * (∫ y in dyadicGridCell G I.1 I.2, ‖z₂ I y‖ ^ 2)) := by
        refine Finset.sum_le_sum fun I _ => ?_
        rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add ((hm₁ I).integrable_norm_pow two_ne_zero |>.const_mul _)
            ((hm₂ I).integrable_norm_pow two_ne_zero |>.const_mul _)]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          (((hm₁ I).integrable_norm_pow two_ne_zero |>.const_mul _).add
            ((hm₂ I).integrable_norm_pow two_ne_zero |>.const_mul _))
          (Filter.Eventually.of_forall fun y => norm_add_sq_le_two _ _)
    _ = 2 * (∑ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, ‖z₁ I y‖ ^ 2) +
          2 * (∑ I ∈ S, ∫ y in dyadicGridCell G I.1 I.2, ‖z₂ I y‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (K₁ ^ 2 * (∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2)) +
          2 * (K₂ ^ 2 * (∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2)) := by linarith
    _ = (2 * K₁ ^ 2 + 2 * K₂ ^ 2) * (∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2) := by ring
    _ ≤ (2 * (K₁ + K₂)) ^ 2 * ∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) hE

/-! ### Predictor approximation and delayed replacement for one low pair -/

/-- The approximation property `eq:predictors` of a predictor list for the chart pair
`(A, A')` in slots `i, k`, against admissible opponents in slots `a, b`. -/
def PredictorApprox (κ : LocalKernelClass) {d e : ℕ} (A : QuadraticChartData d)
    (A' : QuadraticChartData e) (a i k b : Fin 4) (B : ℝ) {ι : Type} (L : Finset ι)
    (ψa ψb : ι → QuadraticChartData (d + e)) (lam : ι → ℝ) (coef : ι → ℝ → ℂ) : Prop :=
  ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ)),
    (∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2) →
    ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ I ∈ S, IsAdmissibleLocalKernel κ
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
    ∀ {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ}, 0 ≤ Ka → 0 ≤ Kb →
    IsAdmissibleOpponent G J Fa za Ka → IsAdmissibleOpponent G J Fb zb Kb →
    HasDepthEnergy G J Fa za Ka → HasDepthEnergy G J Fb zb Kb →
    (∀ I, Measurable (za I)) → (∀ I, Measurable (zb I)) →
    (∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
    (∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) →
    ∀ (f : ℤ × ℤ → Fin 4 → ℝ → ℂ), (∀ I, f I a = za I) →
    (∀ I, f I i = quadraticChartAtom A) → (∀ I, f I k = quadraticChartAtom A') →
    (∀ I, f I b = zb I) →
    ∑ I ∈ S, dyadicGridLength G I.1 *
      ‖localProgressionForm (dyadicGridLength G I.1) (w I) (f I) -
        ∑ ℓ ∈ L, coef ℓ (dyadicGridLength G I.1) *
          separatedLocalForm (dyadicGridLength G I.1) (w I)
            (fun t => (Real.fourierChar (lam ℓ * t ^ 2) : ℂ)) a b
            (fun y => za I y * quadraticChartAtom (ψa ℓ) y)
            (fun y => zb I y * quadraticChartAtom (ψb ℓ) y)‖ ≤
      Real.exp (-B) * Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)

/-- Blueprint lem:predictors (`THT.Base.finitePredictorList`) in the packaged form used by
prop:base. -/
theorem finitePredictorList_approx (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ c₁ C : ℕ, 1 ≤ c₁ ∧ ∀ {d e : ℕ} (H B : ℝ) (A : QuadraticChartData d)
      (A' : QuadraticChartData e), 1 ≤ d → 1 ≤ e → QuadraticChartComplexity c₀ H A →
      QuadraticChartComplexity c₀ H A' → IsBoundedQuadraticChart A →
      IsBoundedQuadraticChart A' → 1 ≤ B →
      ∀ {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
      ∃ (ι : Type) (L : Finset ι) (ψa ψb : ι → QuadraticChartData (d + e)) (lam : ι → ℝ)
        (coef : ι → ℝ → ℂ),
        (L.card : ℝ) ≤ Real.exp (C * (1 + B + Real.log H) ^ C) ∧
        (∀ ℓ ∈ L, IsBoundedQuadraticChart (ψa ℓ) ∧ IsBoundedQuadraticChart (ψb ℓ) ∧
          QuadraticChartComplexity c₁ (Real.exp (C * (1 + B + Real.log H) ^ C)) (ψa ℓ) ∧
          QuadraticChartComplexity c₁ (Real.exp (C * (1 + B + Real.log H) ^ C)) (ψb ℓ)) ∧
        (∀ r, ∑ ℓ ∈ L, ‖coef ℓ r‖ ≤ Real.exp (C * (1 + B + Real.log H) ^ C)) ∧
        (∀ ℓ r, coef ℓ r ≠ 0 → |lam ℓ| * r ^ 2 ≤ Real.exp (C * (1 + B + Real.log H) ^ C)) ∧
        PredictorApprox κ A A' a i k b B L ψa ψb lam coef := by
  obtain ⟨c₁, C, hc₁, h⟩ := finitePredictorList c₀ hc κ
  refine ⟨c₁, C, hc₁, fun H B A A' hd he hA hA' hAb hA'b hB a i k b h1 h2 h3 h4 h5 h6 => ?_⟩
  obtain ⟨ι, L, ψa, ψb, lam, coef, hcard, hbd, hcoef, hlam, happ⟩ :=
    h H B A A' hd he hA hA' hAb hA'b hB h1 h2 h3 h4 h5 h6
  exact ⟨ι, L, ψa, ψb, lam, coef, hcard, hbd, hcoef, hlam, fun G J S hS w hw => happ G J S hS w hw⟩

/-- The four inputs `(z_a, φ, φ', z_b)` placed in the slots `a, i, k, b`. -/
noncomputable def slots4 (a i k : Fin 4) (za φ φ' zb : ℝ → ℂ) : Fin 4 → ℝ → ℂ :=
  fun l => by classical exact if l = a then za else if l = i then φ else if l = k then φ' else zb

theorem slots4_a {a i k : Fin 4} (za φ φ' zb : ℝ → ℂ) : slots4 a i k za φ φ' zb a = za := by
  simp [slots4]

theorem slots4_i {a i k : Fin 4} (hai : a ≠ i) (za φ φ' zb : ℝ → ℂ) :
    slots4 a i k za φ φ' zb i = φ := by
  simp [slots4, Ne.symm hai]

theorem slots4_k {a i k : Fin 4} (hak : a ≠ k) (hik : i ≠ k) (za φ φ' zb : ℝ → ℂ) :
    slots4 a i k za φ φ' zb k = φ' := by
  simp [slots4, Ne.symm hak, Ne.symm hik]

theorem slots4_b {a i k b : Fin 4} (hab : a ≠ b) (hib : i ≠ b) (hkb : k ≠ b) (za φ φ' zb : ℝ → ℂ) :
    slots4 a i k za φ φ' zb b = zb := by
  simp [slots4, Ne.symm hab, Ne.symm hib, Ne.symm hkb]

theorem IsAdmissibleOpponent.mono {G : RealDyadicGrid} {J : ℤ × ℤ} {F : ℝ → ℂ}
    {z : ℤ × ℤ → ℝ → ℂ} {K K' : ℝ} (h : IsAdmissibleOpponent G J F z K) (hK : 0 ≤ K)
    (hKK : K ≤ K') : IsAdmissibleOpponent G J F z K' := by
  intro ι R hR
  refine (h ι R hR).trans ?_
  have hE : 0 ≤ ∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2 := integral_nonneg fun _ => by positivity
  have : K ^ 2 ≤ K' ^ 2 := pow_le_pow_left₀ hK hKK 2
  have := mul_nonneg (sq_nonneg R.bound) hE
  nlinarith

theorem HasDepthEnergy.mono {G : RealDyadicGrid} {J : ℤ × ℤ} {F : ℝ → ℂ}
    {z : ℤ × ℤ → ℝ → ℂ} {K K' : ℝ} (h : HasDepthEnergy G J F z K) (hK : 0 ≤ K)
    (hKK : K ≤ K') : HasDepthEnergy G J F z K' := by
  intro s S hS
  refine (h s S hS).trans ?_
  have hE : 0 ≤ ∫ y in dyadicGridCell G J.1 J.2, ‖F y‖ ^ 2 := integral_nonneg fun _ => by positivity
  have : K ^ 2 ≤ K' ^ 2 := pow_le_pow_left₀ hK hKK 2
  nlinarith

/-! ### The predictor high system -/

/-- A predictor list for a chart pair with budget `D` (blueprint lem:predictors). -/
structure PredictorPackage (κ : LocalKernelClass) {d e : ℕ} (A : QuadraticChartData d)
    (A' : QuadraticChartData e) (a i k b : Fin 4) (B D : ℝ) (c₁ : ℕ) where
  /-- Index type for the finite family of predictors. -/
  ι : Type
  /-- Finite set of predictor indices used by the package. -/
  L : Finset ι
  /-- First chart factor of each separated predictor. -/
  ψa : ι → QuadraticChartData (d + e)
  /-- Second chart factor of each separated predictor. -/
  ψb : ι → QuadraticChartData (d + e)
  /-- Scalar quadratic phase coefficient of each predictor. -/
  lam : ι → ℝ
  /-- Scale-dependent coefficient of each predictor. -/
  coef : ι → ℝ → ℂ
  card_le : (L.card : ℝ) ≤ D
  bdd : ∀ ℓ ∈ L, IsBoundedQuadraticChart (ψa ℓ) ∧ IsBoundedQuadraticChart (ψb ℓ) ∧
    QuadraticChartComplexity c₁ D (ψa ℓ) ∧ QuadraticChartComplexity c₁ D (ψb ℓ)
  coef_le : ∀ r, ∑ ℓ ∈ L, ‖coef ℓ r‖ ≤ D
  lam_le : ∀ ℓ r, coef ℓ r ≠ 0 → |lam ℓ| * r ^ 2 ≤ D
  approx : PredictorApprox κ A A' a i k b B L ψa ψb lam coef

/-- lem:predictors provides packages for all admissible chart pairs. -/
theorem predictorPackage_nonempty (c₀ : ℕ) (hc : 1 ≤ c₀) (κ : LocalKernelClass) :
    ∃ c₁ C : ℕ, 1 ≤ c₁ ∧ ∀ {d e : ℕ} (H B : ℝ) (A : QuadraticChartData d)
      (A' : QuadraticChartData e), 1 ≤ d → 1 ≤ e → QuadraticChartComplexity c₀ H A →
      QuadraticChartComplexity c₀ H A' → IsBoundedQuadraticChart A →
      IsBoundedQuadraticChart A' → 1 ≤ B →
      ∀ {a i k b : Fin 4}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i ≠ b → k ≠ b →
      Nonempty (PredictorPackage κ A A' a i k b B
        (Real.exp (C * (1 + B + Real.log H) ^ C)) c₁) := by
  obtain ⟨c₁, C, hc₁, h⟩ := finitePredictorList_approx c₀ hc κ
  refine ⟨c₁, C, hc₁, fun H B A A' hd he hA hA' hAb hA'b hB a i k b h1 h2 h3 h4 h5 h6 => ?_⟩
  obtain ⟨ι, L, ψa, ψb, lam, coef, hcard, hbd, hcoef, hlam, happ⟩ :=
    h H B A A' hd he hA hA' hAb hA'b hB h1 h2 h3 h4 h5 h6
  exact ⟨⟨ι, L, ψa, ψb, lam, coef, hcard, hbd, hcoef, hlam, happ⟩⟩

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Bridges for the replacement -/

theorem memLp_normalized_of_cell {a r : ℝ} {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Set.Ico a (a + r)))) :
    MemLp g 2 (normalizedIntervalMeasure a r) := by
  unfold normalizedIntervalMeasure
  rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
  exact hg.smul_measure ENNReal.ofReal_ne_top

end TrilinearHT.Auto

end
