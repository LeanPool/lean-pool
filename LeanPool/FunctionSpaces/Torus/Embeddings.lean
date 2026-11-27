/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Sobolev

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Embedding theorems on the torus

The general embedding theorems of `FunctionSpaces.MeasureSpaces.Besov.Embeddings` and
`FunctionSpaces.MeasureSpaces.Sobolev.Embeddings`, applied to the scheme of trigonometric
polynomials on `𝕋^d`, which has the Nikolskii property of dimension `d`
(`Torus.trigScheme_hasNikolskii`):

* **Besov embedding** (`Torus.memBesov_exists_inclusion_eq`): for `1 ≤ p ≤ r ≤ ∞` and
  `s > d(1/p - 1/r)`, `B^s_{p,q}(𝕋^d) ⊆ B^{s - d(1/p - 1/r)}_{r,q}(𝕋^d)`;
* **into continuous functions** (`Torus.memBesov_exists_continuous`): for `s > d/p`, every
  `f ∈ B^s_{p,q}(𝕋^d)` has a continuous representative;
* **Sobolev embedding** (`Torus.sobolev_exists_continuous`): for `s > d/2`, every
  `f ∈ L_2(𝕋^d)` with `∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞` has a continuous
  representative;
* **`H^s` and Besov spaces** (`Torus.sobolev_memBesov_top`, `Torus.exists_sobolev_of_memBesov`):
  `H^s(𝕋^d) ⊆ B^s_{2,∞}(𝕋^d)` and `B^t_{2,q}(𝕋^d) ⊆ H^s(𝕋^d)` for `t > s`; and
  `H^s(𝕋^d) ⊆ L_r(𝕋^d)` with `B^{s - d(1/2 - 1/r)}_{r,∞}` smoothness for `2 ≤ r` and
  `s > d(1/2 - 1/r)` (`Torus.sobolev_exists_inclusion_eq`).

The torus measure is Mathlib's normalised Haar measure, available as `volume` after
`open scoped TorusHaar`.
-/

@[expose] public section

open MeasureTheory UnitAddTorus FunctionScheme
open scoped ENNReal BoundedContinuousFunction TorusHaar lp

namespace Torus

variable {d : Type*} [Fintype d] {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] {s : ℝ}
  {q : ℝ≥0∞}

/-- A bounded continuous function on the compact torus is a continuous function, with the same
`L_∞` class. -/
theorem toLp_toContinuousMap (a : UnitAddTorus d →ᵇ ℂ) :
    ContinuousMap.toLp (E := ℂ) ∞ volume ℝ a.toContinuousMap =
      BoundedContinuousFunction.toLp (E := ℂ) ∞ volume ℝ a := by
  rw [ContinuousMap.toLp_def]
  congr 1

/-- **The Besov embedding on the torus**: for `1 ≤ p ≤ r ≤ ∞`, `1 ≤ q ≤ ∞` and
`s > d(1/p - 1/r)`, every `f ∈ B^s_{p,q}(𝕋^d)` lies in `L_r` and in
`B^{s - d(1/p - 1/r)}_{r,q}(𝕋^d)`. -/
theorem memBesov_exists_inclusion_eq (hpr : p ≤ r)
    (hs : (Fintype.card d : ℝ) * (p.toReal⁻¹ - r.toReal⁻¹) < s) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : (trigScheme d).MemBesov volume p s q f) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume hpr g = f ∧
        (trigScheme d).MemBesov volume r (s - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) q g :=
  MemBesov.exists_inclusion_eq_of_nikolskii trigScheme_hasNikolskii (Nat.cast_nonneg _) hpr hs hq
    hf

/-- **Besov functions are continuous** for `s > d/p`: every `f ∈ B^s_{p,q}(𝕋^d)` has a
continuous representative. -/
theorem memBesov_exists_continuous (hs : (Fintype.card d : ℝ) * p.toReal⁻¹ < s) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : (trigScheme d).MemBesov volume p s q f) :
    ∃ g : C(UnitAddTorus d, ℂ),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume le_top (ContinuousMap.toLp (E := ℂ) ∞ volume ℝ g) =
        f := by
  obtain ⟨a, ha⟩ :=
    MemBesov.exists_boundedContinuous trigScheme_hasNikolskii (Nat.cast_nonneg _) hs hq hf
  exact ⟨a.toContinuousMap, by rw [toLp_toContinuousMap, ha]⟩

/-- **`H^s(𝕋^d) ⊆ B^s_{2,∞}(𝕋^d)`**, from Jackson's inequality. -/
theorem sobolev_memBesov_top (hs : 0 < s) (c : ℓ²(d → ℤ, ℂ)) :
    (trigScheme d).MemBesov volume 2 s ∞ ((sobolevSpace s hs).incl c) :=
  (sobolevSpace s hs).memApprox_top c

/-- **`B^t_{2,q}(𝕋^d) ⊆ H^s(𝕋^d)` for `t > s`**, from Bernstein's inequality. -/
theorem exists_sobolev_of_memBesov (hs : 0 < s) {t : ℝ} (hst : s < t) (hq : 1 ≤ q)
    {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))} (hf : (trigScheme d).MemBesov volume 2 t q f) :
    ∃ c : ℓ²(d → ℤ, ℂ), (sobolevSpace s hs).incl c = f :=
  (sobolevSpace s hs).exists_eq_of_lt hst hq hf

/-- **The Sobolev embedding into `L_r`** on the torus: for `2 ≤ r ≤ ∞` and
`s > d(1/2 - 1/r)`, every element of `H^s(𝕋^d)` lies in `L_r` and in
`B^{s - d(1/2 - 1/r)}_{r,∞}(𝕋^d)`. -/
theorem sobolev_exists_inclusion_eq (h2r : (2 : ℝ≥0∞) ≤ r) (hs : 0 < s)
    (hsr : (Fintype.card d : ℝ) * ((2 : ℝ≥0∞).toReal⁻¹ - r.toReal⁻¹) < s) (c : ℓ²(d → ℤ, ℂ)) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume h2r g = (sobolevSpace s hs).incl c ∧
        (trigScheme d).MemBesov volume r
          (s - Fintype.card d * ((2 : ℝ≥0∞).toReal⁻¹ - r.toReal⁻¹)) ∞ g :=
  memBesov_exists_inclusion_eq h2r hsr le_top (sobolev_memBesov_top hs c)

/-- **The Sobolev embedding into continuous functions** on the torus: for `s > d/2`, every
`f ∈ L_2(𝕋^d)` with `∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞` has a continuous
representative. -/
theorem sobolev_exists_continuous (hs : (Fintype.card d : ℝ) / 2 < s)
    {f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (hf : Memℓp (fun k => ((((1 + deg k : ℕ) : ℝ) ^ s : ℝ) : ℂ) * mFourierCoeff f k) 2) :
    ∃ g : C(UnitAddTorus d, ℂ),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume le_top (ContinuousMap.toLp (E := ℂ) ∞ volume ℝ g) =
        f := by
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
  obtain ⟨c, rfl⟩ := (mem_range_sobolev_iff s hs0 f).2 hf
  have hs' : (Fintype.card d : ℝ) * (2 : ℝ≥0∞).toReal⁻¹ < (sobolevSpace (d := d) s hs0).order := by
    simpa [div_eq_mul_inv] using hs
  obtain ⟨a, ha⟩ := SobolevSpace.exists_boundedContinuous trigScheme_hasNikolskii
    (Nat.cast_nonneg _) (sobolevSpace s hs0) hs' c
  exact ⟨a.toContinuousMap, by rw [toLp_toContinuousMap, ha]⟩

end Torus
