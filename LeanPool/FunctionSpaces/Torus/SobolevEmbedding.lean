/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.SobolevTriebelLizorkin
public import LeanPool.FunctionSpaces.Torus.Embeddings

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev embeddings on the torus

Let `d ≥ 1` and `1 < p < ∞`. Through `W^m_p(𝕋^d) ⊆ B^m_{p,max(p,2)}(𝕋^d)` for `m ≥ 1`
(`Torus.memBesov_of_memSobolev`) the Besov embeddings of the torus
(`FunctionSpaces.Torus.Embeddings`) give, with `α = d (1/p - 1/r)`:

* **into `L_r`** (`Torus.memSobolev_exists_inclusion_eq`): for `p ≤ r ≤ ∞` and `m > α`, every
  `f ∈ W^m_p(𝕋^d)` lies in `L_r(𝕋^d)` and in `B^{m - α}_{r,max(p,2)}(𝕋^d)`;
* **into continuous functions** (`Torus.memSobolev_exists_continuous`): for `m > d/p`, every
  `f ∈ W^m_p(𝕋^d)` has a continuous representative;
* **between Sobolev spaces** (`Torus.memSobolev_of_memSobolev_of_lt`): for `p ≤ r < ∞` and
  `k < m - α`, `W^m_p(𝕋^d) ⊆ W^k_r(𝕋^d)`, through `B^{m - α}_{r,max(p,2)} ⊆ B^k_{r,min(r,2)}`
  (`ApproximationScheme.MemApprox.of_lt`) and `B^k_{r,min(r,2)} ⊆ W^k_r`
  (`Torus.memSobolev_of_memBesov`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal TorusHaar

namespace Torus

variable {d : Type*} [Fintype d] {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- **The Sobolev embedding into `L_r` on the torus**: for `d ≥ 1`, `1 < p < ∞`, `p ≤ r ≤ ∞` and
`m > d (1/p - 1/r)`, every `f ∈ W^m_p(𝕋^d)` is the class in `L_p` of some `g ∈ L_r(𝕋^d)`, and
`g` lies in the Besov space `B^{m - d(1/p - 1/r)}_{r,max(p,2)}(𝕋^d)`
(`Torus.memBesov_of_memSobolev` and `Torus.memBesov_exists_inclusion_eq`). The order satisfies
`m ≥ 1` since `d (1/p - 1/r) ≥ 0`. -/
theorem memSobolev_exists_inclusion_eq [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) (hpr : p ≤ r)
    {m : ℕ} (hm : (Fintype.card d : ℝ) * (p.toReal⁻¹ - r.toReal⁻¹) < m)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume hpr g = f ∧
        (trigScheme d).MemBesov volume r
          ((m : ℝ) - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹)) (max p 2) g :=
  memBesov_exists_inclusion_eq hpr hm (le_max_of_le_right one_le_two)
    (memBesov_of_memSobolev hp1 hp
      (one_le_of_nikolskiiExponent_lt (Nat.cast_nonneg _) Fact.out hpr hm) hf)

/-- **The Sobolev embedding into continuous functions on the torus**: for `d ≥ 1`, `1 < p < ∞`
and `m > d/p`, every `f ∈ W^m_p(𝕋^d)` has a continuous representative
(`Torus.memBesov_of_memSobolev` and `Torus.memBesov_exists_continuous`). -/
theorem memSobolev_exists_continuous [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (hm : (Fintype.card d : ℝ) * p.toReal⁻¹ < m)
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemSobolev m f) :
    ∃ g : C(UnitAddTorus d, ℂ),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume le_top (ContinuousMap.toLp (E := ℂ) ∞ volume ℝ g) =
        f :=
  memBesov_exists_continuous hm (le_max_of_le_right one_le_two)
    (memBesov_of_memSobolev hp1 hp (Nat.cast_pos.1 (lt_of_le_of_lt (by positivity) hm)) hf)

/-- **The embeddings between Sobolev spaces on the torus**: for `d ≥ 1`, `1 < p ≤ r < ∞` and
orders `k < m - d (1/p - 1/r)`, every `f ∈ W^m_p(𝕋^d)` is the class in `L_p` of some
`g ∈ W^k_r(𝕋^d)`. The class `g ∈ B^{m - d(1/p - 1/r)}_{r,max(p,2)}(𝕋^d)` of
`Torus.memSobolev_exists_inclusion_eq` lies in `B^k_{r,min(r,2)}(𝕋^d)` since `k` is smaller
(`ApproximationScheme.MemApprox.of_lt`), hence in `W^k_r(𝕋^d)` (`Torus.memSobolev_of_memBesov`). -/
theorem memSobolev_of_memSobolev_of_lt [Nonempty d] (hp1 : 1 < p) (hp : p ≠ ∞) (hpr : p ≤ r)
    (hr : r ≠ ∞) {k m : ℕ}
    (hkm : (k : ℝ) < m - Fintype.card d * (p.toReal⁻¹ - r.toReal⁻¹))
    {f : Lp ℂ p (volume : Measure (UnitAddTorus d))} (hf : MemSobolev m f) :
    ∃ g : Lp ℂ r (volume : Measure (UnitAddTorus d)),
      Lp.inclusionOfExponentLe (𝕜 := ℝ) volume hpr g = f ∧ MemSobolev k g := by
  have hm : (Fintype.card d : ℝ) * (p.toReal⁻¹ - r.toReal⁻¹) < m := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨g, hgf, hg⟩ := memSobolev_exists_inclusion_eq hp1 hp hpr hm hf
  exact ⟨g, hgf, memSobolev_of_memBesov (hp1.trans_le hpr) hr
    (hg.of_lt (le_max_of_le_right one_le_two) (le_min Fact.out one_le_two) (Nat.cast_nonneg k)
      hkm)⟩

end Torus
