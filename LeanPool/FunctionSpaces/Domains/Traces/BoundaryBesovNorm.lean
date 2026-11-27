/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Traces.LipschitzBoundaryTrace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov quasi-norms on the boundary of a bounded Lipschitz domain

Let `Ω` be a bounded Lipschitz domain with boundary `Γ`, charts `γ_j : H_j → V` and a smooth
resolution of unity `(ψ_j)` on `Γ` (`Rd.BoundedLipschitzDomain.BoundaryPartition`). Let
`1 ≤ p < ∞`, `0 < s < 1` and `1 ≤ q ≤ ∞`.

* **The quasi-norm** (`Rd.BoundedLipschitzDomain.boundaryBesovNorm`): the chart definition
  on domains of dimension at least two is in Schneider–Vybíral, Definition 3.3. See also Triebel
  2002. Here `‖g‖_{B^s_{p,q}(Γ)}` is the sum over the charts of
  `‖G_j‖_{L_p(H_j)} + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q}` for the chart pieces
  `G_j = (ψ_j g) ∘ γ_j` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_sum`). It is finite
  exactly on `B^s_{p,q}(Γ)`
  (`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundaryBesovNorm_lt_top`), sees `g` only
  almost everywhere on `Γ`, and it is subadditive and homogeneous.
* **The trace is bounded** (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`):
  `‖Tr_Γ F‖_{B^s_{p,q}(Γ)} ≤ C (‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q})`, chart by chart
  (`Rd.LipschitzGraph.exists_modNorm_trace_mulLp_le`).
* **The extension is bounded** (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`): every
  `g ∈ B^s_{p,q}(Γ)` is `Tr_Γ F` almost everywhere on `Γ` for an `F` with
  `‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C ‖g‖_{B^s_{p,q}(Γ)}`, namely
  `F = ∑_j ζ_j E_j G_j` (`Rd.LipschitzGraph.exists_modNorm_mulLp_graphExtension_le`).
* **Independence of the resolution of unity**
  (`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_le_of_partition`): two resolutions
  of unity give equivalent quasi-norms.

The constants depend on `Ω`, `ψ`, `p`, `s`, `q` and `L` and are fixed before the functions; the
bounds give ambient-space estimates for the chart construction of the trace and its extension.
Schneider–Vybíral, Theorems 4.2 and 4.10, give bounded-domain estimates in dimension at least two.
-/

@[expose] public section

open MeasureTheory Filter Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

/-! ### The extension in one chart -/

namespace LipschitzGraph

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : LipschitzGraph V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The localised extension is bounded**: for `1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞`, `L ≥ 2`
and a smooth `ζ` with derivatives bounded by `M` up to order `L`, there is `K < ∞` with
`‖ζ E g‖_p + ‖(2^(k(s+1/p)) ω_L(ζ E g, 2^(-k))_p)_k‖_{ℓ_q} ≤
K (‖g‖_p + ‖(2^(ks) ω_1(g, 2^(-k))_p)_k‖_{ℓ_q})` for every `g ∈ B^s_{p,q}(H)`, with
`K = M_ζ 2^(L-2) K_E`: the multiplier bound (`Rd.modNorm_mulLp_le`), the change of the order of the
differences (`Rd.modNorm_order_le_of_le`) and the bound of the extension
(`Rd.LipschitzGraph.modNorm_graphExtension_le`). -/
theorem exists_modNorm_mulLp_graphExtension_le (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) {ζ : V → ℂ}
    (hζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ) {M : ℝ}
    (hM : ∀ l ≤ L, ∀ x, ‖iteratedFDeriv ℝ l ζ x‖ ≤ M) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ g : Lp ℂ p (volume : Measure Ω.hyperplane),
      ‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k) < ∞ →
      ‖mulLp hζ.continuous (norm_le_of_iteratedFDeriv_le hM) (Ω.graphExtension hp 1 g)‖ₑ +
          lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * lpModulus p L
            (mulLp hζ.continuous (norm_le_of_iteratedFDeriv_le hM) (Ω.graphExtension hp 1 g)) k) ≤
        K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k)) := by
  have hsL := add_one_div_toReal_lt hp hs1 hL
  obtain ⟨K, hK, hle⟩ := Ω.modNorm_graphExtension_le hp hs hs1 hq
  refine ⟨multiplierTotal (V := V) hp L (s + 1 / p.toReal) M * 2 ^ (L - 2) * K,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (multiplierTotal_ne_top hp hsL M) (by simp)) hK,
    fun g hg => ?_⟩
  calc _ ≤ multiplierTotal (V := V) hp L (s + 1 / p.toReal) M *
        (‖Ω.graphExtension hp 1 g‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k *
          lpModulus p L (Ω.graphExtension hp 1 g) k)) := modNorm_mulLp_le hp hζ hM hsL hq _
    _ ≤ multiplierTotal (V := V) hp L (s + 1 / p.toReal) M *
        (2 ^ (L - 2) * (‖Ω.graphExtension hp 1 g‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p 2 (Ω.graphExtension hp 1 g) k))) :=
        mul_le_mul' le_rfl (modNorm_order_le_of_le hL _ q _)
    _ ≤ multiplierTotal (V := V) hp L (s + 1 / p.toReal) M * (2 ^ (L - 2) *
        (K * (‖g‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 g k)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (hle g hg))
    _ = _ := by ring

end LipschitzGraph

namespace BoundedLipschitzDomain

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (Ω : BoundedLipschitzDomain V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The quasi-norm -/

variable (p) in
/-- **The Besov quasi-norm on the boundary**. This uses the chart formula of
Schneider–Vybíral, Definition 3.3, with Lebesgue measure on the hyperplanes and also
allows dimension one for the domain. For a resolution of unity `ψ`,
`‖g‖_{B^s_{p,q}(Γ)} = ∑_j (‖G_j‖_{L_p(H_j)} + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})` for the
chart pieces `G_j ∈ L_p(H_j)` with `G_j = (ψ_j g) ∘ γ_j` almost everywhere on `H_j`. Each infimum
runs over at most one element of `L_p(H_j)`, the class of the chart piece, and is `∞` if the chart
piece is not in `L_p(H_j)` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_sum`). -/
noncomputable def boundaryBesovNorm (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) (g : V → ℂ) :
    ℝ≥0∞ :=
  ∑ j, ⨅ (G : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (_ : (G : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')),
    (‖G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 G k))

/-- **The quasi-norm is at most the sum for chart pieces**: for `G_j = (ψ_j g) ∘ γ_j` almost
everywhere on `H_j`,
`‖g‖_{B^s_{p,q}(Γ)} ≤ ∑_j (‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})`. -/
theorem boundaryBesovNorm_le_sum (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} {g : V → ℂ}
    (G : ∀ j, Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (hG : ∀ j, (G j : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) :
    Ω.boundaryBesovNorm p ψ s q g ≤
      ∑ j, (‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) :=
  Finset.sum_le_sum fun j _ => iInf₂_le (G j) (hG j)

/-- **The quasi-norm is the sum for chart pieces**: for `G_j = (ψ_j g) ∘ γ_j` almost everywhere on
`H_j`, `‖g‖_{B^s_{p,q}(Γ)} = ∑_j (‖G_j‖_p + ‖(2^(ks) ω_1(G_j, 2^(-k))_p)_k‖_{ℓ_q})`, since two
elements of `L_p(H_j)` that agree almost everywhere are equal. -/
theorem boundaryBesovNorm_eq_sum (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} {g : V → ℂ}
    (G : ∀ j, Lp ℂ p (volume : Measure (Ω.graph j).hyperplane))
    (hG : ∀ j, (G j : (Ω.graph j).hyperplane → ℂ) =ᵐ[volume]
      fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) :
    Ω.boundaryBesovNorm p ψ s q g =
      ∑ j, (‖G j‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p 1 (G j) k)) := by
  refine le_antisymm (Ω.boundaryBesovNorm_le_sum ψ G hG)
    (Finset.sum_le_sum fun j _ => le_iInf₂ fun G' hG' => ?_)
  rw [Lp.ext ((hG j).trans hG'.symm)]

/-- **The quasi-norm is finite exactly on `B^s_{p,q}(Γ)`**: `g ∈ B^s_{p,q}(Γ)` iff
`‖g‖_{B^s_{p,q}(Γ)} < ∞`. -/
theorem memBoundaryBesov_iff_boundaryBesovNorm_lt_top (ψ : Ω.BoundaryPartition) {s : ℝ}
    {q : ℝ≥0∞} (g : V → ℂ) :
    Ω.MemBoundaryBesov p ψ s q g ↔ Ω.boundaryBesovNorm p ψ s q g < ∞ := by
  constructor
  · intro hg
    choose G hG hGfin using hg
    rw [Ω.boundaryBesovNorm_eq_sum ψ G hG]
    exact ENNReal.sum_lt_top.2 fun j _ => hGfin j
  · intro h j
    obtain ⟨G, hG⟩ := iInf_lt_iff.1 (ENNReal.sum_lt_top.1 h j (Finset.mem_univ j))
    obtain ⟨hGg, hGfin⟩ := iInf_lt_iff.1 hG
    exact ⟨G, hGg, hGfin⟩

/-- **The quasi-norm is infinite outside `B^s_{p,q}(Γ)`**: if `g ∉ B^s_{p,q}(Γ)`, then
`‖g‖_{B^s_{p,q}(Γ)} = ∞`
(`Rd.BoundedLipschitzDomain.memBoundaryBesov_iff_boundaryBesovNorm_lt_top`). -/
theorem boundaryBesovNorm_eq_top_of_not_mem (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    {g : V → ℂ} (hg : ¬ Ω.MemBoundaryBesov p ψ s q g) : Ω.boundaryBesovNorm p ψ s q g = ∞ :=
  not_lt_top_iff.1 fun h => hg ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).2 h)

/-- **The quasi-norm sees `g` only almost everywhere on `Γ`**: if `g = h` almost everywhere on
`Γ`, then `‖g‖_{B^s_{p,q}(Γ)} = ‖h‖_{B^s_{p,q}(Γ)}`. -/
theorem boundaryBesovNorm_congr (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} {g h : V → ℂ}
    (hgh : g =ᶠ[Ω.aeBoundary] h) :
    Ω.boundaryBesovNorm p ψ s q g = Ω.boundaryBesovNorm p ψ s q h := by
  refine Finset.sum_congr rfl fun j _ => iInf_congr fun G => ?_
  have hj := chart_ae_eq_of_eventuallyEq ψ hgh j
  exact iInf_congr_Prop ⟨fun hG => hG.trans hj, fun hG => hG.trans hj.symm⟩ fun _ => rfl

/-- The quasi-norm of `0` vanishes. -/
theorem boundaryBesovNorm_zero (ψ : Ω.BoundaryPartition) (s : ℝ) (q : ℝ≥0∞) :
    Ω.boundaryBesovNorm p ψ s q 0 = 0 := by
  rw [Ω.boundaryBesovNorm_eq_sum ψ (fun _ => 0) fun j => ?_]
  · simp [lpModulus_zero, ENNReal.lqNorm_zero_right]
  · exact (Lp.coeFn_zero ℂ p _).trans (Eventually.of_forall fun x' => by simp)

/-- **The quasi-norm is subadditive on `B^s_{p,q}(Γ)`**: for `q ≥ 1` and
`g, h ∈ B^s_{p,q}(Γ)`, `‖g + h‖_{B^s_{p,q}(Γ)} ≤ ‖g‖_{B^s_{p,q}(Γ)} + ‖h‖_{B^s_{p,q}(Γ)}`; the
chart pieces of `g + h` are the sums of those of `g` and `h` (`Rd.modNorm_add_le`). -/
theorem boundaryBesovNorm_add_le_of_mem (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    (hq : 1 ≤ q) {g h : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g)
    (hh : Ω.MemBoundaryBesov p ψ s q h) :
    Ω.boundaryBesovNorm p ψ s q (g + h) ≤
      Ω.boundaryBesovNorm p ψ s q g + Ω.boundaryBesovNorm p ψ s q h := by
  choose G hG _ using hg
  choose H hH _ using hh
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Ω.boundaryBesovNorm_eq_sum ψ H hH,
    ← Finset.sum_add_distrib]
  refine (Ω.boundaryBesovNorm_le_sum ψ (fun j => G j + H j) fun j => ?_).trans
    (Finset.sum_le_sum fun j _ => modNorm_add_le (G j) (H j) 1 s hq)
  filter_upwards [Lp.coeFn_add (G j) (H j), hG j, hH j] with x' h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.add_apply, mul_add]

/-- **The quasi-norm is subadditive**: for `q ≥ 1` and all functions `g`, `h` on `V`,
`‖g + h‖_{B^s_{p,q}(Γ)} ≤ ‖g‖_{B^s_{p,q}(Γ)} + ‖h‖_{B^s_{p,q}(Γ)}`: for `g, h ∈ B^s_{p,q}(Γ)` by
`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le_of_mem`; otherwise the right side is `∞`
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_top_of_not_mem`). -/
theorem boundaryBesovNorm_add_le (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g h : V → ℂ) :
    Ω.boundaryBesovNorm p ψ s q (g + h) ≤
      Ω.boundaryBesovNorm p ψ s q g + Ω.boundaryBesovNorm p ψ s q h := by
  by_cases hg : Ω.MemBoundaryBesov p ψ s q g
  · by_cases hh : Ω.MemBoundaryBesov p ψ s q h
    · exact Ω.boundaryBesovNorm_add_le_of_mem ψ hq hg hh
    · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hh, add_top]
      exact le_top
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg, top_add]
    exact le_top

variable {Ω} in
/-- `B^s_{p,q}(Γ)` is closed under addition, for `q ≥ 1`
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_add_le`). -/
theorem MemBoundaryBesov.add {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (hq : 1 ≤ q)
    {g h : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) (hh : Ω.MemBoundaryBesov p ψ s q h) :
    Ω.MemBoundaryBesov p ψ s q (g + h) :=
  (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ _).2
    ((Ω.boundaryBesovNorm_add_le ψ hq g h).trans_lt (ENNReal.add_lt_top.2
      ⟨(Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg,
        (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ h).1 hh⟩))

/-- **The quasi-norm is homogeneous on `B^s_{p,q}(Γ)`**: for `c ∈ ℂ` and
`g ∈ B^s_{p,q}(Γ)`, `‖c g‖_{B^s_{p,q}(Γ)} = |c| ‖g‖_{B^s_{p,q}(Γ)}`; the chart pieces of `c g` are
`c G_j` (`Rd.modNorm_const_smul`). -/
theorem boundaryBesovNorm_const_smul_of_mem (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞}
    (c : ℂ) {g : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) :
    Ω.boundaryBesovNorm p ψ s q (c • g) = ‖c‖ₑ * Ω.boundaryBesovNorm p ψ s q g := by
  choose G hG _ using hg
  have hcG : ∀ j, ((c • G j : Lp ℂ p (volume : Measure (Ω.graph j).hyperplane)) :
      (Ω.graph j).hyperplane → ℂ) =ᵐ[volume] fun x' =>
        ψ.toComplex j ((Ω.graph j).graphMap x') * (c • g) ((Ω.graph j).graphMap x') := fun j => by
    filter_upwards [Lp.coeFn_smul c (G j), hG j] with x' h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Finset.mul_sum,
    Ω.boundaryBesovNorm_eq_sum ψ (fun j => c • G j) hcG]
  exact Finset.sum_congr rfl fun j _ => modNorm_const_smul c (G j) 1 s q

variable {Ω} in
/-- `B^s_{p,q}(Γ)` is closed under multiplication by constants
(`Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul_of_mem`). -/
theorem MemBoundaryBesov.const_smul {ψ : Ω.BoundaryPartition} {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    {g : V → ℂ} (hg : Ω.MemBoundaryBesov p ψ s q g) : Ω.MemBoundaryBesov p ψ s q (c • g) := by
  rw [memBoundaryBesov_iff_boundaryBesovNorm_lt_top, Ω.boundaryBesovNorm_const_smul_of_mem ψ c hg]
  exact ENNReal.mul_lt_top eNorm_lt_top
    ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg)

/-- **The quasi-norm is homogeneous**: for `c ∈ ℂ` and every function `g` on `V`,
`‖c g‖_{B^s_{p,q}(Γ)} = |c| ‖g‖_{B^s_{p,q}(Γ)}`. For `c = 0` both sides vanish; for `c ≠ 0`,
`c g ∈ B^s_{p,q}(Γ)` iff `g ∈ B^s_{p,q}(Γ)`, since `g = c⁻¹ (c g)`, and outside the space both
sides are `∞` (`Rd.BoundedLipschitzDomain.boundaryBesovNorm_const_smul_of_mem`,
`Rd.BoundedLipschitzDomain.boundaryBesovNorm_eq_top_of_not_mem`). -/
theorem boundaryBesovNorm_const_smul (ψ : Ω.BoundaryPartition) {s : ℝ} {q : ℝ≥0∞} (c : ℂ)
    (g : V → ℂ) :
    Ω.boundaryBesovNorm p ψ s q (c • g) = ‖c‖ₑ * Ω.boundaryBesovNorm p ψ s q g := by
  by_cases hc : c = 0
  · rw [hc, zero_smul, eNorm_zero, zero_mul]
    exact Ω.boundaryBesovNorm_zero ψ s q
  by_cases hg : Ω.MemBoundaryBesov p ψ s q g
  · exact Ω.boundaryBesovNorm_const_smul_of_mem ψ c hg
  have hcg : ¬ Ω.MemBoundaryBesov p ψ s q (c • g) := fun h => hg (by
    have h' := h.const_smul c⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h')
  rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hcg, Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg,
    ENNReal.mul_top (eNorm_ne_zero.2 hc)]

/-- **Vanishing quasi-norm**: if `‖g‖_{B^s_{p,q}(Γ)} = 0`, then every chart piece
`(ψ_j g) ∘ γ_j` vanishes almost everywhere on `H_j`. -/
theorem chart_ae_eq_zero_of_boundaryBesovNorm_eq_zero (ψ : Ω.BoundaryPartition) {s : ℝ}
    {q : ℝ≥0∞} {g : V → ℂ} (h0 : Ω.boundaryBesovNorm p ψ s q g = 0) (j : Fin Ω.N) :
    (fun x' => ψ.toComplex j ((Ω.graph j).graphMap x') * g ((Ω.graph j).graphMap x')) =ᵐ[volume]
      0 := by
  have hg : Ω.MemBoundaryBesov p ψ s q g :=
    (Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).2 (h0 ▸ ENNReal.zero_lt_top)
  choose G hG _ using hg
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Finset.sum_eq_zero_iff] at h0
  have hG0 : G j = 0 := eNorm_eq_zero.1 (add_eq_zero.1 (h0 j (Finset.mem_univ j))).1
  refine (hG j).symm.trans ?_
  rw [hG0]
  exact Lp.coeFn_zero ℂ p _

/-! ### The bounded trace and the bounded extension -/

/-- **The boundary trace is bounded by the ambient Besov norm**. For
`1 ≤ p < ∞`, `0 < s < 1`, `1 ≤ q ≤ ∞` and `s + 1/p < L` (so `L ≥ 1`), there is `C < ∞` with
`‖Tr_Γ F‖_{B^s_{p,q}(Γ)} ≤ C (‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q})` for every `F`
with a finite right side. The chart pieces of `Tr_Γ F` are the traces `Tr_j(ψ_j F)`
(`Rd.BoundedLipschitzDomain.trace_mulLp_ae_boundaryTrace`), bounded chart by chart
(`Rd.LipschitzGraph.exists_modNorm_trace_mulLp_le`); `C = ∑_j K_j`. -/
theorem exists_boundaryBesovNorm_boundaryTrace_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞)
    {L : ℕ} {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (hsL : s + 1 / p.toReal < L)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
        dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) < ∞ →
      Ω.boundaryBesovNorm p ψ s q (Ω.boundaryTrace ψ hp L F) ≤
        C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k)) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2
    (Nat.cast_pos.1 ((show (0 : ℝ) < s + 1 / p.toReal by positivity).trans hsL)).ne'
  choose M hM using fun j => exists_iteratedFDeriv_bound (ψ.contDiff_toComplex j)
    (ψ.hasCompactSupport_toComplex j) L
  choose K hK hle using fun j =>
    (Ω.graph j).exists_modNorm_trace_mulLp_le hp hs hs1 hsL hq (ψ.contDiff_toComplex j) (hM j)
  refine ⟨∑ j, K j, ENNReal.sum_ne_top.2 fun j _ => hK j, fun F hF => ?_⟩
  rw [Finset.sum_mul]
  exact (Ω.boundaryBesovNorm_le_sum ψ _ fun j =>
    Ω.trace_mulLp_ae_boundaryTrace ψ hp hL hs hsL hq hF j (hM j)).trans
    (Finset.sum_le_sum fun j _ => hle j F hF)

/-- **A bounded extension from the boundary to the ambient space**. For `1 ≤ p < ∞`, `0 < s <
1`, `1 ≤ q ≤ ∞` and `L ≥ 2`, there is `C < ∞` such that every
`g ∈ B^s_{p,q}(Γ)` is `Tr_Γ F` almost everywhere on `Γ` for some `F` with
`‖F‖_p + ‖(2^(k(s+1/p)) ω_L(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C ‖g‖_{B^s_{p,q}(Γ)}`. The function is
`F = ∑_j ζ_j E_j G_j` for the chart pieces `G_j` and the cut-offs `ζ_j`
(`Rd.BoundedLipschitzDomain.boundaryTrace_extensionSum_eventuallyEq`), with the triangle inequality
`Rd.modNorm_finsetSum_le` and the chart bounds
`Rd.LipschitzGraph.exists_modNorm_mulLp_graphExtension_le`; `C = ∑_j K_j`. -/
theorem exists_boundaryTrace_eq_le (ψ : Ω.BoundaryPartition) (hp : p ≠ ∞) {L : ℕ} (hL : 2 ≤ L)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ, Ω.MemBoundaryBesov p ψ s q g →
      ∃ F : Lp ℂ p (volume : Measure V), ‖F‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / p.toReal) k * lpModulus p L F k) ≤
          C * Ω.boundaryBesovNorm p ψ s q g ∧
        Ω.boundaryTrace ψ hp L F =ᶠ[Ω.aeBoundary] g := by
  choose ζ hζs hζc hζB hζ1 using ψ.exists_cutoff
  choose M hM using fun j => exists_iteratedFDeriv_bound (hζs j) (hζc j) L
  choose K hK hle using fun j =>
    (Ω.graph j).exists_modNorm_mulLp_graphExtension_le hp hL hs hs1 hq (hζs j) (hM j)
  refine ⟨∑ j, K j, ENNReal.sum_ne_top.2 fun j _ => hK j, fun g hg => ?_⟩
  choose G hG hGfin using hg
  refine ⟨_, ?_, Ω.boundaryTrace_extensionSum_eventuallyEq ψ hp hL hs hs1 hq hζs hζB hζ1 hM G hG
    hGfin⟩
  rw [Ω.boundaryBesovNorm_eq_sum ψ G hG, Finset.mul_sum]
  refine (modNorm_finsetSum_le _ _ L _ hq).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (hle j (G j) (hGfin j)).trans
    (mul_le_mul' (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)) le_rfl)

/-- **The quasi-norms of two resolutions of unity are equivalent**: for `1 ≤ p < ∞`, `0 < s < 1`
and `1 ≤ q ≤ ∞` and resolutions of unity `ψ`, `ψ'` there is `C < ∞` with
`‖g‖_{B^s_{p,q}(Γ), ψ'} ≤ C ‖g‖_{B^s_{p,q}(Γ), ψ}` for every `g`. For `g ∈ B^s_{p,q}(Γ)`, the
bounded extension for `ψ` (`Rd.BoundedLipschitzDomain.exists_boundaryTrace_eq_le`) gives `F` with
`Tr_Γ F = g`, the boundary traces of `ψ` and `ψ'` agree
(`Rd.BoundedLipschitzDomain.boundaryTrace_eventuallyEq`), and the trace bound for `ψ'`
(`Rd.BoundedLipschitzDomain.exists_boundaryBesovNorm_boundaryTrace_le`) finishes; otherwise the
right side is `∞`. -/
theorem exists_boundaryBesovNorm_le_of_partition (ψ ψ' : Ω.BoundaryPartition)
    (hp : p ≠ ∞) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g : V → ℂ,
      Ω.boundaryBesovNorm p ψ' s q g ≤ C * Ω.boundaryBesovNorm p ψ s q g := by
  have hsL := add_one_div_toReal_lt hp hs1 (le_refl 2)
  obtain ⟨C₁, hC₁, h₁⟩ := Ω.exists_boundaryTrace_eq_le ψ hp le_rfl hs hs1 hq
  obtain ⟨C₂, hC₂, h₂⟩ :=
    Ω.exists_boundaryBesovNorm_boundaryTrace_le ψ' hp hs hs1 hsL hq
  refine ⟨C₂ * C₁ + 1, ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC₂ hC₁, ENNReal.one_ne_top⟩,
    fun g => ?_⟩
  by_cases hg : Ω.MemBoundaryBesov p ψ s q g
  · obtain ⟨F, hFle, hFg⟩ := h₁ g hg
    have hF := hFle.trans_lt (ENNReal.mul_lt_top hC₁.lt_top
      ((Ω.memBoundaryBesov_iff_boundaryBesovNorm_lt_top ψ g).1 hg))
    rw [← Ω.boundaryBesovNorm_congr ψ'
      ((Ω.boundaryTrace_eventuallyEq ψ' ψ hp one_le_two hs hsL hq hF).trans hFg)]
    calc _ ≤ C₂ * (‖F‖ₑ + lqNorm q (fun k =>
          dyadicWeight (s + 1 / (p.toReal)) k * lpModulus p 2 F k)) := h₂ F hF
      _ ≤ C₂ * (C₁ * Ω.boundaryBesovNorm p ψ s q g) := mul_le_mul' le_rfl hFle
      _ ≤ (C₂ * C₁ + 1) * Ω.boundaryBesovNorm p ψ s q g := by
          rw [← mul_assoc]
          exact mul_le_mul' le_self_add le_rfl
  · rw [Ω.boundaryBesovNorm_eq_top_of_not_mem ψ hg, ENNReal.mul_top (by positivity)]
    exact le_top

end BoundedLipschitzDomain

end Rd
