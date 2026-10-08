/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialSecondPartial
public import Mathlib.MeasureTheory.Function.EssSup

/-!
# Integer Sobolev spaces `H^m(U)` on open subsets of `ℝ³`

The local Sobolev space `H^m(U) = W^{m,2}(U)` used in
`lem:local-heat-gain` and `lem:local-div-curl` of the Escauriaza–Seregin–Šverák
manuscript, and `lem:vorticity-products` of that manuscript. It consists of
the functions
in `L²(U)` whose weak partial derivatives through order `m` lie in `L²(U)`.

A derivative of order `k` is indexed by an ordered word `α = [j₁, …, j_k]` of
coordinate directions, and denotes `∂_{j_k} ⋯ ∂_{j₁}`: the first letter is
applied first. A *Sobolev family* of `f` through order `m` on `U` is a map `D`
from words to functions such that `D []` is `f`, every `D α` with
`α.length ≤ m` is square integrable on `U`, and `D (α ++ [j])` is the weak
`j`-th partial derivative of `D α` on `U`. The squared norm is the sum of
`∫_U (D α)²` over all words of length at most `m`, each ordered word counted
once. Since `Σ_{|α| = k} |ξ^α|² = |ξ|^{2k}` over ordered words, this is the
integer Sobolev norm `Σ_{k ≤ m} ‖∇^k f‖²_{L²(U)}`.

For a fixed `f`, weak derivatives on an open set are unique almost everywhere,
so the norm does not depend on the family. The intrinsic norm `hNormOn` is the
infimum over families, with value `⊤` when `f ∉ H^m(U)`, for a finite family
of components indexed by a finite type (scalar, vector or tensor fields).

A time-dependent field in `L²(I; H^m(U))` is represented by a jointly square
integrable family of its spatial distributional derivatives on `U × I`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The ordered derivative words of length at most `m`. -/
@[expose]
def sobolevWords (m : ℕ) : Finset (List (Fin 3)) :=
  (Finset.range (m + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → Fin 3)).image List.ofFn

/-- A word lies in `sobolevWords m` exactly when its length is at most `m`. -/
theorem mem_sobolevWords {m : ℕ} {α : List (Fin 3)} :
    α ∈ sobolevWords m ↔ α.length ≤ m := by
  constructor
  · intro h
    simp only [sobolevWords, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and] at h
    obtain ⟨k, hk, σ, rfl⟩ := h
    rw [List.length_ofFn]
    omega
  · intro h
    simp only [sobolevWords, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨α.length, by omega, α.get, List.ofFn_get α⟩

/-- The classical derivative along a word, `wordDeriv [j₁, …, j_k] f =
∂_{j_k} ⋯ ∂_{j₁} f`. -/
@[expose]
def wordDeriv : List (Fin 3) → (Vec3 → ℝ) → Vec3 → ℝ
  | [], f => f
  | j :: α, f => wordDeriv α (spatialDeriv f j)

/-- `D` is a Sobolev family of `f` through order `m` on `U`: `D []` is `f`
almost everywhere on `U`, each `D α` with `α.length ≤ m` is in `L²(U)`, and
`D (α ++ [j])` is the weak `j`-th partial derivative of `D α` on `U`. -/
structure IsSobolevFamilyOn (m : ℕ) (U : Set Vec3) (f : Vec3 → ℝ)
    (D : List (Fin 3) → Vec3 → ℝ) : Prop where
  zero : D [] =ᵐ[volume.restrict U] f
  memL2 : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 (volume.restrict U)
  weak : ∀ (α : List (Fin 3)) (j : Fin 3), α.length < m →
    HasWeakPartialDerivOn U j (D α) (D (α ++ [j]))

/-- The squared `H^m(U)` norm of a Sobolev family: the sum of the squared
`L²(U)` norms of all ordered derivatives through order `m`. -/
@[expose]
def sobolevNormSqOn (m : ℕ) (U : Set Vec3) (D : List (Fin 3) → Vec3 → ℝ) : ℝ :=
  ∑ α ∈ sobolevWords m, ∫ x in U, D α x ^ 2

/-- Membership in `H^m(U)`. -/
@[expose]
def MemSobolevOn (m : ℕ) (U : Set Vec3) (f : Vec3 → ℝ) : Prop :=
  ∃ D : List (Fin 3) → Vec3 → ℝ, IsSobolevFamilyOn m U f D

/-- The `H^m(U)` norm of a field with finitely many components, indexed by
`ι`: the infimum of `(Σ_i ‖D_i‖²_{H^m(U)})^{1/2}` over Sobolev families `D_i`
of the components, and `⊤` if some component is not in `H^m(U)`. -/
@[expose]
def hNormOn {ι : Type*} [Fintype ι] (m : ℕ) (U : Set Vec3) (f : ι → Vec3 → ℝ) : ℝ≥0∞ :=
  ⨅ (D : ι → List (Fin 3) → Vec3 → ℝ) (_ : ∀ i, IsSobolevFamilyOn m U (f i) (D i)),
    ENNReal.ofReal (Real.sqrt (∑ i, sobolevNormSqOn m U (D i)))

/-- The components of a vector field, as the argument of `hNormOn`. -/
@[expose]
def vecComponents (v : Vec3 → Vec3) : Fin 3 → Vec3 → ℝ := fun i x => v x i

/-- The components of the tensor product `v ⊗ v`, as the argument of
`hNormOn`. -/
@[expose]
def tensorSquareComponents (v : Vec3 → Vec3) : Fin 3 × Fin 3 → Vec3 → ℝ :=
  fun ij x => v x ij.1 * v x ij.2

/-- `z ∈ L²(I; H^m(U))`, with derivative family `D`: each `D α` with
`α.length ≤ m` is square integrable on `U × I`, `D []` is `z` almost
everywhere on `U × I`, and `D (α ++ [j])` is the distributional `j`-th spatial
derivative of `D α` on `U × I`. A field in `L²(U × I)` whose spatial
distributional derivatives through order `m` are in `L²(U × I)` is exactly an
element of `L²(I; H^m(U))`. -/
structure IsL2SobolevFamilyOn (m : ℕ) (U : Set Vec3) (I : Set ℝ) (z : Vec3 × ℝ → ℝ)
    (D : List (Fin 3) → Vec3 × ℝ → ℝ) : Prop where
  memL2 : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 (volume.restrict (U ×ˢ I))
  zero : D [] =ᵐ[volume.restrict (U ×ˢ I)] z
  weak : ∀ (α : List (Fin 3)) (j : Fin 3), α.length < m →
    ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U ×ˢ I →
      ∫ p in U ×ˢ I, D α p * spatialPartial φ j p =
        -∫ p in U ×ˢ I, D (α ++ [j]) p * φ p

/-- The squared `L²(I; H^m(U))` norm of a space-time derivative family. -/
@[expose]
def l2SobolevNormSqOn (m : ℕ) (U : Set Vec3) (I : Set ℝ)
    (D : List (Fin 3) → Vec3 × ℝ → ℝ) : ℝ :=
  ∑ α ∈ sobolevWords m, ∫ p in U ×ˢ I, D α p ^ 2

/-- `z` solves `∂ₜ z - Δ z = G` in distributions on `U × I`. -/
@[expose]
def IsHeatSolutionOn (U : Set Vec3) (I : Set ℝ) (z G : Vec3 × ℝ → ℝ) : Prop :=
  ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ U ×ˢ I →
    ∫ y in U ×ˢ I, z y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
      ∫ y in U ×ˢ I, G y * ψ y

/-- `div v = 0` and `curl v = ζ` in distributions on `U`, where
`(curl v)_k = ∂_{k+1} v_{k+2} - ∂_{k+2} v_{k+1}` with indices mod `3`. -/
@[expose]
def IsWeakDivCurlOn (U : Set Vec3) (v ζ : Vec3 → Vec3) : Prop :=
  (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x in U, ∑ i : Fin 3, v x i * spatialDeriv φ i x = 0) ∧
  (∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∀ k : Fin 3,
      ∫ x in U, ζ x k * φ x =
        ∫ x in U, (v x (k + 1) * spatialDeriv φ (k + 2) x -
          v x (k + 2) * spatialDeriv φ (k + 1) x))

/-- The zero field solves the homogeneous heat equation. -/
theorem isHeatSolutionOn_zero (U : Set Vec3) (I : Set ℝ) :
    IsHeatSolutionOn U I (fun _ => 0) (fun _ => 0) := by
  intro ψ _ _ _
  simp

/-- The zero field is divergence free with zero curl. -/
theorem isWeakDivCurlOn_zero (U : Set Vec3) :
    IsWeakDivCurlOn U (fun _ => 0) (fun _ => 0) :=
  ⟨fun φ _ _ _ => by simp, fun φ _ _ _ k => by simp⟩

/-- The zero function lies in every `H^m(U)`. -/
theorem memSobolevOn_zero (m : ℕ) (U : Set Vec3) : MemSobolevOn m U (fun _ => 0) := by
  refine ⟨fun _ _ => 0, ⟨Filter.EventuallyEq.rfl, fun _ _ => MemLp.zero, ?_⟩⟩
  intro α j _ φ _ _ _
  simp

end CKN
