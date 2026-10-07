/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalDivCurlLocal
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalDivCurlWhole

/-!
# `lem:local-div-curl`

For concentric balls `B_r ⋐ B_R` and `m ∈ {0, 1, 2}`: if `v ∈ H^m(B_R; ℝ³)`,
`div v = 0` and `curl v = ζ ∈ H^m(B_R; ℝ³)`, then
`‖v‖_{H^{m+1}(B_r)} ≤ C (‖ζ‖_{H^m(B_R)} + ‖v‖_{H^m(B_R)})` with `C` depending
only on `m, r, R`; the same estimate holds after taking an `L²` or `L∞` norm
in time.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `lem:local-div-curl`. -/
theorem localDivCurl (m : ℕ) (hm : m ≤ 2) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (v ζ : Vec3 → Vec3),
      hNormOn m (vec3Ball x₀ R) (vecComponents v) < ⊤ →
      hNormOn m (vec3Ball x₀ R) (vecComponents ζ) < ⊤ →
      IsWeakDivCurlOn (vec3Ball x₀ R) v ζ →
      hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents v) ≤
        ENNReal.ofReal C * (hNormOn m (vec3Ball x₀ R) (vecComponents ζ) +
          hNormOn m (vec3Ball x₀ R) (vecComponents v)) := by
  have _hm := hm
  exact localDivCurl_of_whole m hr hrR (divCurl_whole_family m)

/-- `lem:local-div-curl`, the time-norm variants. -/
theorem localDivCurl_time (m : ℕ) (hm : m ≤ 2) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (I : Set ℝ) (v ζ : ℝ → Vec3 → Vec3),
      (∀ᵐ t ∂(volume.restrict I),
        hNormOn m (vec3Ball x₀ R) (vecComponents (v t)) < ⊤ ∧
        hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) < ⊤ ∧
        IsWeakDivCurlOn (vec3Ball x₀ R) (v t) (ζ t)) →
      (∫⁻ t in I, hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents (v t)) ^ 2) ≤
          ENNReal.ofReal C ^ 2 * ∫⁻ t in I,
            (hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) +
              hNormOn m (vec3Ball x₀ R) (vecComponents (v t))) ^ 2 ∧
      essSup (fun t => hNormOn (m + 1) (vec3Ball x₀ r) (vecComponents (v t)))
          (volume.restrict I) ≤
        ENNReal.ofReal C * essSup (fun t =>
          hNormOn m (vec3Ball x₀ R) (vecComponents (ζ t)) +
            hNormOn m (vec3Ball x₀ R) (vecComponents (v t))) (volume.restrict I) := by
  obtain ⟨C, hC, h⟩ := localDivCurl m hm hr hrR
  exact ⟨C, hC, localDivCurl_time_of_pointwise m h⟩

end ESS
