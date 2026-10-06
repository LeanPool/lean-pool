/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.StretchingBounds
public import LeanPool.CIVAxisymmetric.Identities.StretchingIdentity

/-!
# Stretching Split

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Finset
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The vortex-stretching term `∑ᵢ ∑ⱼ ωⱼ ∂ⱼ uᵢ ωᵢ` splits into `stretchGTerm` and
`stretchAngularSwirl`: the former is the "G-term" (first three terms of `eq:aniso:closure:stretch`
plus the `∂_z u_r` mixed term), the latter is the angular swirl factor `u_θ · (ω_r / r)`.
The proof moves to the meridional representative via `exists_rotZ_polarR` and
`stretching_rotZ_invariant`,
applies `stretching_meridional` to expand the sum, then unfolds the two definitions and uses
`radialQuotient`'s `hoff` branch to match by `ring`. -/
theorem stretching_eq_stretchGTerm {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {x : Vec3} {t : ℝ}
    (hz : ((x, t) : ParabolicPoint) ∈ unitCylinder) (hoff : polarR x ≠ 0) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        curlComp u j (x, t) * spatialPartial (fun w => u w i) j (x, t) * curlComp u i (x, t)
      = stretchGTerm u x t
        + spatialPartial (fun w => u w 2) 0 (meridional (polarR x) (x 2), t)
            * curlComp u 0 (meridional (polarR x) (x 2), t)
            * curlComp u 2 (meridional (polarR x) (x 2), t)
        - 2 * stretchAngularSwirl u x t * curlComp u 1 (meridional (polarR x) (x 2), t) := by
  set rep : Vec3 := meridional (polarR x) (x 2) with hrep
  have hrep_axis : rep 1 = 0 := by
    simp [hrep, meridional]
  have hrep_rad : rep 0 = polarR x := by
    simp [hrep, meridional]
  have hrep_rad_ne : rep 0 ≠ 0 := by rw [hrep_rad]; exact hoff
  have hzrep : (rep, t) ∈ unitCylinder := by
    obtain ⟨φ, hxeq⟩ := exists_rotZ_polarR x
    have hz' : ((rotZ φ rep : Vec3), t) ∈ unitCylinder := by
      rw [← hxeq]
      exact hz
    exact (rotZ_mem_unitCylinder_iff φ rep t).1 hz'
  obtain ⟨φ, hxeq⟩ := exists_rotZ_polarR x
  conv_lhs => rw [hxeq]
  rw [stretching_rotZ_invariant haxi hu hzrep φ]
  rw [stretching_meridional haxi hu hzrep hrep_axis hrep_rad_ne]
  unfold stretchGTerm
  unfold stretchAngularSwirl
  have h_rad_u : radialQuotient u (rep, t) = u (rep, t) 0 / rep 0 := by
    unfold radialQuotient
    split_ifs with h
    · exact absurd h hrep_rad_ne
    · rfl
  have h_rad_vort : radialQuotient (vorticityField u) (rep, t) = vorticityField u (rep, t) 0 /
    rep 0 := by
    unfold radialQuotient
    split_ifs with h
    · exact absurd h hrep_rad_ne
    · rfl
  have h_vort_zero : vorticityField u (rep, t) 0 = curlComp u 0 (rep, t) := rfl
  rw [h_rad_u, h_rad_vort, h_vort_zero, hrep_rad]
  rw [hrep]
  simp [meridional]
  ring

end CIV
