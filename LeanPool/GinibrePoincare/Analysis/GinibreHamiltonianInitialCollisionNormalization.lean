/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianInitialCollisionNormalization.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianGaussianCoordinateLaw
public import LeanPool.GinibrePoincare.Analysis.CollisionNull

/-!
# Ginibre Hamiltonian initial collision normalization

Part of the ginibre stochastic dynamics development of the
Ginibre Poincaré formalization.

Main results: `ginibreInitialCollisionNormalize_measurable`,
`ginibreInitialCollisionNormalize_of_free`, `ginibreGaussian_coordinates_collisionFree_ae`.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- A fixed collision-free configuration, placing particle `j` at the point `(j : ℂ)`. -/
def ginibreCollisionFreeDefault (n : ℕ) : {z : Configuration n // CollisionFree z} :=
  ⟨fun j => (j.val : ℂ), by
    intro i j hij
    apply Fin.ext
    change (i.val : ℂ) = (j.val : ℂ) at hij
    exact_mod_cast hij⟩
local instance ginibreInitialCollisionNormalization_nonempty (n : ℕ) :
    Nonempty {z : Configuration n // CollisionFree z} := ⟨ginibreCollisionFreeDefault n⟩

theorem ginibreInitialCollisionEmbedding (n : ℕ) :
    MeasurableEmbedding (Subtype.val : {z : Configuration n // CollisionFree z} → Configuration n)
        :=
  MeasurableEmbedding.subtype_coe (isOpen_collisionFree n).measurableSet

/-- A left inverse (`Function.invFun`) of the inclusion of collision-free configurations: it
keeps collision-free configurations and sends the others to some collision-free point. -/
def ginibreInitialCollisionNormalize (n : ℕ) : Configuration n → {z : Configuration n //
    CollisionFree z} :=
  (ginibreInitialCollisionEmbedding n).invFun

theorem ginibreInitialCollisionNormalize_measurable (n : ℕ) :
    Measurable (ginibreInitialCollisionNormalize n) :=
  (ginibreInitialCollisionEmbedding n).measurable_invFun

theorem ginibreInitialCollisionNormalize_of_free {n : ℕ} (z : Configuration n) (hz : CollisionFree
    z) :
    ginibreInitialCollisionNormalize n z = ⟨z, hz⟩ :=
  (ginibreInitialCollisionEmbedding n).leftInverse_invFun ⟨z, hz⟩

theorem ginibreGaussian_coordinates_collisionFree_ae {n : ℕ} (hn : 0 < n) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2)),
      CollisionFree (ginibreHamiltonianOUCoordinateAssembly n x) := by
  have hCF : ∀ᵐ z ∂complexGaussianMeasure n, CollisionFree z := by
    rw [ae_iff]
    have he : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      simp only [Set.mem_ofPred_eq, collisionFree_iff_not_mem_collisionSet, not_not]
    rw [he]
    exact complexGaussianMeasure_collisionSet n
  have hp : MeasurePreserving (ginibreHamiltonianOUCoordinateAssembly n)
      (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))) (complexGaussianMeasure n) :=
    ⟨(ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable,
        ginibreGaussian_coordinate_assembly_law hn⟩
  exact hp.quasiMeasurePreserving.ae hCF

end
end GinibrePoincare
