/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Coordinate representatives on the Fourier velocity carrier

Coordinate fields in the Leray space J can be transferred to the Hilbert
space used by the Fourier transform.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The continuous linear map that realizes coordinate vectors in the Hilbert `L²` model. -/
@[expose]
def coordinateToHilbertValueBridge : Vec3 →L[ℝ] L2Vec3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

/-- The continuous linear map that reads a Hilbert `L²` vector in coordinates. -/
@[expose]
def hilbertToCoordinateValue : L2Vec3 →L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ) |>.toContinuousLinearMap

/-- The measure-preserving transfer from coordinate-valued `L²` functions to real Hilbert-valued
`L²` functions. -/
@[expose]
def coordinateL2Transfer :
    Lp (α := Vec3) Vec3 2 volume →L[ℝ] RealVectorL2 :=
  (coordinateToHilbertValueBridge.compLpL 2 volume).comp
    ((Lp.compMeasurePreservingₗᵢ ℝ
      (WithLp.ofLp : L2Vec3 → Vec3)
      (PiLp.volume_preserving_ofLp (Fin 3))).toContinuousLinearMap)

/-- The bounded map from coordinate velocity L² to the Hilbert velocity L². -/
@[expose]
def realVectorL2OfCoordinateLp (u : Lp (α := Vec3) Vec3 2 volume) : RealVectorL2 :=
  coordinateL2Transfer u

/-- The transferred class has coordinate representative equal to the input. -/
theorem realVectorL2OfCoordinateLp_rep
    (u : Lp (α := Vec3) Vec3 2 volume) :
    realVectorL2Representative (realVectorL2OfCoordinateLp u) =ᵐ[volume] u := by
  have hdomain : Lp.compMeasurePreserving (WithLp.ofLp : L2Vec3 → Vec3)
      (PiLp.volume_preserving_ofLp (Fin 3)) u =ᵐ[volume]
      fun x : L2Vec3 => u (WithLp.ofLp x) :=
    Lp.coeFn_compMeasurePreserving u (PiLp.volume_preserving_ofLp (Fin 3))
  have hvalue : coordinateToHilbertValueBridge.compLpL 2 volume
      (Lp.compMeasurePreserving (WithLp.ofLp : L2Vec3 → Vec3)
        (PiLp.volume_preserving_ofLp (Fin 3)) u) =ᵐ[volume]
      fun x => coordinateToHilbertValueBridge
        (Lp.compMeasurePreserving (WithLp.ofLp : L2Vec3 → Vec3)
          (PiLp.volume_preserving_ofLp (Fin 3)) u x) :=
    ContinuousLinearMap.coeFn_compLpL
      (L := coordinateToHilbertValueBridge) (p := 2) (μ := volume) _
  have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hvalue
  have hdomTransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hdomain
  filter_upwards [htransport, hdomTransport] with x hx hd
  change hilbertToCoordinateValue
      ((coordinateToHilbertValueBridge.compLpL 2 volume
        (Lp.compMeasurePreserving (WithLp.ofLp : L2Vec3 → Vec3)
          (PiLp.volume_preserving_ofLp (Fin 3)) u)) (WithLp.toLp 2 x)) = u x
  rw [hx, hd]
  simp [hilbertToCoordinateValue, coordinateToHilbertValueBridge,
    PiLp.continuousLinearEquiv]

theorem coordinateFunction_memLp (a : Vec3 → Vec3)
    (ha : MemLp a 2 volume) :
    MemLp (fun y : L2Vec3 => coordinateToHilbertValueBridge (a (WithLp.ofLp y)))
      2 volume := by
  have hcoord : MemLp (fun y : L2Vec3 => a (WithLp.ofLp y)) 2 volume :=
    ha.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
  exact hcoord.continuousLinearMap_comp coordinateToHilbertValueBridge

/-- Transfer a coordinate L² representative to the Hilbert-space velocity
carrier used by Fourier analysis. -/
@[expose]
def realVectorL2OfCoordinateFunction (a : Vec3 → Vec3)
    (ha : MemLp a 2 volume) : RealVectorL2 :=
  (coordinateFunction_memLp a ha).toLp
    (fun y : L2Vec3 => coordinateToHilbertValueBridge (a (WithLp.ofLp y)))

/-- The transferred L² field has the prescribed coordinate representative. -/
theorem realVectorL2OfCoordinateFunction_rep
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume) :
    realVectorL2Representative (realVectorL2OfCoordinateFunction a ha) =ᵐ[volume] a := by
  have hLp := (coordinateFunction_memLp a ha).coeFn_toLp
  have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hLp
  filter_upwards [htransport] with x hx
  change hilbertToCoordinateValue
      ((coordinateFunction_memLp a ha).toLp
        (fun y : L2Vec3 => coordinateToHilbertValueBridge (a (WithLp.ofLp y)))
        (WithLp.toLp 2 x)) = a x
  rw [hx]
  simp [hilbertToCoordinateValue, coordinateToHilbertValueBridge,
    PiLp.continuousLinearEquiv]

/-- Equality of coordinate representatives determines a real velocity L²
class. -/
theorem realVectorL2Representative_injective_ae
    {u v : RealVectorL2}
    (h : realVectorL2Representative u =ᵐ[volume]
      realVectorL2Representative v) : u = v := by
  apply Lp.ext
  have h' := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae h
  filter_upwards [h'] with x hx
  have hx' : hilbertToCoordinateValue (u x) = hilbertToCoordinateValue (v x) := by
    simpa [realVectorL2Representative, hilbertToCoordinateValue] using hx
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).injective hx'

/-- Reconstructing a Hilbert-space velocity field from its coordinate
representative returns the original field. -/
theorem realVectorL2OfCoordinateFunction_representation
    (u : RealVectorL2) :
    realVectorL2OfCoordinateFunction (realVectorL2Representative u)
      (by
        have hcoord : MemLp
            (fun x : Vec3 => u (WithLp.toLp 2 x)) 2 volume :=
          (Lp.memLp u).comp_measurePreserving vec3ToL2Vec3_measurePreserving
        change MemLp (fun x : Vec3 =>
          hilbertToCoordinateValue (u (WithLp.toLp 2 x))) 2 volume
        exact hcoord.continuousLinearMap_comp hilbertToCoordinateValue) = u := by
  apply realVectorL2Representative_injective_ae
  simpa using realVectorL2OfCoordinateFunction_rep
    (realVectorL2Representative u) _

end CKN.Leray

end
