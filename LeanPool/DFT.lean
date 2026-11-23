/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques, Stefano Pittalis
-/

module

public import LeanPool.DFT.Lattice.Generic.DensityDim.Fermions
public import LeanPool.DFT.Lattice.Generic.ShortestPathSign
public import LeanPool.DFT.Lattice.Generic.SignGauge
public import LeanPool.DFT.Lattice.KohnSham.Hypersimplex
public import LeanPool.DFT.Lattice.KohnSham.RegularizedKS

/-!
# Density-functional theory for lattice fermions

Source: url:https://github.com/hyllios/lean_dft/tree/144b0dca3e597f2ae021f1c1b263ceab857f8f26
Authors: Miguel A. L. Marques, Stefano Pittalis
Status: verified
Main declarations: `DFT.generic_hk_lattice_fermions_w`, `DFT.dimH_nonUVDens_lattice_fermions_w`,
  `DFT.ks_potential_exists_interior`, `DFT.lattice_myksoda`
Tags: density-functional-theory, spinless-fermions, convex-optimization
MSC: 81V55, 81Q10, 90C25
-/
