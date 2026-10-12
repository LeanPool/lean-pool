/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/

module

public import LeanPool.LiebThirring.Theorems.Baxter
public import LeanPool.LiebThirring.Theorems.KineticEnergySchwartz
public import LeanPool.LiebThirring.Theorems.KineticLiebThirring
public import LeanPool.LiebThirring.Theorems.StabilityOfMatter
public import LeanPool.LiebThirring.Theorems.StabilityOfMatterReal

/-!
# Stability of matter and the kinetic Lieb–Thirring inequality

Source: arxiv:2007.09326, url:https://github.com/scottnarmstrong/LiebThirring/tree/8bf4656f07f5aaa227b0b850d77b16976915bbd4
Authors: Scott Armstrong, Amélie Loher
Status: verified
Main declarations: `LiebThirring.stability_of_matter`
Tags: mathematical-physics, stability-of-matter, lieb-thirring, coulomb-energy, fourier-analysis
MSC: 81Q10, 35P15, 46N50
-/

/-!
# Stability of non-relativistic Coulomb matter

The stability, kinetic and electrostatic dependency closure from Armstrong and Loher.
Imported from
https://github.com/scottnarmstrong/LiebThirring/tree/8bf4656f07f5aaa227b0b850d77b16976915bbd4.
The upstream ionization, thermodynamic-limit and Thomas–Fermi developments are separate from this
scope.

The kinetic and stability formulations follow Frank, arXiv:2007.09326, Section 2.
The explicit Rumin coefficient and Baxter correction follow Lundholm’s lecture notes,
Theorems 6.1 and 7.2; this import does not assert an optimal kinetic constant.
Lundholm’s notes: https://www.math.lmu.de/~lundholm/methmmp.pdf.

Scott Armstrong acknowledges ERC grant No. 101200828. Amélie Loher acknowledges support from the
Fondation Sciences Mathématiques de Paris.
-/
