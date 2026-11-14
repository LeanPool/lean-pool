/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.MainTheorems
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.DisplacementExpectations
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.DisplacementIntegrability
public import LeanPool.Superdiffusion.Algsuperdiff.SuperdiffusivityFiniteMoments

/-!
# Superdiffusion and anomalous regularization in self-similar random flows

Source: arxiv:2601.22142, url:https://github.com/scottnarmstrong/Superdiffusion
Authors: Scott Armstrong, Tuomo Kuusi
Status: verified
Main declarations: `Algsuperdiff.superdiffusivity_with_finite_moments`
Tags: superdiffusion, stochastic-homogenization, random-incompressible-flows, anomalous-regularity
MSC: 60K37, 35B27, 60J60
-/
