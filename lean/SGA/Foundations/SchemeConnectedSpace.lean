/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Connectedness of schemes along isomorphisms

An isomorphism of schemes is a homeomorphism of the underlying spaces
(`AlgebraicGeometry.Scheme.Hom.homeomorph`), so connectedness transfers along it
(`AlgebraicGeometry.Scheme.connectedSpace_of_iso`). This is used to compute that fibre products
such as `U ×_X Spec 𝒪^{sh}_{X,x̄}` are connected by identifying them with spectra of domains.

Reference: EGA I (2nd ed.), 2.1 (isomorphisms of ringed spaces).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A scheme isomorphic to a connected scheme is connected. -/
lemma connectedSpace_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z) [ConnectedSpace Z] : ConnectedSpace Y :=
  (Homeomorph.connectedSpace_iff (Scheme.Hom.homeomorph e.hom)).mpr inferInstance

end AlgebraicGeometry.Scheme
