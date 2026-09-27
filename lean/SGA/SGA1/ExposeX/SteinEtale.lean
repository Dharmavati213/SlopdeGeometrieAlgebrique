/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.SteinEtale
import SGA.SGA1.ExposeX.Product

/-!
# SGA 1, Exposé X, 1.2: the Stein factorization of a proper separable morphism is étale

X.1.2 (EGA III 7.8.10 (i)) is proved in `SGA.Foundations.Cohomology.SteinEtale`
(`AlgebraicGeometry.etale_fromNormalization`) by cohomology and base change in
degree `0` (EGA III 7.7–7.8): over a noetherian local base, `Γ(X, 𝒪_X)` is free and its reduction
is `Γ(X_k, 𝒪)`, a geometrically reduced, hence étale, algebra over the residue field. This file
proves `SteinFactorizationEtaleStatement` and hence, through `CoveringOfBase` and `Product`,
X.1.3 (`coveringOfBaseStatement`), X.1.4 (`range_map_eq_ker_map_and_surjective`) and X.1.7
(`bijective_map_prod`, for a rational base point and `X` reduced).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- X.1.2 (EGA III 7.8.10 (i)): for `f : X ⟶ Y` proper and separable with `Y` locally noetherian,
the finite part `Y' = Spec_Y f_* 𝒪_X ⟶ Y` of the Stein factorization (mathlib's relative
normalization of `Y` in `X`) is étale. -/
theorem etale_fromNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f]
    [IsLocallyNoetherian Y] : Etale f.fromNormalization :=
  AlgebraicGeometry.etale_fromNormalization f

/-- X.1.2: the Stein factorization `X ⟶ Y' ⟶ Y` of a proper separable morphism, `Y` locally
noetherian, has `Y'` finite and étale over `Y`. -/
theorem steinFactorizationEtaleStatement : SteinFactorizationEtaleStatement.{u} :=
  steinFactorizationEtaleStatement_of_etale_fromNormalization fun _ _ f _ _ _ ↦
    etale_fromNormalization f

/-- X.1.3: for `f : X ⟶ Y` proper and separable with `f_* 𝒪_X = 𝒪_Y`, `Y` locally noetherian and
connected, a connected étale covering of `X` comes from an étale covering of `Y` iff its
geometric fibre over a point `y` has a section. -/
theorem coveringOfBaseStatement : CoveringOfBaseStatement.{u} :=
  coveringOfBaseStatement_of_steinFactorizationEtaleStatement steinFactorizationEtaleStatement

/-- X.1.4, the homotopy exact sequence `π₁(X̄_y, a) → π₁(X, a) → π₁(Y, a) → e` for `f : X ⟶ Y`
proper and separable with `f_* 𝒪_X = 𝒪_Y`, `Y` locally noetherian and connected, `y ∈ Y` and
`a` a geometric point of the geometric fibre `X̄_y`: the image of `π₁(X̄_y, a) → π₁(X, a)` is
the kernel of `π₁(X, a) → π₁(Y, a)`, and the latter is surjective. -/
theorem range_map_eq_ker_map_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsSeparable f] [IsLocallyNoetherian Y] [ConnectedSpace Y]
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f (geometricPoint Y y)) :
    (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPoint Y y)) a).range =
        (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))).ker ∧
      Function.Surjective
        (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))) :=
  homotopyExactSequence steinFactorizationEtaleStatement f hf y Ω a

/-- X.1.7 (for a rational base point and `X` reduced; SGA reduces to this case by passing to
`X_red`): for `k` algebraically closed, `X` proper, connected and reduced over `k`, `Y` locally
noetherian and connected over `k`, and `c` a rational point of `X ×ₖ Y`, the map
`π₁(X ×ₖ Y, c) → π₁(X, c) × π₁(Y, c)` is an isomorphism. -/
theorem bijective_map_prod {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsProper sX] [IsReduced X]
    [ConnectedSpace X] [IsLocallyNoetherian Y] [ConnectedSpace Y]
    (c : Spec (.of k) ⟶ pullback sX sY) (hc : c ≫ pullback.snd sX sY ≫ sY = 𝟙 _) :
    Function.Bijective ((ExposeV.etaleFundamentalGroup.map k (pullback.fst sX sY) c).prod
      (ExposeV.etaleFundamentalGroup.map k (pullback.snd sX sY) c)) :=
  bijective_map_prod_of_steinFactorizationEtaleStatement sX sY steinFactorizationEtaleStatement c
    hc

end SGA.SGA1.ExposeX
