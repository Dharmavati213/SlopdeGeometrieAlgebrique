/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.FiniteLengthModuleCategory
import SGA.SGA2.ExposeIV.LocalCompletionEquivalence

/-!
# Nonlocal finite-length Hom detects locally Artinian modules

Actual restricted Hom is fully faithful on locally Artinian modules over a
noetherian ring. The recovered linear map is defined on actual cyclic
submodules; naturality on finite spans and actual finite images proves both
linearity and agreement with the original natural transformation. Neither
coefficient is assumed finite, and the ring need not be local.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Original additive Hom on the entire finite-length test category. -/
abbrev finiteLengthModuleRepresentations : ModuleCat.{u} R ⥤
    ((FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  preadditiveYoneda ⋙
    (whiskeringLeft (FiniteLengthModuleCat R)ᵒᵖ (ModuleCat R)ᵒᵖ AddCommGrpCat).obj
      (finiteLengthInclusion R).op

/-- The same actual Hom restricted to locally Artinian coefficients. -/
def locallyArtinianRestrictedHom : LocallyArtinianModuleCat R ⥤
    ((FiniteLengthModuleCat R)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (locallyArtinianModuleProperty R).ι ⋙ finiteLengthModuleRepresentations

variable [IsNoetherianRing R]

/-- Every finite submodule of the actual coefficient is a finite-length
test object. The whole coefficient is not required to be finite. -/
def locallyArtinianFiniteSubmodule (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) (P : Submodule R H) [Module.Finite R P] :
    FiniteLengthModuleCat R :=
  ⟨ModuleCat.of R P, (moduleLocallyArtinian_iff_finiteLength H).mp hH P
    (Module.Finite.iff_fg.mp inferInstance)⟩

/-- The original inclusion of this test module. -/
def locallyArtinianFiniteSubmoduleι (H : ModuleCat.{u} R)
    (hH : ModuleLocallyArtinian (R := R) H) (P : Submodule R H) [Module.Finite R P] :
    (locallyArtinianFiniteSubmodule H hH P).obj ⟶ H :=
  ModuleCat.ofHom P.subtype

variable {H K : ModuleCat.{u} R} (hH : ModuleLocallyArtinian (R := R) H)
  (α : finiteLengthModuleRepresentations.obj H ⟶ finiteLengthModuleRepresentations.obj K)

/-- Recover the value on an element from its actual cyclic submodule. -/
def finiteLengthRestrictedHomValue (x : H) : K :=
  ModuleCat.Hom.hom (α.app (op (locallyArtinianFiniteSubmodule H hH (Submodule.span R {x})))
    (locallyArtinianFiniteSubmoduleι H hH (Submodule.span R {x})))
      ⟨x, Submodule.mem_span_singleton_self x⟩

/-- Naturality identifies the same value computed on any finite submodule. -/
theorem finiteLengthRestrictedHomValue_eq (P : Submodule R H) [Module.Finite R P]
    (x : H) (hx : x ∈ P) :
    finiteLengthRestrictedHomValue hH α x =
      ModuleCat.Hom.hom (α.app (op (locallyArtinianFiniteSubmodule H hH P))
        (locallyArtinianFiniteSubmoduleι H hH P)) ⟨x, hx⟩ := by
  let Q := Submodule.span R ({x} : Set H)
  have hQP : Q ≤ P := Submodule.span_le.mpr (by simpa using hx)
  let j : locallyArtinianFiniteSubmodule H hH Q ⟶ locallyArtinianFiniteSubmodule H hH P :=
    ObjectProperty.homMk (ModuleCat.ofHom (Submodule.inclusion hQP))
  have h := ConcreteCategory.congr_hom (α.naturality j.op)
    (locallyArtinianFiniteSubmoduleι H hH P)
  exact congrArg (fun f : (locallyArtinianFiniteSubmodule H hH Q).obj ⟶ K ↦
    f ⟨x, Submodule.mem_span_singleton_self x⟩) h

/-- The recovered map is linear by comparison on finite spans. -/
def finiteLengthRestrictedHomPreimage : H ⟶ K :=
  ModuleCat.ofHom
    { toFun := finiteLengthRestrictedHomValue hH α
      map_add' x y := by
        let P := Submodule.span R ({x, y} : Set H)
        have : Module.Finite R P :=
          Module.Finite.span_of_finite R ((Set.finite_singleton y).insert x)
        have hx : x ∈ P := Submodule.subset_span (by simp)
        have hy : y ∈ P := Submodule.subset_span (by simp)
        rw [finiteLengthRestrictedHomValue_eq hH α P (x + y) (P.add_mem hx hy),
          finiteLengthRestrictedHomValue_eq hH α P x hx,
          finiteLengthRestrictedHomValue_eq hH α P y hy]
        exact (ModuleCat.Hom.hom (α.app (op (locallyArtinianFiniteSubmodule H hH P))
          (locallyArtinianFiniteSubmoduleι H hH P))).map_add ⟨x, hx⟩ ⟨y, hy⟩
      map_smul' r x := by
        let P := Submodule.span R ({x} : Set H)
        have hx : x ∈ P := Submodule.mem_span_singleton_self x
        rw [finiteLengthRestrictedHomValue_eq hH α P (r • x) (P.smul_mem r hx),
          finiteLengthRestrictedHomValue_eq hH α P x hx]
        exact (ModuleCat.Hom.hom (α.app (op (locallyArtinianFiniteSubmodule H hH P))
          (locallyArtinianFiniteSubmoduleι H hH P))).map_smul r ⟨x, hx⟩ }

/-- On every original test module, the transformation is actual
postcomposition by the recovered map. -/
theorem finiteLengthRestrictedHomPreimage_naturality (M : FiniteLengthModuleCat R)
    (g : M.obj ⟶ H) (x : M.obj) :
    ModuleCat.Hom.hom (α.app (op M) g) x = finiteLengthRestrictedHomPreimage hH α (g x) := by
  let P := g.hom.range
  have : Module.Finite R P := Module.Finite.range g.hom
  let j : M ⟶ locallyArtinianFiniteSubmodule H hH P :=
    ObjectProperty.homMk (ModuleCat.ofHom g.hom.rangeRestrict)
  have h := ConcreteCategory.congr_hom (α.naturality j.op)
    (locallyArtinianFiniteSubmoduleι H hH P)
  have h' := congrArg (fun f : M.obj ⟶ K ↦ f x) h
  change ModuleCat.Hom.hom (α.app (op M) g) x =
    ModuleCat.Hom.hom (α.app (op (locallyArtinianFiniteSubmodule H hH P))
      (locallyArtinianFiniteSubmoduleι H hH P)) ⟨g x, ⟨x, rfl⟩⟩ at h'
  exact h'.trans (finiteLengthRestrictedHomValue_eq hH α P (g x) ⟨x, rfl⟩).symm

@[simp] theorem finiteLengthModuleRepresentations_map_preimage :
    finiteLengthModuleRepresentations.map (finiteLengthRestrictedHomPreimage hH α) = α := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  apply ModuleCat.hom_ext
  ext x
  exact (finiteLengthRestrictedHomPreimage_naturality hH α M.unop g x).symm

@[simp] theorem finiteLengthModuleRepresentations_preimage_map (f : H ⟶ K) :
    finiteLengthRestrictedHomPreimage hH (finiteLengthModuleRepresentations.map f) = f := by
  ext x
  rfl

/-- **IV.4.2, uniqueness foundation.** Actual Hom on finite-length tests
is fully faithful on arbitrary locally Artinian modules over a noetherian
ring, without a local-ring or finite-coefficient assumption. -/
def locallyArtinianRestrictedHomFullyFaithful :
    (locallyArtinianRestrictedHom (R := R)).FullyFaithful where
  preimage {H _K} α := ObjectProperty.homMk (finiteLengthRestrictedHomPreimage H.property α)
  map_preimage α := finiteLengthModuleRepresentations_map_preimage _ α
  preimage_map f := ObjectProperty.hom_ext _
    (finiteLengthModuleRepresentations_preimage_map _ f.hom)

instance : (locallyArtinianRestrictedHom (R := R)).Full :=
  (locallyArtinianRestrictedHomFullyFaithful (R := R)).full

instance : (locallyArtinianRestrictedHom (R := R)).Faithful :=
  (locallyArtinianRestrictedHomFullyFaithful (R := R)).faithful

/-- A specified natural isomorphism of original restricted Hom functors
recovers an actual isomorphism of locally Artinian coefficients. -/
def locallyArtinianIsoOfFiniteLengthHom
    (hK : ModuleLocallyArtinian (R := R) K)
    (e : finiteLengthModuleRepresentations.obj H ≅ finiteLengthModuleRepresentations.obj K) :
    H ≅ K :=
  (locallyArtinianModuleProperty R).ι.mapIso
    ((locallyArtinianRestrictedHomFullyFaithful (R := R)).preimageIso
      (X := ⟨H, hH⟩) (Y := ⟨K, hK⟩) e)

/-- The recovered isomorphism induces the specified natural transformation
itself, not merely some natural isomorphism of the same functors. -/
@[simp]
theorem locallyArtinianIsoOfFiniteLengthHom_hom_map
    (hK : ModuleLocallyArtinian (R := R) K)
    (e : finiteLengthModuleRepresentations.obj H ≅ finiteLengthModuleRepresentations.obj K) :
    finiteLengthModuleRepresentations.map (locallyArtinianIsoOfFiniteLengthHom hH hK e).hom =
      e.hom :=
  finiteLengthModuleRepresentations_map_preimage hH e.hom

end SGA.SGA2.ExposeIV
