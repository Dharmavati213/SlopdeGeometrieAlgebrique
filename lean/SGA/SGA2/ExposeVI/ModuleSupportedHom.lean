/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleGlobalHom
import SGA.SGA2.ExposeVI.ModuleSupportedSheaf

/-!
# SGA 2, VI.1.4.3: supported linear maps and the supported coefficient sheaf

For closed support, a local linear map vanishes off the support exactly when
its values belong to the actual supported coefficient submodules. Globally,
this gives the natural identification `Γ_Z(Hom(F,G)) ≅ Hom(F,Γ̲_Z(G))`.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Every value of a supported local linear map is an actual supported section. -/
theorem moduleSupportedLocalHom_mem (F G : SheafOfModules.{u} R) (Z : Closeds X)
    (U : Opens X)
    (φ : ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U)
    (V : Over U) (x : F.val.obj (op V.left)) :
    φ.val.val.app (op V) x ∈ ExposeV.moduleGammaZSections R Z V.left G := by
  let A := V.left ⊓ Z.compl
  let a : A ⟶ V.left := homOfLE inf_le_left
  let b : A ⟶ U ⊓ Z.compl :=
    homOfLE (le_inf (inf_le_left.trans (leOfHom V.hom)) inf_le_right)
  have h := congrArg (fun ψ : moduleLocalHom F.val G.val (U ⊓ Z.compl) ↦
    ψ.val.app (op (Over.mk b)) (F.val.map a.op x)) φ.property
  have hn := NatTrans.naturality_apply φ.val.val
    (Over.homMk a : Over.mk (a ≫ V.hom) ⟶ V).op x
  exact hn.symm.trans h

/-- A supported local map factors through the original supported coefficient submodules. -/
def moduleSupportedLocalHomLift (F G : SheafOfModules.{u} R) (Z : Closeds X) (U : Opens X)
    (φ : ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U) :
    moduleLocalHom F.val (moduleGammaZSheaf R Z G).val U :=
  ⟨
    { app V := AddCommGrpCat.ofHom
        { toFun x := ⟨φ.val.val.app V x, moduleSupportedLocalHom_mem R F G Z U φ V.unop x⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' x y := Subtype.ext (map_add _ x y) }
      naturality {V W} i := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro x
        apply Subtype.ext
        exact NatTrans.naturality_apply φ.val.val i x },
    fun V r x ↦ Subtype.ext (φ.val.property V r x)⟩

/-- A local map into the actual supported coefficient sheaf vanishes off the support. -/
def moduleLocalHomToSupported (F G : SheafOfModules.{u} R) (Z : Closeds X) (U : Opens X)
    (φ : moduleLocalHom F.val (moduleGammaZSheaf R Z G).val U) :
    ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U :=
  ⟨moduleLocalHomPostcomp F.val (moduleGammaZSheafι R Z G).val U φ, by
    change moduleLocalHomRestrict F.val G.val
      (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U))
        (moduleLocalHomPostcomp F.val (moduleGammaZSheafι R Z G).val U φ) = 0
    apply moduleLocalHom_ext
    intro V x
    exact moduleGammaZSheaf_section_eq_zero R Z G ((leOfHom V.hom).trans inf_le_right)
      (φ.val.app (op ((Over.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U))).obj V)) x)⟩

/-- The local supported-Hom comparison uses the original factorization and inclusion maps. -/
def moduleSupportedLocalHomEquiv (F G : SheafOfModules.{u} R) (Z : Closeds X) (U : Opens X) :
    ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U ≃+
      moduleLocalHom F.val (moduleGammaZSheaf R Z G).val U where
  toFun := moduleSupportedLocalHomLift R F G Z U
  invFun := moduleLocalHomToSupported R F G Z U
  left_inv φ := by
    apply Subtype.ext
    apply moduleLocalHom_ext
    intro V x
    rfl
  right_inv φ := by
    apply moduleLocalHom_ext
    intro V x
    apply Subtype.ext
    rfl
  map_add' φ ψ := by
    apply moduleLocalHom_ext
    intro V x
    apply Subtype.ext
    rfl

/-- The local factorization commutes with actual coefficient maps. -/
theorem moduleSupportedLocalHomEquiv_naturality (F : SheafOfModules.{u} R)
    {G H : SheafOfModules.{u} R} (a : G ⟶ H) (Z : Closeds X) (U : Opens X)
    (φ : ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U) :
    moduleSupportedLocalHomEquiv R F H Z U
        (ExposeI.gammaZSectionsMap
          ((moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).map a) Z U φ) =
      moduleLocalHomPostcomp F.val (moduleGammaZSheafMap R Z a).val U
        (moduleSupportedLocalHomEquiv R F G Z U φ) := by
  apply moduleLocalHom_ext
  intro V x
  apply Subtype.ext
  rfl

/-- The same factorization commutes with every open restriction. -/
theorem moduleSupportedLocalHomEquiv_restrict (F G : SheafOfModules.{u} R)
    (Z : Closeds X) {U V : Opens X} (i : V ⟶ U)
    (φ : ExposeI.gammaZSections (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z U) :
    moduleSupportedLocalHomEquiv R F G Z V
        (ExposeI.gammaZSectionsRestriction
          (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z i φ) =
      moduleLocalHomRestrict F.val (moduleGammaZSheaf R Z G).val i
        (moduleSupportedLocalHomEquiv R F G Z U φ) := by
  apply moduleLocalHom_ext
  intro W x
  apply Subtype.ext
  rfl

/-- VI.1.4.3 for closed support: supported global linear maps are maps into the
original module sheaf of supported sections. -/
def moduleSupportedHomEquiv (F G : SheafOfModules.{u} R) (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (F ⟶ moduleGammaZSheaf R Z G) :=
  (moduleSupportedLocalHomEquiv R F G Z ⊤).trans
    (moduleSheafHomAbGlobalEquiv R F (moduleGammaZSheaf R Z G))

/-- VI.1.4.3 also respects the actual contravariant maps in its first module sheaf. -/
theorem moduleSupportedHomEquiv_precomp {E F : SheafOfModules.{u} R} (a : E ⟶ F)
    (G : SheafOfModules.{u} R) (Z : Closeds X)
    (φ : ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z) :
    moduleSupportedHomEquiv R E G Z
        (ExposeI.gammaZSectionsMap
          (moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G) Z ⊤ φ) =
      a ≫ moduleSupportedHomEquiv R F G Z φ := by ext U x; rfl

/-- The actual additive supported-Hom coefficient functor. -/
def moduleSupportedHomFunctor (F : SheafOfModules.{u} R) (Z : Closeds X) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙ ExposeI.gammaZSectionsFunctor Z ⊤

/-- VI.1.4.3 is natural for the original coefficient maps, not just objectwise. -/
def moduleSupportedHomFunctorIso (F : SheafOfModules.{u} R) (Z : Closeds X) :
    moduleSupportedHomFunctor R F Z ≅
      moduleGammaZSheafFunctor R Z ⋙ preadditiveCoyoneda.obj (op F) :=
  NatIso.ofComponents (fun G ↦ (moduleSupportedHomEquiv R F G Z).toAddCommGrpIso)
    (fun a ↦ by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      rfl)

/-- The supported-Hom comparison is compatible with both opens and coefficients. -/
def moduleSupportedInternalHomPresheafIso (F : SheafOfModules.{u} R) (Z : Closeds X) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaZSectionsPresheafFunctor Z ≅
      moduleGammaZSheafFunctor R Z ⋙
        moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
  NatIso.ofComponents
    (fun G ↦ NatIso.ofComponents
      (fun U ↦ (moduleSupportedLocalHomEquiv R F G Z U.unop).toAddCommGrpIso)
      (fun i ↦ by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro φ
        exact moduleSupportedLocalHomEquiv_restrict R F G Z i.unop φ))
    (fun a ↦ by
      apply NatTrans.ext
      funext U
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      exact moduleSupportedLocalHomEquiv_naturality R F a Z U.unop φ)

/-- Sheaf form of VI.1.4.3 for closed support, retaining actual local module-linearity. -/
def moduleSupportedInternalHomFunctorIso (F : SheafOfModules.{u} R) (Z : Closeds X) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.underlineGammaZFunctor Z ≅
      moduleGammaZSheafFunctor R Z ⋙
        moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (SheafOfModules.{u} R)).preimageIso
      (Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
          (ExposeI.underlineGammaZPresheafFunctorIso Z) ≪≫
        moduleSupportedInternalHomPresheafIso R F Z)

end SGA.SGA2.ExposeVI
