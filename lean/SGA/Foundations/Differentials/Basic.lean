/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.Presheaf
import SGA.Foundations.Differentials.Sections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_X`-module `M`, a derivation of `𝒪_X` into `M`
relative to `f` (`Scheme.Modules.Derivation M f`) is a family of additive maps
`Γ(X, U) → Γ(M, U)`, compatible with restrictions, satisfying the Leibniz rule and vanishing on
the sections `f^♯ s`; these are the `f⁻¹ 𝒪_Y`-linear derivations of EGA IV 16.5 and of the
Stacks Project, Tag 01UM. The sheaf of relative differentials `Ω_{X/Y}`
(`Scheme.Hom.relativeDifferentials f`) is the sheafification of the presheaf of relative
differentials `U ↦ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`; it carries a universal derivation
`Scheme.Hom.universalDerivation f` (Stacks Project, Tag 01UP; EGA IV 16.5.3):

`Hom_{𝒪_X}(Ω_{X/Y}, M) ≃ Der_Y(𝒪_X, M)` (`Scheme.Hom.relativeDifferentialsHomEquiv`).

We also define the direct image of a derivation (`Scheme.Modules.Derivation.pushforward`), used
to compare the sheaves of differentials of different morphisms.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

variable {X Y Z X' : Scheme.{u}}

namespace Scheme.Modules

/-- A derivation of `𝒪_X` with values in the `𝒪_X`-module `M`, relative to `f : X ⟶ Y`: a family
of additive maps `Γ(X, U) → Γ(M, U)`, compatible with the restrictions, satisfying the Leibniz
rule and vanishing on the sections `f^♯ s`, `s ∈ Γ(Y, V)`. These are the `f⁻¹ 𝒪_Y`-derivations
of `𝒪_X` into `M`. -/
abbrev Derivation (M : X.Modules) (f : X ⟶ Y) : Type u :=
  M.val.Derivation (F := Opens.map f.base) (R := X.presheaf) f.c

namespace Derivation

variable {M N P : X.Modules} {f : X ⟶ Y} (D : M.Derivation f)

/-- The additive map `Γ(X, U) → Γ(M, U)` of a derivation. -/
def app (U : X.Opens) : Γ(X, U) →+ Γ(M, U) := D.d (X := op U)

lemma app_mul (U : X.Opens) (a b : Γ(X, U)) :
    D.app U (a * b) = a • D.app U b + b • D.app U a :=
  D.d_mul a b

@[simp]
lemma app_one (U : X.Opens) : D.app U 1 = 0 :=
  D.d_one (op U)

lemma app_map {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, V)) :
    D.app U (X.presheaf.map i.op a) = M.presheaf.map i.op (D.app V a) :=
  D.d_map i.op a

/-- A derivation relative to `f` vanishes on the sections `f^♯ s`. -/
@[simp]
lemma app_app (V : Y.Opens) (s : Γ(Y, V)) : D.app (f ⁻¹ᵁ V) (f.app V s) = 0 :=
  D.d_app (X := op V) s

@[ext]
lemma ext {D D' : M.Derivation f} (h : ∀ U a, D.app U a = D'.app U a) : D = D' := by
  apply PresheafOfModules.Derivation.ext
  ext U a
  exact h U.unop a

/-- A derivation vanishes on the image of `𝒪_Y`: this is `app_app` for a section of `𝒪_X` over
`U ⊆ f⁻¹ V` which is the restriction of some `f^♯ s`. -/
lemma app_appLE {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) (s : Γ(Y, V)) :
    D.app U (f.appLE V U e s) = 0 := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, app_map, app_app, map_zero]

/-- Composition of a derivation with a morphism of `𝒪_X`-modules. -/
def postcomp (α : M ⟶ N) : N.Derivation f :=
  PresheafOfModules.Derivation.postcomp D α.val

@[simp]
lemma postcomp_app (α : M ⟶ N) (U : X.Opens) (a : Γ(X, U)) :
    (D.postcomp α).app U a = α.app U (D.app U a) :=
  rfl

@[simp]
lemma postcomp_id : D.postcomp (𝟙 M) = D := rfl

lemma postcomp_comp (α : M ⟶ N) (β : N ⟶ P) :
    D.postcomp (α ≫ β) = (D.postcomp α).postcomp β :=
  rfl

/-- The universal property of a derivation `d : M.Derivation f` among `𝒪_X`-modules: every
derivation factors uniquely through `d`. -/
structure Universal (d : M.Derivation f) where
  /-- A derivation relative to `f` factors through `d`. -/
  desc {N : X.Modules} (d' : N.Derivation f) : M ⟶ N
  fac {N : X.Modules} (d' : N.Derivation f) : d.postcomp (desc d') = d'
  postcomp_injective {N : X.Modules} (α β : M ⟶ N) (h : d.postcomp α = d.postcomp β) : α = β

namespace Universal

variable {d : M.Derivation f} (hd : d.Universal)

attribute [simp] fac

/-- The bijection `Hom(M, N) ≃ Der_f(𝒪_X, N)` given by a universal derivation. -/
@[simps]
def homEquiv (N : X.Modules) : (M ⟶ N) ≃ N.Derivation f where
  toFun α := d.postcomp α
  invFun := hd.desc
  left_inv α := hd.postcomp_injective _ _ (by simp)
  right_inv := hd.fac

include hd in
lemma hom_ext {N : X.Modules} {α β : M ⟶ N}
    (h : ∀ U a, α.app U (d.app U a) = β.app U (d.app U a)) : α = β :=
  hd.postcomp_injective α β (Derivation.ext h)

@[simp]
lemma desc_postcomp {N : X.Modules} (α : M ⟶ N) : hd.desc (d.postcomp α) = α :=
  (hd.homEquiv N).left_inv α

@[simp]
lemma desc_app_app {N : X.Modules} (d' : N.Derivation f) (U : X.Opens) (a : Γ(X, U)) :
    (hd.desc d').app U (d.app U a) = d'.app U a := by
  rw [← postcomp_app, hd.fac]

/-- Two universal derivations have isomorphic targets. -/
@[simps]
def iso {M' : X.Modules} {d' : M'.Derivation f} (hd' : d'.Universal) : M ≅ M' where
  hom := hd.desc d'
  inv := hd'.desc d
  hom_inv_id := hd.postcomp_injective _ _ (by rw [postcomp_comp, fac, fac, postcomp_id])
  inv_hom_id := hd'.postcomp_injective _ _ (by rw [postcomp_comp, fac, fac, postcomp_id])

include hd in
/-- A universal derivation composed with an isomorphism is universal. -/
def ofIso {M' : X.Modules} (e : M ≅ M') : (d.postcomp e.hom).Universal where
  desc d' := e.inv ≫ hd.desc d'
  fac d' := by rw [← postcomp_comp, e.hom_inv_id_assoc, hd.fac]
  postcomp_injective α β h := by
    rw [← cancel_epi e.hom]
    exact hd.postcomp_injective _ _ (by rw [postcomp_comp, postcomp_comp, h])

end Universal

section pushforward

variable {g : X' ⟶ X} {N : X'.Modules}

/-- The direct image of a derivation: a derivation `𝒪_{X'} → N` relative to `g ≫ f` induces a
derivation `𝒪_X → g_* N` relative to `f`, namely `a ↦ d(g^♯ a)`. -/
def pushforward (D : N.Derivation (g ≫ f)) : ((pushforward g).obj N).Derivation f where
  d {U} := (D.app (g ⁻¹ᵁ U.unop)).comp (g.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change D.app _ (g.app _ (a * b)) = _
    rw [map_mul, app_mul]
    rfl
  d_map {U V} i a := by
    change D.app _ (g.app _ (X.presheaf.map i a)) =
      N.presheaf.map ((Opens.map g.base).map i.unop).op (D.app _ (g.app _ a))
    rw [← app_map]
    congr 1
    exact congr($(g.c.naturality i) a)
  d_app {V} s := by
    change D.app _ (g.app _ (f.app _ s)) = 0
    exact D.app_app (f := g ≫ f) V.unop s

@[simp]
lemma pushforward_app (D : N.Derivation (g ≫ f)) (U : X.Opens) (a : Γ(X, U)) :
    D.pushforward.app U a = D.app (g ⁻¹ᵁ U) (g.app U a) :=
  rfl

end pushforward

end Derivation

end Scheme.Modules

namespace Scheme.Hom

open PresheafOfModules Scheme.Modules

variable (f : X ⟶ Y)

/-- The presheaf of relative differentials `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_Y)(U)}` of a morphism of
schemes. -/
noncomputable abbrev relativeDifferentialsPresheaf : X.PresheafOfModules :=
  DifferentialsConstruction.relativeDifferentials (F := Opens.map f.base) (R := X.presheaf) f.c

/-- The sheaf of relative differentials `Ω_{X/Y}` of a morphism of schemes `f : X ⟶ Y`: the
sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_Y)(U)}` (Stacks Project, Tag 01UM). -/
noncomputable def relativeDifferentials : X.Modules :=
  (sheafification (𝟙 X.ringCatSheaf.obj)).obj f.relativeDifferentialsPresheaf

/-- The unit `Ω^{pre}_{X/Y} ⟶ Ω_{X/Y}` of the sheafification. -/
noncomputable def toRelativeDifferentials :
    f.relativeDifferentialsPresheaf ⟶ f.relativeDifferentials.val :=
  (sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

/-- The universal derivation `d : 𝒪_X → Ω_{X/Y}`. -/
noncomputable def universalDerivation : f.relativeDifferentials.Derivation f :=
  (DifferentialsConstruction.derivation (F := Opens.map f.base) (R := X.presheaf) f.c).postcomp
    f.toRelativeDifferentials

lemma universalDerivation_postcomp {N : X.Modules} (α : f.relativeDifferentials ⟶ N) :
    f.universalDerivation.postcomp α =
      (DifferentialsConstruction.derivation (F := Opens.map f.base) (R := X.presheaf) f.c).postcomp
        ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ N α) := by
  have : (sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ N α =
      f.toRelativeDifferentials ≫ α.val :=
    Adjunction.homEquiv_unit _ _ _ _
  rw [this]
  rfl

/-- The derivation `d : 𝒪_X → Ω_{X/Y}` is universal (Stacks Project, Tag 01UP). -/
noncomputable def isUniversal : f.universalDerivation.Universal where
  desc {N} d' := ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ N).symm
    ((DifferentialsConstruction.isUniversal (F := Opens.map f.base) (R := X.presheaf) f.c).desc d')
  fac d' := (universalDerivation_postcomp f _).trans <|
    (congrArg _ (Equiv.apply_symm_apply _ _)).trans <|
      (DifferentialsConstruction.isUniversal (F := Opens.map f.base) (R := X.presheaf) f.c).fac d'
  postcomp_injective {N} α β h :=
    ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ N).injective <|
      (DifferentialsConstruction.isUniversal (F := Opens.map f.base) (R := X.presheaf)
        f.c).postcomp_injective _ _ <|
          (universalDerivation_postcomp f α).symm.trans (h.trans (universalDerivation_postcomp f β))

/-- The universal property of `Ω_{X/Y}`: `Hom_{𝒪_X}(Ω_{X/Y}, M) ≃ Der_Y(𝒪_X, M)`
(Stacks Project, Tag 01UP; EGA IV 16.5.3). -/
noncomputable def relativeDifferentialsHomEquiv (M : X.Modules) :
    (f.relativeDifferentials ⟶ M) ≃ M.Derivation f :=
  f.isUniversal.homEquiv M

end Scheme.Hom

end AlgebraicGeometry

end
