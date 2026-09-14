/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexComposition

/-! # V.1: actual cocycles and quotient classes for the source differential -/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (F G : CochainComplex C ℤ)

/-- The original cocycles are the actual kernel of the displayed source
differential; the inclusion does not rescale any component. -/
def sourceCocycleIsKernel (n m : ℤ) (h : n + 1 = m) :
    IsLimit (KernelFork.ofι (f := (sourceHomComplex F G).d n m)
      (AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom F G n)) (by
        ext z
        exact (sourceHomδ_eq_zero_iff n m z.1).2 (z.δ_eq_zero m))) :=
  Fork.IsLimit.mk _
    (fun s => AddCommGrpCat.ofHom
      { toFun z := ⟨s.ι z, by
          rw [Cocycle.mem_iff _ m h]
          exact (sourceHomδ_eq_zero_iff n m _).1 (ConcreteCategory.congr_hom s.condition z)⟩
        map_zero' := by apply Subtype.ext; exact map_zero s.ι.hom
        map_add' z w := by apply Subtype.ext; exact map_add s.ι.hom z w })
    (by cat_disch)
    (fun s l hl => by ext z; apply Subtype.ext; exact ConcreteCategory.congr_hom hl z)

/-- The source complex's actual left homology data uses the original
cocycle inclusion and unscaled quotient map. -/
def sourceHomLeftHomologyData' (n m p : ℤ) (hm : n + 1 = m) (hp : m + 1 = p) :
    ((sourceHomComplex F G).sc' n m p).LeftHomologyData where
  K := .of (Cocycle F G m)
  H := .of (CohomologyClass F G m)
  i := AddCommGrpCat.ofHom (Cocycle.toCochainAddMonoidHom F G m)
  π := AddCommGrpCat.ofHom (CohomologyClass.mkAddMonoidHom F G m)
  wi := by ext z; exact (sourceHomδ_eq_zero_iff m p z.1).2 (z.δ_eq_zero p)
  hi := sourceCocycleIsKernel F G m p hp
  wπ := by
    ext z
    dsimp
    rw [CohomologyClass.mk_eq_zero_iff]
    refine ⟨n, hm, m.negOnePow • z, ?_⟩
    change δ n m (m.negOnePow • z) = sourceHomδ n m z
    exact δ_units_smul n m m.negOnePow z
  hπ := Cofork.IsColimit.mk _
    (fun s => AddCommGrpCat.ofHom (CohomologyClass.descAddMonoidHom s.π.hom (by
      rintro ⟨_, _⟩ ⟨q, hq, z, rfl⟩
      obtain rfl : q = n := by omega
      have hs := ConcreteCategory.congr_hom s.condition (m.negOnePow • z)
      simp only [zero_comp] at hs
      change s.π.hom ⟨sourceHomδ q m (m.negOnePow • z), _⟩ = 0 at hs
      simpa only [AddMonoidHom.mem_ker, sourceHomδ, δ_units_smul, smul_smul,
        Int.units_mul_self, one_smul]
        using hs)))
    (fun s => rfl)
    (fun s l hl => by
      ext z
      obtain ⟨z, rfl⟩ := z.mk_surjective
      exact ConcreteCategory.congr_hom hl z)

/-- Unscaled source homology data in any integer degree. -/
def sourceHomLeftHomologyData (n : ℤ) :
    ((sourceHomComplex F G).sc n).LeftHomologyData :=
  sourceHomLeftHomologyData' F G _ n _ (by simp) (by simp)

/-- Source homology is the quotient of the original cocycles by the original
coboundaries, without the degreewise normalization sign. -/
def sourceHomologyUnscaledAddEquiv (n : ℤ) :
    (sourceHomComplex F G).homology n ≃+ CohomologyClass F G n :=
  (sourceHomLeftHomologyData F G n).homologyIso.addCommGroupIsoToAddEquiv

/-- The explicit normalization acts on both the original cocycles and their
quotient classes by the same degreewise sign. -/
def sourceHomNormalizationMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
        (sourceHomComplexIso F G).hom)
      (sourceHomLeftHomologyData F G n) (HomComplex.leftHomologyData F G n) where
  φK := AddCommGrpCat.ofHom
    { toFun z := sourceHomSign n • z
      map_zero' := smul_zero _
      map_add' z w := smul_add _ z w }
  φH := AddCommGrpCat.ofHom
    { toFun z := sourceHomSign n • z
      map_zero' := smul_zero _
      map_add' z w := smul_add _ z w }
  commi := by ext z; rfl
  commf' := by
    ext z
    apply Subtype.ext
    exact (ConcreteCategory.congr_hom
      ((sourceHomComplexIso F G).hom.comm ((ComplexShape.up ℤ).prev n) n) z).symm
  commπ := by
    ext z
    exact ((CohomologyClass.mkAddMonoidHom F G n).map_zsmul (sourceHomSign n : ℤ) z).symm

/-- The existing normalized homology equivalence differs from the unscaled
original quotient by exactly the specified sign, not an unspecified automorphism. -/
theorem sourceHomologyAddEquiv_eq_sign (n : ℤ) (z : (sourceHomComplex F G).homology n) :
    sourceHomologyAddEquiv F G n z = sourceHomSign n • sourceHomologyUnscaledAddEquiv F G n z :=
  ConcreteCategory.congr_hom (sourceHomNormalizationMapData F G n).homologyMap_comm z

variable {F G} {K : CochainComplex C ℤ}

/-- The class of an original cocycle in the actual source Hom-complex
homology, using its unscaled inclusion and quotient maps. -/
def sourceHomologyMk {n : ℤ} (z : Cocycle F G n) : (sourceHomComplex F G).homology n :=
  (sourceHomologyUnscaledAddEquiv F G n).symm (CohomologyClass.mk z)

/-- The literal source's original graded composition, on actual homology. -/
def sourceHomologyComp {i j k : ℤ} (h : i + j = k) :
    (sourceHomComplex F G).homology i →+
      ((sourceHomComplex G K).homology j →+ (sourceHomComplex F K).homology k) where
  toFun z :=
    { toFun w := (sourceHomologyUnscaledAddEquiv F K k).symm
        (homClassComp h (sourceHomologyUnscaledAddEquiv F G i z)
          (sourceHomologyUnscaledAddEquiv G K j w))
      map_zero' := by simp
      map_add' w w' := by simp }
  map_zero' := by ext w; simp
  map_add' z z' := by ext w; simp

/-- The source pairing is induced by the original cochain composite, with
no sign inserted into the product itself. -/
theorem sourceHomologyComp_mk {i j k : ℤ} (h : i + j = k)
    (z : Cocycle F G i) (w : Cocycle G K j) :
    sourceHomologyComp h (sourceHomologyMk z) (sourceHomologyMk w) =
      sourceHomologyMk (homCocycleComp z w h) := by
  simp [sourceHomologyComp, sourceHomologyMk, homClassComp_mk]

/-- The exact composition sign under the specified normalization on actual
homology: it is `(-1)^(ij)`, just as for the original cochains. -/
theorem sourceHomologyAddEquiv_comp {i j k : ℤ} (h : i + j = k)
    (z : (sourceHomComplex F G).homology i) (w : (sourceHomComplex G K).homology j) :
    sourceHomologyAddEquiv F K k (sourceHomologyComp h z w) =
      (i * j).negOnePow • homClassComp h (sourceHomologyAddEquiv F G i z)
        (sourceHomologyAddEquiv G K j w) := by
  subst k
  simp only [sourceHomologyAddEquiv_eq_sign, sourceHomologyComp,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddEquiv.apply_symm_apply,
    Units.smul_def, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul,
    sourceHomSign_add, Units.val_mul]
  congr 1
  ring

end SGA.SGA2.ExposeV
