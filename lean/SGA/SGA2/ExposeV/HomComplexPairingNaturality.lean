/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexBoundaryPairing

/-! # Naturality of the original Hom pairing in its middle complex -/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  {F G H P : CochainComplex C ℤ} {i j k : ℤ}

/-- Original standard homology representatives commute with precomposition. -/
theorem homComplexHomologyMk_precomp (f : F ⟶ G) (z : Cocycle G P i) :
    homologyMap (homComplexPrecomp f P) i (homComplexHomologyMk z) =
      homComplexHomologyMk (z.precomp f) := by
  apply (HomComplex.homologyAddEquiv F P i).injective
  rw [homComplexHomologyAddEquiv_precomp, homComplexHomologyMk_compare,
    homComplexClassPrecomp_mk, homComplexHomologyMk_compare]

/-- Original standard homology representatives commute with postcomposition. -/
theorem homComplexHomologyMk_postcomp (f : G ⟶ H) (z : Cocycle F G i) :
    homologyMap (homComplexPostcomp F f) i (homComplexHomologyMk z) =
      homComplexHomologyMk (z.postcomp f) := by
  apply (HomComplex.homologyAddEquiv F H i).injective
  rw [homComplexHomologyAddEquiv_naturality, homComplexHomologyMk_compare,
    homComplexClassPostcomp_mk, homComplexHomologyMk_compare]

/-- The actual standard homology product on original representatives. -/
theorem homologyComp_mk (h : i + j = k) (z : Cocycle F G i) (w : Cocycle G P j) :
    homologyComp h (homComplexHomologyMk z) (homComplexHomologyMk w) =
      homComplexHomologyMk (homCocycleComp z w h) := by
  apply (HomComplex.homologyAddEquiv F P k).injective
  rw [homologyAddEquiv_homologyComp, homComplexHomologyMk_compare,
    homComplexHomologyMk_compare, homClassComp_mk, homComplexHomologyMk_compare]

/-- Original composition is balanced across an unchanged middle chain map. -/
theorem homCocycleComp_naturality_middle (f : G ⟶ H) (h : i + j = k)
    (z : Cocycle F G i) (w : Cocycle H P j) :
    homCocycleComp (z.postcomp f) w h = homCocycleComp z (w.precomp f) h := by
  apply Subtype.ext
  change (z.1.comp (Cochain.ofHom f) (add_zero i)).comp w.1 h =
    z.1.comp ((Cochain.ofHom f).comp w.1 (zero_add j)) h
  rw [Cochain.comp_assoc_of_second_is_zero_cochain]

/-- **V.1, formula (1.4):** naturality of the actual standard cohomology
pairing in the middle complex, retaining the original Hom-complex maps. -/
theorem homologyComp_naturality_middle (f : G ⟶ H) (h : i + j = k)
    (x : (HomComplex F G).homology i) (y : (HomComplex H P).homology j) :
    homologyComp h (homologyMap (homComplexPostcomp F f) i x) y =
      homologyComp h x (homologyMap (homComplexPrecomp f P) j y) := by
  obtain ⟨z, rfl⟩ := homComplexHomologyMk_surjective F G i x
  obtain ⟨w, rfl⟩ := homComplexHomologyMk_surjective H P j y
  rw [homComplexHomologyMk_postcomp, homComplexHomologyMk_precomp,
    homologyComp_mk, homologyComp_mk, homCocycleComp_naturality_middle]

/-- The literal displayed-source pairing is natural in the middle complex,
with its original unscaled product and unchanged pre/postcomposition maps. -/
theorem sourceHomologyComp_naturality_middle (f : G ⟶ H) (h : i + j = k)
    (x : (sourceHomComplex F G).homology i) (y : (sourceHomComplex H P).homology j) :
    sourceHomologyComp h (homologyMap (sourceHomPostcomp F f) i x) y =
      sourceHomologyComp h x (homologyMap (sourceHomPrecomp f P) j y) := by
  obtain ⟨z, rfl⟩ := sourceHomologyMk_surjective G F i x
  obtain ⟨w, rfl⟩ := sourceHomologyMk_surjective P H j y
  rw [sourceHomologyMk_postcomp, sourceHomologyMk_precomp,
    sourceHomologyComp_mk, sourceHomologyComp_mk, homCocycleComp_naturality_middle]

end SGA.SGA2.ExposeV
