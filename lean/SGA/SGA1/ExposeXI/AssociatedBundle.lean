/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.GroupSchemeSequence
import SGA.SGA1.ExposeXI.Representability

/-!
# SGA 1, Exposé XI.4: representability of torsors under affine groups, associated bundles

Let `G` be a group scheme over `S` which is affine over `S`.

* Footnote 296 of XI.4.4: every fpqc torsor under `G` (a sheaf `T` on `S`-schemes with a simply
  transitive action of `Hom_S(-, G)`, locally trivial for the fpqc topology) is representable by
  an `S`-scheme affine over `S` (`exists_representableBy_of_torsor`). Over an affine open subset
  of `S` the torsor is trivialized by one faithfully flat quasi-compact morphism, and the
  representing scheme `G ×_S S'` descends by VIII.2.1 (`RepresentsOver.descend`); the pieces are
  glued along the Zariski topology of `S` (`exists_representableBy_of_isAffinelyRepresentedOn`).
* The representing scheme carries the transported action of `G` and is a principal homogeneous
  bundle in the sense of XI.4.1 with the same class (`exists_isPrincipalBundle_class_eq`), so
  `H¹(S, G)` defined by torsors of the fpqc site agrees with SGA's `H¹(S, G)`, the set of
  isomorphism classes of principal homogeneous bundles (`exists_isPrincipalBundle_of_mem_H1`).
* XI.4, associated bundles: for a homomorphism `G ⟶ H` of group schemes with `H` affine over
  `S`, every principal homogeneous bundle `P` under `G` has an associated principal homogeneous
  bundle `P^(H)` under `H`, whose class is the image of the class of `P`
  (`IsPrincipalBundle.exists_associated`). As a sheaf it is the change of group of the torsor
  of `P` (`Torsor.changeGroup`), so it is functorial in `G ⟶ H` (`H1.map_map`).

The associated bundle `E^(P)` for an arbitrary `S`-scheme `E` affine over `S` with an action of
`G` is in `SGA.SGA1.ExposeXI.ContractedProduct`.
-/

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry MorphismProperty

namespace SGA.SGA1.ExposeXI

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

section Transport

variable {T : Torsor (fpqc S) (yonedaGrpObj G)} {X : Over S} (e : T.obj.RepresentableBy X)

/-- An `S`-scheme representing a `G`-torsor, with the transported action of `G`, is a torsor
object (formally principal homogeneous and locally trivial for the fpqc topology). -/
theorem isTorsorObj_of_representableBy :
    letI := modObjOfRepresentableBy e
    IsTorsorObj (fpqc S) G X := by
  let _ := modObjOfRepresentableBy e
  have key : ∀ {Z : Over S} (m : Z ⟶ G) (x : Z ⟶ X),
      e.homEquiv (m • x) = T.smul (op Z) m (e.homEquiv x) :=
    fun m x ↦ homEquiv_lift_torsorSMul e m x
  refine ⟨ModObj.isIso_leftSMul_iff.2 fun Z x y ↦ ?_, fun U ↦ ?_⟩
  · obtain ⟨m, hm, hu⟩ := T.existsUnique_smul (op Z) (e.homEquiv x) (e.homEquiv y)
    exact ⟨m, e.homEquiv.injective ((key m x).trans hm),
      fun m' hm' ↦ hu m' ((key m' x).symm.trans (congrArg e.homEquiv hm'))⟩
  · obtain ⟨R, hR, hne⟩ := T.locallyNonempty U
    exact ⟨R, hR, fun V f hf ↦ (hne f hf).map e.homEquiv.symm⟩

/-- The torsor object representing `T` has the class of `T`. -/
theorem class_isTorsorObj_of_representableBy :
    letI := modObjOfRepresentableBy e
    (isTorsorObj_of_representableBy e).class = T.class := by
  let _ := modObjOfRepresentableBy e
  exact (Torsor.class_eq_class_iff _ _).2
    ⟨asIso ⟨e.toIso.hom, fun U g x ↦ homEquiv_lift_torsorSMul e g x⟩⟩

end Transport

variable [IsAffineHom G.hom]

set_option backward.isDefEq.respectTransparency.types false in
/-- Footnote 296 of XI.4.4, local form: over an affine `S`-scheme `V`, a torsor under `G` affine
over `S` is represented by an `S`-scheme affine over `V`. It is trivialized by a single
faithfully flat `Spec B ⟶ V`, over which it is represented by `G ×_S Spec B`, and this descends
by VIII.2.1. -/
theorem exists_representsOver_of_isAffine (T : Torsor (fpqc S) (yonedaGrpObj G)) (V : Over S)
    [IsAffine V.left] :
    ∃ (X : Over S) (f : X ⟶ V) (u : T.obj.obj (op X)), IsAffineHom f.left ∧
      RepresentsOver T.obj f u := by
  obtain ⟨R, hR, hne⟩ := T.locallyNonempty V
  let a : Spec Γ(V.left, ⊤) ⟶ S := V.left.isoSpec.inv ≫ V.hom
  let e : Over.mk a ⟶ V := CategoryTheory.Over.homMk V.left.isoSpec.inv rfl
  obtain ⟨B, φ, hφ, ⟨p⟩⟩ := exists_faithfullyFlat_section T.isSheaf a (R.pullback e)
    ((fpqc S).pullback_stable e hR) fun _ g hg ↦ hne _ hg
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  let g : affOver a φ ⟶ V := CategoryTheory.Over.homMk (Spec.map φ ≫ V.left.isoSpec.inv) (by
    change (Spec.map φ ≫ V.left.isoSpec.inv) ≫ V.hom = Spec.map φ ≫ V.left.isoSpec.inv ≫ V.hom
    rw [Category.assoc])
  have : Surjective g.left := inferInstanceAs (Surjective (Spec.map φ ≫ V.left.isoSpec.inv))
  have : Flat g.left := inferInstanceAs (Flat (Spec.map φ ≫ V.left.isoSpec.inv))
  have : QuasiCompact g.left := inferInstanceAs (QuasiCompact (Spec.map φ ≫ V.left.isoSpec.inv))
  have : IsAffineHom (snd G (affOver a φ)).left :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ ‹IsAffineHom G.hom›
  obtain ⟨X, f, u, -, haff, hrep, -, -⟩ :=
    RepresentsOver.descend T.isSheaf g (representsOver_smul T p)
  exact ⟨X, f, u, haff, hrep⟩

/-- Footnote 296 of XI.4.4: an fpqc torsor under a group scheme `G` affine over `S` is
representable by an `S`-scheme affine over `S`. -/
theorem exists_representableBy_of_torsor (T : Torsor (fpqc S) (yonedaGrpObj G)) :
    ∃ X : Over S, IsAffineHom X.hom ∧ Nonempty (T.obj.RepresentableBy X) := by
  refine exists_representableBy_of_isAffinelyRepresentedOn T.isSheaf fun x ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsAffine (Over.mk (Scheme.Opens.ι V)).left := hV
  exact ⟨V, hxV, exists_representsOver_of_isAffine T (Over.mk (Scheme.Opens.ι V))⟩

/-- Footnote 296 of XI.4.4: for `G` affine over `S`, every fpqc torsor under `G` is (the torsor
of) a principal homogeneous bundle, affine over `S`, with the same class. -/
theorem exists_isPrincipalBundle_class_eq (T : Torsor (fpqc S) (yonedaGrpObj G)) :
    ∃ (P : Over S) (_ : ModObj G P) (h : IsPrincipalBundle G P), IsAffineHom P.hom ∧
      h.class = T.class := by
  obtain ⟨X, haff, ⟨e⟩⟩ := exists_representableBy_of_torsor T
  let _ := modObjOfRepresentableBy e
  exact ⟨X, _, isPrincipalBundle_of_isTorsorObj (isTorsorObj_of_representableBy e), haff,
    class_isTorsorObj_of_representableBy e⟩

/-- XI.4.4 and footnote 296: for `G` affine over `S`, every element of `H¹(S, G)` (defined with
torsors of the fpqc site) is the class of a principal homogeneous bundle; two bundles have the
same class if and only if they are isomorphic (`IsPrincipalBundle.class_eq_class_iff`). So
`H¹(S, G)` is SGA's set of isomorphism classes of principal homogeneous bundles. -/
theorem exists_isPrincipalBundle_of_mem_H1 (c : H1 (fpqc S) (yonedaGrpObj G)) :
    ∃ (P : Over S) (_ : ModObj G P) (h : IsPrincipalBundle G P), IsAffineHom P.hom ∧
      h.class = c := by
  obtain ⟨T, rfl⟩ := H1.mk_surjective c
  exact exists_isPrincipalBundle_class_eq T

/-- XI.4 (associated bundles): for a homomorphism `φ : G ⟶ H` of group schemes over `S` with
`H` affine over `S`, a principal homogeneous bundle `P` under `G` has an associated principal
homogeneous bundle `P^(H)` under `H`, affine over `S`, whose class is the image of the class of
`P` under `H¹(S, G) → H¹(S, H)`. (We do not assume `G` affine.) -/
theorem IsPrincipalBundle.exists_associated {G : Over S} [GrpObj G] {H : Over S} [GrpObj H]
    [IsAffineHom H.hom] (φ : G ⟶ H) [IsMonHom φ] {P : Over S} [ModObj G P]
    (hP : IsPrincipalBundle G P) :
    ∃ (Q : Over S) (_ : ModObj H Q) (hQ : IsPrincipalBundle H Q), IsAffineHom Q.hom ∧
      hQ.class = H1.map (yonedaGrpObjMap φ) (isSheaf_yonedaGrpObj H) hP.class := by
  obtain ⟨Q, _, hQ, haff, hc⟩ := exists_isPrincipalBundle_class_eq
    (hP.isTorsorObj.torsor.changeGroup (yonedaGrpObjMap φ) (isSheaf_yonedaGrpObj H))
  exact ⟨Q, _, hQ, haff, hc.trans (H1.map_class _ _ _).symm⟩

end SGA.SGA1.ExposeXI
