/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.AbelianH1
import SGA.SGA1.ExposeXI.GroupSheaves
import SGA.SGA1.ExposeXI.PrincipalBundle

/-!
# SGA 1, Exposé XI.4.4–XI.4.5: the exact cohomology sequence of group schemes

Let `S` be a scheme. For a group scheme `G` over `S`, `H⁰(S, G)` is the group of sections
`S → G`, i.e. morphisms `𝟙_ (Over S) ⟶ G`, and `H¹(S, G)` is the set of classes of fpqc
torsors under `G` (XI.4.4; principal homogeneous bundles are exactly the representable ones,
`isPrincipalBundle_iff_isTorsorObj`, and for affine `G` all of them are, by footnote 296 of
XI.4.4, which is not formalized here). Both are functorial in `G` (`yonedaGrpObjMap`).

A sequence `1 → G' →u G →v G'' → 1` of group schemes is exact in the sense of XI.4 if `v u = 1`
and `G` is a principal homogeneous bundle over `G''` under `G' ×_S G''`. By XI.4.2 applied over
the base `G''` (with `G'` flat and quasi-compact) this means that `u` is a kernel of `v` (on
`T`-valued points) and that `v` is faithfully flat and quasi-compact; this is the form we use
(`IsExactSeq`). Then the sheaves of groups represented by `G'`, `G`, `G''` form a short exact
sequence on the fpqc site of `S` (`IsExactSeq.isShortExact`), and XI.4.5 follows from the
non-commutative exact sequence of `SGA.Foundations.Etale.NonabelianExact`:
```
1 → H⁰(S, G') → H⁰(S, G) → H⁰(S, G'') →∂ H¹(S, G') → H¹(S, G) → H¹(S, G'')
```
(`IsExactSeq.cohomology_exact`, which is also the non-commutative variant asked for in XI.4.9).
For commutative `G'` and `G` the coboundary `∂` and the maps on `H¹` are group homomorphisms
(`IsExactSeq.connectingHom`, `yonedaH1MapHom`). The coboundary `∂ c` of a section `c` of `G''` is
the class of the torsor `v⁻¹(c) = G ×_{G''} S`, which is represented by this `S`-scheme
(`IsExactSeq.fiberTorsorIso`), as in SGA.

The associated bundle `P ×^G H` of XI.4 and the identification of `H¹(S, G)` with classes of
principal homogeneous bundles for affine `G` (footnote 296) are in
`SGA.SGA1.ExposeXI.AssociatedBundle`.
-/

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable {S : Scheme.{u}}

/-- XI.4.4: a homomorphism of group schemes `u : G' ⟶ G` induces a morphism of sheaves of
groups `G'(T) → G(T)`. -/
@[simps]
noncomputable def yonedaGrpObjMap {G' G : Over S} [GrpObj G'] [GrpObj G] (u : G' ⟶ G) [IsMonHom u] :
    yonedaGrpObj G' ⟶ yonedaGrpObj G where
  app T := GrpCat.ofHom (IsMonHom.monoidHom u T.unop)
  naturality _ _ f := GrpCat.hom_ext (MonoidHom.ext fun x ↦ Category.assoc f.unop x u)

lemma yonedaGrpObjMap_app_apply {G' G : Over S} [GrpObj G'] [GrpObj G] (u : G' ⟶ G)
    [IsMonHom u] (T : (Over S)ᵒᵖ) (x : T.unop ⟶ G') :
    (yonedaGrpObjMap u).app T x = x ≫ u :=
  rfl

/-- XI.4.4: `H¹(S, G) → H¹(S, H)` for a homomorphism of commutative group schemes, as a group
homomorphism. -/
noncomputable def yonedaH1MapHom {G' G : Over S} [GrpObj G'] [GrpObj G] [IsCommMonObj G']
    [IsCommMonObj G] (u : G' ⟶ G) [IsMonHom u] :
    letI := H1.commGroupOfGrpObj (K := fpqc S) (G := G')
    letI := H1.commGroupOfGrpObj (K := fpqc S) (G := G)
    H1 (fpqc S) (yonedaGrpObj G') →* H1 (fpqc S) (yonedaGrpObj G) :=
  H1.mapHom (isSheaf_yonedaGrpObj G') (isSheaf_yonedaGrpObj G) isCommutative_yonedaGrpObj
    isCommutative_yonedaGrpObj (yonedaGrpObjMap u)

variable {G' G G'' : Over S} [GrpObj G'] [GrpObj G] [GrpObj G''] (u : G' ⟶ G) (v : G ⟶ G'')
  [IsMonHom u] [IsMonHom v]

/-- XI.4: the sequence `1 → G' →u G →v G'' → 1` of group schemes over `S` is exact: `u` is a
kernel of `v` on `T`-valued points for every `S`-scheme `T`, and `v` is faithfully flat and
quasi-compact. By XI.4.2 (applied over `G''`, for `G'` flat and quasi-compact over `S`) this is
SGA's condition that `G` is a principal homogeneous bundle over `G''` under `G' ×_S G''`. -/
structure IsExactSeq : Prop where
  injective (T : Over S) : Function.Injective fun x : T ⟶ G' ↦ x ≫ u
  exact (T : Over S) (g : T ⟶ G) : g ≫ v = 1 ↔ ∃ g' : T ⟶ G', g' ≫ u = g
  flat : Flat v.left
  surjective : Surjective v.left
  quasiCompact : QuasiCompact v.left

variable {u v}

namespace IsExactSeq

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4: an exact sequence of group schemes gives a short exact sequence of the fpqc sheaves of
groups they represent; `v` is locally surjective since it is itself a faithfully flat
quasi-compact covering. -/
theorem isShortExact (h : IsExactSeq u v) :
    PresheafOfGroups.IsShortExact (fpqc S) (yonedaGrpObjMap u) (yonedaGrpObjMap v) where
  injective T := h.injective T.unop
  exact T g := h.exact T.unop g
  locallySurjective T c := by
    have := h.flat
    have := h.surjective
    have := h.quasiCompact
    let R : Sieve T :=
      { arrows V f := ∃ g : V ⟶ G, g ≫ v = f ≫ c
        downward_closed := by
          rintro V W f ⟨g, hg⟩ a
          exact ⟨a ≫ g, by rw [Category.assoc, hg, Category.assoc]⟩ }
    refine ⟨R, ?_, fun V f hf ↦ hf⟩
    rw [GrothendieckTopology.mem_over_iff]
    let w := pullback.snd v.left c.left
    refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
      (Scheme.Hom.singleton_mem_fpqcPrecoverage w))
    rintro W a ⟨_, b, _, ⟨⟩, rfl⟩
    refine (Sieve.overEquiv T R).downward_closed ?_ b
    rw [Sieve.overEquiv_iff]
    refine ⟨Over.homMk (pullback.fst v.left c.left) ?_, ?_⟩
    · change pullback.fst v.left c.left ≫ G.hom = w ≫ T.hom
      rw [← Over.w v, ← Category.assoc, pullback.condition, Category.assoc, Over.w c]
    · ext
      exact pullback.condition

variable (h : IsExactSeq u v)

/-- XI.4.5: the exact sequence of pointed sets
`1 → H⁰(S, G') → H⁰(S, G) → H⁰(S, G'') →∂ H¹(S, G') → H¹(S, G) → H¹(S, G'')`, where
`H⁰(S, G)` is the group of sections `𝟙_ (Over S) ⟶ G` and `H¹` is fpqc cohomology. This is also
the non-commutative variant of XI.4.9. -/
theorem cohomology_exact :
    Function.Injective (fun x : 𝟙_ (Over S) ⟶ G' ↦ x ≫ u) ∧
    (∀ g : 𝟙_ (Over S) ⟶ G, g ≫ v = 1 ↔ ∃ g', g' ≫ u = g) ∧
    (∀ c : 𝟙_ (Over S) ⟶ G'',
      h.isShortExact.connecting (isSheaf_yonedaGrpObj G) (isSheaf_yonedaGrpObj G'')
          Over.mkIdTerminal c = H1.trivialClass _ _ (isSheaf_yonedaGrpObj G') ↔
        ∃ g : 𝟙_ (Over S) ⟶ G, g ≫ v = c) ∧
    (∀ x : H1 (fpqc S) (yonedaGrpObj G'),
      H1.map (yonedaGrpObjMap u) (isSheaf_yonedaGrpObj G) x =
          H1.trivialClass _ _ (isSheaf_yonedaGrpObj G) ↔
        ∃ c, h.isShortExact.connecting (isSheaf_yonedaGrpObj G) (isSheaf_yonedaGrpObj G'')
          Over.mkIdTerminal c = x) ∧
    (∀ y : H1 (fpqc S) (yonedaGrpObj G),
      H1.map (yonedaGrpObjMap v) (isSheaf_yonedaGrpObj G'') y =
          H1.trivialClass _ _ (isSheaf_yonedaGrpObj G'') ↔
        ∃ x, H1.map (yonedaGrpObjMap u) (isSheaf_yonedaGrpObj G) x = y) := by
  refine ⟨h.injective _, h.exact _, fun c ↦ ?_, fun x ↦ ?_, fun y ↦ ?_⟩
  · exact h.isShortExact.connecting_eq_trivialClass_iff (isSheaf_yonedaGrpObj G')
      (isSheaf_yonedaGrpObj G) (isSheaf_yonedaGrpObj G'') Over.mkIdTerminal c
  · obtain ⟨P, rfl⟩ := H1.mk_surjective x
    exact h.isShortExact.map_eq_trivialClass_iff (isSheaf_yonedaGrpObj G)
      (isSheaf_yonedaGrpObj G'') Over.mkIdTerminal P
  · obtain ⟨P, rfl⟩ := H1.mk_surjective y
    refine (h.isShortExact.map_p_eq_trivialClass_iff (isSheaf_yonedaGrpObj G)
      (isSheaf_yonedaGrpObj G'') P).trans ⟨fun ⟨Q, hQ⟩ ↦ ⟨Q.class, hQ⟩, fun ⟨x, hx⟩ ↦ ?_⟩
    obtain ⟨Q, rfl⟩ := H1.mk_surjective x
    exact ⟨Q, hx⟩

/-- XI.4.5: for commutative `G'` and `G`, the coboundary `∂ : H⁰(S, G'') → H¹(S, G')` is a group
homomorphism. -/
noncomputable def connectingHom [IsCommMonObj G'] [IsCommMonObj G] :
    letI := H1.commGroupOfGrpObj (K := fpqc S) (G := G')
    (𝟙_ (Over S) ⟶ G'') →* H1 (fpqc S) (yonedaGrpObj G') :=
  h.isShortExact.connectingHom (isSheaf_yonedaGrpObj G') (isSheaf_yonedaGrpObj G)
    (isSheaf_yonedaGrpObj G'') Over.mkIdTerminal isCommutative_yonedaGrpObj
    isCommutative_yonedaGrpObj

/-- XI.4: the coboundary `∂ c` is represented by the `S`-scheme `v⁻¹(c) = G ×_{G''} S`: the
underlying sheaf of the torsor `p⁻¹(c)` is `Hom(-, G ×_{G''} S)`. -/
noncomputable def fiberTorsorIso (c : Over.mk (𝟙 S) ⟶ G'') :
    (h.isShortExact.fiberTorsor (isSheaf_yonedaGrpObj G) (isSheaf_yonedaGrpObj G'')
      Over.mkIdTerminal c).obj ≅ yoneda.obj (pullback v c) :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    { toFun x := pullback.lift x.1 (Over.mkIdTerminal.from T.unop) x.2
      invFun w := ⟨w ≫ pullback.fst v c, by
        change (w ≫ pullback.fst v c) ≫ v = Over.mkIdTerminal.from T.unop ≫ c
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        congr 1
        exact Over.mkIdTerminal.hom_ext _ _⟩
      left_inv x := Subtype.ext (pullback.lift_fst _ _ _)
      right_inv w := by
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · exact Over.mkIdTerminal.hom_ext _ _ })
    fun {T T'} f ↦ by
      ext x
      apply pullback.hom_ext
      · change pullback.lift (f.unop ≫ x.1) _ _ ≫ pullback.fst v c =
          (f.unop ≫ pullback.lift x.1 _ _) ≫ pullback.fst v c
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        exact (pullback.lift_fst _ _ _).trans
          (congrArg (f.unop ≫ ·) (pullback.lift_fst _ _ _)).symm
      · exact Over.mkIdTerminal.hom_ext _ _

end IsExactSeq

end SGA.SGA1.ExposeXI
