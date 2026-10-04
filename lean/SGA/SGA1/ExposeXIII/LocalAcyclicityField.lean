/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicityBaseChange
import SGA.SGA1.ExposeV.QuotientComponents
import SGA.SGA1.ExposeXIII.LocalAcyclicity
import SGA.SGA1.ExposeXIII.ProperBaseChangeField

/-!
# SGA 1, Exposé XIII, 3.2 1) over a separably closed field (locally noetherian base changes)

XIII.3.2 1) (`SGA.SGA1.ExposeXIII.FieldCohomologicalPropernessStatement`) says that for a coherent
`f : X ⟶ Spec k`, the formation of `f_* F` commutes with every base change `S' ⟶ Spec k`. Over a
separably closed field this is Stacks 0EZY (stated there for a qcqs morphism). For locally
noetherian base changes `S' ⟶ Spec k` (e.g. locally of finite type, or strict localizations of
those) we prove it with no hypothesis on `f`
(`SGA.SGA1.ExposeXIII.isIso_etaleBaseChangeMap_field_of_isSepClosed`), from Stacks 0EZX
(`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_forall_exists`):

* a connected scheme over a separably closed field is geometrically connected
  (`SGA.SGA1.ExposeXIII.geometricallyConnected_of_isSepClosed`; Stacks 0363 for schemes): its
  base change to an algebraic closure `L` of any extension `K` is connected, because
  `Spec L ⟶ Spec k` is universally submersive with geometrically connected fibres (IX.3.4,
  `SGA.SGA1.ExposeXIII.geometricallyConnected_specMap_of_isSepClosed`), and maps onto `X_K`;
* every point of a locally noetherian scheme lies in a quasi-compact connected open
  (`SGA.SGA1.ExposeXIII.exists_isOpen_connectedSpace_compactSpace`).

We also record Stacks 0A3I (`SGA.SGA1.ExposeXIII.isIso_etaleAdjunction_unit_app_pullback_specMap`):
for `k` separably closed, `K/k` any extension and `S` a `k`-scheme, `Γ(S, F) = Γ(S_K, F)`.

The general case (every field `k`, every base change, `f` coherent) is proved by a different
route, through strict localizations (SGA 4 VIII 5.2) and Stacks 0A3H:
`SGA.SGA1.ExposeXIII.fieldCohomologicalPropernessStatement` in
`SGA.SGA1.ExposeXIII.LocalAcyclicityFieldStalks`.

## References

* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0363](https://stacks.math.columbia.edu/tag/0363)
* [Stacks Project, Tag 0A3I](https://stacks.math.columbia.edu/tag/0A3I)
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

/-- A connected scheme over a separably closed field is geometrically connected (Stacks 0363). -/
theorem geometricallyConnected_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [ConnectedSpace X] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ ↦ ?_⟩
  let L := AlgebraicClosure K
  let yK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let a := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have ha : a ≫ yK = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    rw [← Spec.map_comp]
    congr 1
  have hpb := (IsPullback.of_hasPullback (pullback.snd f yK) a).paste_horiz
    (IsPullback.of_hasPullback f yK)
  rw [ha] at hpb
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    geometricallyConnected_specMap_of_isSepClosed k L
  have : ExposeIX.UniversallySubmersive (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    ExposeIX.universallySubmersive_specMap_field k L
  let π := pullback.fst (pullback.snd f yK) a ≫ pullback.fst f yK
  have : GeometricallyConnected π :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.flip ‹_›
  have : ExposeIX.UniversallySubmersive π :=
    MorphismProperty.of_isPullback (P := @ExposeIX.UniversallySubmersive) hpb.flip ‹_›
  have : ConnectedSpace ↥(pullback (pullback.snd f yK) a) :=
    ExposeIX.connectedSpace_of_submersive π
  have : Surjective a := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst (pullback.snd f yK) a).surjective.connectedSpace
    (pullback.fst (pullback.snd f yK) a).continuous

open TopologicalSpace in
/-- Every point of a locally noetherian scheme lies in a quasi-compact connected open subscheme
(a connected component of an affine open neighbourhood). -/
lemma exists_isOpen_connectedSpace_compactSpace {W : Scheme.{u}} [IsLocallyNoetherian W]
    (w : W) : ∃ C : W.Opens, w ∈ C ∧ ConnectedSpace C ∧ CompactSpace C := by
  obtain ⟨A, hA, hwA, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w) trivial
  have : IsNoetherianRing Γ(W, A) := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  have : NoetherianSpace (A : Set W) := noetherianSpace_of_isAffineOpen A hA
  let y : (A : Set W) := ⟨w, hwA⟩
  let C : W.Opens := ⟨Subtype.val '' connectedComponent y,
    A.isOpenEmbedding.isOpenMap _ (ExposeV.isOpen_connectedComponent_of_noetherianSpace y)⟩
  have hC : _root_.IsConnected (C : Set W) :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hCc : IsCompact (C : Set W) :=
    (NoetherianSpace.isCompact _).image continuous_subtype_val
  refine ⟨C, ⟨y, mem_connectedComponent, rfl⟩, ?_, ?_⟩
  · exact Subtype.connectedSpace hC
  · exact isCompact_iff_compactSpace.mp hCc

variable {k : Type u} [Field k] [IsSepClosed k]

/-- **Stacks 0EZY** (Lemma 59.87.3) for locally noetherian base changes: let `k` be separably
closed, `f : X ⟶ Spec k` any morphism and `g : Y' ⟶ Spec k` with `Y'` locally noetherian (e.g. `g`
locally of finite type, or `Y'` a strict localization of such a scheme). Then for the cartesian
square `X' = X ×_k Y'`, the base change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism for
every étale sheaf of sets `F` on `X`. Every étale `Y'`-scheme is covered by quasi-compact connected
opens, which are geometrically connected over `k` (`geometricallyConnected_of_isSepClosed`), so
Stacks 0EZX applies (`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_forall_exists`). Stacks
treats arbitrary `g` by a limit argument (Stacks 59.86.3, SGA 4 VII 5.7), which is not done
here. -/
theorem isIso_etaleBaseChangeMap_of_isSepClosed_of_isLocallyNoetherian {X X' Y' : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {g : Y' ⟶ Spec (.of k)} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    (hsq : IsPullback h f' f g) [IsLocallyNoetherian Y']
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((Scheme.etaleBaseChangeMap hsq.w).app F) := by
  refine Scheme.isIso_etaleBaseChangeMap_of_forall_exists hsq (fun W w ↦ ?_) F
  have : Etale W.hom := W.prop
  have : IsLocallyNoetherian ((Functor.fromPUnit Y').obj W.right) := ‹IsLocallyNoetherian Y'›
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  obtain ⟨C, hwC, hC, hCc⟩ := exists_isOpen_connectedSpace_compactSpace w
  let U : Y'.Etale := Scheme.Etale.mk (C.ι ≫ W.hom)
  let ρ : U ⟶ W := MorphismProperty.Over.homMk C.ι rfl trivial
  have hU : (U.hom ≫ g) ≫ (Scheme.Etale.top (Spec (.of k))).hom = U.hom ≫ g :=
    Category.comp_id _
  let ι : U ⟶ (Scheme.Etale.pullback g).obj (Scheme.Etale.top (Spec (.of k))) :=
    MorphismProperty.Over.homMk (pullback.lift (U.hom ≫ g) U.hom hU) (pullback.lift_snd _ _ _)
      trivial
  have hc : ι.left ≫ pullback.fst (Scheme.Etale.top (Spec (.of k))).hom g = C.ι ≫ W.hom ≫ g :=
    (pullback.lift_fst _ _ _).trans (Category.assoc _ _ _)
  have : Subsingleton ((𝟭 Scheme).obj (Scheme.Etale.top (Spec (.of k))).left) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have : IsIntegral ((𝟭 Scheme).obj (Scheme.Etale.top (Spec (.of k))).left) :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  have : IsAffine ((𝟭 Scheme).obj (Scheme.Etale.top (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  have : ConnectedSpace U.left := hC
  have : CompactSpace U.left := hCc
  refine ⟨U, ρ, ⟨w, hwC⟩, _, ι, rfl, inferInstance, ?_, ?_⟩
  · exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr hCc
  · exact geometricallyConnected_of_isSepClosed (k := k) _

/-- XIII.3.2 1) for a separably closed field `k` and locally noetherian base changes `S' ⟶ Spec k`
(e.g. locally of finite type), for every morphism `f : X ⟶ Spec k` (not necessarily coherent) and
every sheaf of sets `F` on `X`: the formation of `f_* F` commutes with the base change. This is the
part of `FieldCohomologicalPropernessStatement` given by Stacks 0EZY without the limit argument.
For coherent `f`, every field `k` and every `S'`, see
`SGA.SGA1.ExposeXIII.fieldCohomologicalPropernessStatement`. -/
theorem isIso_etaleBaseChangeMap_field_of_isSepClosed {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (F : Sheaf X.smallEtaleTopology (Type u)) {S' Y' X' : Scheme.{u}} (t : S' ⟶ Spec (.of k))
    [IsLocallyNoetherian S'] (s' : Y' ⟶ S') (g : Y' ⟶ Spec (.of k)) (h : X' ⟶ X)
    (f' : X' ⟶ Y') (hY : IsPullback g s' (𝟙 _) t) (hX : IsPullback h f' f g) :
    IsIso ((Scheme.etaleBaseChangeMap hX.w).app F) := by
  have : IsIso s' := hY.flip.isIso_fst_of_isIso
  have : IsLocallyNoetherian Y' := isLocallyNoetherian_of_isOpenImmersion s'
  exact isIso_etaleBaseChangeMap_of_isSepClosed_of_isLocallyNoetherian hX F

/-- `Spec K ⟶ Spec k` is geometrically connected for every field extension `K` of a separably
closed field `k`. -/
lemma geometricallyConnected_specMap_algebraMap (K : Type u) [Field K] [Algebra k K] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  geometricallyConnected_of_isSepClosed _

/-- **Stacks 0A3I**: let `K/k` be an extension of fields with `k` separably closed, `S` a
`k`-scheme and `p : S_K ⟶ S` the projection. Then the unit `F ⟶ p_* p^* F` is an isomorphism for
every étale sheaf of sets `F` on `S`; in particular `Γ(S, F) = Γ(S_K, p^* F)`
(`AlgebraicGeometry.Scheme.bijective_sections_etalePullback_of_geometricallyConnected`). This is
Stacks 0A3H for `p`, which is flat, quasi-compact and geometrically connected as a base change of
`Spec K ⟶ Spec k`. -/
theorem isIso_etaleAdjunction_unit_app_pullback_specMap (K : Type u) [Field K] [Algebra k K]
    {S : Scheme.{u}} (s : S ⟶ Spec (.of k)) (F : Sheaf S.smallEtaleTopology (Type u)) :
    IsIso ((Scheme.etaleAdjunction
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k K))))).unit.app F) := by
  have := geometricallyConnected_specMap_algebraMap (k := k) K
  exact Scheme.isIso_etaleAdjunction_unit_app_of_geometricallyConnected _ F

end SGA.SGA1.ExposeXIII
