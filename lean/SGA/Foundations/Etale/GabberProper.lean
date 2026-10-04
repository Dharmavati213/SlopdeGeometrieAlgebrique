/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.GabberZariski
import SGA.Foundations.Etale.LocalAcyclicityStrictLocalization

/-!
# Sections of étale sheaves over a proper scheme over a henselian local ring

Let `q : Z ⟶ Spec A` be proper, `A` a henselian local ring, and `i : Z₀ ⟶ Z` the closed fibre.
For every étale sheaf of sets `F` on `Z`, the restriction `Γ(Z, F) ⟶ Γ(Z₀, i^* F)`
(`AlgebraicGeometry.Scheme.etaleSectionsRestrict i F`) is bijective (Stacks 0A3S; Gabber's theorem,
Stacks 09ZF, 0A0C). This is the input of the proper base change theorem in degree `0` over a
strictly local base.

* Injectivity holds for every universally closed `q` over a local ring
  (`AlgebraicGeometry.injective_etaleSectionsRestrict_of_universallyClosed`): the agreement locus of
  two sections is open and contains the closed fibre, so its closed complement is empty.
* Bijectivity, `A` noetherian, is `ProperHenselianSectionsStatement`, proved in
  `SGA.Foundations.Etale.GabberHenselian` (`AlgebraicGeometry.properHenselianSectionsStatement`,
  `AlgebraicGeometry.bijective_etaleSectionsRestrict_of_henselianLocalRing`). Gabber's proof:
  a section over `Z₀` is étale-locally the restriction of sections of `F`, on affine étale
  neighbourhoods `W` whose whole closed fibre `W ×_Z Z₀` carries the agreement
  (`AlgebraicGeometry.exists_etaleAdjunction_unit_eq_of_isClosedImmersion`, proved); after a finite
  surjective `π : Z' ⟶ Z` which Zariski-locally factors through these étale neighbourhoods
  (Stacks 09Z0, registry row A37) it becomes Zariski-locally liftable, hence liftable
  (`AlgebraicGeometry.exists_eq_of_forall_closedFibre_of_henselianLocalRing`, Stacks 0A0B, row A35),
  and the lift descends along `π` (row A36,
  `AlgebraicGeometry.Scheme.exists_etaleAdjunction_unit_eq_of_surjective`) once it is étale-locally
  the image of sections of `F`, which holds near the closed fibre and hence everywhere by
  properness. The case of sheaves represented by separated étale `Z`-schemes is
  `SGA.SGA1.ExposeXIII.exists_section_of_henselianLocalRing` (without Gabber's argument).

## References

* [Stacks Project, Tag 0A3S](https://stacks.math.columbia.edu/tag/0A3S)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
* [Stacks Project, Tag 0A0C](https://stacks.math.columbia.edu/tag/0A0C)
* [SGA 4, Exposé XII, 5.5][sga4]
-/

universe u

open CategoryTheory Limits Opposite IsLocalRing

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry

/-- The spectrum of a field maps onto the closed point of `Spec A` under a local homomorphism. -/
lemma range_specMap_eq_singleton_closedPoint {A : CommRingCat.{u}} [IsLocalRing A] {K : Type u}
    [Field K] (φ : A ⟶ .of K) [IsLocalHom φ.hom] : Set.range (Spec.map φ) = {closedPoint A} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨closedPoint K, (Spec_closedPoint (f := φ)).trans hx.symm⟩⟩
  rintro ⟨t, rfl⟩
  rw [Subsingleton.elim t (closedPoint K)]
  exact Spec_closedPoint

/-- **Injectivity of `Γ(Z, F) ⟶ Γ(Z₀, i^* F)`** for `Z` universally closed over a local ring and
`Z₀ = Z ×_A T` the base change along `r : T ⟶ Spec A` with image the closed point (for instance
the closed fibre, or a geometric fibre over the closed point): two global sections of `F` with the
same restriction to `Z₀` agree near every point of the closed fibre, hence everywhere. -/
theorem injective_etaleSectionsRestrict_of_range_eq_closedPoint {A : CommRingCat.{u}}
    [IsLocalRing A] {Z Z₀ T : Scheme.{u}} (q : Z ⟶ Spec A) [UniversallyClosed q] {i : Z₀ ⟶ Z}
    {q₀ : Z₀ ⟶ T} {r : T ⟶ Spec A} (hi : IsPullback i q₀ q r) (hr : Set.range r = {closedPoint A})
    (F : Sheaf Z.smallEtaleTopology (Type u)) :
    Function.Injective (Scheme.etaleSectionsRestrict i F) := by
  intro σ σ' h
  have hr' := Scheme.range_subset_etaleAgreementLocus i
    (Scheme.Etale.sectionOfHom i (Scheme.Etale.top Z) i (Category.comp_id i)) h
  have hri : Set.range i ⊆ Scheme.etaleAgreementLocus F σ σ' := by
    rintro _ ⟨z₀, rfl⟩
    refine hr' ⟨z₀, ?_⟩
    change (pullback.lift i (𝟙 Z₀) _ ≫ pullback.fst (𝟙 Z) i) z₀ = i z₀
    rw [pullback.lift_fst]
  obtain ⟨t, ht⟩ : closedPoint A ∈ Set.range r := hr ▸ rfl
  have hc := eq_empty_of_isClosed_of_forall_ne_closedPoint q
    (Scheme.isOpen_etaleAgreementLocus σ σ').isClosed_compl fun z hz hzm ↦ by
      obtain ⟨z₀, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hi z t (hzm.trans ht.symm)
      exact hz (hri ⟨z₀, rfl⟩)
  have := Scheme.map_eq_of_range_subset_etaleAgreementLocus (𝟙 (Scheme.Etale.top Z))
    (s := σ) (t := σ') fun z _ ↦ by
      by_contra hz
      exact (Set.eq_empty_iff_forall_notMem.1 hc) z hz
  simpa using this

/-- **Injectivity of `Γ(Z, F) ⟶ Γ(Z₀, i^* F)`** for `Z` universally closed over a local ring and
`Z₀` its closed fibre (any cartesian square). -/
theorem injective_etaleSectionsRestrict_of_universallyClosed {A : CommRingCat.{u}} [IsLocalRing A]
    {Z Z₀ : Scheme.{u}} (q : Z ⟶ Spec A) [UniversallyClosed q] {i : Z₀ ⟶ Z}
    {q₀ : Z₀ ⟶ Spec (.of (ResidueField A))}
    (hi : IsPullback i q₀ q (Spec.map (CommRingCat.ofHom (residue A))))
    (F : Sheaf Z.smallEtaleTopology (Type u)) :
    Function.Injective (Scheme.etaleSectionsRestrict i F) :=
  have : IsLocalHom (CommRingCat.ofHom (residue A)).hom := inferInstanceAs (IsLocalHom (residue A))
  injective_etaleSectionsRestrict_of_range_eq_closedPoint q hi
    (range_specMap_eq_singleton_closedPoint _) F

/-- **Stacks 0A3S, noetherian case** (Gabber's theorem for proper schemes): for
`q : Z ⟶ Spec A` proper, `A` a noetherian henselian local ring, and every étale sheaf of sets `F`
on `Z`, the restriction `Γ(Z, F) ⟶ Γ(Z₀, F)` to the closed fibre `Z₀ = Z ×_A κ` is bijective.
Injectivity is `injective_etaleSectionsRestrict_of_universallyClosed` (any local `A`). Proved:
`AlgebraicGeometry.properHenselianSectionsStatement` (`SGA.Foundations.Etale.GabberHenselian`). -/
def ProperHenselianSectionsStatement : Prop :=
  ∀ (A : CommRingCat.{u}) [HenselianLocalRing A] [IsNoetherianRing A] (Z : Scheme.{u})
    (q : Z ⟶ Spec A) [IsProper q] (F : Sheaf Z.smallEtaleTopology (Type u)),
    Function.Bijective
      (Scheme.etaleSectionsRestrict (pullback.fst q (Spec.map (CommRingCat.ofHom (residue A)))) F)

/-- **Local lifts of sections over a closed subscheme** (the first step of Gabber's proof,
Stacks 09ZF): for a closed immersion `i : Z₀ ⟶ Z`, an étale sheaf `F` on `Z`, a section `τ₀` of
`i^* F` over `Z₀` and a point `z₀` of `Z₀`, there are an affine étale `Z`-scheme `W`, a point of
`W ×_Z Z₀` over `z₀` and a section `a ∈ F(W)` whose restriction to `W ×_Z Z₀` is the restriction of
`τ₀` (the agreement locus is open in `W ×_Z Z₀`, which is closed in `W`, so `W` can be shrunk). -/
theorem exists_etaleAdjunction_unit_eq_of_isClosedImmersion {Z Z₀ : Scheme.{u}} (i : Z₀ ⟶ Z)
    [IsClosedImmersion i] (F : Sheaf Z.smallEtaleTopology (Type u))
    (τ₀ : ((Scheme.etalePullback i).obj F).obj.obj (op (Scheme.Etale.top Z₀))) (z₀ : Z₀) :
    ∃ (W : Z.Etale) (a : F.obj.obj (op W)) (w : ((Scheme.Etale.pullback i).obj W).left),
      ((Scheme.Etale.pullback i).obj W).hom w = z₀ ∧ IsAffine W.left ∧
      ((Scheme.etaleAdjunction i).unit.app F).hom.app (op W) a =
        ((Scheme.etalePullback i).obj F).obj.map
          ((Scheme.Etale.isTerminalTop Z₀).from ((Scheme.Etale.pullback i).obj W)).op τ₀ := by
  let G := (Scheme.etalePullback i).obj F
  let η := (Scheme.etaleAdjunction i).unit.app F
  obtain ⟨W, a, w, hwz, hw⟩ := Scheme.exists_mem_etaleAgreementLocus_etaleAdjunction_unit F i τ₀ z₀
  let L := Scheme.etaleAgreementLocus G
    (G.obj.map ((Scheme.Etale.isTerminalTop Z₀).from ((Scheme.Etale.pullback i).obj W)).op τ₀)
    (η.hom.app (op W) a)
  let j := pullback.fst W.hom i
  have hj : Topology.IsClosedEmbedding j := j.isClosedEmbedding
  have hLo : IsOpen L := Scheme.isOpen_etaleAgreementLocus _ _
  let O : Set W.left := (j '' Lᶜ)ᶜ
  have hO : IsOpen O := (hj.isClosedMap _ hLo.isClosed_compl).isOpen_compl
  have hjw : j w ∈ O := by
    rintro ⟨w', hw', hjw'⟩
    exact hw' (hj.injective hjw' ▸ hw)
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hwV, hVO⟩ :=
    W.left.isBasis_affineOpens.exists_subset_of_mem_open hjw hO
  let V : W.left.Opens := V₀
  let W' : Z.Etale := Scheme.Etale.mk (V.ι ≫ W.hom)
  let ψ : W' ⟶ W := MorphismProperty.Over.homMk V.ι rfl trivial
  have e : (V.ι ≫ W.hom) ⟨j w, hwV⟩ = i z₀ := by
    have e₁ := congrArg (fun φ ↦ φ w) (pullback.condition (f := W.hom) (g := i))
    simp only [Scheme.Hom.comp_apply] at e₁ ⊢
    rw [Scheme.Opens.ι_apply]
    exact e₁.trans (congrArg i hwz)
  obtain ⟨w', -, hw'⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.ι ≫ W.hom) (g := i)
    ⟨j w, hwV⟩ z₀ e
  refine ⟨W', F.obj.map ψ.op a, w', hw', hV, ?_⟩
  have nat : η.hom.app (op W') (F.obj.map ψ.op a) =
      G.obj.map ((Scheme.Etale.pullback i).map ψ).op (η.hom.app (op W) a) :=
    NatTrans.naturality_apply η.hom ψ.op a
  have hrange : Set.range ((Scheme.Etale.pullback i).map ψ).left ⊆ L := by
    rintro _ ⟨p, rfl⟩
    by_contra hp
    have h₁ := congrArg (fun φ ↦ φ p) (Scheme.Etale.pullback_map_left_fst i ψ)
    simp only [Scheme.Hom.comp_apply] at h₁
    have h₂ : V.ι (pullback.fst W'.hom i p) ∈ O := hVO ((Scheme.Opens.range_ι V).le ⟨_, rfl⟩)
    exact h₂ ⟨_, hp, h₁⟩
  have H := Scheme.map_eq_of_range_subset_etaleAgreementLocus _ hrange
  rw [nat, ← H, ← Functor.map_comp_apply, ← op_comp,
    (Scheme.Etale.isTerminalTop Z₀).hom_ext (_ ≫ (Scheme.Etale.isTerminalTop Z₀).from _)
      ((Scheme.Etale.isTerminalTop Z₀).from _)]

end AlgebraicGeometry
