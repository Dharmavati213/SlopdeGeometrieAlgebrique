/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.TorsorCech
import SGA.SGA1.ExposeXI.GroupSheaves
import SGA.SGA1.ExposeXI.PrincipalBundle

/-!
# SGA 1, Exposé XI.4.7: locally trivial principal bundles and Zariski cohomology

Let `S` be a scheme and `G` a sheaf of groups on the fpqc site of `S`-schemes (for instance the
sheaf of points of a group scheme). Its restriction to the open subsets of `S` is the sheaf
`𝒪_S(G)` of sections of `G` (`zariskiSheaf`, with the inclusion `opensToOver S` of the open
subschemes), a sheaf for the Zariski topology (`isSheaf_opensToOver`).

XI.4.7: an fpqc torsor under `G` is *locally trivial* if it has sections over the members of an
open covering of `S`. Such a torsor restricts to a torsor under `𝒪_S(G)` on the Zariski site
(`Torsor.zariskiRestrict`), and this gives a bijection between the classes of locally trivial
torsors and `H¹(S_Zar, 𝒪_S(G))` (`locallyTrivialH1Equiv`).
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable (S : Scheme.{u})

/-- The open subschemes of `S`, as `S`-schemes. -/
@[simps obj]
noncomputable def opensToOver : S.Opens ⥤ Over S where
  obj U := Over.mk U.ι
  map {U V} h := Over.homMk (S.homOfLE (leOfHom h)) (S.homOfLE_ι _)
  map_id U := by
    ext1
    exact S.homOfLE_rfl U
  map_comp f g := by
    ext1
    exact (S.homOfLE_homOfLE (leOfHom f) (leOfHom g)).symm

variable {S}

@[simp]
lemma opensToOver_map_left {U V : S.Opens} (h : U ⟶ V) :
    ((opensToOver S).map h).left = S.homOfLE (leOfHom h) :=
  rfl

/-- There is at most one morphism of `S`-schemes to an open subscheme of `S`. -/
instance (W : Over S) (V : S.Opens) : Subsingleton (W ⟶ (opensToOver S).obj V) :=
  ⟨fun a b ↦ Over.OverMorphism.ext ((cancel_mono V.ι).1 ((Over.w a).trans (Over.w b).symm))⟩

/-- The morphism from an `S`-scheme whose image lies in the open `V` to the open subscheme `V`. -/
noncomputable def homOpensToOver (W : Over S) (V : S.Opens) (h : Set.range W.hom ⊆ V) :
    W ⟶ (opensToOver S).obj V :=
  Over.homMk (show W.left ⟶ (V : Scheme) from
      IsOpenImmersion.lift V.ι W.hom (by rwa [Scheme.Opens.range_ι]))
    (IsOpenImmersion.lift_fac V.ι W.hom _)

lemma range_hom_subset_of_hom {W : Over S} {V : S.Opens} (a : W ⟶ (opensToOver S).obj V) :
    Set.range W.hom ⊆ V := by
  rw [← Over.w a, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact (Set.image_subset_range _ _).trans (Scheme.Opens.range_ι V).le

/-- A morphism to two open subschemes factors through their intersection. -/
noncomputable def homInf {W : Over S} {V₁ V₂ : S.Opens} (a : W ⟶ (opensToOver S).obj V₁)
    (b : W ⟶ (opensToOver S).obj V₂) : W ⟶ (opensToOver S).obj (V₁ ⊓ V₂) :=
  homOpensToOver W _ fun _ hx ↦ ⟨range_hom_subset_of_hom a hx, range_hom_subset_of_hom b hx⟩

variable {F : (Over S)ᵒᵖ ⥤ Type u}

/-- XI.4.7: the restriction of an fpqc sheaf on `S`-schemes to the open subsets of `S` is a sheaf
for the Zariski topology. -/
theorem isSheaf_opensToOver (hF : Presieve.IsSheaf (fpqc S) F) :
    Presieve.IsSheaf (Opens.grothendieckTopology S) ((opensToOver S).op ⋙ F) := by
  intro (U : S.Opens) R hR x hx
  have compat : ∀ ⦃W : Over S⦄ ⦃V₁ V₂ : S.Opens⦄ (h₁ : V₁ ⟶ U) (h₂ : V₂ ⟶ U) (hV₁ : R h₁)
      (hV₂ : R h₂) (k₁ : W ⟶ (opensToOver S).obj V₁) (k₂ : W ⟶ (opensToOver S).obj V₂),
      F.map k₁.op (x h₁ hV₁) = F.map k₂.op (x h₂ hV₂) := by
    intro W V₁ V₂ h₁ h₂ hV₁ hV₂ k₁ k₂
    have e₁ : k₁ = homInf k₁ k₂ ≫ (opensToOver S).map (homOfLE inf_le_left) :=
      Subsingleton.elim _ _
    have e₂ : k₂ = homInf k₁ k₂ ≫ (opensToOver S).map (homOfLE inf_le_right) :=
      Subsingleton.elim _ _
    have hc := hx (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) (homOfLE inf_le_right) hV₁ hV₂
      (Subsingleton.elim _ _)
    rw [e₁, e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congr_arg (F.map (homInf k₁ k₂).op) hc
  let R' : Sieve ((opensToOver S).obj U) := Sieve.functorPushforward (opensToOver S) R
  let y : Presieve.FamilyOfElements F R'.arrows := fun W g hg ↦
    F.map hg.choose_spec.choose_spec.choose.op (x _ hg.choose_spec.choose_spec.choose_spec.1)
  have hy : ∀ ⦃W : Over S⦄ (g : W ⟶ (opensToOver S).obj U) (hg : R' g) ⦃V : S.Opens⦄
      (h : V ⟶ U) (hV : R h) (k : W ⟶ (opensToOver S).obj V), y g hg = F.map k.op (x h hV) :=
    fun _ _ _ _ _ _ _ ↦ compat _ _ _ _ _ _
  have hyc : y.Compatible := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    obtain ⟨V₁, a₁, k₁, ha₁, -⟩ := id h₁
    obtain ⟨V₂, a₂, k₂, ha₂, -⟩ := id h₂
    rw [hy f₁ h₁ a₁ ha₁ k₁, hy f₂ h₂ a₂ ha₂ k₂, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp]
    exact compat _ _ _ _ _ _
  have hR' : R' ∈ fpqc S ((opensToOver S).obj U) := by
    rw [GrothendieckTopology.mem_over_iff]
    have hpt (y : (U : Scheme)) : ∃ (V : S.Opens) (h : V ⟶ U), R h ∧ y.1 ∈ V :=
      hR y.1 y.2
    choose V h hV hyV using hpt
    let 𝒰 : Scheme.OpenCover.{u} U :=
      Scheme.Cover.mkOfCovers U (fun y ↦ (U.ι ⁻¹ᵁ V y : Scheme)) (fun y ↦ (U.ι ⁻¹ᵁ V y).ι)
        fun y ↦ ⟨y, ⟨y, hyV y⟩, rfl⟩
    refine mem_fpqcTopology_of_openCover _ 𝒰 (fun y ↦ 𝒰.X y) (fun y ↦ 𝟙 _)
      (fun y ↦ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩) fun y ↦ ?_
    rw [Sieve.overEquiv_iff]
    refine ⟨V y, h y, homOpensToOver _ (V y) ?_, hV y, Subsingleton.elim _ _⟩
    change Set.range ((𝟙 _ ≫ (U.ι ⁻¹ᵁ V y).ι) ≫ U.ι) ⊆ V y
    rw [Category.id_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι, Set.image_subset_iff]
    exact fun z hz ↦ hz
  obtain ⟨t, ht, ht'⟩ := hF R' hR' y hyc
  refine ⟨t, fun V h hV ↦ ?_, fun t' ht'' ↦ ht' t' fun W g hg ↦ ?_⟩
  · have hg : R' ((opensToOver S).map h) := ⟨V, h, 𝟙 _, hV, (Category.id_comp _).symm⟩
    change F.map ((opensToOver S).map h).op t = x h hV
    rw [ht _ hg, hy _ hg h hV (𝟙 _), op_id, F.map_id]
    rfl
  · obtain ⟨V, a, k, ha, e⟩ := id hg
    rw [hy g hg a ha k, e, op_comp, Functor.map_comp_apply]
    exact congr_arg (F.map k.op) (ht'' a ha)


/-- The open subschemes `Uᵢ` of an open covering of `S` cover the final object of the fpqc site
of `S`-schemes. -/
lemma coversTop_opensToOver {ι : Type*} (U : ι → S.Opens) (hU : ∀ x : S, ∃ i, x ∈ U i) :
    (fpqc S).CoversTop fun i ↦ (opensToOver S).obj (U i) := by
  intro Y
  rw [GrothendieckTopology.mem_over_iff]
  choose idx hidx using hU
  let 𝒰 : Scheme.OpenCover.{u} Y.left :=
    Scheme.Cover.mkOfCovers Y.left (fun y ↦ (Y.hom ⁻¹ᵁ U (idx (Y.hom y)) : Scheme))
      (fun y ↦ (Y.hom ⁻¹ᵁ U (idx (Y.hom y))).ι) fun y ↦ ⟨y, ⟨y, hidx _⟩, rfl⟩
  refine mem_fpqcTopology_of_openCover _ 𝒰 (fun y ↦ 𝒰.X y) (fun y ↦ 𝟙 _)
    (fun y ↦ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩) fun y ↦ ?_
  rw [Sieve.overEquiv_iff]
  refine ⟨idx (Y.hom y), ⟨homOpensToOver _ _ ?_⟩⟩
  change Set.range ((𝟙 _ ≫ (Y.hom ⁻¹ᵁ U (idx (Y.hom y))).ι) ≫ Y.hom) ⊆ U (idx (Y.hom y))
  rw [Category.id_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.Opens.range_ι, Set.image_subset_iff]
  exact fun z hz ↦ hz

section Torsor

variable (G : (Over S)ᵒᵖ ⥤ GrpCat.{u})

/-- XI.4.7: the Zariski sheaf `𝒪_S(G)` of sections of `G` over the open subsets of `S`. -/
noncomputable abbrev zariskiSheaf : S.Opensᵒᵖ ⥤ GrpCat.{u} :=
  (opensToOver S).op ⋙ G

variable {G}

lemma isSheaf_zariskiSheaf (hG : Presieve.IsSheaf (fpqc S) (G ⋙ CategoryTheory.forget GrpCat)) :
    Presieve.IsSheaf (Opens.grothendieckTopology S)
      (zariskiSheaf G ⋙ CategoryTheory.forget GrpCat) :=
  isSheaf_opensToOver hG

/-- XI.4.7: an fpqc torsor under `G` is locally trivial if it has sections over the members of
an open covering of `S`. -/
def IsLocallyTrivial (Q : Torsor (fpqc S) G) : Prop :=
  ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ Nonempty (Q.obj.obj (op ((opensToOver S).obj U)))

/-- XI.4.7: the restriction of a locally trivial fpqc torsor to the Zariski site of `S`, a torsor
under `𝒪_S(G)`. -/
@[simps obj]
noncomputable def zariskiRestrict (Q : Torsor (fpqc S) G) (hQ : IsLocallyTrivial Q) :
    Torsor (Opens.grothendieckTopology S) (zariskiSheaf G) where
  obj := (opensToOver S).op ⋙ Q.obj
  isSheaf := isSheaf_opensToOver Q.isSheaf
  smul U := Q.smul ((opensToOver S).op.obj U)
  one_smul U := Q.one_smul _
  mul_smul U := Q.mul_smul _
  map_smul f := Q.map_smul _
  existsUnique_smul U := Q.existsUnique_smul _
  locallyNonempty U := by
    refine ⟨((opensToOver S).op ⋙ Q.obj).nonemptySieve' U, fun x hx ↦ ?_, fun _ _ h ↦ h⟩
    obtain ⟨V, hxV, ⟨s⟩⟩ := hQ x
    exact ⟨U ⊓ V, homOfLE inf_le_left,
      ⟨Q.obj.map ((opensToOver S).map (homOfLE inf_le_right)).op s⟩, hx, hxV⟩

lemma zariskiRestrict_diff (Q : Torsor (fpqc S) G) (hQ : IsLocallyTrivial Q) {V : S.Opens}
    (x y : Q.obj.obj (op ((opensToOver S).obj V))) :
    (zariskiRestrict Q hQ).diff x y = Q.diff x y :=
  (zariskiRestrict Q hQ).diff_eq_iff.2 (Q.diff_smul x y)

/-- The morphism of restrictions induced by a morphism of torsors. -/
@[simps]
noncomputable def zariskiRestrictMap {Q Q' : Torsor (fpqc S) G} (hQ : IsLocallyTrivial Q)
    (hQ' : IsLocallyTrivial Q') (φ : Q ⟶ Q') : zariskiRestrict Q hQ ⟶ zariskiRestrict Q' hQ' where
  hom := Functor.whiskerLeft (opensToOver S).op φ.hom
  map_smul _ g x := φ.map_smul _ g x

variable (G) in
/-- A class in `H¹(S, G)` is locally trivial if it is the class of a locally trivial torsor
(then all its representatives are locally trivial). -/
def IsLocallyTrivialClass (c : H1 (fpqc S) G) : Prop :=
  ∃ Q : Torsor (fpqc S) G, IsLocallyTrivial Q ∧ Q.class = c

lemma isLocallyTrivial_of_iso {Q Q' : Torsor (fpqc S) G} (e : Q ⟶ Q') (hQ : IsLocallyTrivial Q) :
    IsLocallyTrivial Q' := fun x ↦ by
  obtain ⟨U, hxU, ⟨s⟩⟩ := hQ x
  exact ⟨U, hxU, ⟨e.hom.app _ s⟩⟩

/-- XI.4.7, injectivity: two locally trivial torsors whose restrictions to the Zariski site are
isomorphic are isomorphic. -/
theorem nonempty_iso_of_zariskiRestrict {Q Q' : Torsor (fpqc S) G} (hQ : IsLocallyTrivial Q)
    (hQ' : IsLocallyTrivial Q') (e : zariskiRestrict Q hQ ⟶ zariskiRestrict Q' hQ') :
    Nonempty (Q ≅ Q') := by
  have hQ₀ := hQ
  choose U hxU hs using hQ₀
  let s x := (hs x).some
  let s' : ∀ x, Q'.obj.obj (op ((opensToOver S).obj (U x))) := fun x ↦ e.hom.app (op (U x)) (s x)
  refine Torsor.nonempty_iso_of_isCohomologous (U := fun x ↦ (opensToOver S).obj (U x)) Q s
    (coversTop_opensToOver U fun x ↦ ⟨x, hxU x⟩) s' ⟨1, fun i j T a b ↦ ?_⟩
  change G.map a.op 1 * Q.diff _ _ = Q'.diff _ _ * G.map b.op 1
  rw [map_one, map_one, one_mul, mul_one]
  obtain ⟨m, hm⟩ : ∃ m, m = homInf a b := ⟨_, rfl⟩
  have ha : a = m ≫ (opensToOver S).map (homOfLE inf_le_left) := Subsingleton.elim _ _
  have hb : b = m ≫ (opensToOver S).map (homOfLE inf_le_right) := Subsingleton.elim _ _
  rw [ha, hb, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    Functor.map_comp_apply, Functor.map_comp_apply, ← Q.map_diff, ← Q'.map_diff]
  congr 1
  have n₁ : Q'.obj.map ((opensToOver S).map (homOfLE inf_le_left)).op (s' i) =
      e.hom.app (op (U i ⊓ U j))
        (Q.obj.map ((opensToOver S).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).op (s i)) :=
    (NatTrans.naturality_apply e.hom (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i)).symm
  have n₂ : Q'.obj.map ((opensToOver S).map (homOfLE inf_le_right)).op (s' j) =
      e.hom.app (op (U i ⊓ U j))
        (Q.obj.map ((opensToOver S).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).op (s j)) :=
    (NatTrans.naturality_apply e.hom (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j)).symm
  rw [n₁, n₂]
  exact ((zariskiRestrict_diff Q hQ _ _).symm.trans (Torsor.diff_hom_app _ e _ _).symm).trans
    (zariskiRestrict_diff Q' hQ' _ _)

/-- A torsor on the Zariski site of `S` has sections over a neighbourhood of every point. -/
lemma exists_section_zariski {H : S.Opensᵒᵖ ⥤ GrpCat.{u}}
    (P : Torsor (Opens.grothendieckTopology S) H) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ Nonempty (P.obj.obj (op V)) := by
  obtain ⟨V, f, hf, hx⟩ :=
    ((Opens.mem_grothendieckTopology S).1 (P.nonemptySieve_mem ⊤)) x _root_.trivial
  exact ⟨V, hx, hf⟩

lemma coversTop_zariski {ι : Type*} (U : ι → S.Opens) (hU : ∀ x : S, ∃ i, x ∈ U i) :
    (Opens.grothendieckTopology S).CoversTop U := by
  intro V y hy
  obtain ⟨i, hi⟩ := hU y
  exact ⟨V ⊓ U i, homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩, hy, hi⟩

variable (hG : Presieve.IsSheaf (fpqc S) (G ⋙ CategoryTheory.forget GrpCat))

section Extension

variable {ι : Type u} {U : ι → S.Opens} (hU : ∀ x : S, ∃ i, x ∈ U i)
  (γ : PresheafOfGroups.OneCocycle (zariskiSheaf G) U)

/-- The value of a Zariski cocycle on `Uᵢ ∩ Uⱼ`. -/
noncomputable abbrev zariskiCocycleValue (i j : ι) : G.obj (op ((opensToOver S).obj (U i ⊓ U j))) :=
  γ.ev i j (homOfLE inf_le_left) (homOfLE inf_le_right)

lemma zariskiCocycleValue_map {T : Over S} {i j : ι} (a : T ⟶ (opensToOver S).obj (U i))
    (b : T ⟶ (opensToOver S).obj (U j)) {W : S.Opens} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (m : T ⟶ (opensToOver S).obj W) :
    G.map (homInf a b).op (zariskiCocycleValue γ i j) =
      G.map m.op (γ.ev i j (homOfLE hWi) (homOfLE hWj)) := by
  have e : homInf a b = m ≫ (opensToOver S).map (homOfLE (le_inf hWi hWj)) :=
    Subsingleton.elim _ _
  rw [e, op_comp, Functor.map_comp_apply]
  congr 1
  exact γ.ev_precomp i j (homOfLE (le_inf hWi hWj)) (homOfLE inf_le_left)
    (homOfLE inf_le_right)

/-- XI.4.7: the fpqc cocycle on the open subschemes `Uᵢ` defined by a Zariski cocycle. -/
noncomputable def fpqcCocycle :
    PresheafOfGroups.OneCocycle G fun i ↦ (opensToOver S).obj (U i) where
  ev i j T a b := G.map (homInf a b).op (zariskiCocycleValue γ i j)
  ev_precomp i j T T' φ a b := by
    rw [← Functor.map_comp_apply, ← op_comp]
    exact congr_arg (fun m ↦ G.map (Quiver.Hom.op m) (zariskiCocycleValue γ i j))
      (Subsingleton.elim _ _)
  ev_trans i j k T a b c := by
    let m := homInf (homInf a b) c
    rw [zariskiCocycleValue_map γ a b (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right) m,
      zariskiCocycleValue_map γ b c (inf_le_left.trans inf_le_right) inf_le_right m,
      zariskiCocycleValue_map γ a c (inf_le_left.trans inf_le_left) inf_le_right m,
      ← map_mul, γ.ev_trans]

lemma fpqcCocycle_ev_map {W : S.Opens} (i j : ι) (a : W ⟶ U i) (b : W ⟶ U j) :
    (fpqcCocycle γ).ev i j ((opensToOver S).map a) ((opensToOver S).map b) = γ.ev i j a b := by
  change G.map _ (zariskiCocycleValue γ i j) = _
  rw [zariskiCocycleValue_map γ _ _ (leOfHom a) (leOfHom b) (𝟙 _), op_id, G.map_id]
  rfl

/-- XI.4.7: the fpqc torsor glued from a Zariski cocycle. -/
noncomputable def fpqcTorsorOfCocycle : Torsor (fpqc S) G :=
  (fpqcCocycle γ).torsor hG (coversTop_opensToOver U hU)

lemma isLocallyTrivial_fpqcTorsorOfCocycle :
    IsLocallyTrivial (fpqcTorsorOfCocycle hG hU γ) := fun x ↦ by
  obtain ⟨i, hi⟩ := hU x
  exact ⟨U i, hi, ⟨(fpqcCocycle γ).torsorSection hG (coversTop_opensToOver U hU) i⟩⟩

end Extension

include hG in
/-- XI.4.7, surjectivity: every torsor under `𝒪_S(G)` on the Zariski site is the restriction of a
locally trivial fpqc torsor. -/
theorem exists_zariskiRestrict_iso (P : Torsor (Opens.grothendieckTopology S) (zariskiSheaf G)) :
    ∃ (Q : Torsor (fpqc S) G) (hQ : IsLocallyTrivial Q), Nonempty (zariskiRestrict Q hQ ≅ P) := by
  choose U hxU hs using exists_section_zariski P
  have hU : ∀ x : S, ∃ i, x ∈ U i := fun x ↦ ⟨x, hxU x⟩
  let s x := (hs x).some
  let γ := P.cocycle s
  let Q := fpqcTorsorOfCocycle hG hU γ
  let hQ := isLocallyTrivial_fpqcTorsorOfCocycle hG hU γ
  let e : ∀ x, (zariskiRestrict Q hQ).obj.obj (op (U x)) :=
    fun x ↦ (fpqcCocycle γ).torsorSection hG (coversTop_opensToOver U hU) x
  refine ⟨Q, hQ, Torsor.nonempty_iso_of_isCohomologous _ e (coversTop_zariski U hU) s
    ⟨1, fun i j W a b ↦ ?_⟩⟩
  change (zariskiSheaf G).map a.op 1 * (zariskiRestrict Q hQ).diff _ _ = P.diff _ _ *
    (zariskiSheaf G).map b.op 1
  rw [map_one, map_one, one_mul, mul_one]
  refine (zariskiRestrict_diff Q hQ _ _).trans ?_
  have := (fpqcCocycle γ).torsor_cocycle_ev hG (coversTop_opensToOver U hU) i j
    ((opensToOver S).map a) ((opensToOver S).map b)
  rw [Torsor.cocycle_ev, fpqcCocycle_ev_map] at this
  exact this

lemma zariskiRestrict_class_eq {Q Q' : Torsor (fpqc S) G} (hQ : IsLocallyTrivial Q)
    (hQ' : IsLocallyTrivial Q') (h : Q.class = Q'.class) :
    (zariskiRestrict Q hQ).class = (zariskiRestrict Q' hQ').class := by
  obtain ⟨e⟩ := (Torsor.class_eq_class_iff _ _).1 h
  exact (Torsor.class_eq_class_iff _ _).2 ⟨asIso (zariskiRestrictMap hQ hQ' e.hom)⟩

variable (G) in
/-- XI.4.7: the map from the classes of locally trivial fpqc torsors to `H¹(S_Zar, 𝒪_S(G))`,
induced by restriction to the Zariski site. -/
noncomputable def locallyTrivialToZariski :
    {c : H1 (fpqc S) G // IsLocallyTrivialClass G c} →
      H1 (Opens.grothendieckTopology S) (zariskiSheaf G) :=
  fun c ↦ (zariskiRestrict c.2.choose c.2.choose_spec.1).class

lemma locallyTrivialToZariski_class (Q : Torsor (fpqc S) G) (hQ : IsLocallyTrivial Q) :
    locallyTrivialToZariski G ⟨Q.class, Q, hQ, rfl⟩ = (zariskiRestrict Q hQ).class :=
  zariskiRestrict_class_eq _ _ (⟨Q, hQ, rfl⟩ : IsLocallyTrivialClass G Q.class).choose_spec.2

include hG in
/-- XI.4.7: the classes of locally trivial principal homogeneous bundles (fpqc torsors) under `G`
are in bijection with `H¹(S_Zar, 𝒪_S(G))`, the cohomology of the Zariski sheaf of sections of
`G` (SGA: `H¹(X, 𝒪_X(G))`). -/
theorem bijective_locallyTrivialToZariski : Function.Bijective (locallyTrivialToZariski G) := by
  constructor
  · rintro ⟨c, Q, hQ, rfl⟩ ⟨c', Q', hQ', rfl⟩ h
    rw [locallyTrivialToZariski_class Q hQ, locallyTrivialToZariski_class Q' hQ',
      Torsor.class_eq_class_iff] at h
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := nonempty_iso_of_zariskiRestrict hQ hQ' e.hom
    exact Subtype.ext ((Torsor.class_eq_class_iff _ _).2 ⟨e'⟩)
  · intro d
    obtain ⟨P, rfl⟩ := H1.mk_surjective d
    obtain ⟨Q, hQ, ⟨e⟩⟩ := exists_zariskiRestrict_iso hG P
    exact ⟨⟨Q.class, Q, hQ, rfl⟩, by
      rw [locallyTrivialToZariski_class Q hQ]
      exact (Torsor.class_eq_class_iff _ _).2 ⟨e⟩⟩

/-- XI.4.7: the bijection between the classes of locally trivial fpqc torsors under `G` and
`H¹(S_Zar, 𝒪_S(G))`. -/
noncomputable def locallyTrivialH1Equiv :
    {c : H1 (fpqc S) G // IsLocallyTrivialClass G c} ≃
      H1 (Opens.grothendieckTopology S) (zariskiSheaf G) :=
  Equiv.ofBijective _ (bijective_locallyTrivialToZariski hG)

omit hG in
/-- If every fpqc torsor under `G` is locally trivial, so is every class. -/
lemma isLocallyTrivialClass_of_forall (h : ∀ Q : Torsor (fpqc S) G, IsLocallyTrivial Q)
    (c : H1 (fpqc S) G) : IsLocallyTrivialClass G c := by
  obtain ⟨Q, rfl⟩ := H1.mk_surjective c
  exact ⟨Q, h Q, rfl⟩

/-- XI.5.3 (formal part): if every fpqc torsor under `G` is locally trivial (XI.5.1), restriction
to the Zariski site is a bijection `H¹(S, G) ≅ H¹(S_Zar, 𝒪_S(G))`. -/
noncomputable def h1EquivOfLocallyTrivial (h : ∀ Q : Torsor (fpqc S) G, IsLocallyTrivial Q) :
    H1 (fpqc S) G ≃ H1 (Opens.grothendieckTopology S) (zariskiSheaf G) :=
  (Equiv.subtypeUnivEquiv (isLocallyTrivialClass_of_forall h)).symm.trans
    (locallyTrivialH1Equiv hG)

end Torsor

end SGA.SGA1.ExposeXI
