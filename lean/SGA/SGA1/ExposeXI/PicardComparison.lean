/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.Picard
import SGA.SGA1.ExposeXI.KummerCohomology
import SGA.SGA1.ExposeXI.MultiplicativeTorsors

/-!
# SGA 1, Exposé XI.5.1 and XI.5.3 for `𝔾_m`: fpqc torsors and the Picard group

The Zariski sheaf of sections of `𝔾_{m,S}` is the sheaf of units `𝒪_S^×` (`zariskiGmIso`), so
by XI.4.7 the classes of locally trivial fpqc torsors under `𝔾_{m,S}` are in bijection with
`Pic(S) = H¹(S_Zar, 𝒪_S^×)` (`SGA.Foundations.Etale.Picard`); the bijection is a group
isomorphism for the contracted product (`zariskiRestrict_mul`).

XI.5.1 for `𝔾_m` says that every principal homogeneous bundle under `𝔾_{m,S}` is locally trivial
(Hilbert's theorem 90); this is `isLocallyTrivial_Gm` (`MultiplicativeTorsors`). We obtain XI.5.3
for `𝔾_m`, `H¹(S, 𝔾_m) ≅ Pic(S)` (`h1GmMulEquivPic`), and XI.6.4–XI.6.6 in SGA's form, with
`ₙPic(S)` (`kummer_exact_pic`, `kummerLeft_bijective_of_pic`, `kummerRightPic_bijective`).

We also prove the example of XI.6.5: the Picard group of a scheme with a point whose only open
neighbourhood is the whole scheme (e.g. the spectrum of a local ring) is trivial
(`Pic_subsingleton_of_forall_mem`), so that `H¹(S, μ_n) ≅ Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ` there
(`kummerLeft_bijective_of_forall_mem`).
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable {S : Scheme.{u}}

section Units

lemma homOfLE_appTop_topIso {U V : S.Opens} (h : V ≤ U) :
    (S.homOfLE h).appTop ≫ V.topIso.hom = U.topIso.hom ≫ S.presheaf.map (homOfLE h).op := by
  rw [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom, Scheme.Opens.topIso_hom]
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

variable (S) in
/-- XI.5.3: the Zariski sheaf of sections of `𝔾_{m,S}` is the sheaf of units `𝒪_S^×`. -/
noncomputable def zariskiGmIso : zariskiSheaf (Gm S) ≅ S.unitsPresheaf :=
  NatIso.ofComponents (fun U ↦ MulEquiv.toGrpIso
      (Units.mapEquiv U.unop.topIso.commRingCatIsoToRingEquiv.toMulEquiv))
    fun {U V} f ↦ by
      ext x
      apply Units.ext
      change V.unop.topIso.hom ((S.homOfLE (leOfHom f.unop)).appTop x.1) =
        S.presheaf.map f (U.unop.topIso.hom x.1)
      exact ConcreteCategory.congr_hom (homOfLE_appTop_topIso (leOfHom f.unop))
        (show Γ(U.unop.toScheme, ⊤) from x.1)

lemma zariskiSheaf_Gm_isCommutative : PresheafOfGroups.IsCommutative (zariskiSheaf (Gm S)) :=
  fun _ a b ↦ Gm_isCommutative S _ a b

lemma isSheaf_zariskiSheaf_Gm :
    Presieve.IsSheaf (Opens.grothendieckTopology S)
      (zariskiSheaf (Gm S) ⋙ CategoryTheory.forget GrpCat) :=
  isSheaf_zariskiSheaf (isSheaf_Gm S)

noncomputable instance : CommGroup (H1 (Opens.grothendieckTopology S) (zariskiSheaf (Gm S))) :=
  H1.commGroup zariskiSheaf_Gm_isCommutative isSheaf_zariskiSheaf_Gm

variable (S) in
/-- XI.5.3: `H¹(S_Zar, 𝒪_S(𝔾_m)) ≅ Pic(S)`, induced by `𝒪_S(𝔾_m) ≅ 𝒪_S^×`. -/
noncomputable def zariskiH1GmMulEquivPic :
    H1 (Opens.grothendieckTopology S) (zariskiSheaf (Gm S)) ≃* S.Pic where
  toFun := H1.map (zariskiGmIso S).hom S.isSheaf_unitsPresheaf
  invFun := H1.map (zariskiGmIso S).inv isSheaf_zariskiSheaf_Gm
  left_inv c := by
    rw [H1.map_map, Iso.hom_inv_id, H1.map_id]
  right_inv c := by
    rw [H1.map_map, Iso.inv_hom_id, H1.map_id]
  map_mul' := H1.map_mul isSheaf_zariskiSheaf_Gm S.isSheaf_unitsPresheaf
    zariskiSheaf_Gm_isCommutative S.isCommutative_unitsPresheaf _

end Units

section Mul

variable {G : (Over S)ᵒᵖ ⥤ GrpCat.{u}} (hc : PresheafOfGroups.IsCommutative G)
  (hG : Presieve.IsSheaf (fpqc S) (G ⋙ CategoryTheory.forget GrpCat))

include hc in
lemma zariskiSheaf_isCommutative : PresheafOfGroups.IsCommutative (zariskiSheaf G) :=
  fun _ a b ↦ hc _ a b

include hc in
/-- The contracted product of locally trivial torsors is locally trivial. -/
lemma isLocallyTrivial_mul {Q Q' : Torsor (fpqc S) G} (hQ : IsLocallyTrivial Q)
    (hQ' : IsLocallyTrivial Q') : IsLocallyTrivial (Torsor.mul hc hG Q Q') := fun x ↦ by
  obtain ⟨U, hxU, ⟨s⟩⟩ := hQ x
  obtain ⟨U', hxU', ⟨s'⟩⟩ := hQ' x
  refine ⟨U ⊓ U', ⟨hxU, hxU'⟩, ⟨(Torsor.toChangeGroup _ hG (Q.prod Q')).hom.app _
    (show Q.obj.obj _ × Q'.obj.obj _ from
      (Q.obj.map ((opensToOver S).map (homOfLE inf_le_left)).op s,
        Q'.obj.map ((opensToOver S).map (homOfLE inf_le_right)).op s'))⟩⟩

/-- XI.4.7: restriction to the Zariski site commutes with the contracted product. -/
theorem zariskiRestrict_mul {Q Q' : Torsor (fpqc S) G} (hQ : IsLocallyTrivial Q)
    (hQ' : IsLocallyTrivial Q') :
    (zariskiRestrict (Torsor.mul hc hG Q Q') (isLocallyTrivial_mul hc hG hQ hQ')).class =
      H1.mul (zariskiSheaf_isCommutative hc) (isSheaf_zariskiSheaf hG)
        (zariskiRestrict Q hQ).class (zariskiRestrict Q' hQ').class := by
  rw [H1.mul_class_eq_map, eq_comm, H1.map_class_eq_class_iff]
  exact ⟨{ hom := Functor.whiskerLeft (opensToOver S).op
              (Torsor.toChangeGroup (PresheafOfGroups.mulHom hc) hG (Q.prod Q')).hom
           map_smul U g x :=
            (Torsor.toChangeGroup (PresheafOfGroups.mulHom hc) hG (Q.prod Q')).map_smul _ g x }⟩

end Mul

section Hilbert90

variable (S) in
/-- XI.5.3 for `𝔾_m`: `H¹(S, 𝔾_{m,S}) ≅ Pic(S) = H¹(S_Zar, 𝒪_S^×)`, induced by the restriction
of torsors to the Zariski site (every torsor is locally trivial by XI.5.1,
`isLocallyTrivial_Gm`). -/
noncomputable def h1GmMulEquivPic : H1 (fpqc S) (Gm S) ≃* S.Pic :=
  MulEquiv.mk' ((Equiv.subtypeUnivEquiv (isLocallyTrivialClass_of_forall
      isLocallyTrivial_Gm)).symm.trans
      ((locallyTrivialH1Equiv (isSheaf_Gm S)).trans (zariskiH1GmMulEquivPic S).toEquiv))
    (by
      intro a b
      obtain ⟨Q, rfl⟩ := H1.mk_surjective a
      obtain ⟨Q', rfl⟩ := H1.mk_surjective b
      change zariskiH1GmMulEquivPic S (locallyTrivialToZariski (Gm S) ⟨_, _⟩) =
        zariskiH1GmMulEquivPic S (locallyTrivialToZariski (Gm S) ⟨_, _⟩) *
          zariskiH1GmMulEquivPic S (locallyTrivialToZariski (Gm S) ⟨_, _⟩)
      rw [← map_mul]
      congr 1
      have e : Q.class * Q'.class = (Torsor.mul (Gm_isCommutative S) (isSheaf_Gm S) Q Q').class :=
        rfl
      simp only [e]
      rw [locallyTrivialToZariski_class _ (isLocallyTrivial_mul (Gm_isCommutative S)
          (isSheaf_Gm S) (isLocallyTrivial_Gm Q) (isLocallyTrivial_Gm Q')),
        locallyTrivialToZariski_class _ (isLocallyTrivial_Gm Q),
        locallyTrivialToZariski_class _ (isLocallyTrivial_Gm Q'), zariskiRestrict_mul]
      rfl)

end Hilbert90

section Local

/-- XI.6.5 (Zariski side): if `S` has a point whose only open neighbourhood is `S` itself (for
instance `S` the spectrum of a local ring), every torsor under `𝒪_S^×` is trivial: `Pic(S) = 0`. -/
theorem Pic_subsingleton_of_forall_mem (x : S) (hx : ∀ U : S.Opens, x ∈ U → U = ⊤) :
    Subsingleton S.Pic := by
  refine ⟨fun a b ↦ ?_⟩
  suffices h : ∀ c : S.Pic, c = 1 by rw [h a, h b]
  intro c
  obtain ⟨P, rfl⟩ := H1.mk_surjective c
  obtain ⟨U, hxU, ⟨s⟩⟩ := exists_section_zariski P x
  obtain rfl := hx U hxU
  exact (Torsor.class_eq_trivialClass_iff_of_isTerminal
    Limits.isTerminalTop S.isSheaf_unitsPresheaf P).2 ⟨s⟩

/-- The spectrum of a local ring: the only open neighbourhood of the closed point is the whole
spectrum. -/
theorem eq_top_of_closedPoint_mem (R : CommRingCat.{u}) [IsLocalRing R] (U : (Spec R).Opens)
    (hU : IsLocalRing.closedPoint R ∈ U) : U = ⊤ := by
  refine eq_top_iff.2 fun p _ ↦ ?_
  have hp : (p : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal p.2.ne_top)
  exact hp.mem_open U.2 hU

/-- XI.6.5 (Zariski side): the Picard group of the spectrum of a local ring is trivial. -/
theorem Pic_subsingleton_of_isLocalRing (R : CommRingCat.{u}) [IsLocalRing R] :
    Subsingleton (Spec R).Pic :=
  Pic_subsingleton_of_forall_mem (IsLocalRing.closedPoint R) (eq_top_of_closedPoint_mem R)

end Local

section Kummer

/-- An isomorphism of commutative groups induces an isomorphism of their `n`-torsion
subgroups. -/
def torsionMulEquiv {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) (n : ℕ) :
    (powMonoidHom n : A →* A).ker ≃* (powMonoidHom n : B →* B).ker where
  toFun x := ⟨e x, by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    exact (congr_arg e x.2).trans (map_one e)⟩
  invFun y := ⟨e.symm y, by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
    exact (congr_arg e.symm y.2).trans (map_one e.symm)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : A) y)

variable (n : ℕ) [NeZero n]

variable (S) in
/-- XI.6.4: the map `H¹(S, μ_n) → ₙPic(S)`. -/
noncomputable def kummerRightPic :
    H1 (fpqc S) (Mu S n) →* (powMonoidHom n : S.Pic →* S.Pic).ker :=
  (torsionMulEquiv (h1GmMulEquivPic S) n).toMonoidHom.comp (kummerRight S n)

/-- XI.6.4, in SGA's form: the exact sequence
`0 → Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ → H¹(S, μ_n) → ₙPic(S) → 0`. -/
theorem kummer_exact_pic :
    Function.Injective (kummerLeft S n) ∧
      (kummerRightPic S n).ker = (kummerLeft S n).range ∧
      Function.Surjective (kummerRightPic S n) := by
  obtain ⟨h₁, h₂, h₃⟩ := kummer_exact S n
  refine ⟨h₁, ?_, (torsionMulEquiv (h1GmMulEquivPic S) n).surjective.comp h₃⟩
  rw [← h₂]
  ext x
  simp only [MonoidHom.mem_ker, kummerRightPic, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

/-- XI.6.5: if `ₙPic(S) = 0`, then
`H¹(S, μ_n) ≅ Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ`. -/
theorem kummerLeft_bijective_of_pic (h : ∀ x : S.Pic, x ^ n = 1 → x = 1) :
    Function.Bijective (kummerLeft S n) := by
  refine kummerLeft_bijective S n fun x hx ↦ ?_
  have := h (h1GmMulEquivPic S x) (by rw [← map_pow, hx, map_one])
  exact (MulEquiv.map_eq_one_iff _).1 this

/-- XI.6.5, example of a local base: if `S` has a point whose only
open neighbourhood is `S` (e.g. `S` is the spectrum of a local ring), then
`H¹(S, μ_n) ≅ Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ`. -/
theorem kummerLeft_bijective_of_forall_mem (x : S) (hx : ∀ U : S.Opens, x ∈ U → U = ⊤) :
    Function.Bijective (kummerLeft S n) :=
  have := Pic_subsingleton_of_forall_mem x hx
  kummerLeft_bijective_of_pic n fun _ _ ↦ Subsingleton.elim _ _

/-- XI.6.6: if every element of `Γ(S, 𝒪_S)` is an `n`-th power,
then `H¹(S, μ_n) ≅ ₙPic(S)`. -/
theorem kummerRightPic_bijective (h : ∀ a : Γ(S, ⊤), ∃ b, b ^ n = a) :
    Function.Bijective (kummerRightPic S n) :=
  (torsionMulEquiv (h1GmMulEquivPic S) n).bijective.comp (kummerRight_bijective S n h)

end Kummer

end SGA.SGA1.ExposeXI
