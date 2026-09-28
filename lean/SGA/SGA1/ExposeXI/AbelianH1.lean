/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import SGA.Foundations.Etale.NonabelianExact
import SGA.Foundations.Etale.TorsorProduct

/-!
# Functoriality of `H¹` of commutative sheaves of groups

This file collects the facts about `H¹` of commutative sheaves of groups used in XI.4.4, XI.4.5
and §6 of SGA 1, Exposé XI, on top of `SGA.Foundations.Etale`:

* the map `H¹(G) → H¹(H)` induced by a morphism of commutative sheaves of groups is a group
  homomorphism (`CategoryTheory.H1.mapHom`), and `H¹` turns pointwise products of morphisms into
  products (`CategoryTheory.H1.map_homMul`); in particular the `n`-th power morphism induces the
  `n`-th power on `H¹` (`CategoryTheory.H1.map_powHom`), and `φ⁻¹` induces the inverse of the map
  induced by `φ` (`CategoryTheory.H1.map_homInv`);
* for a short exact sequence of commutative sheaves of groups the coboundary
  `G''(X) → H¹(X, G')` is a group homomorphism (`IsShortExact.connectingHom`);
* the kernel of a locally surjective morphism of sheaves of groups gives a short exact sequence
  (`PresheafOfGroups.kernel`, `PresheafOfGroups.isShortExact_kernel`).

These are general facts about torsors, stated as they would be in `SGA.Foundations.Etale`.

## References

* [J. Giraud, *Cohomologie non abélienne*, III 3.4][giraud1971]
-/

universe w v u

open CategoryTheory Opposite Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace PresheafOfGroups

variable {G H K : Cᵒᵖ ⥤ GrpCat.{w}}

/-- The morphism `g ↦ (φ g, ψ g)` to a product of presheaves of groups. -/
@[simps]
def prodLift (φ : G ⟶ H) (ψ : G ⟶ K) : G ⟶ prod H K where
  app U := GrpCat.ofHom ((φ.app U).hom.prod (ψ.app U).hom)
  naturality U V f := by
    ext x
    exact _root_.Prod.ext (NatTrans.naturality_apply φ f x) (NatTrans.naturality_apply ψ f x)

/-- The pointwise product `g ↦ φ g * ψ g` of two morphisms to a commutative presheaf of
groups. -/
def homMul (hc : IsCommutative H) (φ ψ : G ⟶ H) : G ⟶ H :=
  prodLift φ ψ ≫ mulHom hc

@[simp]
lemma homMul_app_apply (hc : IsCommutative H) (φ ψ : G ⟶ H) (U : Cᵒᵖ) (g : G.obj U) :
    (homMul hc φ ψ).app U g = φ.app U g * ψ.app U g :=
  rfl

/-- The pointwise inverse `g ↦ (φ g)⁻¹` of a morphism to a commutative presheaf of groups. -/
def homInv (hc : IsCommutative H) (φ : G ⟶ H) : G ⟶ H :=
  φ ≫ invHom hc

@[simp]
lemma homInv_app_apply (hc : IsCommutative H) (φ : G ⟶ H) (U : Cᵒᵖ) (g : G.obj U) :
    (homInv hc φ).app U g = (φ.app U g)⁻¹ :=
  rfl

/-- The `n`-th power morphism `g ↦ gⁿ` of a commutative presheaf of groups. -/
def powHom (hc : IsCommutative G) (n : ℕ) : G ⟶ G where
  app U := GrpCat.ofHom
    { toFun g := g ^ n
      map_one' := one_pow n
      map_mul' a b := (Commute.mul_pow (hc U a b) n) }
  naturality U V f := by
    ext g
    exact (map_pow (G.map f).hom g n).symm

@[simp]
lemma powHom_app_apply (hc : IsCommutative G) (n : ℕ) (U : Cᵒᵖ) (g : G.obj U) :
    (powHom hc n).app U g = g ^ n :=
  rfl

lemma powHom_zero (hc : IsCommutative G) : powHom hc 0 = homMul hc (𝟙 G) (homInv hc (𝟙 G)) := by
  ext U g
  change g ^ 0 = g * g⁻¹
  rw [pow_zero, mul_inv_cancel]

lemma powHom_succ (hc : IsCommutative G) (n : ℕ) :
    powHom hc (n + 1) = homMul hc (powHom hc n) (𝟙 G) := by
  ext U g
  exact pow_succ g n

/-- A morphism of presheaves of groups commutes with the multiplications of commutative
presheaves of groups. -/
lemma mulHom_comp (hcG : IsCommutative G) (hcH : IsCommutative H) (φ : G ⟶ H) :
    mulHom hcG ≫ φ = prodMap φ φ ≫ mulHom hcH := by
  ext U x
  exact map_mul (φ.app U).hom x.1 x.2

end PresheafOfGroups

namespace Torsor

open PresheafOfGroups

variable {G H K : Cᵒᵖ ⥤ GrpCat.{w}}

/-- The equivariant morphism `x ↦ (a x, b x)` to a product of torsors. -/
def HomOver.prodLift {φ : G ⟶ H} {ψ : G ⟶ K} {P : Torsor J G} {Q : Torsor J H}
    {R : Torsor J K} (a : HomOver φ P Q) (b : HomOver ψ P R) :
    HomOver (PresheafOfGroups.prodLift φ ψ) P (Q.prod R) where
  hom :=
    { app U := ↾fun x ↦ ((a.hom.app U x, b.hom.app U x) : Q.obj.obj U × R.obj.obj U)
      naturality U V f := by
        ext x
        change ((a.hom.app V (P.obj.map f x), b.hom.app V (P.obj.map f x)) :
            Q.obj.obj V × R.obj.obj V) = (Q.obj.map f (a.hom.app U x), R.obj.map f (b.hom.app U x))
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply] }
  map_smul U g x := _root_.Prod.ext (a.map_smul U g x) (b.map_smul U g x)

end Torsor

namespace H1

open PresheafOfGroups

variable {G H : Cᵒᵖ ⥤ GrpCat.{w}}
  (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))

/-- The product of two classes is the class induced from the product torsor along the
multiplication. -/
lemma mul_class_eq_map (hc : IsCommutative G) (P Q : Torsor J G) :
    mul hc hG P.class Q.class = map (mulHom hc) hG (P.prod Q).class :=
  rfl

/-- `H¹` turns the pointwise product of two morphisms into the product of the induced maps. -/
theorem map_homMul (hcH : IsCommutative H) (φ ψ : G ⟶ H) (c : H1 J G) :
    map (homMul hcH φ ψ) hH c = mul hcH hH (map φ hH c) (map ψ hH c) := by
  obtain ⟨P, rfl⟩ := mk_surjective c
  simp only [map_class, mul_class]
  rw [← map_class, map_class_eq_class_iff]
  exact ⟨(Torsor.HomOver.prodLift (Torsor.toChangeGroup φ hH P)
    (Torsor.toChangeGroup ψ hH P)).comp (Torsor.toChangeGroup (mulHom hcH) hH _)⟩

/-- A morphism of commutative sheaves of groups induces a multiplicative map on `H¹`. -/
theorem map_mul (hcG : IsCommutative G) (hcH : IsCommutative H) (φ : G ⟶ H) (a b : H1 J G) :
    map φ hH (mul hcG hG a b) = mul hcH hH (map φ hH a) (map φ hH b) := by
  obtain ⟨P, rfl⟩ := mk_surjective a
  obtain ⟨Q, rfl⟩ := mk_surjective b
  rw [mul_class_eq_map, map_map, mulHom_comp hcG hcH]
  simp only [map_class, mul_class]
  rw [← map_class, map_class_eq_class_iff]
  exact ⟨(Torsor.HomOver.prodMap (Torsor.toChangeGroup φ hH P)
    (Torsor.toChangeGroup φ hH Q)).comp (Torsor.toChangeGroup (mulHom hcH) hH _)⟩

/-- The map `H¹(G) → H¹(H)` induced by a morphism of commutative sheaves of groups, as a group
homomorphism. -/
noncomputable def mapHom (hcG : IsCommutative G) (hcH : IsCommutative H) (φ : G ⟶ H) :
    letI := commGroup hcG hG
    letI := commGroup hcH hH
    H1 J G →* H1 J H :=
  letI := commGroup hcG hG
  letI := commGroup hcH hH
  { toFun := map φ hH
    map_one' := map_trivialClass φ hH hG
    map_mul' := map_mul hG hH hcG hcH φ }

lemma mapHom_apply (hcG : IsCommutative G) (hcH : IsCommutative H) (φ : G ⟶ H) (c : H1 J G) :
    mapHom hG hH hcG hcH φ c = map φ hH c :=
  rfl

/-- `H¹` turns the pointwise inverse of a morphism into the inverse of the induced map. -/
theorem map_homInv (hcH : IsCommutative H) (φ : G ⟶ H) (c : H1 J G) :
    letI := commGroup hcH hH
    map (homInv hcH φ) hH c = (map φ hH c)⁻¹ :=
  (map_map φ hH (invHom hcH) hH c).symm

/-- The `n`-th power morphism of a commutative sheaf of groups induces the `n`-th power on
`H¹`. -/
theorem map_powHom (hc : IsCommutative G) (n : ℕ) (c : H1 J G) :
    letI := commGroup hc hG
    map (powHom hc n) hG c = c ^ n := by
  let _ := commGroup hc hG
  induction n with
  | zero =>
    rw [powHom_zero, map_homMul, map_homInv, map_id, pow_zero]
    exact mul_inv_cancel c
  | succ n ih =>
    rw [powHom_succ, map_homMul, ih, map_id, pow_succ]
    rfl

end H1

namespace PresheafOfGroups.IsShortExact

variable {G' G G'' : Cᵒᵖ ⥤ GrpCat.{w}} {i : G' ⟶ G} {p : G ⟶ G''}
  (h : IsShortExact J i p)
  (hG' : Presieve.IsSheaf J (G' ⋙ CategoryTheory.forget GrpCat))
  (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  (hG'' : Presieve.IsSheaf J (G'' ⋙ CategoryTheory.forget GrpCat))
  {X : C} (hX : IsTerminal X)

/-- The product of sections of the fibres `p⁻¹(c)` and `p⁻¹(c')`, a section of `p⁻¹(c c')`.
It is equivariant for the multiplication `G' × G' ⟶ G'` when `G` is commutative. -/
def fiberMulHomOver (hc' : IsCommutative G') (hc : IsCommutative G) (c c' : G''.obj (op X)) :
    Torsor.HomOver (mulHom hc') ((h.fiberTorsor hG hG'' hX c).prod (h.fiberTorsor hG hG'' hX c'))
      (h.fiberTorsor hG hG'' hX (c * c')) where
  hom :=
    { app U := ↾fun x ↦ ⟨(fiberVal x.1 * fiberVal x.2 : G.obj U), by
        change p.app U (_ * _) = _
        rw [map_mul, p_app_fiberVal, p_app_fiberVal, map_mul]⟩
      naturality U V f := by
        ext x
        apply Subtype.ext
        change G.map f (fiberVal x.1) * G.map f (fiberVal x.2) =
          G.map f (fiberVal x.1 * fiberVal x.2)
        rw [map_mul] }
  map_smul U g x := Subtype.ext (by
    change (i.app U g.1 * fiberVal x.1) * (i.app U g.2 * fiberVal x.2) =
      i.app U (g.1 * g.2) * (fiberVal x.1 * fiberVal x.2)
    rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fiberVal x.1), hc U (fiberVal x.1),
      mul_assoc])

/-- The coboundary of a product is the product of the coboundaries, for commutative `G'` and
`G`. -/
theorem connecting_mul (hc' : IsCommutative G') (hc : IsCommutative G) (c c' : G''.obj (op X)) :
    h.connecting hG hG'' hX (c * c') =
      H1.mul hc' hG' (h.connecting hG hG'' hX c) (h.connecting hG hG'' hX c') := by
  rw [connecting, connecting, connecting, H1.mul_class, Torsor.class_eq_class_iff]
  exact ⟨(Torsor.changeGroupIsoOfHomOver hG' (h.fiberMulHomOver hG hG'' hX hc' hc c c')).symm⟩

/-- The coboundary `G''(X) → H¹(X, G')` of a short exact sequence of commutative sheaves of
groups, as a group homomorphism. -/
noncomputable def connectingHom (hc' : IsCommutative G') (hc : IsCommutative G) :
    letI := H1.commGroup hc' hG'
    G''.obj (op X) →* H1 J G' :=
  letI := H1.commGroup hc' hG'
  { toFun := h.connecting hG hG'' hX
    map_one' := (h.connecting_eq_trivialClass_iff hG' hG hG'' hX 1).2 ⟨1, map_one _⟩
    map_mul' := h.connecting_mul hG' hG hG'' hX hc' hc }

lemma connectingHom_apply (hc' : IsCommutative G') (hc : IsCommutative G)
    (c : G''.obj (op X)) :
    h.connectingHom hG' hG hG'' hX hc' hc c = h.connecting hG hG'' hX c :=
  rfl

end PresheafOfGroups.IsShortExact

namespace PresheafOfGroups

variable {G G'' : Cᵒᵖ ⥤ GrpCat.{w}} (p : G ⟶ G'')

/-- The kernel of a morphism of presheaves of groups. -/
def kernel : Cᵒᵖ ⥤ GrpCat.{w} where
  obj U := GrpCat.of (p.app U).hom.ker
  map {U V} f := GrpCat.ofHom (((G.map f).hom.comp (p.app U).hom.ker.subtype).codRestrict _
    fun x ↦ by
      change p.app V (G.map f x.1) = 1
      rw [NatTrans.naturality_apply p, MonoidHom.mem_ker.mp x.2, map_one])
  map_id U := by
    ext x
    change G.map (𝟙 U) x.1 = x.1
    rw [G.map_id]
    rfl
  map_comp f g := by
    ext x
    change G.map (f ≫ g) x.1 = G.map g (G.map f x.1)
    rw [G.map_comp]
    rfl

lemma kernel_map_val {U V : Cᵒᵖ} (f : U ⟶ V) (x : (kernel p).obj U) :
    ((kernel p).map f x : (p.app V).hom.ker).1 = G.map f (x : (p.app U).hom.ker).1 :=
  rfl

/-- The inclusion of the kernel. -/
def kernelι : kernel p ⟶ G where
  app U := GrpCat.ofHom (p.app U).hom.ker.subtype

lemma kernelι_app_apply {U : Cᵒᵖ} (x : (kernel p).obj U) :
    (kernelι p).app U x = (x : (p.app U).hom.ker).1 :=
  rfl

lemma kernelι_app_injective (U : Cᵒᵖ) : Function.Injective ((kernelι p).app U).hom :=
  Subtype.val_injective

variable {p}

/-- The kernel of a morphism from a sheaf of groups to a separated presheaf of groups is a
sheaf. -/
lemma isSheaf_kernel (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    (hG'' : Presieve.IsSeparated J (G'' ⋙ CategoryTheory.forget GrpCat)) :
    Presieve.IsSheaf J (kernel p ⋙ CategoryTheory.forget GrpCat) := by
  intro U R hR x hx
  let y : Presieve.FamilyOfElements (G ⋙ CategoryTheory.forget GrpCat) R :=
    fun V f hf ↦ (show (p.app (op V)).hom.ker from x f hf).1
  have hy : y.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun z : (p.app (op Z)).hom.ker ↦ z.1) (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨t, ht, ht'⟩ := hG R hR y hy
  have hpt : p.app (op U) t = 1 := by
    refine (hG'' R hR).ext fun V f hf ↦ ?_
    change G''.map f.op (p.app (op U) t) = G''.map f.op 1
    rw [← NatTrans.naturality_apply p, map_one]
    have := ht f hf
    change G.map f.op t = _ at this
    rw [this]
    exact (show (p.app (op V)).hom.ker from x f hf).2
  refine ⟨(⟨t, hpt⟩ : (p.app (op U)).hom.ker), fun V f hf ↦ ?_, fun s hs ↦ ?_⟩
  · exact Subtype.ext (ht f hf)
  · refine Subtype.ext (ht' (show (p.app (op U)).hom.ker from s).1 fun V f hf ↦ ?_)
    exact congr_arg (fun z : (p.app (op V)).hom.ker ↦ z.1) (hs f hf)

/-- The kernel of a locally surjective morphism `p` of presheaves of groups gives a short exact
sequence `1 → ker p → G → G'' → 1`. -/
lemma isShortExact_kernel
    (hp : ∀ (U : C) (c : G''.obj (op U)), ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      ∃ g : G.obj (op V), p.app (op V) g = G''.map f.op c) :
    IsShortExact J (kernelι p) p where
  injective := kernelι_app_injective p
  exact U g := ⟨fun hg ↦ ⟨(⟨g, hg⟩ : (p.app U).hom.ker), rfl⟩,
    fun ⟨g', hg'⟩ ↦ hg' ▸ (show (p.app U).hom.ker from g').2⟩
  locallySurjective := hp

end PresheafOfGroups

end CategoryTheory
