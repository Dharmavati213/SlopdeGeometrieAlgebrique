/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import SGA.Foundations.Formal.FormalColimit

/-!
# The formal spectrum of an adic ring

Let `A` be a ring and `I` an ideal. The *formal spectrum* `Spf A` (EGA I, §10.1) is the colimit of
the thickening sequence `Spec (A ⧸ I) ⟶ Spec (A ⧸ I²) ⟶ ⋯` in locally ringed spaces
(EGA I, §10.6). Its underlying space is `Spec (A ⧸ I)` and its structure sheaf is
`lim← 𝒪_{Spec (A ⧸ Iⁿ⁺¹)}`. If `A` is `I`-adically complete, `Γ(Spf A, 𝒪) = A`
(EGA I, §10.1).

We work with locally ringed spaces and do not record the topology on the rings of sections:
for noetherian adic rings it is the `I`-adic topology, determined by `I`.

## Main definitions and results

* `AlgebraicGeometry.Spf.ringDiagram A I`: the inverse system `n ↦ A ⧸ I ^ (n + 1)`.
* `AlgebraicGeometry.Spf.diagram A I`: the thickening sequence `n ↦ Spec (A ⧸ I ^ (n + 1))`.
* `AlgebraicGeometry.Spf A I`: the formal spectrum.
* `AlgebraicGeometry.Spf.homeomorph`: the underlying space of `Spf A I` is `Spec (A ⧸ I)`.
* `AlgebraicGeometry.Spf.ΓIso`: `Γ(Spf A I) ≅ A` for `A` complete.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] (I : Ideal A)

namespace Spf

/-- The inverse system of rings `A ⧸ I ⟵ A ⧸ I² ⟵ A ⧸ I³ ⟵ ⋯`. -/
noncomputable abbrev ringDiagram : ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj n := .of (A ⧸ I ^ (unop n + 1))
  map {m n} f := CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f.unop)))
  map_id n := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

/-- The thickening sequence `Spec (A ⧸ I) ⟶ Spec (A ⧸ I²) ⟶ ⋯`, i.e. `Spec` of
`ringDiagram`. -/
noncomputable abbrev diagram : ℕ ⥤ Scheme.{u} where
  obj n := Spec (.of (A ⧸ I ^ (n + 1)))
  map {m n} f := Spec.map ((ringDiagram A I).map f.op)
  map_id n := by rw [← Spec.map_id]; congr 1; exact (ringDiagram A I).map_id _
  map_comp f g := by rw [← Spec.map_comp, ← Functor.map_comp]

/-- The kernel of `A ⧸ I ^ (n + 2) → A ⧸ I ^ (n + 1)` is nilpotent. -/
lemma ker_factorPow_le_nilradical (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))) ≤
      nilradical (A ⧸ I ^ (n + 1 + 1)) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.pow_le_pow_right (by lia : n + 1 + 1 ≤ (n + 1) * 2) ?_
  rw [pow_mul]
  exact Ideal.pow_mem_pow hx 2

instance : Scheme.IsThickeningSequence (diagram A I) where
  isClosedImmersion n :=
    IsClosedImmersion.spec_of_surjective _ fun x ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  surjective n := by
    constructor
    have := PrimeSpectrum.isHomeomorph_comap
      (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))
      (fun x ↦ ⟨1, one_pos, by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.factor_surjective
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x
        exact ⟨y, (pow_one _).symm⟩⟩)
      (ker_factorPow_le_nilradical A I n)
    exact this.surjective

end Spf

/-- The formal spectrum `Spf A` of `A` with respect to the ideal `I` (EGA I, §10.1), as the
colimit `lim→ Spec (A ⧸ I ^ (n + 1))` in locally ringed spaces (EGA I, §10.6). For `A` noetherian
and `I`-adically complete this is an affine noetherian formal scheme. -/
noncomputable abbrev Spf : LocallyRingedSpace.{u} :=
  Scheme.formalColimit (Spf.diagram A I)

namespace Spf

/-- The closed immersion `Spec (A ⧸ I ^ (n + 1)) ⟶ Spf A`. -/
noncomputable def ι (n : ℕ) : ((diagram A I).obj n).toLocallyRingedSpace ⟶ Spf A I :=
  Scheme.formalColimit.ι (diagram A I) n

@[reassoc (attr := simp)]
lemma w {m n : ℕ} (f : m ⟶ n) : ((diagram A I).map f).toLRSHom ≫ ι A I n = ι A I m :=
  Scheme.formalColimit.w _ f

variable {A I} in
@[ext]
lemma hom_ext {Y : LocallyRingedSpace.{u}} {g g' : Spf A I ⟶ Y}
    (h : ∀ n, ι A I n ≫ g = ι A I n ≫ g') : g = g' :=
  Scheme.formalColimit.hom_ext _ h

/-- The underlying space of `Spf A` is that of `Spec (A ⧸ I)` (EGA I, §10.1). -/
noncomputable def homeomorph : Spec (.of (A ⧸ I ^ (0 + 1))) ≃ₜ Spf A I :=
  Scheme.formalColimit.homeomorph (diagram A I) 0

/-- The cone `A ⟶ A ⧸ I ^ (n + 1)` over the inverse system `ringDiagram`. -/
@[simps]
noncomputable def adicCone : Cone (ringDiagram A I) where
  pt := .of A
  π :=
    { app n := CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (unop n + 1)))
      naturality {m n} f := by
        ext a
        rfl }

lemma strictMono_succ : StrictMono (fun n : ℕ ↦ n + 1) := strictMono_id.add_const 1

/-- The components `s.pt ⟶ A ⧸ I ^ (n + 1)` of a cone over `ringDiagram`. -/
noncomputable def coneComponent (s : Cone (ringDiagram A I)) (n : ℕ) :
    s.pt →+* A ⧸ I ^ (n + 1) :=
  (s.π.app (op n)).hom

lemma coneComponent_compatible (s : Cone (ringDiagram A I)) {m : ℕ} :
    (Ideal.Quotient.factorPow I (strictMono_succ.monotone m.le_succ)).comp
      (coneComponent A I s (m + 1)) = coneComponent A I s m := by
  have := s.w (homOfLE m.le_succ).op
  ext x
  exact congr($(this).hom x)

/-- The map from the vertex of a cone to `A`, for `A` complete. -/
noncomputable def adicLift [IsAdicComplete I A] (s : Cone (ringDiagram A I)) : s.pt ⟶ .of A :=
  CommRingCat.ofHom (IsAdicComplete.StrictMono.liftRingHom I strictMono_succ
    (coneComponent A I s) (coneComponent_compatible A I s))

lemma mk_adicLift [IsAdicComplete I A] (s : Cone (ringDiagram A I)) (n : ℕ) (x : s.pt) :
    Ideal.Quotient.mk (I ^ (n + 1)) ((adicLift A I s).hom x) = coneComponent A I s n x :=
  IsAdicComplete.StrictMono.mk_liftRingHom I strictMono_succ _
    (coneComponent_compatible A I s) x

lemma adicLift_fac [IsAdicComplete I A] (s : Cone (ringDiagram A I)) (n : ℕᵒᵖ) :
    adicLift A I s ≫ (adicCone A I).π.app n = s.π.app n := by
  ext x
  exact mk_adicLift A I s (unop n) x

lemma adicLift_uniq [IsAdicComplete I A] (s : Cone (ringDiagram A I)) (g : s.pt ⟶ .of A)
    (hg : ∀ n, g ≫ (adicCone A I).π.app n = s.π.app n) : g = adicLift A I s := by
  have := IsAdicComplete.StrictMono.eq_liftRingHom I strictMono_succ _
    (coneComponent_compatible A I s) (F := g.hom) fun n ↦ by
      ext y
      exact congr($(hg (op n)).hom y)
  ext x
  exact congr($this x)

/-- `A` is the limit of the `A ⧸ I ^ (n + 1)` when it is `I`-adically complete. -/
noncomputable def isLimitAdicCone [IsAdicComplete I A] : IsLimit (adicCone A I) where
  lift := adicLift A I
  fac := adicLift_fac A I
  uniq := adicLift_uniq A I

/-- `Γ(Spec (A ⧸ Iⁿ⁺¹)) ≅ A ⧸ Iⁿ⁺¹`, naturally in `n`. -/
noncomputable def diagramΓIso : (diagram A I).op ⋙ Scheme.Γ ≅ ringDiagram A I :=
  NatIso.ofComponents (fun _ ↦ Scheme.ΓSpecIso _) fun _ ↦ Scheme.ΓSpecIso_naturality _

/-- `Γ(Spf A, 𝒪) = A` for `A` complete (EGA I, §10.1). -/
noncomputable def ΓIso [IsAdicComplete I A] :
    LocallyRingedSpace.Γ.obj (op (Spf A I)) ≅ .of A :=
  IsLimit.conePointUniqueUpToIso (Scheme.formalColimit.isLimitΓcone (diagram A I))
    ((IsLimit.postcomposeHomEquiv (diagramΓIso A I).symm (adicCone A I)).symm
      (isLimitAdicCone A I))

end Spf

end AlgebraicGeometry

namespace AlgebraicGeometry.Spf

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The morphism `Spec C ⟶ Spf A` defined by a ring map `ψ : A → C` which kills `I ^ (n + 1)`:
the composite `Spec C ⟶ Spec (A ⧸ I ^ (n + 1)) ⟶ Spf A`. It does not depend on `n`
(`fromSpec_eq`). -/
noncomputable def fromSpec {C : CommRingCat.{u}} (ψ : A →+* C) (n : ℕ)
    (h : I ^ (n + 1) ≤ RingHom.ker ψ) : (Spec C).toLocallyRingedSpace ⟶ Spf A I :=
  Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ
    fun _ ha ↦ RingHom.mem_ker.mp (h ha))) : Spec C ⟶ (diagram A I).obj n) ≫ ι A I n

lemma ι_eq_fromSpec (n : ℕ) :
    ι A I n = fromSpec (C := .of (A ⧸ I ^ (n + 1))) (Ideal.Quotient.mk _) n
      Ideal.mk_ker.symm.le := by
  have : CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (n + 1)) (Ideal.Quotient.mk (I ^ (n + 1)))
      fun _ ha ↦ RingHom.mem_ker.mp (Ideal.mk_ker.symm.le ha)) = 𝟙 _ := by
    ext x
    rfl
  rw [fromSpec, this, Spec.map_id]
  rfl

lemma Spec_map_fromSpec {C D : CommRingCat.{u}} (g : C ⟶ D) (ψ : A →+* C) (n : ℕ)
    (h : I ^ (n + 1) ≤ RingHom.ker ψ) :
    (Spec.map g).toLRSHom ≫ fromSpec ψ n h =
      fromSpec (g.hom.comp ψ) n (h.trans fun x hx ↦ by simp [RingHom.mem_ker.mp hx]) := by
  rw [fromSpec, fromSpec, ← Category.assoc, ← Scheme.Hom.comp_toLRSHom, ← Spec.map_comp]
  congr 3
  ext x
  rfl

lemma fromSpec_eq {C : CommRingCat.{u}} (ψ : A →+* C) (m n : ℕ)
    (hm : I ^ (m + 1) ≤ RingHom.ker ψ) (hn : I ^ (n + 1) ≤ RingHom.ker ψ) :
    fromSpec ψ m hm = fromSpec ψ n hn := by
  wlog hmn : m ≤ n generalizing m n
  · exact (this n m hn hm (le_of_not_ge hmn)).symm
  rw [fromSpec, fromSpec, ← w A I (homOfLE hmn), ← Category.assoc,
    ← Scheme.Hom.comp_toLRSHom, ← Spec.map_comp]
  congr 4
  ext x
  rfl

lemma ι_comp_fromSpec {C : CommRingCat.{u}} (ψ : A →+* C) (n : ℕ)
    (h : I ^ (n + 1) ≤ RingHom.ker ψ) :
    Scheme.Hom.toLRSHom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ
      fun _ ha ↦ RingHom.mem_ker.mp (h ha))) : Spec C ⟶ (diagram A I).obj n) ≫ ι A I n =
      fromSpec ψ n h := rfl

section Functoriality

variable {B : Type u} [CommRing B] {J : Ideal B}

lemma pow_le_ker_of_pow_le_comap (φ : A →+* B) {k : ℕ} (hk : I ^ k ≤ J.comap φ) (n : ℕ) :
    I ^ (k * (n + 1) + 1) ≤ RingHom.ker ((Ideal.Quotient.mk (J ^ (n + 1))).comp φ) := by
  intro a ha
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  have h₁ : I ^ (k * (n + 1) + 1) ≤ (I ^ k) ^ (n + 1) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (Nat.le_succ _)
  exact Ideal.le_comap_pow φ (n + 1) (Ideal.pow_right_mono hk _ (h₁ ha))

/-- A continuous ring map `φ : A → B` (that is, `φ (I ^ k) ⊆ J` for some `k`) induces a morphism
`Spf B ⟶ Spf A` (EGA I, §10.2). -/
noncomputable def map (φ : A →+* B) (hφ : ∃ k, I ^ k ≤ J.comap φ) : Spf B J ⟶ Spf A I :=
  Scheme.formalColimit.desc (diagram B J)
    (fun n ↦ fromSpec (C := .of (B ⧸ J ^ (n + 1))) ((Ideal.Quotient.mk _).comp φ)
      (hφ.choose * (n + 1)) (pow_le_ker_of_pow_le_comap φ hφ.choose_spec n))
    (fun n ↦ by
      rw [Spec_map_fromSpec]
      exact fromSpec_eq _ _ _ _ _)

lemma ι_map (φ : A →+* B) (hφ : ∃ k, I ^ k ≤ J.comap φ) (n : ℕ) :
    ι B J n ≫ map φ hφ = fromSpec (C := .of (B ⧸ J ^ (n + 1))) ((Ideal.Quotient.mk _).comp φ)
      (hφ.choose * (n + 1)) (pow_le_ker_of_pow_le_comap φ hφ.choose_spec n) :=
  Scheme.formalColimit.ι_desc (diagram B J) _ _ n

lemma fromSpec_map {C : CommRingCat.{u}} (ψ : B →+* C) (n : ℕ) (h : J ^ (n + 1) ≤ RingHom.ker ψ)
    (φ : A →+* B) (hφ : ∃ k, I ^ k ≤ J.comap φ) (m : ℕ)
    (h' : I ^ (m + 1) ≤ RingHom.ker (ψ.comp φ)) :
    fromSpec ψ n h ≫ map φ hφ = fromSpec (ψ.comp φ) m h' := by
  rw [fromSpec, Category.assoc, ι_map, Spec_map_fromSpec]
  exact fromSpec_eq _ _ _ _ _

@[simp]
lemma map_id : map (RingHom.id A) ⟨1, by simp⟩ = 𝟙 (Spf A I) := by
  refine hom_ext fun n ↦ ?_
  rw [ι_map, Category.comp_id, ι_eq_fromSpec]
  exact fromSpec_eq _ _ _ _ _

lemma map_comp {C : Type u} [CommRing C] {K : Ideal C} (φ : A →+* B) (ψ : B →+* C)
    (hφ : ∃ k, I ^ k ≤ J.comap φ) (hψ : ∃ k, J ^ k ≤ K.comap ψ) :
    map ψ hψ ≫ map φ hφ = map (ψ.comp φ) (by
      obtain ⟨k, hk⟩ := hφ
      obtain ⟨l, hl⟩ := hψ
      refine ⟨k * l, ?_⟩
      calc I ^ (k * l) = (I ^ k) ^ l := pow_mul _ _ _
        _ ≤ (J.comap φ) ^ l := Ideal.pow_right_mono hk l
        _ ≤ (J ^ l).comap φ := Ideal.le_comap_pow φ l
        _ ≤ (K.comap ψ).comap φ := Ideal.comap_mono hl
        _ = K.comap (ψ.comp φ) := Ideal.comap_comap _ _) := by
  refine hom_ext fun n ↦ ?_
  rw [← Category.assoc, ι_map, ι_map]
  exact fromSpec_map _ _ _ _ _ _ _

/-- `Spf A` only depends on the `I`-adic topology: if `I ^ k ⊆ J` and `J ^ l ⊆ I`, then
`Spf A` computed with `I` and with `J` agree (EGA I, §10.1). -/
noncomputable def isoOfPowLE {J : Ideal A} (hIJ : ∃ k, I ^ k ≤ J) (hJI : ∃ l, J ^ l ≤ I) :
    Spf A I ≅ Spf A J where
  hom := map (RingHom.id A) (by simpa using hJI)
  inv := map (RingHom.id A) (by simpa using hIJ)
  hom_inv_id := by rw [map_comp]; exact map_id
  inv_hom_id := by rw [map_comp]; exact map_id

end Functoriality

end AlgebraicGeometry.Spf

namespace AlgebraicGeometry.Spf

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- `Γ(Spec R) ≅ R`, for the locally ringed space `Spec R`. -/
noncomputable def ΓSpecIsoLRS (R : CommRingCat.{u}) :
    LocallyRingedSpace.Γ.obj (op (Spec R).toLocallyRingedSpace) ≅ R :=
  Scheme.ΓSpecIso R

lemma ΓSpecIsoLRS_inv_naturality {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ (ΓSpecIsoLRS S).inv =
      (ΓSpecIsoLRS R).inv ≫ LocallyRingedSpace.Γ.map (Spec.map f).toLRSHom.op :=
  Scheme.ΓSpecIso_inv_naturality f

/-- Under `Γ(Spf A) ≅ A`, restriction to `Spec (A ⧸ I ^ (n + 1))` is the quotient map. -/
lemma ΓIso_inv_comp_Γ_map_ι [IsAdicComplete I A] (n : ℕ) :
    (ΓIso A I).inv ≫ LocallyRingedSpace.Γ.map (ι A I n).op =
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫ (ΓSpecIsoLRS _).inv :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (op n)

end AlgebraicGeometry.Spf

namespace AlgebraicGeometry.Spf

variable {A : Type u} [CommRing A] {I : Ideal A} {B : Type u} [CommRing B] {J : Ideal B}

lemma Γ_map_fromSpec [IsAdicComplete I A] {C : CommRingCat.{u}} (ψ : A →+* C) (n : ℕ)
    (h : I ^ (n + 1) ≤ RingHom.ker ψ) :
    (ΓIso A I).inv ≫ LocallyRingedSpace.Γ.map (fromSpec ψ n h).op =
      CommRingCat.ofHom ψ ≫ (ΓSpecIsoLRS C).inv := by
  rw [fromSpec, op_comp, Functor.map_comp, ← Category.assoc, ΓIso_inv_comp_Γ_map_ι,
    Category.assoc, ← ΓSpecIsoLRS_inv_naturality, ← Category.assoc, ← CommRingCat.ofHom_comp]
  congr 2

lemma ΓIso_hom_comp_mk [IsAdicComplete I A] (n : ℕ) :
    (ΓIso A I).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) =
      LocallyRingedSpace.Γ.map (ι A I n).op ≫ (ΓSpecIsoLRS _).hom := by
  rw [← cancel_epi (ΓIso A I).inv, Iso.inv_hom_id_assoc, ← Category.assoc,
    ΓIso_inv_comp_Γ_map_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `Γ(Spf.map φ) = φ` under `Γ(Spf A) = A` (EGA I, §10.2): in particular `φ ↦ Spf.map φ` is
injective on continuous maps between complete rings. -/
lemma ΓIso_map [IsAdicComplete I A] [IsAdicComplete J B] (φ : A →+* B)
    (hφ : ∃ k, I ^ k ≤ J.comap φ) :
    (ΓIso A I).inv ≫ LocallyRingedSpace.Γ.map (map φ hφ).op ≫ (ΓIso B J).hom =
      CommRingCat.ofHom φ := by
  refine (isLimitAdicCone B J).hom_ext fun n ↦ ?_
  change _ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (unop n + 1))) =
    _ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (unop n + 1)))
  rw [Category.assoc, Category.assoc, ΓIso_hom_comp_mk,
    ← Category.assoc (LocallyRingedSpace.Γ.map _), ← Functor.map_comp, ← op_comp, ι_map,
    ← Category.assoc, Γ_map_fromSpec, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end AlgebraicGeometry.Spf

namespace AlgebraicGeometry.Spf

variable {A : Type u} [CommRing A] {I : Ideal A} {B : Type u} [CommRing B] {J : Ideal B}

/-- Between complete rings, `φ ↦ Spf.map φ` is injective (EGA I, §10.2). -/
lemma map_injective [IsAdicComplete I A] [IsAdicComplete J B] {φ ψ : A →+* B}
    (hφ : ∃ k, I ^ k ≤ J.comap φ) (hψ : ∃ k, I ^ k ≤ J.comap ψ) (h : map φ hφ = map ψ hψ) :
    φ = ψ := by
  have e₁ := ΓIso_map φ hφ
  have e₂ := ΓIso_map ψ hψ
  rw [h] at e₁
  rw [e₁] at e₂
  exact congrArg CommRingCat.Hom.hom e₂

end AlgebraicGeometry.Spf
