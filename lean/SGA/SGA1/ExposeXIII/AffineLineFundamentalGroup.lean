/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.ArtinSchreier
import SGA.SGA1.ExposeXI.ArtinSchreierScheme
import SGA.SGA1.ExposeXI.FundamentalGroupCohomology
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeXIII.SchemeFundamentalGroup

/-!
# SGA 1, Exposé XIII, Remark 2.13: `π₁(𝔸¹)` is not topologically finitely generated

Remark XIII.2.13 (M. Raynaud, 2003) observes, through Artin–Schreier theory (XI.6.9), that
`Hom_cont(π₁(𝔸¹_k), ℤ/p)` contains the infinite group `k[T]/℘(k[T])`, so that `π₁(𝔸¹_k)` is not
topologically of finite type in characteristic `p > 0`.

For a ring `R` of characteristic `p` with connected spectrum and a geometric point `R → Ω`, the
Artin–Schreier covering `R[T]/(Tᵖ - T + a)` of XI.6.7 (`SGA.SGA1.ExposeXI.ArtinSchreierAlgebra`) is
a principal object with group `ℤ/p` of the Galois category of finite étale `R`-algebras
(`artinSchreierPrincipal`): `ℤ/p` acts simply transitively on its geometric points, the roots of
`Tᵖ - T + a`. Two of them are isomorphic principal objects only if `a - b ∈ ℘(R)`
(`sub_mem_of_isIso_artinSchreierPrincipal`, from XI.6.8–6.9). So the homomorphisms
`π₁ → ℤ/p` attached to them (V.5.11) separate the classes of `R/℘(R)`. For `R = k[T]`, `k` a field
of characteristic `p`, the classes of the polynomials without monomials of degree divisible by `p`
are pairwise distinct (`SGA.SGA1.ExposeXIII.injective_mk_primeToPPolys`) and infinite in number;
hence `π₁(𝔸¹_k)` has infinitely many continuous homomorphisms to `ℤ/p` and is not topologically
finitely generated (`not_isTopologicallyFG_fundamentalGroup_affineLine`). No hypothesis on `k`
beyond its characteristic is needed.

For `k` algebraically closed, XI.6.9 (`SGA.SGA1.ExposeXI.artinSchreierEquivContinuousMonoidHom`)
gives the full description `Hom_cont(π₁(𝔸¹_k, x), ℤ/p) ≃ k[T]/℘(k[T])`
(`affineLineArtinSchreier`).
-/

universe u

namespace SGA.SGA1.ExposeXIII

open CategoryTheory PreGaloisCategory Polynomial AlgebraicGeometry

section Algebra

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]

/-- The Artin–Schreier covering `R[T]/(Tᵖ - T + a)` of XI.6.7, as a finite étale `R`-algebra. -/
noncomputable def artinSchreierFE (a : R) : CommAlgCat.FiniteEtale.{u} R :=
  haveI := ExposeXI.ArtinSchreier.etale hp.out (CharP.cast_eq_zero R p) a
  CommAlgCat.FiniteEtale.of R (ExposeXI.ArtinSchreierAlgebra R p a)

/-- The automorphism `T ↦ T + k` of the Artin–Schreier covering, in the opposite category of
finite étale algebras (the category of étale coverings). -/
noncomputable def artinSchreierAut (a : R) (g : Multiplicative (ZMod p)) :
    Aut (Opposite.op (artinSchreierFE p a)) :=
  (CommAlgCat.FiniteEtale.isoMk (ExposeXI.ArtinSchreier.action p a g)).op

lemma artinSchreierAut_hom_unop_apply (a : R) (g : Multiplicative (ZMod p))
    (y : ExposeXI.ArtinSchreierAlgebra R p a) :
    (artinSchreierAut p a g).hom.unop.hom.hom y = ExposeXI.ArtinSchreier.action p a g y :=
  rfl

/-- The right action of `ℤ/p` on the Artin–Schreier covering, `k` acting by `T ↦ T + k`. -/
noncomputable def artinSchreierAction (a : R) :
    DiscreteZMod.{u} p →* (Aut (Opposite.op (artinSchreierFE p a)))ᵐᵒᵖ where
  toFun g := MulOpposite.op (artinSchreierAut p a (DiscreteZMod.equiv p g))
  map_one' := by
    rw [map_one, MulOpposite.op_eq_one_iff]
    apply Iso.ext
    apply Quiver.Hom.unop_inj
    ext y
    change ExposeXI.ArtinSchreier.action p a 1 y = y
    rw [map_one]
    rfl
  map_mul' g h := by
    rw [← MulOpposite.op_mul, MulOpposite.op_inj]
    apply Iso.ext
    apply Quiver.Hom.unop_inj
    ext y
    change ExposeXI.ArtinSchreier.action p a (DiscreteZMod.equiv p (g * h)) y =
      ExposeXI.ArtinSchreier.action p a (DiscreteZMod.equiv p g)
        (ExposeXI.ArtinSchreier.action p a (DiscreteZMod.equiv p h) y)
    rw [map_mul, map_mul]
    rfl

variable (R) in
lemma charP_of_algebra (Ω : Type*) [Field Ω] [Algebra R Ω] : CharP Ω p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (algebraMap R Ω), CharP.cast_eq_zero, map_zero])

variable {p} (Ω : Type u) [Field Ω] [Algebra R Ω] [CharP Ω p]

/-- The geometric points of the Artin–Schreier covering move under `k ∈ ℤ/p` by translation of the
root: `x ↦ x ∘ (T ↦ T + k)` sends `x(T)` to `x(T) + k`. -/
lemma comp_action_root (a : R) (x : ExposeXI.ArtinSchreierAlgebra R p a →ₐ[R] Ω)
    (k : Multiplicative (ZMod p)) :
    x (ExposeXI.ArtinSchreier.action p a k (AdjoinRoot.root _)) =
      x (AdjoinRoot.root _) + ZMod.castHom (dvd_refl p) Ω (Multiplicative.toAdd k) := by
  rw [ExposeXI.ArtinSchreier.action_root, map_add, AlgHom.commutes]
  congr 1
  rw [← RingHom.comp_apply, RingHom.ext_zmod ((algebraMap R Ω).comp (ZMod.castHom _ R))]

/-- XI.6.7: `ℤ/p` acts simply transitively on the geometric points of the Artin–Schreier
covering. -/
theorem existsUnique_comp_action (a : R) (x y : ExposeXI.ArtinSchreierAlgebra R p a →ₐ[R] Ω) :
    ∃! k : Multiplicative (ZMod p), x.comp (ExposeXI.ArtinSchreier.action p a k).toAlgHom = y := by
  have hx := (ExposeXI.ArtinSchreier.pointsEquiv p a Ω x).2
  have hy := (ExposeXI.ArtinSchreier.pointsEquiv p a Ω y).2
  change x (AdjoinRoot.root _) - x (AdjoinRoot.root _) ^ p = _ at hx
  change y (AdjoinRoot.root _) - y (AdjoinRoot.root _) ^ p = _ at hy
  set d := y (AdjoinRoot.root _) - x (AdjoinRoot.root _)
  have hd : d ^ p - d + 0 = 0 := by
    rw [sub_pow_char]
    linear_combination hx - hy
  -- `d` is a root of `Tᵖ - T = ∏ (T - k)`
  have hprod := congrArg (Polynomial.eval d)
    (ExposeXI.ArtinSchreier.X_pow_sub_X_eq_prod (A := Ω) (p := p))
  rw [eval_add, eval_sub, eval_pow, eval_X, eval_C, hd, eval_prod] at hprod
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hprod.symm
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
  have hcomp (l : Multiplicative (ZMod p)) : (x.comp (ExposeXI.ArtinSchreier.action p a l).toAlgHom)
      (AdjoinRoot.root _) = x (AdjoinRoot.root _) + ZMod.castHom (dvd_refl p) Ω
        (Multiplicative.toAdd l) :=
    comp_action_root Ω a x l
  refine ⟨Multiplicative.ofAdd k, AdjoinRoot.algHom_ext ?_, fun l hl ↦ ?_⟩
  · rw [hcomp, toAdd_ofAdd, ← hk]
    ring
  · have h₁ := congrArg (fun z ↦ z (AdjoinRoot.root (X ^ p - X + C a))) hl
    rw [hcomp] at h₁
    have h₂ : ZMod.castHom (dvd_refl p) Ω (Multiplicative.toAdd l) =
        ZMod.castHom (dvd_refl p) Ω k := by
      rw [← hk]
      linear_combination h₁
    rw [← toAdd_ofAdd k] at h₂
    exact Multiplicative.toAdd.injective ((ZMod.castHom (dvd_refl p) Ω).injective h₂)

omit [CharP R p] in
lemma nontrivial_artinSchreierAlgebra [IsDomain R] (a : R) :
    Nontrivial (ExposeXI.ArtinSchreierAlgebra R p a) := by
  refine AdjoinRoot.nontrivial _ ?_
  rw [degree_eq_natDegree (ExposeXI.ArtinSchreier.monic hp.out a).ne_zero,
    ExposeXI.ArtinSchreier.natDegree_eq hp.out]
  exact_mod_cast hp.out.ne_zero

variable [IsDomain R] [ConnectedSpace (PrimeSpectrum R)] [IsSepClosed Ω]

/-- XI.6.7, V.5.11: the Artin–Schreier covering of `a` is a principal object with group `ℤ/p` of
the Galois category of étale coverings of `Spec R`, for the fibre functor at the geometric point
`R → Ω`. -/
noncomputable def artinSchreierPrincipal (a : R) :
    ExposeXI.PrincipalObject (ExposeV.fiberFunctor R Ω) (DiscreteZMod.{u} p) where
  X := Opposite.op (artinSchreierFE p a)
  α := artinSchreierAction p a
  isPrincipalHomogeneous x y := by
    obtain ⟨k, hk, huniq⟩ := existsUnique_comp_action Ω a x y
    refine ⟨(DiscreteZMod.equiv.{u} p).symm k, ?_, fun g hg ↦ ?_⟩
    · change x.comp (ExposeXI.ArtinSchreier.action p a
        (DiscreteZMod.equiv.{u} p ((DiscreteZMod.equiv.{u} p).symm k))).toAlgHom = y
      rw [MulEquiv.apply_symm_apply]
      exact hk
    · rw [MulEquiv.eq_symm_apply]
      exact huniq _ hg
  nonempty := by
    have := ExposeXI.ArtinSchreier.etale hp.out (CharP.cast_eq_zero R p) a
    have := nontrivial_artinSchreierAlgebra (p := p) a
    exact ExposeV.nonempty_algHom_of_nontrivial (R := R)
      (A := ExposeXI.ArtinSchreierAlgebra R p a) Ω

/-- XI.6.8–XI.6.9: if the Artin–Schreier coverings of `a` and `b` are isomorphic principal
objects, then `b - a ∈ ℘(R)`. -/
theorem exists_sub_eq_of_isIso_artinSchreierPrincipal (a b : R)
    (h : (artinSchreierPrincipal Ω a).IsIso (artinSchreierPrincipal Ω b)) :
    ∃ c : R, b - a = c - c ^ p := by
  obtain ⟨φ, hφ⟩ := h
  let e₁ : ExposeXI.ArtinSchreierAlgebra R p b →ₐ[R] ExposeXI.ArtinSchreierAlgebra R p a :=
    φ.hom.unop.hom.hom
  let e₂ : ExposeXI.ArtinSchreierAlgebra R p a →ₐ[R] ExposeXI.ArtinSchreierAlgebra R p b :=
    φ.inv.unop.hom.hom
  have h₁ : e₁.comp e₂ = AlgHom.id R _ := by
    have := congrArg (fun f ↦ f.unop.hom.hom) φ.hom_inv_id
    exact this
  have h₂ : e₂.comp e₁ = AlgHom.id R _ := by
    have := congrArg (fun f ↦ f.unop.hom.hom) φ.inv_hom_id
    exact this
  let e := AlgEquiv.ofAlgHom e₁ e₂ h₁ h₂
  refine (ExposeXI.ArtinSchreier.nonempty_equivariant_iff b a).mp ⟨e, fun k y ↦ ?_⟩
  have := congrArg (fun f ↦ f.unop.hom.hom y) (hφ ((DiscreteZMod.equiv.{u} p).symm k)).symm
  simp only [artinSchreierPrincipal, artinSchreierAction] at this
  exact this

end Algebra

section TopologicallyFG

/-- A continuous surjective image of a topologically finitely generated group is topologically
finitely generated. -/
theorem IsTopologicallyFG.of_surjective {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (hG : IsTopologicallyFG G) (φ : G →* H) (hφ : Continuous φ)
    (hs : Function.Surjective φ) : IsTopologicallyFG H := by
  classical
  obtain ⟨s, hsd⟩ := hG
  refine ⟨s.image φ, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, Subgroup.coe_map]
  exact hs.denseRange.dense_image hφ hsd

end TopologicallyFG

section AffineLine

/-- XIII.2.13, algebraic form: for a field `k` of characteristic `p` and a geometric point
`k[T] → Ω`, the automorphism group of the fibre functor of the finite étale `k[T]`-algebras
(`π₁(𝔸¹_k)`, V.7) is not topologically finitely generated: the Artin–Schreier coverings of the
polynomials without monomials of degree divisible by `p` give infinitely many continuous
homomorphisms to `ℤ/p`. -/
theorem not_isTopologicallyFG_aut_fiberFunctor (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra k[X] Ω] :
    ¬ IsTopologicallyFG (Aut (ExposeV.fiberFunctor k[X] Ω)) := by
  intro hfg
  have : CharP Ω p := charP_of_algebra p k[X] Ω
  have hfin := finite_continuousMonoidHom_of_isTopologicallyFG hfg (DiscreteZMod.{u} p)
  let P := fun e : primeToPPolys k p ↦ artinSchreierPrincipal (p := p) Ω (e : k[X])
  let ρ : primeToPPolys k p →
      ContinuousMonoidHom (Aut (ExposeV.fiberFunctor k[X] Ω)) (DiscreteZMod.{u} p) :=
    fun e ↦ ⟨(P e).hom (P e).nonempty.some, ExposeV.continuous_torsorHom _ _⟩
  have hinj : Function.Injective ρ := by
    intro e e' h
    have hh : (P e).hom (P e).nonempty.some = (P e').hom (P e').nonempty.some :=
      congrArg ContinuousMonoidHom.toMonoidHom h
    obtain ⟨c, hc⟩ := exists_sub_eq_of_isIso_artinSchreierPrincipal Ω _ _
      ((P e).exists_iso_of_torsorHom_eq (P e') _ _ hh)
    have hmem : (e' : k[X]) - e ∈ (artinSchreierPoly k p).range := ⟨-c, by
      rw [artinSchreierPoly_apply, ExposeXI.ArtinSchreier.neg_pow_char, hc]
      ring⟩
    have := eq_zero_of_mem_primeToPPolys_of_mem_range (sub_mem e'.2 e.2) hmem
    exact Subtype.ext (sub_eq_zero.mp this).symm
  have := infinite_primeToPPolys k p
  have := Finite.of_injective ρ hinj
  exact _root_.not_finite (primeToPPolys k p)

/-- XIII.2.13: over a field `k` of characteristic `p > 0` (algebraically closed in SGA), the
fundamental group `π₁(𝔸¹_k, x)` of the affine line is not topologically finitely generated, for
every geometric point `x`. -/
theorem not_isTopologicallyFG_fundamentalGroup_affineLine (p : ℕ) [Fact p.Prime] (k : Type u)
    [Field k] [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of k[X])) :
    ¬ IsTopologicallyFG (FundamentalGroup x) := by
  intro hfg
  let := ExposeV.algebraOfPoint (CommRingCat.of k[X]) Ω x
  have hE : ∀ R : CommRingCat.{u}, (ExposeV.specFunctor R).IsEquivalence := fun _ ↦ inferInstance
  have := hE (CommRingCat.of k[X])
  let u : ExposeV.specFunctor (CommRingCat.of k[X]) ⋙ ExposeV.FEt.fiber Ω x ≅
      ExposeV.fiberFunctor (CommRingCat.of k[X]) Ω :=
    Functor.isoWhiskerLeft (ExposeV.specFunctor _) (ExposeV.FEt.fiberSpecIso _ Ω x) ≪≫
      (Functor.associator (ExposeV.specFunctor _) (ExposeV.specEquivalence _).inverse
        (ExposeV.fiberFunctor _ Ω)).symm ≪≫
      Functor.isoWhiskerRight (ExposeV.specEquivalence _).unitIso.symm _ ≪≫
      Functor.leftUnitor _
  exact not_isTopologicallyFG_aut_fiberFunctor p k Ω (hfg.of_surjective
    (ExposeV.autMap (ExposeV.specFunctor _) u) (ExposeV.continuous_autMap _ u)
    (ExposeV.autMap_bijective _ u).2)

/-- XI.6.9 for the affine line, as used in XIII.2.13: for `k` algebraically closed of
characteristic `p`, the continuous homomorphisms `π₁(𝔸¹_k, x) → ℤ/p` correspond bijectively to
`k[T]/℘(k[T])`. This is XI's `artinSchreierEquivContinuousMonoidHom` for `S = Spec k[T]`, with
`Γ(Spec k[T], 𝒪) = k[T]` and the sign convention `℘ = id - F` of XI changed to `℘ = F - id`. -/
theorem affineLineArtinSchreier (p : ℕ) [Fact p.Prime] :
    AffineLineArtinSchreierStatement.{u} p := by
  intro k _ _ _ Ω _ _ x
  let ψ : Γ(Spec (CommRingCat.of k[X]), ⊤) ≃+* k[X] :=
    (Scheme.ΓSpecIso (CommRingCat.of k[X])).commRingCatIsoToRingEquiv
  have hS : ((p : ℕ) : Γ(Spec (CommRingCat.of k[X]), ⊤)) = 0 := by
    apply ψ.injective
    rw [map_natCast, map_zero, CharP.cast_eq_zero]
  have : ConnectedSpace (Spec (CommRingCat.of k[X])) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum k[X]))
  let e₁ := ExposeXI.artinSchreierEquivContinuousMonoidHom (Spec (CommRingCat.of k[X])) p hS x
    (DiscreteZMod.equiv.{u} p)
  refine ⟨e₁.symm.trans (Quotient.congr (Multiplicative.toAdd.trans ψ.toEquiv) fun a b ↦ ?_)⟩
  rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
  change _ ↔ -ψ (Multiplicative.toAdd a) + ψ (Multiplicative.toAdd b) ∈ _
  constructor
  · rintro ⟨c, hc⟩
    rw [← ofAdd_toAdd c, ExposeXI.wpΓ_apply] at hc
    have hc' : Multiplicative.toAdd c - Multiplicative.toAdd c ^ p =
        -Multiplicative.toAdd a + Multiplicative.toAdd b := by
      have := congrArg Multiplicative.toAdd hc
      simpa using this
    refine ⟨-ψ (Multiplicative.toAdd c), ?_⟩
    have h := congrArg ψ hc'
    rw [map_sub, map_pow, map_add, map_neg] at h
    rw [artinSchreierPoly_apply, ExposeXI.ArtinSchreier.neg_pow_char]
    linear_combination h
  · rintro ⟨d, hd⟩
    rw [artinSchreierPoly_apply] at hd
    refine ⟨Multiplicative.ofAdd (-ψ.symm d), ?_⟩
    rw [ExposeXI.wpΓ_apply]
    apply Multiplicative.toAdd.injective
    apply ψ.injective
    simp only [toAdd_ofAdd, toAdd_mul, toAdd_inv, map_sub, map_neg, map_pow, map_add,
      RingEquiv.apply_symm_apply]
    rw [ExposeXI.ArtinSchreier.neg_pow_char]
    linear_combination hd

end AffineLine

end SGA.SGA1.ExposeXIII
