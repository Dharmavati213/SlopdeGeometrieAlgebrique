/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXI.Kummer
import SGA.SGA1.ExposeXI.KummerCohomology
import SGA.SGA1.ExposeXI.Representability

/-!
# SGA 1, Exposé XI.6.4: the coboundary of a unit is the class of its Kummer covering

For a unit `a` of `Γ(S, 𝒪_S)`, the coboundary `∂ a ∈ H¹(S, μ_n)` of the Kummer sequence is, by
definition (XI.4), the class of the `μ_n`-torsor `u_n⁻¹(a)` of `n`-th roots of `a`. When `S` is
affine, with ring `A`, this torsor is represented by the Kummer covering
`Spec A[T]/(Tⁿ - a) ⟶ S` of XI.6.2 (`representableBy_kummerCovering`): an `S`-morphism
`T ⟶ Spec A[T]/(Tⁿ - a)` is an `n`-th root of `a` in `Γ(T, 𝒪_T)`, necessarily a unit.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Polynomial

namespace SGA.SGA1.ExposeXI

/-- A morphism to an affine scheme `Spec R` is determined by the ring map `R ⟶ Γ(X, ⊤)` it
induces. -/
lemma eq_toSpecΓ_comp_Spec_map {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

variable (S : Scheme.{u}) [IsAffine S] (n : ℕ) [NeZero n] (a : (Γ(S, ⊤))ˣ)

/-- The ring `Γ(S)[T]/(Tⁿ - a)` of the Kummer covering of `a`. -/
noncomputable abbrev kummerRing : CommRingCat.{u} := CommRingCat.of (KummerAlgebra Γ(S, ⊤) n (a : Γ(S, ⊤)))

/-- XI.6.2, XI.6.4: the Kummer covering `Spec Γ(S)[T]/(Tⁿ - a)` of an affine scheme `S`, as an
`S`-scheme. -/
noncomputable abbrev kummerCovering : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (kummerRing S n a))) ≫ S.isoSpec.inv)

/-- The `μ_n`-torsor `u_n⁻¹(a)` of `n`-th roots of `a`, whose class is `∂ a` (XI.6.4). -/
noncomputable abbrev kummerFiberTorsor : CategoryTheory.Torsor (fpqc S) (Mu S n) :=
  (kummer_isShortExact S n).fiberTorsor (isSheaf_Gm S) (isSheaf_Gm S) Over.mkIdTerminal a

omit [IsAffine S] in
/-- XI.6.4: `∂ a` is the class of the torsor of `n`-th roots of `a`. -/
lemma kummerConnecting_apply : kummerConnecting S n a = (kummerFiberTorsor S n a).class :=
  rfl

/-- The root `T` of `Tⁿ - a`, as a global section of the Kummer covering. -/
noncomputable def kummerRoot : Γ(Spec (kummerRing S n a), ⊤) :=
  (Scheme.ΓSpecIso (kummerRing S n a)).inv (AdjoinRoot.root _)

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.6.4: for affine `S`, the torsor `u_n⁻¹(a)` of `n`-th roots of `a`, whose class is `∂ a`,
is represented by the Kummer covering `Spec Γ(S)[T]/(Tⁿ - a)`: the `S`-morphisms
`T ⟶ Spec Γ(S)[T]/(Tⁿ - a)` are the `n`-th roots of `a` in `Γ(T, 𝒪_T)`, by pulling back the
root `T`. -/
theorem representableBy_kummerCovering :
    Nonempty ((kummerFiberTorsor S n a).obj.RepresentableBy (kummerCovering S n a)) := by
  let K := kummerRing S n a
  let ι : Γ(S, ⊤) ⟶ K := CommRingCat.ofHom (algebraMap Γ(S, ⊤) K)
  -- The ring maps `K ⟶ Γ(T)` induced by `S`-morphisms `T ⟶ Spec K` extend `Γ(S) ⟶ Γ(T)`.
  have hstr : ∀ {T : Over S} (φ : T ⟶ kummerCovering S n a),
      ι ≫ (Scheme.ΓSpecIso K).inv ≫ φ.left.appTop = T.hom.appTop := by
    intro T φ
    have hφ : φ.left ≫ Spec.map ι = T.hom ≫ S.isoSpec.hom := by
      rw [← Iso.comp_inv_eq, Category.assoc]
      exact Over.w φ
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, hφ,
      Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ S.toSpecΓ.appTop ≫ T.hom.appTop = _
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  have hroot : (AdjoinRoot.root _ : K) ^ n = ι (a : Γ(S, ⊤)) := Kummer.root_pow n _
  have hunit : IsUnit (kummerRoot S n a) := by
    have : IsUnit ((AdjoinRoot.root _ : K) ^ n) := hroot ▸ a.isUnit.map ι.hom
    exact ((isUnit_pow_iff (NeZero.ne n)).1 this).map (Scheme.ΓSpecIso K).inv.hom
  let F := (kummerFiberTorsor S n a).obj
  have hfrom : ∀ T : Over S, (Over.mkIdTerminal.from T).left = T.hom := fun T ↦ by
    simp
  have hmem : ∀ {T : Over S} (x : (Γ(T.left, ⊤))ˣ),
      (x : Γ(T.left, ⊤)) ^ n = T.hom.appTop (a : Γ(S, ⊤)) →
        (powGm S n).app (op T) x = (Gm S).map (Over.mkIdTerminal.from T).op a :=
    fun {T} x hx ↦ Units.ext (by
      change (x : Γ(T.left, ⊤)) ^ n = (Over.mkIdTerminal.from T).left.appTop (a : Γ(S, ⊤))
      rw [hfrom]
      exact hx)
  have hcov : ((kummerRoot S n a) : Γ(Spec K, ⊤)) ^ n =
      (kummerCovering S n a).hom.appTop (a : Γ(S, ⊤)) := by
    have := congrArg (fun m ↦ m (a : Γ(S, ⊤))) (hstr (𝟙 (kummerCovering S n a)))
    simp only [Over.id_left, Scheme.Hom.id_appTop] at this
    rw [← this, kummerRoot, ← map_pow, hroot]
    rfl
  let u : F.obj (op (kummerCovering S n a)) := ⟨hunit.unit, hmem _ hcov⟩
  refine ⟨representableByOfBijective u fun T ↦ ⟨fun φ ψ e ↦ ?_, fun s ↦ ?_⟩⟩
  · have e' : φ.left.appTop (kummerRoot S n a) = ψ.left.appTop (kummerRoot S n a) :=
      congrArg (fun y : F.obj (op T) ↦ ((show (Γ(T.left, ⊤))ˣ from y.1) : Γ(T.left, ⊤))) e
    have hρ : (Scheme.ΓSpecIso K).inv ≫ φ.left.appTop =
        (Scheme.ΓSpecIso K).inv ≫ ψ.left.appTop := by
      ext1
      refine AdjoinRoot.ringHom_ext ?_ e'
      have h := (hstr φ).trans (hstr ψ).symm
      rw [← AdjoinRoot.algebraMap_eq]
      exact congrArg CommRingCat.Hom.hom h
    ext
    calc φ.left = _ := eq_toSpecΓ_comp_Spec_map _
      _ = _ := by rw [hρ]
      _ = ψ.left := (eq_toSpecΓ_comp_Spec_map _).symm
  · obtain ⟨x₀, hx⟩ := s
    let x : (Γ(T.left, ⊤))ˣ := x₀
    have hx' : (x : Γ(T.left, ⊤)) ^ n = T.hom.appTop (a : Γ(S, ⊤)) := by
      have h := congrArg Units.val hx
      change (x : Γ(T.left, ⊤)) ^ n = (Over.mkIdTerminal.from T).left.appTop (a : Γ(S, ⊤)) at h
      rwa [hfrom] at h
    have hev : eval₂ T.hom.appTop.hom (x : Γ(T.left, ⊤)) (X ^ n - C (a : Γ(S, ⊤))) = 0 := by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, hx', sub_self]
    let ρ : K ⟶ Γ(T.left, ⊤) := CommRingCat.ofHom (AdjoinRoot.lift T.hom.appTop.hom
      (x : Γ(T.left, ⊤)) hev)
    have hιρ : ι ≫ ρ = T.hom.appTop := by
      ext y
      exact AdjoinRoot.lift_of hev
    let φ₀ : T.left ⟶ Spec K := T.left.toSpecΓ ≫ Spec.map ρ
    have hφ₀ : φ₀ ≫ (kummerCovering S n a).hom = T.hom := by
      change (T.left.toSpecΓ ≫ Spec.map ρ) ≫ Spec.map ι ≫ S.isoSpec.inv = T.hom
      rw [Category.assoc, ← Spec.map_comp_assoc, hιρ, ← Scheme.toSpecΓ_naturality_assoc]
      change T.hom ≫ S.isoSpec.hom ≫ S.isoSpec.inv = T.hom
      rw [Iso.hom_inv_id, Category.comp_id]
    refine ⟨CategoryTheory.Over.homMk φ₀ hφ₀, Subtype.ext (Units.ext ?_)⟩
    let r₀ : K := AdjoinRoot.root (X ^ n - C (a : Γ(S, ⊤)))
    have step : (Spec.map ρ).appTop ((Scheme.ΓSpecIso K).inv r₀) =
        (Scheme.ΓSpecIso Γ(T.left, ⊤)).inv (ρ r₀) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change (T.left.toSpecΓ ≫ Spec.map ρ).appTop ((Scheme.ΓSpecIso K).inv r₀) = x
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, step, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_apply]
    exact AdjoinRoot.lift_root hev

end SGA.SGA1.ExposeXI
