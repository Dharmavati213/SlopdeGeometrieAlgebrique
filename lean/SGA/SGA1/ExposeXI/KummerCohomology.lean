/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.CohomologySequence
import SGA.SGA1.ExposeXI.GroupSheaves
import SGA.SGA1.ExposeXI.Kummer

/-!
# SGA 1, Exposé XI.6.1–XI.6.6: the Kummer sequence in fpqc cohomology

Let `S` be a scheme and `n > 0`. On the site of `S`-schemes with the fpqc topology, the `n`-th
power map `u_n` of `𝔾_{m,S}` is locally surjective: over an affine `Spec A ⟶ T`, a unit `a`
becomes an `n`-th power on the Kummer covering `Spec A[T]/(Tⁿ - a)`, which is faithfully flat.
Hence the Kummer sequence `1 → μ_n → 𝔾_m → 𝔾_m → 1` is a short exact sequence of fpqc sheaves
(`kummer_isShortExact`, XI.6.1), and the exact sequence of XI.4.5 gives XI.6.4:
```
1 → μ_n(S) → Γ(S, 𝒪_S)ˣ → Γ(S, 𝒪_S)ˣ → H¹(S, μ_n) → H¹(S, 𝔾_m) → H¹(S, 𝔾_m)
1 → Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ → H¹(S, μ_n) → ₙH¹(S, 𝔾_m) → 1
```
together with its degenerate cases XI.6.5 and XI.6.6.

Here `H¹(S, G)` is the group of classes of fpqc torsors under the sheaf `G` on `S`-schemes
(`SGA.Foundations.Etale`); for `G = μ_n` these are the Kummer principal coverings of XI.6.2
(they are representable by effective descent of affine schemes, footnote 296 of XI.4.4, see
`SGA.SGA1.ExposeXI.AssociatedBundle`; for `S` affine, the torsor `∂ a` is represented by the
Kummer covering `Spec Γ(S)[T]/(Tⁿ - a)`, see `SGA.SGA1.ExposeXI.KummerCovering`). SGA writes
`Pic(S) = H¹(S, 𝒪_S^*)` for the Zariski cohomology group and identifies it with `H¹(S, 𝔾_{m,S})`
by XI.5.3; this file uses the fpqc group `H¹(S, 𝔾_m)`, and the statements with `Pic(S)`, through
the isomorphism `H¹(S, 𝔾_m) ≅ Pic(S)` (Hilbert 90), are in `PicardComparison`.
-/

universe u

open CategoryTheory Opposite Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable (S : Scheme.{u}) (n : ℕ)

/-- XI.6.1: the `n`-th power homomorphism `u_n : 𝔾_{m,S} → 𝔾_{m,S}`. -/
abbrev powGm : Gm S ⟶ Gm S :=
  PresheafOfGroups.powHom (Gm_isCommutative S) n

/-- XI.6.1, XI.6.2: the Kummer group `μ_{n,S}`, kernel of `u_n`. -/
abbrev Mu : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  PresheafOfGroups.kernel (powGm S n)

/-- XI.6.1: the inclusion `μ_{n,S} → 𝔾_{m,S}`. -/
abbrev muι : Mu S n ⟶ Gm S :=
  PresheafOfGroups.kernelι (powGm S n)

theorem isSheaf_Mu : Presieve.IsSheaf (fpqc S) (Mu S n ⋙ CategoryTheory.forget GrpCat) :=
  PresheafOfGroups.isSheaf_kernel (isSheaf_Gm S) (isSheaf_Gm S).isSeparated

lemma Mu_isCommutative : PresheafOfGroups.IsCommutative (Mu S n) :=
  fun T a b ↦ Subtype.ext (Gm_isCommutative S T a.1 b.1)

/-- XI.6.2: the group `H¹(S, μ_n)` of Kummer principal coverings. -/
noncomputable instance : CommGroup (H1 (fpqc S) (Mu S n)) :=
  H1.commGroup (Mu_isCommutative S n) (isSheaf_Mu S n)

/-- XI.6.4: the group `H¹(S, 𝔾_m)`. -/
noncomputable instance : CommGroup (H1 (fpqc S) (Gm S)) :=
  H1.commGroup (Gm_isCommutative S) (isSheaf_Gm S)

variable {S n}

/-- A unit of `A` becomes an `n`-th power in the Kummer algebra `A[T]/(Tⁿ - a)`, seen as the ring
of global sections of its spectrum. -/
lemma exists_pow_eq_appTop_kummer {X : Scheme.{u}} (A : CommRingCat.{u}) (g : Spec A ⟶ X)
    (c : Γ(X, ⊤)) :
    ∃ v : Γ(Spec (CommRingCat.of (KummerAlgebra A n ((Scheme.ΓSpecIso A).hom (g.appTop c)))), ⊤),
      v ^ n = (Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ g).appTop c := by
  refine ⟨(Scheme.ΓSpecIso _).inv (AdjoinRoot.root _), ?_⟩
  rw [← map_pow, Kummer.root_pow]
  exact ΓSpecIso_inv_map_appTop (CommRingCat.ofHom (algebraMap A _)) g c

variable (S n)

/-- XI.6.1: the `n`-th power map `u_n` of `𝔾_{m,S}` is locally surjective for the fpqc
topology: a unit is an `n`-th power on a Kummer covering. -/
theorem powGm_locallySurjective [NeZero n] (T : Over S) (c : (Gm S).obj (op T)) :
    ∃ R ∈ fpqc S T, ∀ ⦃V : Over S⦄ (f : V ⟶ T), R f →
      ∃ g : (Gm S).obj (op V), (powGm S n).app (op V) g = (Gm S).map f.op c := by
  obtain ⟨R, hR, hQ⟩ := exists_fpqc_cover_of_affine (T := T)
    (fun W g ↦ ∃ v : Γ(W, ⊤), v ^ n = g.appTop (c : (Γ(T.left, ⊤))ˣ).1)
    (fun W W' h g ⟨v, hv⟩ ↦ ⟨h.appTop v, by rw [← map_pow, hv, Scheme.Hom.comp_appTop]; rfl⟩)
    (fun A g ↦ ⟨_, CommRingCat.ofHom (algebraMap A _),
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance,
      exists_pow_eq_appTop_kummer (n := n) A g _⟩)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨v, hv⟩ := hQ f hf
  have hu : IsUnit v := (isUnit_pow_iff (NeZero.ne n)).mp
    (hv ▸ (Units.isUnit (c : (Γ(T.left, ⊤))ˣ)).map f.left.appTop.hom)
  refine ⟨(hu.unit : (Γ(V.left, ⊤))ˣ), Units.ext ?_⟩
  change ((hu.unit ^ n : (Γ(V.left, ⊤))ˣ) : Γ(V.left, ⊤)) = f.left.appTop (c : (Γ(T.left, ⊤))ˣ).1
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hv]

/-- XI.6.1: the Kummer sequence `1 → μ_n → 𝔾_m → 𝔾_m → 1` is exact on the fpqc site of `S`. -/
theorem kummer_isShortExact [NeZero n] :
    PresheafOfGroups.IsShortExact (fpqc S) (muι S n) (powGm S n) :=
  PresheafOfGroups.isShortExact_kernel (powGm_locallySurjective S n)

/-- XI.6.4: the coboundary `∂ : Γ(S, 𝒪_S)ˣ → H¹(S, μ_n)`; `∂ a` is the class of the Kummer
torsor `u_n⁻¹(a)` of `n`-th roots of `a`. -/
noncomputable def kummerConnecting [NeZero n] : (Γ(S, ⊤))ˣ →* H1 (fpqc S) (Mu S n) :=
  (kummer_isShortExact S n).connectingHom (isSheaf_Mu S n) (isSheaf_Gm S) (isSheaf_Gm S)
    Over.mkIdTerminal (Mu_isCommutative S n) (Gm_isCommutative S)

/-- XI.6.4: the map `H¹(S, μ_n) → H¹(S, 𝔾_m)`. -/
noncomputable def kummerH1Map : H1 (fpqc S) (Mu S n) →* H1 (fpqc S) (Gm S) :=
  H1.mapHom (isSheaf_Mu S n) (isSheaf_Gm S) (Mu_isCommutative S n) (Gm_isCommutative S)
    (muι S n)

/-- XI.6.4: `u_n` induces the `n`-th power on `H¹(S, 𝔾_m)`. -/
theorem H1_map_powGm (c : H1 (fpqc S) (Gm S)) :
    H1.map (powGm S n) (isSheaf_Gm S) c = c ^ n :=
  H1.map_powHom (isSheaf_Gm S) (Gm_isCommutative S) n c

/-- XI.6.4, exactness at `Γ(S, 𝒪_S)ˣ`: the kernel of `∂` consists of the `n`-th powers. -/
theorem kummerConnecting_ker [NeZero n] :
    (kummerConnecting S n).ker = (powMonoidHom n : (Γ(S, ⊤))ˣ →* _).range := by
  ext c
  refine ((kummer_isShortExact S n).connecting_eq_trivialClass_iff (isSheaf_Mu S n)
    (isSheaf_Gm S) (isSheaf_Gm S) Over.mkIdTerminal c).trans ?_
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g, hg⟩, fun ⟨g, hg⟩ ↦ ⟨g, hg⟩⟩

/-- XI.6.4, exactness at `H¹(S, μ_n)`: the kernel of `H¹(S, μ_n) → H¹(S, 𝔾_m)` is the image
of `∂`. -/
theorem kummerH1Map_ker [NeZero n] : (kummerH1Map S n).ker = (kummerConnecting S n).range := by
  ext x
  obtain ⟨P, rfl⟩ := H1.mk_surjective x
  exact (kummer_isShortExact S n).map_eq_trivialClass_iff (isSheaf_Gm S) (isSheaf_Gm S)
    Over.mkIdTerminal P

/-- XI.6.4, exactness at the first `H¹(S, 𝔾_m)`: the kernel of the `n`-th power map is the
image of `H¹(S, μ_n)`. -/
theorem powMonoidHom_ker_eq_range [NeZero n] :
    (powMonoidHom n : H1 (fpqc S) (Gm S) →* _).ker = (kummerH1Map S n).range := by
  ext x
  obtain ⟨P, rfl⟩ := H1.mk_surjective x
  change P.class ^ n = 1 ↔ _
  rw [← H1_map_powGm]
  refine ((kummer_isShortExact S n).map_p_eq_trivialClass_iff (isSheaf_Gm S) (isSheaf_Gm S)
    P).trans ⟨fun ⟨Q, hQ⟩ ↦ ⟨Q.class, hQ⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨Q, rfl⟩ := H1.mk_surjective y
  exact ⟨Q, hy⟩

/-- XI.6.4: the map `Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ → H¹(S, μ_n)` induced by `∂`. -/
noncomputable def kummerLeft [NeZero n] :
    (Γ(S, ⊤))ˣ ⧸ (powMonoidHom n : (Γ(S, ⊤))ˣ →* _).range →* H1 (fpqc S) (Mu S n) :=
  cokerLift (kummerConnecting_ker S n)

/-- XI.6.4: the map `H¹(S, μ_n) → ₙH¹(S, 𝔾_m)` to the `n`-torsion of `H¹(S, 𝔾_m)`. -/
noncomputable def kummerRight [NeZero n] :
    H1 (fpqc S) (Mu S n) →* (powMonoidHom n : H1 (fpqc S) (Gm S) →* _).ker :=
  kerRestrict (powMonoidHom_ker_eq_range S n)

/-- XI.6.4: the Kummer exact sequence
`1 → Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ → H¹(S, μ_n) → ₙH¹(S, 𝔾_m) → 1`, with the fpqc group
`H¹(S, 𝔾_m)` in place of `Pic(S)`: the first map is injective, its image is the kernel of the
second, and the second is surjective. -/
theorem kummer_exact [NeZero n] :
    Function.Injective (kummerLeft S n) ∧
      (kummerRight S n).ker = (kummerLeft S n).range ∧
      Function.Surjective (kummerRight S n) :=
  ⟨cokerLift_injective _, kerRestrict_ker _ (kummerH1Map_ker S n) _,
    kerRestrict_surjective _⟩

/-- XI.6.5: if `ₙH¹(S, 𝔾_m) = 0` (SGA: `ₙPic(S) = 0`), then
`H¹(S, μ_n) ≅ Γ(S, 𝒪_S)ˣ / Γ(S, 𝒪_S)ˣⁿ`. -/
theorem kummerLeft_bijective [NeZero n]
    (h : ∀ x : H1 (fpqc S) (Gm S), x ^ n = 1 → x = 1) :
    Function.Bijective (kummerLeft S n) :=
  cokerLift_bijective_of_ker_eq_bot _ (kummerH1Map_ker S n) (powMonoidHom_ker_eq_range S n)
    ((MonoidHom.ker_eq_bot_iff _).2 ((injective_iff_map_eq_one _).2 h))

/-- XI.6.6: if every element of `Γ(S, 𝒪_S)` is an `n`-th power, then
`H¹(S, μ_n) ≅ ₙH¹(S, 𝔾_m)` (SGA: `ₙPic(S)`). -/
theorem kummerRight_bijective [NeZero n] (h : ∀ a : Γ(S, ⊤), ∃ b, b ^ n = a) :
    Function.Bijective (kummerRight S n) := by
  refine kerRestrict_bijective_of_surjective (kummerConnecting_ker S n) (kummerH1Map_ker S n) _
    fun a ↦ ?_
  obtain ⟨b, hb⟩ := h a
  have hu : IsUnit b := (isUnit_pow_iff (NeZero.ne n)).mp (hb ▸ a.isUnit)
  exact ⟨hu.unit, Units.ext (by rw [powMonoidHom_apply, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec, hb])⟩

end SGA.SGA1.ExposeXI
