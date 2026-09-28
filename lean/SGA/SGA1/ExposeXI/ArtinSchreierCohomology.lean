/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.ArtinSchreier
import SGA.SGA1.ExposeXI.CohomologySequence
import SGA.SGA1.ExposeXI.GroupSheaves

/-!
# SGA 1, Exposé XI.6.7–XI.6.10: the Artin–Schreier sequence in fpqc cohomology

Let `p` be a prime and `S` a scheme of characteristic `p` (`p · 𝒪_S = 0`). The Frobenius
`F : 𝔾_{a,S} → 𝔾_{a,S}`, `a ↦ aᵖ`, is a homomorphism, and so is `℘ = id - F`. On the site of
`S`-schemes with the fpqc topology `℘` is locally surjective: over an affine `Spec A ⟶ T`, a
section `a` is in the image of `℘` on the Artin–Schreier covering `Spec A[T]/(Tᵖ - T + a)`,
which is faithfully flat. Its kernel is the sheaf `(ℤ/p)_S` (`ZpS`, the sections `a` with
`aᵖ = a`; for `S` affine this is the constant group `ℤ/p` by
`ArtinSchreier.bijective_kernelEval`). So the Artin–Schreier sequence
`0 → (ℤ/p)_S → 𝔾_a → 𝔾_a → 0` is exact on the fpqc site (`artinSchreier_isShortExact`, XI.6.7),
and XI.4.5 gives XI.6.8:
```
0 → Γ(S, 𝒪_S) / ℘ Γ(S, 𝒪_S) → H¹(S, ℤ/p) → H¹(S, 𝒪_S)^F → 0
```
with its degenerate cases XI.6.9 and XI.6.10.

As in `Ga`, the additive group `𝔾_a` is written multiplicatively (`Multiplicative Γ(S, 𝒪_S)`),
because the sheaves of groups of `SGA.Foundations.Etale` are multiplicative. `H¹(S, 𝒪_S)` is the
fpqc group `H¹(S, 𝔾_a)`, which SGA identifies with the Zariski cohomology group by XI.5.3
(`h1GaEquivZariski`). The example "`S` affine" of XI.6.9 is
`artinSchreierLeft_bijective_of_isAffine` (`AdditiveTorsors`).
-/

universe u

open CategoryTheory Opposite Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable (S : Scheme.{u}) (p : ℕ) [hp : Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

omit hp in
include hS in
lemma natCast_eq_zero_of_over (T : Over S) : (p : Γ(T.left, ⊤)) = 0 := by
  rw [← map_natCast T.hom.appTop.hom, hS, map_zero]

/-- XI.6.7: the Frobenius homomorphism `F : 𝔾_{a,S} → 𝔾_{a,S}`, `a ↦ aᵖ`. -/
def frobGa : Ga S ⟶ Ga S where
  app T := GrpCat.ofHom (AddMonoidHom.toMultiplicative
    { toFun a := a ^ p
      map_zero' := zero_pow hp.out.ne_zero
      map_add' a b := ArtinSchreier.add_pow_of_natCast_eq_zero hp.out
        (natCast_eq_zero_of_over S p hS T.unop) a b })
  naturality T T' f := by
    ext a
    exact (map_pow f.unop.left.appTop.hom _ p).symm

/-- XI.6.7: `℘ = id - F : 𝔾_{a,S} → 𝔾_{a,S}`, `a ↦ a - aᵖ`. -/
def wpGa : Ga S ⟶ Ga S :=
  PresheafOfGroups.homMul (Ga_isCommutative S) (𝟙 _)
    (PresheafOfGroups.homInv (Ga_isCommutative S) (frobGa S p hS))

lemma wpGa_app_apply (T : (Over S)ᵒᵖ) (a : Γ(T.unop.left, ⊤)) :
    (wpGa S p hS).app T (Multiplicative.ofAdd a) = Multiplicative.ofAdd (a - a ^ p) := by
  change Multiplicative.ofAdd (a + -(a ^ p)) = _
  rw [← sub_eq_add_neg]

/-- XI.6.7: the sheaf `(ℤ/p)_S`, kernel of `℘`: the sections `a` of `𝒪` with `aᵖ = a`. -/
abbrev ZpS : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  PresheafOfGroups.kernel (wpGa S p hS)

/-- XI.6.7: the inclusion `(ℤ/p)_S → 𝔾_{a,S}`. -/
abbrev zpι : ZpS S p hS ⟶ Ga S :=
  PresheafOfGroups.kernelι (wpGa S p hS)

theorem isSheaf_ZpS : Presieve.IsSheaf (fpqc S) (ZpS S p hS ⋙ CategoryTheory.forget GrpCat) :=
  PresheafOfGroups.isSheaf_kernel (isSheaf_Ga S) (isSheaf_Ga S).isSeparated

lemma ZpS_isCommutative : PresheafOfGroups.IsCommutative (ZpS S p hS) :=
  fun T a b ↦ Subtype.ext (Ga_isCommutative S T a.1 b.1)

/-- XI.6.8: the group `H¹(S, ℤ/p)`. -/
noncomputable instance : CommGroup (H1 (fpqc S) (ZpS S p hS)) :=
  H1.commGroup (ZpS_isCommutative S p hS) (isSheaf_ZpS S p hS)

/-- XI.6.8: the group `H¹(S, 𝒪_S) = H¹(S, 𝔾_a)`. -/
noncomputable instance : CommGroup (H1 (fpqc S) (Ga S)) :=
  H1.commGroup (Ga_isCommutative S) (isSheaf_Ga S)

variable {S p}

omit hp in
/-- A section `a` becomes of the form `v - vᵖ` on the Artin–Schreier covering
`A[T]/(Tᵖ - T + a)`, seen as the ring of global sections of its spectrum. -/
lemma exists_sub_pow_eq_appTop_artinSchreier {X : Scheme.{u}} (A : CommRingCat.{u})
    (g : Spec A ⟶ X) (c : Γ(X, ⊤)) :
    ∃ v : Γ(Spec (CommRingCat.of
        (ArtinSchreierAlgebra A p ((Scheme.ΓSpecIso A).hom (g.appTop c)))), ⊤),
      v - v ^ p = (Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ g).appTop c := by
  refine ⟨(Scheme.ΓSpecIso _).inv (AdjoinRoot.root _), ?_⟩
  rw [← map_pow, ← map_sub, ArtinSchreier.root_pow, sub_sub_cancel]
  exact ΓSpecIso_inv_map_appTop (CommRingCat.ofHom (algebraMap A _)) g c

variable (S p)

/-- XI.6.7: `℘` is locally surjective for the fpqc topology: every section is in the image of
`℘` on an Artin–Schreier covering. -/
theorem wpGa_locallySurjective (T : Over S) (c : (Ga S).obj (op T)) :
    ∃ R ∈ fpqc S T, ∀ ⦃V : Over S⦄ (f : V ⟶ T), R f →
      ∃ g : (Ga S).obj (op V), (wpGa S p hS).app (op V) g = (Ga S).map f.op c := by
  obtain ⟨R, hR, hQ⟩ := exists_fpqc_cover_of_affine (T := T)
    (fun W g ↦ ∃ v : Γ(W, ⊤), v - v ^ p = g.appTop (Multiplicative.toAdd c))
    (fun W W' h g ⟨v, hv⟩ ↦ ⟨h.appTop v, by
      rw [← map_pow, ← map_sub, hv, Scheme.Hom.comp_appTop]; rfl⟩)
    (fun A g ↦ ⟨_, CommRingCat.ofHom (algebraMap A _),
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance,
      exists_sub_pow_eq_appTop_artinSchreier A g _⟩)
  refine ⟨R, hR, fun V f hf ↦ ?_⟩
  obtain ⟨v, hv⟩ := hQ f hf
  refine ⟨Multiplicative.ofAdd v, ?_⟩
  rw [wpGa_app_apply, hv]
  rfl

/-- XI.6.7: the Artin–Schreier sequence `0 → (ℤ/p)_S → 𝔾_a → 𝔾_a → 0` is exact on the fpqc
site of `S`. -/
theorem artinSchreier_isShortExact :
    PresheafOfGroups.IsShortExact (fpqc S) (zpι S p hS) (wpGa S p hS) :=
  PresheafOfGroups.isShortExact_kernel (wpGa_locallySurjective S p hS)

/-- XI.6.8: the coboundary `∂ : Γ(S, 𝒪_S) → H¹(S, ℤ/p)`; `∂ a` is the class of the
Artin–Schreier torsor `℘⁻¹(a)`. -/
noncomputable def artinSchreierConnecting :
    Multiplicative Γ(S, ⊤) →* H1 (fpqc S) (ZpS S p hS) :=
  (artinSchreier_isShortExact S p hS).connectingHom (isSheaf_ZpS S p hS) (isSheaf_Ga S)
    (isSheaf_Ga S) Over.mkIdTerminal (ZpS_isCommutative S p hS) (Ga_isCommutative S)

/-- XI.6.8: the map `H¹(S, ℤ/p) → H¹(S, 𝒪_S)`. -/
noncomputable def artinSchreierH1Map : H1 (fpqc S) (ZpS S p hS) →* H1 (fpqc S) (Ga S) :=
  H1.mapHom (isSheaf_ZpS S p hS) (isSheaf_Ga S) (ZpS_isCommutative S p hS) (Ga_isCommutative S)
    (zpι S p hS)

/-- XI.6.8: the Frobenius `F` acting on `H¹(S, 𝒪_S)`. -/
noncomputable def frobH1 : H1 (fpqc S) (Ga S) →* H1 (fpqc S) (Ga S) :=
  H1.mapHom (isSheaf_Ga S) (isSheaf_Ga S) (Ga_isCommutative S) (Ga_isCommutative S)
    (frobGa S p hS)

/-- XI.6.8: the map induced by `℘` on `H¹(S, 𝒪_S)`. -/
noncomputable def wpH1 : H1 (fpqc S) (Ga S) →* H1 (fpqc S) (Ga S) :=
  H1.mapHom (isSheaf_Ga S) (isSheaf_Ga S) (Ga_isCommutative S) (Ga_isCommutative S)
    (wpGa S p hS)

/-- XI.6.8: `℘` induces `id - F` on `H¹(S, 𝒪_S)` (written multiplicatively). -/
theorem wpH1_apply (x : H1 (fpqc S) (Ga S)) : wpH1 S p hS x = x * (frobH1 S p hS x)⁻¹ := by
  change H1.map (wpGa S p hS) (isSheaf_Ga S) x = _
  rw [wpGa, H1.map_homMul, H1.map_homInv, H1.map_id]
  rfl

/-- XI.6.8: the kernel of `℘` on `H¹(S, 𝒪_S)` is the subgroup `H¹(S, 𝒪_S)^F` of invariants of
the Frobenius. -/
theorem mem_wpH1_ker_iff (x : H1 (fpqc S) (Ga S)) :
    x ∈ (wpH1 S p hS).ker ↔ frobH1 S p hS x = x := by
  rw [MonoidHom.mem_ker, wpH1_apply, mul_inv_eq_one, eq_comm]

/-- XI.6.8: `℘` on `H⁰(S, 𝒪_S) = Γ(S, 𝒪_S)`. -/
noncomputable def wpΓ : Multiplicative Γ(S, ⊤) →* Multiplicative Γ(S, ⊤) :=
  ((wpGa S p hS).app (op (Over.mk (𝟙 S)))).hom

lemma wpΓ_apply (a : Γ(S, ⊤)) :
    wpΓ S p hS (Multiplicative.ofAdd a) = Multiplicative.ofAdd (a - a ^ p) :=
  wpGa_app_apply S p hS (op (Over.mk (𝟙 S))) a

/-- XI.6.8, exactness at `Γ(S, 𝒪_S)`: the kernel of `∂` is `℘ Γ(S, 𝒪_S)`. -/
theorem artinSchreierConnecting_ker :
    (artinSchreierConnecting S p hS).ker = (wpΓ S p hS).range := by
  ext c
  exact (artinSchreier_isShortExact S p hS).connecting_eq_trivialClass_iff (isSheaf_ZpS S p hS)
    (isSheaf_Ga S) (isSheaf_Ga S) Over.mkIdTerminal c

/-- XI.6.8, exactness at `H¹(S, ℤ/p)`. -/
theorem artinSchreierH1Map_ker :
    (artinSchreierH1Map S p hS).ker = (artinSchreierConnecting S p hS).range := by
  ext x
  obtain ⟨P, rfl⟩ := H1.mk_surjective x
  exact (artinSchreier_isShortExact S p hS).map_eq_trivialClass_iff (isSheaf_Ga S)
    (isSheaf_Ga S) Over.mkIdTerminal P

/-- XI.6.8, exactness at the first `H¹(S, 𝒪_S)`. -/
theorem wpH1_ker : (wpH1 S p hS).ker = (artinSchreierH1Map S p hS).range := by
  ext x
  obtain ⟨P, rfl⟩ := H1.mk_surjective x
  refine ((artinSchreier_isShortExact S p hS).map_p_eq_trivialClass_iff (isSheaf_Ga S)
    (isSheaf_Ga S) P).trans ⟨fun ⟨Q, hQ⟩ ↦ ⟨Q.class, hQ⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  obtain ⟨Q, rfl⟩ := H1.mk_surjective y
  exact ⟨Q, hy⟩

/-- XI.6.8: the map `Γ(S, 𝒪_S) / ℘ Γ(S, 𝒪_S) → H¹(S, ℤ/p)` induced by `∂`. -/
noncomputable def artinSchreierLeft :
    Multiplicative Γ(S, ⊤) ⧸ (wpΓ S p hS).range →*
      H1 (fpqc S) (ZpS S p hS) :=
  cokerLift (artinSchreierConnecting_ker S p hS)

/-- XI.6.8: the map `H¹(S, ℤ/p) → H¹(S, 𝒪_S)^F`, where `H¹(S, 𝒪_S)^F` is the kernel of `℘`
(`mem_wpH1_ker_iff`). -/
noncomputable def artinSchreierRight : H1 (fpqc S) (ZpS S p hS) →* (wpH1 S p hS).ker :=
  kerRestrict (wpH1_ker S p hS)

/-- XI.6.8: the exact sequence `0 → Γ(S, 𝒪_S)/℘ Γ(S, 𝒪_S) → H¹(S, ℤ/p) → H¹(S, 𝒪_S)^F → 0`:
the first map is injective, its image is the kernel of the second, and the second is
surjective. -/
theorem artinSchreier_exact :
    Function.Injective (artinSchreierLeft S p hS) ∧
      (artinSchreierRight S p hS).ker = (artinSchreierLeft S p hS).range ∧
      Function.Surjective (artinSchreierRight S p hS) :=
  ⟨cokerLift_injective _, kerRestrict_ker _ (artinSchreierH1Map_ker S p hS) _,
    kerRestrict_surjective _⟩

/-- XI.6.9: if `H¹(S, 𝒪_S)^F = 0`, then `H¹(S, ℤ/p) ≅ Γ(S, 𝒪_S) / ℘ Γ(S, 𝒪_S)`. -/
theorem artinSchreierLeft_bijective
    (h : ∀ x : H1 (fpqc S) (Ga S), frobH1 S p hS x = x → x = 1) :
    Function.Bijective (artinSchreierLeft S p hS) :=
  cokerLift_bijective_of_ker_eq_bot _ (artinSchreierH1Map_ker S p hS) (wpH1_ker S p hS)
    ((Subgroup.eq_bot_iff_forall _).2 fun x hx ↦ h x ((mem_wpH1_ker_iff S p hS x).1 hx))

/-- XI.6.10: if `℘` is surjective on `Γ(S, 𝒪_S)`, then `H¹(S, ℤ/p) ≅ H¹(S, 𝒪_S)^F`. -/
theorem artinSchreierRight_bijective (h : ∀ a : Γ(S, ⊤), ∃ b, b - b ^ p = a) :
    Function.Bijective (artinSchreierRight S p hS) := by
  refine kerRestrict_bijective_of_surjective (artinSchreierConnecting_ker S p hS)
    (artinSchreierH1Map_ker S p hS) _ fun a ↦ ?_
  obtain ⟨b, hb⟩ := h (Multiplicative.toAdd a)
  exact ⟨Multiplicative.ofAdd b, by rw [wpΓ_apply, hb]; rfl⟩

end SGA.SGA1.ExposeXI
