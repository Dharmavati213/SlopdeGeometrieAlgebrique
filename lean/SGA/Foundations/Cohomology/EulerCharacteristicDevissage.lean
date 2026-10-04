/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.ProperFiniteness

/-!
# Comparison of additive functions of coherent modules

An additive function on coherent modules which vanishes on modules supported in proper closed
subsets takes the same value on two coherent modules related by a morphism which is bijective on
sections over a nonempty affine open (`CohomologyAux.additive_eq_of_bijective_app`; EGA III 3.2.1,
proof; Stacks Tag 01YF). The dévissage itself, for any property closed under extensions, is in
`SGA.Foundations.Cohomology.Devissage` (`CohomologyAux.prop_of_integral_step`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section Comparison

variable {Z : Scheme.{u}}

/-- **Comparison over an affine open** for additive functions (EGA III 3.2.1, proof): let `λ` be a
function on coherent `𝒪_Z`-modules, additive on short exact sequences and vanishing on modules
supported in proper closed subsets. If `φ : G ⟶ Q` is a morphism of coherent modules which is
bijective on sections over a nonempty affine open `U`, then `λ G = λ Q`: the kernel and cokernel
of `φ` are quasi-coherent with no sections over `U`, so they vanish off `Z ∖ U`
(`vanishesOff_kernel_factorThruImage`, `vanishesOff_cokernel`). -/
theorem additive_eq_of_bijective_app [IsLocallyNoetherian Z] (lam : Z.Modules → ℤ)
    (hadd : ∀ S : ShortComplex Z.Modules, S.ShortExact → S.X₁.IsCoherent → S.X₂.IsCoherent →
      S.X₃.IsCoherent → lam S.X₂ = lam S.X₁ + lam S.X₃)
    (IH : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
      VanishesOff N T' → lam N = 0)
    {G Q : Z.Modules} [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q) {U : Z.Opens}
    (hU : IsAffineOpen U) (hne : (U : Set Z).Nonempty) (hφ : Function.Bijective (φ.app U)) :
    lam G = lam Q := by
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hT : IsClosed (U : Set Z)ᶜ := U.2.isClosed_compl
  have hTne : (U : Set Z)ᶜ ≠ Set.univ := fun h ↦ by
    obtain ⟨z, hz⟩ := hne
    have : z ∈ (U : Set Z)ᶜ := h ▸ Set.mem_univ z
    exact this hz
  -- the two short exact sequences
  have hS₁ := shortExact_kernelSequence (Abelian.factorThruImage φ)
  have hS₂ := shortExact_kernelSequence (cokernel.π φ)
  have : (Abelian.image φ).IsQuasicoherent := isQuasicoherent_image φ
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₂.IsQuasicoherent :=
    ‹G.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₃.IsQuasicoherent :=
    ‹(Abelian.image φ).IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁.IsQuasicoherent :=
    isQuasicoherent_X₁_of_shortExact hS₁
  have hG : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₂.IsCoherent :=
    ‹G.IsCoherent›
  have hK : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁.IsCoherent :=
    isCoherent_X₁_of_shortExact hS₁
  have hI : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₃.IsCoherent :=
    isCoherent_X₃_of_shortExact hS₁
  have : (ShortComplex.kernelSequence (cokernel.π φ)).X₁.IsQuasicoherent :=
    ‹(Abelian.image φ).IsQuasicoherent›
  have hQ : (ShortComplex.kernelSequence (cokernel.π φ)).X₂.IsCoherent := ‹Q.IsCoherent›
  have hC : (ShortComplex.kernelSequence (cokernel.π φ)).X₃.IsCoherent :=
    isCoherent_X₃_of_shortExact hS₂
  have e₁ := hadd _ hS₁ hK hG hI
  have e₂ := hadd _ hS₂ hI hQ hC
  rw [IH _ hK _ hT hTne (vanishesOff_kernel_factorThruImage φ hU hφ.1), zero_add] at e₁
  rw [IH _ hC _ hT hTne (vanishesOff_cokernel φ hU hφ.2), add_zero] at e₂
  exact e₁.trans e₂.symm

end Comparison

end AlgebraicGeometry.CohomologyAux
