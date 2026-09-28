/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedHomCogenerator
import SGA.SGA2.ExposeIV.SupportedHomOrthogonality

/-!
# Noetherian Hom duals imply actual Artinian modules

Actual Hom cogeneration separates an element from any submodule, without
finite-generation or support restrictions on the module. Orthogonality
therefore embeds its full submodule lattice into the opposite submodule
lattice of its dual. A noetherian dual gives the genuine descending-chain
condition, not only local Artinian behavior.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {H : ModuleCat.{u} R} (hH : SupportedDualizingModule H)

include hH

/-- Original Hom separates every element outside an arbitrary submodule. -/
theorem SupportedDualizingModule.homCoorthogonal_homOrthogonal
    (M : ModuleCat.{u} R) (N : Submodule R M) :
    homCoorthogonal H M (homOrthogonal H M N) = N := by
  apply le_antisymm
  · intro x hx
    by_contra hxn
    have hxq : N.mkQ x ≠ 0 := by
      intro h
      exact hxn ((Submodule.Quotient.mk_eq_zero N).mp h)
    obtain ⟨f, hf⟩ := hH.exists_hom_apply_ne_zero (ModuleCat.of R (M ⧸ N)) (N.mkQ x) hxq
    let g : M ⟶ H := ModuleCat.ofHom N.mkQ ≫ f
    have hg : g ∈ homOrthogonal H M N := by
      intro y hy
      change f (N.mkQ y) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hy]
      exact map_zero f.hom
    exact hf (hx g hg)
  · intro x hx f hf
    exact hf x hx

/-- Orthogonality detects the reverse inclusion of arbitrary original submodules. -/
theorem SupportedDualizingModule.homOrthogonal_le_iff
    (M : ModuleCat.{u} R) (N P : Submodule R M) :
    homOrthogonal H M N ≤ homOrthogonal H M P ↔ P ≤ N := by
  constructor
  · intro h x hx
    rw [← hH.homCoorthogonal_homOrthogonal M N]
    intro f hf
    exact h hf x hx
  · intro h f hf x hx
    exact hf x (h hx)

/-- The actual orthogonal gives an order embedding of full submodule lattices. -/
def SupportedDualizingModule.homOrthogonalOrderEmbedding (M : ModuleCat.{u} R) :
    Submodule R M ↪o (Submodule R ((moduleHomDual H).obj (op M)))ᵒᵈ where
  toFun N := OrderDual.toDual (homOrthogonal H M N)
  inj' := by
    intro N P h
    apply le_antisymm
    · exact (hH.homOrthogonal_le_iff M P N).mp (le_of_eq h.symm)
    · exact (hH.homOrthogonal_le_iff M N P).mp (le_of_eq h)
  map_rel_iff' := by
    intro N P
    exact hH.homOrthogonal_le_iff M P N

/-- A noetherian actual Hom dual forces the original module itself to
be Artinian, including all its submodules. -/
theorem SupportedDualizingModule.isArtinian_of_noetherian_dual
    (M : ModuleCat.{u} R) [IsNoetherian R ((moduleHomDual H).obj (op M))] :
    IsArtinian R M := by
  let e := hH.homOrthogonalOrderEmbedding M
  have : WellFoundedGT (Submodule R ((moduleHomDual H).obj (op M))) :=
    IsNoetherian.wellFoundedGT (inferInstance : IsNoetherian R ((moduleHomDual H).obj (op M)))
  apply (isArtinian_iff R M).mpr
  exact (InvImage.wf e wellFounded_lt).mono (fun _ _ h => e.strictMono h)

end SGA.SGA2.ExposeIV
