/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeI.Permanence
import SGA.Foundations.CommAlg.PurityScheme
import SGA.Foundations.Dimension.StalkKrullDim

/-!
# Normal curves over a perfect field are smooth

The curve case of X.2.9 is X.2.6 for smooth projective curves; the reduction of X.2.9 to curves
(`SGA.SGA1.ExposeX.TopologicallyFiniteReduction`) produces *normal* curves. They are smooth:

* `IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one` (in
  `SGA.Foundations.Dimension.StalkKrullDim`; alias
  `isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one`): a noetherian integrally
  closed local domain of dimension `≤ 1` is a principal ideal ring (a field or a discrete
  valuation ring), hence regular; with `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim`
  (alias `ringKrullDim_stalk_le_topologicalKrullDim`) this applies to the local rings of a normal
  scheme of dimension `≤ 1`;
* `smooth_of_forall_isRegularLocalRing_stalk`: a scheme locally of finite type over a perfect
  field whose local rings are regular is smooth (the scheme form of the converse of II.5.4,
  `ExposeII.smooth_of_isRegularLocalRing`);
* `smooth_of_isNormalScheme_of_topologicalKrullDim_le_one`: a normal scheme of dimension `≤ 1`,
  locally of finite type over a perfect field, is smooth.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- A noetherian integrally closed local domain of Krull dimension `≤ 1` is a principal ideal
ring (moved to Foundations as
`IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one`; this name is kept for its
callers). -/
alias isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one :=
  _root_.IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one

/-- The scheme form of the converse of II.5.4 (`ExposeII.smooth_of_isRegularLocalRing`): a
scheme locally of finite type over a perfect field `k` whose local rings are all regular is
smooth over `k`. -/
theorem smooth_of_forall_isRegularLocalRing_stalk {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (h : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) : Smooth f := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth) (fun V : X.affineOpens ↦ V)
    (iSup_affineOpens_eq_top X) fun V ↦ ?_
  let φ := f.appLE ⊤ V.1 le_top
  let ψ : CommRingCat.of k ⟶ Γ(X, V.1) := (Scheme.ΓSpecIso (.of k)).inv ≫ φ
  rw [← RingHom.Smooth.propertyIsLocal.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of k)).inv φ]
  have hft : ψ.hom.FiniteType :=
    (RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of k)).inv φ).mpr
      (f.finiteType_appLE (isAffineOpen_top _) V.2 le_top)
  algebraize [ψ.hom]
  have : Algebra.Smooth k Γ(X, V.1) := ExposeII.smooth_of_isRegularLocalRing k fun Q _ ↦
    IsRegularLocalRing.of_ringEquiv (V.2.localizationAtPrimeEquivStalk ⟨Q, inferInstance⟩).symm
  exact this

/-- The local rings of a scheme have dimension at most the dimension of the scheme (moved to
Foundations as `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim`; this name is kept
for its callers). -/
alias ringKrullDim_stalk_le_topologicalKrullDim :=
  _root_.AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim

/-- A normal scheme of dimension `≤ 1`, locally of finite type over a perfect field `k` (e.g. a
normal curve over an algebraically closed field), is smooth over `k`: its local rings are fields
or discrete valuation rings, hence regular. -/
theorem smooth_of_isNormalScheme_of_topologicalKrullDim_le_one {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (hX : ExposeI.IsNormalScheme X) (hd : topologicalKrullDim X ≤ 1) : Smooth f := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  refine smooth_of_forall_isRegularLocalRing_stalk f fun x ↦ ?_
  obtain ⟨_, _⟩ := hX x
  have := IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one
    ((AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim x).trans hd)
  infer_instance

end SGA.SGA1.ExposeX
