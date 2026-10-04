/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.Foundations.Smooth.GeometricallyReduced
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeXI.Geometry

/-!
# SGA 1, Exposé XI, §2: abelian varieties, their torsion points and Tate module

SGA defines an abelian variety over an algebraically closed field `k` as a group scheme over `k`
which is proper, smooth and connected. We record the elementary facts used in XI.2.1:

* `geometricallyIntegral_of_smooth_of_isAlgClosed`: a connected scheme smooth over an
  algebraically closed field is geometrically integral. It is geometrically reduced (smooth,
  `Smooth.geometricallyReduced`), and its base changes to fields are connected
  (`geometricallyConnected_of_isAlgClosed`) and smooth, hence integral
  (`ExposeX.isIntegral_of_isRegularScheme`);
* `isCommMonObj_of_smooth`: an abelian variety in SGA's sense is commutative. This is the case of
  `isCommMonObj_of_abelianVariety` (mathlib's
  `isCommMonObj_of_isProper_of_geometricallyIntegral`) given by the previous item;
* `torsionPoints G n`: the group `K_n` of `n`-torsion points `𝟙 ⟶ G` of a commutative group
  object `G`; for an abelian variety these are the `k`-points of the kernel of `n_A`;
* `tateModule G`: `T(G) = lim_n K_n`, the compatible families `(x_n)` with `x_{ns}ˢ = x_n`,
  topologized as a subspace of the product of the discrete groups `K_n`.
-/

universe u v w

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

namespace SGA.SGA1.ExposeXI

section Integral

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A connected scheme smooth over an algebraically closed field is geometrically integral
(EGA IV 4.5.21, 6.15.7, 17.5.7). Its base change to a field `K ⊇ k` is connected
(`geometricallyConnected_of_isAlgClosed`) and smooth over `K`, hence regular (II.5.3) and
integral (`ExposeX.isIntegral_of_isRegularScheme`). -/
theorem geometricallyIntegral_of_smooth_of_isAlgClosed {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] [ConnectedSpace X] : GeometricallyIntegral f := by
  have := geometricallyConnected_of_isAlgClosed f
  have : GeometricallyIrreducible f := ⟨fun K _ y Z fst snd h ↦ by
    have : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
    have : ConnectedSpace Z :=
      GeometricallyConnected.geometrically_connectedSpace (f := f) y fst snd h
    have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
    have : IsIntegral Z := ExposeX.isIntegral_of_isRegularScheme
      (ExposeII.isRegularLocalRing_stalk_of_smooth_field K snd)
    infer_instance⟩
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

/-- An abelian variety in SGA's sense (a group scheme proper, smooth and connected over an
algebraically closed field) is commutative: the case of `isCommMonObj_of_abelianVariety` (XI.2)
given by `geometricallyIntegral_of_smooth_of_isAlgClosed`. (SGA's XI.2 states that `π₁(A)` is
commutative; this is the commutativity of `A` itself, which SGA uses implicitly.) -/
theorem isCommMonObj_of_smooth (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom]
    [Smooth A.hom] [ConnectedSpace A.left] : IsCommMonObj A :=
  have := geometricallyIntegral_of_smooth_of_isAlgClosed A.hom
  isCommMonObj_of_abelianVariety A

end Integral

section Torsion

open MonObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- XI.2.1: the group `K_n` of `n`-torsion points of a commutative group object `G`, i.e. of the
points `x : 𝟙 ⟶ G` with `xⁿ = 1`. For an abelian variety `A` over an algebraically closed field
these are the `k`-points of the kernel `ₙA` of multiplication by `n`. -/
def torsionPoints (G : C) [GrpObj G] [IsCommMonObj G] (n : ℕ) : Subgroup (𝟙_ C ⟶ G) :=
  (powMonoidHom n : (𝟙_ C ⟶ G) →* (𝟙_ C ⟶ G)).ker

variable (G : C) [GrpObj G] [IsCommMonObj G]

lemma mem_torsionPoints {n : ℕ} {x : 𝟙_ C ⟶ G} : x ∈ torsionPoints G n ↔ x ^ n = 1 :=
  MonoidHom.mem_ker

/-- The groups `K_n` are discrete. -/
instance (n : ℕ) : TopologicalSpace (torsionPoints G n) := ⊥

instance (n : ℕ) : DiscreteTopology (torsionPoints G n) := ⟨rfl⟩

/-- XI.2.1: `T(G) = lim_n K_n`, the families `(x_n)_{n > 0}` of `n`-torsion points with
`x_{ns}ˢ = x_n` (for `m = ns`, `K_m → K_n` is multiplication by `s`). It is a subgroup of the
product of the discrete groups `K_n`, with the subspace topology. -/
def tateModule : Subgroup ((n : ℕ+) → torsionPoints G n) where
  carrier := {x | ∀ n s : ℕ+, ((x (n * s) : 𝟙_ C ⟶ G)) ^ (s : ℕ) = x n}
  mul_mem' := by
    intro a b ha hb n s
    simp only [Pi.mul_apply, Subgroup.coe_mul, mul_pow, ha n s, hb n s]
  one_mem' := by intro n s; simp
  inv_mem' := by
    intro a ha n s
    simp only [Pi.inv_apply, Subgroup.coe_inv, inv_pow, ha n s]

variable {G}

lemma pow_tateModule (x : tateModule G) (n s : ℕ+) :
    ((x.1 (n * s) : 𝟙_ C ⟶ G)) ^ (s : ℕ) = x.1 n :=
  x.2 n s

lemma pow_tateModule_apply (x : tateModule G) (n : ℕ+) : ((x.1 n : 𝟙_ C ⟶ G)) ^ (n : ℕ) = 1 :=
  (mem_torsionPoints G).mp (x.1 n).2

variable (G)

/-- If every `K_n` is finite, `T(G)` is compact: it is a closed subgroup of the product of the
finite discrete groups `K_n`. -/
theorem compactSpace_tateModule (h : ∀ n : ℕ+, Finite (torsionPoints G n)) :
    CompactSpace (tateModule G) := by
  have hcl : IsClosed (tateModule G : Set ((n : ℕ+) → torsionPoints G n)) := by
    have : (tateModule G : Set ((n : ℕ+) → torsionPoints G n)) = ⋂ p : ℕ+ × ℕ+,
        (fun x : (n : ℕ+) → torsionPoints G n ↦ (x (p.1 * p.2), x p.1)) ⁻¹'
          {q | (q.1 : 𝟙_ C ⟶ G) ^ (p.2 : ℕ) = q.2} := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq,
        Prod.forall]
      rfl
    rw [this]
    exact isClosed_iInter fun p ↦ (isClosed_discrete _).preimage
      ((continuous_apply _).prodMk (continuous_apply _))
  exact isCompact_iff_compactSpace.mp hcl.isCompact

variable {G}

/-- Given `a ∈ K_m` and a multiple `N > 0` of `m` such that `a` has an `N/m`-th root `b`, the
powers `x_n = b^{N/n}` (`n ∣ N`) form a family with `x_m = a` and `x_{ns}ˢ = x_n` whenever
`ns ∣ N`. -/
lemma exists_compatible_of_dvd (m : ℕ+) (a : torsionPoints G m) {N : ℕ} (hmN : (m : ℕ) ∣ N)
    {b : 𝟙_ C ⟶ G} (hb : b ^ (N / m) = a) :
    ∃ x : (n : ℕ+) → torsionPoints G n, x m = a ∧
      ∀ n s : ℕ+, (n : ℕ) * s ∣ N → ((x (n * s) : 𝟙_ C ⟶ G)) ^ (s : ℕ) = x n := by
  classical
  have hbN : b ^ N = 1 := by
    rw [← Nat.div_mul_cancel hmN, pow_mul, hb]
    exact (mem_torsionPoints G).mp a.2
  let x : (n : ℕ+) → torsionPoints G n := fun n ↦ if hn : (n : ℕ) ∣ N then
    ⟨b ^ (N / n), (mem_torsionPoints G).mpr (by rw [← pow_mul, Nat.div_mul_cancel hn, hbN])⟩
    else 1
  have hx (n : ℕ+) (hn : (n : ℕ) ∣ N) : (x n : 𝟙_ C ⟶ G) = b ^ (N / n) := by
    simp only [x, hn, ↓reduceDIte]
  refine ⟨x, Subtype.ext ((hx m hmN).trans hb), fun n s hns ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hns
  rw [hx _ (by rw [PNat.mul_coe]; exact Dvd.intro c rfl), hx _ (Dvd.intro _ (mul_assoc _ _ _).symm),
    ← pow_mul, PNat.mul_coe, Nat.mul_div_cancel_left _ (Nat.mul_pos n.pos s.pos), Nat.mul_assoc,
    Nat.mul_div_cancel_left _ n.pos, Nat.mul_comm]

/-- If every `K_n` is finite and `G(k)` is divisible, every `m`-torsion point is the `m`-th
component of an element of `T(G)` (a projective limit of nonempty finite sets). -/
theorem exists_tateModule_apply_eq (hfin : ∀ n : ℕ+, Finite (torsionPoints G n))
    (hdiv : ∀ n : ℕ, 0 < n → ∀ a : 𝟙_ C ⟶ G, ∃ b, b ^ n = a)
    (m : ℕ+) (a : torsionPoints G m) : ∃ x : tateModule G, x.1 m = a := by
  let P := (n : ℕ+) → torsionPoints G n
  let t : ℕ+ × ℕ+ → Set P := fun p ↦ (fun x : P ↦ (x (p.1 * p.2), x p.1)) ⁻¹'
    {q | (q.1 : 𝟙_ C ⟶ G) ^ (p.2 : ℕ) = q.2}
  have htc (p : ℕ+ × ℕ+) : IsClosed (t p) :=
    (isClosed_discrete _).preimage ((continuous_apply _).prodMk (continuous_apply _))
  let s : Set P := (fun x : P ↦ x m) ⁻¹' {a}
  have hs : IsCompact s := ((isClosed_discrete {a}).preimage (continuous_apply m)).isCompact
  have hst (u : Finset (ℕ+ × ℕ+)) : (s ∩ ⋂ i ∈ u, t i).Nonempty := by
    let N : ℕ := m * ∏ p ∈ u, ((p.1 : ℕ) * p.2)
    have hN : 0 < N := Nat.mul_pos m.pos (Finset.prod_pos fun p _ ↦ Nat.mul_pos p.1.pos p.2.pos)
    have hmN : (m : ℕ) ∣ N := Dvd.intro _ rfl
    obtain ⟨b, hb⟩ := hdiv (N / m) (Nat.div_pos (Nat.le_of_dvd hN hmN) m.pos) a
    obtain ⟨x, hxm, hx⟩ := exists_compatible_of_dvd m a hmN hb
    refine ⟨x, hxm, Set.mem_iInter₂.mpr fun p hp ↦ hx p.1 p.2 ?_⟩
    exact (Finset.dvd_prod_of_mem (fun p : ℕ+ × ℕ+ ↦ (p.1 : ℕ) * p.2) hp).mul_left _
  obtain ⟨x, hxs, hxt⟩ := hs.inter_iInter_nonempty t htc hst
  exact ⟨⟨x, fun n s' ↦ Set.mem_iInter.mp hxt (n, s')⟩, hxs⟩

end Torsion

end SGA.SGA1.ExposeXI
