/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.MultiplicativeGroupCoveringCompositum
import SGA.SGA1.ExposeXIII.AbhyankarPurity

/-!
# Connected Galois coverings of `𝔾_m` of degree prime to `p` are Kummer coverings (XIII.2.12)

Let `k` be algebraically closed and `A` a connected Galois covering of `𝔾_{m,k}` of degree `d`
prime to the characteristic (a finite étale `k[T, T⁻¹]`-algebra which is a domain with at least
`d` automorphisms). Then its automorphism group is cyclic (`isCyclic_algEquiv_of_laurent`), and
`π₁^{p'}(𝔾_m) = Ẑ^{(p')}` (XIII.2.12 for `g = 0`, `n = 2`, `SGA.SGA1.ExposeXIII`). SGA deduces
this from Riemann's existence theorem; the proof here is algebraic:

* pull back along the Kummer covering `z ↦ z^d`: a composite `F` of `L = Frac A` and
  `K' = k(z)` is Galois over `K'` of degree dividing `d` (`MultiplicativeGroupCoveringCompositum`);
* by Abhyankar's lemma (X.3.6) at `T = 0`, and since `A` is unramified at the points `a ≠ 0`, the
  normalization of `k[z]` in `F` is finite étale over `k[z]` (`etale_integralClosure_compositum`);
* by the case `g = 0`, `n = 1` (`finrank_eq_one_of_le_card`, the lattice method of XI.1.1) this
  covering of `𝔸¹_z` is trivial, so `F = K'` and `L ⊆ K'`: `Gal(L/k(T))` is a quotient of
  `Gal(K'/k(T)) = μ_d`, hence cyclic.
-/

universe u

open Polynomial Module IsLocalRing
open scoped LaurentPolynomial KummerExtension

namespace SGA.SGA1.ExposeXI.MultiplicativeGroupCovering

section Abhyankar

open ExposeXIII

variable {k : Type u} [Field k] {d : ℕ} [NeZero d]

omit [NeZero d] in
lemma not_ringChar_dvd_of_natCast_ne_zero (hd : (d : k) ≠ 0) (a : k) :
    ¬ ringChar (ResidueField (localRingAt k a)) ∣ d := by
  rw [ringChar_residueField_localRing]
  intro h
  exact hd ((ringChar.spec k d).mpr h)

omit [NeZero d] in
lemma natCast_notMem_maximalIdeal (hd : (d : k) ≠ 0) (a : k) :
    (d : localRingAt k a) ∉ maximalIdeal (localRingAt k a) := by
  rw [← map_natCast (algebraMap k (localRingAt k a))]
  exact fun h ↦ (maximalIdeal.isMaximal _).ne_top
    (Ideal.eq_top_of_isUnit_mem _ h ((isUnit_iff_ne_zero.mpr hd).map _))

variable {L : Type u} [Field L] [Algebra (FractionRing k[X]) L]
  [FiniteDimensional (FractionRing k[X]) L] [IsGalois (FractionRing k[X]) L]

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the algebra structures of `k[T]_(T - a)` on the quotient of the tensor
-- product `K' ⊗ L` takes more than the default 20000 heartbeats
/-- Abhyankar's lemma for the Kummer pullback of a connected Galois covering of `𝔾_m` of degree
`d` prime to the characteristic, at the point `a` of `𝔸¹`: the normalization of `k[T]_(T - a)` in
the composite `F` is finite étale over its normalization in `K'`. At `a = 0` this uses that the
ramification indices of `L` divide `d = e(K')`; at `a ≠ 0` it uses that `L` is unramified (`hL`). -/
theorem etale_integralClosure_compositum (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
    (hd : (d : k) ≠ 0) (hdL : finrank (FractionRing k[X]) L = d) (a : k)
    [Algebra (localRingAt k a) L] [IsScalarTower (localRingAt k a) (FractionRing k[X]) L]
    (hL : a ≠ 0 → ∀ (Q : Ideal (integralClosure (localRingAt k a) L)) [Q.IsPrime],
      Q.ramificationIdx (localRingAt k a) = 1) :
    letI := integralClosure.algebraOfTower (localRingAt k a) (KummerField k d) (Compositum k d L)
    Module.Finite (integralClosure (localRingAt k a) (KummerField k d))
        (integralClosure (localRingAt k a) (Compositum k d L)) ∧
      Algebra.Etale (integralClosure (localRingAt k a) (KummerField k d))
        (integralClosure (localRingAt k a) (Compositum k d L)) := by
  have := isGalois_kummerField hζ
  have : FiniteDimensional (FractionRing k[X]) (KummerField k d) :=
    FiniteDimensional.of_finrank_pos (by rw [finrank_kummerField hζ]; exact NeZero.pos d)
  have := isSeparable_compositum hζ (L := L)
  have hLt : IsTameExtension (localRingAt k a) (K := FractionRing k[X]) L :=
    isTameExtension_of_isGalois _ L (hdL ▸ not_ringChar_dvd_of_natCast_ne_zero hd a)
  have hK't : IsTameExtension (localRingAt k a) (K := FractionRing k[X]) (KummerField k d) :=
    isTameExtension_of_isGalois _ _ ((finrank_kummerField hζ).symm ▸
      not_ringChar_dvd_of_natCast_ne_zero hd a)
  refine etale_integralClosure_of_dvd (localRingAt k a) (toCompositum k d L)
    (adjoin_compositum k d L) hLt hK't fun Q Q' hQ hQm hQ' hQ'm ↦ ?_
  by_cases ha : a = 0
  · subst ha
    have := ramificationIdx_integralClosure_adjoinRoot (localRingAt k 0) (K := FractionRing k[X])
      (uniformizer 0) d (natCast_notMem_maximalIdeal hd 0) Q'
    rw [this.1, ← hdL]
    exact ramificationIdx_dvd_finrank _ L Q
  · rw [hL ha Q]
    exact one_dvd _

end Abhyankar

section ZLine

variable (k : Type u) [Field k] (d : ℕ) [NeZero d]

/-- The coordinate ring `k[z]` of the line `𝔸¹_z` mapping to `𝔸¹_T` by `T = z^d`: a copy of
`k[X]`, so that its algebra structures (`T ↦ z^d`, and `z ↦ ⁿ√T` in `K'`) do not interfere with
those of `k[T]`. -/
@[nolint unusedArguments]
def ZLine (k : Type u) [Field k] (_d : ℕ) : Type u := k[X]

noncomputable instance : CommRing (ZLine k d) := inferInstanceAs (CommRing k[X])
instance : IsDomain (ZLine k d) := inferInstanceAs (IsDomain k[X])
instance : IsPrincipalIdealRing (ZLine k d) := inferInstanceAs (IsPrincipalIdealRing k[X])
noncomputable instance : Algebra k (ZLine k d) := inferInstanceAs (Algebra k k[X])

/-- `k[T] → k[z]`, `T ↦ z^d`. -/
noncomputable instance : Algebra k[X] (ZLine k d) :=
  (expand k d : k[X] →ₐ[k] k[X]).toRingHom.toAlgebra

/-- `k[z] → K' = k(T)[z]/(z^d - T)`, `z ↦ z`. -/
noncomputable instance : Algebra (ZLine k d) (KummerField k d) :=
  (Polynomial.eval₂RingHom (algebraMap k (KummerField k d)) (AdjoinRoot.root _) :
    k[X] →+* KummerField k d).toAlgebra

variable {k d}

lemma coordT_eq : coordT k = algebraMap k[X] (FractionRing k[X]) X := by
  rw [coordT, uniformizer, ← IsScalarTower.algebraMap_apply, map_zero, sub_zero]

lemma algebraMap_zLine_apply (g : ZLine k d) :
    algebraMap (ZLine k d) (KummerField k d) g =
      Polynomial.eval₂ (algebraMap k (KummerField k d)) (AdjoinRoot.root _) (g : k[X]) := rfl

lemma root_pow_kummer :
    (AdjoinRoot.root (X ^ d - C (coordT k))) ^ d =
      algebraMap k[X] (KummerField k d) X := by
  have h := AdjoinRoot.eval₂_root (X ^ d - C (coordT k))
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  rw [h, IsScalarTower.algebraMap_apply k[X] (FractionRing k[X]) (KummerField k d), ← coordT_eq]
  rfl

instance isScalarTower_zLine :
    IsScalarTower k[X] (ZLine k d) (KummerField k d) := by
  refine .of_algebraMap_eq' (Polynomial.ringHom_ext (fun c ↦ ?_) ?_)
  · change _ = Polynomial.eval₂ (algebraMap k (KummerField k d)) (AdjoinRoot.root _)
      (expand k d (C c))
    rw [expand_C, eval₂_C, IsScalarTower.algebraMap_apply k k[X] (KummerField k d)]
    rfl
  · change _ = Polynomial.eval₂ (algebraMap k (KummerField k d)) (AdjoinRoot.root _)
      (expand k d X)
    rw [expand_X, eval₂_X_pow, root_pow_kummer]

/-- `k[z] → K'` is injective: if `g(z) = 0` in `K' = k(T)[z]/(z^d - T)` then `z^d - T` divides
`g` in `k[T][z]`, and substituting `T = z^d` gives `g = 0`. -/
lemma injective_algebraMap_zLine :
    Function.Injective (algebraMap (ZLine k d) (KummerField k d)) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  let g' : k[X] := g
  let ι := algebraMap k[X] (FractionRing k[X])
  have h1 : (X ^ d - C (coordT k)) ∣ g'.map (algebraMap k (FractionRing k[X])) := by
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map,
      ← IsScalarTower.algebraMap_eq]
    exact hg
  let P : k[X][X] := X ^ d - C X
  have hP : P.Monic := monic_X_pow_sub_C _ (NeZero.ne d)
  let G : k[X][X] := g'.map C
  have hPmap : P.map ι = X ^ d - C (coordT k) := by
    simp [P, coordT_eq, ι]
  have hGmap : G.map ι = g'.map (algebraMap k (FractionRing k[X])) := by
    rw [Polynomial.map_map]
    rfl
  have h2 : G %ₘ P = 0 := by
    apply Polynomial.map_injective ι (IsFractionRing.injective k[X] (FractionRing k[X]))
    rw [Polynomial.map_modByMonic _ hP, Polynomial.map_zero, hPmap, hGmap,
      Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow_sub_C _ (NeZero.ne d))]
    exact h1
  obtain ⟨Q, hQ⟩ := (Polynomial.modByMonic_eq_zero_iff_dvd hP).mp h2
  have := congrArg (Polynomial.eval₂ (expand k d : k[X] →ₐ[k] k[X]).toRingHom X) hQ
  simp only [G, P, eval₂_map, eval₂_mul, eval₂_sub, eval₂_X_pow, eval₂_C,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, expand_X, sub_self, zero_mul] at this
  have hg' :
      g' = Polynomial.eval₂ (((expand k d : k[X] →ₐ[k] k[X]) : k[X] →+* k[X]).comp C) X g' := by
    rw [show ((expand k d : k[X] →ₐ[k] k[X]) : k[X] →+* k[X]).comp C = C from
      RingHom.ext fun c ↦ expand_C d c, eval₂_C_X]
  change g' = 0
  rw [hg']
  exact this

/-- The coordinate `z` of `𝔸¹_z`. -/
noncomputable def zCoord : ZLine k d := (X : k[X])

lemma algebraMap_zCoord : algebraMap (ZLine k d) (KummerField k d) zCoord = AdjoinRoot.root _ :=
  eval₂_X _ _

omit [NeZero d] in
lemma algebraMap_X_zLine : algebraMap k[X] (ZLine k d) X = zCoord ^ d := by
  change expand k d X = (X : k[X]) ^ d
  rw [expand_X]

omit [NeZero d] in
lemma algebraMap_C_zLine (c : k) : algebraMap k[X] (ZLine k d) (C c) = algebraMap k (ZLine k d) c :=
  expand_C d c

/-- `K' = k(T)[z]/(z^d - T)` is the fraction field `k(z)` of `k[z]`. -/
instance isFractionRing_zLine : IsFractionRing (ZLine k d) (KummerField k d) where
  map_units y := isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ injective_algebraMap_zLine).mpr
    (nonZeroDivisors.ne_zero y.2))
  surj x := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨b, hb, hbp⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors k[X]) (S := FractionRing k[X]) p
    set q := IsLocalization.integerNormalization (nonZeroDivisors k[X]) p
    let num : ZLine k d := Polynomial.eval₂ (algebraMap k[X] (ZLine k d)) zCoord q
    let den : ZLine k d := algebraMap k[X] (ZLine k d) b
    have hden : den ∈ nonZeroDivisors (ZLine k d) := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      change expand k d b ≠ 0
      rw [Ne, ← map_zero (expand k d), (expand_injective (NeZero.pos d)).eq_iff]
      exact nonZeroDivisors.ne_zero hb
    refine ⟨⟨num, ⟨den, hden⟩⟩, ?_⟩
    change AdjoinRoot.mk _ p * algebraMap (ZLine k d) (KummerField k d) den =
      algebraMap (ZLine k d) (KummerField k d) num
    have h1 : algebraMap (ZLine k d) (KummerField k d) num =
        Polynomial.eval₂ (algebraMap k[X] (KummerField k d)) (AdjoinRoot.root _) q := by
      rw [Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq, algebraMap_zCoord]
    have h2 : algebraMap (ZLine k d) (KummerField k d) den =
        AdjoinRoot.of _ (algebraMap k[X] (FractionRing k[X]) b) := by
      change algebraMap (ZLine k d) (KummerField k d) (algebraMap k[X] (ZLine k d) b) = _
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    rw [h1, h2, mul_comm, ← AdjoinRoot.mk_C, ← map_mul, ← smul_eq_C_mul, algebraMap_smul,
      ← hbp, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map]
    rfl
  exists_of_eq h := ⟨1, by rw [injective_algebraMap_zLine h]⟩

/-- `k[z]` is integral over `k[T]` (`z^d = T`). -/
instance isIntegral_zLine : Algebra.IsIntegral k[X] (ZLine k d) := by
  have hz : IsIntegral k[X] (zCoord : ZLine k d) := by
    refine ⟨X ^ d - C X, monic_X_pow_sub_C _ (NeZero.ne d), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, algebraMap_X_zLine, sub_self]
  have hadj : Algebra.adjoin k[X] {(zCoord : ZLine k d)} = ⊤ := by
    refine eq_top_iff.mpr fun g _ ↦ ?_
    let g' : k[X] := g
    have : g = Polynomial.aeval (zCoord : ZLine k d) (g'.map C) := by
      rw [aeval_def, eval₂_map]
      have hc : (algebraMap k[X] (ZLine k d)).comp C = algebraMap k (ZLine k d) :=
        RingHom.ext fun c ↦ algebraMap_C_zLine c
      rw [hc]
      exact (eval₂_C_X (p := g')).symm
    rw [this]
    exact Polynomial.aeval_mem_adjoin_singleton k[X] _
  have hfg := adjoin_le_integralClosure hz
  rw [hadj] at hfg
  exact ⟨fun g ↦ hfg (Algebra.mem_top (x := g))⟩

/-- The submonoid `{f(z^d) : f(a) ≠ 0}` of `k[z]`. -/
noncomputable abbrev zSubmonoid (a : k) : Submonoid (ZLine k d) :=
  (Ideal.span {X - C a} : Ideal k[X]).primeCompl.map (algebraMap k[X] (ZLine k d))

/-- `k[z]` lands in the normalization of `k[T]_(T - a)` in `K'`. -/
noncomputable instance algebraZLineIntegralClosure (a : k) :
    Algebra (ZLine k d) (integralClosure (localRingAt k a) (KummerField k d)) :=
  (RingHom.codRestrict (algebraMap (ZLine k d) (KummerField k d))
    (integralClosure (localRingAt k a) (KummerField k d)).toSubring fun g ↦ by
      have hg : IsIntegral k[X] (algebraMap (ZLine k d) (KummerField k d) g) :=
        (Algebra.IsIntegral.isIntegral g).map (IsScalarTower.toAlgHom k[X] (ZLine k d) _)
      exact hg.tower_top (A := localRingAt k a)).toAlgebra

instance (a : k) : IsScalarTower (ZLine k d)
    (integralClosure (localRingAt k a) (KummerField k d)) (KummerField k d) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The normalization of `k[T]_(T - a)` in `K' = k(z)` is the localization of `k[z]` at the
`f(z^d)` with `f(a) ≠ 0`. -/
instance isLocalization_integralClosure_localRing (a : k) :
    IsLocalization (zSubmonoid (d := d) a)
      (integralClosure (localRingAt k a) (KummerField k d)) where
  map_units := by
    rintro ⟨_, m, hm, rfl⟩
    have hu : IsUnit (algebraMap k[X] (localRingAt k a) m) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (localRingAt k a) _ m).mpr hm
    have : algebraMap (ZLine k d) (integralClosure (localRingAt k a) (KummerField k d))
        (algebraMap k[X] (ZLine k d) m) =
        algebraMap (localRingAt k a) _ (algebraMap k[X] (localRingAt k a) m) := by
      apply Subtype.ext
      change algebraMap (ZLine k d) (KummerField k d) (algebraMap k[X] (ZLine k d) m) =
        algebraMap (localRingAt k a) (KummerField k d) (algebraMap k[X] (localRingAt k a) m)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact hu.map _
  surj := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Ideal.span {X - C a} : Ideal k[X]).primeCompl x hx
    obtain ⟨g, hg⟩ := (IsIntegralClosure.isIntegral_iff (A := ZLine k d)).mp hmx
    refine ⟨⟨g, ⟨_, m, hm, rfl⟩⟩, Subtype.ext ?_⟩
    change x * algebraMap (ZLine k d) (KummerField k d) (algebraMap k[X] (ZLine k d) m) =
      algebraMap (ZLine k d) (KummerField k d) g
    rw [hg, ← IsScalarTower.algebraMap_apply, Submonoid.smul_def, Algebra.smul_def, mul_comm]
  exists_of_eq {g₁ g₂} h := by
    refine ⟨1, ?_⟩
    rw [injective_algebraMap_zLine (congrArg Subtype.val h)]

end ZLine

section Global

variable {k : Type u} [Field k] {d : ℕ} [NeZero d] {L : Type u} [Field L]
  [Algebra (FractionRing k[X]) L] [FiniteDimensional (FractionRing k[X]) L]
  [IsGalois (FractionRing k[X]) L]

/-- `k[T]_(T - a)` acting on a field over `k(T)`. -/
noncomputable abbrev algebraLocalRing (a : k) (E : Type*) [Field E]
    [Algebra (FractionRing k[X]) E] : Algebra (localRingAt k a) E :=
  ((algebraMap (FractionRing k[X]) E).comp
    (algebraMap (localRingAt k a) (FractionRing k[X]))).toAlgebra

set_option maxHeartbeats 1000000 in
-- the identification of the normalizations of `k[T]_(T - a)` and of its normalization in `K'`
-- (the equivalence `Z`) unfolds the algebra structures on the quotient of `K' ⊗ L`
set_option synthInstance.maxHeartbeats 200000 in
-- instance search for these algebra structures takes more than 20000 heartbeats
/-- The normalization `Ã` of `k[z]` in the composite `F` is étale over `k[z]` at every prime `q`
avoiding the `f(z^d)`, `f(a) ≠ 0`: localize at `T = a` and apply Abhyankar's lemma
(`etale_integralClosure_compositum`). -/
theorem isEtaleAt_integralClosure_zLine (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
    (hd : (d : k) ≠ 0) (hdL : finrank (FractionRing k[X]) L = d)
    (hL : ∀ a : k, a ≠ 0 → letI := algebraLocalRing a L
      ∀ (Q : Ideal (integralClosure (localRingAt k a) L)) [Q.IsPrime],
        Q.ramificationIdx (localRingAt k a) = 1)
    (a : k) (q : Ideal (integralClosure (ZLine k d) (Compositum k d L))) [q.IsPrime]
    (hq : ∀ s ∈ zSubmonoid (d := d) a,
      algebraMap (ZLine k d) (integralClosure (ZLine k d) (Compositum k d L)) s ∉ q) :
    Algebra.IsEtaleAt (ZLine k d) q := by
  let := algebraLocalRing a L
  have : IsScalarTower (localRingAt k a) (FractionRing k[X]) L := .of_algebraMap_eq' rfl
  obtain ⟨-, het⟩ := etale_integralClosure_compositum hζ hd hdL a (hL a)
  set F := Compositum k d L
  set S' := integralClosure (localRingAt k a) (KummerField k d)
  have : IsScalarTower (ZLine k d) S' F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid F (zSubmonoid (d := d) a)) F := by
    refine IsLocalization.self ?_
    rintro _ ⟨s, ⟨m, hm, rfl⟩, rfl⟩
    refine (isUnit_iff_ne_zero.mpr ?_)
    rw [IsScalarTower.algebraMap_apply (ZLine k d) (KummerField k d) F]
    refine (map_ne_zero_iff _ (algebraMap (KummerField k d) F).injective).mpr ?_
    refine (map_ne_zero_iff _ injective_algebraMap_zLine).mpr ?_
    change expand k d m ≠ 0
    rw [Ne, ← map_zero (expand k d), (expand_injective (NeZero.pos d)).eq_iff]
    rintro rfl
    exact hm (zero_mem _)
  -- the normalizations of `k[T]_(T - a)` and of `S'` in `F` agree
  let := integralClosure.algebraOfTower (localRingAt k a) (KummerField k d) F
  have : IsScalarTower (localRingAt k a) S' F := .of_algebraMap_eq fun _ ↦ rfl
  let Z : integralClosure S' F ≃ₐ[S'] integralClosure (localRingAt k a) F :=
    { toFun x := ⟨x.1, isIntegral_trans (A := S') _ x.2⟩
      invFun y := ⟨y.1, y.2.tower_top⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl
      commutes' _ := Subtype.ext rfl }
  have : Algebra.FormallyEtale S' (integralClosure S' F) := Algebra.FormallyEtale.of_equiv Z.symm
  exact ExposeXIII.isEtaleAt_integralClosure_of_isLocalization (S := ZLine k d) (S' := S')
    (C := F) (C' := F) (zSubmonoid (d := d) a) q hq

/-- A prime of `k[T]` (`k` algebraically closed) is contained in some `(T - a)`. -/
lemma exists_le_span_X_sub_C [IsAlgClosed k] (p : Ideal k[X]) [p.IsPrime] :
    ∃ a : k, p ≤ Ideal.span {X - C a} := by
  by_cases hp : p = ⊥
  · exact ⟨0, hp ▸ bot_le⟩
  obtain ⟨f, rfl⟩ : ∃ f : k[X], p = Ideal.span {f} :=
    ⟨Submodule.IsPrincipal.generator p, (Submodule.IsPrincipal.span_singleton_generator p).symm⟩
  have hf0 : f ≠ 0 := fun h ↦ hp (by rw [h, Ideal.span_singleton_eq_bot])
  have hfu : ¬ IsUnit f := fun h ↦ (‹(Ideal.span {f}).IsPrime›).ne_top
    (Ideal.span_singleton_eq_top.mpr h)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f (degree_pos_of_ne_zero_of_nonunit hf0 hfu).ne'
  exact ⟨a, Ideal.span_singleton_le_span_singleton.mpr (dvd_iff_isRoot.mpr ha)⟩

/-- `Ã`, the normalization of `k[z]` in the composite `F`, is finite étale over `k[z]`. -/
theorem etale_integralClosure_zLine [IsAlgClosed k]
    (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
    (hd : (d : k) ≠ 0) (hdL : finrank (FractionRing k[X]) L = d)
    (hL : ∀ a : k, a ≠ 0 → letI := algebraLocalRing a L
      ∀ (Q : Ideal (integralClosure (localRingAt k a) L)) [Q.IsPrime],
        Q.ramificationIdx (localRingAt k a) = 1) :
    Module.Finite (ZLine k d) (integralClosure (ZLine k d) (Compositum k d L)) ∧
      Algebra.Etale (ZLine k d) (integralClosure (ZLine k d) (Compositum k d L)) := by
  set F := Compositum k d L
  have := isGalois_compositum hζ (L := L)
  have : FiniteDimensional (KummerField k d) F :=
    Module.Finite.right (FractionRing k[X]) (KummerField k d) F
  have hfin : Module.Finite (ZLine k d) (integralClosure (ZLine k d) F) :=
    IsIntegralClosure.finite (ZLine k d) (KummerField k d) F (integralClosure (ZLine k d) F)
  refine ⟨hfin, ?_⟩
  have : Algebra.FinitePresentation (ZLine k d) (integralClosure (ZLine k d) F) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine Algebra.etaleLocus_eq_univ_iff_etale.mp (Set.eq_univ_of_forall fun q ↦ ?_)
  let φ : k[X] →+* integralClosure (ZLine k d) F :=
    (algebraMap (ZLine k d) _).comp (algebraMap k[X] (ZLine k d))
  obtain ⟨a, ha⟩ := exists_le_span_X_sub_C (q.asIdeal.comap φ)
  refine isEtaleAt_integralClosure_zLine hζ hd hdL hL a q.asIdeal ?_
  rintro _ ⟨m, hm, rfl⟩ hmq
  exact hm (ha hmq)

/-- The normalization `Ã` of `k[z]` in `F` has finitely many automorphisms, at least `[F : K']`
of them (those of `Gal(F/K')`), and rank `[F : K']` over `k[z]`. -/
theorem finrank_le_card_algEquiv_integralClosure_zLine
    (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty) :
    Finite (integralClosure (ZLine k d) (Compositum k d L) ≃ₐ[ZLine k d]
        integralClosure (ZLine k d) (Compositum k d L)) ∧
      finrank (ZLine k d) (integralClosure (ZLine k d) (Compositum k d L)) =
        finrank (KummerField k d) (Compositum k d L) ∧
      finrank (KummerField k d) (Compositum k d L) ≤
        Nat.card (integralClosure (ZLine k d) (Compositum k d L) ≃ₐ[ZLine k d]
          integralClosure (ZLine k d) (Compositum k d L)) := by
  have := isGalois_compositum hζ (L := L)
  have : FiniteDimensional (KummerField k d) (Compositum k d L) :=
    Module.Finite.right (FractionRing k[X]) (KummerField k d) (Compositum k d L)
  have : FaithfulSMul (ZLine k d) (Compositum k d L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      rw [IsScalarTower.algebraMap_eq (ZLine k d) (KummerField k d) (Compositum k d L)]
      exact (algebraMap (KummerField k d) (Compositum k d L)).injective.comp
        injective_algebraMap_zLine)
  have : Module.IsTorsionFree (ZLine k d) (Compositum k d L) :=
    .trans_faithfulSMul (ZLine k d) (Compositum k d L) (Compositum k d L)
  have : IsFractionRing (integralClosure (ZLine k d) (Compositum k d L)) (Compositum k d L) :=
    IsIntegralClosure.isFractionRing_of_finite_extension (ZLine k d) (KummerField k d) _ _
  have hloc := IsIntegralClosure.isLocalization (ZLine k d) (KummerField k d) (Compositum k d L)
    (integralClosure (ZLine k d) (Compositum k d L))
  -- automorphisms of `Ã` extend to `F`
  have hfin : Finite (integralClosure (ZLine k d) (Compositum k d L) ≃ₐ[ZLine k d]
      integralClosure (ZLine k d) (Compositum k d L)) :=
    Finite.of_injective _ (IsFractionRing.fieldEquivOfAlgEquivHom_injective (ZLine k d)
      (integralClosure (ZLine k d) (Compositum k d L)) (KummerField k d) (Compositum k d L))
  refine ⟨hfin, IsIntegralClosure.rank (ZLine k d) (KummerField k d) _ _, ?_⟩
  -- elements of `Gal(F/K')` restrict to `Ã`
  let ρ : Gal(Compositum k d L/KummerField k d) → (integralClosure (ZLine k d) (Compositum k d L)
      ≃ₐ[ZLine k d] integralClosure (ZLine k d) (Compositum k d L)) :=
    fun σ ↦ (σ.restrictScalars (ZLine k d)).mapIntegralClosure
  have hρ : Function.Injective ρ := by
    intro σ τ h
    have h' : (σ : Compositum k d L →+* Compositum k d L).comp
        (algebraMap (integralClosure (ZLine k d) (Compositum k d L)) (Compositum k d L)) =
        (τ : Compositum k d L →+* Compositum k d L).comp
        (algebraMap (integralClosure (ZLine k d) (Compositum k d L)) (Compositum k d L)) := by
      ext x
      exact congrArg Subtype.val (AlgEquiv.congr_fun h x)
    have h'' := IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid
      (integralClosure (ZLine k d) (Compositum k d L)) (nonZeroDivisors (ZLine k d))) h'
    exact AlgEquiv.ext fun x ↦ RingHom.congr_fun h'' x
  rw [← IsGalois.card_aut_eq_finrank]
  exact Nat.card_le_card_of_injective ρ hρ

/-- The composite `F` is `K'`: the normalization `Ã` of `k[z]` in `F` is a connected Galois
étale covering of `𝔸¹_z` of degree `[F : K']` prime to the characteristic, hence trivial
(`finrank_eq_one_of_le_card`, XIII.2.12 for `g = 0`, `n = 1`). -/
theorem finrank_compositum_eq_one [IsAlgClosed k]
    (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
    (hd : (d : k) ≠ 0) (hdL : finrank (FractionRing k[X]) L = d)
    (hL : ∀ a : k, a ≠ 0 → letI := algebraLocalRing a L
      ∀ (Q : Ideal (integralClosure (localRingAt k a) L)) [Q.IsPrime],
        Q.ramificationIdx (localRingAt k a) = 1) :
    finrank (KummerField k d) (Compositum k d L) = 1 := by
  obtain ⟨hfin, het⟩ := etale_integralClosure_zLine (L := L) hζ hd hdL hL
  obtain ⟨hAut, hrank, hle⟩ := finrank_le_card_algEquiv_integralClosure_zLine (L := L) hζ
  have hdvd := finrank_compositum_dvd hζ (L := L)
  rw [hdL] at hdvd
  have hFp : (finrank (KummerField k d) (Compositum k d L) : k) ≠ 0 := by
    obtain ⟨c, hc⟩ := hdvd
    intro h
    exact hd (by rw [hc, Nat.cast_mul, h, zero_mul])
  rw [← hrank]
  let : Algebra k[X] (integralClosure (ZLine k d) (Compositum k d L)) :=
    (inferInstance : Algebra (ZLine k d) (integralClosure (ZLine k d) (Compositum k d L)))
  have : Algebra.Etale k[X] (integralClosure (ZLine k d) (Compositum k d L)) := het
  have : Module.Finite k[X] (integralClosure (ZLine k d) (Compositum k d L)) := hfin
  have : Finite (integralClosure (ZLine k d) (Compositum k d L) ≃ₐ[k[X]]
      integralClosure (ZLine k d) (Compositum k d L)) := hAut
  exact finrank_eq_one_of_le_card (k := k) (A := integralClosure (ZLine k d) (Compositum k d L))
    (hrank ▸ hle) (hrank ▸ hFp)

omit [IsGalois (FractionRing k[X]) L] in
/-- If the composite `F` is `K'`, then `L ≅ K'` over `k(T)`, so every Galois group of `L/k(T)` is
a quotient of `Gal(K'/k(T)) ≅ μ_d`, hence cyclic. -/
theorem isCyclic_of_finrank_compositum_eq_one
    (hζ : (primitiveRoots d (FractionRing k[X])).Nonempty)
    (hdL : finrank (FractionRing k[X]) L = d)
    (hF1 : finrank (KummerField k d) (Compositum k d L) = 1)
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G L]
    [IsGaloisGroup G (FractionRing k[X]) L] : IsCyclic G := by
  have hbij : Function.Bijective (algebraMap (KummerField k d) (Compositum k d L)) :=
    bijective_algebraMap_of_finrank_eq_one hF1
  let e₁ : KummerField k d ≃ₐ[FractionRing k[X]] Compositum k d L :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom _ _ _) hbij
  let g : L →ₐ[FractionRing k[X]] KummerField k d :=
    e₁.symm.toAlgHom.comp (toCompositum k d L)
  have hdim : finrank (FractionRing k[X]) L =
      finrank (FractionRing k[X]) (KummerField k d) := by
    rw [hdL, finrank_kummerField hζ]
  have hgbij : Function.Bijective g :=
    ⟨g.injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := g.toLinearMap)).mp g.injective⟩
  let e₂ : L ≃ₐ[FractionRing k[X]] KummerField k d := AlgEquiv.ofBijective g hgbij
  have := isCyclic_kummerField hζ
  have : IsCyclic Gal(L/FractionRing k[X]) :=
    isCyclic_of_surjective (e₂.autCongr).symm.toMonoidHom (e₂.autCongr).symm.surjective
  exact isCyclic_of_surjective
    (IsGaloisGroup.mulEquivAlgEquiv G (FractionRing k[X]) L).symm.toMonoidHom
    (IsGaloisGroup.mulEquivAlgEquiv G (FractionRing k[X]) L).symm.surjective

end Global

section Main

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- XIII.2.12 for `g = 0`, `n = 2`, algebraic form: let `k` be algebraically closed and `A` a
finite étale `k[T, T⁻¹]`-algebra which is a domain, with at least `[A : k[T, T⁻¹]]` automorphisms
(a connected Galois covering of `𝔾_{m,k}`), of degree prime to the characteristic. Then its
automorphism group is cyclic: the covering is a Kummer covering `z ↦ z^d`. -/
theorem isCyclic_algEquiv_of_laurent {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A]
    [IsDomain A] [Algebra k[T;T⁻¹] A] [Algebra.Etale k[T;T⁻¹] A] [Module.Finite k[T;T⁻¹] A]
    [Finite (A ≃ₐ[k[T;T⁻¹]] A)] (hG : finrank k[T;T⁻¹] A ≤ Nat.card (A ≃ₐ[k[T;T⁻¹]] A))
    (hp : (finrank k[T;T⁻¹] A : k) ≠ 0) : IsCyclic (A ≃ₐ[k[T;T⁻¹]] A) := by
  set d := finrank k[T;T⁻¹] A
  have hd0 : d ≠ 0 := fun h ↦ hp (by rw [h, Nat.cast_zero])
  have : NeZero d := ⟨hd0⟩
  let : Algebra k[X] A := ((algebraMap k[T;T⁻¹] A).comp (algebraMap k[X] k[T;T⁻¹])).toAlgebra
  have : IsScalarTower k[X] k[T;T⁻¹] A := .of_algebraMap_eq' rfl
  have : FaithfulSMul k[T;T⁻¹] A := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ((injective_iff_map_eq_zero _).mpr
      fun r hr ↦ ?_)
    rw [Algebra.algebraMap_eq_smul_one] at hr
    exact (smul_eq_zero.mp hr).resolve_right one_ne_zero
  let := IsFractionRing.mulSemiringAction (A ≃ₐ[k[T;T⁻¹]] A) A (FractionRing A)
  have hGal := isGaloisGroup_algEquiv (k := k) A hG
  have : IsGalois (FractionRing k[X]) (FractionRing A) :=
    IsGaloisGroup.isGalois (A ≃ₐ[k[T;T⁻¹]] A) _ (FractionRing A)
  have := finiteDimensional_fractionRing (k := k) A
  have hdL : finrank (FractionRing k[X]) (FractionRing A) = d := finrank_fractionRing (k := k) A
  have hζ := primitiveRoots_nonempty (k := k) hp
  -- the covering is unramified over the points `a ≠ 0`
  have hL : ∀ a : k, a ≠ 0 → letI := algebraLocalRing a (FractionRing A)
      ∀ (Q : Ideal (integralClosure (localRingAt k a) (FractionRing A))) [Q.IsPrime],
        Q.ramificationIdx (localRingAt k a) = 1 := by
    intro a ha
    let := algebraLocalRing a (FractionRing A)
    have : IsScalarTower (localRingAt k a) (FractionRing k[X]) (FractionRing A) :=
      .of_algebraMap_eq' rfl
    intro Q _
    exact ramificationIdx_eq_one_of_ne_zero A a ha Q
  -- the Kummer pullback is trivial: `F = K'`
  have hF1 := finrank_compositum_eq_one (L := FractionRing A) hζ hp hdL hL
  -- so `L` embeds in `K'`, and `Gal(L/k(T))` is a quotient of `Gal(K'/k(T)) = μ_d`
  exact isCyclic_of_finrank_compositum_eq_one hζ hdL hF1 (A ≃ₐ[k[T;T⁻¹]] A)

end Main

end SGA.SGA1.ExposeXI.MultiplicativeGroupCovering
