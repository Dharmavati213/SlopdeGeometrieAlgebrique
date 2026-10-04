/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.ConstantFamily
import SGA.SGA1.ExposeXIII.ProLShortExact

/-!
# SGA 1, Exposé XIII, 4.3–4.4 over a regular base: group theory and Galois categories

The second part of XIII.4.4 over a regular base ("route B",
`ProperSmoothHomotopyExactSequenceRegularStatement`) replaces SGA's argument through `R¹f_*`
(XIII.1.16, XIII.4.3.1) by the core of X.3.8 at the codimension-one points of the base and purity.
This file contains the parts of that argument that do not involve the geometry of `X`.

* `comap_primeKernel_le_proLKernel_of_forall_exists`: the criterion of the proof of XIII.4.3
  (V.6.8 for `π'₁`). If `u : π₁(X_s̄) → π₁(X)` has image the kernel of `h : π₁(X) → π₁(S)`
  (X.1.4) and every open normal subgroup `N` of `π₁(X_s̄)` of `L`-index is `u⁻¹(M)` for an open
  subgroup `M` of `π₁(X)`, then `π₁^L(X_s̄) → π'₁(X)` is injective. Unlike SGA's criterion, no
  `L`-condition on the covering of `X` is needed, because `u` maps onto the kernel of `h`. The
  covering form is `isProLShortExact_of_forall_exists_mono`: it suffices that every principal
  covering of `X_s̄` whose group is an `L`-group is a connected component of `E|X_s̄` for an étale
  covering `E` of `X`.
* Good elements. Let `π : H → Γ` be split by `σ` (in the application `H = π₁(X_K)`,
  `Γ = π₁(Spec K)` for the function field `K` of `S`, and `σ` comes from the section of
  `f : X → S`), `P = ker π` (`π₁(X_K̄)`), and `𝓝` a conjugation-stable family of subgroups of `P`
  normal in `P` (`lIndexSubgroups L P`, the open normal subgroups of `L`-index). An element
  `p σ(γ)` of `H` is *good* (`IsGoodFor P σ 𝓝`) if `p` lies in every `M ∈ 𝓝` and `σ(γ)` acts
  trivially on every `P/M`.
  * `IsGoodFor.conj`: good elements are stable under conjugation;
  * `IsGoodFor.mem_sup`: a good element lies in `N ⊔ σ(Γ_N)` for every `N ∈ 𝓝`, where
    `Γ_N = σ⁻¹(normalizer N)`; this subgroup meets `P` in `N` (`sup_map_inf_ker_eq`) and is open
    (`isOpen_sup_map`).
* A codimension-one point `s` of `S` (`isGoodFor_of_mem_ker`). Let `ι : H_s → H` (in the
  application `H_s = π₁(X_{F_s})`, `F_s` the fraction field of the completed strict henselization
  `R_s` of `𝒪_{S,s}`), compatible with sections `σ_s`, `σ`, with `ι(ker π_s) ⊇ ker π`, and
  `J ⊆ H_s` a normal subgroup containing `σ_s(Γ_s)` (the kernel of `π₁(X_{F_s}) → π₁(X_{R_s})`)
  such that `ι` maps `J ∩ ker π_s` into every `M ∈ 𝓝` (the core of X.3.8,
  `SGA.SGA1.ExposeX.tameLiftingDVRStatement`). Then `ι(J)` consists of good elements.
* Galois categories:
  * `exists_iso_of_forall_mem_ker_smul_eq` (V.6.7, second part): for `H : C ⥤ C'` compatible with
    fibre functors and inducing a surjection `Aut F' → Aut F`, an object of `C'` on whose fibre the
    kernel acts trivially comes from `C`. This is `SGA.SGA1.ExposeIX.mem_essImage_of_smul_eq`,
    transported from `ExposeIX.autMap H F'` to `autHom H v` (they differ by the conjugation by
    `v`);
  * `exists_isConnected_mono_forall_isGoodFor`: a covering `W` of the generic fibre (constructed as
    the connected object with stabilizer `N ⊔ σ(Γ_N)`; the conclusion does not record the
    stabilizer), containing a given principal covering of the geometric generic fibre as a
    connected component of its base change, on whose fibre good elements act trivially;
  * `exists_iso_of_forall_isGoodFor`: if the kernel of `π₁(X_{F_s}) → π₁(X_{R_s})` maps to good
    elements, `W|X_{F_s}` extends over `X_{R_s}`.
* Functoriality of `π₁` up to paths: `autHom_trans`, `autHom_congr`, `autHom_comp` are
  `SGA.SGA1.ExposeX.autMap_trans`, `SGA.SGA1.ExposeV.autMap_congr` and
  `SGA.SGA1.ExposeV.autMap_comp` restated for `autHom` (which is `ExposeV.autMap` by `rfl`), and
  `FundamentalGroup.exists_map_comp_eq` (V.6.3: `π₁(g₂) ∘ π₁(g₁)` is `π₁(g₁ ≫ g₂)` followed by the
  conjugation by an isomorphism of fibre functors).
-/

universe u

namespace SGA.SGA1.ExposeXIII

section Criterion

variable (L : Set ℕ) {G'' G' G : Type*} [Group G''] [Group G'] [Group G]
  [TopologicalSpace G''] [TopologicalSpace G'] [IsTopologicalGroup G'']
  [IsTopologicalGroup G'] [CompactSpace G''] [T2Space G']

/-- The criterion of the proof of XIII.4.3 (V.6.8 for `π'₁`), when `u : π₁(X_s̄) → π₁(X)` maps
onto the kernel of `h : π₁(X) → π₁(S)` (X.1.4): if every open normal subgroup `N` of `π₁(X_s̄)`
of `L`-index is the preimage `u⁻¹(M)` of an open subgroup `M` of `π₁(X)`, then
`π₁^L(X_s̄) → π'₁(X)` is injective. Indeed `u(N)` is then an open normal subgroup of `L`-index of
`ker h = u(π₁(X_s̄))`, so it contains the kernel of `ker h → (ker h)^L`, and `u(N) ⊆ M`. -/
theorem comap_primeKernel_le_proLKernel_of_forall_exists (u : G'' →* G') (h : G' →* G)
    (hu : Continuous u) (hr : u.range = h.ker)
    (H : ∀ N : Subgroup G'', N.Normal → IsOpen (N : Set G'') → IsLIndex L N →
      ∃ M : Subgroup G', IsOpen (M : Set G') ∧ M.comap u = N) :
    (primeKernel L h).comap u ≤ proLKernel L G'' := by
  intro x hx
  rw [mem_proLKernel]
  intro N hNn hNo hNL
  obtain ⟨M, -, hM⟩ := H N hNn hNo hNL
  -- `k : G'' → ker h`, surjective
  have hmem (y : G'') : u y ∈ h.ker := hr ▸ ⟨y, rfl⟩
  let k : G'' →* h.ker := u.codRestrict h.ker hmem
  have hk : Function.Surjective k := by
    rintro ⟨y, hy⟩
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, rfl⟩
  have hkc : Continuous k := hu.subtype_mk _
  let N₀ : Subgroup h.ker := N.map k
  have hN₀n : N₀.Normal := Subgroup.Normal.map hNn k hk
  have hidx : N₀.index ∣ N.index := N.index_map_dvd hk
  have hN₀L : IsLIndex L N₀ := by
    refine ⟨fun h0 ↦ hNL.1 (Nat.eq_zero_of_zero_dvd (h0 ▸ hidx)), fun p hp hdvd ↦ ?_⟩
    exact hNL.2 p hp (hdvd.trans hidx)
  have : N₀.FiniteIndex := ⟨hN₀L.1⟩
  have hN₀c : IsClosed (N₀ : Set h.ker) := by
    have : IsCompact (N : Set G'') := (Subgroup.isClosed_of_isOpen N hNo).isCompact
    exact (this.image hkc).isClosed
  have hN₀o : IsOpen (N₀ : Set h.ker) := N₀.isOpen_of_isClosed_of_finiteIndex hN₀c
  -- `u x` lies in the pro-`L` kernel of `ker h`, hence in `N₀`
  obtain ⟨y, hy, hyx⟩ := hx
  have hyN₀ : y ∈ N₀ := proLKernel_le hN₀n hN₀o hN₀L hy
  obtain ⟨n, hn, hny⟩ := hyN₀
  have hux : u x = u n := by
    rw [← hyx]
    exact congrArg Subtype.val hny.symm
  have hnM : n ∈ M.comap u := hM ▸ hn
  have hxM : x ∈ M.comap u := by
    rw [Subgroup.mem_comap, hux]
    exact hnM
  rwa [hM] at hxM

end Criterion

section Good

variable {H Γ : Type*} [Group H] [Group Γ] (P : Subgroup H) (σ : Γ →* H)
  (𝓝 : Set (Subgroup H))

/-- An element of `H` is *good* for `(P, σ, 𝓝)` if it is `p σ(γ)` with `p` in every member of `𝓝`
and `σ(γ)` acting trivially on `P/M` for every `M ∈ 𝓝` (in the application `P = ker π` for a
retraction `π` of `σ`). -/
def IsGoodFor (j : H) : Prop :=
  ∃ (p : H) (γ : Γ), j = p * σ γ ∧ (∀ M ∈ 𝓝, p ∈ M) ∧
    ∀ M ∈ 𝓝, ∀ x ∈ P, σ γ * x * (σ γ)⁻¹ * x⁻¹ ∈ M

variable {P} (π : H →* Γ)

variable {π σ 𝓝}

/-- Good elements are stable under conjugation, when `𝓝` consists of subgroups of `P = ker π`
normal in `P` and is stable under conjugation by `H` (`M ∈ 𝓝` implies `g⁻¹ M g ∈ 𝓝`). -/
theorem IsGoodFor.conj (hσ : ∀ γ, π (σ γ) = γ)
    (hnorm : ∀ M ∈ 𝓝, ∀ q ∈ π.ker, ∀ m ∈ M, q * m * q⁻¹ ∈ M)
    (hconj : ∀ M ∈ 𝓝, ∀ g : H, M.comap (MulAut.conj g).toMonoidHom ∈ 𝓝)
    {j : H} (hj : IsGoodFor π.ker σ 𝓝 j) (g : H) : IsGoodFor π.ker σ 𝓝 (g * j * g⁻¹) := by
  obtain ⟨p, γ, rfl, hp, hγ⟩ := hj
  have hc (M : Subgroup H) (hM : M ∈ 𝓝) (g x : H) (hx : x ∈ M.comap (MulAut.conj g).toMonoidHom) :
      g * x * g⁻¹ ∈ M := by
    simpa [MulAut.conj_apply] using hx
  -- `g = q σ(δ)` with `q ∈ ker π`
  set δ := π g
  set q := g * (σ δ)⁻¹ with hq
  have hqP : q ∈ π.ker := by
    rw [MonoidHom.mem_ker, hq, map_mul, map_inv, hσ, mul_inv_cancel]
  have hg : g = q * σ δ := by rw [hq, inv_mul_cancel_right]
  set γ' := δ * γ * δ⁻¹
  -- `σ(γ')` acts trivially on every `P/M`
  have hγ' : ∀ M ∈ 𝓝, ∀ x ∈ π.ker, σ γ' * x * (σ γ')⁻¹ * x⁻¹ ∈ M := by
    intro M hM x hx
    have hy : (σ δ)⁻¹ * x * σ δ ∈ π.ker := by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [map_mul, map_mul, map_inv, hσ, hx, mul_one, inv_mul_cancel]
    have h1 := hc M hM (σ δ) _ (hγ _ (hconj M hM (σ δ)) _ hy)
    have : σ γ' * x * (σ γ')⁻¹ * x⁻¹ =
        σ δ * (σ γ * ((σ δ)⁻¹ * x * σ δ) * (σ γ)⁻¹ * ((σ δ)⁻¹ * x * σ δ)⁻¹) * (σ δ)⁻¹ := by
      simp only [γ', map_mul, map_inv]
      group
    rw [this]
    exact h1
  refine ⟨g * p * g⁻¹ * (q * σ γ' * q⁻¹ * (σ γ')⁻¹), γ', ?_, fun M hM ↦ ?_, hγ'⟩
  · rw [hg]
    simp only [γ', map_mul, map_inv]
    group
  · refine M.mul_mem (hc M hM g p (hp _ (hconj M hM g))) ?_
    have h2 := hγ' M hM q⁻¹ (inv_mem hqP)
    have := hnorm M hM q hqP _ h2
    have heq : q * (σ γ' * q⁻¹ * (σ γ')⁻¹ * q⁻¹⁻¹) * q⁻¹ = q * σ γ' * q⁻¹ * (σ γ')⁻¹ := by
      group
    rwa [heq] at this

/-- A good element lies in `N ⊔ σ(Γ_N)` for every `N ∈ 𝓝`, where `Γ_N = σ⁻¹(normalizer N)`, when
the members of `𝓝` lie in `P = ker π`. -/
theorem IsGoodFor.mem_sup (hP : ∀ M ∈ 𝓝, M ≤ π.ker) {j : H} (hj : IsGoodFor π.ker σ 𝓝 j)
    {N : Subgroup H} (hN : N ∈ 𝓝) :
    j ∈ N ⊔ ((Subgroup.normalizer (N : Set H)).comap σ).map σ := by
  obtain ⟨p, γ, rfl, hp, hγ⟩ := hj
  refine Subgroup.mul_mem_sup (hp N hN) ⟨γ, ?_, rfl⟩
  change σ γ ∈ Subgroup.normalizer (N : Set H)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ y ∈ π.ker, σ γ * y * (σ γ)⁻¹ = σ γ * y * (σ γ)⁻¹ * y⁻¹ * y := fun y _ ↦ by group
  constructor
  · intro hx
    rw [key x (hP N hN hx)]
    exact N.mul_mem (hγ N hN x (hP N hN hx)) hx
  · intro hx
    have hxP : x ∈ π.ker := by
      have h := hP N hN hx
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv] at h
      rw [MonoidHom.mem_ker]
      simpa using h
    have h3 := N.mul_mem (N.inv_mem (hγ N hN x hxP)) hx
    have : (σ γ * x * (σ γ)⁻¹ * x⁻¹)⁻¹ * (σ γ * x * (σ γ)⁻¹) = x := by group
    rwa [this] at h3

omit 𝓝 in
/-- The subgroup `N ⊔ σ(Γ_N)` of `H` meets `P = ker π` in `N`, for `N ⊆ P`. -/
theorem sup_map_inf_ker_eq (hσ : ∀ γ, π (σ γ) = γ) {N : Subgroup H} (hN : N ≤ π.ker) :
    (N ⊔ ((Subgroup.normalizer (N : Set H)).comap σ).map σ) ⊓ π.ker = N := by
  refine le_antisymm (fun x hx' ↦ ?_) (le_inf le_sup_left hN)
  have hx : x ∈ N ⊔ ((Subgroup.normalizer (N : Set H)).comap σ).map σ := hx'.1
  have hxP : x ∈ π.ker := hx'.2
  have hle : ((Subgroup.normalizer (N : Set H)).comap σ).map σ ≤
      Subgroup.normalizer (N : Set H) := Subgroup.map_comap_le _ _
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hx
  obtain ⟨n, hn, _, ⟨γ, -, rfl⟩, rfl⟩ := hx
  have hγ : γ = 1 := by
    have := hxP
    rw [MonoidHom.mem_ker, map_mul, hσ, hN hn, one_mul] at this
    exact this
  change n * σ γ ∈ N
  rw [hγ, map_one, mul_one]
  exact hn

/-- A codimension-one point of the base. Let `π_s : H_s → Γ_s` be split by `σ_s`,
`ι : H_s → H`, `ι_Γ : Γ_s → Γ` with `ι ∘ σ_s = σ ∘ ι_Γ` and `ι(ker π_s) ⊇ ker π`, and `J` a normal
subgroup of `H_s` containing `σ_s(Γ_s)` such that `ι` maps `J ∩ ker π_s` into every member of `𝓝`.
Then `ι(j)` is good for every `j ∈ J`. -/
theorem isGoodFor_of_mem_ker {H_s Γ_s : Type*} [Group H_s] [Group Γ_s] {π_s : H_s →* Γ_s}
    {σ_s : Γ_s →* H_s} (hσ_s : ∀ γ, π_s (σ_s γ) = γ) (ι : H_s →* H) (ιΓ : Γ_s →* Γ)
    (hισ : ∀ γ, ι (σ_s γ) = σ (ιΓ γ)) (hιP : ∀ x ∈ π.ker, ∃ y ∈ π_s.ker, ι y = x)
    (J : Subgroup H_s) [J.Normal] (hJσ : ∀ γ, σ_s γ ∈ J)
    (hcore : ∀ y ∈ J, y ∈ π_s.ker → ∀ M ∈ 𝓝, ι y ∈ M) {j : H_s} (hj : j ∈ J) :
    IsGoodFor π.ker σ 𝓝 (ι j) := by
  set γ := π_s j
  have hp : j * (σ_s γ)⁻¹ ∈ π_s.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ_s, mul_inv_cancel]
  refine ⟨ι (j * (σ_s γ)⁻¹), ιΓ γ, ?_,
    fun M hM ↦ hcore _ (J.mul_mem hj (J.inv_mem (hJσ γ))) hp M hM, fun M hM x hx ↦ ?_⟩
  · rw [← hισ, ← map_mul, inv_mul_cancel_right]
  · obtain ⟨y, hy, rfl⟩ := hιP x hx
    have hyJ : σ_s γ * y * (σ_s γ)⁻¹ * y⁻¹ ∈ J := by
      have := J.mul_mem (hJσ γ) (‹J.Normal›.conj_mem _ (J.inv_mem (hJσ γ)) y)
      simpa only [mul_assoc] using this
    have hyP : σ_s γ * y * (σ_s γ)⁻¹ * y⁻¹ ∈ π_s.ker := by
      rw [MonoidHom.mem_ker] at hy ⊢
      simp [hy]
    have := hcore _ hyJ hyP M hM
    simpa only [map_mul, map_inv, hισ] using this

/-- `isGoodFor_of_mem_ker` when `ι` is compatible with the sections only up to an inner
automorphism of `H` (as for maps of fundamental groups, which are compatible up to paths):
`ι(σ_s(γ)) = c σ(ι_Γ(γ)) c⁻¹`. -/
theorem isGoodFor_of_mem_ker_of_conj (hσ : ∀ γ, π (σ γ) = γ)
    (hnorm : ∀ M ∈ 𝓝, ∀ q ∈ π.ker, ∀ m ∈ M, q * m * q⁻¹ ∈ M)
    (hconj : ∀ M ∈ 𝓝, ∀ g : H, M.comap (MulAut.conj g).toMonoidHom ∈ 𝓝)
    {H_s Γ_s : Type*} [Group H_s] [Group Γ_s] {π_s : H_s →* Γ_s}
    {σ_s : Γ_s →* H_s} (hσ_s : ∀ γ, π_s (σ_s γ) = γ) (ι : H_s →* H) (ιΓ : Γ_s →* Γ) (c : H)
    (hισ : ∀ γ, ι (σ_s γ) = c * σ (ιΓ γ) * c⁻¹) (hιP : ∀ x ∈ π.ker, ∃ y ∈ π_s.ker, ι y = x)
    (J : Subgroup H_s) [J.Normal] (hJσ : ∀ γ, σ_s γ ∈ J)
    (hcore : ∀ y ∈ J, y ∈ π_s.ker → ∀ M ∈ 𝓝, ι y ∈ M) {j : H_s} (hj : j ∈ J) :
    IsGoodFor π.ker σ 𝓝 (ι j) := by
  have hker : π.ker.Normal := inferInstance
  let ι' : H_s →* H := (MulAut.conj c⁻¹).toMonoidHom.comp ι
  have hι' (y : H_s) : ι' y = c⁻¹ * ι y * c := by
    simp [ι']
  have hgood := isGoodFor_of_mem_ker (π := π) (σ := σ) (𝓝 := 𝓝) hσ_s ι' ιΓ
    (fun γ ↦ by rw [hι', hισ]; group) (fun x hx ↦ ?_) J hJσ (fun y hyJ hyP M hM ↦ ?_) hj
  · have := hgood.conj hσ hnorm hconj c
    rwa [hι', show c * (c⁻¹ * ι j * c) * c⁻¹ = ι j by group] at this
  · obtain ⟨y, hy, hyx⟩ := hιP (c * x * c⁻¹) (hker.conj_mem x hx c)
    exact ⟨y, hy, by rw [hι', hyx]; group⟩
  · have := hcore y hyJ hyP _ (hconj M hM c⁻¹)
    simpa [hι', MulAut.conj_apply] using this

end Good

section LIndex

variable (L : Set ℕ) {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The subgroups `M ⊆ K` that are open, normal and of `L`-index in `K` (with the subspace
topology); for `K = π₁(X_K̄) ⊆ π₁(X_K)` these are the open normal subgroups of `π₁(X_K̄)` with
`L`-group quotient. -/
def lIndexSubgroups (K : Subgroup H) : Set (Subgroup H) :=
  {M | M ≤ K ∧ (M.subgroupOf K).Normal ∧ IsOpen ((M.subgroupOf K : Subgroup K) : Set K) ∧
    IsLIndex L (M.subgroupOf K)}

variable {L} {K : Subgroup H}

omit [IsTopologicalGroup H] in
lemma conj_mem_of_mem_lIndexSubgroups {M : Subgroup H} (hM : M ∈ lIndexSubgroups L K) {q : H}
    (hq : q ∈ K) {m : H} (hm : m ∈ M) : q * m * q⁻¹ ∈ M := by
  have := hM.2.1.conj_mem ⟨m, hM.1 hm⟩ (by simpa [Subgroup.mem_subgroupOf] using hm) ⟨q, hq⟩
  simpa [Subgroup.mem_subgroupOf] using this

/-- The family `lIndexSubgroups L K` is stable under conjugation when `K` is normal. -/
lemma comap_conj_mem_lIndexSubgroups [K.Normal] {M : Subgroup H} (hM : M ∈ lIndexSubgroups L K)
    (g : H) : M.comap (MulAut.conj g).toMonoidHom ∈ lIndexSubgroups L K := by
  obtain ⟨hMK, hMn, hMo, hML⟩ := hM
  -- conjugation by `g` restricted to `K`
  let φ : K →* K :=
    { toFun x := ⟨g * x * g⁻¹, ‹K.Normal›.conj_mem _ x.2 g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφc : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφs : Function.Surjective φ := fun y ↦ by
    refine ⟨⟨g⁻¹ * y * g, by simpa using ‹K.Normal›.conj_mem _ y.2 g⁻¹⟩, Subtype.ext ?_⟩
    change g * (g⁻¹ * y * g) * g⁻¹ = y
    group
  have heq : (M.comap (MulAut.conj g).toMonoidHom).subgroupOf K = (M.subgroupOf K).comap φ := by
    ext x
    simp [Subgroup.mem_subgroupOf, φ, MulAut.conj_apply]
  refine ⟨fun x hx ↦ ?_, ?_, ?_, ?_⟩
  · have := ‹K.Normal›.conj_mem _ (hMK hx) g⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using this
  · rw [heq]; exact Subgroup.Normal.comap hMn φ
  · rw [heq]; exact hMo.preimage hφc
  · rw [heq]
    refine ⟨?_, fun p hp hdvd ↦ hML.2 p hp ?_⟩
    · rw [Subgroup.index_comap_of_surjective _ hφs]; exact hML.1
    · rwa [Subgroup.index_comap_of_surjective _ hφs] at hdvd

variable [CompactSpace H] [TotallyDisconnectedSpace H] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
  {π : H →* Γ} {σ : Γ →* H}

/-- The subgroup `N ⊔ σ(Γ_N)` is open, for `N` open in `K = ker π` and `σ` a continuous section
of the continuous `π`. -/
theorem isOpen_sup_map (hπ : Continuous π) (hσc : Continuous σ) (hσ : ∀ γ, π (σ γ) = γ)
    {N : Subgroup H} (hN : N ∈ lIndexSubgroups L π.ker) :
    IsOpen ((N ⊔ ((Subgroup.normalizer (N : Set H)).comap σ).map σ : Subgroup H) : Set H) := by
  obtain ⟨hNK, hNn, hNo, -⟩ := hN
  -- `N = U ∩ ker π` for an open `U`
  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.mp hNo
  have h1U : (1 : H) ∈ U := by
    have : (1 : π.ker) ∈ ((N.subgroupOf π.ker : Subgroup π.ker) : Set π.ker) := one_mem _
    rw [← hU] at this
    exact this
  obtain ⟨O, hOU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have hOK : ∀ x ∈ O, x ∈ π.ker → x ∈ N := fun x hxO hxK ↦ by
    have : (⟨x, hxK⟩ : π.ker) ∈ ((N.subgroupOf π.ker : Subgroup π.ker) : Set π.ker) := by
      rw [← hU]; exact hOU hxO
    simpa [Subgroup.mem_subgroupOf] using this
  -- `O` normalizes `N`
  have hON : ∀ o ∈ O, o ∈ Subgroup.normalizer (N : Set H) := by
    have key : ∀ o ∈ O, ∀ n ∈ N, o * n * o⁻¹ ∈ N := fun o ho n hn ↦ by
      have hnK := hNK hn
      have h₁ : n⁻¹ * (o * n * o⁻¹) ∈ (O : Subgroup H) := by
        have h₀ : n⁻¹ * o * n ∈ (O : Subgroup H) := by
          have := (O.isNormal').conj_mem o ho n⁻¹
          simpa only [inv_inv] using this
        have h2 : n⁻¹ * (o * n * o⁻¹) = n⁻¹ * o * n * o⁻¹ := by group
        rw [h2]
        exact (O : Subgroup H).mul_mem h₀ (inv_mem ho)
      have h₂ : n⁻¹ * (o * n * o⁻¹) ∈ π.ker := by
        rw [MonoidHom.mem_ker] at hnK ⊢
        simp [hnK]
      have := N.mul_mem hn (hOK _ h₁ h₂)
      simpa using this
    intro o ho
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨key o ho n, fun h ↦ ?_⟩
    have := key o⁻¹ (inv_mem ho) _ h
    simpa [mul_assoc] using this
  refine Subgroup.isOpen_mono (H₁ := (O : Subgroup H) ⊓ ((O : Subgroup H).comap σ).comap π)
    (fun o ho ↦ ?_) (((O.isOpen').inter (((O.isOpen').preimage hσc).preimage hπ)))
  obtain ⟨hoO, hoσ⟩ := Subgroup.mem_inf.mp ho
  have hσo : σ (π o) ∈ (O : Subgroup H) := hoσ
  have hp : o * (σ (π o))⁻¹ ∈ N := hOK _ ((O : Subgroup H).mul_mem hoO (inv_mem hσo))
    (by rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, mul_inv_cancel])
  have : o = o * (σ (π o))⁻¹ * σ (π o) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hp ⟨π o, hON _ hσo, rfl⟩

end LIndex

section AutHomComp

open CategoryTheory

universe w

variable {C : Type*} [Category C] {C' : Type*} [Category C']
  {F F₁ : C ⥤ FintypeCat.{w}} {F' : C' ⥤ FintypeCat.{w}}

/-- Composing the compatibility isomorphism with an isomorphism `φ` of fibre functors conjugates
`autHom` by `φ` (`SGA.SGA1.ExposeX.autMap_trans` for `autHom = ExposeV.autMap`). -/
lemma autHom_trans (H : C ⥤ C') (u : H ⋙ F' ≅ F) (φ : F ≅ F₁) :
    autHom H (u ≪≫ φ) = φ.conjAut.toMonoidHom.comp (autHom H u) :=
  MonoidHom.ext fun σ ↦ ExposeX.autMap_trans H u φ σ

/-- `autHom` is compatible with composition of functors (`SGA.SGA1.ExposeV.autMap_comp` for
`autHom = ExposeV.autMap`). -/
lemma autHom_comp {C'' : Type*} [Category C''] {F'' : C'' ⥤ FintypeCat.{w}} (H : C ⥤ C')
    (u : H ⋙ F' ≅ F) (H' : C' ⥤ C'') (u' : H' ⋙ F'' ≅ F') :
    (autHom H u).comp (autHom H' u') =
      autHom (H ⋙ H') (Functor.associator H H' F'' ≪≫ Functor.isoWhiskerLeft H u' ≪≫ u) :=
  ExposeV.autMap_comp H' u' H u

/-- `autHom` only depends on the functor up to isomorphism (`SGA.SGA1.ExposeV.autMap_congr` for
`autHom = ExposeV.autMap`). -/
lemma autHom_congr {H H' : C ⥤ C'} (ρ : H ≅ H') (u : H' ⋙ F' ≅ F) :
    autHom H (Functor.isoWhiskerRight ρ F' ≪≫ u) = autHom H' u :=
  ExposeV.autMap_congr ρ u

end AutHomComp

section EssImage

open CategoryTheory Limits PreGaloisCategory

universe u₁ u₂ u₃ u₄ w

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] {F : C ⥤ FintypeCat.{w}}
  [FiberFunctor F] {C' : Type u₃} [Category.{u₄} C'] [GaloisCategory C']
  {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F'] (H : C ⥤ C') (v : H ⋙ F' ≅ F)

/-- V.6.7, second part, for `autHom`: let `H : C ⥤ C'` be compatible with fibre functors
(`v : H ⋙ F' ≅ F`) with `Aut F' → Aut F` surjective. An object `Y` of `C'` on whose fibre the
kernel of `Aut F' → Aut F` acts trivially is isomorphic to `H X` for some `X`. This is
`SGA.SGA1.ExposeIX.mem_essImage_of_smul_eq`: `autHom H v` is `ExposeIX.autMap H F'` followed by
the conjugation by `v` (`ExposeX.autHom_refl`, `autHom_trans`), so both have the same kernel. -/
theorem exists_iso_of_forall_mem_ker_smul_eq (hs : Function.Surjective (autHom H v)) (Y : C')
    (hY : ∀ σ ∈ (autHom H v).ker, ∀ y : F'.obj Y, σ • y = y) :
    ∃ X : C, Nonempty (H.obj X ≅ Y) := by
  have : FiberFunctor (H ⋙ F') := ExposeV.fiberFunctor_of_iso v.symm
  have he : autHom H v = v.conjAut.toMonoidHom.comp (ExposeIX.autMap H F') := by
    rw [← ExposeX.autHom_refl, ← autHom_trans, Iso.refl_trans]
  have hker : (autHom H v).ker = (ExposeIX.autMap H F').ker := by
    ext σ
    simp [he, MonoidHom.mem_ker]
  refine ExposeIX.mem_essImage_of_smul_eq H F' (fun τ ↦ ?_) Y (hker ▸ hY)
  obtain ⟨σ, hσ⟩ := hs (v.conjAut τ)
  refine ⟨σ, v.conjAut.injective ?_⟩
  rw [← hσ, he]
  rfl

end EssImage

section GenericCovering

open CategoryTheory PreGaloisCategory

/-- The image of an open normal subgroup of `L`-index under a continuous injective homomorphism
`u : P → H` of a compact group into a Hausdorff group is open, normal and of `L`-index in the
image of `u`. -/
lemma map_mem_lIndexSubgroups {L : Set ℕ} {P H : Type*} [Group P] [TopologicalSpace P]
    [CompactSpace P] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (u : P →* H) (hu : Function.Injective u) (huc : Continuous u) {N₀ : Subgroup P}
    (hn : N₀.Normal) (ho : IsOpen (N₀ : Set P)) (hL : IsLIndex L N₀) :
    N₀.map u ∈ lIndexSubgroups L u.range := by
  let e : P ≃* u.range := MonoidHom.ofInjective hu
  have he : Continuous e := huc.subtype_mk _
  let t := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
  have heq : (N₀.map u).subgroupOf u.range = N₀.map e.toMonoidHom := by
    ext ⟨x, y, rfl⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, hnx⟩
      exact ⟨n, hn, Subtype.ext hnx⟩
    · rintro ⟨n, hn, hnx⟩
      exact ⟨n, hn, congrArg Subtype.val hnx⟩
  refine ⟨Subgroup.map_le_range u N₀, ?_, ?_, ?_⟩
  · rw [heq]; exact hn.map _ e.surjective
  · rw [heq]
    have : ((N₀.map e.toMonoidHom : Subgroup u.range) : Set u.range) = t '' (N₀ : Set P) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe]
      rfl
    rw [this]
    exact t.isOpenMap _ ho
  · rw [heq]
    have hi : (N₀.map e.toMonoidHom).index = N₀.index := Subgroup.index_map_equiv N₀ e
    exact ⟨hi ▸ hL.1, fun p hp hdvd ↦ hL.2 p hp (hi ▸ hdvd)⟩

universe u₁ u₂ u₃ u₄ w

variable {CY : Type u₁} [Category.{u₂} CY] [GaloisCategory CY] {FY : CY ⥤ FintypeCat.{w}}
  [FiberFunctor FY] {CΩ : Type u₃} [Category.{u₄} CΩ] [GaloisCategory CΩ]
  {FΩ : CΩ ⥤ FintypeCat.{w}} [FiberFunctor FΩ] (B : CY ⥤ CΩ) (b : B ⋙ FΩ ≅ FY)
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {π : Aut FY →* Γ} {σ : Γ →* Aut FY}

/-- The covering of the generic fibre attached to a principal covering of the geometric generic
fibre (Galois-category form). Let `B : C_Y ⥤ C_Ω` (base change from `X_K` to `X_K̄`) induce an
injection `u : Aut F_Ω → Aut F_Y` onto the kernel of `π : Aut F_Y → Γ` (`Γ = π₁(Spec K)`), and let
`σ` be a continuous section of `π`. For a connected `Z` of `C_Ω` and `z ∈ F_Ω Z` with normal
stabilizer `N₀` of `L`-index (a principal covering with `L`-group), there is a connected `W` of
`C_Y` such that `Z` is a connected component of `B W`, and every good element (`IsGoodFor`) of
`Aut F_Y` acts trivially on `F_Y W`. (`W` is constructed as the connected object with a point of
stabilizer `u(N₀) ⊔ σ(Γ_{N₀})`; the conclusion does not record this.) -/
theorem exists_isConnected_mono_forall_isGoodFor (L : Set ℕ) (hπ : Continuous π)
    (hσc : Continuous σ) (hσ : ∀ γ, π (σ γ) = γ) (hu : Function.Injective (autHom B b))
    (hr : (autHom B b).range = π.ker) (Z : CΩ) [IsConnected Z] (z : FΩ.obj Z)
    (hzn : (MulAction.stabilizer (Aut FΩ) z).Normal)
    (hzL : IsLIndex L (MulAction.stabilizer (Aut FΩ) z)) :
    ∃ (W : CY) (_ : IsConnected W) (i : Z ⟶ B.obj W), Mono i ∧
      ∀ j : Aut FY, IsGoodFor π.ker σ (lIndexSubgroups L π.ker) j → ∀ w : FY.obj W, j • w = w := by
  let u := autHom B b
  let N₀ := MulAction.stabilizer (Aut FΩ) z
  let N := N₀.map u
  have hN : N ∈ lIndexSubgroups L π.ker := hr ▸
    map_mem_lIndexSubgroups u hu (continuous_autHom B b) hzn (stabilizer_isOpen _ _) hzL
  have hNK : N ≤ π.ker := hN.1
  let N' := N ⊔ ((Subgroup.normalizer (N : Set (Aut FY))).comap σ).map σ
  have hN'o : IsOpen (N' : Set (Aut FY)) := isOpen_sup_map hπ hσc hσ hN
  obtain ⟨W, w, _, hw⟩ := exists_isConnected_stabilizer_eq FY ⟨N', hN'o⟩
  change MulAction.stabilizer (Aut FY) w = N' at hw
  -- the stabilizer of `w` in `Aut F_Ω` is `N₀`
  have hstab : MulAction.stabilizer (Aut FΩ) ((fiberEquiv B b W).symm w) = N₀ := by
    rw [stabilizer_fiberEquiv_symm, hw]
    ext x
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      have hxK : u x ∈ π.ker := hr ▸ ⟨x, rfl⟩
      have : u x ∈ N' ⊓ π.ker := ⟨hx, hxK⟩
      rw [sup_map_inf_ker_eq hσ hNK] at this
      obtain ⟨y, hy, hyx⟩ := this
      rwa [← hu hyx]
    · intro hx
      exact le_sup_left (a := N) ⟨x, hx, rfl⟩
  obtain ⟨i, hi, -⟩ := exists_mono_of_stabilizer_eq FΩ z ((fiberEquiv B b W).symm w) hstab.symm
  refine ⟨W, inferInstance, i, hi, fun j hj w' ↦ ?_⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Aut FY) w w'
  have hgood : IsGoodFor π.ker σ (lIndexSubgroups L π.ker) (g⁻¹ * j * g⁻¹⁻¹) :=
    hj.conj hσ (fun M hM q hq m hm ↦ conj_mem_of_mem_lIndexSubgroups hM hq hm)
      (fun M hM g ↦ comap_conj_mem_lIndexSubgroups hM g) g⁻¹
  have hmem : g⁻¹ * j * g ∈ MulAction.stabilizer (Aut FY) w := by
    rw [hw]
    simpa only [inv_inv] using hgood.mem_sup (fun M hM ↦ hM.1) hN
  rw [MulAction.mem_stabilizer_iff] at hmem
  calc j • g • w = g • (g⁻¹ * j * g) • w := by simp [mul_smul]
    _ = g • w := by rw [hmem]

omit [GaloisCategory CY] [FiberFunctor FY] [TopologicalSpace Γ] in
/-- The codimension-one step (Galois-category form). Let `D : C_Y ⥤ C_s` (base change from `X_K`
to `X_{F_s}`) and `E : C_R ⥤ C_s` (restriction from `X_{R_s}` to its generic fibre) be compatible
with fibre functors, with `Aut F_s → Aut F_R` surjective. If `Aut F_s → Aut F_Y` maps the kernel of
`Aut F_s → Aut F_R` to good elements, and the good elements act trivially on `F_Y W`, then
`W|X_{F_s}` extends over `X_{R_s}`. -/
theorem exists_iso_of_forall_isGoodFor {Cs : Type u₃} [Category.{u₄} Cs] [GaloisCategory Cs]
    {Fs : Cs ⥤ FintypeCat.{w}} [FiberFunctor Fs] {CR : Type u₁} [Category.{u₂} CR]
    [GaloisCategory CR] {FR : CR ⥤ FintypeCat.{w}} [FiberFunctor FR] (D : CY ⥤ Cs)
    (d : D ⋙ Fs ≅ FY) (E : CR ⥤ Cs) (e : E ⋙ Fs ≅ FR) (hs : Function.Surjective (autHom E e))
    {𝓝 : Set (Subgroup (Aut FY))}
    (hgood : ∀ j ∈ (autHom E e).ker, IsGoodFor π.ker σ 𝓝 (autHom D d j)) (W : CY)
    (hW : ∀ j : Aut FY, IsGoodFor π.ker σ 𝓝 j → ∀ w : FY.obj W, j • w = w) :
    ∃ T : CR, Nonempty (E.obj T ≅ D.obj W) :=
  exists_iso_of_forall_mem_ker_smul_eq E e hs (D.obj W) fun j hj y ↦
    (fiberEquiv D d W).injective (by rw [fiberEquiv_smul, hW _ (hgood j hj)])

end GenericCovering

section Scheme

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

/-- V.6.3 for schemes: for `g = g₁ ≫ g₂`, the composite `π₁(T, y) → π₁(S) → π₁(R)` is
`π₁(T, y) → π₁(R, g(y))` followed by the conjugation by an isomorphism of fibre functors (a path
from `g(y)` to `g₂(g₁(y))`). -/
theorem FundamentalGroup.exists_map_comp_eq {Ω : Type u} [Field Ω] {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g : T ⟶ R) (w : g = g₁ ≫ g₂) (y : Spec (.of Ω) ⟶ T) :
    ∃ φ : ExposeV.FEt.fiber Ω (y ≫ g) ≅ ExposeV.FEt.fiber Ω ((y ≫ g₁) ≫ g₂),
      (FundamentalGroup.map g₂ (y ≫ g₁)).comp (FundamentalGroup.map g₁ y) =
        φ.conjAut.toMonoidHom.comp (FundamentalGroup.map g y) := by
  let ρ : ExposeV.FEt.pullback g ≅ ExposeV.FEt.pullback g₂ ⋙ ExposeV.FEt.pullback g₁ :=
    MorphismProperty.Over.pullbackComp g₁ g₂ g w
  let E₀ : (ExposeV.FEt.pullback g₂ ⋙ ExposeV.FEt.pullback g₁) ⋙ ExposeV.FEt.fiber Ω y ≅
      ExposeV.FEt.fiber Ω ((y ≫ g₁) ≫ g₂) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (fiberPullbackIso g₁ y) ≪≫
      fiberPullbackIso g₂ (y ≫ g₁)
  let e := fiberPullbackIso g y
  refine ⟨e.symm ≪≫ Functor.isoWhiskerRight ρ _ ≪≫ E₀, ?_⟩
  rw [FundamentalGroup.map_eq_autHom g y, ← autHom_trans, Iso.self_symm_id_assoc,
    autHom_congr, FundamentalGroup.map_eq_autHom, FundamentalGroup.map_eq_autHom, autHom_comp]

end Scheme

section Scheme

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

/-- The criterion of the proof of XIII.4.3 for coverings (V.6.8 for `π'₁`): let `f : X ⟶ S` be
proper, flat, with separable connected geometric fibres over a connected locally noetherian `S`,
`s̄` a geometric point of `S` and `a` one of `X_s̄`. If every Galois covering `Z` of `X_s̄` whose
degree has all its prime factors in `L` is a connected component of `E|X_s̄` for an étale
covering `E` of `X`, then `1 → π₁^L(X_s̄, a) → π'₁(X, a) → π₁(S, a) → 1` is exact. -/
theorem isProLShortExact_of_forall_exists_mono (L : Set ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
    [IsLocallyNoetherian S] [ConnectedSpace S] (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s)
    (h : ∀ Z : ExposeV.FEt (pullback f s), IsConnected Z → IsGalois Z →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card ((ExposeV.FEt.fiber Ω a).obj Z) → p ∈ L) →
      ∃ (E : ExposeV.FEt X) (i : Z ⟶ (ExposeV.FEt.pullback (pullback.fst f s)).obj E), Mono i) :
    IsProLShortExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) := by
  obtain ⟨-, -, hr⟩ := properHomotopyExactSequenceFull f Ω₀ s Ω a
  refine ⟨properHomotopyExactSequence L f Ω₀ s Ω a, ?_⟩
  have : ConnectedSpace ↥(pullback f s) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) s _ _
      (IsPullback.of_hasPullback f s)
  have : ExposeIX.Submersive f := inferInstance
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_submersive f
  refine comap_primeKernel_le_proLKernel_of_forall_exists L _ _
    (FundamentalGroup.continuous_map _ _) hr fun N hNn hNo hNL ↦ ?_
  let F := ExposeV.FEt.fiber Ω a
  obtain ⟨Z, z, _, hz⟩ := exists_isConnected_stabilizer_eq F ⟨N, hNo⟩
  change MulAction.stabilizer (Aut F) z = N at hz
  have : IsGalois Z := (ExposeV.isGalois_iff_normal_stabilizer F Z z).mpr (by rw [hz]; exact hNn)
  have hcard : Nat.card (F.obj Z) = N.index := by
    rw [← hz, MulAction.index_stabilizer]
    have : MulAction.orbit (Aut F) z = Set.univ := by
      rw [MulAction.orbit_eq_univ]
    rw [this, Set.ncard_univ]
  obtain ⟨E, i, _⟩ := h Z inferInstance this fun p hp hdvd ↦ hNL.2 p hp (hcard ▸ hdvd)
  let Hf := ExposeV.FEt.pullback (pullback.fst f s)
  let v := fiberPullbackIso (pullback.fst f s) a
  refine ⟨MulAction.stabilizer _ (fiberEquiv Hf v E ((ExposeV.FEt.fiber Ω a).map i z)),
    stabilizer_isOpen _ _, ?_⟩
  ext σ
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, ← hz, MulAction.mem_stabilizer_iff]
  change autHom Hf v σ • fiberEquiv Hf v E (F.map i z) = fiberEquiv Hf v E (F.map i z) ↔ σ • z = z
  rw [← fiberEquiv_smul, (fiberEquiv Hf v E).injective.eq_iff, ← MulAction.mem_stabilizer_iff,
    stabilizer_map_of_mono F i z, MulAction.mem_stabilizer_iff]

end Scheme

end SGA.SGA1.ExposeXIII
