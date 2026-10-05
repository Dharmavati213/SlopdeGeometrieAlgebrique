# SGA 3, Exposé VIB — Generalities on group schemes

By J.-E. Bertin. English translation of the Gille–Polo recomposition,
`Exp6B-13oct24.pdf` (112 pages; not in this repository).
Complete draft; not yet independently reviewed against the French.

| File | Source pages |
| --- | --- |
| [`SGA3-VIB.tex`](SGA3-VIB.tex) | Standalone wrapper |
| [`en-01.tex`](en-01.tex) | 1–8 |
| [`en-02.tex`](en-02.tex) | 9–16 |
| [`en-03.tex`](en-03.tex) | 17–21 |
| [`en-04.tex`](en-04.tex) | 22–26 |
| [`en-05.tex`](en-05.tex) | 27–32 |
| [`en-06.tex`](en-06.tex) | 33–38 |
| [`en-07.tex`](en-07.tex) | 39–46 |
| [`en-08.tex`](en-08.tex) | 47–54 |
| [`en-09.tex`](en-09.tex) | 55–60 |
| [`en-10.tex`](en-10.tex) | 61–66 |
| [`en-11.tex`](en-11.tex) | 67–72 |
| [`en-12.tex`](en-12.tex) | 73–78 |
| [`en-13.tex`](en-13.tex) | 79–84 |
| [`en-14.tex`](en-14.tex) | 85–90 |
| [`en-15.tex`](en-15.tex) | 91–96 |
| [`en-16.tex`](en-16.tex) | 97–102 |
| [`en-17.tex`](en-17.tex) | 103–108 |
| [`en-18.tex`](en-18.tex) | 109–112 |
| [`SGA3-VIB.pdf`](SGA3-VIB.pdf) | Compiled PDF |

Build: `make -C translation/SGA3/ExposeVIB`.

Notes on the source: p. 112 is blank. Editor notes 56 and 117 are each
cited a second time by their number (`\footnotemark`). Editor note 34
contains Theorem 5.3A (Raynaud), the 1965 SGAD statement that 5.3 revises.

## Typographical corrections

Corrected in the English and marked `% typo:` in the source: 1.4 proof
`limitive` → limit; 2.10 `quel soit` → `quel que soit`; 4.2 proof
`composante irréductibles` → `composantes irréductibles`; editor note 34
`exemples du` → `exemples dus`; 5.6.1.0 proof, duplicated `le` before
`changement`; 5.8.4, extra closing parenthesis in the equivalence relation
removed and missing period after the openness assertion supplied; 6.5
`lorsque H un` → `lorsque H est un`; 6.5.2 proof `S et noethérien` →
`S est noethérien`; editor note 69 `sous l'hypothèses` and `peut-être omise`
corrected; 8.4 proof `Nous somme` → `Nous sommes`; 11.0 `aux limite
inductives` → `aux limites inductives`; 11.8.0, 11.10.1, 11.12 and the
bibliography, encoding corruption in “counit” (`coÃ¼nité`) and in the name
Lütkebohmert; 11.9.1 `des morphisme` → `des morphismes`; 11.17 proof (d),
duplicated `est`; 12.10 proof `toplogie` → `topologie`, and final period
supplied before Corollary 12.10.1.

## Source points retained as printed

Marked `% typo?:` in the source. These may be slips in the French; the translation keeps them.

| Place | As printed |
| --- | --- |
| 1.2 proof | The closure of the image is called a reduced subgroup scheme of G (rather than H). |
| 1.3.0 proof | B/n in the first sentence (rather than B/nB). |
| 1.4.2 (iii) | “the unit k-group”, although A is an artinian local ring. |
| 2.1 proof, display | b is omitted before (h,v). |
| 2.5 proof | W_X for the flatness locus of u_X. |
| 2.5 proof | Cites EGA IV_2, 11.3.10. |
| 2.5 proof of (ii) | “If moreover G is locally of finite type” (rather than u). |
| 2.5 proof of (ii) | “If moreover G is locally of finite presentation” (rather than u). |
| 3.8 proof | “locally of finite presentation over S” (rather than S_0) and EGA IV_2, 8.14.2. |
| 4.2 proof | The generic point x of G_s^0 becomes ξ in the next sentence. |
| 5.6.1.0 proof | f universally open at x and f′ at x′ (rather than z and z′). |
| 5.6.1 proof | O_{S′,s} (rather than O_{S′,s′}). |
| 5.6.2.0 (iii) | Products over S, although the base is k. |
| Editor note 44 (5.6.3) | B_x is not defined. |
| 5.8.4 | f : X → k (rather than X′). |
| 5.8.4 | The pointed homeomorphism is named q_F (rather than h_F). |
| 6.2.3 proof | “fidèlement et quasi-compact”, with `plat` missing. |
| 6.5 (i′) | Refers to 6.2 (iv), although 6.2 has only (i)–(iii). |
| 7.1 (iii) | X_S (rather than X_{i,S}). |
| 7.3 proof of (i) | X_S is said to be reduced for arbitrary S. |
| 7.3 proof of (iii) | Ends with Γ_G(f) (rather than Γ_G(φ)). |
| 7.4 proof, second case | g′ⁿ(Yⁿ), without a prime on Y, in the middle inclusion. |
| 7.6.0 | “subgroup k-functor”, although the base is S. |
| 7.6 proof | The target of μ : H ×_S H is omitted, and μ is said to be of finite presentation. |
| 7.8 proof | The morphism (A,B⁰) × (A,B⁰) → (A,B)⁰ repeats the same factor twice. |
| 7.9 proof of (i) | Concludes (A,B)₀ = A₀·B₀ (rather than (A·B)₀). |
| 8.4 proof | K_s^p = (G, K_s^{p−1}) in the nilpotent case (rather than G_s). |
| 8.4 proof | G′_α is said to be flat and separated over A. |
| 9.2 (vii) | π′ : G′ → S′ (rather than S). |
| 10.7 proof | Cites EGA IV_2 (rather than IV_3) for 8.8.2, 8.8.3, 8.10.5, 11.2.6. |
| 10.9 proof | H_i → S (rather than S_i). |
| 10.12.1 | K_η^p = (G, K_η^{p−1}) in the nilpotent case (rather than G_η). |
| 10.14 (ii) | Ends with (G,X) (rather than (G,H)). |
| 11.0 proof of (c) | q′⁻¹(U) (rather than q′⁻¹(U′)). |
| 11.7 | “the restriction δ_0 of μ” (rather than δ). |
| 11.10.bis proof | δ = θ ∘ τ, with θ an automorphism of f*(E). |
| 11.10.bis proof | The lower arrow of the diagram is labelled τ (rather than δ). |
| 11.10.bis proof | π (rather than π_α) in the final diagram and composite. |
| 11.12 proof | a_j = Σ ε(a_j) b_{ij} (rather than ε(a_i)). |
| 11.16 proof | ρ(e_j) is summed from i = 1, although the basis starts at e₀. |
| 11.16 proof | Announces H′ = H, but concludes H′ ⊂ H. |
| 11.17 proof (c) | Cites (a) (rather than (b)). |
| 11.18.1 proof | G_i without a prime. |
| 11.18.2 proof of (i) | The limit exact sequence ends with G/N (rather than G′). |
| 11.18.2 proof of (ii) | G′ in the cartesian square and identity section, while the augmentation is B → k. |
| 13.1 (i) | j : U ↪ X (rather than U ↪ S). |
| 13.5 (ii) | “for some n”, while the exponent and GL use d. |
| 13.7 proof | id_F ⊗ ε is called a section of ρ. |
