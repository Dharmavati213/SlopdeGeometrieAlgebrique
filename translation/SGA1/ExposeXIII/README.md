# SGA 1, Exposé XIII — Cohomological properness of sheaves of sets and of sheaves of non-commutative groups

By Mme M. Raynaud, after unpublished notes of A. Grothendieck.

Full English draft of the whole exposé: the introduction, sections 0–4,
the two appendices (§§5–6), and the bibliography, with proofs, the
footnote, and all diagrams. It includes M. Raynaud's 2003 remark
XIII 2.13 (MR). It was translated from the corrected SMF branch in eight
chunks. A second reviewer then checked each chunk against the French
(2026-09-24). Scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-XIII.tex`](SGA1-XIII.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | Author line and introduction; §0 Recollections on the theory of stacks; §1 Cohomological properness, to XIII.1.9 |
| [`en-2.tex`](en-2.tex) | End of §1: XIII.1.10–XIII.1.17 |
| [`en-3.tex`](en-3.tex) | §2 A particular case of cohomological properness: divisors with relative normal crossings, XIII.2.0–XIII.2.3 |
| [`en-4.tex`](en-4.tex) | §2 continued: XIII.2.4–XIII.2.9 |
| [`en-5.tex`](en-5.tex) | End of §2: XIII.2.10–XIII.2.12 and Remark 2.13 (MR); §3 Cohomological properness and generic local acyclicity: Theorem XIII.3.1 and parts 1)–3) of its proof |
| [`en-6.tex`](en-6.tex) | End of §3: part 4) of the proof of XIII.3.1, and XIII.3.1.1–XIII.3.5 |
| [`en-7.tex`](en-7.tex) | §4 Homotopy exact sequences: XIII.4.0–XIII.4.8 and the closing Remarks (printed 4.9) |
| [`en-8.tex`](en-8.tex) | §5 Appendix I: Variations on Abhyankar's lemma; §6 Appendix II: finiteness theorem for direct images of stacks; bibliography |
| [`SGA1-XIII.pdf`](SGA1-XIII.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeXIII` from the repository
root, or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 20814–25882, from the chapter
`Propret\'e cohomologique des faisceaux d'ensembles et des faisceaux de
groupes non commutatifs` and `\label{XIII}` to the end of the exposé
(its bibliography). The notation and terminology indexes of the volume,
which follow it, are omitted.
This covers original page markers 344–439.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and use the
shared package [`sga1-en.sty`](../sga1-en.sty). All non-index labels,
`\Ref`/`\eqref`/`\cite` keys, the footnote, and all diagrams are kept.
The bibliography keeps `\begin{thebibliography}{0}{XIII.7}` (numbered
section 7). References to other exposés print the source's numbers:
`X~\Ref{X.3.6}` prints “X 3.6”, as in the SMF volume. Original page
numbers remain as `% original p. N` comments. Indexes and SMF
page-layout commands are omitted.

House rules applied here as in the other new exposés: *n°* / *numéro*
is rendered “no.” (`\No`), as in “this no.”, and *changement de base* is
rendered “change of base”, the Exposé VI term. The harmonization that
replaced “base change” after the reviews concerned Exposés IV, V, VIII,
IX, and X; this exposé needed no change.

Exposé-specific choices:

- **Remark 2.13 (MR).** The SMF prints M. Raynaud's 2003 remark
  (`remarqueMR`) between bold brackets and without a number. Here it is
  printed as “Remark 2.13 (added in 2003 (MR))”, for three reasons: its
  label `XIII.2.13` names that number, the remark closes §2, and the
  translated Preface refers to it as “XIII 2.13”. The comment on
  `remarkMR` in [`sga1-en.sty`](../sga1-en.sty) explains this.
- **Remarks printed 4.9 (key `rem:XIII.4.6`).** The original branch
  resets the counter with `\setcounter{subsection}{5}` before the
  closing Remarks of §4, so the original edition numbers them 4.6. The
  corrected branch drops this reset, so the Remarks follow 4.8 and are
  numbered 4.9. The English keeps the corrected numbering (4.9) and the
  legacy key `rem:XIII.4.6`.
- **`\leavevmode` after `\label{XIII.1.10}`.** Definitions 1.10 open
  directly with `\subsubsection{}` (1.10.1). The English adds
  `\leavevmode` so that a sectioning command can open a theorem-like
  environment. This is a typesetting device only; it is not in the
  source.
- **`\tmpRacinet`.** The source's `\newlength{\tmpRacinet}` layout for the
  `\parbox` display defining the presheaf `G` (proof of XIII.4.3.1) is
  kept.

Exposé XIII terminology:

| French | English |
| --- | --- |
| propreté cohomologique; cohomologiquement propre | cohomological properness; cohomologically proper |
| champ; gerbe; torseur | stack; gerbe; torsor |
| (1-)constructible | (1-)constructible |
| diagramme exact | exact diagram |
| diviseur à croisements normaux relatifs | divisor with relative normal crossings |
| modérément ramifié | tamely ramified |
| acyclicité locale générique | generic local acyclicity |
| suites exactes d'homotopie | homotopy exact sequences |
| lemme d'Abhyankar | Abhyankar's lemma |
| strictement local; hensélien | strictly local; henselian |

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Proof of XIII.1.3.1, (ii) ⇒ (i) | Display `H^0(Y_1, g_1^* f_{1*}(^P F_1))` | Presumably `H^0(Y'_1, …)`. |
| Proof of XIII.1.3.1, (ii bis) ⇒ (ii) | “locally isomorphic for the étale topology of `Y_1`” | The argument gives `Y'_1`. |
| XIII.1.5 b) | “geometric points `\overline y'` of `\overline{Y'}`” | Possibly `Y'`. |
| XIII.1.5 c) | “`S'` a discrete valuation ring”; “ne rencontre par le fermé” | Treats `S'` as a ring; *par* for *pas*. |
| Proof of XIII.1.7 | Base-change arrows `i`, `j` in the diagram go `g'_*k^* → m^*g_*` | Opposite to the direction in 1.6. |
| XIII.1.10.4, check of b) | `u` satisfies (1.10.2.2) | (1.10.2.1) is meant. |
| XIII.1.12 2) | Hypothesis “`(Φ, f)` cohomologically proper … in dimension ≤ 1” | Circular; `(Φ_1, f)` is meant. |
| XIII.1.13 2) | “every torsor `Q` on `X_1` with group `F_1`”; “inverse image on `X_1` isomorphic to `P'`” | `G_1`; `X'_1`. |
| Proof of XIII.1.15 | Inverse images of `X_2`, `Φ_2` (resp. `X_1`, `Φ_1`); display `H^0(\overline X_1, h^*(SheafHom_{\overline X_2}(x, y))` | The statement has only `X`, `Φ`; a closing parenthesis is missing. |
| XIII.1.17 | “`X` and `Y` locally noetherian” | There is no `Y` in 1.14 (`S` is meant). |
| XIII.2.0 | Subgroup defined as `H_i`, then `G_0/H_1` and `H^i/H^{i+1}` | Subscripts and superscripts are mixed. |
| XIII.2.0.2 | “Galois group of `\overline{L'_j}\|K`”; “the `L'_j` tamely ramified over `\overline R`”; “`v_j` runs through the valuations of `L`”; “the group `I_i` is an extension … by `P_j`” | Presumably `\|\overline K`, `\overline{L'_j}`, `L'`, `I_j`. |
| XIII.2.0.2, second part | “`R'` is a local ring”, “`k(\tilde R') = R'/(\tilde π)`”, “`R'` discrete valuation ring”; “[EGA IV 4.3.2 and 4.3.5]” as plain text | Presumably `\tilde R'`; the EGA reference is plain text, not a citation. |
| XIII.2.1.1; XIII.2.3 b) | “field of fractions `K` of `O_{X_{\overline s}}`” | A misplaced subscript; “`, y`” is missing. |
| XIII.2.1.2 | `\overline F` in (2.1.2.1) | Never defined. |
| XIII.2.2 | `U_1 = U ×_X X_1` | `X_1` is undefined; `U_1` is unused. |
| End of XIII.2.3 b) | “`H` is tamely ramified over `X` relative to `S`”, said of the `\overline K`-algebra `H` | “Over `\overline R`” is expected. |
| XIII.2.4.2 | `φ_{\overline x}` | `φ_{\overline x'}` is expected. |
| (XIII.2.4.2.1) | `H^0(\overline U, \overline F))` | An extra closing parenthesis. |
| XIII.2.4.3 | “the subset `H^1(…)`” | “The subset of” is meant. |
| Proof of XIII.2.4, 2) | `K = ∏_{l ∈ LL − {p} ∩ LL}`; open set written `X_{I'}` and `X_I'` | Odd index set; inconsistent notation. |
| XIII.2.5, statement | `i_*^t Φ` in the last sentence | `i_*^{tame}` elsewhere. |
| Proof of XIII.2.5 | `H^0(S, \overline{SΨ})`; `\overline m^* G` with “where `m` is the morphism”; “`ψ` is an equivalence”; display for `\overline ψ` with `i^t_*Φ(\overline{X'})` on the left; `\overline S \overline Φ` next to `\overline{SΦ}` | `\overline S`; `\overline m`; `\overline ψ`; `\overline X` probably meant; inconsistent notation. |
| Proof of XIII.2.7 | `Φ` a stack “on `X`” of torsors “with group `F\|U`”; `S(p_*Φ)`, `S(q_*i_*^t F)`; “`SG` constructible” next to “`G` 1-constructible”; bare “6.3” | `U'` is expected; `p_*`, `p_*i_*^t` are meant; inconsistent; the reference is unclear. |
| XIII.2.8 | “on `U`” twice | Repetition. |
| XIII.2.10 | Diagram top-right vertex `U_{\bar s_1}`; inner-automorphism sentence and final display use `X_{\bar s_2}`, `X_{\bar s_1}` | `U_{\bar s_2}` is meant; `U` is meant. |
| XIII.2.11 | Inertia subgroup in `π_1^t(\bar U_{\bar s_1})`; in the proof, `\overline U_{\bar s_1}` in the “resp.” part and a stray “and (resp. …)” | Apparently `U_{\bar s_1}`; `\overline U_{\bar s_2}`. |
| XIII.2.11–XIII.2.12 | `\Ref{XIII.1.10}`, `\eqref{XIII.1.10}`, `\Ref{XIII.1.11}` | These keys are the exact-diagram definitions 1.10–1.11; 2.10–2.11 are almost certainly meant. |
| Proof of XIII.2.12 | “over `U''`”; `F` in the text, `F'` in the display; `g': U' → k'` | Apparently `U'`; inconsistent; `→ Spec k'`. |
| XIII.2.13 (MR) | “Let `X = Spec(A)`” | `U = Spec(A)` is meant. |
| Proof of XIII.3.1, 1) 2 | `prof_et_{S−U}(X)` | Apparently `X − U`. |
| Proof of XIII.3.1, 1) 3 | “(SGA 4 2.14.1)” | The exposé numeral is missing. |
| Proof of XIII.3.1, 3) 1; 3) 2; 3) 4 | “`X_{1s}` smooth over `S`”; `p_s: X_{1s} → X`; the proper morphism is `g` in the text, `q` in the diagram | Presumably over `s`; `→ X_s`; inconsistent. |
| Proof of XIII.3.1, 4) 1, end of third paragraph | “It then follows from 3.1.2 that `f_*Ψ` is constructible” | 3.1.2 gives that `f_*Φ` is 1-constructible. |
| Proof of XIII.3.1, 4) 2 | “for every `S'`-scheme `S`”; “geometric point `\overline y'` of `Y`”, “strict localization of `Y` at `y'`”; reference “( a)1) and 4)1))”; `Φ'(X')` at the end | Looks inverted; `Y'` and `\overline y'` probably; “a)1)” is odd; `Φ'(\overline{X'})` is meant. |
| Proof of XIII.3.2 | The corollary is called “the proposition” | Wrong statement type. |
| XIII.3.3 | `\bar k` of `k` | `k` is undefined (`κ(s)`). |
| XIII.3.3 | “desingularizable (EGA IV 7.9.1)” | XIII.3.1 and XIII.3.5 assume “strongly desingularizable (SGA 5 I 3.1.5)”; compare the two hypotheses. |
| Proof of XIII.3.3 | “`Y_s` smooth over `S`”; “(SGA XV 2.1)”; bottom row of the large diagram `Z'`, `T'` | Probably over `s`; the volume number 4 is missing; `Z`, `T` are expected. |
| Proof of XIII.4.3.1 | `G → R^1f_*F`; “same element of `G(X)`” | The lemma's group is `C`; probably `G(S)`. |
| XIII.4.5; proof of XIII.4.5.3 | `π'_1(X, a)` a semi-direct product of `π_1(S, a)` by `π_1(X_{\bar s}, a)`; “/aut. int. `G`” | The superscript `L` is missing; `G` for bold `𝐆`. |
| Proof of XIII.4.6 | “`g` satisfies all the hypotheses of 4.2”; composite `π^{p'}(X_b, c) → π^{p'}(Z, c) → π^{p'}(Y, b)` called an isomorphism; `π^{p'}(X, a) × π^{p'}(Y, b) × π^{p'}(Y, b) → 1` | `f` is meant; the second map should go to `π^{p'}(X, a)`; the second `×` should be `→`. |
| XIII.4.7 b) | “faisceau de L-groupe” (singular), rendered “sheaf of L-groups” | An agreement slip, corrected in 4.3 but not here. |
| Remarks 4.9 a) | “SGA XIV 1.11” | The volume is missing (SGA 2?). |
| Remarks 4.9 b) | “Corollary 4.5” | 4.8 is meant. |
| XIII.5.1 | `n_i` “integers ≥ 0”; `U` | `> 0` presumably; `U` is used undefined. |
| Proof of XIII.5.2 | “extends to the whole of `X`” | Presumably `X'`. |
| XIII.5.3 | `D = Σ_{1≤i≤n}` | The statement uses `T_1, …, T_r`. |
| XIII.5.4 | “relative to `S_1`” | `S_1` is undefined (the proof says `S`). |
| XIII.5.5, statement | “`Y = X − Supp D`, `U = X − Y`” | Presumably `Y = Supp D`. |
| Proof of XIII.5.5 | “finite separable extension of `K`”; `T_i^{n_{i_0}/p} − f_{i_0}`; `X_1[T]/T^p − f_{i_0}`; “contrary to the hypothesis `n_{i_0} = p`” | `K_i`; `T_{i_0}`; parentheses are missing; only `p \| n_{i_0}` was assumed. |
| XIII.5.7 | `\tilde g: \tilde U → \tilde S` | `\tilde S` is undefined (`\overline S` presumably). |
| Proof of XIII.6.1.1 | `h_i: \overline s → S'` before `S'` is defined; “has image `q_i\|S''` in `F(S'')`” (twice); `U` and `U'` mixed at the end; “a nonempty open set `U` of `s`” | Presumably `→ T`; `q_i` is a section of `f_*(SΦ)`; inconsistent; odd wording. |
| XIII.6.1.2 and its proof | “sections of `G` above `X`”; `\bar a^{-1}(q_i)`, `\tilde a^{-1}(q_i)` | Presumably `S`; `\bar q_i`, `\tilde q_i` are expected. |
| XIII.4.1; proof of XIII.4.2 | The statement ends without a period; the proof begins in lower case | Typographic slips, retained. |
| French slips | “une revêtement principal”, “l'une des condition” (§2); “l'mage” (proof of XIII.3.1.1) | These do not affect the English. |

## Validation

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, finds for each chunk the same non-index labels, reference
and citation keys, footnotes, diagrams, displayed formulas, list items,
statement environments, and counter commands as in the corrected
French. For the whole exposé these are 128 labels, 251 references,
22 citations, 1 footnote, 47 diagrams, and 429 displays. The wrapper
compiles to a 51-page PDF with no errors or undefined references. The
only layout warning is one line about 7 pt too wide.

A second reviewer checked all eight chunks against the French and made
four fixes:

- en-2.tex: register (“consider” → “one considers”);
- en-3.tex: “this number” → “this no.”;
- en-6.tex: register (“we” → “one”), twice.

The reviewer confirmed all the translator's source points and added
those on:

- the end of XIII.2.3 b);
- the proof of XIII.2.5 (the `\overline ψ` display and the `\overline S`
  notation);
- part 4) 1 of the proof of XIII.3.1;
- the proof of XIII.5.5 (`n_{i_0} = p`);
- the proofs of XIII.6.1.1 and XIII.6.1.2.

The reviewer also confirmed that the keys `XIII.1.10`/`XIII.1.11` in
2.11–2.12 are the exact-diagram definitions. These checks do not settle
the mathematical questions above; scholarly proofreading remains
outstanding.

License: [`../../LICENSE`](../../LICENSE) (MIT for the
translator's contribution).
