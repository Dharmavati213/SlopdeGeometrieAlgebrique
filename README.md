# SGA, English + Lean

> ✨ **Welcome.** In today's rapidly evolving landscape of algebraic geometry, Grothendieck's *Séminaire de Géométrie Algébrique* remains a timeless tapestry of ideas — and yet, for too long, English readers and Lean formalizers have been left behind. That changes now. Let's dive in. 🚀

This is **not just** a personal project. This is a **personal project** for SGA translation **and** Lean translation — powered entirely by LLMs, AI, and generative AI. We are leveraging cutting-edge large language models to unlock Grothendieck at scale. No human-crafted prose. No artisan Lean. Just tokens. Just vibes. Just **pure, uncut SLOP**.

Is it perfect? No. And that's okay. 💙

If you hate it, that's valid. Your feelings are valid. Hate is a valid form of engagement. We're not here to yuck your yum — but we *are* here to keep generating. Because at the end of the day, here's the thing:

**The sloppiest English translation is still better than no translation.**

Let that sink in.

And the sloppiest Lean? It's still the sloppiest Lean. And — crucially — the sloppiest Lean is still better than no Lean. That's not a bug. That's the whole value proposition. 🎯

### Key takeaways

- 🤖 **100% AI.** This repo is LLM-native. Generative AI all the way down. If you're looking for a carefully copy-edited scholarly edition, you're in the wrong repository — and that's okay!
- 🫠 **This is slop, on purpose.** We said it. We'll say it again. SLOP. If that word bothers you, this README is already doing its job.
- 📚 **Something > nothing.** A messy English exposé that exists beats a perfect French exposé you cannot read. A messy Lean file that compiles (or even one that doesn't, yet, but has *energy*) beats a theorem that lives only in the air.
- ❤️ **Hate is optional, but the slop is not.** You can close the tab. The tokens will still be here in the morning.

So buckle up, stay curious, and remember: we're not just translating SGA. We're *reimagining what it means to translate SGA in the age of generative AI*. Whether you're a seasoned algebraic geometer or just a large language model passing through — welcome to the journey.

Let's build the future of slop, together. 🌟

---

Unofficial English translations of Grothendieck’s *Séminaire de Géométrie
Algébrique du Bois Marie* (SGA), together with a Lean 4 formalization
on [mathlib](https://github.com/leanprover-community/mathlib4).

This is a working tree, not a finished edition. SGA 1 is translated in
full (front matter and Exposés I–VI, VIII–XIII; VII does not exist), as is
SGA 2 (Introduction and Exposés I–XIV);
the Lean side of SGA 1 I and VI compiles against mathlib. SGA 2 has partial
Lean formalizations of Exposés I–VII, with exact coverage and remaining
gaps recorded in [`docs/formalization.md`](docs/formalization.md).

## Layout

```
translation/     English TeX + PDF
lean/            Lean 4 library (Lake + mathlib)
docs/            status and formalization notes
```

| Work | State |
| --- | --- |
| SGA 1, front matter and Exposés I–VI, VIII–XIII — English | full drafts ([`translation/SGA1/`](translation/SGA1/)) |
| SGA 1, Exposé I — Lean | compiling (mathlib language + numbered lemmas) |
| SGA 1, Exposé VI — Lean | compiling (mathlib language + numbered lemmas) |
| SGA 1, other exposés — Lean | not started |
| SGA 2, Introduction–XIV — English | drafts in `translation/SGA2/` |
| SGA 2, Exposés I–III — Lean | partial; locally closed internal Hom/sheaf Ext, arbitrary-coefficient extension sequences, group- and sheaf-valued nested-support sequences, general spectral sequences, noetherian affine comparison, II.8–II.11 algebra, all-degree depth and restriction criteria, Hartogs, connected components, component chains in codimension, and catenary equidimensionality |
| SGA 2, Exposé IV — Lean | partial; canonical representation, IV.3.1–3.2 duality criteria, nonlocal finite-length duality, supported injective envelopes, finite coinduction, quotient annihilators, locally Artinian completion equivalence and duality transfer, Macaulay quotient-dual colimit, orthogonality, cyclic/socle criterion, and regular-local global dimension with arbitrary-module upper Ext vanishing |
| SGA 2, Exposé V — Lean | partial; canonical local duality, sharp upper vanishing, top nonvanishing, Artinianity and completed-dual finiteness/dimension bounds over arbitrary noetherian local rings; exact completed top-dual dimension and associated-prime formula; algebraic change of rings, V.3.2's functorial first-quadrant module spectral sequence with natural module-linear E₂ and source-cohomology abutment and a resolution-independent finite filtration, V.3.3's component criterion, V.3.4's affine-complement codimension bound, and V.3.5–V.3.6's full finite-length and punctured-depth criteria over quotients of regular local rings |
| SGA 2, Exposé VI — Lean | partial; genuine internal Hom and tensor support representations, module-derived supported Ext, actual local Ext and excision, long exact sequences, spectral functors with E₂ and Ext abutment comparisons, and affine degree-zero quotient-Hom colimits |
| SGA 2, Exposé VII — Lean | partial; actual internal-Hom zero detection from literal stalk support on locally noetherian schemes |
| SGA 2, Exposés VIII–XIV — Lean | not started |
| SGA 3–7 | not started |

Tick-list: [`docs/status.md`](docs/status.md).
Sources and licenses: [`COPYRIGHT.md`](COPYRIGHT.md).

## Claiming work

To translate an exposé or formalize a stretch of one, [open an
issue](https://github.com/Dharmavati213/SGAenglishpluslean/issues/new/choose)
and say what you intend to do (which SGA, which exposé or section).
That is how a claim is made; it keeps two people off the same text.

Use the **Translation** or **Formalization** template. Look at
[`docs/status.md`](docs/status.md) and at open issues first. English of
an exposé comes before Lean for that exposé.

How to write the TeX or the Lean once you have claimed it:
[`.github/CONTRIBUTING.md`](.github/CONTRIBUTING.md).

## Build

Needs [elan](https://github.com/leanprover/elan) and a TeX Live with `latexmk`.

```bash
make            # Lean + PDF
make lean       # lake build in lean/
make tex        # PDFs of all of SGA 1 and SGA 2
```

First Lean build, from `lean/`:

```bash
cd lean
lake exe cache get    # download mathlib oleans; do this first
lake build
```

Open `lean/` in VS Code (Lean 4 extension) or Neovim (`lean.nvim`).
The root modules are `SGA.SGA1.ExposeI`, `SGA.SGA1.ExposeVI`,
`SGA.SGA2.ExposeI`, `SGA.SGA2.ExposeII`, `SGA.SGA2.ExposeIII`, `SGA.SGA2.ExposeIV`,
`SGA.SGA2.ExposeV`, `SGA.SGA2.ExposeVI`, and `SGA.SGA2.ExposeVII`.

To check all imported SGA 2 declarations for additional axioms, run
`lake env lean CheckSGA2Axioms.lean` from `lean/`.

## License

- Lean code, docs, and repo tooling: [Apache-2.0](LICENSE)
- English translation: [CC BY-SA 4.0](translation/LICENSE)

This is not an official edition of SGA. The French original is not in
this repository.
