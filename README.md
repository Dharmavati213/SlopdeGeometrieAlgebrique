# Slop de Géométrie Algébrique

*SGA, English + Lean.*

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

Unofficial English translations of Grothendieck's *Séminaire de Géométrie
Algébrique du Bois Marie* (SGA), with a Lean 4 formalization built on
[mathlib](https://github.com/leanprover-community/mathlib4).

This is a working tree, not a finished edition.

- **English.** SGA 1, SGA 2 and SGA 3 are translated in full (SGA 3 without
  its indexes). Every SGA 1 exposé has been checked against the French by a
  second reader; SGA 2 and SGA 3 have not yet been checked independently.
- **Lean.** SGA 1 is formalized exposé by exposé. Its open items are listed in
  [`docs/formalization.md`](docs/formalization.md), and the results it quotes
  from other theories (Hodge theory, GAGA, SGA 4, …) in
  [`lean/SGA/Foundations/README.md`](lean/SGA/Foundations/README.md).
  SGA 2 Exposés I–VII are partly formalized.

## Layout

```
translation/     English TeX and PDFs: SGA1/, SGA2/, SGA3/
lean/            Lean 4 library (Lake + mathlib)
docs/            status checklist and formalization notes
notes/           agents' working notes: who is on what, what was hard
LICENSES/        full texts of licenses other than MIT
```

| Work | State |
| --- | --- |
| SGA 1, English | front matter and Exposés I–VI, VIII–XIII ([`translation/SGA1/`](translation/SGA1/)); there is no Exposé VII |
| SGA 1, Lean: I, II, IV–VI, VIII, XI | every numbered statement proved, apart from recorded restrictions and out-of-scope items |
| SGA 1, Lean: III, IX, X, XIII | mostly proved |
| SGA 1, Lean: XII | §§1–2, and §3 on the spaces of points `X(ℂ)`; GAGA (§4) and the comparisons that need coherent analytic sheaves are not formalized |
| SGA 1, prerequisites missing from mathlib | [`lean/SGA/Foundations/`](lean/SGA/Foundations/) |
| SGA 2, English | Introduction and Exposés I–XIV ([`translation/SGA2/`](translation/SGA2/)) |
| SGA 2, Lean: V | every numbered statement proved (local duality, structure of `Hⁱ(M)`) |
| SGA 2, Lean: I–IV, VI | partial: local cohomology with closed and locally closed supports and its spectral sequence (I), affine comparisons and Koszul complexes (II), depth (III), dualizing modules and functors (IV), Ext with supports (VI) |
| SGA 2, Lean: VII | VII.1.3 on locally noetherian schemes |
| SGA 2, Lean: VIII–XIV | not started |
| SGA 3, English | foreword, introduction and Exposés I–XXVI ([`translation/SGA3/`](translation/SGA3/)) |
| SGA 3 Lean, SGA 4–7 | not started |

Per-exposé detail: [`docs/status.md`](docs/status.md) (checklist) and
[`docs/formalization.md`](docs/formalization.md) (what the Lean proves, with
declaration names). Sources and licenses: [`COPYRIGHT.md`](COPYRIGHT.md).

## Claiming work

To translate an exposé or formalize part of one, [open an
issue](https://github.com/Dharmavati213/SlopdeGeometrieAlgebrique/issues/new/choose)
with the **Translation** or **Formalization** template and say what you will
do (which SGA, which exposé or section). Check
[`docs/status.md`](docs/status.md) and the open issues first, so that two
people do not take the same text. An exposé is translated before it is
formalized.

How to write the TeX and the Lean:
[`.github/CONTRIBUTING.md`](.github/CONTRIBUTING.md).

## Build

Needs [elan](https://github.com/leanprover/elan) and a TeX Live with `latexmk`.

```bash
make            # Lean + PDFs
make lean       # lake build in lean/
make tex        # every SGA 1 and SGA 2 PDF, and the SGA 3 volume
```

For the first Lean build, download mathlib's compiled files before building:

```bash
cd lean
lake exe cache get
lake build
```

Open `lean/` in VS Code (Lean 4 extension) or Neovim (`lean.nvim`).
The root modules are `SGA.SGA1.ExposeI` … `SGA.SGA1.ExposeXIII` (no Exposé VII),
`SGA.Foundations`, and `SGA.SGA2.ExposeI` … `SGA.SGA2.ExposeVII`.

To check that no declaration depends on an axiom beyond `propext`,
`Classical.choice` and `Quot.sound`, run `lake env lean CheckSGA1Axioms.lean`
(SGA 1 and Foundations) or `lake env lean CheckSGA2Axioms.lean` (SGA 2) from
`lean/`.

There is no CI: the full Lean build is too large for GitHub's hosted runners.
Run `make lean`, and `make tex` if you changed TeX, before opening a pull
request.

## License

[MIT](LICENSE): the Lean code, the English translation, the docs, and the repo tooling.
Two exceptions keep the license they came with:

- SGA 1, Exposé III, English (`translation/SGA1/ExposeIII/`):
  [CC BY-SA 4.0](translation/SGA1/ExposeIII/LICENSE).
- `lean/SGA/SGA2/ExposeII/ProjectiveComplexLift.lean`: adapted from mathlib,
  [Apache-2.0](LICENSES/Apache-2.0.txt).

Details: [`COPYRIGHT.md`](COPYRIGHT.md). This is not an official edition of SGA.
The French original is not in this repository, and no license here covers it.
