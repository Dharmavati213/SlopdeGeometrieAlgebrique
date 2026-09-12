# SGA 2, Exposé XII

Unofficial English draft of Applications to projective algebraic schemes.
Scholarly proofreading remains outstanding.

Build: `make -C translation/SGA2/ExposeXII` from the repository root.

Source: corrected SMF branch (`orig = false`) of
[arXiv:math/0511279](https://arxiv.org/abs/math/0511279).
The French TeX and PDF are not included in this repository.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).

## Source points for scholarly review

Apparent issues present in the corrected French TeX have been retained
in the translation, in accordance with the convention against silently
repairing the source. Typical retained slips include mismatched
indices, truncated formulae, and grammar in the SMF file.
Scholarly proofreading remains outstanding.

Validation: `make tex` builds this exposé; non-index source labels are
checked by `python3 translation/SGA2/check_coverage.py`.
