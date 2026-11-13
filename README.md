# Mutual evaluation

Lean 4 / Mathlib formalization accompanying:

**Mutual Evaluation and Supervision without Peers**  
Zachary Robertson, 2026.  
[Paper](https://arxiv.org/abs/2609.20789).
[Expository article](https://zrobertson466920.github.io/MutualEvaluation/).

Lean namespace `MutualEvaluation`.
Toolchain: Lean `4.33.0`, Mathlib `v4.33.0`.

## Interface

**The Public Lean modules are the authoritative home of the declarations and
their author annotations.** Theorems include proofs checked by Lean.

| Module | Material | Declarations |
|---|---|---:|
| [Core](MutualEvaluation/Public/Core.lean) | Shared kernels, scores, independence, binary critics, and probability mass | 8 |
| [TwoPairOutcome](MutualEvaluation/Public/TwoPairOutcome.lean) | Paper game, sampling, robustness, and equilibrium | 14 |
| [Abstract](MutualEvaluation/Public/Abstract.lean) | Value envelopes, regret, separability, and committed loss | 13 |
| [CriticTiming](MutualEvaluation/Public/CriticTiming.lean) | CA/VPP timing, conditional transfer, Boolean objective, and example | 24 |
| [Replication](MutualEvaluation/Public/Replication.lean) | Validity, Pearson/KL replication payments, information, regret, and single-worker equilibrium | 70 |
| [Certification](MutualEvaluation/Public/Certification.lean) | Uniform-diagonal semantics and distribution-free confidence bound | 5 |

Import all six modules with:

```lean
import MutualEvaluation
```

Internal modules supply proof dependencies and additional results. They are
included in the package, but transitive availability through an import does not
make an internal result part of the annotated interface. Public/Internal is an
annotation boundary, not Lean visibility.

Core and the internal replication expression support have no project import path
through the paper game or its results. The full replication theorem import still
has paper proof dependencies; this separation concerns shared prerequisites.

## Annotation inventory

The source markers identify 35 author annotation passages. These are counted
separately from the 134 declarations and from unmarked documentation; a passage
may describe several declarations. Zero marked passages does not mean a module
has no explanatory prose or that its prose has no author.

| Module | Marked author passages | Unmarked block comments | Unmarked doc comments | Module comments |
|---|---:|---:|---:|---:|
| Core | 0 | 5 | 0 | 0 |
| TwoPairOutcome | 0 | 14 | 0 | 0 |
| Abstract | 0 | 7 | 3 | 2 |
| CriticTiming | 16 | 1 | 0 | 4 |
| Replication | 14 | 28 | 0 | 1 |
| Certification | 5 | 0 | 0 | 1 |
| Total | 35 | 55 | 3 | 8 |

[scripts/annotation_inventory.json](scripts/annotation_inventory.json) uses a
lightweight format inspired by the [W3C Web Annotation Data Model](https://www.w3.org/TR/annotation-model/).
Each module lists `annotation_ids` (passage identities, not author identities),
unmarked comment counts, and `annotations` records with four distinct parts:

- `id`: the stable passage ID. The 30 existing `AUTHOR-PROSE-01`–`16` and
  `RP-01`–`14` IDs are retained; Certification adds `CF-01`–`05`.
- `creator`: Zachary Robertson (`https://github.com/zrobertson466920`), credited
  separately based on his authorship statement for the 35 marked passages.
- `body`: a `SpecificResource` selecting the existing prose in its Lean file,
  using a `TextPositionSelector`. No second copy of the prose is stored.
- `target`: the containing Public module as a whole. A passage can cover several
  declarations, so this does not claim a verified declaration-level mapping.

Paths resolve from the repository root at the same checkout as the inventory.
Body offsets are zero-based Unicode code-point positions in UTF-8 source with
line endings normalized to LF; `start` is inclusive and `end` exclusive. They
exclude the comment delimiters, passage marker, and surrounding whitespace.
For example, `CF-02` selects positions `[758, 835)` of
`MutualEvaluation/Public/Certification.lean`: “For positive m, information when
X=Y is uniformly distributed over m letters.” Its target is that whole module,
not a fabricated GitHub declaration anchor.

Preserve IDs when editing or moving passages; do not renumber to fill gaps or
reuse retired IDs. Update the checked-in records when source movement changes
positions. Offsets describe the current checkout, not a historical revision;
no original dates or revision history are asserted. This is ordinary project
JSON, with local IDs and paths, not a JSON-LD/RDF implementation or a claim of
full W3C compliance.

[scripts/check_annotations.py](scripts/check_annotations.py) reconstructs records
from the current source and checks IDs, creator metadata, selectors, counts,
and declaration/audit coverage. It validates structure and current coverage,
not historical authorship, verbatim preservation over time, or mathematical
correctness. Lean separately checks formal types and proofs.
[scripts/test_annotations.py](scripts/test_annotations.py) tests the parser,
Unicode positions, and rejection of stale selectors or inconsistent metadata.

Counts use outer block comments only: nested comments belong to their outer
passage; line comments are excluded. Unmarked `/--` doc comments and `/-!`
module comments are reported separately from ordinary `/-` blocks. The creator
credit does not extend to those unmarked categories.

## Build and check

Install [Elan](https://github.com/leanprover/elan). The checked-in toolchain and
Lake manifest pin Lean and dependencies. Audits also require Python 3.9 or later,
with no third-party Python packages.

```bash
lake exe cache get
lake build
python3 scripts/audit.py
```

The default build checks the public root and `MutualEvaluation/Internal.lean`,
with warnings treated as errors. The audit runner checks declaration ownership
and coverage against the Public sources, computational annotation closure, and
recursive dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
Logs are written to `.verification/`.

Individual checks can be run after building:

```bash
python3 scripts/check_annotations.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_interface.py
lake env lean -DwarningAsError=true Audit/Abstract.lean
```

Checks inspect source structure, formal types, and proofs; they do not establish
natural-language meaning or author intent. Changes to the public interface and
its interpretation require author review.

## Scope

Consult the Public declarations and their annotations for exact hypotheses.

TwoPairOutcome's `robust` and `Model.robustness` concern additional garbling of **worker 0
only**, independently on that worker's replicas. `robustBoth` requires robustness
for both workers. Truthful joint optimality needs an additional value-maximality
bound; one-sided robustness alone does not imply it.

Timing assumes ideal law access. Replication covers finite task priors and finite
report alphabets without full support; sampling theorems require measurable
singletons. Both payments have termination, integrability, unbiasedness,
information envelopes, posterior regret, and truthful single-worker equilibrium
results. Invalid critics receive zero.

Replication's `SampleSpace R` describes the anchor and two infinite streams of
potential draws, not the calls actually requested. `Transcript R` remains a
definitional alias. Replication uses one fixed reporting kernel per experiment,
not within-loop adaptive strategies. Its equilibrium is distinct from TwoPairOutcome's two-worker Nash
predicate and is not a `Model.robustness` certificate. Pearson's expected score
has an internal same-task-pair-law factorization; no such claim is made for KL.

Sampling-cost and variance identities, learned-score guarantees, and adaptive
strategies are not implemented. No semantic correctness, unique-equilibrium,
or efficient-learning guarantee is claimed.

## Citation

If you use the results or formalization in this repository, please cite the paper:

```bibtex
@article{robertson2026mutual,
  title   = {Mutual Evaluation and Supervision without Peers},
  author  = {Robertson, Zachary},
  year    = {2026},
  eprint  = {2609.20789},
  archivePrefix = {arXiv},
  primaryClass = {cs.GT}
}
```
