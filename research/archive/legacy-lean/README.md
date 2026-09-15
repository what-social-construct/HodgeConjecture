# Archived Lean prototypes

Archived: 2026-09-14.

These six sources are preserved for provenance, outside the active
`HodgeConjecture/` library. They were already excluded from the root import
graph before archival. An import audit found no consumers outside this
six-file set in the project Lean sources, including the verification and
submission wrappers.

Each archived source retains its original bytes, including its namespace,
imports, comments, and historical claims. SHA-256 checks before and after the
moves match. These files are not current build targets, and their historical
import paths are not maintained as public compatibility modules. In
particular, imports between these snapshots have not been rewritten to make
the archive an alternative live library.

| Original library path | Archived source | Reason |
| --- | --- | --- |
| `HodgeConjecture/Boundary/Normalization/GlobalExtension.lean` | [GlobalExtension.lean](HodgeConjecture/Boundary/Normalization/GlobalExtension.lean) | Broad conditional normalization-purity/global-triviality prototype; not the selected source-input interfaces used by the current spine. |
| `HodgeConjecture/Realization/BoundaryProjector.lean` | [BoundaryProjector.lean](HodgeConjecture/Realization/BoundaryProjector.lean) | Historical commutative selector-realization lane. |
| `HodgeConjecture/Realization/CohomologicalProjector.lean` | [CohomologicalProjector.lean](HodgeConjecture/Realization/CohomologicalProjector.lean) | Historical commutative selector-action and cohomological projector interfaces. |
| `HodgeConjecture/Realization/CompactificationProjector.lean` | [CompactificationProjector.lean](HodgeConjecture/Realization/CompactificationProjector.lean) | Compactification adapter for the historical commutative lane. |
| `HodgeConjecture/Realization/Chow/SelectorRealization.lean` | [SelectorRealization.lean](HodgeConjecture/Realization/Chow/SelectorRealization.lean) | Selector-generated commutative quotient specialization, superseded in the active spine by noncommutative Chow correspondence interfaces. |
| `HodgeConjecture/Realization/Chow/SheetLinearization.lean` | [SheetLinearization.lean](HodgeConjecture/Realization/Chow/SheetLinearization.lean) | Auxiliary linear coset-average map; it is not a multiplicative sheet-to-correspondence bridge. |

The declaration-free `HodgeConjecture/InertiaSaturation.lean` import shim
remains in the live library intentionally. It preserves an older public
import path to the canonical sheet module without duplicating declarations.

Current status and organization are recorded in the
[gap map](../../GAP_MAP.md), [claim ledger](../../CLAIM_LEDGER.md),
[semantic-parity queue](../../working/0005-semantic-parity-cleanup.md),
[selected-input checkpoint](../../working/0016-source-input-packages.md), and
[proof-spine/archive checkpoint](../../working/0017-proof-spine-and-archive.md).
The canonical manuscript remains [paper/main.tex](../../../paper/main.tex).
