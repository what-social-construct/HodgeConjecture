# Fixed-ring proof pruning and parity queue

Status: ACTIVE AUDIT -- no Lean declarations are deleted by this document.

Last audited: 2026-09-10.

## Scope and target

This queue audits the proof originally presented in
`research/archive/manuscripts/paper1.tex` against the Lean implementation in
`HodgeConjecture/Boundary/Normalization/`. Section numbers below refer to
that archived draft. The active manuscript is `paper/main.tex`; its
fixed-ring argument is a technical appendix, and only `paper/main.pdf` is an
active publication PDF. The intended self-contained normalization endpoint is:

```text
height-one normalization prime Q
  + actual prime inertia I_Q
  + I_Q <= H
  -> S^G is unramified at Q contracted to S^H.
```

Stacks Project Tags `09EH` and `0BST` may remain as provenance, but the final
Lean endpoint must not take their conclusion as an opaque argument.  The
generic theorem for arbitrary `A`, `S`, `I`, and `H` must remain conditional:
an arbitrary subgroup named `I` is not automatically an inertia group.

The audit dispositions are:

- **CORE**: part of the shortest final proof or its public statement.
- **SUPPORT**: a real implementation lemma; keep it, but do not advertise it
  as a separate mathematical result.
- **ADAPTER**: a legitimate boundary between two representations; keep only
  while it has a semantic client.
- **COMPAT**: superseded public wrapper; migrate callers, then deprecate rather
  than silently deleting it.
- **RESEARCH**: exploratory or explanatory material outside the compiled
  proof path.
- **MISSING**: a new theorem or bridge that the self-contained endpoint really
  requires.

Reference counts from `research/Verification.lean`, manuscript prose, and
comments do not make a declaration part of the semantic proof path.

## Minimal dependency spine

```text
finite invariant extension
  -> going down
  -> height-one contraction
  -> selected fixed-ring localization is a DVR

prime inertia at Q
  -> [MISSING: inertia-fixed DVR theorem]
  -> unramifiedness of S^I at the selected contraction
  -> local subgroup descent for I <= H

centered valuation at Q
  -> localization identification
  -> prime inertia <= valuation inertia
  -> translate the sheet condition I_val <= H
```

The second and third lines are independent.  The valuation comparison is
needed to connect the normalization diagram to the prime-inertia theorem; it
is not needed to prove the fixed-prime-inertia theorem itself.

## Section-by-section audit

### 1. Finite invariants and height

Source: `FixedRingLocalization.lean`, manuscript Section 2.

| Object | Disposition | Reason |
|---|---|---|
| `fixedPoints_hasGoingDown` | CORE | Supplies the invariant-specific going-down instance used by height transfer. |
| `primeHeight_under_le_of_hasGoingDown` | SUPPORT / PRIVATE REVIEW | Generic chain-height lemma used exactly once; either make it private or propose it upstream to Mathlib. |
| `fixedPoints_primeHeight_under_le` | SUPPORT | Thin specialization, but it keeps the public height-one proof readable. |
| `fixedPoints_primeHeight_under_eq_one` | CORE | Advertised result and direct input to the height-one descent. |
| `localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one` | CORE | Converts the geometric height-one condition to the exact local algebra required downstream. |

Decision: keep this chain.  It has one mathematical role per layer and no
semantic duplicate.  Do not replace it by a global `IsDedekindDomain`
assumption; the project rings can have dimension greater than one.

### 2. The selected local morphism

Source: `FixedRingUnramified.lean`, manuscript Section 3.

| Object | Disposition | Reason |
|---|---|---|
| `fixedPointsLocalRingHom` | CORE | The canonical arrow `(S^H)_{q_H} -> (S^I)_{q_I}`. |
| `fixedPointsLocalRingHom_isLocalHom` | SUPPORT | Needed by local unramified descent. |
| `fixedPointsLocalRingHom_injective` | SUPPORT | Needed to install faithful scalar action in the local tower. |
| `localRingHom_injective_of_injective` | SUPPORT/private | Correctly private; implementation only. |
| `formallyUnramified_localizationAtMaximalIdeal_iff` | SUPPORT/private | Correctly private; removes a localization-of-a-local-ring artifact. |

Decision: keep all five.  The public surface should emphasize only the map;
the locality and injectivity theorems are its two certified properties.

### 3. Conditional subgroup descent

Sources: `FixedRingUnramified.lean`, `FixedRingLocalization.lean`, manuscript
Section 4, and the root `Challenge.lean`/`Solution.lean` pair.

| Object | Disposition | Reason |
|---|---|---|
| `fixedRing_isUnramifiedAt_of_inertia_le_localized` | CORE | The actual local descent theorem. |
| `fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one` | CORE | The height-one wrapper and current Palomar-facing theorem. |
| `InertiaFixedRingUnramifiedAt` | TEMPORARY ADAPTER | One-field record wrapping one `Algebra.IsUnramifiedAt` proposition.  It names the current gap, but must not remain a required argument of the new self-contained endpoint.  After closure, prefer a direct proposition/alias or retain only as compatibility. |
| `fixedRing_isUnramifiedAt_of_inertia_le` | COMPAT | Global-Dedekind wrapper with no semantic caller outside verification.  The localized theorem supersedes it. |

Decision: the generic descent remains conditional.  Closing prime inertia
adds a new source theorem; it does not make the generic statement true
without `hI`.  Keep the current Challenge/Solution pair as a separate small
conditional package unless a new challenge statement is deliberately added.

### 4. Normal-closure and fixed-field models

Sources: `InvariantIntermediate.lean`, `FixedRingLocalization.lean`, and
manuscript Section 5.

| Object | Disposition | Reason |
|---|---|---|
| `normalClosureNormalizationRingActionHom` and its action instances | CORE | Installs the canonical Galois action used by prime inertia. |
| `FixedSubgroupNormalizationRing` | CORE | Stable name for the fixed normalization. |
| `fixedFieldNormalizationToFixedRing` | SUPPORT | Forward map used to build the equivalence. |
| `fixedFieldNormalizationEquivFixedRing` | CORE | Identifies the fixed ring with the integral closure in the fixed field. |
| `baseEquivFullInvariantNormalizationRing` | KEEP OUTSIDE FINAL SPINE | Correctly separates `B` from `S^G`, but has no production consumer.  Retain as an explicit transport theorem rather than silently inserting it into the `S^G` endpoint. |
| `fixedSubgroupNormalizationRing_localization_isDiscreteValuationRing` | ADAPTER / MERGE REVIEW | Mathematically useful specialization, but not used by the exact `S^G` endpoint.  Either give it a real downstream client or leave it out of the headline surface. |
| `fixedSubgroupNormalizationRing_isUnramifiedAt_of_inertia_le` | COMPAT | Based over `B`, whereas the literal fixed-inertia source is `S^G`; it has no semantic caller and is superseded by the exact full-invariant endpoint. |
| `intermediateNormalizationEquivFixedRing` and its coercion lemma | KEEP OUTSIDE THIS PAPER | Needed by the wider Hodge architecture, but not by the fixed-inertia proof. |

Decision: do not duplicate the normalization model.  The new DVR theorem
should use Mathlib's canonical integral-closure action and transport through
the existing fixed-field/fixed-ring equivalence.

### 5. Prime inertia

Source: `PrimeInertia.lean`, manuscript Section 5.1.

| Object | Disposition | Reason |
|---|---|---|
| `primeInertiaSubgroup` | CORE | Exact stabilizer-kernel subgroup. |
| `primeInertiaSubgroup_le_stabilizer` | SUPPORT | Used by the new unique-prime lemma. |
| `mem_primeInertiaSubgroup_iff` | CORE | Human-readable characterization and residue-action interface. |
| `mem_primeInertiaSubgroup_of_smul_sub_mem` | KEEP WITH OPTIONAL FORWARD BRANCH | Its sole semantic role is the Jacobian-inherited `I_val <= I_Q` comparison, not final descent. |
| `FullInvariantNormalizationRing` | CORE | Prevents the incorrect silent replacement `S^G = B`. |
| `normalizationPrimeInertiaGroup` | CORE | Exact normalization specialization. |
| `NormalizationPrimeInertiaFixedRingUnramifiedAt` | TEMPORARY GAP NAME | Currently names an external premise.  Replace its role with a proved theorem; retain an alias only if it improves statement readability. |
| `valuationInertia_sub_centerPrime` | KEEP OUTSIDE FINAL SPINE | Direct residue congruence inherited from the Jacobian architecture, but the descent endpoint does not consume this direction. |
| `valuationInertia_le_normalizationPrimeInertiaGroup` | OPTIONAL COMPARISON | Feeds equality corollaries only; it is not needed to turn `I_val <= H` into `I_Q <= H`. |

First new result, now added and compiled as
`eq_of_under_primeInertiaSubgroup_eq`:

```text
Q' under S^(I_Q) = Q under S^(I_Q)  ->  Q' = Q.
```

This unique-prime lemma uses only invariant-prime transitivity and
`primeInertiaSubgroup_le_stabilizer`; it needs no DVR, purity, or external
ramification theorem.

### 6. Valuation-to-prime localization bridge

Sources: `LocalizationBridge.lean`, the tail of `PrimeInertia.lean`, and
manuscript Section 6.

| Object | Disposition | Reason |
|---|---|---|
| `ValuationLocalizationAt` | CORE for diagram path | Records the compatible identification with the selected localization. |
| `HasValuationLocalizationAt` | ADAPTER | Useful `Prop` wrapper around existence of the datum. |
| `localRingEquivOfPrimeStabilizer` and its two comparison lemmas | SUPPORT | Implements transport of the action to the local ring. |
| `smul_mem_valuationRing_of_prime_stable` and `smul_valuationRing_eq_of_prime_stable` | SUPPORT | Internal action-compatibility steps. |
| `residue_localRingEquivOfPrimeInertia` | SUPPORT | Converts prime congruence into trivial residue action. |
| `ValuationLocalizationAt.primeInertia_le_valuationInertia` | CORE | Reverse containment after localization. |
| `Diagram.hasValuationLocalizationAt_of_isNoetherianRing` | CORE | Discharges the localization datum in the intended height-one setting. |
| `Diagram.valuationInertia_eq_normalizationPrimeInertiaGroup_of_isNoetherianRing` | OPTIONAL COMPARISON | Clean statement, but stronger than the containment used by descent and dependent on the unused forward branch. |
| `Diagram.normalizationPrimeInertia_le_of_valuationInertia_le_of_isNoetherianRing` | CORE | Exact arrow consumed by descent. |
| `primeCompl_map_eq_of_smul_eq` | INTERNALIZE REVIEW | Used only inside this bridge; consider making it private after the proof settles. |
| `ValuationLocalizationAt.toValuationCenteredAt` | COMPAT | No semantic caller; the diagram already supplies centeredness. |
| `PrimeInertiaComparisonAt` and the generic comparison wrappers | TEMPORARY COMPAT | This was the explicit reverse-containment input before the Noetherian localization theorem was proved.  Move it off the main proof path; keep only if a non-Noetherian client is identified. |
| `..._of_localization` wrapper variants | MERGE REVIEW | Preserve the direct localization theorem and the clean Noetherian endpoint; collapse intermediate record-assembly wrappers where they have no independent client. |

Decision: the conditional `PrimeInertiaComparisonAt` architecture was useful
scaffolding, but the Noetherian theorem now proves the required reverse
containment internally.  The main endpoint should compose that containment
directly with `I_val <= H`; neither the Jacobian-inherited forward direction
nor equality of the two inertia groups belongs in the shortest proof.

### 7. Composite normalization endpoints

Source: `PrimeInertiaDescent.lean`.

| Object | Disposition | Reason |
|---|---|---|
| `normalizationFixedRing_isUnramifiedAt_of_primeInertia_le` | TEMPORARY CONDITIONAL ENDPOINT | Correct today, but still takes the gap proposition.  Keep as a compatibility theorem with an explicit suffix after the unconditional theorem exists. |
| `Diagram.fixedRing_isUnramifiedAt_of_valuationInertia_le` | TEMPORARY CONDITIONAL ENDPOINT | Same issue at diagram level. |
| New prime-inertia height-one endpoint without `hI` | MISSING/CORE | The self-contained normalization theorem requested for the repository. |
| New diagram endpoint without `hI` | MISSING/CORE | Compose the proved prime-inertia theorem with the existing valuation comparison. |

Decision: migrate callers to the unconditional specializations, but do not
remove the generic conditional descent theorem.

### 8. Manuscript and research artifacts

| Artifact | Disposition | Reason |
|---|---|---|
| `research/archive/manuscripts/paper1.tex`, Sections 2--4 | ARCHIVED PROSE | Historical account of the compiled generic descent; current prose belongs in the technical appendix of `paper/main.tex`. |
| Section 5.1's “external input” discussion | REWRITE AFTER CLOSURE | It will be false as a description of the final repository once the DVR theorem is internal.  Keep the Stacks citations as provenance. |
| Section 6 valuation comparison | SLIM TO REVERSE CONTAINMENT | The current equality proof includes the Jacobian-inherited forward direction, but the diagram endpoint needs only `I_Q <= I_val <= H`. |
| `Challenge.lean` / `Solution.lean` | SEPARATE CONDITIONAL PACKAGE | Internally consistent and useful for Palomar, but not parity evidence for a new unconditional normalization result. |
| `research/inbox/PrimeInertiaScratch.lean` | RESEARCH/SUPERSEDED | Its two constructions have already been promoted to `PrimeInertia.lean`; retain only as history or mark archived. |
| `research/Verification.lean` | VERIFICATION INDEX | It intentionally keeps names alive and therefore must not be used to infer that a wrapper has a real client. |
| `GAP_MAP.md`, `CLAIM_LEDGER.md`, `SOURCE_LEDGER.md`, README files | ATOMIC PARITY UPDATE | Change their “external input open” status only after the new theorem compiles. |

### 9. Module and import parity

The production import chain is currently:

```text
PrimeInertiaDescent
|- FixedRingLocalization -> FixedRingUnramified
`- LocalizationBridge -> PrimeInertia -> FixedRingUnramified
```

| Import | Disposition | Reason |
|---|---|---|
| `FixedRingUnramified -> InvariantIntermediate` | REMOVE AFTER REWIRING | `FixedRingUnramified` uses no declaration from it.  `FixedRingLocalization` and `PrimeInertia` must then import their actual normalization dependency directly. |
| `SelectorComparison -> FixedRingUnramified` | REPLACE | `SelectorComparison` uses no fixed-ring-unramified declaration; import the actual normal-closure/sheet dependency instead. |
| Direct fixed-ring/prime-inertia imports in `Boundary.lean` | UMBRELLA REVIEW | Several are transitively implied by `PrimeInertiaDescent`.  Keeping explicit imports can be intentional for discoverability, so remove them only if the umbrella policy is “minimal imports.” |

Import counts alone do not decide theorem necessity.  They do expose accidental
coupling: the generic local-descent module should not import the entire
normal-closure model merely to reach Mathlib invariant-ring declarations.

## Missing proof objects: add only these

### Final-proof objects

1. **DONE:** unique prime over the contraction to the inertia-fixed ring.
2. A kernel-level inertia subgroup inside the decomposition group, together
   with proof that its ambient image is `primeInertiaSubgroup`.
3. The faithful action of decomposition modulo inertia on the relevant
   residue extension.
4. Cardinal identities connecting stabilizers, ramification indices, and
   inertia degrees.
5. Residue separability for the inertia-fixed intermediate normalization.
6. The DVR theorem proving ramification index one and hence
   `Algebra.IsUnramifiedAt`.
7. The height-one localization corollary producing the existing
   normalization gap proposition internally.

### Bridge-only objects

1. Kernel/image subgroup equivalences.
2. Fixed-ring/fixed-field transport equivalences.
3. Integral closure after localization at the contracted base prime.
4. Fixed points commuting with that base localization.
5. Equality of prime inertia before and after base localization.

These bridge objects should be private or placed in a clearly named local
module unless a second semantic client appears.

### Do not add

- A renamed opaque “DVR fixed-inertia input”.
- A new assumption equating inertia cardinality with ramification index.
- A global Dedekind-domain hypothesis on the original fixed rings.
- A claim that `Localization.AtPrime Q` is finite over the base localization
  when several primes lie over the base prime.
- The full arbitrary-ring `0BST` flat-base-change/product-splitting/fpqc
  apparatus during this closure pass.
- Purely inseparable residue-field infrastructure unless the faithful
  residue-action argument actually fails.
- A second valuation-inertia model; the current valuation comparison is
  already sufficient.

## Execution queue

- [x] **P0. Baseline.** Focused build of
  `PrimeInertiaDescent` and `Solution` succeeds.  Direct checks of
  `FixedRingUnramified`, `FixedRingLocalization`, `PrimeInertia`,
  `LocalizationBridge`, `PrimeInertiaDescent`, and `Solution` emit no
  compiler deprecation warnings.
- [x] **P1. Inventory.** Identify the current semantic spine and distinguish
  real callers from verification/manuscript references.
- [x] **P2. Unique-prime lemma.** Added and compiled
  `eq_of_under_primeInertiaSubgroup_eq`, with no domain, height, DVR,
  Noetherian, or module-finiteness assumptions.
- [ ] **P3. Kernel and residue action.** Add only the subgroup and faithful
  residue-action bridges required by the cardinal proof.
- [ ] **P4. DVR fixed-inertia theorem.** Prove the unramified consequence of
  Tag `09EH` for the canonical integral-closure action.
- [ ] **P5. Height-one transport.** Localize the normalization at the
  contracted base prime and transport fixed rings and inertia without a
  global dimension-one hypothesis.
- [ ] **P6. Endpoint migration.** Add unconditional normalization and diagram
  endpoints; keep generic arbitrary-`I` descent conditional.
- [ ] **P7. Compatibility/import pruning.** Move callers off the temporary
  premise record and `PrimeInertiaComparisonAt`, replace the two accidental
  imports above, and mark surviving wrappers deprecated only after the
  replacements compile.
- [ ] **P8. Manuscript parity.** Rewrite the introduction, prime-inertia
  subsection, formal-status section, conclusion, ledgers, and handoff notes
  in the same change that promotes the theorem.
- [ ] **P9. Release verification.** Run full build, verification file,
  `#print axioms`, `rg` for proof gaps, and manuscript build before promotion
  to `research/queue/`.

## Parity gates

Before any publication candidate is queued:

1. Every manuscript implication must name the exact Lean theorem that has the
   same hypotheses and conclusion.
2. A citation may explain provenance but may not be counted as a compiled
   proof dependency.
3. `B` and `S^G` must remain distinct unless the displayed base equivalence
   is explicitly transported.
4. Selected-prime unramifiedness must not be described as global etaleness.
5. Verification-only references must not prevent deprecation of a wrapper.
6. The generic conditional theorem and the normalization-specific
   unconditional theorem must not be conflated.
7. No “partial Hodge conjecture” language is permitted unless the endpoint
   actually constructs an algebraic cycle for a separately specified Hodge
   class.

## Current verdict

The existing height-one descent is not the part to prune: it is a compact,
well-factored result.  The main cleanup opportunity is to retire temporary
conditional interfaces after the missing prime-inertia theorem is proved.
The self-contained closure is feasible, but it is a medium-to-large
ramification formalization with nontrivial localization transport; it should
be implemented through the staged queue above rather than hidden behind one
new premise.
