import HodgeConjecture.Inputs.FixedInertia
import HodgeConjecture.Inputs.FiniteEtaleExtension
import HodgeConjecture.Inputs.ChowLocalization

/-!
# Explicit literature-input packages

These modules name selected conclusions needed from external geometric
theorems. They introduce no project axioms or default instances asserting
those conclusions. Every consumer writes its required source input in its
own signature, as a named argument or a local hypothesis-class binder.

The three source topics stay separate: selected fixed-inertia
unramifiedness, finite-étale cover/deck extension, and additive Chow
localization. The inertia package preserves its existing declaration and
the unbundled Palomar statement. Cover existence and automorphism lifting
are separate hypotheses. Chow exactness supplies raw lifts and conditional
boundary support; it does not supply multiplicative restriction or defect
vanishing.

Matching the full cited theorem's geometric assumptions remains a task for
each application. Compactified Chow comparison, residual realization, and
class-dependent coverage are not fields of a blanket literature hypothesis.
The broad historical normalization-triviality package is not imported here.
-/
