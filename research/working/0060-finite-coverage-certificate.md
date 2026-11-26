# Exact finite coverage aggregates (2026-11-26)

The public subject is a fixed `RationalHodgeCycleClassModel M` and a basis of
its independently defined rational Hodge submodule. The selected cycle
family has exactly the complete basis index type. Each coordinate column
has a checked equality to the actual cycle image; harmonic exact-difference
certificates can construct these proof gates through a faithful realization.
Neither coverage nor surjectivity is stored as an assumption in the aggregate.

The finite arithmetic payload is a nonzero integer denominator `d`, an integer
square matrix `B`, a prime modulus, and a modular right inverse. The executable
checker requires exact rational binding `B_Q = d A`, the denominator gate,
primality and every entry of the right-inverse equation. A nonzero determinant
modulo the prime certifies a nonzero integer determinant, so `A` is surjective
over ℚ. The direction used for rank needs no integer entry-size bound. The
checker reduces `B` only; denominators may share the prime. Modular equality
is never used to infer the rational binding equation.

`FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check` proves that an
accepted, proof-bound aggregate represents every class of the fixed target
by a finite rational combination of the supplied actual cycles. The model
and complete basis remain public parameters. Thus a basis of only the cycle
image cannot be substituted for the independently defined Hodge target.

The P¹ instance uses the independently proved Betti coordinate, geometric
Hodge target, actual infinity Chow class and the existing cover-harmonic
realization. Its identity matrix and inverse modulo three pass the check,
and the fixed-model Hodge target follows through the aggregate theorem.

`make check-finite-coverage` runs ten controls and fifteen enforced axiom
audits. Controls reject composite moduli, wrong inverses, forged rational
bindings, singular matrices, and invalid geometric bindings. Fractional
coordinates and denominators divisible by the rank prime have positive
controls. The pure arithmetic checker is also executed on accepted and
forged payloads. Import guards keep it geometry-free and the generic
coverage layer independent of concrete realization modules.

This is the exact inner certificate, not a SNARK implementation. Arbitrary
geometric byte decoding, canonical profile/statement binding, constraint
compilation, cryptographic verification and its soundness proof remain separate
backend obligations. HCP's bundle and bounded-lift modules are useful patterns;
its SNARK interface alone does not supply those guarantees. The initial rank
payload uses selected square columns over a prime field. Extension-field
batching and rectangular certificates are not claimed here. General-variety
geometric comparisons and construction of spanning cycle families remain open.

Validation on 2026-11-26: `make check-finite-coverage` passes all ten controls,
fifteen enforced standard-three axiom audits, 126 import guards and the
runtime output `(true, false)`. The public-library build passes 5,399 jobs.
The complete root inventory passes: 1,858 nonempty axiom lists stay within
`propext`, `Classical.choice` and `Quot.sound`, and one further report is
axiom-free. All 733 active library/root/Solution sources pass the scan that
ignores comments and strings. The two intentional Challenge statement
placeholders remain separate. Nonblocking Lean style/deprecation warnings
remain.

The canonical manuscript builds to 106 pages without overfull boxes or
undefined references; the aggregate theorem, backend boundary and declaration
crosswalk were checked in rendered pages. Local file links and whitespace
checks pass. These are cached working-tree checks; clean-clone and human
release sign-offs remain open.
