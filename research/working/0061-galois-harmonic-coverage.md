# Galois coefficient descent and harmonic transport (2026-11-26)

The new adapters feed the existing finite coverage certificate for a fixed
rational Hodge target. The complete target basis, actual Chow module and
original cycle map remain the public parameters. Coverage is obtained from
the existing exact arithmetic checker after the new proof gates are met.

`LinearAlgebra/GaloisDescent.lean` adapts
`GaloisObstructionTheory/Jacobian/General/Galois/TensorInvariants.lean`
from the sibling `galois-obstruction-theory` repository. Its source SHA-256 is
`ce099a1f1cb419ec4a7ddce7ee0aa30559cdbc6b9ba8d6f112bdeeaec35778b8`.
The full MIT notice from `Jacobian/LICENSE` is retained in the new file.
The algebra statement is generalized to arbitrary vector spaces, so a Chow
module needs no additional multiplication structure.

`LinearAlgebra/Harmonic/Morphism.lean` adapts
`GaloisObstructionTheory/Homotopical/Sheaf/Morphism.lean`, source SHA-256
`07b10080516a939afdad2e8bb45ce38821d598ec1f7f231c537e28bdc22eabd3`.
`LinearAlgebra/Harmonic/HarmonicCohomology.lean` adapts
`GaloisObstructionTheory/Homotopical/Sheaf/HarmonicCohomology.lean`, source SHA-256
`bccd03005c0c82becb49c8bb11311b2fe7e39d76ff51e5c10eacae6c1f47213d`.
Both come from the same sibling repository, retain the attributed copyright
headers, and preserve the MIT notice and permission in
`LinearAlgebra/Harmonic/LICENSE`. Their bridges to the existing quotient and
the rational witness transport are documented explicitly in the local files.

For a finite Galois extension `N/K`, `tensorInclude` sends `v` to `1 ⊗ v`.
`mem_range_tensorInclude_iff_fixed` identifies its range with tensors fixed
by every `scalarAction` on the coefficient factor. `descendFixed` recovers
the unique original vector, with inclusion and uniqueness theorems. Inclusion
is injective for any field extension; fixed-tensor descent uses the finite
Galois hypotheses.

`Realization/Chow/GaloisHarmonicCoverage.lean` applies this result to the
existing rational Chow module. `extendedCycleClass` is exactly the tensor
extension of the original cycle map. `of_galois_fixed` requires invariant
cycle tensors and exact extended column identities. It descends the tensors
to actual original Chow classes, then uses scalar-inclusion injectivity to
recover their original cycle-class column bindings.

The harmonic side uses the actual finite real cellular differentials.
`CohomologyOne` is the native kernel/range quotient; its comparison with the
existing closed-cochain quotient is a linear equivalence. The equivalence
`cohomologyOneEquivHarmonic` selects harmonic representatives. Cellular
morphisms induce quotient maps, and a symmetric degree-one endomorphism
satisfies `cohomologyOneEquivHarmonic_naturality`.

`transportHarmonicWitness` is defined through this quotient and comparison.
`of_transported_harmonic` requires symmetry, exact differences of the raw
transformed witnesses, and injectivity of the transported witness map.
Symmetry does not imply injectivity. `of_galois_transported_harmonic` first
descends the invariant coefficient tensors, then binds the descended columns
through these faithful harmonic gates. Both factories produce the existing
certificate type and retain its original complete-target acceptance theorem.

`Realization/DeRham/ProjectiveLineGaloisCoverage.lean` uses the actual
quadratic field `ℚ(i)`, implemented by `GaloisDescent.Gaussian.Coefficients`, with
proved degree two and explicit conjugation. The invariant tensor is the
included ordinary infinity Chow class, and its descended class is exactly
that original class. A second aggregate uses multiplication by two on the
existing finite-cover cellular sheaf and its native cohomology quotient.
Both use the original P¹ Hodge basis and identity rank payload modulo three.
Conjugation moves the imaginary multiple of the nonzero infinity class.
The zero cellular endomorphism fails transported injectivity. These controls
exercise the two mandatory gates on the actual geometric instance.

The focused target `make check-galois-harmonic-coverage` runs the retained
arithmetic suite and the new descent/transport suite. The latter has
17 controls and 35 enforced standard-three axiom audits.

The construction descends scalar coefficients in a supplied Chow module.
It does not establish geometric Chow base change or automatically construct
spanning cycle families for general varieties. Real harmonic theory, Galois
coefficient fields and prime-field rank arithmetic retain distinct roles.
Extension-field batching, SNARK soundness and geometric byte codecs remain
separate obligations.

Validation on 2026-11-26: the new standalone verification passes all 17
controls and 35 audits with no errors or warnings. The retained aggregate
suite passes its ten controls, fifteen audits and runtime output
`(true, false)`. Thus 27 controls and 50 enforced axiom audits pass; every
audited dependency is among `propext`, `Classical.choice` and `Quot.sound`.
All 130 import guards pass. The public-library build passes 5,410 jobs,
and the complete root inventory passes with 1,858 nonempty standard-three
axiom lists plus one axiom-free report. All 740 active library/root/Solution
sources pass the scan excluding comments and strings; the two intentional
Challenge statement placeholders remain separate. Nonblocking style and
deprecation warnings in the wider library remain.

The canonical manuscript builds to 107 pages without overfull boxes or
undefined references. The new descent/transport pages and declaration
crosswalk were checked in rendered pages. Source hashes, retained MIT
notices, local file links and whitespace checks pass. These are cached
working-tree checks; clean-clone and human release sign-offs remain open.
