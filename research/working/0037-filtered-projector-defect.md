# The cyclic filtered detector of the existing projector defect

Date: 2026-11-08.

## Construction and detection

Keep the existing raw closure `C : AlgebraProjectorClosure G A e` and
`x : C.Closure`. In the same possibly noncommutative compactified algebra
A, put q = C.closureClass x and d = C.convolutionDefect x = q² − q.
No new defect or cycle-class image is substituted for d.

Use Mathlib's `Module.AEval ℚ A q`: the polynomial variable T acts on A
by left multiplication with q. The constructed object is the native cyclic
submodule

\[
 M_q=\mathbf Q[T]\cdot d\ \subset A,
 \qquad p(T)\cdot d=p(q)d.
\]

Its inclusion into A is rational linear and injective. The canonical
surjective presentation ℚ[T] → M_q sends p to p(q)d, and its degree
filtration is

\[
 F_nM_q=\operatorname{span}_{\mathbf Q}
       \{d,qd,\ldots,q^nd\},\qquad n\geq0.
\]

This is an increasing algebraic filtration. It is separate from the
decreasing Hodge filtration on the independently constructed Hodge target.
The native `IsModuleFiltration` interface records compatibility with
polynomial degree: a coefficient of degree at most m sends F_n into
F_(m+n). The stages are finite rational modules and exhaust M_q.
The cyclic module is finite and finitely presented over the Noetherian
ring ℚ[T], without finite-dimensionality or commutativity assumptions on A.

The proved detection statements are

\[
 M_q=0\ \Longleftrightarrow\ d=0
 \ \Longleftrightarrow\ q^2=q,
 \qquad F_nM_q=0\ \Longleftrightarrow\ d=0\quad(n\geq0).
\]

In Lean a zero module is expressed by `Subsingleton`. The proof retains
the distinguished original element d in F_0 and the injective inclusion;
no faithfulness of Betti realization or injectivity of a cycle-class map
is assumed. The native annihilator gives the exact relation test

\[
 p\in\operatorname{Ann}_{\mathbf Q[T]}(M_q)
 \ \Longleftrightarrow\ p(q)d=0.
\]

Its underlying submodule is precisely the kernel of the cyclic
presentation. Thus relations are the actual relations in A, rather than
formal free words or an assumed relation ideal.

## Existing restriction and Chow localization

The original algebra restriction r satisfies r(d)=0, and hence
r(p(q)d)=0 for every element of M_q. The range of its injective inclusion
lies in ker r, and restriction sends every filtration stage to zero.
The existing `ChowLocalization` package then places this whole range,
and each filtered image, in the additive boundary image. Its hypotheses
remain explicit for the actual maps. Multiplicative compatibility of a
geometric Chow restriction is not supplied by additive exactness alone.

If the detector is proved zero, the adapter produces the existing
`ZeroDefectWitness`, which the old `toAlgebraProjectorExtension` already
consumes. No second projector-extension record was created.

## Ownership and reuse

| Owner | Role |
| --- | --- |
| [Correspondence/FilteredProjectorDefect.lean](../../HodgeConjecture/Correspondence/FilteredProjectorDefect.lean) | Cyclic submodule, injective inclusion, finite presentation, degree filtration, native filtered-module instances, annihilator and detection. Imports only the existing elementary defect and Mathlib. |
| [Boundary/FilteredProjectorDefect.lean](../../HodgeConjecture/Boundary/FilteredProjectorDefect.lean) | Abbreviations specializing that same object to C.closureClass x; original restriction, kernel and extension-witness theorems. |
| [Inputs/ChowLocalization.lean](../../HodgeConjecture/Inputs/ChowLocalization.lean) | Existing localization interface and the new whole-module/filtered-stage boundary-image consequences. |

The module carrier is a native submodule, its action uses `Module.AEval`,
and its stages are images of `Polynomial.degreeLE` under the original
cyclic presentation. Finite generation, finite presentation and the
filtered-module interface reuse Mathlib. No new filtered-object record,
ambient algebra, boundary cycle or supported-cohomology carrier is added.

## What remains to connect to vanishing

The variable T acts by q; it is neither a geometric boundary equation nor
the twistor parameter λ in Yun's paper. No Rees family, connection, Hodge
filtration, mixed Hodge module, analytic comparison or zero-defect theorem
is constructed by naming this module. The affine module is finitely
presented, but a geometric coherent-sheaf or D-module identification is
still a separate construction.

The negative control uses A = ℚ[z], q = z and r = evaluation at z=0.
It is a legitimate raw closure of the zero projector. Its defect z²−z
is nonzero, F_0 is strictly smaller than F_1, and its ℚ[T]-annihilator
is zero, despite r killing the whole detector. Consequently geometric
restriction-zero does not imply vanishing or even polynomial-parameter
torsion. Replacing r by localization in T is not justified.

The repo's older product-algebra control q=(1,2), r=first projection,
has defect (0,2). Its detector is nonzero but is annihilated by T−2.
Thus the opposite behavior, a nonzero torsion detector, is also possible;
finite presentation supplies neither a connection nor torsion-freeness.
There is a concrete descent obstruction here: differentiating the relation
T−2 gives 1, which cannot annihilate that nonzero module. Thus polynomial
differentiation does not automatically descend through the cyclic
presentation. This is a mathematical deduction from the relation control,
not a newly installed connection theorem.

The construction is attached to the specified raw closure. Changing that
closure can change the module; finding an appropriate corrected closure
remains separate from detecting idempotence of the chosen class.

The next research task is to relate this exact detector, or an independently
proved sufficient quotient, to a geometric filtered construction with
boundary control. A connection or a comparison must be constructed on
the actual object; taking these as premises would leave the earlier gap
conditional. See the [vanishing comparison](0036-filtered-hodge-target-and-vanishing.md)
for the separate Chow-detection and boundary-direction obligations.

## Validation

The focused verification checks the nonzero polynomial raw closure,
strict growth of its filtration, zero annihilator and original restriction.
It also checks the old product-algebra detector and its nonzero annihilating
polynomial.
The positive control reuses the existing universal idempotent selector.
The noncommutative endomorphism algebra checks finite presentation and
finite filtration stages without adding commutativity. A scoped exact
kernel sequence tests the additive localization consumer; it is not
presented as a geometric Chow example.

The full library build passed (5,106 jobs). The new focused suite passed
30 axiom audits, and the unchanged Chow-localization suite passed its
20 audits and geometric regression examples. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted in those audits. All
import-boundary checks, local documentation links and `git diff --check`
passed. A focused root-import check confirmed export of all 15 new
inventory entries. Existing unrelated full-build and localization style warnings
retain their previous scope.
