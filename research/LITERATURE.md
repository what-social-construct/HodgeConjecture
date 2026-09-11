# Literature and announcement audit

Last checked: 2026-09-05 (America/New_York).

This is a targeted source check, not an exhaustive priority search. It records
the closest verified literature found for the project's finite-group,
correspondence-projector, and modular-variety themes, and it separates public
evidence from same-day rumor.

## OpenAI/Hodge rumor assessment

No credible public evidence of an imminent OpenAI proof or announcement of the
Hodge conjecture was found as of the check date.

- The [OpenAI Research index](https://openai.com/research/index/) and
  [OpenAI research newsroom](https://openai.com/news/research/) had no Hodge
  conjecture item. Their visible latest entries were dated September 3, 2026.
- OpenAI's August 1 release,
  [“Ten advances in mathematics and theoretical computer science”](https://openai.com/index/ten-advances-in-mathematics/),
  names ten problems; the Hodge conjecture is not among them.
- The [Clay Mathematics Institute's Hodge conjecture page](https://www.claymath.org/millennium/hodge-conjecture/)
  still labels the problem “Unsolved” and says the dimension-four case is
  unknown.
- A same-day [r/math AI discussion thread](https://www.reddit.com/r/math/comments/1w84pqt/ai_in_mathematics_september_05_2026/)
  records shifting, unsourced speculation about an AI/Anthropic Millennium
  problem and Navier--Stokes. It does not supply a paper, proof, or official
  OpenAI Hodge announcement and is not authoritative evidence.

This conclusion is deliberately time-bounded: absence from current official
pages does not rule out a private result or a later announcement. It does mean
the rumor is not a sound reason to mislabel or rush the repository's claims.

## Closest verified prior art

| Work | Verified content relevant here | Relation to this repository |
| --- | --- | --- |
| A. J. Scholl, [“Motives for modular forms”](https://www.dpmms.cam.ac.uk/~ajs1005/preprints/mf.pdf), *Inventiones Mathematicae* 100 (1990), 419--430; [DOI](https://doi.org/10.1007/BF01231194) | Constructs the relevant modular-form cohomology using a projector in the group algebra of a finite group of automorphisms of a Kuga--Sato variety. | This is direct prior art for the mathematical theme “finite group action -> group-algebra projector -> cohomological/motivic summand.” It does not duplicate the Lean formalization or the repository's collision and boundary interfaces. |
| B. Brent Gordon and Jacob P. Murre, [“Chow motives of elliptic modular surfaces and threefolds”](https://arxiv.org/abs/alg-geom/9610007) (1996 preprint); published as “Chow motives of elliptic modular threefolds,” *J. Reine Angew. Math.* 514 (1999), 145--164 | Establishes Chow-motive and Chow--Künneth results in elliptic modular settings. | It is close prior art for concrete algebraic correspondence projectors on modular varieties, beyond the repository's presently abstract Chow-model interface. |
| B. Brent Gordon, Masaki Hanamura, and Jacob P. Murre, [“Chow--Künneth projectors for modular varieties”](https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.1016/S1631-073X%2802%2902506-2/), *C. R. Math.* 335 (2002), 745--750; [DOI](https://doi.org/10.1016/S1631-073X%2802%2902506-2) | Proves existence of mutually orthogonal Chow-correspondence idempotents giving the cohomological degree decomposition for certain varieties, including Kuga--Shimura varieties over Hilbert modular varieties. | This is close prior art for the intended Chow-projector endpoint. |
| Gordon--Hanamura--Murre, [“Relative Chow--Künneth projectors for modular varieties”](https://doi.org/10.1515/crll.2003.039), *J. Reine Angew. Math.* 558 (2003), 1--14, and [“Absolute Chow--Künneth projectors for modular varieties”](https://doi.org/10.1515/crll.2005.2005.580.139), *J. Reine Angew. Math.* 580 (2005), 139--155 | Develops relative and absolute Chow--Künneth projectors for modular varieties, including passage from relative geometry toward compactified absolute projectors under substantive hypotheses. | These works are particularly relevant to any future claim that the repository's abstract compactification interfaces give a new modular-variety theorem. |
| Jörg Wildeshaus, [*Intermediate extension of Chow motives of Abelian type*](https://arxiv.org/abs/1211.5327), *Advances in Mathematics* 305 (2017), 515--600 | In the Kuga-family/pure-Shimura/Baily--Borel setting, Theorem 0.1(d) says that idempotent endomorphisms of the relevant Abelian-type Chow-motive factor admit idempotent extensions to the motivic intermediate extension; Theorem 0.2 gives realization compatibility. | This is the closest located result to the repository's compactified-idempotent interface. It can support a special-case route only after the geometric objects and projector are identified with the theorem's hypotheses; it does not give the repository's abstract inertia criterion. |

The Stacks Project sources for the Noether different, clopen diagonal,
torsors, and purity are mapped declaration-by-declaration in
[`SOURCE_LEDGER.md`](SOURCE_LEDGER.md).

## Claim consequence

The verified literature already contains finite-group-algebra projectors on
Kuga--Sato varieties and Chow--Künneth projectors for modular varieties. On the
current tree, the defensible novelty claim is therefore a Lean formalization
and organization of collision, finite-étale correspondence, group/Hecke
projector, and boundary-obstruction mechanisms. A claim of a new Hodge case
would require a concrete new variety or class, construction of the actual
Chow realization, and proof that its action equals a separately prescribed
Hodge projector; those steps remain open in the claim ledger.
