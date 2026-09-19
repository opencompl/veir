# QPFTypes v1.0

> [!NOTE]
> This is a reimplementation of the QPFTypes project.

TODO: write an intro

## Differences with Previous QPFTypes

The main difference with the previous version is that v1.0 no longer provides a 
single `codata` or `data` command. The user is expected to explicitly define 
the base functor as a regular `inductive` type, which can automatically be shown 
to be a QPF via a new `deriving QPF` mechanism. The user then defines their final
(co)inductive type explicitly as a (co)fixpoint of this functor, in a regular
definition. A `@[qpf_type]` attribute is provided to automatically generate
constructors as before.

Further changes are:

* The theory of QPFs is now part of the QPFTypes library,
    removing the dependency on Mathlib.
* Live parameters are now encoded using the `liveParam` gadget, inspired by how
  `outParam` & co work for annotating parameters of a type class. Unannotated
  parameters are considered "dead" (i.e, non-functorial) by default.
* The theory of (selective) QPFs has been augmented with a partial ordering,
  so that corecursive functions can be defined via Lean's `partial_fixpoint`
  mechanism

## Acknowledgements

The theory of QPFs has been largely adapted from the relevant files in
[Mathlib](https://github.com/leanprover-community/mathlib4).
License and Authorship notices of those files have been preserved.
The theory of QPFs was first described by Jeremy Avigad, Mario Carneiro,
and Simon Hudon. [1]

The ordering on coinductive types that enables the CCPO structure is based on
discussions with Michael Sammler, and his
[coinductive](https://github.com/ISTA-PLV/coinductive) library.

## References

[1] Jeremy Avigad, Mario Carneiro, and Simon Hudon. "Data Types as Quotients of Polynomial Functors."
In *10th International Conference on Interactive Theorem Proving (ITP 2019)*,
Leibniz International Proceedings in Informatics (LIPIcs), vol. 141, pp. 6:1–6:19.
Schloss Dagstuhl – Leibniz-Zentrum für Informatik, 2019.
DOI: [10.4230/LIPIcs.ITP.2019.6](https://doi.org/10.4230/LIPIcs.ITP.2019.6)

[2] Alex C. Keizer. "Implementing a Definitional (Co)datatype Package in Lean 4, Based on
Quotients of Polynomial Functors." MSc thesis, Universiteit van Amsterdam, 2023.
Report MoL-2023-03. URL: <https://eprints.illc.uva.nl/id/eprint/2239/>
