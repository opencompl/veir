# QPFTypes

This is a library for defining coinductive types in Lean,
based heavily on [alexkeizer/QPFTypes](https://github.com/alexkeizer/QPFTypes).

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
