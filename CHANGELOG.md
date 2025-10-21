# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2025-10-21

### Added
- Affine solution counting for inhomogeneous linear systems over finite fields
- Proof that affine solution sets are translates of kernel solutions
- Explicit cardinality formula: |solutions| = |K|^(n - rank(A))
- Column vector variants for standard matrix equations (A*v = b)
- Bijection proofs via matrix transpose for column vectors
- Concrete example for rank-1 systems (ax + by = z)

## [0.1.0] - 2025-10-18

### Added
- Initial release of rocq-rouche-capelli
- Formal proof of the Rouché–Capelli theorem
- Complete formalization using Rocq Mathematical Components
- Support for Rocq Core 9.0.0 and Mathematical Components 2.4.0

[0.2.0]: https://github.com/weng-chenghui/rocq-rouche-capelli/releases/tag/v0.2.0
[0.1.0]: https://github.com/weng-chenghui/rocq-rouche-capelli/releases/tag/v0.1.0

