# rocq-rouche-capelli

A formal proof of the Rouché–Capelli theorem using [Rocq Prover](https://rocq-prover.org/) and the [Mathematical Components](https://math-comp.github.io/) library.

## Overview

The Rouché–Capelli theorem (also known as the Kronecker–Capelli theorem) is a fundamental result in linear algebra that provides necessary and sufficient conditions for a system of linear equations to have solutions. This project provides a machine-checked proof of this theorem.

## Installation

### Via opam

Once published, you can install this package using opam:

```bash
opam install rocq-rouche-capelli
```

### Building from Source

#### Dependencies

- OCaml (>= 4.14.0)
- Rocq Core (= 9.0.0)
- Rocq Mathematical Components:
  - ssreflect (= 2.4.0)
  - algebra (= 2.4.0)
  - field (= 2.4.0)
  - fingroup (= 2.4.0)
  - finmap (>= 2.1.0)
  - solvable (= 2.4.0)
- Coq Mathematical Components Classical (= 1.13.0)

#### Build Instructions

```bash
# Clone the repository
git clone https://github.com/weng-chenghui/rocq-rouche-capelli.git
cd rocq-rouche-capelli

# Install dependencies
opam install . --deps-only

# Build the project
make

# Install (optional)
make install
```

## Contents

The main proof is located in:
- [`src/rouche_capelli_v_jq.v`](src/rouche_capelli_v_jq.v) - Formal proof of the Rouché–Capelli theorem

## Documentation

For additional documentation and development guidelines, see the [`docs/`](docs/) directory.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests on [GitHub](https://github.com/weng-chenghui/rocq-rouche-capelli).

## Authors

- Cheng-Hui Weng
- Reynald Affeldt
- Jacques Garrigue
- Takafumi Saikawa

