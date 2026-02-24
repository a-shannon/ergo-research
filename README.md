# Ergo Cryptographic Research

[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

Open-source research papers on scaling zero-knowledge proofs, privacy protocols, and verifiable computation on the [Ergo](https://ergoplatform.org) blockchain.

## Papers

| # | Title | Date | PDF |
|---|-------|------|-----|
| 1 | **Scaling Zero-Knowledge Proofs on Ergo: Native secq256k1 Simulation and eUTXO Pipelining for Curve Trees** | Feb 2026 | [PDF](papers/curve-trees/ergo_curve_trees_research_paper.pdf) |

## Repository Structure

```
ergo-research/
├── README.md
├── LICENSE
└── papers/
    └── curve-trees/
    │   ├── ergo_curve_trees_research_paper.pdf   # Formal paper (print-ready)
    │   ├── ergo_curve_trees_research_paper.md     # Markdown source
    │   └── ergo_curve_trees_research_paper.html   # Browser version (MathJax)
    └── <future-paper>/
        ├── ...
```

## Research Areas

- **Zero-Knowledge Accumulators** — Curve Trees, Bulletproofs, membership proofs
- **Elliptic Curve Simulation** — Non-native curve arithmetic via `UnsignedBigInt`
- **eUTXO Computation Models** — Execution Pipelining, state continuation, permissionless cranking
- **Privacy Protocol Design** — Anonymity sets, MEV resilience, anti-griefing mechanisms

## Key Contributions

### Curve Trees on Ergo L1
Our first paper demonstrates that Ergo can natively verify Curve Tree membership proofs — one of the most advanced zero-knowledge accumulator constructions — **without any protocol modifications**. Key findings:

- **secq256k1 simulation** via Ergo 6.0's `UnsignedBigInt` modular arithmetic completes the 2-chain required for recursive proof composition
- **The eUTXO Affine Anomaly** — Ergo's JIT cost model makes Affine coordinates 35% cheaper than Jacobian, inverting standard cryptographic practice
- **Execution Pipelining** — A deterministic multi-block computation pattern that serializes 1.2 Billion JitCost across ~1,200 chained transactions
- **Permissionless Cranking** — MEV-incentivized relayers advance pipeline state, ensuring liveness without centralized operators

## Related Repositories

- [sigmastate-interpreter](https://github.com/a-shannon/sigmastate-interpreter) — Bulletproof verification implementation (PR to ergoplatform)
- [ergo-agent-sdk](https://github.com/a-shannon/ergo-agent-sdk) — Python SDK for AI agents on Ergo

## Author

**A. Shannon** — Independent cryptographic researcher focused on the Ergo ecosystem.

## License

This work is licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/). You are free to share and adapt this material for any purpose, provided you give appropriate credit.
