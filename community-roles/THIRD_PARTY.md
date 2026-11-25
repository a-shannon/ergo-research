# Third-party components and terms

Both historical profiles use the local Cargo dependencies in `source/`.

* `vendor/dory/` contains `dory-pcs` 0.4.2 and its derive crate. The upstream version is tag `v0.4.2` at commit `5246da503c3e2c6baa40ec00d714987c73a3e6eb`. The crate declares `Apache-2.0 OR MIT`. [Dory source](https://github.com/a16z/dory/tree/5246da503c3e2c6baa40ec00d714987c73a3e6eb) · [Apache license](source/vendor/dory/LICENSE-APACHE) · [MIT license](source/vendor/dory/LICENSE-MIT)
* `vendor/header-core/` contains the prototype's Rust codec for canonical Ergo headers. Its consensus reference is the Ergo node at commit `8995ff243b140e7fe716bd3204423dd35690c2e4`. That repository publishes its material under CC0-1.0. [Reference node](https://github.com/ergoplatform/ergo/tree/8995ff243b140e7fe716bd3204423dd35690c2e4) · [Reference license](https://github.com/ergoplatform/ergo/blob/8995ff243b140e7fe716bd3204423dd35690c2e4/LICENSE)
* `vendor/r4-audit-coordinates/` contains the project's Rust implementation of work-coordinate derivation for the PoW audit.

The shared lockfile identifies the additional crates resolved by Cargo. Their respective packages carry their licensing terms. The project has yet to specify a license for its own Rust implementation. Obtain the author's terms before reusing that code outside technical review.
