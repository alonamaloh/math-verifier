# Language documentation

The language documentation has three canonical entry points:

- [`docs/tutorial.md`](docs/tutorial.md) is the example-driven introduction.
- [`docs/reference.md`](docs/reference.md) catalogues supported surface forms.
- [`docs/style.md`](docs/style.md) explains how library proofs should read.

These documents describe the current math-facing language. Historical plans
and implementation notes are not syntax references.

For a mathematical library area, begin with its brief README:

- [`library/README.md`](library/README.md) maps the whole library.
- `library/<Area>/README.md` lists the area’s public definitions, important
  theorems, imports, and abstraction rules.

Focused advanced notes live in `docs/conventions/`:

- [`relation-chains.md`](docs/conventions/relation-chains.md)
- [`algebra-tactics.md`](docs/conventions/algebra-tactics.md)
- [`quotients.md`](docs/conventions/quotients.md)
- [`structures-and-inference.md`](docs/conventions/structures-and-inference.md)
- [`numerals-and-naming.md`](docs/conventions/numerals-and-naming.md)
- [`opaque.md`](docs/conventions/opaque.md)
- [`build-and-layout.md`](docs/conventions/build-and-layout.md)

The examples use proof forms exercised by files in the clean manifest.

Build the library with:

```sh
make -j 16 library
```

Build the language feature tests with:

```sh
make -j 16 tests
```
