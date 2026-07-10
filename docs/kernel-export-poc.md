# PLAN_KERNEL_EXPORT Stage-0 toolchain proof-of-concept — notes (2026-07-10)

Everything below was done under this directory (`.../scratchpad/lean-poc/`); the math repo was not touched.

## Headline surprise

**The "lean4export text format" no longer exists upstream.** lean4export transitioned to an
**NDJSON format (format version 3.1.0)** in commit `c840756` (authored by **ammkrn** himself,
Dec 13 2025), first shipped in tag `v4.28.0-rc1`. The last tag with the classic line-based text
format is `v4.27.0-rc1`. ammkrn's checker (nanoda_lib) now consumes the NDJSON format directly
(accepts format versions `>= 3.1.0, < 3.2.0` — `src/parser.rs:22-23`). PLAN_KERNEL_EXPORT.md's
§A item 2 should target **NDJSON 3.1.0**, not the old text format. This is good news for us:
JSON lines with explicit back-reference indices and decimal-string Nat literals are easier to
emit correctly than the positional text format.

## (a) Versions

| component | version |
|---|---|
| elan | 4.2.3 (b6cec7e10 2026-06-08), `ELAN_HOME=lean-poc/elan-home` |
| Lean | **4.31.0**, githash `68218e876d2a38b1985b8590fff244a83c321783` (`leanprover/lean4:v4.31.0`) |
| lean4export | tag `v4.31.0` (commit `8554815`), exporter self-reports version **3.1.0** |
| export format | **3.1.0** (meta line: `{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{...}}}`) |
| nanoda_lib | 0.4.10-beta (master `f58f2f6`), binary target `nanoda_bin` |
| Rust for nanoda | rustc/cargo **1.97.0** via user-local rustup (system 1.75 too old: can't read Cargo.lock v4) |
| lean4lean | master `8865b15`, pins `leanprover/lean4:v4.29.0` |

## (b) Producing an export file

```sh
export ELAN_HOME=.../lean-poc/elan-home; export PATH=$ELAN_HOME/bin:$PATH

# build the exporter (in lean4export/ at tag v4.31.0)
lake build                       # -> .lake/build/bin/lean4export

# in the target project (pocproj/, lean-toolchain = v4.31.0)
lake build
lake env ../lean4export/.lake/build/bin/lean4export Poc > Poc.ndjson

# selective export: only the listed decls + their transitive dependency closure
lake env ../lean4export/.lake/build/bin/lean4export Poc -- big_sum parity_zero_two > Poc.selective.ndjson
```

Options: `--export-unsafe` (include unsafe decls), `--export-mdata` (keep `Expr.mdata`; stripped by default).

**Memory-cap gotcha:** `ulimit -v 8000000` (8 GB virtual) makes Lean die with
"failed to create thread" — Lean reserves large per-thread virtual address space.
**16 GB virtual (`ulimit -v 16000000`) works** for all Lean/lake steps here; actual RSS stayed under 1 GB.

## (c) Export size / item counts (trivial library + Init prelude closure)

Test library `pocproj/Poc.lean` (14 decls): Nat defs/theorems, one inductive (`Tree`) with
recursion, a 39-digit Nat literal + `by decide` arithmetic on it, a `Quot` (`Parity` =
Nat mod parity, `Quot.mk`/`Quot.sound`), an `And` swap, an `Iff` from propositional `Eq`.

Full export `lean4export Poc` (module + transitive deps = whole Init prelude closure):

- **344,480,246 bytes (~344 MB), 6,429,693 NDJSON lines**; export took **10.2 s**, max RSS 962 MB.
- Item counts: expr 6,077,641 · name 294,211 · level 575 · `thm` 41,419 · `def` 14,908 ·
  `inductive` groups 609 · `opaque` 318 · `axiom` 7 · `quot` 4 · `meta` 1.
- Expr kinds: app 5,170,323 · lam 534,574 · forallE 299,415 · const 56,377 · letE 11,258 ·
  proj 3,402 · strVal 1,783 · natVal 249 · bvar 138 · sort 122.
- Axioms present in the Init closure: `propext`, `Classical.choice`, `Quot.sound`,
  `Lean.trustCompiler`, `Lean.ofReduceNat`, `Lean.ofReduceBool`, and `sorryAx`
  (declared by the prelude, used by nothing).

**Selective export** (`-- big_sum parity_zero_two`): **368 KB, 6,821 lines, 147 def/thm items** —
the dependency closure only. So an export trail for a single theorem is ~1000x smaller than
module export; very relevant for CI granularity.

## (d) External checker: nanoda

Build (needs Rust >= ~1.78 for lockfile v4; used 1.97 via user-local rustup):

```sh
cargo build --release --bin nanoda_bin     # 10.7 s, ~1.3 MB binary
```

No CLI flags — it takes a single JSON config file (`nanoda-config.json` here):

```json
{
    "export_file_path": ".../pocproj/Poc.ndjson",
    "use_stdin": false,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound",
                         "Lean.trustCompiler", "Lean.ofReduceNat", "Lean.ofReduceBool"],
    "unpermitted_axiom_hard_error": false,
    "nat_extension": true,
    "string_extension": true,
    "pp_declars": ["double_add", "bigNumber", "parity_zero_two", "and_swap"],
    "pp_to_stdout": true,
    "print_success_message": true
}
```

Invocation and result:

```sh
./nanoda_lib/target/release/nanoda_bin nanoda-config.json
# real 23.06s  user 22.92s  (single-threaded; RSS well under the 16 GB cap)  exit 0
```

Report format (sample, verbatim): requested decls pretty-printed with `_` proof bodies,
then every axiom admitted to the environment with its full statement, then a one-line verdict:

```
theorem double_add (m n : Nat) : Eq (double (HAdd.hAdd m n)) (HAdd.hAdd (double m) (double n)) := _
def bigNumber : Nat := OfNat.ofNat 123456789012345678901234567890123456789
theorem parity_zero_two : Eq (Parity.mk (OfNat.ofNat 0)) (Parity.mk (OfNat.ofNat 2)) := _
...
axiom Classical.choice.{u} {α : Sort u} : Nonempty α → α
axiom propext {a b : Prop} : Iff a b → Eq a b
axiom Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} : r a b → Eq (Quot.mk r a) (Quot.mk r b)
axiom Lean.trustCompiler : True
axiom Lean.ofReduceNat (a b : Nat) : Eq (Lean.reduceNat a) b → Eq a b
axiom Lean.ofReduceBool (a b : Bool) : Eq (Lean.reduceBool a) b → Eq a b

Checked 58703 declarations with no errors, skipping exported but unpermitted axioms ["sorryAx"]
```

Axiom policy knobs: `permitted_axioms` allowlist; `unpermitted_axiom_hard_error: false` skips
unlisted axioms (hard error only if something *uses* one — this is what lets `sorryAx` pass
harmlessly); `unsafe_permit_all_axioms` exists for debugging. The Nat/String kernel extensions
(GMP-style literal arithmetic) are **off by default**; `"nat_extension": true` is required for
any realistic prelude closure. Exit code is the machine-readable success signal
(`print_success_message: false` for silent CI use).

## (e) lean4lean verdict

- Builds fine: pins Lean v4.29.0; `lake build lean4lean` (CLI target only, skips the metatheory
  proofs) completed in a few minutes; binary at `.lake/build/bin/lean4lean`.
- **It has no lean4export frontend.** It consumes **.olean module data** off the Lean search
  path (`readModuleDataParts` / `importModulesCore` in `Main.lean`); usage is
  `lake env .lake/build/bin/lean4lean [--fresh] [MOD]` inside a Lean package. So it can
  re-check *Lean* libraries, but cannot check *our* exporter's output. Not a candidate for our
  external-checker slot; nanoda is.
- Runtime gotcha: it **segfaults immediately without `ulimit -s unlimited`** (deep recursion,
  stack overflow); with unlimited stack it checked `Init.Data.Nat.Basic` fine.

## (f) Format facts relevant to writing our own exporter (NDJSON 3.1.0)

Spec: `lean4export/format_ndjson.md` (at tag v4.31.0). One JSON object per line, no line breaks
inside an object. First line is the `meta` object (exporter name/version, lean githash/version,
format version — nanoda semver-checks it and rejects `>= 3.2.0` or `< 3.1.0`).

- **Back-references**: three separate index namespaces, assigned by the keys
  `"in"` (name), `"il"` (level), `"ie"` (expr). Reserved: **name 0 = anonymous**,
  **level 0 = Level.zero** (never explicitly assigned in the file). Exprs have *no* reserved
  index — the first expr is explicitly assigned `"ie": 0`. Indices must be assigned before use;
  duplicates are a parse error (lean4export's own test parser rejects them).
- **Names**: `{"in":k, "str":{"pre":j, "str":"..."}}` and `{"in":k, "num":{"pre":j, "i":n}}`.
- **Levels**: `succ` (int), `max`/`imax` (`[int,int]`), `param` (name index).
- **Exprs**: `bvar` (de Bruijn int), `sort` (level idx), `const` (`{"name":n,"us":[levels]}`),
  `app` (`{"fn":i,"arg":j}`), `lam`/`forallE` (`{"name","type","body","binderInfo"}` with
  binderInfo one of `"default"|"implicit"|"strictImplicit"|"instImplicit"`),
  `letE` (`{"name","type","value","body","nondep":bool}`), `proj`
  (`{"typeName","idx","struct"}`), `natVal`, `strVal`, `mdata` (stripped by default).
- **Nat literals**: `{"ie":N, "natVal":"<decimal string>"}` — arbitrary-precision decimal
  **string**, e.g. our 39-digit test literal appears verbatim as
  `{"ie":3167248,"natVal":"123456789012345678901234567890123456789"}`. Our GMP `NaturalLiteral`
  kernel node maps directly onto this. The checker side needs the Nat kernel extension enabled
  to reduce them.
- **Declarations**: `axiom`, `def` (with reducibility `hints`: `"opaque"|"abbrev"|{"regular":n}`,
  and `safety`), `thm`, `opaque`, `quot`, `inductive`. `def`/`thm`/`opaque` carry an `all`
  array (mutual group). Level params are name indices.
- **#QUOT handling**: the kernel-side input is the field-less `quotDecl`, but the export
  materializes **four `quot` items** with `"kind": "type" | "ctor" | "lift" | "ind"`
  (Quot / Quot.mk / Quot.lift / Quot.ind), each with name/levelParams/full type. Since
  commit `706c92f`, lean4export also always exports `Eq` alongside the Quot package (the
  quotient typing rules mention it). `Quot.sound` is a plain `axiom`.
- **And/Iff recursors**: `And` and `Iff` export as ordinary single-inductive groups
  `{"inductive":{"types":[...],"ctors":[And.intro],"recs":[And.rec]}}` — and the recursors are
  **included in the file**, each with **one universe level parameter** (`And.rec.{u}`,
  `Iff.rec.{u}`, exactly like `Nat.rec.{u}`): subsingleton (large) elimination appears as
  ordinary universe polymorphism of the exported recursor, not as any special flag. The format
  doc explicitly says recursor data is redundant-for-checkers (a real checker like nanoda
  rederives/validates recursors from the inductive spec); it is included for tooling.
  RecursorVal carries `numParams/numIndices/numMotives/numMinors`, `rules`
  (`{"ctor","nfields","rhs"}` per constructor) and the `k : bool` K-like-reduction flag.
- **Grouping**: related inductive types + ctors + recs are emitted together in one line
  (also for mutual groups); mutual def/thm groups are tied by `all`.
- **Prelude closure is unavoidable for module export** (~58.7k checked declarations, 344 MB for
  anything importing Init), but the `-- <decl names>` selective mode emits just the dependency
  cone (368 KB for two theorems). For our exporter the analogous choice is ours to make; nanoda
  is happy either way as long as every referenced constant is declared before use.

## Directory map (all under scratchpad/lean-poc/)

- `elan-home/` — elan + Lean v4.31.0 toolchain (`export ELAN_HOME=...; PATH=$ELAN_HOME/bin:$PATH`)
- `lean4export/` — at tag v4.31.0, built (`.lake/build/bin/lean4export`)
- `pocproj/` — trivial library (`Poc.lean`), `Poc.ndjson` (344 MB), `Poc.selective.ndjson` (368 KB)
- `rustup-home/`, `cargo-home/` — user-local Rust 1.97
- `nanoda_lib/` — master f58f2f6, built (`target/release/nanoda_bin`)
- `nanoda-config.json` — the config used for the successful replay
- `lean4lean/` — master 8865b15, CLI built (olean checker only)
