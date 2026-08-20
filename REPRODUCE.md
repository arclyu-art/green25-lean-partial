# Reproducing the verification

Requirements: Lean 4.32.1 and a working Git installation. Lake resolves mathlib 4.32.1 from
`lakefile.toml`.

From the repository root:

```powershell
lake build
lake env lean Green25\Audit.lean
```

The first command should finish with `Build completed successfully`. The second prints the axiom
dependencies of the final theorem; the expected final entry is:

```text
'Green25.green25_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Optional finite regression audit:

```powershell
py -3 audit\code_coset_weight_audit.py
```

The finite computation is supporting evidence only. It is not used to prove the general theorem.

