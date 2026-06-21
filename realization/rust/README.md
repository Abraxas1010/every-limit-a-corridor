# Rust realization of the running-convergent construction

A second substrate (besides the cubical-Agda kernel) that *executes* the same
brackets and checks the same theorems the Agda proves, with exact
cross-multiplied integer arithmetic (never floating point).

```
rustc -O corridor_running.rs -o /tmp/corridor_running && /tmp/corridor_running
```

Mirrors `agda/corpus/cubical_agda/Corridor/Running/` one-for-one:
Cassini, the convergent bracket + Cassini-exact width, non-degeneracy, nesting,
forcing, the golden equation x²=x+1 (squeeze + exact integer identity), the
Dedekind cut `lo m < hi n` ∀m,n, and √2 via Pell. Aligned with heyting-imm
(cubical pin d684d7d8).
