# Rocq formalization of the Reuse theorem

A Rocq mechanization of the paper's Reuse theorem for bounded Signal
Temporal Logic over a *metric chain*: a differentiable logic whose window
reductions admit weakening exactly and contraction up to δ interprets
bounded STL within `B = δ_atom + δ∧·d∧ + δ∨·d∨` of its idempotent
(lattice) shadow.

## Building

Pinned toolchain via Nix (Rocq 9.1, MathComp 2.5, mathcomp-analysis 1.16):

```
nix-build
```

Or with an existing opam switch providing the same versions:

```
eval $(opam env)
make
```

## Files

| File | Contents |
|---|---|
| `BoundedSTL.v` | The shared bounded-STL vocabulary: syntax `form`, Boolean semantics `sat` (until is the Maler–Ničković strong until), Donzé–Maler reference robustness `rho` with its sign-soundness `rho_sound`, the reduction-nesting depth/window measures `dconj`/`ddisj`/`maxwin`, and the head-form min/max reductions `rmin`/`rmax` of nonempty real sequences (membership, bounds, pointwise non-expansiveness, behaviour under negation/concatenation/padding) they rest on. |
| `MetricChains.v` | HB structure `metricChainType R d`: a mathcomp total order with an `R`-valued distance, symmetric/triangular/reflexive and **order-convex** (the only metric–order interaction the proof needs; Birkhoff non-expansiveness of min/max is derived from it). Generic instances make every `realDomainType`/`realFieldType` a metric chain with `d(x,y) = |x−y|`. Head-form window folds `minS`/`maxS` and their non-expansiveness, involution theory (antitone involutive isometries), and the **defect builders** `monoid_window_bound`(`_max`): a monotone sub-meet (dually super-join) operator deviates from the strict window reduction by at most its W-th **idempotency defect** `sup_x d(x^{⊗W}, x)`. |
| `ReuseTheorem.v` | The theorem. Reference semantics `rhoL` into the lattice reduct (min/max/involution `ineg`), satisfaction threshold θ = the involution's fixpoint, sign-soundness `rhoL_sound`, DL semantics `evalL` (exact §5.1 windows, no padding), `reuse_quantitative` (`cdist (evalL Φ) (rhoL Φ) ≤ Bdef`), and the boolean parts in **separation form**: a DL value whose closed B-ball clears θ decides satisfaction. No σ: a σ=− DL is the same instance in the flipped orientation, absorbed by the involution. The bounded-STL vocabulary comes from `BoundedSTL.v`. |
| `ReuseInstances.v` | `real_sep`: on real chains the separation premise is literally the margin `θ + B < value`. **Gödel/STL** (exact reductions, ¬ = −x, θ = 0, δ = 0 ⟹ B = δ_atom). **Kleene–Zadeh** (min/max/1−x on [0,1], θ = ½, all-zero slacks — the bounded De Morgan counterexample: exact reductions *and* an involutive negation, in a non-residuated algebra). **Łukasiewicz** via the defect builder with δ = 1 − 1/W (honest but order-1: Łukasiewicz is not n-contractive). **DL2** non-instance: `+` has unbounded idempotency defect already on the constant 2-window — the paper's DL2 exclusion as a theorem. |
| `ReuseQLL.v` | Log-sum-exp at sharpness p: monotone and sub-meet on **all** of ℝ (`inrange := predT`), self-power computed **exactly** (`x − ln(n+1)/p`), so the window deviation is `ln W / p` — the paper's δ, *derived* from the builder rather than assumed. Final corollary `qll_quantitative`: `B = δ_atom + (ln W / p) *+ (d∧ + d∨)`, the paper's Section-"Instantiations" formula. |

### Axiom audit (`Print Assumptions`)

`reuse_quantitative`, `reuse_boolean_sat`, `monoid_window_bound`,
`godel_quantitative`, `kleene_zadeh_sound`, `luk_window_bound`,
`dl2_no_finite_defect`: **closed under the global context** (no
axioms at all). `qll_quantitative`: only the three `boolp` classical
axioms that come with mathcomp-analysis's `realType` (needed for
`expR`/`ln`).

### Design notes

- The involution and threshold are *section parameters*, not part of
  the HB structure: one carrier supports several involutions (−x and
  1−x on ℝ), so they cannot be canonical per type.
- The generic `metricChainType` instances are keyed on the sorts of
  `realDomainType`/`realFieldType`/`realType` (the last declared in
  `ReuseQLL.v`) and marked `#[non_forgetful_inheritance]` — the
  metric is derived data with no competing inheritance path.
- The residuum `→` of a residuated lattice is never used by the
  proof; what the theorem consumes is the lattice reduct, an
  involution, and a compatible distance. The monoidal (⊗) structure
  lives entirely on the *instance* side, where the defect builder
  turns "monotone + integral + bounded contraction defect" into the
  theorem's window condition. In substructural terms: R1 = exchange/
  monotonicity, unit laws = weakening, the defect = quantitative
  contraction.
