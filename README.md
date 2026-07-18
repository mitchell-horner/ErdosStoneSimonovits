# Formalising the Erdős-Stone-Simonovits theorem and the Kővári-Sós-Turán theorem in Lean

[![Lean Action CI](https://github.com/mitchell-horner/ErdosStoneSimonovitsKovariSosTuran/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mitchell-horner/ErdosStoneSimonovitsKovariSosTuran/actions/workflows/lean_action_ci.yml)

This repository contains a formalisation of the Erdős-Stone-Simonovits theorem and the Kővári-Sós-Turán theorem in [Lean](https://lean-lang.org/). The statements of the results are as follows:

**The Erdős-Stone theorem (minimal degree version)**

Suppose $\varepsilon > 0$ is a positive real number, $r$ and $t$ are natural numbers, and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the minimal degree $\delta(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)v(G)$, then $G$ contains a copy of the complete equipartite graph $K_{r+1}(t)$.

```lean
theorem eventually_completeEquipartiteGraph_isContained_of_minDegree
  {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
  ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
    G.minDegree ≥ (1 - 1 / r + ε) * n
      → completeEquipartiteGraph (r + 1) t ⊑ G
```

**The Erdős-Stone theorem**

Suppose $\varepsilon > 0$ is a positive real number, $r$ and $t$ are natural numbers, and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the number of edges $e(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)\frac{v(G)^2}{2}$, then $G$ contains a copy of the complete equipartite graph $K_{r+1}(t)$.

```lean
theorem eventually_completeEquipartiteGraph_isContained_of_card_edgeFinset
  {ε : ℝ} (hε_pos : 0 < ε) (r t : ℕ) :
  ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
    #G.edgeFinset ≥ (1 - 1 / r + ε) * n ^ 2 / 2
    → completeEquipartiteGraph (r + 1) t ⊑ G
```

**The Erdős-Stone theorem (colorable subgraph version)**

Suppose $\varepsilon > 0$ is a positive real number and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the number of edges $e(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)\frac{v(G)^2}{2}$, then $G$ contains a copy of any $r+1$-colorable simple graph $H$.

```lean
theorem eventually_isContained_of_card_edgeFinset_of_colorable
  {r : ℕ} (hc : H.Colorable (r + 1)) {ε : ℝ} (hε_pos : 0 < ε) :
  ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
    #G.edgeFinset ≥ (1 - 1 / r + ε) * n ^ 2 / 2 → H ⊑ G
```

**The Erdős-Stone-Simonovits theorem**

Suppose $H$ is a simple graph and $\varepsilon > 0$ is a positive real number. If the chromatic number $\chi(H) = r+1 > 1$, then the extremal numbers of $H$ satisfy

$$
\left( 1-\frac{1}{r}-\varepsilon \right) \frac{n^2}{2} \leq \textrm{ex}(n, H) \leq \left( 1-\frac{1}{r}+\varepsilon \right) \frac{n^2}{2}
$$ 

for sufficiently large $n$.

```lean
theorem eventually_le_extremalNumber_le_of_chromaticNumber {ε : ℝ} (hε : 0 < ε)
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
  ∀ᶠ n in atTop, (1 - 1 / r - ε) * n ^ 2 / 2 < extremalNumber n H ∧
    extremalNumber n H ≤ (1 - 1 / r + ε) * n ^ 2 / 2
```

**The Erdős-Stone-Simonovits theorem (little-O version)**

Suppose $H$ is a simple graph. If the chromatic number $\chi(H) = r+1 > 1$, then the extremal numbers of $H$ satisfy

$$
\textrm{ex}(n, H) = \left( 1-\frac{1}{r} + o(1) \right) \frac{n^2}{2}
$$

as $n \rightarrow \infty$.

```lean
theorem isLittleO_extremalNumber_of_chromaticNumber
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
  (fun (n : ℕ) ↦ (extremalNumber n H - (1 - 1 / r) * n ^ 2 / 2 : ℝ))
    =o[atTop] (fun (n : ℕ) ↦ (n ^ 2 : ℝ))
```

**The Erdős-Stone-Simonovits theorem (Turán density version)**

Suppose $H$ is a simple graph. If the chromatic number $\chi(H) = r+1 > 1$, then the Turán density

$$
\pi(H) = 1-\frac{1}{r}.
$$

```lean
theorem turanDensity_eq_of_chromaticNumber
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) : turanDensity H = 1 - 1 / r
```

**The Erdős-Stone-Simonovits theorem (equivalence version)**

Suppose $H$ is a simple graph. If the chromatic number $\chi(H) = r+1 > 2$, then the extremal numbers of $H$ satisfy

$$
\textrm{ex}(n, H) \sim \left( 1-\frac{1}{r} \right) {\binom{n}{2}}
$$

as $n \rightarrow \infty$.

```lean
theorem isEquivalent_extremalNumber_of_chromaticNumber
  {r : ℕ} (hr : 1 < r) (hχ : H.chromaticNumber = r + 1) :
  (fun (n : ℕ) ↦ (extremalNumber n H : ℝ))
    ~[atTop] (fun (n : ℕ) ↦ ((1 - 1 / r) * n.choose 2 : ℝ))
```

**The Erdős-Stone(-Simonovits) theorem (chromatic number subgraph version)**

Suppose $\varepsilon > 0$ is a positive real number and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the number of edges $e(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)\binom{v(G)}{2}$, then $G$ contains a copy of any simple graph $H$ such that the chromatic number $\chi(H) = r+1 > 1$.

```lean
theorem eventually_isContained_of_card_edgeFinset_of_chromaticNumber
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) {ε : ℝ} (hε_pos : 0 < ε) :
  ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
    #G.edgeFinset ≥ (1 - 1 / r + ε) * n.choose 2 → H ⊑ G
```

**The Kővári-Sós-Turán theorem**

Suppose $m$, $n$, $s$ and $t$ are natural numbers such that $1 \leq s \leq t$. The Zarankiewicz function $z(m, n; s, t)$ satisfies 

$$
\textrm{z}(m, n; s, t) \leq (t-1)^{1/s} m n^{1-1/s}+(s-1)n.
$$

```lean
theorem zarankiewicz_le (m n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) :
  (zarankiewicz m n s t : ℝ)
    ≤ ((t - 1) ^ (s⁻¹ : ℝ) * m * n ^ (1 - (s⁻¹ : ℝ)) + (s - 1) * n : ℝ)
```

**The Kővári-Sós-Turán theorem (extremal number version)**

Suppose $n$, $s$ and $t$ are natural numbers such that $1 \leq s \leq t$. The extremal numbers of complete bipartite graphs satisfy

$$
\textrm{ex}(n, K_{s, t}) \leq \frac{1}{2}(t-1)^{1/s} n^{2-1/s}+\frac{1}{2}(s-1)n.
$$

```lean
theorem extremalNumber_completeBipartiteGraph_le
  (n : ℕ) [Nonempty α] (hcard_le : card α ≤ card β) :
  (extremalNumber n (completeBipartiteGraph α β) : ℝ) 
    ≤ (card β - 1) ^ (card α : ℝ)⁻¹ * n ^ (2 - (card α : ℝ)⁻¹) / 2 + (card α - 1) * n / 2
```

## Upstreaming to mathlib

The progress towards upstreaming these results to [mathlib](https://github.com/leanprover-community/mathlib4) is as follows:

- [x] [The Erdős-Stone theorem (minimal degree version)](https://github.com/leanprover-community/mathlib4/pull/28685)
- [ ] [The Erdős-Stone theorem](https://github.com/leanprover-community/mathlib4/pull/28686)
- [ ] [The Erdős-Stone theorem (colorable subgraph version)](https://github.com/leanprover-community/mathlib4/pull/28686)
- [ ] [The Erdős-Stone-Simonovits theorem](https://github.com/leanprover-community/mathlib4/pull/28687)
- [ ] [The Erdős-Stone-Simonovits theorem (little-O version)](https://github.com/leanprover-community/mathlib4/pull/28689)
- [ ] [The Erdős-Stone-Simonovits theorem (Turán density version)](https://github.com/leanprover-community/mathlib4/pull/28689)
- [ ] [The Erdős-Stone-Simonovits theorem (equivalence version)](https://github.com/leanprover-community/mathlib4/pull/28689)
- [ ] [The Erdős-Stone(-Simonovits) theorem (chromatic number subgraph version)](https://github.com/leanprover-community/mathlib4/pull/28689)
- [ ] [The Kővári-Sós-Turán theorem](https://github.com/leanprover-community/mathlib4/pull/25841)
- [ ] [The Kővári-Sós-Turán theorem (extremal number version)](https://github.com/leanprover-community/mathlib4/pull/25841)

## Future work

Future work formalising the forbidden subgraph problem could include:

- The supersaturation theorem ([mitchell-horner/Supersaturation](https://github.com/mitchell-horner/Supersaturation))

