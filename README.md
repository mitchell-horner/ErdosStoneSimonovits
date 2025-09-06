# Formalising the Erdős-Stone-Simonovits theorem and the Kővári–Sós–Turán theorem in Lean

[![Lean Action CI](https://github.com/mitchell-horner/ErdosStoneSimonovits/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/mitchell-horner/ErdosStoneSimonovits/actions/workflows/lean_action_ci.yml)

This repository contains a formalisation of the Erdős-Stone-Simonovits theorem and the Kővári–Sós–Turán theorem in [Lean](https://lean-lang.org/). The statements of the results are as follows:

**The Erdős-Stone theorem (minimal degree version)**

Suppose $\varepsilon > 0$ is a positive real number, $r$ and $t$ are natural numbers, and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the minimal degree $\delta(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)v(G)$, then $G$ contains a copy of the complete equipartite graph $K_{r+1}(t)$.

```lean
theorem completeEquipartiteGraph_isContained_of_minDegree
  {ε : ℝ} (hε : 0 < ε) (r t : ℕ) :
  ∃ N, ∀ {V : Type*} [Fintype V] [DecidableEq V], N < card V →
    ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      G.minDegree ≥ (1 - 1 / r + ε) * card V
        → completeEquipartiteGraph (r + 1) t ⊑ G
```

**The Erdős-Stone theorem**

Suppose $\varepsilon > 0$ is a positive real number, $r$ and $t$ are natural numbers, and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the number of edges $e(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)\frac{v(G)^2}{2}$, then $G$ contains a copy of the complete equipartite graph $K_{r+1}(t)$.

```lean
theorem completeEquipartiteGraph_isContained_of_card_edgeFinset
  {ε : ℝ} (hε_pos : 0 < ε) (r t : ℕ) :
  ∃ N, ∀ {V : Type*} [Fintype V] [DecidableEq V], N < card V →
    ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (1 - 1 / r + ε) * card V ^ 2 / 2
      → completeEquipartiteGraph (r + 1) t ⊑ G
```

**The Erdős-Stone theorem (colorable subgraph version)**

Suppose $\varepsilon > 0$ is a positive real number and $G$ is a simple graph. If the number of vertices $v(G)$ is sufficiently large and the number of edges $e(G) \geq \left( 1-\frac{1}{r}+\varepsilon \right)\frac{v(G)^2}{2}$, then $G$ contains a copy of any $r+1$-colorable simple graph $H$.

```lean
theorem isContained_of_card_edgeFinset_of_colorable
  {r : ℕ} (hc : H.Colorable (r + 1)) {ε : ℝ} (hε_pos : 0 < ε) :
  ∃ N, ∀ {V : Type*} [Fintype V] [DecidableEq V], N < card V →
    ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (1 - 1 / r + ε) * card V ^ 2 / 2 → H ⊑ G
```

**The Erdős-Stone-Simonovits theorem**

Suppose $H$ is a simple graph and $\varepsilon > 0$ is a positive real number. If the chromatic number $\chi(H) = r+1 > 1$, then the extremal numbers of $H$ satisfy

$$\left( 1-\frac{1}{r}-\varepsilon \right) \frac{n^2}{2} < \textrm{ex}(n, H) \leq \left( 1-\frac{1}{r}+\varepsilon \right) \frac{n^2}{2}$$ 

for sufficiently large $n$.

```lean
theorem lt_extremalNumber_le_of_chromaticNumber {ε : ℝ} (hε : 0 < ε)
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
  ∃ N, ∀ n > N, (1 - 1 / r - ε) * n ^ 2 / 2 < extremalNumber n H ∧
    extremalNumber n H ≤ (1 - 1 / r + ε) * n ^ 2 / 2
```

**The Erdős-Stone-Simonovits theorem (little-O version)**

Suppose $H$ is a simple graph. If the chromatic number $\chi(H) = r+1 > 1$, then the extremal numbers of $H$ satisfy

$$\textrm{ex}(n, H) = \left( 1-\frac{1}{r} + o(1) \right) \frac{n^2}{2}.$$

as $n \rightarrow \infty$.

```lean
theorem isLittleO_extremalNumber_of_chromaticNumber
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) :
  (fun (n : ℕ) ↦ (extremalNumber n H - (1 - 1 / r) * n ^ 2 / 2 : ℝ))
    =o[atTop] (fun (n : ℕ) ↦ (n ^ 2 : ℝ))
```

**The Erdős-Stone-Simonovits theorem (Turán density version)**

Suppose $H$ is a simple graph. If the chromatic number $\chi(H) = r+1 > 1$, then the Turán density

$$\pi(H) = 1-\frac{1}{r}.$$

```lean
theorem turanDensity_eq_of_chromaticNumber
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) : turanDensity H = 1 - 1 / r
```

**The Erdős-Stone-Simonovits theorem (equivalence version)**

Suppose $H$ is a simple graph. If the chromatic number $\chi(H) = r+1 > 2$, then the extremal numbers of $H$ satisfy

$$\textrm{ex}(n, H) \sim \left( 1-\frac{1}{r} \right) {\binom{n}{2}}$$

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
theorem isContained_of_card_edgeFinset_of_chromaticNumber
  {r : ℕ} (hr_pos : 0 < r) (hχ : H.chromaticNumber = r + 1) {ε : ℝ} (hε_pos : 0 < ε) :
  ∃ N, ∀ {V : Type*} [Fintype V] [DecidableEq V], N < card V →
    ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (1 - 1 / r + ε) * (card V).choose 2 → H ⊑ G
```

**The Kővári–Sós–Turán theorem**

Suppose $s$ and $t$ are natural numbers such that $1 \leq s \leq t$. The extremal numbers of complete bipartite graphs satisfy 

$$\textrm{ex}(n, K_{s, t}) \leq \frac{1}{2}(t-1)^{1/s}n^{2-1/s}+\frac{1}{2}n(s-1).$$

```lean
theorem extremalNumber_completeBipartiteGraph_le (n : ℕ) [Nonempty α] (hcard_le : card α ≤ card β) :
  extremalNumber n (completeBipartiteGraph α β)
    ≤ ((card β-1)^(1/card α : ℝ)*n^(2-1/card α : ℝ)/2 + n*(card α-1)/2 : ℝ)
```

## Upstreaming to mathlib

The progress towards upstreaming these results to [mathlib](https://github.com/leanprover-community/mathlib4) is as follows:

- [ ] The Erdős-Stone theorem (minimal degree version)
- [ ] The Erdős-Stone theorem
- [ ] The Erdős-Stone theorem (colorable subgraph version)
- [ ] The Erdős-Stone-Simonovits theorem
- [ ] The Erdős-Stone-Simonovits theorem (little-O version)
- [ ] The Erdős-Stone-Simonovits theorem (Turán density version)
- [ ] The Erdős-Stone-Simonovits theorem (equivalence version)
- [ ] The Erdős-Stone(-Simonovits) theorem (chromatic number subgraph version)
- [ ] The Kővári–Sós–Turán theorem
