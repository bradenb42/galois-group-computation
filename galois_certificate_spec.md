# One Code Path for Gal(f) over Z, O\_K, F\_q[t]: Derivations, Proofs, and Checker

## 0. Scope and notation

This document gives the derivations behind a single parametrized algorithm that computes the Galois group of a monic separable polynomial over the integers, over the ring of integers of a number field, and over a rational function field, together with the certificate format and the independent checker that verifies its output.

| Section Content  |                                                                         |
| ---------------- | ----------------------------------------------------------------------- |
| 1                | Rings, lifts, Hensel lifting with precision loss, local input precision |
| 2                | Elements of G from the approximation ring; coset pruning                |
| 3                | Invariants valid over every ring; degree bound                          |
| 4                | Recognition and resolvent precisions                                    |
| 5                | Verification of simple roots; degree-one detection                      |
| 6                | Subfields, block systems, starting group, its order                     |
| 7                | Constant field, geometric group, inertia                                |
| 8                | Certificate and checker; soundness; complexity                          |
| 9                | Termination and step count                                              |
| 10               | The three family checks, stated and then made precise                   |

**Standing notation.** $`f\in R[x]`$ monic separable of degree $`n`$; $`R\in\{\mathbb Z,\ \mathcal O_K,\ \mathbb F_q[t]\}`$ (cases 1, 2, 3); $`\hat{\mathcal O}`$ the approximation ring in which the $`n`$ roots $`\alpha_1,\dots,\alpha_n`$ live, $`\hat{\mathcal O}_0\subseteq\hat{\mathcal O}`$ the completion of $`R`$ at the chosen prime/point; $`I_k`$ the $`k`$-th precision ideal; $`L`$ the splitting field; $`G=\mathrm{Gal}(L/\mathrm{Frac}R)\le S_n`$ in the labelling fixed by the approximate roots. For a pair $`V<U`$ with $`\mathrm{Stab}_U(F)=V`$: $`N=[U:V]`$, $`\rho_\sigma=\sigma F(\alpha)`$ for $`\sigma\in U/V`$, $`R_{U,V,F}(x)=\prod_\sigma(x-\rho_\sigma)`$. Lower-case $`v`$ is a valuation; $`\tilde x`$ or $`\hat x`$ an approximation of $`x`$.

---

## 1. Rings, lifts, precision

### 1.1 The unique-lift lemma

Let $`R`$ be a domain, $`I_k`$ a descending chain of ideals, $`\rho_k:R\to\hat R_k=R/I_k`$ (possibly composed with an inclusion into a larger ring containing the roots), $`s:R\to\mathbb R\cup\{-\infty\}`$ a size with $`s(0)=-\infty`$ and $`s(a-b)\le\max(s(a),s(b))+\varepsilon`$, $`\varepsilon=1`$ (archimedean, $`s=\log_2|\cdot|_\infty`$) or $`0`$ (ultrametric). Put $`\mu(k)=\min\{s(x):x\in I_k\setminus0\}`$.

**Lemma 1.1.** If $`s(r)\le B`$ and $`\mu(k)>B+\varepsilon`$, then $`r`$ is the unique element of its fiber of size $`\le B`$; any lift $`L_k`$ returning an element of the fiber of size $`\le B`$ (in particular a size-minimal one) satisfies $`L_k(\rho_k(r))=r`$.

A value $`r`$ is never observed directly: one observes $`E(\tilde\alpha)`$ for $`E\in R[x_1,\dots,x_n]`$, and $`E(\tilde\alpha)\equiv E(\alpha)\pmod{I_k\hat{\mathcal O}}`$ whenever $`\tilde\alpha\equiv\alpha\pmod{I_k\hat{\mathcal O}}`$. So the only precision questions are (a) $`\mu(k)>B+\varepsilon`$ and (b) how well $`\tilde\alpha`$ determines $`\alpha`$.

### 1.2 Hensel with precision loss

For a root $`\alpha`$ and $`\tilde\alpha`$ with $`v(\tilde\alpha-\alpha)>v(f'(\alpha))`$: $`v(f(\tilde\alpha))=v(f'(\alpha))+v(\tilde\alpha-\alpha)`$ exactly. Hence from $`f(\tilde\alpha)\equiv0\pmod{\mathfrak m^k}`$ and $`k>2v(f'(\tilde\alpha))`$ one certifies a unique root $`\alpha`$ with

$$
v(\alpha-\tilde\alpha)\ \ge\ k\_{\mathrm{eff}}:=k-v\big(f'(\tilde\alpha)\big).
$$

In cases 1 and 3, choosing the prime (point) with $`\bar f`$ squarefree gives $`v(f')=0`$ and $`k_{\mathrm{eff}}=k`$. In case 2 (Eisenstein) $`v_{\pi'}(f'(\alpha))=e'v_\pi(\operatorname{disc}f)/n>0`$ and every downstream comparison uses $`k_{\mathrm{eff}}`$, not $`k`$. The same loss occurs for each Eisenstein step $`g`$ of the tower defining $`K'`$, so $`k_{\mathrm{eff}}=k-\max(v_{\pi'}(f'(\tilde\alpha)),\max_g v_{\pi'}(g'(\tilde y_g)))`$.

### 1.3 The three instantiations

| $`R`$ $`I_k`$, $`\mu(k)`$ $`s,\varepsilon`$ lift $`L_k`$ recognition condition  |                    |                                                        |                                    |                                                                                                                                       |                                                             |
| ------------------------------------------------------------------------------- | ------------------ | ------------------------------------------------------ | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------- |
| 1                                                                               | $`\mathbb Z`$      | $`p^k\mathbb Z`$, $`k\log_2p`$                         | $`\log_2\lvert\cdot\rvert`$, $`1`$ | symmetric remainder in $`(-p^k/2,p^k/2]`$, after checking the value lies in $`\mathbb Z/p^k\subset\mathcal O_q/p^k`$                  | $`p^k>2^{B+1}`$, i.e. $`k\ge\lfloor(B+1)/\log_2p\rfloor+1`$ |
| 2                                                                               | $`\mathcal O_K`$   | $`\pi^{\lceil k_{\mathrm{eff}}/e'\rceil}\mathcal O_K`$ | $`v_\pi`$, $`0`$                   | truncation of the $`\mathcal O_K`$-coordinate; certifies $`v_\pi(r)`$ iff nonzero at that precision                                   | decisions are by separation, §1.4                           |
| 3                                                                               | $`\mathbb F_q[t]`$ | $`u^k\mathbb F_q[t]`$, $`k`$ ($`u=t-t_0`$)             | $`\deg_t`$, $`0`$                  | read the truncation as $`\sum_{j<k}c_ju^j`$, substitute $`u=t-t_0`$, **then** test that the $`t`$-coefficients lie in $`\mathbb F_q`$ | $`k\ge B+1`$                                                |

Roots: case 1, $`p\nmid\operatorname{disc}f`$, roots in the unramified $`\mathcal O_q`$, $`q=p^{\mathrm{lcm}(\text{factor degrees})}`$; case 3, $`\operatorname{disc}f(t_0)\ne0`$, roots in $`\mathbb F_{q^s}[[u]]`$; case 2, $`K'\supseteq`$ splitting field with ramification index $`e'`$. In case 3 the Frobenius test must be applied to the $`t`$-polynomial (for $`t_0\notin\mathbb F_q`$ the $`u`$-coefficients of an honest element of $`\mathbb F_q[t]`$ are not in $`\mathbb F_q`$).

Size bounds: $`f`$ monic with $`s(\text{coeff})\le\delta`$; case 1 take $`\delta:=\log_2(1+\max_j|a_j|)`$ (Cauchy), case 3 $`\delta:=\max_j\deg_t(a_j)/j`$ (Newton polygon at $`\infty`$); $`F`$ of degree $`d`$ with $`\ell^1`$-norm $`\|F\|_1`$:

$$
B=\log\_2|F|\_1+d\delta\ \ (\text{case }1),\qquad B=d\delta\ \ (\text{case }3).
$$

### 1.4 Case 2: separation and the Krasner lemma

No a priori height exists. Put $`V_{\mathrm{sep}}:=\max\{v_{\pi'}(\rho_\sigma-\rho_\tau):\rho_\sigma\ne\rho_\tau\}`$.

**Lemma 1.2 (Krasner type).** If $`\rho_\sigma\notin K`$ and $`r\in K`$ then $`v_{\pi'}(\rho_\sigma-r)\le V_{\mathrm{sep}}`$.
*Proof.* Pick $`g\in\mathrm{Gal}(K'/K)`$ with $`g\rho_\sigma\ne\rho_\sigma`$; $`g\rho_\sigma=\rho_{g\sigma}`$ is again a value since $`G\le U`$ permutes $`U/V`$. Then $`\rho_\sigma-g\rho_\sigma=(\rho_\sigma-r)-g(\rho_\sigma-r)`$, so $`v(\rho_\sigma-g\rho_\sigma)\ge v(\rho_\sigma-r)`$, and the left side is $`\le V_{\mathrm{sep}}`$. $`\square`$

**Consequence.** At $`k_{\mathrm{eff}}>V_{\mathrm{sep}}`$ the *image check* (all coordinates of $`\tilde\rho_\sigma`$ off the $`\mathcal O_K`$-component vanish to precision $`k_{\mathrm{eff}}`$) is sound and complete for "$`\rho_\sigma\in K`$". $`V_{\mathrm{sep}}`$ is certified exactly by pairwise distinctness of the $`\tilde\rho_\sigma`$ modulo $`\pi'^{k_{\mathrm{eff}}}`$ (each difference then has valuation $`<k_{\mathrm{eff}}`$, exactly known); this presupposes $`R`$ squarefree, otherwise a Tschirnhaus transformation (§9) is applied. **This is the local-case certificate used by the checker.** A failing image check proves $`\rho_\tau\notin K`$ unconditionally.

Input precision: if $`f`$ (or a tower polynomial) is known only modulo $`\pi^N`$, all $`\tilde f\equiv f`$ have the same splitting field and group provided $`\operatorname{disc}f\not\equiv0\pmod{\pi^N}`$ (then $`v_\pi(\operatorname{disc}f)<N`$ is exact and $`N>2v_\pi(\operatorname{disc}f)/n`$, so Krasner matches the roots).

---

## 2. Elements of G from the approximation ring; pruning

### 2.1 The common source

If $`\psi`$ is an automorphism of $`\hat{\mathcal O}`$ over $`\hat{\mathcal O}_0`$, it permutes the roots, maps $`L`$ to $`L`$, and $`\tau_\psi\in S_n`$ defined by $`\psi(\alpha_i)=\alpha_{\tau_\psi(i)}`$ lies in $`G`$ *in the same labelling*. $`\tau_\psi(i)`$ is the unique $`j`$ with $`\psi(\tilde\alpha_i)\equiv\tilde\alpha_j`$ at a precision above the root separation.

- **Case 1.** $`\phi=`$ Frobenius of $`\mathbb Q_q/\mathbb Q_p`$; $`\tau_\phi`$ is read from $`\mathbb F_q`$: $`\bar\alpha_i^{\,p}=\bar\alpha_{\tau_\phi(i)}`$ ($`k=1`$ suffices as roots are distinct mod $`p`$). Cycle type = factorization pattern of $`\bar f`$.
- **Case 3.** $`\phi(\sum c_ju^j)=\sum c_j^qu^j`$, the Frobenius at the place $`t_0`$; $`\tau_\phi`$ from $`\bar\alpha_i^{\,q}=\bar\alpha_{\tau_\phi(i)}`$. Note $`\tau_\phi\in G_{\mathrm{arith}}`$ and $`\tau_\phi\notin G_{\mathrm{geom}}`$ unless $`c=1`$ (§7).
- **Case 2, tame.** $`K'=K_0(\varpi)`$, $`\varpi^{e'}=u\pi`$, $`\iota:\varpi\mapsto\zeta_{e'}\varpi`$, $`\iota|_{K_0}=\mathrm{id}`$, computable coordinatewise on $`\bigoplus\mathcal O_{K_0}\varpi^i`$; $`\tau_\iota`$ generates $`I(L/K)`$, certified at $`k_{\mathrm{eff}}>e'v_\pi(\operatorname{disc}f)/n`$. For Eisenstein $`f`$: $`K(\alpha)\cap K_0=K`$ gives $`I`$ transitive, cyclic, faithful on $`n`$ points, hence $`\tau_\iota`$ is an $`n`$-cycle, $`e(L/K)=n`$, and $`C_n=\langle\tau_\iota\rangle\trianglelefteq G\le C_n\rtimes(\mathbb Z/n)^\times`$. The residual Frobenius is available only as a coset $`\tilde\phi I`$.
- **Case 2, wild.** No canonical element: automorphisms of a wild extension are obtained only by root finding, i.e. by the explicit construction. Only group-theoretic constraints ($`P\trianglelefteq I\trianglelefteq G`$, $`I/P`$ cyclic of order prime to $`p`$, $`|I|=e(L/K)`$), which prune pairs, not cosets.

### 2.2 Pruning count

For $`V<U`$ maximal and certified $`\tau\in G`$, test only conjugates $`\sigma V\sigma^{-1}`$ with $`\sigma^{-1}\tau\sigma\in V`$; this depends only on $`\sigma N_U(V)`$. The map $`\sigma\mapsto\sigma^{-1}\tau\sigma`$ has fibers the right cosets of $`C_U(\tau)`$, so

$$
c\_\tau=\frac{|\tau^U\cap V|,|C\_U(\tau)|}{|N\_U(V)|}=\frac{\chi\_{U/V}(\tau)}{[N\_U(V)\:V]},\qquad \frac{c\_\tau}{[U\:N\_U(V)]}=\frac{|\tau^U\cap V|}{|\tau^U|}.
$$

If $`\tau^U\cap V=\emptyset`$ the pair is dismissed. Elements known only up to $`S_n`$-conjugacy (Frobenius at other primes) prune pairs, all-or-nothing.

**Safety.** If $`G\le\sigma V\sigma^{-1}`$ then $`\tau\in\sigma V\sigma^{-1}`$, so the coset survives. Hypotheses: $`\tau\in G`$ in the current labelling; $`\tau`$ correctly computed (precision); $`\tau`$ conjugated along any relabelling ($`\tau\mapsto\sigma^{-1}\tau\sigma`$). The checker never uses pruning data; a wrong prune can only produce a rejected or longer certificate.

---

## 3. Invariants valid over every ring

### 3.1 Two characteristic-free tools

**(A) 0–1 supports.** For a finite set $`M`$ of monomials and $`F_M=\sum_{m\in M}m`$: $`\mathrm{Stab}_U(F_M\otimes A)=\mathrm{Stab}_U(M)`$ for every ring $`A\ne0`$ (distinct monomials are a basis, $`S_n`$ permutes it).

**(B) Equivariant substitution.** $`\Omega=\bigsqcup B_j`$, $`h_j\in\mathbb Z[x_{B_j}]`$ nonconstant with leading coefficient $`1`$ in a fixed multiplicative monomial order, $`uh_j=h_{\bar u(j)}`$ for $`u\in U`$ via $`\pi:U\to\bar U`$. Then $`\phi_A:A[y]\to A[x]`$, $`y_j\mapsto h_j`$, is injective for every $`A`$ (leading monomials $`\prod\mathrm{lm}(h_j)^{e_j}`$ are distinct because the $`h_j`$ are in disjoint variables) and $`\mathrm{Stab}_U(\phi(G)\otimes A)=\pi^{-1}(\mathrm{Stab}_{\bar U}(G\otimes A))`$. Power sums are *not* admissible substitutes ($`p_2=p_1^2`$ mod 2); disjoint variables is the hypothesis, not algebraic independence over $`\mathbb Q`$.

**Maximality shortcut.** For $`V<U`$ maximal and $`F`$ $`V`$-invariant, $`\mathrm{Stab}_U(F\otimes A)\in\{V,U\}`$; so "$`\mathrm{Stab}=V`$ over $`\mathbb Z`$ and $`\mathbb F_2`$" is equivalent to: one $`u\notin V`$ with $`uF-F`$ having an odd coefficient. All constructions below make $`uF-F`$ have a coefficient $`\pm1`$.

### 3.2 Separating monomial and the degree function

For a chain $`\{\text{points}\}=\mathcal C_0\prec\dots\prec\mathcal C_r=\{\Omega\}`$ with branching $`m_1,\dots,m_r`$ ($`n=\prod m_i`$) define

$$
\delta(m\_1,\dots,m\_r)=\sum\_{i=1}^r\frac{n}{m\_1\cdots m\_i}\binom{m\_i}{2}\ \le\ \binom n2 .
$$

Address each point by $`(a_1,\dots,a_r)`$ and set $`e(x)=(a_1-1)+\sum_{l=2}^r(a_l-1)\mathbf 1[a_1=m_1,\dots,a_{l-1}=m_{l-1}]`$, $`m_{\mathcal C}=\prod x^{e(x)}`$.

**Lemma 3.1.** $`\mathrm{Stab}_{U_0}(m_{\mathcal C})=1`$ for $`U_0`$ preserving the chain; $`\deg m_{\mathcal C}=\delta`$.
*Proof.* In a level-$`i`$ block, the all-maximal point is the unique maximum of the level-$`i`$ multiset $`M_i`$ (if $`l_0`$ is the first non-maximal index, $`e\le\sum_{l<l_0}(m_l-1)+(a_{l_0}-1)<\max M_i`$). A level-$`i`$ block's multiset is $`M_i`$ with that maximum raised by $`t_B=\sum_{l>i}(a_l-1)\mathbf 1[a_{i+1}=m_{i+1},\dots,a_{l-1}=m_{l-1}]`$; siblings differ in $`a_{i+1}`$ and have distinct $`t_B`$ ($`a_{i+1}-1`$ if not maximal, $`\ge m_{i+1}-1`$ if maximal), hence distinct multisets. Downward induction fixes every block, then every point. Degree: each child contributes $`(a_i-1)`$ once at its maximal point. $`\square`$

### 3.3 Generic invariant

$`F^{\mathrm{gen}}_{U,V}=\sum_{v\in V}v\cdot m_{\mathcal C}`$, 0–1 with $`|V|`$ terms of degree $`\delta`$; $`\mathrm{Stab}_U=V`$ over every ring (if $`uM=M`$ then $`um=vm`$, $`v^{-1}u\in\mathrm{Stab}(m)=1`$). Valid for any pair, maximal or not.

### 3.4 Trichotomy for a maximal pair

Fix a block system $`\mathcal B`$, $`\pi:U\to\bar U`$, $`K=\ker\pi`$, local groups $`U_1=\mathrm{Stab}_U(B_1)|_{B_1}`$, $`V_1=\mathrm{Stab}_V(B_1)|_{B_1}`$.

- **Type I, $****`\pi(V)<\pi(U)`****$.** Then $`V=\pi^{-1}(\pi V)`$, $`\pi(V)`$ maximal in $`\pi(U)`$; with $`G`$ a $`\pi(U)`$-relative $`\pi(V)`$-invariant (recursion) and $`s_j=\sum_{x\in B_j}x`$: $`F^{\mathrm I}=G(s_1,\dots,s_d)`$, stabilizer $`V`$ by (B), degree $`\le\delta(m_{i+1},\dots,m_r)\le\binom d2`$. Any $`U_1`$-invariant 0–1 block polynomial may replace $`s_j`$.
- **Type II, $****`\pi(V)=\pi(U)`****$, $****`V_1<U_1`****$.** Choose $`W_1`$ maximal in $`U_1`$ with $`V_1\le W_1<U_1`$ (maximality of $`V_1`$ in $`U_1`$ is not proven, and need not be), $`H`$ a $`U_1`$-relative $`W_1`$-invariant with zero constant term, $`v_j\in V`$ with $`v_jB_1=B_j`$ for $`j`$ in the $`\bar U`$-orbit of $`B_1`$, and $`F^{\mathrm{II}}=\sum_jv_jH`$. For $`u\in U`$ write $`uv_j=v_{j'}w_j`$; comparing block components (disjoint monomial sets) $`uF^{\mathrm{II}}=F^{\mathrm{II}}`$ iff $`w_j|_{B_1}\in W_1`$ for all $`j`$ iff $`u\in\hat W:=\{u:(v_{\bar u(j)}^{-1}uv_j)|_{B_1}\in W_1\ \forall j\}`$, a subgroup containing $`V`$ and $`\ne U`$; maximality gives $`\hat W=V`$. Degree $`\le\delta(m_1,\dots,m_i)\le\binom m2`$.
- **Type III, otherwise.** Use $`F^{\mathrm{gen}}`$, degree $`\delta`$. (Example of a structured alternative: the sign-product subgroup of $`S_m\wr S_d`$ is the exact stabilizer in all characteristics of $`\sum_{|S|\text{ even}}\prod_{j\in S}\Delta''_j\prod_{j\notin S}\Delta'_j`$, degree $`d\binom m2`$; no general structured construction for Type III is claimed.)

**Theorem 3.2.** For every maximal pair $`V<U\le U_0`$ the invariant produced has $`\mathrm{Stab}_U(F\otimes A)=V`$ for every ring $`A\ne0`$ and $`\deg F\le\delta(m_1,\dots,m_r)`$. The recursion is well founded (each recursive pair is maximal on a strictly smaller set).

Stabilizer of $`F`$ as a polynomial is distinct from distinctness of values at roots; the latter is handled by the separation checks and Tschirnhaus (§9).

---

## 4. Recognition and resolvent precisions

$`\rho_\sigma`$ are uniformly bounded by $`B`$; $`e_j`$ the coefficients of $`R`$.

**Case 1.** $`k_{\mathrm{rec}}=\lfloor(B+1)/\log_2p\rfloor+1>(B+1)/\log_2p`$. $`|e_j|\le\binom Nj2^{jB}`$, and since $`\binom Nj\le2^{N-1}`$ for $`0<j<N`$, $`B_R\le N(B+1)-1`$ (and $`B_R\le NB`$ if $`B\ge\log_2N`$). So $`k_{\mathrm{prf}}=\lfloor(B_R+1)/\log_2p\rfloor+1\le\lfloor N(B+1)/\log_2p\rfloor+1\le Nk_{\mathrm{rec}}`$. Tight up to $`O(N/\log_2p)`$ since $`|e_N|`$ can reach $`2^{NB}`$.

**Case 3.** $`k_{\mathrm{rec}}=B+1`$, $`\deg e_j\le jB`$, $`k_{\mathrm{prf}}=NB+1\le Nk_{\mathrm{rec}}`$.

**Case 2.** $`k_{\mathrm{rec}}=V_{\mathrm{sep}}+1`$ (on $`k_{\mathrm{eff}}`$), and with the pairwise certificate $`k_{\mathrm{prf}}=k_{\mathrm{rec}}`$. If one insists on certifying from $`R`$: $`|R|:=\max_\sigma v(R'(\rho_\sigma))\le(N-1)V_{\mathrm{sep}}`$ gives $`k_{\mathrm{prf}}=|R|+1\le Nk_{\mathrm{rec}}`$; the discriminant certificate needs $`k_{\mathrm{eff}}>v(\operatorname{disc}R)\le N(N-1)V_{\mathrm{sep}}`$ and is not used.

**Identification threshold.** After $`R(r)=0`$ is proved, the coset with $`\rho_\sigma=r`$ is identified by $`\rho_\sigma\equiv r`$ at precision $`k_{\mathrm{id}}=v(R'(r))+1`$ (Hensel uniqueness: at most one root in the ball $`v(x-r)>v(R'(r))`$); $`k_{\mathrm{id}}\le(N-1)k_{\mathrm{rec}}+1`$ (case 1), $`\le(N-1)k_{\mathrm{rec}}`$ (case 3).

**Theorem 4.1.** In all cases $`k_{\mathrm{prf}}\le[U:V]\,k_{\mathrm{rec}}`$ and $`\max(k_{\mathrm{prf}},k_{\mathrm{id}})\le[U:V]\,k_{\mathrm{rec}}+1`$.

---

## 5. Verification of a simple root; degree-one detection suffices

### 5.1 One criterion

$`R\in\mathcal O[x]`$ monic over a complete DVR, $`c\in\mathcal O`$, $`R(y+c)=\sum c_jy^j`$, $`\lambda_1\ge\lambda_2\ge\cdots`$ the valuations $`w(\rho-c)`$ over roots (all $`\ge0`$).

**Lemma 5.1.** Equivalent: (1) $`(1,w(c_1))`$ is a vertex of the Newton polygon of $`R(y+c)`$; (2) $`\lambda_1>\lambda_2`$; (3) $`R`$ has a simple root $`\rho^\ast\in\mathrm{Frac}\mathcal O`$ strictly closest to $`c`$. Then $`w(\rho^\ast-c)=w(c_0)-w(c_1)`$ and $`\lambda_2=\max_{j\ge2}(w(c_1)-w(c_j))/(j-1)`$. (Uniqueness of the extension of $`w`$ to the splitting field is where completeness is used; the unique closest root is Galois-fixed.)

Certification from $`c_j`$ known mod $`\mathfrak m^\kappa`$: if $`w(c_1)<\kappa`$, the polygon right of $`j=1`$ is exact (later vertices have $`w\le w(c_1)`$ since slopes are $`\le0`$), so $`\lambda_2`$ is exact, and

$$
(\ast)\qquad c\_0\equiv0\pmod{\mathfrak m^\kappa}\quad\text{and}\quad\kappa>w(c\_1)+\lambda\_2
$$

certifies (1). Classical Hensel is the case $`w(c_1)=0`$.

### 5.2 Case 1

$`R\in\mathbb Z[x]`$ exact. Choose a prime $`\ell`$ with $`\bar R`$ squarefree ($`\gcd(\bar R,\bar R')=1`$; implies $`\operatorname{disc}R\ne0`$, all roots simple; $`\ell=p`$ iff $`p\nmid\operatorname{disc}R`$). Newton-lift the distinct linear factors of $`\bar R`$ (each iteration is the linear solve $`R'(a)\delta\equiv-R(a)`$) to $`\ell^{k}`$, $`\ell^k>2^{B+1}`$; take symmetric remainders; **discard candidates with $****`|v_i|>2^B`****$** (spurious lifts can be large and would break the evaluation bound); test survivors by $`R(v_i)=0`$ exactly or modulo $`\ell^{k_{\mathrm{prf}}}`$ using $`|R(v_i)|\le2^{N(B+1)}`$. Completeness: an integer root $`v=\rho_\sigma`$ has $`|v|\le2^B`$, reduces to a simple root $`\bar a_i`$, equals the unique $`\ell`$-adic root in that residue class, so $`v\equiv a_i`$ and the symmetric remainder returns it. Simplicity: from $`\operatorname{disc}R\ne0`$, or $`R'(v)\not\equiv0\pmod{\ell^{k_{\mathrm{prf}}}}`$ with $`|R'(v)|\le2^{(N-1)(B+1)}`$. No product of local factors is ever formed.

### 5.3 Case 2

Data $`R\bmod\pi^m`$, $`m=\lceil k_{\mathrm{eff}}/e'\rceil`$, center $`v`$ the truncation of $`\rho_\sigma`$. Apply $`(\ast)`$ with $`\kappa=m`$, and additionally check $`k_{\mathrm{eff}}>e'\lambda_2`$ (not implied by $`(\ast)`$ when $`m=1`$, $`e'\ge3`$); then $`\rho_\sigma`$, at distance $`\ge k_{\mathrm{eff}}`$, is the unique closest root. $`(\ast)`$ is attained once $`k_{\mathrm{eff}}>NV_{\mathrm{sep}}`$. Other roots in $`K`$ are decided per coset by the image check (a single Newton polygon cannot see rationality at shared distances). This is the method "from $`R`$ alone"; the checker uses §1.4 instead.

### 5.4 Case 3

$`R\in\mathbb F_q[t][x]`$ exact; $`R(v)=0`$ iff $`R(v)\equiv0\pmod{u^{NB+1}}`$, $`R'(v)\ne0`$ iff $`R'(v)\not\equiv0\pmod{u^{(N-1)B+1}}`$. Complete root list as in 5.2 with a point $`t_1\in\mathbb F_{q^{s_1}}`$ where $`R(t_1,x)`$ is squarefree, lifting linear factors over $`\mathbb F_{q^{s_1}}`$ to $`u_1^{B+1}`$, re-expanding in $`t`$, keeping those with $`t`$-coefficients in $`\mathbb F_q`$.

### 5.5 What the descent step needs

**Theorem 5.2.** $`V<U`$, $`\mathrm{Stab}_U(F)=V`$, $`G\le U`$, $`\mathcal K=\mathrm{Frac}(R)`$. (1) If $`v\in\mathcal K`$ is a simple root of $`R`$ then $`v=\rho_\sigma`$ for a unique $`\sigma`$ and $`G\le\sigma V\sigma^{-1}`$. (2) If $`R`$ has no root in $`\mathcal K`$ then $`G\le`$ no conjugate of $`V`$. (3) The step is determined by the degree-one factors of $`R`$ over $`\mathcal K`$ and their multiplicities.
*Proof.* (1) $`G`$ fixes $`v`$, $`g\rho_\sigma=\rho_{g\sigma}`$, simplicity forces $`g\sigma V=\sigma V`$; integrality puts $`v`$ in the ring. (2) Galois theory. (3) For squarefree $`R`$, irreducible factors over $`\mathcal K`$ are $`G`$-orbits on $`U/V`$. $`\square`$ Maximality of $`V`$ is not used.

---

## 6. Subfields, block systems, starting group

### 6.1 Principal subfields

$`K_f=\mathrm{Frac}(R)(\alpha)`$, $`H=\mathrm{Stab}_G(1)`$, $`f=\prod_if_i`$ over $`K_f`$ with root sets the $`H`$-orbits $`O_i`$ (double cosets $`H\sigma_jH`$). $`L_i=\{g(\alpha):f_i\mid g(y)-g(\alpha)\}`$ is the equalizer of $`K_f\rightrightarrows K_f[y]/(f_i)`$, hence a subfield, computable as the kernel of an explicit $`\mathrm{Frac}(R)`$-linear map.

**Lemma 6.1.** $`L_i=\mathrm{Fix}(\langle H,\sigma_j\rangle)`$ for $`j\in O_i`$.
**Theorem 6.2.** $`\mathrm{Fix}(M)=\bigcap_{i:O_i\subseteq M\cdot1}L_i`$ for every $`H\le M\le G`$ (since $`M=\bigcup_{\sigma_i\in M}H\sigma_iH`$). The lattice is the intersection closure of $`\{L_i\}`$.

### 6.2 Factorization in $`\hat R`$

Choose the prime/point so that $`\tau`$ has a fixed point, relabel $`\tau(1)=1`$, so $`K_f\hookrightarrow\hat K_0`$ via $`\alpha\mapsto\alpha_1`$. Each $`f_i`$ is a product of $`\tau`$-cycles (as $`\tau\in H`$). Coefficients $`\gamma`$ of a candidate $`g_S=\prod_{m\in S}(y-\alpha_m)`$ are recognized from one embedding: $`D\gamma=c(\alpha)`$, $`c\in R^n`$, and

**Lemma 6.3.** For $`0\ne c\in R^n`$, $`\deg c<n`$, with $`c(\alpha_1)\equiv0\pmod{I_a}`$: $`N=\prod_jc(\alpha_j)\in R\setminus0`$, $`I_a\mid N`$, hence $`\log_2\|c\|_1\ge\frac{a\log_2p}{n}-(n-1)\log_2M`$ (case 1), $`\deg c\ge\frac an-(n-1)\delta`$ (case 3).

So Lemma 1.1 applies to the coset of the kernel lattice $`\Lambda_0(a)`$ with $`\mu(a)`$ as above; the lift is a closest-vector computation (exact linear algebra over $`\mathbb F_q`$ in case 3; LLL in case 1 with the factor $`2^{(n-1)/2}`$ absorbed into $`a=O(\frac n{\log_2p}(B'+n+n\log_2M))`$). Soundness is by exact verification $`g_S\in K_f[y]`$, $`g_S\mid f`$. A coarser factorization yields a sublattice and a larger $`W`$, still sound. Case 2: $`H`$ and the lattice are read off the explicitly known $`G`$.

### 6.3 Block systems and $`W`$

**Lemma 6.4.** For $`L=\mathrm{Fix}(M)`$ with primitive element $`b(\alpha)`$ and minimal polynomial $`h`$: $`j\sim k\iff b(\alpha_j)=b(\alpha_k)`$ is $`G`$-invariant with $`d=[G:M]`$ classes of size $`n/d`$, the classes being the blocks $`\mathcal B_L`$ of $`M`$. The grouping of the $`b(\tilde\alpha_j)`$ at precision $`k>v(\operatorname{disc}h)/2`$ is provably correct ($`\operatorname{disc}h\in R`$ exact).

$`W:=\bigcap_L\mathrm{Stab}_{S_n}(\mathcal B_L)=\bigcap_L S_{m_L}\wr S_{d_L}`$.
**Theorem 6.5.** $`G\le W`$, and every block system of $`G`$ is among the $`\mathcal B_L`$.

**Order.** For a chain: $`|W|=\prod_i(m_i!)^{n/(m_1\cdots m_i)}`$. In general $`|W|=\prod_i|x_i^{W_{x_1..x_{i-1}}}|\le\prod_i|T_i|`$, $`T_i`$ the class of points with the same type $`(\mathcal B(x,x_s))_{s<i}`$ ($`\mathcal B(x,s)`$ the finest system with $`x,s`$ in one block; meets exist since $`(M\cap M')\cdot1=M\cdot1\cap M'\cdot1`$). Equality for chains; strict in general ($`S_3`$ regular: bound $`12`$, $`|W|=6`$), so $`|W|`$ depends on the incidence structure, not just the abstract lattice.

**Checkable starting groups (fix).** Computing $`W`$ as an intersection of partition stabilizers is not known to be polynomial. The artifact therefore uses as $`U_0`$ either (a) the iterated wreath product of a chain $`\mathcal C\subseteq\Lambda`$ (explicit generators, built by the checker), or (b) a supplied group $`U_0`$ with $`U_0\le W`$ verified generator-by-generator (each generator preserves each $`\mathcal B_L`$) and $`|U_0|=\prod_{i=1}^{n}|T_i|`$, where the types are taken relative to the sequence of **all** $`n`$ points in some order (so that the pointwise stabilizer at the end is trivial and the product is unconditionally an upper bound on $`|W|`$); then $`U_0=W`$. In both cases $`G\le U_0`$. Remaining block systems are used for invariants and pruning; under (a) the passage from the chain group to $`W`$ occurs as ordinary positive descent steps (non-maximal pairs allowed, §5.5).

---

## 7. Constant field, geometric group, inertia (case 3)

$`F=\mathbb F_q(t)`$, $`\mathbb F_{q^c}=L\cap\overline{\mathbb F}_q`$, $`G_{\mathrm{geom}}=\mathrm{Gal}(L/\mathbb F_{q^c}(t))`$, $`1\to G_{\mathrm{geom}}\to G\to\mathrm{Gal}(\mathbb F_{q^c}/\mathbb F_q)\to1`$.

**Lemma 7.0.** $`\tau`$ restricts to the generator $`x\mapsto x^q`$; hence $`G=G_{\mathrm{geom}}\langle\tau\rangle`$, $`G_{\mathrm{geom}}\cap\langle\tau\rangle=\langle\tau^c\rangle`$, $`c\mid s`$, $`c=\min\{j\ge1:\tau^j\in G_{\mathrm{geom}}\}`$. Also $`c\mid\gcd_{t_1}\mathrm{lcm}(\deg\text{ factors of }f(t_1,x))`$ over unramified degree-one $`t_1`$.

**Lemma 7.1.** $`L\cap\overline{\mathbb F}_q(t)=\mathbb F_{q^c}(t)`$ (finite subextensions of $`\overline{\mathbb F}_q(t)/F`$ are the $`\mathbb F_{q^j}(t)`$, $`\overline{\mathbb F}_q(t)/F`$ being Galois with group $`\hat{\mathbb Z}`$), so for a resolvent value: $`\rho_\sigma\in\mathbb F_{q^s}[t]\iff\rho_\sigma\in\mathbb F_{q^c}(t)\iff G_{\mathrm{geom}}`$ fixes $`\rho_\sigma`$.

Thus the same descent with the geometric lift (no Frobenius test) computes $`G_{\mathrm{geom}}`$, starting from $`G`$. Each geometric step $`(U,V)`$ has $`V\trianglelefteq G`$ of prime index $`\ell`$, $`\tau^{[G:U]}`$ cycles the $`\ell`$ cosets, and the values in the orbit are related by coefficientwise $`q^{[G:U]}`$-powers. Hence $`c=\prod\ell_i=[G:G_{\mathrm{geom}}]`$, $`\mathbb F_{q^c}=\mathbb F_q(\text{coefficients of }\rho)`$ for the value $`\rho`$ of a $`G`$-relative $`G_{\mathrm{geom}}`$-invariant, and $`G_{\mathrm{geom}}=\{g\in G:g\rho=\rho\}`$.

**Theorem 7.2.** $`G_{\mathrm{geom}}=\mathcal I:=\langle I_{\mathfrak P}:\mathfrak P\text{ places of }L\rangle`$ = normal closure in $`G`$ of $`\langle I_{\mathfrak P_P}:P\text{ ramified}\rangle`$, ramified places including $`\infty`$.
*Proof.* $`I_{\mathfrak P}`$ acts trivially on $`\kappa(\mathfrak P)\supseteq\mathbb F_{q^c}`$, so $`\mathcal I\le G_{\mathrm{geom}}`$. Conversely $`E=\mathrm{Fix}(\mathcal I)`$ is Galois and unramified over $`F`$; Riemann–Hurwitz for $`E`$ over its constant field $`\mathbb F_{q^{c_E}}`$ gives $`2g_E-2=-2d_E`$, so $`d_E=1`$, $`E=\mathbb F_{q^{c_E}}(t)\subseteq\mathbb F_{q^c}(t)`$, $`\mathcal I\supseteq G_{\mathrm{geom}}`$. $`\square`$

Consequences: $`G=\langle\tau,I_{\mathfrak P}\rangle`$; $`|G_{\mathrm{geom}}|=|G|/c`$ is an independent check against the inertia data (matched to the $`t_0`$-labelling up to $`G`$ via the exact descent data; normal closures in $`G`$ are insensitive to $`G`$-conjugacy).

---

## 8. Certificate and checker

### 8.1 Certificate

$`\mathcal C=(\mathsf H,\Lambda,(S_i)_{i<\ell},\mathsf T)`$.

- $`\mathsf H`$: case, $`f`$, local datum ($`p,s`$ / $`K,\pi`$, tower, $`e'`$ / $`t_0,s`$), $`k_{\max}`$, $`\hat\alpha\in(\hat{\mathcal O}/I_{k_{\max}})^n`$.
- $`\Lambda`$: subfields (basis, $`b_L`$, $`h_L`$, $`\mathcal B_L`$); the chain $`\mathcal C`$ or the type-bound data for $`U_0`$.
- $`S_i=(U_i,U_{i+1},F_i,\sigma_i,v_i,k_i,\mathrm{proof}_i)`$: groups by generators; $`F_i`$ in §3 normal form (canonical form and syntactic permutation action available); $`\sigma_i\in U_i`$; $`v_i\in R`$; $`k_i\le k_{\max}`$; $`\mathrm{proof}_i`$ = the resolvent $`R_i`$ (exact in cases 1, 3) and an auxiliary prime/point for complete root lists when needed. Semantics: $`V_i=\mathrm{Stab}_{U_i}(F_i)`$, $`U_{i+1}=\sigma_iV_i\sigma_i^{-1}`$, $`v_i=\sigma_iF_i(\alpha)`$.
- $`\mathsf T`$: $`\mathsf T_1`$ elements $`g_r`$ with ring-automorphism witnesses generating $`U_\ell`$; $`\mathsf T_2`$ (cases 1, 3 only) an invariant $`\Theta`$ with trivial $`U_\ell`$-stabilizer and the Galois resolvent $`P_\Theta`$; $`\mathsf T_3`$ an external lower bound $`|G|\ge\beta`$ with provenance and $`\beta=|U_\ell|`$.

### 8.2 Checker

- **C0.** Cases 1, 3: $`\bar f`$ squarefree; $`\hat\alpha_j`$ pairwise distinct mod $`I_1`$; $`f(\hat\alpha_j)\equiv0\pmod{I_{k_{\max}}}`$; $`k_{\mathrm{eff}}=k_{\max}`$. Case 2: tower verified with $`\operatorname{disc}\not\equiv0`$ at input precision; $`f(\hat\alpha_j)\equiv0`$; $`k_{\mathrm{eff}}`$ per §1.2 with $`k_{\mathrm{eff}}>e'v_\pi(\operatorname{disc}f)/n`$.
- **C1.** For each $`L`$: closure under multiplication; $`b_L\in L`$, $`h_L(b_L)=0`$, $`\deg h_L=\dim L`$, $`h_L`$ squarefree; $`k_{\mathrm{eff}}>v(\operatorname{disc}h_L)/2`$; $`\mathcal B_L`$ equals the partition of the $`b_L(\hat\alpha_j)\bmod I_{k_{\mathrm{eff}}}`$. Then $`U_0`$ per §6.3 (a) or (b).
- **C2.** BSGS for $`U_i,U_{i+1}`$; generators of $`U_{i+1}`$ and $`\sigma_i`$ in $`U_i`$; generators of $`V_i'=\sigma_i^{-1}U_{i+1}\sigma_i`$ fix $`F_i`$; orbit $`\mathcal O_i=U_i\cdot F_i`$ by breadth-first search on canonical forms, reject if it exceeds $`N_i=|U_i|/|U_{i+1}|`$, accept iff $`|\mathcal O_i|=N_i`$ (certifies $`\mathrm{Stab}_{U_i}(F_i)=V_i'`$; maximality not needed).
- **C3.** $`\sigma_iF_i(\hat\alpha)\equiv\rho_{k_i}(v_i)`$ in $`\hat{\mathcal O}/I_{k_i}`$ (subsumes the image check; in case 3 on the $`t`$-polynomial).
- **C4.** Recompute $`B_i`$ from $`F_i,f`$, and $`k_{\mathrm{prf}}(N_i,B_i)`$, $`k_{\mathrm{id}}`$; check $`k_{\mathrm{prf}}\le k_i\le k_{\mathrm{eff}}`$ (cases 1, 3). In case 2 require $`k_i=k_{\mathrm{eff}}`$.
- **C5.** $`\tilde R_i=\prod_{\Phi\in\mathcal O_i}(x-\Phi(\hat\alpha))`$. Cases 1, 3: lift coefficientwise, compare with $`R_i`$; check exactly $`R_i(v_i)=0`$, $`R_i'(v_i)\ne0`$, $`v(R_i'(v_i))<k_i`$. Case 2: the $`\Phi(\hat\alpha)`$ pairwise distinct mod $`\pi'^{k_{\mathrm{eff}}}`$ (certifies $`V_{\mathrm{sep}}<k_{\mathrm{eff}}`$ and squarefreeness); image check on $`\sigma_iF_i(\hat\alpha)`$ passes (then $`\rho_{\sigma_i}\in K`$ by Lemma 1.2, a simple root).
- **C6.** $`\mathsf T_1`$: each witness applied to $`\hat\alpha`$ reproduces $`g_r`$ at a precision above separation; $`\langle g_r\rangle=U_\ell`$ by BSGS. $`\mathsf T_2`$: C2 with $`N=|U_\ell|`$; recover $`P_\Theta`$ at $`k_\Theta\ge k_{\mathrm{prf}}(|U_\ell|,B_\Theta)`$; factor over $`\mathrm{Frac}R`$ (polynomial-time algorithms over $`\mathbb Q`$ and $`\mathbb F_q(t)`$) and require irreducibility. $`\mathsf T_3`$: verify the stated hypotheses and $`\beta=|U_\ell|`$.

### 8.3 Soundness

**Theorem 8.1.** If the checker accepts, then $`G\le U_i`$ for all $`i\le\ell`$, and $`G=U_\ell`$ under $`\mathsf T_1`$, $`\mathsf T_2`$, or $`\mathsf T_3`$ with a true external bound.
*Proof.* C0 certifies $`n`$ distinct roots and the labelling. C1 and §6.3 give $`G\le U_0`$. Step: $`G\le U_i`$ and C2 make the coefficients of the true $`R_i`$ $`G`$-fixed hence in $`R`$; C4 makes its lift exact (the checker's own bound is valid for the true values); C5 gives a simple root $`v_i`$ and identification with $`\sigma_i`$ (Hensel uniqueness, or in case 2 Lemma 1.2 on the value of the coset itself); Theorem 5.2(1) gives $`G\le U_{i+1}`$. $`\mathsf T_1`$: witnesses are elements of $`G`$ (§2.1), so $`U_\ell\le G`$. $`\mathsf T_2`$: $`P_\Theta\in R[x]`$ has root $`\theta\in L`$; irreducible implies it is the minimal polynomial of the separable element $`\theta`$ (so its roots $`g\theta`$ are distinct), $`[\mathrm{Frac}R(\theta):\mathrm{Frac}R]=|U_\ell|\le|G|`$. $`\mathsf T_3`$: $`|G|\ge\beta=|U_\ell|`$. $`\square`$

Scope of the certified statement: it asserts the containments and, under $`\mathsf T`$, the equality. Completeness of $`\Lambda`$, maximality of $`V_i'`$, safety of pruning, and completeness of the maximal-subgroup lists lie outside it; each affects prover efficiency and the length of chains, and none affects acceptance of a false statement. Without $`\mathsf T`$ the certificate certifies exactly $`G\le U_\ell`$.

### 8.4 Complexity

All loops are bounded by quantities present in $`\mathcal C`$ ($`n`$, $`k_{\max}`$, $`N_i=\deg R_i`$, $`|F_i|`$, $`|U_\ell|`$ for $`\mathsf T_2`$). Costs: C0 $`O(nd\,\mathsf c(k_{\max}))`$; C1 exact linear algebra in dimension $`n`$ plus $`O(n\,\mathsf c(k_{\mathrm{eff}}))`$ per $`L`$; C2 Schreier–Sims (polynomial in $`n`$ and number of generators) and $`O(N_ig|F|\log|F|)`$ for the orbit; C3 $`O(|F|\mathsf c(k_i))`$; C5 $`\tilde O(N_i)`$ ring operations at precision $`k_i`$ plus exact tests on a degree-$`N_i`$ polynomial; C6 polynomial-time factoring on a polynomial that is part of $`\mathcal C`$. Hence:

**Theorem 8.2.** The checker runs in time polynomial in $`|\mathcal C|`$ and accepts only certificates all of whose assertions are true.

---

## 9. Termination at G

**Lemma 9.1.** If $`R`$ is squarefree then $`G\le\sigma V\sigma^{-1}\iff\rho_\sigma\in R`$, decidable at finite precision (§4).

**Lemma 9.2 (Tschirnhaus).** There is $`T\in R[x]`$, $`\deg T<n`$, with $`R_T=\prod_\sigma(x-\sigma F(T(\alpha_1),\dots,T(\alpha_n)))`$ squarefree, and Lemma 9.1 holds for $`R_T`$. *Proof.* $`D(c)=\prod_{\sigma\ne\tau}(\sigma F-\tau F)(T(\alpha_j))_j`$ is a nonzero polynomial in the coefficients $`c`$ of $`T`$ (the map $`c\mapsto(T(\alpha_j))_j`$ is the Vandermonde bijection of $`L^n`$, and $`\prod(\sigma F-\tau F)\ne0`$), of degree $`\le N(N-1)d`$; by Schwartz–Zippel a uniform $`c\in S^n`$, $`S\subseteq R`$, $`|S|\ge2N(N-1)d`$, works with probability $`\ge1/2`$, and success ($`\operatorname{disc}R_T\ne0`$, or pairwise separation in case 2) is verified exactly. The Stauduhar argument uses only $`gT(\alpha_j)=T(\alpha_{g(j)})`$. $`\square`$

**Lemma 9.3.** Pruning discards no coset containing $`G`$ (§2.2).

**Theorem 9.4.** From any $`U_0\ge G`$ the loop (list maximal subgroups of $`U`$ up to conjugacy; test surviving cosets with squarefree resolvents; descend on a positive test, stop when all are negative) terminates, every visited group contains $`G`$, and the output is $`G`$. *Proof.* Invariant $`G\le U_i`$ by Lemma 9.1. If $`G<U_i`$, $`G`$ lies in a maximal subgroup $`V'=\sigma V_j\sigma^{-1}`$, whose coset is tested (9.3) and positive (9.1, 9.2). So either some test is positive and $`|U_{i+1}|\le|U_i|/2`$, or all are negative and $`G=U_i`$. Orders strictly decrease, so the loop stops, at $`G`$. $`\square`$ (Completeness of the maximal-subgroup list is the prover's responsibility; the terminal certificate catches failures.)

**Theorem 9.5.** The number of positive steps is $`\ell\le\Omega([U_0:G])\le\log_2[U_0:G]\le\log_2|U_0|`$, and at most the length of the longest subgroup chain of $`U_0`$; by Cameron–Solomon–Turull this is $`\le\lceil3n/2\rceil-b(n)-1`$ for $`U_0\le S_n`$. Per-step test counts and precisions ($`k_{\mathrm{prf}}\le[U_i:U_{i+1}]k_{\mathrm{rec}}`$) are not bounded by this theorem.

---

## 10. The three checks the artifact must satisfy

The artifact is one code path parametrized by $`(R,\hat R,s)`$, returning $`(U_\ell,\mathcal C,\text{verdict})`$. Outside the three families below it returns the group with its certificate and the checker's verdict and does not otherwise certify it. The checks are stated first as required, then in the precise form the artifact implements; where the required wording is mathematically inaccurate this is said explicitly.

### Check 1: compositions $`g\circ h`$ over $`\mathbb Q`$

**Required.** The computed group must be a subgroup of $`\mathrm{Gal}(h)\wr\mathrm{Gal}(g)`$ containing the subgroup generated by the proven groups of the subfields, and must equal the previously proven group.

**Precise form.** Let $`f=g\circ h`$, $`d=\deg g`$, $`m=\deg h`$, $`\beta_1,\dots,\beta_d`$ the roots of $`g`$, $`B_i=\{x:h(x)=\beta_i\}`$ the block system. The artifact verifies:

1. $`\mathcal B=\{B_i\}`$ is among the block systems of §6 and $`G\le S_m\wr S_d`$;
2. the block action $`\pi(G)`$ equals the previously proven $`\mathrm{Gal}(g)`$ (a *quotient* of $`G`$, not a subgroup);
3. the local group $`G_1:=\mathrm{Stab}_G(B_1)|_{B_1}`$ equals $`\mathrm{Gal}\big(h(x)-\beta_1\ /\ \mathbb Q(\beta_1)\big)`$ when that group has been proven, and in any case $`G_1\le A_h:=\mathrm{Gal}(h(x)-t/\mathbb Q(t))`$ (specialization at the non-branch point $`\beta_1`$); consequently $`G\le G_1\wr\mathrm{Gal}(g)`$;
4. $`G`$ equals the previously proven group of $`f`$ when available.

**Caution.** The literal containment $`G\le\mathrm{Gal}(h)\wr\mathrm{Gal}(g)`$, with $`\mathrm{Gal}(h)`$ the group of $`h(x)=0`$ over $`\mathbb Q`$, is false in general: for $`g=x^2-2`$, $`h=x^3-x`$, $`\mathrm{Gal}(h)`$ is trivial while $`\mathrm{Gal}(x^3-x-\sqrt2/\mathbb Q(\sqrt2))=S_3`$ ($`4-27\cdot2=-50`$ is not a square in $`\mathbb Q(\sqrt2)`$), so $`G`$ has order divisible by $`6`$ and is not inside a group of order $`2`$. The group that enters the wreath product is the relative group of item 3. "Containing the subgroup generated by the proven groups of the subfields" is implemented as items 2–3 (quotient and local group), which is the correct sense in which $`\mathrm{Gal}(g)`$ and the $`h`$-data constrain $`G`$.

### Check 2: Eisenstein polynomials of degree $`\le12`$ over $`\mathbb Q_p`$

**Required.** The computed group must equal the group of the explicitly constructed splitting field, and its ramification filtration orders must match the ramification polygon.

**Precise form.** Let $`L=K(\alpha)`$, $`K'`$ the explicitly constructed splitting field, $`G^{\mathrm{aut}}=\mathrm{Gal}(K'/K)`$ read off the explicit automorphisms ($`\mathsf T_1`$), $`H=\mathrm{Gal}(K'/L)`$, $`G_i=\{\sigma:v_{K'}(\sigma\pi'-\pi')\ge i+1\}`$ the lower numbering filtration computed from the automorphisms. The artifact also runs the descent path over $`K`$ with $`K'`$ as approximation ring using only root approximations and the image-check recognition of §1.4 (no automorphisms), obtaining $`G^{\mathrm{desc}}`$. It verifies:

1. $`G^{\mathrm{desc}}=G^{\mathrm{aut}}`$ as permutation groups in the common labelling;
2. the multiset $`\{v_{K'}(\sigma\alpha-\alpha)/e_{K'/L}:\sigma\in G\setminus H\}`$ (each value with multiplicity $`|H|`$ collapsed) equals the multiset $`\{v_L(\alpha_j-\alpha)\}_{j\ne1}`$ read off the ramification polygon of $`f`$ (Newton polygon of $`f(\alpha x+\alpha)/\alpha^n`$ over $`L`$, computed from the coefficients of $`f`$ alone);
3. the different identity $`\sum_{i\ge0}(|G_i|-1)-\sum_{i\ge0}(|H\cap G_i|-1)=e_{K'/L}\,v_K(\operatorname{disc}f)`$, which is Hilbert's formula for $`\mathfrak D_{K'/K}`$ and $`\mathfrak D_{K'/L}`$ (lower numbering restricts to subgroups), transitivity of the different, and $`v_L(\mathfrak D_{L/K})=v_L(f'(\alpha))=v_K(\operatorname{disc}f)`$ for the monogenic totally ramified $`L`$;
4. in the tame case, $`G\le C_n\rtimes(\mathbb Z/n)^\times`$ with $`C_n=\langle\tau_\iota\rangle`$ (§2.1).

### Check 3: specializations over $`\mathbb F_q(t)`$ of lacunary or triangular sparse systems

**Required.** The geometric group of §7 must be contained in the wreath product of the classification and the arithmetic group in the extension by the constant field group; where the full wreath product is known to occur, equality must hold.

**Precise form.** The classification supplies, for the sparse system, a block structure and a group $`W_{\mathrm{cl}}\le S_n`$ (an intersection of wreath products) with $`G_{\mathrm{geom}}\le W_{\mathrm{cl}}`$ for every admissible specialization, an arithmetic overgroup $`A_{\mathrm{cl}}\trianglerighteq W_{\mathrm{cl}}`$ with $`A_{\mathrm{cl}}/W_{\mathrm{cl}}`$ cyclic (the constant field group of the generic splitting field), and a list of conditions under which $`G_{\mathrm{geom}}=W_{\mathrm{cl}}`$. The artifact computes $`G`$ (arithmetic lift), $`G_{\mathrm{geom}}`$ and $`c`$ (§7), and verifies:

1. generators of $`G_{\mathrm{geom}}`$ lie in $`W_{\mathrm{cl}}`$ (membership, after matching the classification's block structure to the computed block systems of §6);
2. generators of $`G`$ lie in $`A_{\mathrm{cl}}`$; $`G/G_{\mathrm{geom}}`$ is cyclic of order $`c`$ generated by the class of $`\tau`$, and $`c`$ equals the degree of $`\mathbb F_q(\text{coefficients of }\rho)`$ for the $`G`$-relative $`G_{\mathrm{geom}}`$-invariant value $`\rho`$; $`c\mid\gcd_{t_1}\operatorname{ord}(\mathrm{Frob}_{t_1})`$;
3. $`|G_{\mathrm{geom}}|`$ equals the order of the normal closure in $`G`$ of the inertia generators at the ramified places including $`\infty`$ (Theorem 7.2), the inertia data being matched to the $`t_0`$-labelling up to $`G`$ via the exact descent data;
4. when the classification's conditions for the full group hold, $`G_{\mathrm{geom}}=W_{\mathrm{cl}}`$ (equality of orders suffices given item 1).

---