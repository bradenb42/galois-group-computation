# Character Tables, Schur Indices, and Model Independence

This document covers the step that turns the certified group `G <= S_n`,
acting on the fixed p-adic numbering of the roots, into representation
theoretic data, and proves that every subsequent analytic output (Artin
conductors, Euler factors, root numbers) depends only on the irreducible
character `chi`, never on the choice of matrix model.

## 1. The Dixon–Schneider table and the uniqueness of lifting

Classes `C_1 = {1}, ..., C_k` with representatives `g_i`, sizes `h_i`,
`e = exp(G)`. The class matrices `M_i = (a_{ijl})` with
`a_{ijl} = #{x in C_i : x^{-1} g_l in C_j}` commute, and the vectors of
central characters `omega_t = (h_i chi_t(g_i)/d_t)_i` are their joint
eigenvectors with pairwise distinct eigenvalue vectors (the rows of the
character table are distinct), so repeated eigenspace refinement over a prime
field `F_{p0}` terminates in `k` one-dimensional joint eigenspaces. The prime
`p0` is chosen with three properties, each doing stated work:

1. `p0 ≡ 1 (mod e)` ,  so `F_{p0}` contains canonical images of all `e`-th
   roots of unity and every character value reduces to a well-defined scalar;
2. `p0 > 2*ceil(sqrt|G|)` ,  the lifting below recovers integers known a
   priori to lie in `[0, sqrt|G|]` (eigenvalue multiplicities `m_j <= d_t <=
   sqrt|G|`) and in `(0, sqrt|G|]` (degrees), and an interval of length
   `< p0/2` contains at most one representative of a residue class; for the
   degrees, the two square roots `r` and `p0 - r` of `d_t^2 mod p0` sum to
   `p0 > 2 sqrt|G|`, so at most one of them is `<= sqrt|G|`;
3. `p0` does not divide `|G|` ,  so `h_i`, `|g_i|`, `d_t` are invertible.

Lifting: for `g` of order `o`, `chi(g) = sum_j m_j zeta_o^j` with
`m_j = o^{-1} sum_{s mod o} chibar(g^s) w^{-js(p0-1)/o} (mod p0)` (`w` a
primitive root mod `p0`), each `m_j` determined uniquely by (2). The lifted
table is then verified **exactly in `Z[zeta_e]`** (canonical residues modulo
`Phi_e`, `Fraction` coefficients): first orthogonality
`sum_i h_i chi_s(g_i) chi_t(g_i^{-1}) = delta_st |G|`, `sum_t d_t^2 = |G|`,
`chi_t(1) = d_t`, integrality of every value, and the Galois consistency
`sigma_a(chi(g)) = chi(g^a)` for all `a` prime to `e` ,  the last identity ties
the cyclotomic representation to the power maps through a relation the
lifting formula never used in that form, so it is a genuine cross-check.

## 2. Models and Schur indices

For a pair `(H, lambda)` ,  `H <= G`, `lambda` a linear character of `H` , 
with multiplicity `mu = <Res_H chi, lambda>`, the idempotent
`Fid = e_chi f_lambda` generates a left ideal of the group algebra affording
exactly `mu * chi`. Two searches are run in order:

* **trivial `lambda` over arbitrary subgroups.** If `<Res_H chi, 1> = 1` the
  ideal lives inside the permutation module `Q(chi)[G/H]`; all linear algebra
  stays in `Q(chi)` and the model needs no descent at all. This covers every
  monomial-with-rational-values case (e.g. the 4-dimensional character of
  `F_20`, where `H` is a point stabilizer) at trivial cost.
* **cyclic `(H, lambda)` with `mu = 1`.** Covers characters that are not
  monomial in any useful sense: for the 2-dimensionals of `SL(2,3)` the pair
  `(C_6, lambda)` has multiplicity one although no induced linear character
  equals `chi`.

Galois descent from `F0 = Q(zeta_e)` to `Q(chi)` runs over generators
`sigma = sigma_a` of the stabilizer `S_chi = Gal(F0/Q(chi))`: solve the
intertwiner `T rho^sigma(g) = rho(g) T`. This is the side for which
`S = T o sigma` commutes with `rho`; the opposite convention conjugates `rho`
to `rho^{sigma^2}` and coincides with this one only when `sigma` has order 2,
so the convention matters for descent of degree greater than 2. Check the
cocycle `S^r = gamma * Id` is scalar and `sigma`-fixed, solve the
norm equation `Nm_sigma(c) = gamma` by bounded search, rescale, and take the
fixed form spanned by `v = sum_l S^l(w)`. Then:

* **descent reaches `Q(chi)`**: `m_chi = 1`, *proven by the exhibited model*
  (all entries verified fixed by `S_chi`, all traces verified `= chi`).
* **descent blocked and `nu(chi) = -1`**: `m_chi = 2`, proven ,  the
  Frobenius–Schur indicator `-1` makes the invariant bilinear form symplectic,
  so the local index at the infinite place is 2 and `2 | m_chi`; by
  Brauer–Speiser a real-valued `chi` has `m_chi | 2`. The model of `2 chi` is
  the restriction of scalars along one quadratic step (entrywise regular
  representation of `F''(eta)/F''`), with character `chi + sigma(chi) = 2 chi`.
* **otherwise**: `m_chi` is reported as undetermined and the deepest model is
  retained. The general method for this case is Unger's splitting; the bounded
  norm search stands in for it and settles every character on the validation
  families. Downstream code reads the flag and never assumes `m_chi = 1`.

## 3. Model-independence of conductors, Euler factors, root numbers

Fix a prime `ell`, a decomposition group `D` with inertia `I` and higher
ramification subgroups `G_i` (lower numbering), and a Frobenius lift
`sigma in D`. Let `rho` be **any** representation over a characteristic-0
field affording `m * chi` (`m >= 1`), `V` its space.

**Lemma (fixed spaces).** `e_H = |H|^{-1} sum_{h in H} rho(h)` is the
projector onto `V^H`, so `dim V^H = Tr e_H = m * <Res_H chi, 1> =
m |H|^{-1} sum_h chi(h)` ,  a function of `chi` and `m`.

**Proposition (Euler factors).** `sigma` normalizes `I`, so `rho(sigma)`
commutes with `e_I` and `(rho(sigma) e_I)^k = rho(sigma^k) e_I`. Hence the
power traces of Frobenius on the inertia invariants are

    Tr(Frob^k | V^I) = Tr(rho(sigma^k) e_I) = m |I|^{-1} sum_{tau in I} chi(sigma^k tau),

functions of `chi` alone. Newton's identities convert the power traces
`k = 1..dim V^I` into the coefficients of `det(1 - rho(sigma) u | V^I)`, so
the Euler factor at `ell` is determined by `chi` (and the class of `sigma`,
which is part of the arithmetic input, not of the model). Well-definedness in
`sigma tau` (`tau in I`) is the same computation: the average over `I` is
visibly unchanged.

**Proposition (conductors).** The Artin conductor exponent

    f(chi) = sum_{i >= 0} (|G_i| / |G_0|) * (chi(1) - dim V^{G_i} / m)

involves only `chi(1)` and the fixed-space dimensions of the Lemma, hence
only `chi`. (That `f(chi)` is a non-negative integer is Artin's conductor
theorem; the implementation verifies integrality per prime as a consistency
check rather than re-proving it.)

**Proposition (root numbers).** The local constants
`epsilon(chi_v, psi_v, dx_v)` of Deligne–Langlands are defined on the
Grothendieck group of virtual representations of the Weil group: they are
additive in `chi`, inductive in degree 0, and normalized on characters via
abelian local constants (Gauss sums). In particular they depend only on the
isomorphism class of the representation ,  equivalently on its character , 
never on a chosen matrix realization. The computation consumes `chi` and the
ramification data only.

**Corollary (Schur multiples are harmless).** If one computes with a model of
`m chi` instead of `chi`, the three outputs transform as `L(s, m chi) =
L(s, chi)^m`, `f(m chi) = m f(chi)`, `epsilon(m chi) = epsilon(chi)^m`. Since
the pipeline computes all three *from `chi` directly* by the formulas above,
no extraction is even necessary: the model's roles are (a) certifying
`m_chi` and realizability for the tables, and (b) optional cross-validation , 
`det(1 - rho(sigma) e_I u)` computed from an actual model must equal the
`chi`-computed factor raised to the `m`-th power, an executable check.

Together: every quantity the artifact will publish for `L(s, chi)` is a
function of the character table, the ramification filtration, and the
Frobenius classes ,  objects the model never touches. Model independence therefore
holds by construction.